"""Shared helpers for the OpenTaint pipeline orchestrator scripts.

Not a runnable script — imported by the PEP723 entry points (get_status.py, generate.py),
which carry the pyyaml dependency. Every path resolves under the fixed
<project-root>/.opentaint/ tree relative to the current directory, so run the entry
scripts from the project root.
"""
import glob
import re
import subprocess
from pathlib import Path

import yaml

ROOT = Path(".opentaint")
MODEL = ROOT / "project"
TRACKING = ROOT / "tracking"
APPROX = TRACKING / "approximations"
RULES_TR = TRACKING / "rules"
SOURCES_TR = RULES_TR / "sources"
SINKS_TR = RULES_TR / "sinks"
JOINS_TR = RULES_TR / "joins"
FINDINGS_TR = TRACKING / "findings"
REFERENCE_TR = TRACKING / "reference"      # enactment mode: the supplied findings, normalized
BOUNDARIES_TR = TRACKING / "boundaries"    # enactment mode: per-family boundary specs
CONTROLS_TR = TRACKING / "controls"        # either pipeline: sanitizer / negative-pattern units
RESULTS = ROOT / "results"
DROPPED = RESULTS / "dropped-external-methods.yaml"
SARIF = RESULTS / "report.sarif"
RULES = ROOT / "rules"
PASS_THROUGH = ROOT / "pass-through"
DATAFLOW = ROOT / "dataflow"


# ---- yaml io ----

def load_yaml(path, default=None):
    p = Path(path)
    if not p.is_file():
        return default
    try:
        return yaml.safe_load(p.read_text(encoding="utf-8")) or default
    except yaml.YAMLError as e:
        raise SystemExit(f"{p}: invalid YAML — {e}\n"
                         "  a JVM signature containing '[' must be quoted in flow style "
                         "(signature: \"([BLjava/lang/String;)V\")")


def dump_yaml(obj):
    return yaml.safe_dump(obj, sort_keys=False, default_flow_style=False, allow_unicode=True)


# ---- fqn / member normalization ----

def strip_quotes(s):
    return str(s).strip().strip('"').strip("'")


def fqn_base(s):
    """The method fqn without its signature/params — `a.b.C#m`."""
    s = strip_quotes(s)
    i = s.find("(")
    return (s[:i] if i != -1 else s).strip()


def member_of(item):
    """A bucket/plan entry (dict or str) normalized to {method, signature?}."""
    if isinstance(item, dict):
        m = strip_quotes(item.get("method", ""))
        sig = str(item.get("signature", "")).strip()
        return {"method": m, "signature": sig} if sig else {"method": m}
    return {"method": strip_quotes(item)}


def member_key(item):
    """Overload-precise key: method + signature. Matches the classification ledger."""
    if isinstance(item, dict):
        return f"{strip_quotes(item.get('method', ''))}{str(item.get('signature', '')).strip()}"
    return strip_quotes(item)


def class_of(fqn):
    return fqn_base(fqn).split("#", 1)[0].strip()


def package_of(fqn):
    cls = class_of(fqn)
    return cls.rsplit(".", 1)[0] if "." in cls else ""


# ---- git ----

def git_head():
    """HEAD commit of the project tree, or None when there's no repo."""
    try:
        out = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True,
                             text=True, check=True)
        return out.stdout.strip() or None
    except (OSError, subprocess.CalledProcessError):
        return None


# ---- approximation batch readers (shared by coverage + partition) ----

# a method counts classified once it sits in any batch classification bucket or in build.done
CLASSIFIED_BUCKETS = ("passthrough", "dataflow", "skipped", "engine_issues")
MODELED_BUCKETS = ("passthrough", "dataflow")


def batch_files():
    """Every approximation batch file (skipped.yaml is the merged view, not a batch)."""
    return [Path(p) for p in sorted(glob.glob(str(APPROX / "*.yaml")))
            if Path(p).name != "skipped.yaml"]


def dropped_entries():
    """The dropped external methods as {method, signature?} rows (order preserved)."""
    rows = []
    for e in load_yaml(DROPPED, []) or []:
        if isinstance(e, dict) and e.get("method"):
            row = {"method": strip_quotes(e["method"])}
            if e.get("signature"):
                row["signature"] = str(e["signature"]).strip()
            rows.append(row)
    return rows


def classified_keys():
    """method+signature keys of every method already classified across the batch files.
    Overload-precise (matches the ledger, build.done, unbuilt and stuck checks): a method with
    one overload classified does not mask a differently-propagating overload still dropped."""
    out = set()
    for p in batch_files():
        doc = load_yaml(p, {}) or {}
        for key in CLASSIFIED_BUCKETS:
            for item in doc.get(key, []) or []:
                if str(item).strip():
                    out.add(member_key(item))
        for item in (doc.get("build") or {}).get("done", []) or []:
            if str(item).strip():
                out.add(member_key(item))
    return out


def skipped_keys():
    """method+signature keys classified terminal — the `skipped` and `engine_issues` buckets of
    every batch. Terminal means the method will never build a working carrier, so it must not hold
    the approximations phase pending even if it is still modeled and still dropped by the scan.
    (skipped.yaml is the merged view of these same buckets, so reading the batches alone suffices.)"""
    out = set()
    for p in batch_files():
        doc = load_yaml(p, {}) or {}
        for bucket in ("skipped", "engine_issues"):
            for item in doc.get(bucket, []) or []:
                if str(item).strip():
                    out.add(member_key(item))
    return out


def modeled_entries():
    """Every passthrough/dataflow entry across batches, tagged with its batch file."""
    out = []
    for p in batch_files():
        doc = load_yaml(p, {}) or {}
        for kind in MODELED_BUCKETS:
            for item in doc.get(kind, []) or []:
                if str(item).strip():
                    out.append((p, kind, member_of(item)))
    return out


def build_done_keys():
    """Overload-precise keys of every built approximation across batches."""
    keys = set()
    for p in batch_files():
        doc = load_yaml(p, {}) or {}
        for item in (doc.get("build") or {}).get("done", []) or []:
            if str(item).strip():
                keys.add(member_key(item))
    return keys


# ---- created rules / rule units ----

def rule_path(rule_id):
    """The artifact path a `<path>.yaml:<id>` / `<path>.yaml#<id>` ref points at."""
    return re.split(r"[:#]", strip_quotes(rule_id), 1)[0]


def is_created_rule(rule_id):
    """True when the ref resolves to a rule this run authored under `.opentaint/rules`.
    A built-in ref is indistinguishable by shape but never sits on disk there."""
    return bool(strip_quotes(rule_id)) and (RULES / rule_path(rule_id)).is_file()


def unit_rules():
    """unit stem -> the created rule_ids its source/sink entries carry. In enactment mode the
    unit stem is the boundary family, which is what ties a control unit to its boundary spec."""
    out = {}
    for side, field in ((SOURCES_TR, "sources"), (SINKS_TR, "sinks")):
        if not side.is_dir():
            continue
        for p in sorted(side.glob("*.yaml")):
            for e in (load_yaml(p, {}) or {}).get(field) or []:
                rid = strip_quotes(e.get("rule_id", "")) if isinstance(e, dict) else ""
                if rid and rid != "None":
                    out.setdefault(p.stem, set()).add(rid)
    return out


# ---- controls ----

RULE_RE = re.compile(r'^rule_id:\s*(.+?)\s*$', re.M)
VERDICT_RE = re.compile(r'^verdict:\s*(.+?)\s*$', re.M)


def control_seeds():
    """Every control target the current tracking implies, as (unit, family, target).

    Three producers, one shape: a triaged false positive on a rule this run authored, and — in
    enactment mode — a boundary spec's own controls plus any reference finding whose cross-check
    blamed the rule rather than a missing carrier. `unit` is the boundary family when the rule
    belongs to one (so a family's controls stay in one file) and the rule file stem otherwise.
    """
    fam_of = {rid: fam for fam, rids in unit_rules().items() for rid in rids}
    for stem, rids in join_rules().items():        # a join belongs to the family it was wired for
        if (BOUNDARIES_TR / f"{stem}.yaml").is_file():
            fam_of.update({rid: stem for rid in rids})
    seeds = []
    if FINDINGS_TR.is_dir():
        for p in sorted(FINDINGS_TR.glob("*.yaml")):
            text = p.read_text(encoding="utf-8")
            verdict, rid = VERDICT_RE.search(text), RULE_RE.search(text)
            if not rid or not verdict or verdict.group(1).strip() != "FP":
                continue
            rid = strip_quotes(rid.group(1))
            if not is_created_rule(rid):          # a built-in FP is not this run's to restrict
                continue
            fam = fam_of.get(rid)
            seeds.append((fam or Path(rule_path(rid)).stem, fam,
                          {"rule_id": rid, "kind": "false-positive", "evidence": str(p),
                           "status": "pending"}))
    if BOUNDARIES_TR.is_dir():
        for p in sorted(BOUNDARIES_TR.glob("*.yaml")):
            spec = load_yaml(p, {}) or {}
            if not (spec.get("sanitizers") or spec.get("negative_patterns")):
                continue
            for rid in sorted(unit_rules().get(p.stem, ())):
                seeds.append((p.stem, p.stem,
                              {"rule_id": rid, "kind": "precision", "evidence": str(p),
                               "status": "pending"}))
    if REFERENCE_TR.is_dir():
        for p in sorted(REFERENCE_TR.glob("*.yaml")):
            doc = load_yaml(p, {}) or {}
            fam = strip_quotes(doc.get("family", ""))
            if not fam or str(doc.get("status", "")).strip() == "reproduced" \
                    or str(doc.get("cause", "")).strip() != "rule":
                continue
            for rid in sorted(unit_rules().get(fam, ())):
                seeds.append((fam, fam,
                              {"rule_id": rid, "kind": "false-negative", "evidence": str(p),
                               "status": "pending"}))
    return seeds


def control_gap():
    """The seeds no control unit carries yet — exactly what `generate.py controls` would add."""
    have = set()
    if CONTROLS_TR.is_dir():
        for p in sorted(CONTROLS_TR.glob("*.yaml")):
            for t in (load_yaml(p, {}) or {}).get("targets") or []:
                if isinstance(t, dict):
                    have.add((p.stem, strip_quotes(t.get("rule_id", "")),
                              str(t.get("kind", "")).strip()))
    return [s for s in control_seeds() if (s[0], s[2]["rule_id"], s[2]["kind"]) not in have]


def join_rules():
    """join file stem -> the join rule_ids it wired. The stem is the vuln class, which in
    enactment mode is also the boundary family — that is what pulls a join's false positive
    into its family's control unit instead of a file of its own."""
    out = {}
    if JOINS_TR.is_dir():
        for p in sorted(JOINS_TR.glob("*.yaml")):
            for j in (load_yaml(p, {}) or {}).get("joins") or []:
                rid = strip_quotes(j.get("rule_id", "")) if isinstance(j, dict) else ""
                if rid:
                    out.setdefault(p.stem, set()).add(rid)
    return out


def ledger_verdicted_keys():
    """method+signature keys already verdicted in classification.yaml (source ∪ safe)."""
    doc = load_yaml(RULES_TR / "classification.yaml", {}) or {}
    return {strip_quotes(x) for key in ("source", "safe") for x in (doc.get(key) or [])}
