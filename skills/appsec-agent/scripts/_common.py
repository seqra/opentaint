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
SCOPE = TRACKING / "scope.yaml"            # every mode: what intake scoped, as the family list
REFERENCE_TR = TRACKING / "reference"      # enactment mode: the supplied findings, normalized
BOUNDARIES_TR = TRACKING / "boundaries"    # every mode: per-family universal boundary specs
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


# ---- intake scope ----

def scope_families():
    """(name, evidence) per family the intake stage scoped, in scope.yaml order.

    One shape for every mode: the evidence items are reference finding ids in enactment mode,
    and the members or code areas intake settled on in onboarding and discovery mode. The
    boundaries stage generalizes one family per entry, whichever mode wrote it."""
    out = []
    for f in (load_yaml(SCOPE, {}) or {}).get("families") or []:
        name = strip_quotes((f or {}).get("name", "")) if isinstance(f, dict) else ""
        if name:
            out.append((name, [strip_quotes(str(e)) for e in (f.get("evidence") or [])]))
    return out


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


# ---- finding files ----

RULE_RE = re.compile(r'^rule_id:\s*(.+?)\s*$', re.M)
VERDICT_RE = re.compile(r'^verdict:\s*(.+?)\s*$', re.M)


def ledger_verdicted_keys():
    """method+signature keys already verdicted in classification.yaml (source ∪ safe)."""
    doc = load_yaml(RULES_TR / "classification.yaml", {}) or {}
    return {strip_quotes(x) for key in ("source", "safe") for x in (doc.get(key) or [])}
