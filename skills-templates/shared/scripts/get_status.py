# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
get_status.py — the orchestrator's status source. Derives, from the .opentaint tree,
which pipeline phase is current and the exact orchestrator tasks for it; writes nothing
(use generate.py to mutate). Run with uv from the project root:

  uv run scripts/get_status.py            current stage + its orchestrator tasks
  uv run scripts/get_status.py --full     every in-scope phase as DONE/IN_PROGRESS/PENDING

Call it at each stage boundary to decide the next move, and --full at run start / on
resume. It lists every pending plan, batch, unit, and finding to hand out — dispatch what
it names rather than re-deriving state by hand.
"""
import argparse
import glob
import os
import subprocess
import sys
from pathlib import Path

from _common import (APPROX, DATAFLOW,
                     FINDINGS_TR, MODEL, PASS_THROUGH, ROOT, RULES, RULES_TR,
                     SARIF, SINKS_TR, SOURCES_TR, TAGS, TRACKING,
                     active_lib_rules, build_done_keys, builtin_rules_root,
                     classified_keys, dropped_entries, git_head, iter_rules,
                     load_yaml, member_key, modeled_entries, rule_tags,
                     skipped_keys)

STATE = load_yaml(TRACKING / "state.yaml", {}) or {}
SCAN_LEVEL = STATE.get("scan_level")
TRIAGE_LEVEL = STATE.get("triage_level")

DISCOVER_PLANS = RULES_TR / "plans"
APPROX_PLANS = APPROX / "plans"
VULN = ROOT / "vulnerabilities.md"
GLOBAL_CAP = 10


def short(c):
    return str(c)[:8] if c else c


# ---- tree readers ----

def load_units(d):
    return [(p.stem, load_yaml(p, {}) or {}) for p in sorted(Path(d).glob("*.yaml"))] \
        if Path(d).is_dir() else []


def load_findings():
    out = []
    if FINDINGS_TR.is_dir():
        for p in sorted(FINDINGS_TR.glob("*.yaml")):
            doc = load_yaml(p, {}) or {}
            notes = str(doc.get("notes") or "")
            out.append({"path": str(p), "name": p.stem,
                        "verdict": str(doc.get("verdict", "pending")).strip(),
                        "poc": str(doc.get("poc", "pending")).strip(),
                        "reconcile": notes.lstrip().startswith("reconcile")})
    return out


def newest_mtime(paths):
    m = 0.0
    for p in paths:
        try:
            m = max(m, p.stat().st_mtime)
        except OSError:
            pass
    return m


def approx_dirty():
    # scan older than the newest applied approximation artifact -> a rescan is pending
    if not SARIF.is_file():
        return False
    arts = list(PASS_THROUGH.rglob("*")) + list(DATAFLOW.rglob("*"))
    return newest_mtime([p for p in arts if p.is_file()]) > SARIF.stat().st_mtime


def rules_dirty():
    if not SARIF.is_file():
        return False
    return newest_mtime([p for p in RULES.rglob("*.yaml") if p.is_file()]) > SARIF.stat().st_mtime


def scan_stale():
    # SARIF older than the model -> a rebuild happened, rescan before trusting it
    manifest = MODEL / "project.yaml"
    if not SARIF.is_file() or not manifest.is_file():
        return False
    return manifest.stat().st_mtime > SARIF.stat().st_mtime


def unit_next(doc, kind, side):
    # the next dispatch step for a not-yet-passing rule unit
    if (doc.get("stages") or {}).get("test_project") != "done":
        return f"create-test-project type {kind}"
    return f"create-rule side {side}"


def _ruleset_roots():
    roots = [builtin_rules_root()]
    if RULES.is_dir():
        roots.append(RULES)
    return roots


def _rule_index():
    language = STATE.get("language")
    out = {}
    for root in _ruleset_roots():
        for ref, rule in iter_rules(root, language):
            out[ref] = rule
    return out


def _registry():
    doc = load_yaml(TAGS, {}) or {}
    def values(key):
        raw = doc.get(key) or []
        raw = [raw] if isinstance(raw, str) else raw
        return {str(tag).strip() for tag in raw if str(tag).strip()}
    return values("sources"), values("sinks")


def _custom_tag_issues(kind):
    """Tags used by custom lib rules must be registered under their matching role."""
    sources, sinks = _registry()
    known = sources if kind == "source" else sinks
    suffix = f"-{kind}"
    issues = []
    language = STATE.get("language")
    if not RULES.is_dir():
        return issues
    for ref, rule in active_lib_rules(RULES, language):
        for tag in sorted(t for t in rule_tags(rule) if t.endswith(suffix)):
            if tag not in known:
                issues.append(f"{ref}: tag `{tag}` is not registered in {TAGS}")
            if kind == "source" and tag != "untrusted-data-source":
                issues.append(f"{ref}: reusable source rules must use `untrusted-data-source`, "
                              f"not `{tag}`")
    return issues


def _source_tag_issues(units):
    index = _rule_index()
    issues = _custom_tag_issues("source")
    for unit, doc in units:
        stages = doc.get("stages") or {}
        blocked = bool(doc.get("blocker") or stages.get("blocker"))
        if str(doc.get("tag") or "").strip() != "untrusted-data-source":
            issues.append(f"{unit}: source unit must use `tag: untrusted-data-source`")
        entries = doc.get("sources") or []
        if not entries and not blocked:
            issues.append(f"{unit}: source unit has no source entries")
        for entry in entries:
            ref = str(entry.get("rule_id") or "").strip() if isinstance(entry, dict) else ""
            if not ref:
                if not blocked:
                    issues.append(f"{unit}: source entry has no implementing rule_id")
                continue
            if ref not in index:
                issues.append(f"{ref}: source rule does not resolve in the active rulesets")
            elif "untrusted-data-source" not in rule_tags(index[ref]):
                issues.append(f"{ref}: source rule must use `untrusted-data-source`")
    return issues


def _sink_tag_issues(units):
    index = _rule_index()
    issues = _custom_tag_issues("sink")
    registered = _registry()[1]
    for unit, doc in units:
        stages = doc.get("stages") or {}
        blocked = bool(doc.get("blocker") or stages.get("blocker"))
        for group in doc.get("groups") or []:
            if not isinstance(group, dict):
                continue
            tag = str(group.get("tag") or "").strip()
            if not tag:
                issues.append(f"{unit}: sink group has no tag")
                continue
            if not tag.endswith("-sink"):
                issues.append(f"{unit}: `{tag}` is not a sink tag")
            elif tag not in registered:
                issues.append(f"{unit}: sink tag `{tag}` is not registered in {TAGS}")
            for entry in group.get("sinks") or []:
                ref = str(entry.get("rule_id") or "").strip() if isinstance(entry, dict) else ""
                if not ref:
                    if not blocked:
                        issues.append(f"{unit}: sink entry in `{tag}` has no implementing rule_id")
                elif tag not in rule_tags(index.get(ref, {})):
                    issues.append(f"{ref}: rule does not carry its group tag `{tag}`")
    return issues


def _tag_pairs():
    """Tag-to-tag edges present in active join rules across builtin + custom rulesets."""
    language = STATE.get("language")
    pairs = set()
    for root in _ruleset_roots():
        for _ref, rule in iter_rules(root, language):
            options = rule.get("options") or {}
            if rule.get("mode") != "join" or "disabled" in options:
                continue
            join = rule.get("join") or {}
            aliases = {str(ref.get("as") or "").strip(): ref
                       for ref in join.get("refs") or [] if isinstance(ref, dict)}
            # PyYAML 1.1 reads the plain YAML key `on` as boolean True.
            for edge in join.get("on") or join.get(True) or []:
                if not isinstance(edge, str) or "->" not in edge:
                    continue
                left, right = edge.split("->", 1)
                left_alias = left.strip().split(".", 1)[0]
                right_alias = right.strip().split(".", 1)[0]
                source_tag = aliases.get(left_alias, {}).get("tag")
                sink_tag = aliases.get(right_alias, {}).get("tag")
                if source_tag and sink_tag:
                    pairs.add((str(source_tag).strip(), str(sink_tag).strip()))
    return pairs


def _missing_tag_pairs():
    """Every reusable active source group must reach every reusable active sink group."""
    language = STATE.get("language")
    used_sources, used_sinks = set(), set()
    for root in _ruleset_roots():
        for _ref, rule in active_lib_rules(root, language):
            for tag in rule_tags(rule):
                if tag.endswith("-source"):
                    used_sources.add(tag)
                elif tag.endswith("-sink"):
                    used_sinks.add(tag)
    covered = _tag_pairs()
    return sorted((source, sink) for source in used_sources for sink in used_sinks
                  if (source, sink) not in covered)


def _pending_units(units, kind, side):
    # units not passing and not settled by a blocker; each tagged with its next step
    out = []
    for name, doc in units:
        st = doc.get("stages") or {}
        if st.get("tests_passing") != "done" and not (doc.get("blocker") or st.get("blocker")):
            out.append(f"  {name}  {unit_next(doc, kind, side)}")
    return out


# ---- phase derivations: each returns (done, tasks, note) ----
# done: the phase is complete. tasks: the brief lines when it is the current stage.
# note: a short suffix shown only on the --full line (e.g. build from a dirty tree).

def ph_build():
    if not (MODEL / "project.yaml").is_file():
        return False, ["determine project language and write to state.yaml.language",
                       "dispatch build-project"], None
    head, mc = git_head(), STATE.get("model_commit")
    if head is None:
        return True, [], "no git — taken as current"
    if mc is None:
        return True, [], "from dirty tree"
    if head == mc:
        return True, [], None
    return False, [f"model stale: HEAD {short(head)} != model_commit {short(mc)}",
                   "dispatch build-project"], None


def ph_discover():
    if not TAGS.is_file():
        return False, ["run `scripts/generate.py tags` to restore the lib-rule tag registry"], None
    if not (TRACKING / "coverage.yaml").is_file():
        return False, ["dispatch triage-dependencies"], None
    leftover = sorted(glob.glob(str(DISCOVER_PLANS / "*.yaml")))
    ledger = load_yaml(RULES_TR / "classification.yaml", {}) or {}
    if leftover:
        tasks = [f"dispatch discover-attack-surface, one per plan (cap {GLOBAL_CAP}):"]
        tasks += [f"  {p}" for p in leftover]
        tasks.append("then run `scripts/generate.py mark-safe` to reconcile the plans")
        return False, tasks, None
    if not ledger:
        return False, ["run `scripts/generate.py partition discover` to plan the used members"], None
    unit_sources = {member_key(entry) for _unit, doc in load_units(SOURCES_TR)
                    for entry in (doc.get("sources") or []) if isinstance(entry, dict)}
    missing = sorted({member_key(entry) for entry in (ledger.get("source") or [])}
                     - unit_sources)
    if missing:
        return False, ["classified sources missing source units:"] \
            + [f"  {entry}" for entry in missing], None
    return True, [], None


def ph_source_rules():
    units = load_units(SOURCES_TR)
    if not units:
        issues = _custom_tag_issues("source")
        if issues:
            return False, ["source rule tag errors:"] + [f"  {x}" for x in issues], None
        return True, [], None
    pend = _pending_units(units, "rule-source", "sources")
    if pend:
        return False, ["pending units:"] + pend, None
    issues = _source_tag_issues(units)
    if issues:
        return False, ["source rule tag errors:"] + [f"  {x}" for x in issues], None
    return True, [], None


def ph_scan():
    if not SARIF.is_file() or scan_stale():
        return False, ["dispatch run-scan"], None
    return True, [], None


def ph_approximations():
    if not SARIF.is_file():
        return False, ["dispatch run-scan"], None
    classified = classified_keys()
    uncovered = [e for e in dropped_entries() if member_key(e) not in classified]
    if uncovered:
        plans = sorted(glob.glob(str(APPROX_PLANS / "*.yaml")))
        if plans:
            tasks = [f"dispatch analyze-external-methods, one per plan (cap {GLOBAL_CAP}):"]
            tasks += [f"  {p}" for p in plans]
            tasks.append("then run `scripts/generate.py merge-skipped` to merge the batches")
            return False, tasks, None
        n = len({e["method"] for e in uncovered})
        return False, [f"{n} methods unclassified",
                       "run `scripts/generate.py partition analyze` to split them into batch plans"], None
    done = build_done_keys()
    terminal = skipped_keys()          # skipped/engine-issue carriers never build — don't hold the gate
    unbuilt = [(p, kind) for p, kind, m in modeled_entries()
               if member_key(m) not in done and member_key(m) not in terminal]
    if unbuilt:
        by_kind = {}
        for p, kind in unbuilt:
            by_kind.setdefault(kind, set()).add(p.stem)
        tasks = ["build unbuilt batches:"]
        if by_kind.get("passthrough"):
            tasks.append("  passthrough  create-pass-through-approximation: "
                         + ", ".join(sorted(by_kind["passthrough"])))
        if by_kind.get("dataflow"):
            tasks.append("  dataflow  create-test-project type dataflow, then "
                         "create-dataflow-approximation: " + ", ".join(sorted(by_kind["dataflow"])))
        return False, tasks, None
    if approx_dirty():
        return False, ["approximations built after the last scan", "dispatch run-scan"], None
    stuck = sorted({e["method"] for e in dropped_entries()
                    if member_key(e) in done and member_key(e) not in terminal})
    if stuck:
        return False, [f"built but still dropped ({len(stuck)}), escalate:"] \
            + [f"  {m}" for m in stuck], None
    return True, [], None


def ph_sink_rules():
    units = load_units(SINKS_TR)
    pend = _pending_units(units, "rule-sink", "sinks")
    if pend:
        return False, ["pending units:"] + pend, None
    issues = _sink_tag_issues(units)
    if issues:
        return False, ["sink rule tag errors:"] + [f"  {x}" for x in issues], None
    missing = _missing_tag_pairs()
    if missing:
        tasks = ["reusable tag groups are not fully joined:"]
        tasks += [f"  {source} -> {sink}" for source, sink in missing]
        tasks.append("dispatch assemble-lib-rules")
        return False, tasks, None
    if rules_dirty():
        return False, ["rules changed after the last scan", "dispatch run-scan"], None
    return True, [], None


def ph_triage():
    findings = load_findings()
    if not findings:
        if not SARIF.is_file():
            return False, ["dispatch run-scan"], None
        return False, ["run `scripts/generate.py findings` to seed the finding files"], None
    pend = [f"  {f['path']}" + ("  (reconcile)" if f["reconcile"] else "")
            for f in findings if f["verdict"] == "pending"]
    if pend:
        return False, ["dispatch analyze-findings over pending findings:"] + pend, None
    tp = sum(1 for f in findings if f["verdict"] == "TP")
    stale = newest_mtime([Path(f["path"]) for f in findings]) > (VULN.stat().st_mtime
                                                                 if VULN.is_file() else 0)
    if not VULN.is_file() or stale:
        return False, [f"rewrite .opentaint/vulnerabilities.md from the TP findings ({tp} TP)"], None
    return True, [], None


def ph_poc():
    findings = load_findings()
    tps = [f for f in findings if f["verdict"] == "TP"]
    pend = [f"  {f['path']}" for f in tps if f["poc"] == "pending"]
    if pend:
        return False, ["generate-poc serially over TP findings without a PoC:"] + pend, None
    servers = (load_yaml(TRACKING / "poc-servers.yaml", {}) or {}).get("servers") or []
    if servers:
        return False, ["tear down the instances in poc-servers.yaml and clear the registry",
                       "refresh .opentaint/vulnerabilities.md"], None
    return True, [], None


PHASES = [
    ("build", ph_build, lambda: True),
    ("discover", ph_discover, lambda: SCAN_LEVEL == "deep"),
    ("source_rules", ph_source_rules, lambda: SCAN_LEVEL == "deep"),
    ("scan", ph_scan, lambda: True),
    ("approximations", ph_approximations, lambda: SCAN_LEVEL in ("normal", "deep")),
    ("sink_rules", ph_sink_rules, lambda: SCAN_LEVEL == "deep"),
    ("triage", ph_triage, lambda: True),
    ("poc", ph_poc, lambda: TRIAGE_LEVEL == "dynamic"),
]


# ---- caps ----

def free_gb():
    mi = Path("/proc/meminfo")
    if mi.is_file():
        for ln in mi.read_text().splitlines():
            if ln.startswith("MemAvailable:"):
                return int(ln.split()[1]) // (1024 * 1024)
    try:
        total = int(subprocess.run(["sysctl", "-n", "hw.memsize"], capture_output=True,
                                   text=True, check=True).stdout.strip())
        return total // (1024 ** 3)
    except (OSError, subprocess.CalledProcessError, ValueError):
        return None


def heavy_cap():
    cores = os.cpu_count() or 1
    fg = free_gb()
    return max(1, min(cores, (fg // 2 if fg else cores), GLOBAL_CAP))


# ---- output ----

def in_scope():
    return [(name, fn) for name, fn, gate in PHASES if gate()]


def evaluate():
    """Every in-scope phase as (name, done, tasks, note), with the current stage marked."""
    rows = [(name,) + fn() for name, fn in in_scope()]
    current = next((i for i, r in enumerate(rows) if not r[1]), None)
    return rows, current


def cmd_full():
    commit = short(STATE.get("model_commit")) or "none"
    print(f"scan={SCAN_LEVEL}  triage={TRIAGE_LEVEL}  language={STATE.get('language')}  "
          f"commit={commit}  cap={GLOBAL_CAP} (heavy {heavy_cap()})")
    rows, current = evaluate()
    # a phase downstream of the current stage that vacuously satisfies its own check is not
    # actually done — its producing stage hasn't run — so it reads PENDING, never DONE.
    for i, (name, done, tasks, note) in enumerate(rows):
        if current is None or i < current:
            state = "DONE"
        elif i == current:
            state = "IN_PROGRESS"
        else:
            state = "PENDING"
        suffix = f"  ({note})" if note and state == "DONE" else ""
        print(f"{name:<15} {state}{suffix}")
    return 0


def cmd_brief():
    rows, current = evaluate()
    if current is None:
        print("run complete")
        return 0
    name, _done, tasks, _note = rows[current]
    print(f"{name}  IN_PROGRESS")
    for t in tasks:
        print(f"  {t}")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--full", action="store_true",
                    help="every in-scope phase as DONE/IN_PROGRESS/PENDING")
    args = ap.parse_args()
    return cmd_full() if args.full else cmd_brief()


if __name__ == "__main__":
    sys.exit(main())
