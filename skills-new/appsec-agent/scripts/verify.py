# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
verify.py — the orchestrator's read-only eyes. Derives, from the .opentaint tree,
where the run stands and what to do next; writes nothing (use generate.py to mutate).
Run with uv from the project root: `uv run scripts/verify.py status [--full]`.

  status         current stage only: the first unfinished phase + its `next:` action
  status --full  the whole picture: every phase, machine caps, integrity, resume point

Call it at the start / on resume / before a large fan-out (`--full`), and at a stage's
gate (`status`) — not after every single subagent.
"""
import argparse
import glob
import os
import re
import subprocess
import sys
from pathlib import Path

from _common import (APPROX, DATAFLOW, DROPPED, FINDINGS_TR, JOINS_TR, MODEL,
                     PASS_THROUGH, ROOT, RULES, RULES_TR, SARIF, SINKS_TR,
                     SOURCES_TR, TRACKING, build_done_keys, classified_keys,
                     dropped_entries, git_head, load_yaml, member_key,
                     modeled_entries)

STATE = load_yaml(TRACKING / "state.yaml", {}) or {}
SCAN_LEVEL = STATE.get("scan_level")
TRIAGE_LEVEL = STATE.get("triage_level")


def short(c):
    return str(c)[:8] if c else c


# ---- tree readers ----

def load_units(d):
    return [(p.stem, load_yaml(p, {}) or {}) for p in sorted(Path(d).glob("*.yaml"))] \
        if Path(d).is_dir() else []


def load_joins():
    return [(p.stem, load_yaml(p, {}) or {}) for p in sorted(JOINS_TR.glob("*.yaml"))] \
        if JOINS_TR.is_dir() else []


def load_findings():
    out = []
    if FINDINGS_TR.is_dir():
        for p in sorted(FINDINGS_TR.glob("*.yaml")):
            doc = load_yaml(p, {}) or {}
            notes = str(doc.get("notes") or "")
            out.append({"name": p.stem, "verdict": str(doc.get("verdict", "pending")).strip(),
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


# ---- phase derivations: each returns (status, summary, items, next) ----

def ph_build():
    if not (MODEL / "project.yaml").is_file():
        return "pending", "project.yaml absent", [], "dispatch build-project"
    head, mc = git_head(), STATE.get("model_commit")
    if head is None:
        return "done", "no git repo — model taken as current", [], None
    if mc is None:
        return "stale", "model_commit null (built from a modified tree)", [], \
            "rebuild if source changed: dispatch build-project"
    if head == mc:
        return "done", f"model_commit==HEAD ({short(head)})", [], None
    return "stale", f"HEAD {short(head)} != model_commit {short(mc)}", [], \
        "source moved — dispatch build-project"


def ph_discover():
    if not (TRACKING / "coverage.yaml").is_file():
        return "pending", "coverage.yaml absent", [], "dispatch triage-dependencies"
    leftover = sorted(glob.glob(str(RULES_TR / "plans" / "*.yaml")))
    units = load_units(SOURCES_TR)
    ledger = load_yaml(RULES_TR / "classification.yaml", {}) or {}
    if leftover:
        return "pending", f"{len(leftover)} discover plan(s) not reconciled", \
            [Path(p).name for p in leftover], \
            "fan out discover-attack-surface per plan, then: uv run scripts/generate.py mark-safe"
    if not ledger and not units:
        return "pending", "no discover run yet", [], \
            ("uv run scripts/generate.py partition discover; fan out discover-attack-surface; "
             "then: uv run scripts/generate.py mark-safe")
    return "done", (f"{len(units)} source unit(s), ledger "
                    f"{len(ledger.get('source') or [])} source/{len(ledger.get('safe') or [])} safe"), [], None


def _unit_pending(units):
    # a unit with a `blocker` is settled (skipped, won't pass) — it must not hold the phase
    # pending forever; it surfaces in integrity instead.
    out = []
    for name, doc in units:
        st = doc.get("stages") or {}
        if st.get("tests_passing") != "done" and not doc.get("blocker"):
            out.append(f"{name}: test_project={st.get('test_project', '?')}, "
                       f"tests_passing={st.get('tests_passing', '?')}")
    return out


def _join_source_refs():
    refs = set()
    for _, doc in load_joins():
        for s in doc.get("sources") or []:
            if str(s).strip():
                refs.add(str(s).strip())
    return refs


def _created_refs(units, field):
    """rule_ids on the units that resolve to a rule file under .opentaint/rules (created, not
    a built-in ref, which is indistinguishable by path but never sits on disk here)."""
    refs = set()
    for _, doc in units:
        for e in doc.get(field) or []:
            rid = str(e.get("rule_id", "")).strip() if isinstance(e, dict) else ""
            if rid and (RULES / re.split(r"[:#]", rid, 1)[0]).is_file():
                refs.add(rid)
    return refs


def ph_source_rules():
    units = load_units(SOURCES_TR)
    if not units:
        return "done", "no source units (built-in covered)", [], None
    pend = _unit_pending(units)
    if pend:
        return "pending", f"{len(pend)}/{len(units)} source unit(s) not passing", pend, \
            "per pending unit: create-test-project(type rule-source) -> create-rule(side sources)"
    missing = sorted(_created_refs(units, "sources") - _join_source_refs())
    if missing:
        return "pending", f"{len(missing)} created source(s) not wired to a join", missing, \
            "dispatch assemble-lib-rules (wire created sources to the built-in sinks for the first scan)"
    return "done", f"{len(units)} source unit(s) passing, sources wired", [], None


def ph_scan():
    if not SARIF.is_file():
        return "pending", "report.sarif absent", [], \
            "dispatch run-scan (--track-external-methods on normal/deep)"
    return "done", "report.sarif present", [], None


def ph_approximations():
    if not SARIF.is_file():
        return "pending", "no scan yet", [], "dispatch run-scan (--track-external-methods)"
    classified = classified_keys()
    uncovered = [e for e in dropped_entries() if member_key(e) not in classified]
    if uncovered:
        methods = sorted({e["method"] for e in uncovered})
        head = methods[:8] + ([f"... (+{len(methods) - 8} more)"] if len(methods) > 8 else [])
        n = f"{len(uncovered)} UNCOVERED overload(s)" + (
            f" across {len(methods)} method(s)" if len(methods) != len(uncovered) else "")
        return "pending", n, head, \
            ("uv run scripts/generate.py partition analyze; fan out analyze-external-methods "
             "(sinks flag on deep); then: uv run scripts/generate.py merge-skipped")
    done = build_done_keys()
    unbuilt = [(p, kind, m) for p, kind, m in modeled_entries() if member_key(m) not in done]
    if unbuilt:
        by_batch = {}
        for p, kind, m in unbuilt:
            by_batch.setdefault(p.stem, {"passthrough": 0, "dataflow": 0})[kind] += 1
        items = [f"{b}: {c['passthrough']} passthrough, {c['dataflow']} dataflow"
                 for b, c in sorted(by_batch.items())]
        return "pending", f"{len(unbuilt)} modeled method(s) not built", items, \
            ("build the batches: passthrough -> create-pass-through-approximation; "
             "dataflow -> create-test-project(type dataflow) -> create-dataflow-approximation")
    if approx_dirty():
        return "pending", "approximations built after the last scan", [], \
            "dispatch run-scan to surface newly-dropped methods"
    stuck = sorted({e["method"] for e in dropped_entries() if member_key(e) in done})
    if stuck:
        head = stuck[:8] + ([f"... (+{len(stuck) - 8} more)"] if len(stuck) > 8 else [])
        return "pending", f"{len(stuck)} built method(s) still dropped", head, \
            ("the approximation isn't propagating — escalate (references/escalation.md): re-plan a "
             "stubborn passThrough as dataflow, or move a truly-unmodelable carrier to the batch's engine_issues")
    return "done", "0 UNCOVERED, all modeled built, scan current", [], None


def _join_sink_refs():
    refs = set()
    for _, doc in load_joins():
        for j in doc.get("joins") or []:
            if isinstance(j, dict) and j.get("sink"):
                refs.add(str(j["sink"]).strip())
    return refs


def ph_sink_rules():
    units = load_units(SINKS_TR)
    pend = _unit_pending(units)
    if pend:
        return "pending", f"{len(pend)}/{len(units)} sink unit(s) not passing", pend, \
            "per pending unit: create-test-project(type rule-sink) -> create-rule(side sinks)"
    refs = _join_sink_refs()
    missing = sorted({e["rule_id"] for _, doc in units for e in (doc.get("sinks") or [])
                      if isinstance(e, dict) and e.get("rule_id") and str(e["rule_id"]).strip() not in refs})
    if missing:
        return "pending", f"{len(missing)} sink rule(s) without a join", missing, \
            "dispatch assemble-lib-rules"
    if rules_dirty():
        return "pending", "rules changed after the last scan", [], \
            "dispatch run-scan (final — surfaces the sink findings)"
    return "done", f"{len(units)} sink unit(s) passing, joins wired", [], None


def ph_triage():
    findings = load_findings()
    if not findings:
        if not SARIF.is_file():
            return "pending", "no scan yet", [], "dispatch run-scan"
        return "pending", "no finding files yet", [], \
            ("uv run scripts/generate.py findings .opentaint/results/report.sarif; "
             "then fan out analyze-findings")
    pend = [f["name"] + (" (reconcile)" if f["reconcile"] else "")
            for f in findings if f["verdict"] == "pending"]
    if pend:
        return "pending", f"{len(pend)}/{len(findings)} finding(s) not verdicted", pend, \
            "fan out analyze-findings over the pending finding(s)"
    tp = sum(1 for f in findings if f["verdict"] == "TP")
    return "done", f"{len(findings)} finding(s) verdicted (TP={tp}, FP={len(findings) - tp})", [], None


def ph_poc():
    findings = load_findings()
    tps = [f for f in findings if f["verdict"] == "TP"]
    pend = [f["name"] for f in tps if f["poc"] == "pending"]
    if pend:
        return "pending", f"{len(pend)}/{len(tps)} TP finding(s) without a PoC", pend, \
            "generate-poc per TP finding, serialized (first without base-url, reuse it after)"
    servers = (load_yaml(TRACKING / "poc-servers.yaml", {}) or {}).get("servers") or []
    if servers:
        return "pending", f"{len(servers)} PoC instance(s) still up", \
            [f"{s.get('kind')}:{s.get('ref')} (port {s.get('port')})" for s in servers], \
            "tear down the poc-servers.yaml instances, then empty the registry"
    return "done", f"{len(tps)} TP finding(s) PoC'd, no instances up", [], None


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


# ---- machine caps ----

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


def caps_line():
    cores = os.cpu_count() or 1
    fg = free_gb()
    if fg is None:
        heavy = max(1, min(cores, 10))
        return f"caps: global=10 heavy={heavy} (cores={cores} free=unknown)"
    heavy = max(1, min(cores, fg // 2, 10))
    return f"caps: global=10 heavy={heavy} (cores={cores} free={fg}G)"


# ---- integrity (cheap, non-blocking warnings) ----

def integrity():
    warns = []
    # units the run couldn't make pass (recorded, skipped) — surface so they aren't silent
    for side, d in (("source", SOURCES_TR), ("sink", SINKS_TR)):
        for name, doc in load_units(d):
            if doc.get("blocker"):
                warns.append(f"{side} unit {name}: blocker — {doc['blocker']}")
    # a join rule assemble wrote (always custom: `<class>-<sink>-lib-ext.yaml`) whose file is gone.
    # unit rule_ids are skipped here — a built-in ref is indistinguishable from a custom path.
    for cls, doc in load_joins():
        for j in doc.get("joins") or []:
            rid = str(j.get("rule_id", "")).strip() if isinstance(j, dict) else ""
            path = re.split(r"[:#]", rid, 1)[0]
            if path.endswith("-lib-ext.yaml") and not (RULES / path).is_file():
                warns.append(f"join {cls}: rule file missing for {rid}")
    # disposable plans that should have been pruned
    for label, g in (("discover", RULES_TR / "plans"), ("approximation", APPROX / "plans")):
        left = glob.glob(str(g / "*.yaml"))
        if left:
            warns.append(f"{len(left)} leftover {label} plan(s) under {g} (prune at the join)")
    # stray nested tree from a cwd bug
    if (ROOT / ".opentaint").exists():
        warns.append(f"stray nested {ROOT / '.opentaint'} — a test ran with cwd inside .opentaint")
    return warns


# ---- output ----

STATUS_TAG = {"done": "DONE", "pending": "PENDING", "stale": "STALE", "n/a": "N/A",
              "waiting": "WAITING"}


def evaluate():
    rows = []
    for name, fn, gate in PHASES:
        if not gate():
            rows.append((name, "n/a", "not in scope for these levels", [], None))
            continue
        st, summ, items, nxt = fn()
        rows.append((name, st, summ, items, nxt))
    return rows


def resume_of(rows):
    for name, st, summ, items, nxt in rows:
        if st in ("pending", "stale"):
            return name, st, summ, items, nxt
    return None


def print_block(name, st, summ, items, indent="  "):
    print(f"{indent}{name:<14} {STATUS_TAG[st]:<8} {summ}")
    for it in items:
        print(f"{indent}    {it}")


def cmd_status(args):
    rows = evaluate()
    levels = f"scan={SCAN_LEVEL} triage={TRIAGE_LEVEL}"
    if args.full:
        head = f"{levels}  language={STATE.get('language')}  model_commit={short(STATE.get('model_commit'))}"
        print(f"{head}  {caps_line()}")
        print("phases:")
        res = resume_of(rows)
        resume_name = res[0] if res else None
        past_resume = False
        for name, st, summ, items, nxt in rows:
            # a phase downstream of the resume point that derives "done" is only vacuously done
            # (its producing stage hasn't run yet) — show it as WAITING, not a misleading DONE
            if past_resume and st == "done":
                print_block(name, "waiting", "not reached yet", [])
            else:
                print_block(name, st, summ, items)
            if name == resume_name:
                past_resume = True
        print(f"resume: {resume_name or 'complete'}")
        if res and res[4]:
            print(f"next: {res[4]}")
        warns = integrity()
        if warns:
            print("integrity:")
            for w in warns:
                print(f"  - {w}")
        return 0

    res = resume_of(rows)
    if not res:
        print(f"resume: complete  ({levels}) — every in-scope phase done")
        warns = integrity()
        if warns:
            print(f"integrity: {len(warns)} warning(s) — run `verify.py status --full`")
        return 0
    name, st, summ, items, nxt = res
    print(f"resume: {name}  ({levels})")
    print_block(name, st, summ, items)
    if nxt:
        print(f"next: {nxt}")
    warns = integrity()
    if warns:
        print(f"integrity: {len(warns)} warning(s) — run `verify.py status --full`")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("status", help="where the run stands + what to do next")
    s.add_argument("--full", action="store_true", help="every phase, caps, and integrity")
    s.set_defaults(func=cmd_status)
    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
