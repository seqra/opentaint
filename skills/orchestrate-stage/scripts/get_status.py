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
import re
import subprocess
import sys
from pathlib import Path

from _common import (APPROX, BOUNDARIES_TR, CONTROLS_TR, DATAFLOW, FINDINGS_TR,
                     JOINS_TR, MODEL, PASS_THROUGH, REFERENCE_TR, ROOT, RULES,
                     RULES_TR, SARIF, SINKS_TR, SOURCES_TR, TRACKING,
                     build_done_keys, classified_keys, dropped_entries,
                     git_head, load_yaml, member_key, modeled_entries,
                     control_gap, skipped_keys, strip_quotes)

STATE = load_yaml(TRACKING / "state.yaml", {}) or {}
MODE = STATE.get("mode") or "discovery"
SCAN_LEVEL = STATE.get("scan_level")
TRIAGE_LEVEL = STATE.get("triage_level")
CONTROLS = str(STATE.get("controls") or "on").strip()

DISCOVER_PLANS = RULES_TR / "plans"
APPROX_PLANS = APPROX / "plans"
VULN = ROOT / "vulnerabilities.md"
ENACTMENT = ROOT / "enactment.md"
GLOBAL_CAP = 10


def short(c):
    return str(c)[:8] if c else c


# ---- tree readers ----

def load_units(d):
    return [(p.stem, load_yaml(p, {}) or {}) for p in sorted(Path(d).glob("*.yaml"))] \
        if Path(d).is_dir() else []


def load_docs(d):
    """(path, doc) for every tracking file in a directory — reference, boundary, control."""
    return [(p, load_yaml(p, {}) or {}) for p in sorted(Path(d).glob("*.yaml"))] \
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


def _join_source_refs():
    return {str(s).strip() for _, doc in load_joins()
            for s in (doc.get("sources") or []) if str(s).strip()}


def _join_sink_refs():
    return {str(j["sink"]).strip() for _, doc in load_joins()
            for j in (doc.get("joins") or []) if isinstance(j, dict) and j.get("sink")}


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
    if not (TRACKING / "coverage.yaml").is_file():
        return False, ["dispatch triage-dependencies"], None
    leftover = sorted(glob.glob(str(DISCOVER_PLANS / "*.yaml")))
    units = load_units(SOURCES_TR)
    ledger = load_yaml(RULES_TR / "classification.yaml", {}) or {}
    if leftover:
        tasks = [f"dispatch discover-attack-surface, one per plan (cap {GLOBAL_CAP}):"]
        tasks += [f"  {p}" for p in leftover]
        tasks.append("then run `scripts/generate.py mark-safe` to reconcile the plans")
        return False, tasks, None
    if not ledger and not units:
        return False, ["run `scripts/generate.py partition discover` to plan the used members"], None
    return True, [], None


def ph_source_rules():
    units = load_units(SOURCES_TR)
    if not units:
        return True, [], "built-in covered"
    pend = _pending_units(units, "rule-source", "sources")
    if pend:
        return False, ["pending units:"] + pend, None
    missing = sorted(_created_refs(units, "sources") - _join_source_refs())
    if missing:
        return False, ["created sources not wired to a join", "dispatch assemble-lib-rules"], None
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
    refs = _join_sink_refs()
    missing = sorted({e["rule_id"] for _, doc in units for e in (doc.get("sinks") or [])
                      if isinstance(e, dict) and e.get("rule_id")
                      and str(e["rule_id"]).strip() not in refs})
    if missing:
        return False, ["sink rules not wired to a join", "dispatch assemble-lib-rules"], None
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


def ph_controls():
    # both modes: land the sanitizers / negative patterns / restrictions the run has evidence for,
    # then hold the phase until a rescan proves the round changed nothing that mattered
    gap = control_gap()
    docs = load_docs(CONTROLS_TR)
    if gap:
        units = sorted({u for u, _fam, _t in gap})
        if not docs:
            return False, [f"{len(gap)} control target(s) implied by triage/boundaries",
                           "run `scripts/generate.py controls` to seed the control units"], None
        return False, [f"new control targets for: {', '.join(units)}",
                       "run `scripts/generate.py controls` to fold them in"], None
    if not docs:
        return True, [], "no controls needed"
    live = [(p, d) for p, d in docs if not d.get("blocker")]
    unlanded = [p.stem for p, d in live if (d.get("stages") or {}).get("landed") != "done"]
    if unlanded:
        return False, ["control units to land:"] + [f"  {u}" for u in unlanded], None
    if rules_dirty():
        return False, ["controls changed after the last scan", "dispatch run-scan"], None
    unverified = [p.stem for p, d in live if (d.get("stages") or {}).get("verified") != "done"]
    if unverified:
        return False, ["verify the landed controls against the rescan:"] \
            + [f"  {u}" for u in unverified], None
    unsaturated = [p.stem for p, d in live
                   if str((d.get("saturation") or {}).get("status", "")).strip() != "saturated"]
    if unsaturated:
        return False, ["control rounds not saturated:"] + [f"  {u}" for u in unsaturated], None
    return True, [], None


# ---- enactment-mode phases ----

def ph_reference_set():
    docs = load_docs(REFERENCE_TR)
    if not docs:
        src = STATE.get("findings") or "state.yaml findings unset"
        return False, [f"normalize the supplied findings ({src}) into "
                       ".opentaint/tracking/reference/<finding-id>.yaml"], None
    missing = sorted(p.stem for p, d in docs if not strip_quotes(d.get("family", "")))
    if missing:
        return False, ["reference findings not assigned to a boundary family:"] \
            + [f"  {m}" for m in missing], None
    return True, [], None


def families():
    return sorted({strip_quotes(d.get("family", "")) for _, d in load_docs(REFERENCE_TR)
                   if strip_quotes(d.get("family", ""))})


def ph_boundaries():
    specs = {p.stem: d for p, d in load_docs(BOUNDARIES_TR)}
    fams = families()
    missing = [f for f in fams if f not in specs]
    if missing:
        return False, ["dispatch discover-universal-boundaries, one per family:"] \
            + [f"  {f}" for f in missing], None
    # a split renames the family on its reference findings, so every spec here owns its findings
    unsaturated = [f for f in fams
                   if str((specs[f].get("saturation") or {}).get("status", "")).strip()
                   != "saturated"]
    if unsaturated:
        return False, ["boundary specs not saturated:"] + [f"  {f}" for f in unsaturated], None
    unfactored = sorted(p.stem for p, d in load_docs(REFERENCE_TR)
                        if p.stem not in (specs.get(strip_quotes(d.get("family", "")), {})
                                          .get("factorization") or {}))
    if unfactored:
        return False, ["reference findings with no factorization in their spec:"] \
            + [f"  {r}" for r in unfactored], None
    unseeded = [f for f in fams if (specs[f].get("stages") or {}).get("units_seeded") != "done"]
    if unseeded:
        return False, ["seed the source and sink units from these specs' candidate_patterns:"] \
            + [f"  {f}" for f in unseeded], None
    return True, [], None


def ph_crossref():
    if not SARIF.is_file():
        return False, ["dispatch run-scan"], None
    docs = load_docs(REFERENCE_TR)
    scanned = SARIF.stat().st_mtime
    pend = [p for p, d in docs
            if str(d.get("crossref", "pending")).strip() != "done" or p.stat().st_mtime < scanned]
    if pend:
        return False, [f"cross-reference the scan against {len(pend)} reference finding(s):"] \
            + [f"  {p}" for p in pend], None
    blocked = sorted({str(m) for _, d in docs for m in (d.get("blocked_at") or [])})
    if blocked:
        return False, ["expected traces stop at unmodeled carriers:"] + [f"  {m}" for m in blocked] \
            + ["model them in an approximation round, rescan, then cross-reference again"], None
    rep = sum(1 for _, d in docs if str(d.get("status", "")).strip() == "reproduced")
    stale = newest_mtime([p for p, _ in docs]) > (ENACTMENT.stat().st_mtime
                                                  if ENACTMENT.is_file() else 0)
    if not ENACTMENT.is_file() or stale:
        return False, [f"rewrite .opentaint/enactment.md coverage manifest "
                       f"({rep}/{len(docs)} reproduced)"], None
    return True, [], None


# controls edit created rules, which only a deep run has, and the caller can opt out of the
# precision pass entirely — an audit that wants every candidate result keeps it off.
def controls_in_scope():
    return SCAN_LEVEL == "deep" and CONTROLS != "off"


DISCOVERY_PHASES = [
    ("build", ph_build, lambda: True),
    ("discover", ph_discover, lambda: SCAN_LEVEL == "deep"),
    ("source_rules", ph_source_rules, lambda: SCAN_LEVEL == "deep"),
    ("scan", ph_scan, lambda: True),
    ("approximations", ph_approximations, lambda: SCAN_LEVEL in ("normal", "deep")),
    ("sink_rules", ph_sink_rules, lambda: SCAN_LEVEL == "deep"),
    ("triage", ph_triage, lambda: True),
    ("poc", ph_poc, lambda: TRIAGE_LEVEL == "dynamic"),
    ("controls", ph_controls, controls_in_scope),
]

# enactment reproduces a supplied finding set: the reference set and its saturated boundaries
# replace dependency discovery, and both rule sides are authored before the first scan so that
# scan is rule-first. The cross-reference closes the run — it judges what the finished rule set,
# its approximations, its verdicts and its controls actually reproduced.
ENACTMENT_PHASES = [
    ("build", ph_build, lambda: True),
    ("reference_set", ph_reference_set, lambda: True),
    ("boundaries", ph_boundaries, lambda: True),
    ("source_rules", ph_source_rules, lambda: True),
    ("sink_rules", ph_sink_rules, lambda: True),
    ("scan", ph_scan, lambda: True),
    ("approximations", ph_approximations, lambda: True),
    ("triage", ph_triage, lambda: True),
    ("poc", ph_poc, lambda: TRIAGE_LEVEL == "dynamic"),
    ("controls", ph_controls, controls_in_scope),
    ("crossref", ph_crossref, lambda: True),
]

PHASES = ENACTMENT_PHASES if MODE == "enactment" else DISCOVERY_PHASES


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
    print(f"mode={MODE}  scan={SCAN_LEVEL}  triage={TRIAGE_LEVEL}  controls={CONTROLS}  "
          f"language={STATE.get('language')}  commit={commit}  "
          f"cap={GLOBAL_CAP} (heavy {heavy_cap()})")
    if MODE == "enactment":
        print(f"findings={STATE.get('findings')}")
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
