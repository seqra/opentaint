# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Report dropped external methods not yet classified (run with uv from the project root).
UNCOVERED = dropped - methods: - done: - engine_issues:, matched FQN-level.
With `--plan <id>` it checks one plan's methods instead — the per-agent done check.
"""
import argparse
import glob
import sys
from pathlib import Path

import yaml

DROPPED = Path(".opentaint/results/dropped-external-methods.yaml")
APPROX_DIR = Path(".opentaint/tracking/approximations")

CLASSIFIED_KEYS = {"methods", "done", "engine_issues"}


def fqn(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    if i != -1:
        s = s[:i]
    return s.strip()


def dropped_methods():
    doc = yaml.safe_load(DROPPED.read_text(encoding="utf-8")) or []
    return {fqn(e["method"]) for e in doc if isinstance(e, dict) and e.get("method")}


def classified_methods():
    # every FQN under a methods/done/engine_issues key across all unit and skip files
    out = set()
    for p in sorted(glob.glob(str(APPROX_DIR / "*.yaml"))):
        doc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        for key in CLASSIFIED_KEYS:
            for item in doc.get(key, []) or []:
                if str(item).strip():
                    out.add(fqn(item))
    return out


def plan_methods(plan_arg):
    # the FQNs a plan assigned (each scope's rows carry `method`); id or path, None if missing
    p = Path(plan_arg)
    if not p.is_file():
        p = APPROX_DIR / "plans" / f"{plan_arg}.yaml"
    if not p.is_file():
        return None
    doc = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    return {fqn(m["method"] if isinstance(m, dict) else m)
            for members in (doc.get("scopes") or {}).values() for m in members}


def report(label, total, uncovered, tail):
    covered = total - len(uncovered)
    print(f"{label}: {covered}/{total} classified, {len(uncovered)} UNCOVERED")
    if uncovered:
        print(f"\nUNCOVERED — classify each (model or skip) {tail}:")
        for m in uncovered:
            print(f"  {m}")
        return 1
    return 0


def main():
    ap = argparse.ArgumentParser(description="report dropped methods not yet classified")
    ap.add_argument("--plan", help="check one plan's methods (id or path) — the per-agent done check")
    args = ap.parse_args()

    classified = classified_methods()

    if args.plan:
        methods = plan_methods(args.plan)
        if methods is None:
            print(f"no plan at {args.plan}")
            return 2
        return report(f"plan {args.plan}", len(methods),
                      sorted(methods - classified), "before returning")

    if not DROPPED.is_file():
        print(f"no dropped file at {DROPPED} — nothing to check")
        return 2
    dropped = dropped_methods()
    return report("coverage", len(dropped), sorted(dropped - classified),
                  "before the phase is done")


if __name__ == "__main__":
    sys.exit(main())
