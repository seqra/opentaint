# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Report dropped external methods not yet classified (run with uv from the project root).
UNCOVERED = dropped - (classification buckets + build.done + skipped.yaml), matched FQN-level.
With `--batch <id>` it checks one batch plan's methods instead — the per-agent done check.
"""
import argparse
import glob
import sys
from pathlib import Path

import yaml

DROPPED = Path(".opentaint/results/dropped-external-methods.yaml")
APPROX_DIR = Path(".opentaint/tracking/approximations")

# classification buckets + skipped.yaml lists; build.done is read separately (nested)
CLASSIFIED_KEYS = {"passthrough", "dataflow", "skipped", "methods", "engine_issues"}


def fqn(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    if i != -1:
        s = s[:i]
    return s.strip()


def fqn_of(item):
    return fqn(item["method"] if isinstance(item, dict) else item)


def dropped_methods():
    doc = yaml.safe_load(DROPPED.read_text(encoding="utf-8")) or []
    return {fqn(e["method"]) for e in doc if isinstance(e, dict) and e.get("method")}


def classified_methods():
    # every FQN in a classification bucket, build.done, or skipped.yaml across the batch files
    out = set()
    for p in sorted(glob.glob(str(APPROX_DIR / "*.yaml"))):
        doc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        for key in CLASSIFIED_KEYS:
            for item in doc.get(key, []) or []:
                if str(item).strip():
                    out.add(fqn_of(item))
        for item in (doc.get("build") or {}).get("done", []) or []:
            if str(item).strip():
                out.add(fqn_of(item))
    return out


def batch_methods(batch_arg):
    # the FQNs a batch plan assigned (scopes: {class: [{method, signature}]}); id or path
    p = Path(batch_arg)
    if not p.is_file():
        p = APPROX_DIR / "plans" / f"{batch_arg}.yaml"
    if not p.is_file():
        return None
    doc = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    return {fqn_of(m)
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
    ap.add_argument("--batch", help="check one batch plan's methods (id or path) — the per-agent done check")
    args = ap.parse_args()

    classified = classified_methods()

    if args.batch:
        methods = batch_methods(args.batch)
        if methods is None:
            print(f"no batch plan at {args.batch}")
            return 2
        return report(f"batch {args.batch}", len(methods),
                      sorted(methods - classified), "before returning")

    if not DROPPED.is_file():
        print(f"no dropped file at {DROPPED} — nothing to check")
        return 2
    dropped = dropped_methods()
    return report("coverage", len(dropped), sorted(dropped - classified),
                  "before the phase is done")


if __name__ == "__main__":
    sys.exit(main())
