# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Rebuild approximations/skipped.yaml from every batch file's `skipped` and `engine_issues`
buckets (run with uv from the project root, at the analyze join). `methods` = the union of
skipped FQNs (non-carriers left to the engine default); `engine_issues` = the union of
carriers the engine can't model. Idempotent — derived wholly from the durable batch files.
"""
import glob
import sys
from pathlib import Path

import yaml

APPROX_DIR = Path(".opentaint/tracking/approximations")


def fqn(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    if i != -1:
        s = s[:i]
    return s.strip()


def fqn_of(item):
    return fqn(item["method"] if isinstance(item, dict) else item)


def main():
    methods, engine_issues = set(), set()
    for p in sorted(glob.glob(str(APPROX_DIR / "*.yaml"))):
        if Path(p).name == "skipped.yaml":
            continue
        doc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        for item in doc.get("skipped", []) or []:
            if str(item).strip():
                methods.add(fqn_of(item))
        for item in doc.get("engine_issues", []) or []:
            if str(item).strip():
                engine_issues.add(fqn_of(item))
    out = {"methods": sorted(methods), "engine_issues": sorted(engine_issues)}
    (APPROX_DIR / "skipped.yaml").write_text(
        yaml.safe_dump(out, sort_keys=False, default_flow_style=False, allow_unicode=True),
        encoding="utf-8",
    )
    print(f"skipped.yaml: {len(methods)} methods, {len(engine_issues)} engine_issues")
    return 0


if __name__ == "__main__":
    sys.exit(main())
