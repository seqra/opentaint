# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Fill each discover plan's `safe` list = its assigned members minus the sources the agent
found (run with uv by the orchestrator, once, after the discover fan-out). A member not
marked a source is safe — examined, not an entry-point source; sinks are found later from
the taint frontier, independent of this ledger.
"""
import glob
import sys
from pathlib import Path

import yaml

PLANS = Path(".opentaint/tracking/rules/plans")


def fqn(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    return (s[:i] if i != -1 else s).strip()


def main():
    plans = sorted(glob.glob(str(PLANS / "lib-*.yaml")))
    if not plans:
        print("no discover plans to reconcile", file=sys.stderr)
        return 0
    total = 0
    for p in plans:
        doc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        members = {fqn(m) for v in (doc.get("scopes") or {}).values() for m in v}
        sources = {fqn(x) for x in (doc.get("source") or [])}
        doc["safe"] = sorted(members - sources)
        Path(p).write_text(
            yaml.safe_dump(doc, sort_keys=False, default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        total += len(doc["safe"])
        print(f"{Path(p).name}: {len(sources)} sources, {len(doc['safe'])} safe")
    print(f"reconciled {len(plans)} plan(s), {total} safe total")
    return 0


if __name__ == "__main__":
    sys.exit(main())
