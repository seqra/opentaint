# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Merge each discover plan's verdicts into the durable ledger rules/classification.yaml
(run with uv by the orchestrator, once, after the discover fan-out). For every plan,
`source` = the FQNs the agent flagged, `safe` = its members minus those — examined,
not an entry-point source. The ledger accumulates across runs so the next discover
partition skips already-verdicted members; the per-run plans are disposable. A member
ever flagged a source stays a source (source wins over safe).
"""
import glob
import sys
from pathlib import Path

import yaml

PLANS = Path(".opentaint/tracking/rules/plans")
LEDGER = Path(".opentaint/tracking/rules/classification.yaml")


def fqn(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    return (s[:i] if i != -1 else s).strip()


def main():
    plans = sorted(glob.glob(str(PLANS / "lib-*.yaml")))
    if not plans:
        print("no discover plans to reconcile", file=sys.stderr)
        return 0
    doc = (yaml.safe_load(LEDGER.read_text(encoding="utf-8")) if LEDGER.is_file() else None) or {}
    source = {fqn(x) for x in (doc.get("source") or [])}
    safe = {fqn(x) for x in (doc.get("safe") or [])}
    for p in plans:
        pdoc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        members = {fqn(m) for v in (pdoc.get("scopes") or {}).values() for m in v}
        srcs = {fqn(x) for x in (pdoc.get("source") or [])}
        source |= srcs
        safe |= members - srcs
        print(f"{Path(p).name}: {len(srcs)} sources, {len(members - srcs)} safe")
    safe -= source
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    LEDGER.write_text(
        yaml.safe_dump({"source": sorted(source), "safe": sorted(safe)},
                       sort_keys=False, default_flow_style=False, allow_unicode=True),
        encoding="utf-8",
    )
    print(f"classification.yaml: {len(source)} source, {len(safe)} safe total")
    return 0


if __name__ == "__main__":
    sys.exit(main())
