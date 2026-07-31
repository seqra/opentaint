# Triage — classify findings + assemble report

Classify the latest project scan's findings and assemble the current vulnerability report from their verdicts.

## Seed the finding files

When status names seeding, run:

```bash
uv run <skill-dir>/scripts/generate.py findings
```

It reads `.opentaint/results/report.sarif` and idempotently writes one `.opentaint/tracking/findings/<name>.yaml` per rule. A rescan adds new hashes without clobbering existing verdicts.

## Dispatch analyze-findings

Fan out one leaf per pending finding file; a few files per leaf is fine.

Inputs:
- `language`
- `findings`

Expect back — each finding's `verdict` set and rationale appended to `notes`. A pending finding tagged `(reconcile)` is dispatched the same way; its notes carry the reconciliation context. After the fan-out, use `get_status.py` to list anything still pending.

Never assign a finding verdict yourself — verdicts come only from analyze-findings leaves.

## Assemble the report

Once every finding is verdicted, rewrite `.opentaint/vulnerabilities.md` from the current `verdict: TP` findings — one entry each: finding name, rule / vulnerability class, the source→sink location, and the one-clause rationale from `notes`. Reflect only current state: drop resolved findings and update changed ones; if no TP remains, say so.

List a finding still carrying `poc: confirmed` from an earlier run under a separate `Previously PoC-confirmed (not re-verified)` section. The PoC stage refreshes the report from its new outcomes.

## Stage gate

`get_status.py` reports `triage` `DONE` when every finding is verdicted and `.opentaint/vulnerabilities.md` is newer than all of them. Report TP/FP totals and any split/reconciled files.
