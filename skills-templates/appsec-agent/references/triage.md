# Triage

Classifies the scan's findings and assembles the final report. On normal/deep, finish the approximation loop first — `get_status.py` must show `approximations` `DONE`, not merely a settled SARIF.
Gate: `get_status.py` reports `triage` `DONE` when every finding is verdicted and `.opentaint/vulnerabilities.md` is newer than all of them; otherwise it names the sub-step: seed the finding files, dispatch analyze-findings over the pending ones, or rewrite the report.

### 1. Seed the finding files

```bash
uv run scripts/generate.py findings
```

Argument-free — reads `results/report.sarif`, writes one `tracking/findings/<name>.yaml` per rule, idempotent across rescans.

### 2. Dispatch analyze-findings

Fan out one subagent per finding file (a few files per agent is fine).

Inputs:
- `project-root`
- `language`
- `findings` — the finding file(s) to triage

Expect back — each finding's `verdict` set and rationale appended to `notes`; `get_status.py` then lists no pending findings. A pending finding tagged `(reconcile)` is a rescan's new hits under an already-triaged rule — dispatch it the same way; its `notes` carry the self-contained reconcile instruction for the subagent.

### 3. Assemble the report

Once every finding is verdicted, rewrite `.opentaint/vulnerabilities.md` from the current `verdict: TP` findings — one entry each: finding name, rule / vuln class, the source→sink location, and the one-clause rationale from `notes`. Reflect only the current state: drop resolved findings, update changed ones; if no TP remains, say so. On a static run, list any finding still carrying `poc: confirmed` from a prior dynamic run under a separate "Previously PoC-confirmed (not re-verified)" section; on a dynamic run the PoC phase refreshes this again (references/poc.md).

Run `uv run scripts/get_status.py` to confirm `triage` `DONE` — it flips only when `vulnerabilities.md` is newer than every finding, so a later analyze-findings re-dispatch flips it back to pending.
