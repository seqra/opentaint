# Triage

On normal/deep, finish the approximation loop first — `verify.py status` must show `approximations: done`, not merely a settled SARIF.

Seed the finding files yourself (deterministic, no context cost):

```bash
uv run scripts/generate.py findings .opentaint/results/report.sarif
```

It writes one `tracking/findings/<name>.yaml` per rule and is idempotent — a rescan adds new result hashes to an untriaged finding, and when every finding for a rule is already triaged it surfaces the new hashes as a fresh `pending` finding whose `notes` open with a `reconcile` line (rather than clobbering a verdict).

Classify — never yourself. Fan out analyze-findings, one subagent per finding file (a few files per agent is fine). Inputs: `project-root`, `findings` (the finding file(s)). Each reconciles any `reconcile` finding by flow, splits the rule's bundle into distinct logical findings, reads each result's code flow, and sets `verdict` + appends its reasoning to `notes`. Assign no verdicts yourself.

A zero-finding scan is not automatically clean on normal/deep — taint that dies before any sink yields zero just as a clean project does. `verify.py` flags 0 findings in integrity; suspect a broken flow (an over-eager skip, a still-dropped method on a source→sink path, or a project model whose scope roots missed the app code) and trace it with debug-rule (references/escalation.md) before concluding clean.

Assemble the report. Rewrite `.opentaint/vulnerabilities.md` from the current `verdict: TP` findings — one entry each: finding name, rule / vuln class, the source→sink location, and the one-clause rationale from `notes`. Reflect only the current state: drop resolved findings, update changed ones; if no TP remains, say so. On a static run, list any finding still carrying `poc: confirmed` from a prior dynamic run under a separate "Previously PoC-confirmed (not re-verified)" section. On a dynamic run the PoC phase refreshes this again (references/poc.md). `verify.py status` confirms `triage: done`.
