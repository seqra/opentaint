# Author sinks + assemble + rescan

The approximation loop flagged the sinks the project's untrusted data can reach into per-package sink units. Author the sink rules, join them to every source, and rescan to surface the findings.
Gate: a deep-only phase. `get_status.py` reports `sink_rules` `DONE` once every sink unit passes, each created sink rule is wired into a join, and no rule changed after the last scan; otherwise it names the next sub-step: a pending unit's next dispatch, `assemble-lib-rules` for unwired sinks, or a rescan.

## Sink lib rules

Per sink unit `get_status.py` lists as not passing, a two-step pipeline dispatched one step at a time (step 2 only after step 1's artifact); units fan out in parallel, capped (create-rule is heavy).

### 1. Dispatch create-test-project

Inputs:
- `project-root`
- `language`
- `type: rule-sink`
- `unit`

Expect back — `stages.test_project: done` on the unit.

### 2. Dispatch create-rule

Inputs:
- `project-root`
- `language`
- `side: sinks`
- `unit`
- `fix-target` (optional) — a scan-flagged rule to correct instead of authoring the unit; fix-mode, per references/escalation.md

Expect back — each sink's `rule_id` and `stages.tests_passing: done` on the unit.

## Assemble the full joins

### 3. Dispatch assemble-lib-rules

Inputs:
- `project-root`
- `language`

Expect back — the created-sink joins added to the joins tally (re-entrant: each sink refing all relevant sources, built-in and created). Then delete the sink units' `test-compiled/` models.

## Final rescan

### 4. Dispatch run-scan (references/scan.md)

Inputs:
- `project-root`
- `max-memory` — `state.yaml.max_memory` when set

Expect back — a fresh `report.sarif` with the new sink rules and joins fired; triage then seeds and reads its findings.

Run `uv run scripts/get_status.py` to confirm `sink_rules` `DONE`.
