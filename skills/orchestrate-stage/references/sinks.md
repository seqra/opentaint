# Author sinks + assemble

Author the sink rules flagged into per-package units during approximation classification and join them to every relevant source. The final project rescan follows to surface findings.

## Sink lib rules

For each sink unit `get_status.py` lists as not passing, run this two-step pipeline one step at a time; units fan out in parallel.

### 1. Dispatch create-test-project

Inputs:
- `language`
- `type: rule-sink`
- `unit`

Expect back — `stages.test_project: done` on the unit.

### 2. Dispatch create-rule

Inputs:
- `language`
- `side: sinks`
- `unit`
- `fix-target` (optional) — only the scan-flagged rule correction explicitly assigned by the task

Expect back — each sink's `rule_id` set and `stages.tests_passing: done`.

## Complete tag coverage

Once no sink unit is pending, status checks the active tag-pair matrix. A created sink that reused an existing tag is already connected, if status names a new uncovered sink tag, dispatch assemble-lib-rules.

Inputs:
- `language`

Expect back — one tag-to-tag join per missing pair, then a clean coverage check. Delete the sink units' `test-compiled/` models.

## Stage gate

`get_status.py` names each pending sink unit, invalid tags, uncovered tag pairs, then the project rescan. Finish when every unit is passing or terminal and the reusable tag matrix is covered. If status reports `rules changed after the last scan`, report the pending rescan and stop.
