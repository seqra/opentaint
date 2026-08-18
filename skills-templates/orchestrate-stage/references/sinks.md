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

Expect back — each sink's `rule_id` set, every custom rule carrying its deliberate sink-family tag, and `stages.tests_passing: done`.

## Assemble the full joins

Once no sink unit is pending, status names unwired sink rules. Dispatch assemble-lib-rules.

Inputs:
- `language`

Expect back — existing tag-expanded joins reused where they already cover the created sinks, extension joins added only for uncovered combinations, and the concrete coverage recorded in the joins tally. Then delete the sink units' `test-compiled/` models.

## Stage gate

`get_status.py` names each pending sink unit, unwired sink rules, then the project rescan. Finish when every unit is passing or terminal and every created sink is wired. If status reports `rules changed after the last scan`, report the pending rescan and stop.
