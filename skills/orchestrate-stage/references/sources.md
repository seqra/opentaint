# Author sources + assemble

Author the source rules the boundaries stage seeded into per-family units, and wire them to every relevant sink. The first project scan follows: it is what proves the boundaries and names the taint frontier the later stages work from.

On re-entry, work only the units `get_status.py` still lists as pending — a unit that already passes is a prior pass's result, not work to redo.

## Source lib rules

For each source unit `get_status.py` lists as not passing, run this two-step pipeline one step at a time; units fan out in parallel.

### 1. Dispatch create-test-project

Inputs:
- `language`
- `type: rule-source`
- `unit`

Expect back — `stages.test_project: done` on the unit.

### 2. Dispatch create-rule

Inputs:
- `language`
- `side: sources`
- `unit`
- `fix-target` (optional) — only the scan-flagged rule correction explicitly assigned by the task

Expect back — each source's `rule_id` set, every custom rule carrying its deliberate source-family tag, and `stages.tests_passing: done`.

## Assemble source joins

Once no source unit is pending, status names unwired created sources. Dispatch assemble-lib-rules.

Inputs:
- `language`

Expect back — existing tag-expanded joins reused where they already cover the created sources, extension joins added only for uncovered combinations, and the concrete coverage recorded in the joins tally. Then delete the source units' `test-compiled/` models.

## Stage gate

`get_status.py` drives `source_rules`, naming the current sub-step and units. Finish when it reads `DONE`, or when the next step it reports is the project scan.
