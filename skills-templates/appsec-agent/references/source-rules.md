# Discover sources + source rules

The deep pass opens on sources: discover the project's used dependency members that are taint sources, author source rules, and wire them to the built-in sinks for the first scan — the taint frontier names the sinks later. On a re-entry partition re-plans only members no prior run verdicted.
Gate: deep pass only. `get_status.py` drives two phases here — `discover` then `source_rules` — reporting `DONE` per phase and naming each sub-step until then.

## Triage dependencies

Dispatch triage-dependencies.

Inputs:
- `project-root`

Expect back — `coverage.yaml` written, get_status then advances discover past this sub-step.

## Discover sources

Run `uv run scripts/generate.py partition discover` — writes balanced plans to `tracking/rules/plans/lib-NNN.yaml` (paths printed), one disjoint slice per agent.

Fan out discover-attack-surface, one agent per plan, capped.

Inputs each:
- `project-root`
- `language`
- `plan`

At the join run `uv run scripts/generate.py mark-safe` — merges the verdicts into `classification.yaml` and prunes the consumed plans.

Expect back — each agent records the sources it finds into its plan and writes any source unit(s), mark-safe folds them into the ledger. Discover is a single fan-out pass, not a loop.

Run `uv run scripts/get_status.py` to confirm `discover` `DONE`.

## Source lib rules

For each source unit `get_status.py` lists as not passing, a two-step pipeline dispatched one step at a time (one by another); units fan out in parallel, capped (create-rule is heavy):

1. Dispatch create-test-project.
   Inputs:
   - `project-root`
   - `language`
   - `type: rule-source`
   - `unit`

   Expect back — `stages.test_project: done` on the unit.

2. Dispatch create-rule.
   Inputs:
   - `project-root`
   - `language`
   - `side: sources`
   - `unit`
   - `fix-target` (optional) — a scan-flagged rule to correct instead of authoring the unit; fix-mode, per references/escalation.md

   Expect back — each source's `rule_id` set and `stages.tests_passing: done` on the unit.

Once every unit passes, get_status names the remaining sub-step — the created sources still need wiring to a join.

## Assemble source joins

Dispatch assemble-lib-rules.

Inputs:
- `project-root`
- `language`

Expect back — the joins tally written (`stages.written: done` per class): one join per built-in sink, each refing all created sources for that vuln class. The scan verifies the joins.

Then delete the source units' `test-compiled/` models — the stage is done with them.

Run `uv run scripts/get_status.py` to confirm `source_rules` `DONE`.
