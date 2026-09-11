# Discover sources + source rules

Discover the project's used dependency members that are taint sources, then author source rules in the reusable source group. Existing tag joins connect them automatically. The first project scan follows and names the later taint frontier. On re-entry, partition plans only members no prior run has classified.

## Triage dependencies

Dispatch triage-dependencies when status names it.

Expect back — `.opentaint/tracking/coverage.yaml` written.

## Discover sources

Run:

```bash
uv run <skill-dir>/scripts/generate.py partition discover
```

It writes balanced `.opentaint/tracking/rules/plans/lib-NNN.yaml` plans, one disjoint slice per leaf, containing the currently unclassified dependency members. Fan out discover-attack-surface, one per plan.

Inputs each:
- `language`
- `plan`

At the join run:

```bash
uv run <skill-dir>/scripts/generate.py mark-safe
```

Expect back — each agent records the sources it finds into its plan and writes any source unit(s); the join folds source/safe verdicts into `classification.yaml` and prunes the consumed plans. Discovery is a single fan-out pass, not a loop.

Run `uv run <skill-dir>/scripts/get_status.py` to confirm `discover` `DONE`.

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

Expect back — each source's `rule_id` set and `stages.tests_passing: done`.

## Complete source rules

Created source rules use `untrusted-data-source`, so existing tag joins expand to them automatically. No source-only join assembly is needed. Once all source units pass and `get_status.py` accepts their tags, delete the source units' `test-compiled/` models.

## Stage gate

`get_status.py` drives every in-scope source phase and names the current sub-step and units. Finish when those phases are `DONE`, or when the next step it reports is the project scan.
