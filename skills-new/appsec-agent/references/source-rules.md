# Discover sources + source rules

The deep pass starts with sources: discover the project's used dependency members that are taint sources, author source rules, and wire them to the built-in sinks for the first scan — the taint frontier names the sinks later. On a re-entry over changed code the partition re-plans only members no prior run verdicted, so unchanged surface is skipped automatically. `verify.py status` drives each sub-step's `next:`.

## Triage dependencies

Dispatch triage-dependencies. Inputs: `project-root`. It reads the model's dependencies and writes `coverage.yaml` — the packages that could introduce a source the built-ins don't cover. On a re-entry it reconciles, adding any newly-classpath package.

## Discover sources

Partition, fan out, reconcile:

```bash
uv run scripts/generate.py partition discover
```

It reads `coverage.yaml`, extracts the project-used members, drops those already verdicted in `classification.yaml`, and writes balanced plans to `tracking/rules/plans/lib-NNN.yaml` (their paths printed). Fan out discover-attack-surface, one agent per plan (capped). Inputs each: `project-root`, `language`, `plan` (the plan path). Each records the sources it finds in its plan and writes each package's source unit (a package fully covered by built-ins gets none).

At the join:

```bash
uv run scripts/generate.py mark-safe
```

It merges every plan's verdicts into the durable `classification.yaml` ledger and prunes the consumed plans. Discover is a single fan-out pass, not a loop. `verify.py status` confirms `discover: done`.

## Source lib rules

For each source unit `verify.py` lists as not passing, a two-step pipeline dispatched one step at a time (step N only after step N−1's artifact):

1. create-test-project — Inputs: `project-root`, `language`, `type: rule-source`, `unit` (the package-kebab). It reads the unit's sources and dependencies, scaffolds and compiles the `sources/` marker project, sets the unit's `test_project: done`.
2. create-rule — Inputs: `project-root`, `language`, `side: sources`, `unit`. It authors the source lib rules + a throwaway test join and iterates until every sample passes, setting each source's `rule_id` and `tests_passing: done`.

`verify.py status` confirms `source_rules: done`.

## Assemble source joins

Dispatch assemble-lib-rules. Inputs: `project-root`, `language`. It reads the source units and wires the created sources to the built-in sinks for the first scan — one join per created-source × built-in-sink — and writes the joins tally. These carry no test project; the scan verifies them.
