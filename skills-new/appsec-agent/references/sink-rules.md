# Author sinks + assemble + rescan

The approximation loop recorded the sinks the project's untrusted data can reach in per-package sink units. Author the sink rules, join them to every source, and rescan to surface the findings. `verify.py status` drives each sub-step's `next:`.

## Sink lib rules

For each sink unit `verify.py` lists as not passing, a two-step pipeline dispatched one step at a time:

1. create-test-project — Inputs: `project-root`, `language`, `type: rule-sink`, `unit` (the package-kebab). Reads the unit's sinks and dependencies, scaffolds and compiles the `sinks/` marker project, sets `test_project: done`.
2. create-rule — Inputs: `project-root`, `language`, `side: sinks`, `unit`. Authors the sink lib rules + test join, iterates until passing, sets each sink's `rule_id` and `tests_passing: done`. If a sample drops a library method on its flow, that's an approximation gap — route it through the approximation loop first (references/approximations.md), then re-dispatch.

## Assemble the full joins

Dispatch assemble-lib-rules. Inputs: `project-root`, `language`. With the sinks now created it writes every source (built-in + created) × created-sink join, extending the joins tally.

## Final rescan

Dispatch run-scan (references/scan.md) so the new sink rules and joins fire — this SARIF is what triage reads. `verify.py status` confirms `sink_rules: done`.
