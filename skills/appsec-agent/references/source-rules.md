# Discover sources + source rules

The deep pass starts with sources only — author source rules, wire them to the built-in sinks for the first scan, and let the taint frontier name the sinks later. On a re-entry over changed code, re-run triage-dependencies and re-run the discover partition: it re-plans only members no prior run verdicted, so unchanged surface is skipped automatically. Existing source rules and their `done` status are the baseline, not work to redo.

## Triage dependencies

Delegate triage-dependencies. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It reads `project.yaml`'s dependency list and writes `tracking/coverage.yaml` — a flat list of the packages that could introduce a source the built-ins don't already cover. On a re-entry it adds any newly-classpath package; a flagged package's shifted usage needs no re-open — the discover partition auto-plans its used members not yet verdicted

## Discover sources

Partition the pending libraries' project-used members into balanced plans, then fan out one agent per plan:

```bash
uv run scripts/partition-methods.py discover
```

It reads `coverage.yaml`'s flagged packages, extracts their project-used members, drops any member already verdicted in `tracking/rules/classification.yaml`, and writes ~50-member plans to `tracking/rules/plans/lib-NNN.yaml`, printing their paths. Fan out discover-attack-surface in parallel, one agent per plan. Inputs each: `<plan>` the plan path, deps-dir `.opentaint/project/dependencies`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. Each agent records the sources it finds in its plan and writes each package's source unit to `tracking/rules/sources/<package-kebab>.yaml` (a package fully covered by built-ins gets no unit).

At the join: run `uv run scripts/mark-safe.py` once — it merges every plan's `source` and computed `safe` (members − sources) into the durable `tracking/rules/classification.yaml` ledger the next partition excludes, then delete the `plans/` files (regenerable). Discover is a single fan-out pass, not a loop: set `phases.discover: done` once every plan's agent has returned and mark-safe has recorded the ledger.

## Source lib rules

Build the source lib rules from the `tracking/rules/sources/<package-kebab>.yaml` units that carry unbuilt sources. Fan out per package (capped); each is a two-step pipeline, dispatched one step at a time after the prior step's artifact:

1. create-test-project — Inputs: `<spec>` = the unit's sources, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/sources/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the unit, `build_jdk` if set. Scaffolds the `sources/` marker project (`test rule init --sources-only`), writes the marker samples, compiles it. Sets `test_project: done`
2. create-rule — Inputs: `<tracking-file>` `.opentaint/tracking/rules/sources/<name>.yaml` (the unit — both spec and where results are recorded), test-compiled `.opentaint/test-compiled/<name>`, test-project `.opentaint/test-projects/<name>`, rules-dir `.opentaint/rules`. Writes the package's source lib rules into `.opentaint/rules`, the `sources` test join against the marker, and iterates `test rule run` until every sample passes; sets `tests_passing: done` and each source's `rule_id`

Set `phases.source_rules: done` once every unit's source side is `tests_passing: done`.

## Assemble source joins

Delegate assemble-lib-rules to wire the new sources to the built-in sinks for the first scan. Inputs: source-units `.opentaint/tracking/rules/sources`, sink-units `.opentaint/tracking/rules/sinks`, rules-dir `.opentaint/rules`, tracking-dir `.opentaint/tracking`. It writes one `.opentaint/rules/java/security/<class>-<sink>-lib-ext.yaml` per created-source × built-in-sink combination plus the `tracking/rules/joins/<class>.yaml` tally. These carry no test project, the scan verifies them.
