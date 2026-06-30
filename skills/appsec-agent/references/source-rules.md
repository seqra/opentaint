# Discover sources + source rules

The deep pass starts with sources only — author source rules, wire them to the built-in sinks for the first scan, and let the taint frontier name the sinks later. On a re-entry over changed code, re-run triage-dependencies and re-run the discover partition: it re-plans only members no prior run verdicted, so unchanged surface is skipped automatically. Existing source rules and their `done` status are the baseline, not work to redo.

## Triage dependencies

Delegate triage-dependencies. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It reads `project.yaml`'s dependency list and writes `tracking/coverage.yaml` (`package` / `status` / `notes`) — one `status: pending` entry per library that could introduce a source the built-ins don't already cover. On a re-entry it also re-opens a prior `done` library to `pending` when its usage may have shifted since the last verdict

## Discover sources

Partition the pending libraries' project-used members into balanced plans, then fan out one agent per plan:

```bash
uv run scripts/partition-methods.py discover
```

It reads `coverage.yaml`'s pending packages, extracts their project-used members, drops any member a prior run already verdicted, and writes ~100-member plans to `tracking/rules/plans/lib-NNN.yaml`, printing their paths. Fan out discover-attack-surface in parallel, one agent per plan. Inputs each: `<plan>` the plan path, deps-dir `.opentaint/project/dependencies`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. Each agent records the sources it finds in its plan, writes each package's source rule plan to `tracking/rules/lib/<package-kebab>.yaml`, and returns the sources planned plus each package's built-in `coverage` verdict (full/partial/none).

At the join: run `uv run scripts/mark-safe.py` once — it fills every plan's `safe` (members − sources), completing the verdict ledger the next partition excludes. Then record each package's returned `coverage` in `coverage.yaml`, and flip a package's entry to `done` once its plans leave no unverdicted members. Set `phases.discover: done` once every `coverage.yaml` entry is `done`.

## Source lib rules

Build the source lib rules from the `tracking/rules/lib/<package-kebab>.yaml` units that carry pending sources. Fan out per package (capped); each is a two-step pipeline, dispatched one step at a time after the prior step's artifact:

1. create-test-project — Inputs: `<spec>` = the unit's sources, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/lib/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the unit, `build_jdk` if set. Scaffolds the `sources/` marker project (`test rule init --sources-only`), writes the marker samples, compiles it. Sets `test_project: done`
2. create-rule — Inputs: requirements (the unit), test-compiled `.opentaint/test-compiled/<name>`, test-project `.opentaint/test-projects/<name>`, rules-dir `.opentaint/rules`, `<tracking-file>`. Writes the package's source lib rules into `.opentaint/rules`, the `sources` test join against the marker, and iterates `test rule run` until every sample passes; sets `tests_passing: done` and the rules' `rule_id`s/`artifact`

Set `phases.source_rules: done` once every unit's source side is `tests_passing: done`.

## Assemble source joins

Delegate assemble-lib-rules to wire the new sources to the built-in sinks for the first scan. Inputs: lib-units `.opentaint/tracking/rules/lib`, rules-dir `.opentaint/rules`, tracking-dir `.opentaint/tracking`. It writes one `.opentaint/rules/java/security/<class>-<sink>-lib-ext.yaml` per created-source × built-in-sink combination plus the `tracking/rules/join/<class>.yaml` tally. These carry no test project, the scan verifies them.
