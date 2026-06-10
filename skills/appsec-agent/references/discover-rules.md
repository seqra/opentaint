# Discover + new rules

## Triage dependencies

Delegate triage-dependencies. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It reads `project.yaml`'s dependency list and writes `tracking/coverage.yaml` (`package` / `status` / `notes`) — one `status: pending` entry per library that could introduce a source or sink, dismissals summarised — returning one line per flagged library. Don't ask for the full list back.

## Discover attack surface

Fan out discover-attack-surface in parallel, one agent per `pending` package in `coverage.yaml` (capped per SKILL.md § Resource limits). Inputs each: `<package>`, deps-dir `.opentaint/project/dependencies`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. Each agent first scopes the package to functions/classes used by the project, running discover-attack-surface's bundled `scripts/package-usages.sh` and saving the package's method usages to `tracking/usage/<package-kebab>.yaml`, then reviews source/config for indirect reachability. It settles built-in coverage for that used scope (full ⇒ no unit, just `coverage.yaml` done; partial ⇒ expand only the missing used methods; none ⇒ plan used members from scratch). It writes the package's project-used rule plan `tracking/rules/lib/<package-kebab>.yaml` (new vs expand; sinks tagged by vuln class), writing no rule and running no test, then flips its `coverage.yaml` entry to `done`. Returns the sources/sinks planned.

Then a quick area cross-check over project-used boundaries only: across network, persistence, environment, serialization, rendering, naming, execution, messaging — is every boundary the project reaches through a dependency either covered by built-ins or now carrying a lib unit? If a reachable boundary has a relevant dependency but produced no unit and no clear reason, dispatch a depth pass for it. Set `phases.discover: done` once every `coverage.yaml` entry is `done`.

## Per-package lib rules

Build the lib rules from the `tracking/rules/lib/<package-kebab>.yaml` units. Fan out per package (capped per SKILL.md § Resource limits — each unit compiles and scans); each unit is a two-step pipeline, dispatched one step at a time after the prior step's artifact:

1. create-test-project — Inputs: `<spec>` = the lib unit's sources/sinks, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/lib/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the unit. Scaffolds the `sinks/` and/or `sources/` marker projects (`test rule init`, `--sinks-only`/`--sources-only` for a one-sided package), writes the generic-marker counterpart samples, compiles each sub-project. Sets `test_project: done`
2. create-rule — Inputs: requirements (the lib unit), test-compiled `.opentaint/test-compiled/<name>`, test-project `.opentaint/test-projects/<name>`, rules-dir `.opentaint/rules`, `<tracking-file>`, and on a re-dispatch the approximation dirs `.opentaint/pass-through` / `.opentaint/dataflow`. Writes the package's source lib rules + per-vuln-class sink lib rules into `.opentaint/rules`, the test joins against the markers into each test project's `test-rules`, and iterates `test rule run` per sub-project until every sample passes; sets `tests_passing: done` and the lib rules' `rule_id`s/`artifact`

If create-rule reports the test project drops a library method on the rule's flow, route the dropped methods through the approximation loop (references/approximations.md), then re-dispatch create-rule with the approximation dirs. If it reports non-convergence with nothing dropped, load references/escalation.md. Set `phases.rules: done` once every lib unit's `tests_passing` is done.

## Assemble joins

Once the per-package lib rules are done, delegate assemble-lib-rules. Inputs: lib-units `.opentaint/tracking/rules/lib`, rules-dir `.opentaint/rules`, tracking-dir `.opentaint/tracking`. With every created lib rule in one view it writes the security joins — one `tracking/rules/join/<class>.yaml` per vuln class (listing its joins) plus one `.opentaint/rules/java/security/<class>-<sink>-lib-ext.yaml` per join (a join refs exactly one sink, so a class with several sinks yields several joins) — merging built-in + created sources with the new sinks, and created sources with built-in sinks (new-end combinations only). These carry no test project; the main scan verifies them (references/scan.md). One agent for the global view; fan out by vuln class only if there are many.
