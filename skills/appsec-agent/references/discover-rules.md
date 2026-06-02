# Discover + new rules

## Triage dependencies

Delegate triage-dependencies. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It reads `project.yaml`'s dependency list and writes `tracking/coverage.yaml` (`package` / `status` / `notes`) — one `status: pending` entry per library that could introduce a source or sink, dismissals summarised — returning one line per flagged library. Don't ask for the full list back.

## Discover attack surface

Fan out discover-attack-surface in parallel, one agent per `pending` package in `coverage.yaml`. Inputs each: `<package>`, `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`, surface `.opentaint/tracking/surface.yaml`. This phase only describes ideas — each agent catalogues the package's untrusted-data sources and dangerous sinks into `surface.yaml` (new patterns vs a built-in ref; sinks tagged by vuln class), writes no rule and runs no test, then flips its `coverage.yaml` entry to `done`. Returns the sources/sinks found.

## Assemble lib rules

Once the discover fan-out is done, delegate assemble-lib-rules. Inputs: surface `.opentaint/tracking/surface.yaml`, tracking-dir `.opentaint/tracking`. With the whole surface in one view it groups sinks by vuln class and writes one `tracking/rules/<name>.yaml` join requirement per class (every source + that class's sink group, new combinations only) — still description, not rule files. One agent for the global view; fan out by vuln class only if the surface is large.

Then a quick area cross-check: across network, persistence, environment, serialization, rendering, naming, execution, messaging — is every boundary a dependency exposes either covered by built-ins or now carrying a join requirement? If a boundary has a relevant dependency but produced no requirement and no clear reason, dispatch a depth pass for it. Set `phases.discover: done` once every `coverage.yaml` entry is `done` and the join requirements are written.

## Rules

Write and test the rules from the join requirements in two passes — sources first (one agent, since a new source is shared across every class's join), then sinks + joins in parallel.

**Pass 1 — source lib rules (one agent).** Dispatch one create-rule to author every new source lib rule the requirements name (the `new:` sources across `tracking/rules/*.yaml`). Inputs: requirements = the `new:` sources, rules-dir `.opentaint/rules`. A source lib rule isn't testable alone — it's verified by the joins that ref it in pass 2. Wait for it to finish before pass 2, so the joins can ref the source rules it wrote.

**Pass 2 — sinks + joins (parallel, per vuln class).** Fan out across the `tracking/rules/<name>.yaml` join requirements. Each unit is a two-step pipeline — dispatch the steps one at a time, waiting for the prior step's artifact:

1. create-test-project — Inputs: spec = the requirement's `sources`/`sinks`, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the requirement. Writes synthetic samples — each new sink fed by a known built-in source, each source (incl. the pass-1 ones) into the class's sink. Sets `test_project: done`
2. create-rule — Inputs: requirements (the tracking file), test-compiled `.opentaint/test-compiled/<name>`, rules-dir `.opentaint/rules`, `<tracking-file>`, and on a re-dispatch the approximation dirs `.opentaint/pass-through` / `.opentaint/approximations`. Writes the class's new sink lib rules + the join (ref every source), iterates `opentaint test rule run` until every sample passes; sets `tests_passing: done`, `rule_id`, `artifact`

If create-rule reports the test project drops a library method on the rule's flow, the rule can't be verified until that method is modeled — route the dropped methods through the approximation loop (references/approximations.md; they're real library methods the main scan needs too), then re-dispatch create-rule with the approximation dirs. If it reports non-convergence with nothing dropped, load references/escalation.md. A join's `tests_passing` stays `pending` until its samples pass; set `phases.rules: done` once every join's is done.
