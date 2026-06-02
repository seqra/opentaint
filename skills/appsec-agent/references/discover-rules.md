# Discover + new rules

## Triage dependencies

Delegate triage-dependencies. Inputs: `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`. It reads `project.yaml`'s dependency list and writes `tracking/coverage.yaml` (`package` / `status` / `notes`) — one `status: pending` entry per library that could introduce a source or sink, dismissals summarised — returning one line per flagged library. Don't ask for the full list back.

## Discover attack surface

Fan out discover-attack-surface in parallel, one agent per `pending` package in `coverage.yaml`. Inputs each: `<package>`, `<project-root>`, model-dir `.opentaint/project`, tracking-dir `.opentaint/tracking`, lib-pieces `.opentaint/tracking/lib-pieces.yaml`. Each works source-first — finds the package's attacker-controlled sources the app uses, pairs each to a dangerous sink as one `tracking/rules/<name>.yaml` join requirement (`description` stage + short requirements + every GAV the flow crosses), and parks any source or sink it couldn't pair in `lib-pieces.yaml`, then flips its `coverage.yaml` entry to `done`. Returns one line per proposed rule plus a loose-piece count.

## Assemble lib rules

Once the discover fan-out is done and `lib-pieces.yaml` has `pending` entries, delegate assemble-lib-rules. Inputs: lib-pieces `.opentaint/tracking/lib-pieces.yaml`, `<project-root>`, tracking-dir `.opentaint/tracking`. With every package's loose pieces in one view it pairs each into a join `tracking/rules/<name>.yaml` (source whose sink lives in another package, sink reached by a built-in source), and resolves every piece's `disposition` to a join name or `dropped: <reason>`. One agent — it needs the global view to dedup; fan out by vuln class only if the piece set is large.

Then a quick area cross-check: across network, persistence, environment, serialization, rendering, naming, execution, messaging — is every boundary a dependency exposes either covered by built-ins or now carrying a rule? If a boundary has a relevant dependency but produced no rule and no clear reason, dispatch a depth pass for it. Set `phases.discover: done` once every `coverage.yaml` entry is `done` and every `lib-pieces.yaml` entry is resolved.

## Rules

Fan out across rule units in parallel. Each unit is a two-step pipeline — dispatch the steps one at a time, waiting for the prior step's artifact before the next:

1. create-test-project — Inputs: spec = the rule's `requirements`, `<project-root>`, `<tracking-file>` `.opentaint/tracking/rules/<name>.yaml`, test-project `.opentaint/test-projects/<name>`, test-compiled `.opentaint/test-compiled/<name>`, dependencies from the tracking file. Sets `test_project: done`
2. create-rule — Inputs: requirements (the tracking file), test-compiled `.opentaint/test-compiled/<name>`, rules-dir `.opentaint/rules`, `<tracking-file>`, and on a re-dispatch the approximation dirs `.opentaint/pass-through` / `.opentaint/approximations`. Iterates `opentaint test rule run` until every sample passes; sets `tests_passing: done`, `rule_id`, `artifact`

If create-rule reports the test project drops a library method on the rule's flow, the rule can't be verified until that method is modeled — route the dropped methods through the approximation loop (references/approximations.md; they're real library methods the main scan needs too), then re-dispatch create-rule with the approximation dirs. If it reports non-convergence with nothing dropped, load references/escalation.md. A rule's `tests_passing` stays `pending` until its samples pass; set `phases.rules: done` once every rule's is done.
