# Debugging taint drops — fact-reachability

When a sample won't pass (or a scan misses a flow) and the cause isn't obvious, trace where taint dies instead of guessing. `test rule reachability` runs one rule and emits a per-instruction fact-reachability trace: the last instruction still carrying the taint fact, and the first where it's gone — the gap between them is where taint is killed.

## Command

```bash
opentaint test rule reachability <full-id> \
  --project-model <model-dir> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset <rules-dir>
```

- `<full-id>` — the one rule whose sample routes taint through the code under test (`<ruleSetRelativePath>.yaml:<shortId>`). One rule per run — across many rules the trace is unusably huge. Its library `refs` are collected automatically
- read the sibling `<results-dir>/debug-ifds-fact-reachability.sarif`, not the `-o` file. The `-o` SARIF only shows default scan output. The sibling holds the per-instruction facts that show where taint dies
- apply the approximations the failing run used so the trace matches it: `--passthrough-approximations <pass-through-dir>` and/or `--dataflow-approximations <dataflow-dir>`. Taint dying at an approximated call then means that approximation isn't propagating
- debug the exact run that showed the problem — same model, rulesets, approximation dirs — or you're debugging something else

## Reading the trace

- missed detection (a positive that won't pass, a flow absent from a scan): confirm a fact exists at the source — if none, the gap is in the sources, not the flow — then walk the facts to the last instruction still carrying it and the first where it's gone — that gap is the kill
- spurious detection (a negative that fires): the reverse — find where a fact appears with no tainted input reaching it

## Forcing an entry point (optional)

When you suspect the entry method is never reached, add `--entry-points "<method-fqn>"`. A finding that appears only with it points to entry-point discovery, not dataflow. On Spring the flag is additive, not restrictive: auto-discovered endpoints stay and your method is added; you can't narrow to one method.

## Confirming a dropped library method

When a positive won't pass and the suspicion is a library method on its flow dropping taint (not a rule bug), scan your own compiled sub-model with `--track-external-methods` and read the methods it lists as dropped:

```bash
opentaint scan --project-model .opentaint/test-compiled/<unit>/<side> \
  -o .opentaint/test-results/<unit>/<side>/diag.sarif \
  --ruleset builtin --ruleset .opentaint/rules --ruleset .opentaint/test-projects/<unit>/<side>/test-rules \
  --passthrough-approximations .opentaint/pass-through \
  --track-external-methods
```

Read `dropped-external-methods.yaml` next to the SARIF: a dropped method on the failing sample's source→sink path is the cause, not the rule — those methods need a model before the positive can pass. This diagnostic scan runs only over your own test sub-model, never the main project model.
