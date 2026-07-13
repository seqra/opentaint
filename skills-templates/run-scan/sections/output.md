Short and concise report of what was done

### Artifacts:

All three sit next to the report under `.opentaint/results/`:

- `.opentaint/results/report.sarif` — findings with code-flow traces
- `.opentaint/results/dropped-external-methods.yaml` — external methods where dataflow facts were killed for lack of a model
- `.opentaint/results/approximated-external-methods.yaml` — external methods already modeled

### Summary:

- finding count, and dropped-vs-approximated external-method counts
- whether memory was bumped to 16G
- if the scan failed at config-load on a malformed approximation: the engine error and the offending file under `.opentaint/pass-through` or `.opentaint/dataflow` (located from the error), so it can be fixed and rescanned — this is not an out-of-memory failure and 16G won't help
- if no SARIF came out even at 16G: that the scan is left failed, with the setup used (full scan command with ruleset, approximation dirs, model)
