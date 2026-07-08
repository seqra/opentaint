Short and concise report of what was done

### Artifacts:

All three sit next to the report under `.opentaint/results/`:

- `.opentaint/results/report.sarif` — findings with code-flow traces
- `.opentaint/results/dropped-external-methods.yaml` — external methods where dataflow facts were killed for lack of a model
- `.opentaint/results/approximated-external-methods.yaml` — external methods already modeled

### Summary:

- finding count, and dropped-vs-approximated external-method counts
- whether memory was bumped to 16G
- if no SARIF came out even at 16G: that the scan is left failed, with the setup used (full scan command with ruleset, approximation dirs, model)
