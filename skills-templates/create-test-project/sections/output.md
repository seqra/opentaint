Short and concise report of what was done

### Artifacts

- `.opentaint/test-projects/<name>` — the sample sources and the `rule-test.yaml` that records their verdicts. A later stage runs a Go test project from here
- `.opentaint/test-compiled/<name>` — Java only: the compiled test model a later stage runs against; report each path and the exact `compile` command used

### Summary

- the number of samples written per case
- any method excluded because no sample could be written (marked `failed`), with a brief reason
- failed projects (if any)
