Short and concise report of what was done

### Artifacts

- `.opentaint/test-compiled/<name>` — the compiled test model a later stage runs against; report each path and the exact `compile` command used
- `.opentaint/test-projects/<name>` — the sample sources alongside the model

### Summary

- the number of samples written per case
- any method excluded because no sample could be written (marked `failed`), with a brief reason
- failed projects (if any)
