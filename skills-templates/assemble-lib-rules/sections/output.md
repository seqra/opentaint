### Artifacts

- one join file per (vuln class, sink rule) under `.opentaint/rules/<lang>/security/<class>-<sink>-lib-ext.yaml`, each refing all relevant sources + its one sink
- `.opentaint/tracking/rules/joins/<class>.yaml` — one per vuln class, recording every join produced (per Tracking)

### Summary

- one line per join: class, sink, source count, and which ends are new
