Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/approximations/<batch>.yaml` — the batch classification (per Tracking)
- `.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — the per-package sink units, when `sinks` was set (per Tracking)

### Summary:

- per-kind method counts (passthrough / dataflow / skipped) and the sink count when `sinks` was set
- that `check-coverage.py --batch <batch>` reports `0 UNCOVERED`
