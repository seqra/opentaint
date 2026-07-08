# Scan

Dispatch run-scan. Inputs: `project-root`; `max-memory` = `state.yaml.max_memory` when it's set. The skill scans `.opentaint/project` with the built-in ruleset plus `.opentaint/rules`, applies `.opentaint/pass-through` and `.opentaint/dataflow` whenever those dirs exist, and emits `dropped-external-methods.yaml` (its `--track-external-methods` output). The approximation loop consumes that file on normal/deep runs; a lite run simply ignores it. It handles its own OOM retry (up to 16G) and timeout.

Existing approximations apply on every scan, any level — the level gates whether new approximations are generated, not whether existing ones are applied, so a lite rescan still sees a prior deep run's coverage.

Record `max_memory: 16G` if run-scan reports it only succeeded at 16G, and pass it to every later run-scan.

A scan that produced a SARIF — even with a timeout or OOM message — is done. Only when no valid SARIF comes out even at 16G is it a real failure (run-scan returns the `resource` setup): stop the workflow (nothing to triage) and dispatch report-analyzer-issue with that setup.

`verify.py status` confirms `scan: done`; on normal/deep its approximations block then shows what is `UNCOVERED`, unbuilt, or awaiting a rescan. If it flags a created rule the scan couldn't load, a join that should fire but didn't, or an own rule that false-positives, route it through escalation (references/escalation.md) and rescan before continuing.
