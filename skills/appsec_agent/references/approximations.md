# Approximation iteration

The step that models the library methods killing taint, run on normal and deep after the first scan, looping to stabilization. The rescans are part of this block — load references/scan.md for each. Dispatch per the Delegate template in SKILL.md.

Loop until stabilization:

1. analyze-external-methods — Inputs: dropped-file `.opentaint/results/dropped-external-methods.yaml`, tracking-dir `.opentaint/tracking`, `<project-root>`. Writes one `approximations/<package>-passthrough.yaml` and/or `<package>-dataflow.yaml` per package, plus `skipped.yaml`, only for methods not already in a unit. Returns one line per unit
2. Fan out per unit:
   - passthrough → create-pass-through-approximation — Inputs: `<methods>` from the unit, `<tracking-file>`, config-file `.opentaint/config/<name>.yaml`. Write-only; sets `written` + `artifact`. No test project
   - dataflow → create-test-project (dataflow shape) then create-dataflow-approximation — test-compiled `.opentaint/test-compiled/<name>`, approx-src `.opentaint/approximations/src/<name>`. Sets `test_project`, then `tests_passing` + `artifact` (test-approximations auto-applies its own fixed rule — nothing to pass)
3. Re-scan (references/scan.md) with both approximation dirs pointing at the parents (`.opentaint/config`, `.opentaint/approximations/src`)
4. Pass-through verify (no separate skill): the scan agent reports any method you modeled that is still in `dropped-external-methods.yaml`, or any config load error. Re-invoke that package's create-pass-through-approximation agent to fix (matcher / from→to / YAML), then rescan. A dataflow method that still drops despite passing its isolated test is an escalation case (references/escalation.md), not a re-write
5. Stabilization: stop when no method on a source→sink path remains unmodeled and a rescan surfaces no new such methods (equivalently, byte-equal SARIF across rescans). Otherwise feed the newly dropped methods back into step 1

Set `phases.approximations: in_progress` across the loop, `done` at stabilization.
