# Approximation iteration

Every dropped method MUST end up either modeled (a passthrough/dataflow unit) or in `skipped.yaml` — no exceptions, no "good enough". This loop does not finish while any method in `dropped-external-methods.yaml` is still unclassified. Do not stop early because the important-looking ones are done, because a batch is large, or because the remaining methods seem minor — an unmodeled method silently kills taint and hides real findings. Keep iterating until the only thing left dropped is the skip set.

Loop until stabilization:

1. analyze-external-methods — Inputs: dropped-file `.opentaint/results/dropped-external-methods.yaml`, tracking-dir `.opentaint/tracking`, `<project-root>`. Writes one `approximations/<package>-passthrough.yaml` and/or `<package>-dataflow.yaml` per package, plus `skipped.yaml`, only for methods not already in a unit. Returns one line per unit
2. Fan out per unit (capped per SKILL.md § Resource limits — these units compile and scan):
   - passthrough → create-pass-through-approximation — Inputs: `<methods>` from the unit, `<tracking-file>`, config-file `.opentaint/pass-through/<name>.yaml`. Write-only; sets `written` + `artifact`. No test project
   - dataflow → two sequential dispatches per unit: first create-test-project (dataflow shape) produces `.opentaint/test-compiled/<name>` and sets `test_project: done`; on its return, dispatch create-dataflow-approximation against that model (approx-src `.opentaint/dataflow/<name>`) — sets `tests_passing` + `artifact` (`test approximation run` auto-applies its own fixed rule — nothing to pass)
3. Re-scan (references/scan.md) with both approximation dirs pointing at the parents (`.opentaint/pass-through`, `.opentaint/dataflow`)
4. Pass-through verify (no separate skill): the scan agent reports any method you modeled that is still in `dropped-external-methods.yaml`, or any config load error. Re-invoke that package's create-pass-through-approximation agent to fix (matcher / from→to / YAML), then rescan. When that agent reports the passThrough won't converge (after ~2 fixes, no clear cause), don't keep re-invoking it — a passThrough copy can't express this method's propagation. Re-plan that method as a dataflow unit (drop its passThrough config first so the two don't collide) and run it through the create-test-project → create-dataflow-approximation pipeline; the custom dataflow overrides the passThrough. A dataflow method that still drops despite passing its isolated test is an escalation case (references/escalation.md), not a re-write
5. Stabilization: keep classifying until every method in `dropped-external-methods.yaml` is either modeled (a passthrough/dataflow unit) or listed in `skipped.yaml`, and a rescan surfaces no new dropped methods — i.e. the only thing left dropped is the skip set. Otherwise feed the newly dropped methods back into step 1

Set `phases.approximations: in_progress` across the loop, `done` at stabilization.
