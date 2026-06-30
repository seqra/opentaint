# Approximation iteration

Every dropped method must end up modeled (a passthrough/dataflow unit) or in `skipped.yaml` — `methods` for a non-carrier, `engine_issues` for a carrier the engine can't model. On a deep run should also be recorded possible sinks: every dropped method is reached by source-derived taint, so analyze flags the dangerous ones into `rules/lib` for the sink-authoring pass — pass it the lib-rules dir so it does.

Existing units are trusted — an FQN already in a unit's `done` is never re-derived; the loop only builds methods the current scan newly drops, and re-applies every existing unit on each rescan.

Loop until stabilization:

1. Classify the frontier. Partition the dropped methods into plans, then fan out agents with analyze-external-methods one per plan:

   ```bash
   uv run scripts/partition-methods.py analyze
   ```

It writes one plan per package (≤20 methods, a bigger package split by sub-package/class) to `tracking/approximations/plans/ext-NNN.yaml`, printing their paths. Dispatch analyze-external-methods per plan (capped) — Inputs: `<plan>` the plan path, tracking-dir `.opentaint/tracking`, `<lib-rules-dir>` `.opentaint/tracking/rules/lib` only on a deep run, `<project-root>`. Each classifies its scopes into `<scope-kebab>-{passthrough,dataflow,skipped}.yaml`, records possible sinks into `rules/lib`, and self-checks with `check-coverage.py --plan <id>`. Returns one line per scope. At the join, merge every `<scope-kebab>-skipped.yaml` into a single `approximations/skipped.yaml` (union `methods` and `engine_issues`) and delete the per-scope skip files
2. Fan out per unit with a non-empty `methods`; a unit with empty `methods` is already built. The build skill moves each finished FQN `methods`→`done`. `<name>` below is the unit's `<scope-kebab>`:
   - passthrough → create-pass-through-approximation — Inputs: `<methods>` (the unit's pending FQNs), `<tracking-file>`, config-file `.opentaint/pass-through/<name>.yaml`. Write-only; sets `written` + `artifact`
   - dataflow → two sequential dispatches: create-test-project (dataflow shape, pass `build_jdk` if set) produces `.opentaint/test-compiled/<name>` and sets `test_project: done`; then create-dataflow-approximation against that model (approx-src `.opentaint/dataflow/<name>`) sets `tests_passing` + `artifact`
3. Re-scan with both approximation dirs pointing at the parents (`.opentaint/pass-through`, `.opentaint/dataflow`)
4. Verify: the rescan's scan agent reports any method you modeled that's still in `dropped-external-methods.yaml`, plus any config load error (`check-coverage.py` won't — a modeled method sits in `done`). Fix each:
   - passThrough still dropped → re-invoke create-pass-through-approximation. If it won't converge (~2 fixes, no clear cause), re-plan it as dataflow: move its FQN out of the passThrough unit, drop its passThrough config, and run create-test-project → create-dataflow-approximation (the dataflow overrides the passThrough)
   - dataflow still dropped despite passing its isolated test → escalate (references/escalation.md)
   - can't be made to work even after escalation → move its FQN to `skipped.yaml`'s `engine_issues` (it's a carrier the engine can't model), remove it from the unit and its config/source, and file it with report-analyzer-issue
5. Stabilization: run check-coverage.py yourself from the project root. Stabilized when it reports `0 UNCOVERED`, every unit's `methods` is empty, step 4 surfaced nothing still-dropped, and the rescan added no new methods. Otherwise its listed methods go back to step 1, and any still-dropped modeled method to step 4

Set `phases.approximations: in_progress` across the loop, `done` at stabilization
