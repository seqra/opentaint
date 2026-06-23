# Approximation iteration

Every dropped method must end up modeled (a passthrough/dataflow unit) or in `skipped.yaml` — no exceptions. Classify on each method's intrinsic propagation (model carriers, skip non-carriers); don't weigh whether it's on a source→sink path here — that's the analyzer's job. `check-coverage.py` is the gate: it lists every dropped method not yet in a unit (`methods:`/`done:`) or `skipped.yaml`, and the loop isn't done while it reports any.

Existing units are trusted — an FQN already in a unit's `done:` is never re-derived; the loop only builds methods the current scan newly drops (a unit's pending `methods:`), and re-applies every existing unit on each rescan.

Loop until stabilization:

1. analyze-external-methods — Inputs: dropped-file `.opentaint/results/dropped-external-methods.yaml`, tracking-dir `.opentaint/tracking`, `<project-root>`. Appends newly-dropped FQNs to each unit's `methods:` or to `skipped.yaml`, and self-checks with `check-coverage.py`. Returns one line per unit
2. Fan out per unit with a non-empty `methods:` (capped — they compile and scan); a unit with empty `methods:` is already built. The build skill moves each finished FQN `methods:`→`done:`:
   - passthrough → create-pass-through-approximation — Inputs: `<methods>` (the unit's pending FQNs), `<tracking-file>`, config-file `.opentaint/pass-through/<name>.yaml`. Write-only; sets `written` + `artifact`
   - dataflow → two sequential dispatches: create-test-project (dataflow shape, pass `build_jdk` if set) produces `.opentaint/test-compiled/<name>` and sets `test_project: done`; then create-dataflow-approximation against that model (approx-src `.opentaint/dataflow/<name>`) sets `tests_passing` + `artifact`
3. Re-scan with both approximation dirs pointing at the parents (`.opentaint/pass-through`, `.opentaint/dataflow`)
4. Verify: the rescan's scan agent reports any method you modeled that's still in `dropped-external-methods.yaml`, plus any config load error (`check-coverage.py` won't — a modeled method sits in `done:`). Fix each:
   - passThrough still dropped → re-invoke create-pass-through-approximation. If it won't converge (~2 fixes, no clear cause), re-plan it as dataflow: move its FQN out of the passThrough unit, drop its passThrough config, and run create-test-project → create-dataflow-approximation (the dataflow overrides the passThrough)
   - dataflow still dropped despite passing its isolated test → escalate (references/escalation.md)
   - can't be made to work even after escalation → move its FQN to `skipped.yaml` (with an "escalated — could not be modeled" comment), remove it from the unit and its config/source. It's now a skip, so it stops blocking
5. Stabilization: run check-coverage.py yourself from the project root (zero-arg, deterministic — run it directly, not via a subagent). Stabilized when it reports `0 UNCOVERED`, every unit's `methods:` is empty, step 4 surfaced nothing still-dropped, and the rescan added no new methods. Otherwise its listed methods go back to step 1, and any still-dropped modeled method to step 4

Set `phases.approximations: in_progress` across the loop, `done` at stabilization.
