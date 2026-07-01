# Approximation iteration

Every dropped method must end up classified — in a `passthrough`/`dataflow`/`skipped`/`engine_issues` bucket of some batch file — and then built (its `build.done`) or left skipped. On a deep run analyze also records possible sinks: every dropped method is reached by source-derived taint, so analyze flags the dangerous ones into per-package sink units under `rules/sinks` for the sink-authoring pass — pass it the sinks dir so it does.

Built methods are trusted — an FQN already in a batch's `build.done` is never re-derived; the loop only builds methods the current scan newly drops, and re-applies every existing approximation on each rescan.

Loop until stabilization:

1. Classify the frontier. Partition the dropped methods into batches, then fan out analyze-external-methods one per batch:

   ```bash
   uv run scripts/partition-methods.py analyze
   ```

It groups the dropped methods by library root into batches of ~20 (roots with few methods pooled into one `misc` batch, a class over the budget kept whole in its own batch), writing one self-contained plan per batch to `tracking/approximations/plans/<batch>.yaml` and printing their paths. Dispatch analyze-external-methods per batch (capped) — Inputs: `<plan>` the plan path, tracking-dir `.opentaint/tracking`, `<sinks-dir>` `.opentaint/tracking/rules/sinks` only on a deep run, `<project-root>`. Each writes `approximations/<batch>.yaml` (classification buckets) and, on a deep run, the possible sinks into per-package units under `rules/sinks`; it self-checks with `check-coverage.py --batch <id>`. At the join, run `uv run scripts/merge-skipped.py` to rebuild `approximations/skipped.yaml` from every batch's `skipped`/`engine_issues` (union), then delete the `plans/` files — partition re-derives them from whatever stays unclassified
2. Build per batch (capped) — a batch needs building while a `passthrough`/`dataflow` entry is not yet in its `build.done`; the build skills append finished methods there:
   - passthrough → one create-pass-through-approximation per batch — Inputs: `<methods>` the batch's `passthrough` entries, `<tracking-file>` the batch file, config-dir `.opentaint/pass-through`. It writes one config per package and appends to `build.done`
   - dataflow → per dataflow class in the batch, two sequential dispatches: create-test-project (dataflow shape, pass `build_jdk` if set) produces `.opentaint/test-compiled/<class-kebab>` and sets `build.test_projects[<class>]: done`; then create-dataflow-approximation against that model (approx-src `.opentaint/dataflow/<class-kebab>`) appends the class's methods to `build.done`
3. Re-scan with both approximation dirs pointing at the parents (`.opentaint/pass-through`, `.opentaint/dataflow`)
4. Verify: the rescan's scan agent reports any method you modeled that's still in `dropped-external-methods.yaml`, plus any config load error. Fix each:
   - passThrough still dropped → re-invoke that batch's create-pass-through-approximation. If it won't converge (~2 fixes, no clear cause), re-plan it as dataflow: move its entry to the batch's `dataflow` bucket, drop its passThrough config entry, and run create-test-project → create-dataflow-approximation (the dataflow overrides the passThrough)
   - dataflow still dropped despite passing its isolated test → escalate (references/escalation.md)
   - can't be made to work even after escalation → move its entry to the batch's `engine_issues`, remove its config/source, and file it with report-analyzer-issue

   Never move a method into `skipped` yourself — only analyze-external-methods skips, and only from the source. A stubborn carrier keeps iterating through build and escalation (`passthrough→dataflow`, then `engine_issues`); it is never parked in `skipped` to end the loop
5. Stabilization is about the dropped methods, not the SARIF. Run check-coverage.py yourself from the project root; the loop is done only when it reports `0 UNCOVERED` — every dropped method classified and every `passthrough`/`dataflow` entry in its batch's `build.done`. Until then keep going: each rescan with freshly-built approximations reaches further into the code and drops new methods, so expect several rounds (commonly 5+). A method check-coverage still lists goes back to step 1; a modeled method still in `dropped-external-methods.yaml` goes back to step 4. Don't stop because the SARIF stopped changing or the obvious methods are done — stop only when no dropped method is left unclassified

Set `phases.approximations: in_progress` across the loop, `done` at stabilization
