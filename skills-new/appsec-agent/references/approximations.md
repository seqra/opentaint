# Approximation iteration

Every dropped method must end classified — in a batch's `passthrough`/`dataflow`/`skipped`/`engine_issues` bucket — and then built (its `build.done`) or left skipped. On a deep run analyze also flags the dangerous methods as sinks into per-package sink units for the sink-authoring pass — pass the `sinks` flag so it does. A method already in a batch's `build.done` is trusted and never re-derived; each rescan re-applies every existing approximation.

Loop until `verify.py status` reports `approximations: done`. Each round it names the `next:` action for the current state:

1. `UNCOVERED > 0` — classify the frontier:

   ```bash
   uv run scripts/generate.py partition analyze
   ```

   It groups the dropped methods into per-root batches (paths printed). Fan out analyze-external-methods per batch (capped). Inputs each: `project-root`, `language`, `plan` (the plan path), `sinks` (flag, deep only). Each writes its batch classification and self-checks with `check-coverage.py --batch`. At the join:

   ```bash
   uv run scripts/generate.py merge-skipped
   ```

2. `unbuilt > 0` — build each batch that has an unbuilt entry:
   - passthrough → create-pass-through-approximation. Inputs: `project-root`, `language`, `batch` (and `methods` only to redo a subset). Writes one config per package, appends to `build.done`.
   - dataflow → two sequential dispatches per batch: create-test-project (Inputs: `project-root`, `language`, `type: dataflow`, `batch`) compiles the batch's dataflow test project; then create-dataflow-approximation (Inputs: `project-root`, `language`, `batch`) models against it and appends to `build.done`.

3. `rescan-pending` — dispatch run-scan (references/scan.md); a fresh build reaches further and drops new methods, so expect several rounds.

4. `built-but-still-dropped` — a method in `build.done` the current scan still drops means its approximation isn't propagating: escalate (references/escalation.md). A passThrough that won't converge is re-planned as dataflow; a carrier the engine truly can't model moves to the batch's `engine_issues` (which resolves it). Never park a carrier in `skipped` yourself — only analyze-external-methods skips, and only from the source.

`verify.py status` is the loop condition: `approximations: done` means 0 UNCOVERED, everything built, and the current scan reflects the latest build.
