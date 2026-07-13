# Approximation iteration

Models the library methods the scan drops so taint keeps propagating: every dropped method ends classified into a batch bucket, then built into a working carrier or left terminal. It is a loop — each rescan reaches further and drops new methods.
Gate: `get_status.py` reports `approximations` `DONE` once every dropped method is classified and every carrier is built or terminal; otherwise it names the current loop state and the exact plans/batches/methods to hand out. It is the loop condition: re-run it after each step, dispatch only what it lists.

Every dropped method must end classified — in a batch's `passthrough`/`dataflow`/`skipped`/`engine_issues` bucket — then built (`build.done`) or left a non-carrier. On a deep run, analyze-external-methods also flags dangerous methods as sinks into per-package sink units for the sink pass; pass the `sinks` flag so it does.

### 1. Classify the frontier

`get_status` lists the unclassified methods, then the plans once they are split. Split the still-unclassified dropped methods into batch plans:

```bash
uv run scripts/generate.py partition analyze
```

It re-plans only the still-unclassified frontier, so re-running it after each rescan picks up only the newly-dropped methods. Then fan out analyze-external-methods, one per plan (capped).

Inputs (each):
- `project-root`
- `language`
- `plan` — the batch plan `.opentaint/tracking/approximations/plans/<batch>.yaml` get_status names
- `sinks` (deep only) — flag: also classify dangerous methods as sinks

Expect back — each batch file's `passthrough`/`dataflow`/`skipped` buckets filled (with `sinks`, its per-package sink units too). At the join:

```bash
uv run scripts/generate.py merge-skipped
```

merges every batch's `skipped`/`engine_issues` into `approximations/skipped.yaml`.

### 2. Build the unbuilt batches

get_status lists the batches with an unbuilt carrier, by kind:
- passthrough → create-pass-through-approximation. Inputs: `project-root`, `language`, `batch` (and optionally `methods` to redo a subset)
- dataflow → two sequential dispatches per batch: create-test-project (`project-root`, `language`, `type: dataflow`, `batch`), then create-dataflow-approximation (`project-root`, `language`, `batch`)

Expect back — the built carriers appended to each batch's `build.done`; `get_status` stops listing a batch once its carriers are built.

### 3. Rescan

`get_status` reports `approximations built after the last scan`. Dispatch run-scan. A fresh build reaches further and drops new methods, so expect several rounds back through step 1.

### 4. Escalate a built-but-still-dropped method

get_status reports `built but still dropped … escalate` for a method in `build.done` the scan still drops — it isn't propagating. Escalate (references/escalation.md), which records it as an engine issue rather than re-dispatching it indefinitely. Never record a carrier in `skipped` yourself — only analyze-external-methods writes `skipped`, and only from the source; the escalation step is the one place you write terminal state.

Run `uv run scripts/get_status.py` after each step and loop 1–4 until it reports `approximations` `DONE`.
