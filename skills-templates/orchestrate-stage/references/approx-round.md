# Approximation round — classify + build

Model one frontier of library methods dropped by the latest project scan: classify each method into a batch bucket, then build its passthrough/dataflow carrier or settle it terminal. This is one round of the pipeline's approximation loop. Finish before the rescan; a later invocation handles the frontier exposed by that rescan.

## Built-but-still-dropped methods

If `get_status.py` reports `built but still dropped ... escalate`, the latest project rescan proved those carriers ineffective. Escalate each method per `<skill-dir>/references/escalation.md`.

## Classify the frontier

When status lists unclassified methods, split only that frontier:

```bash
uv run <skill-dir>/scripts/generate.py partition analyze
```

Fan out analyze-external-methods, one per generated plan.

Inputs each:
- `language`
- `plan`
- `sinks` (optional) — pass when the task requests dangerous methods to also be classified into per-package sink units

Expect back — every method classified into the batch's `passthrough` / `dataflow` / `skipped` / `engine_issues` bucket; with `sinks`, per-package sink units written too. Wait for every plan leaf, then join once:

```bash
uv run <skill-dir>/scripts/generate.py merge-skipped
```

It merges every batch's `skipped` / `engine_issues` into `approximations/skipped.yaml` and prunes the consumed plans.

## Build the unbuilt batches

`get_status.py` lists the batches with an unbuilt carrier by kind. Independent batches fan out in parallel.

- passthrough → dispatch create-pass-through-approximation
  - `language`
  - `batch`
  - `methods` (optional) — only an explicitly assigned subset to redo

On Go the dataflow branch never runs: there is no dataflow approximation, so a Go batch's `dataflow` bucket stays empty, no test project is scaffolded for it, and every carrier is a passThrough. A Go carrier that won't converge goes straight to escalation.

- dataflow step 1 (Java/JVM only) → dispatch create-test-project
  - `language`
  - `type: dataflow`
  - `batch`
- dataflow step 2, after its test project completes → dispatch create-dataflow-approximation
  - `language`
  - `batch`
  - `methods` (optional) — only an explicitly assigned subset to redo

Expect back — the built carriers appended to each batch's `build.done`; `get_status.py` stops listing a batch once its carriers are built. Escalate a non-converging method per `<skill-dir>/references/escalation.md`.

## Stage gate

`get_status.py` names unclassified methods, plans, unbuilt batches, or built-but-still-dropped methods. Delete this round's dataflow `test-compiled/` models and finish when its methods are classified and built or terminal. If status reports `approximations built after the last scan`, report the pending rescan and stop.
