`.opentaint/tracking/approximations/<batch>.yaml` — one batch's callable classification, `<batch>` the plan's filename stem. Every callable sits in exactly one verdict bucket, keyed with the exact language-specific `method` and `signature` from the plan so distinct variants stay separate:
- `passthrough`, `dataflow` — modeled carriers; each entry `{ method, signature }`
- `skipped` — terminal non-carriers; each `{ method, signature, reason }`
- `engine_issues` — a separate bucket for carriers the engine provably can't propagate (built but still dropped); each `{ method, signature, reason }`. Terminal and treated just like `skipped` — the only difference is the reason. `merge-skipped` carries it into `skipped.yaml` as its own `engine_issues` group alongside the regular skipped `methods`.

`dependencies` lists the dependency identifiers a dataflow test project needs. The `build` block tracks the build — `test_project` records each dataflow method's test-project status (`done` if a sample was written into the batch's test project, `failed` if none could be written so the method was excluded from it), and `done` holds the finished `{ method, signature }`. Keep it clear from comments

```yaml
passthrough:
  - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
dataflow:
  - { method: "<qualified-member-b>", signature: "<language-signature-b>" }
skipped:
  - { method: "<qualified-member-c>", signature: "<language-signature-c>", reason: "retains none of its input data" }
engine_issues: []
dependencies: []
build:
  test_project:
    - { method: "<qualified-member-b>", signature: "<language-signature-b>", status: done }
  done: []
```
