# Escalation block

Invoked from inside a stage when an item won't converge. A leaf reports a rule or approximation it couldn't make work after its own retries — with the brief cause it found — and leaves it pending; the scan can also flag a created rule that fires wrong, leave a built approximation still dropped, or fail to load a malformed one. The reported item plus its brief cause is enough to act: handle it here, don't re-dispatch blindly, and don't run debug-rule.

A scan-flagged rule is not immediately terminal: when a rescan flags a created rule that fails to load, or a join that should fire but didn't, first re-dispatch create-rule with `fix-target` (the flagged rule's `<path>#<id>` plus the false positive/negative to correct) to adjust that one rule, then rescan. Only when it still won't converge after that does it go terminal — step 1 then step 2.

### 1. Dispatch report-analyzer-issue

Inputs:
- `project-root`
- `artifact` — the rule's full id (+ ruleset), or the approximation's target method(s)
- `diagnosis` — the leaf's brief cause
- `name` (optional) — the test project the item was traced on

Expect back — the issue written to `.opentaint/issues/<slug>.md`.

### 2. Mark the item terminal

So the pipeline stops returning to it:

- a rule unit that won't converge → add a one-line `blocker` string at the top of its unit file, `.opentaint/tracking/rules/{sources,sinks}/<unit>.yaml`; `scripts/get_status.py` then settles the unit.
- an approximation method → append it to the `engine_issues` list of its owning batch (grep `.opentaint/tracking/approximations/*.yaml` for the method to find the batch), quoting method and signature so the array descriptor stays valid YAML:

  ```yaml
  - { method: "cn.hutool.core.lang.Assert#notNull", signature: "(Ljava/lang/Object;Ljava/util/function/Supplier;)Ljava/lang/Object;", reason: "one line on why the engine can't carry it" }
  ```

  `scripts/get_status.py` then treats the method as terminal, and the next `scripts/generate.py merge-skipped` carries it into `skipped.yaml`.

A malformed approximation is not an engine issue: when run-scan reports a config-load failure naming the offending file, re-dispatch the authoring skill (create-pass-through-approximation / create-dataflow-approximation, `language` + `batch`) to fix that file, then rescan.
