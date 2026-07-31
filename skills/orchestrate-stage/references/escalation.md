# Escalation

Use when a leaf reports a rule or approximation it could not make work after its retries, when the latest scan still drops an already-built approximation, or when MAIN hands off a full-project scan that finished its allowed retry/backstop without producing SARIF.

## Full-scan resource issue

When the task supplies the failed scan `setup`, dispatch report-analyzer-issue.

Inputs:
- `setup` — the exact scan command, project model, rulesets, approximation dirs, final memory bound, current commit, and scan log path

Expect `.opentaint/issues/<slug>.md`; return it to MAIN and stop this stage. There is no rule/approximation terminal mark for a scan-wide resource failure.

## Rule or approximation issue

Handle the reported item here instead of re-dispatching it blindly, and don't run debug-rule.

A scan-flagged created rule that fails to load, false-positives/negatives, or belongs to a join that should fire but does not is not immediately terminal: first re-dispatch create-rule with `fix-target` — the rule's `<path>#<id>` plus the false positive/negative to correct — then finish with the project rescan as the next step. Only if it still does not converge does it go through the terminal flow below.

### 1. Dispatch report-analyzer-issue

Dispatch report-analyzer-issue before marking the item terminal.

Inputs:
- `artifact` — the rule's full id and ruleset, or the approximation target method(s)
- `diagnosis` — the leaf's one-line cause
- `name` (optional) — the known test-project unit/batch used for the failed check

Expect back — `.opentaint/issues/<slug>.md` written.

### 2. Mark the item terminal

The stage orchestrator writes the terminal mark after the reporting leaf returns; the leaf leaves the item pending and only reports its diagnosis. So the stage stops returning to it:

- source/sink rule unit → add one top-level `blocker` string to the known `.opentaint/tracking/rules/<side>/<unit>.yaml`
- approximation method → append it to the known owning batch's `engine_issues`, quoting method and signature:

```yaml
- { method: "cn.hutool.core.lang.Assert#notNull", signature: "(Ljava/lang/Object;Ljava/util/function/Supplier;)Ljava/lang/Object;", reason: "one-line engine limitation" }
```

After an approximation mark, run `uv run <skill-dir>/scripts/generate.py merge-skipped` so `approximations/skipped.yaml` reflects the terminal item.

A malformed approximation is not immediately an engine issue: re-dispatch its authoring skill with `language` + `batch` and, when the scan identifies the affected methods, that `methods` subset. The leaf repairs the existing package config or dataflow source even when those methods are already in `build.done`; unrelated existing carriers stay unchanged. Finish with the project rescan as the next step. If the repaired carrier is still dropped, use the terminal flow above.
