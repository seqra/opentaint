---
name: debug-rule
description: Debug a rule or approximation that behaves unexpectedly by tracing where taint is dropped. Use when its samples won't pass after repeated attempts, or it passes tests but is wrong on a real scan
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Debug Rule

Diagnose why a rule or approximation behaves unexpectedly on a model by tracing where taint is dropped, and decide who owns the fix: the rule, a missing library model, or the engine.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `rule` (required) — the one rule whose sample or flow routes taint through the code under test, as `<ruleSetRelativePath>.yaml:<shortId>`. For an approximation, the rule whose sample routes taint through the approximated method
- `model` (required) — the project model where the behavior shows up

## Workflow

### 1. Reproduce and localize the kill

Reproduce the exact run that showed the problem — same `model`, rulesets, and applied approximation dirs — and trace where taint dies with a fact-reachability run:

```bash
opentaint test rule reachability <rule> \
  --project-model <model> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --passthrough-approximations .opentaint/pass-through \
  --dataflow-approximations .opentaint/dataflow
```

`<results-dir>` is `.opentaint/test-results/<name>` for a test model, `.opentaint/results` for the main scan. The per-instruction facts are in the sibling `<results-dir>/debug-ifds-fact-reachability.sarif`, not the `-o` file — the `-o` SARIF only shows whether the rule fired. Read that sibling to find the kill:

- a missed detection (a positive that won't pass, or a flow absent from a scan) — confirm a fact exists at the source; if none, the gap is in `pattern-sources`, not the flow. Otherwise walk the facts to the last instruction still carrying it and the first where it's gone — that gap is the kill
- a spurious detection (a negative that fires) — the reverse: find where a fact appears with no tainted input reaching it

Trace the exact run that misbehaved — a different `model` or ruleset traces something else; taint dying at an approximated call means that approximation isn't propagating. When the flow is missed and the entry method may never be analyzed, rerun with `--entry-points "<method-fqn>"`: a finding that appears only then is an entry-point-discovery problem, not dataflow. On Spring the flag is additive — auto-discovered endpoints stay and your method is added, so use it to force-include an endpoint the analyzer never starts from, not to narrow to one method.

### 2. Classify the cause

The killing instruction decides who owns the fix. An engine bug is by far the least likely — assume it last, only once the other two are ruled out; nearly every kill is a missing or wrong library model or a rule defect, both tedious to exclude but far more probable, and the tedium is no reason to jump to "engine". Three outcomes:

- the kill is at an external library method → a model issue. Cross-check `dropped-external-methods.yaml` from that run (a `--track-external-methods` scan regenerates it if absent): listed there means the method is unmodeled — the missing model is the cause, for the approximation stage to model. Not listed but a built-in claims to model it, yet taint dies here → that model is wrong for this case: a passThrough override applies at the rule level, so prefer one for the method; a dataflow override conflicts with built-ins at load, so fall back to a passThrough, or call it an engine issue when only a dataflow shape can express the propagation
- the kill is where the rule should have matched — a sanitizer misfires, a sink or source variant went unmatched → a rule defect, for rule authoring to fix
- the kill is a plain instruction the engine must propagate through (assignment, cast, field read, an already-modeled call), with the rule correct and the model complete → an engine issue

### 3. Report the diagnosis

This skill diagnoses and routes the fix — it doesn't author the rule or approximation, or re-run the pipeline. Report the diagnosis per Output.

## Output

### Artifacts

- `debug-ifds-fact-reachability.sarif` — the per-instruction fact-reachability trace the CLI emits next to the `-o` SARIF

### Summary

- the diagnosis: `file:line` and the instruction where taint is killed (or spuriously introduced), and which of the three causes owns the fix
- for an engine cause: the fact-reachability trace up to the last reachable fact (consumed by the engine-issue report), plus the exact debug command(s) and the model they ran against
