---
name: debug-rule
description: Debug a rule or approximation that behaves unexpectedly by tracing where taint is dropped. Use when its samples won't pass after repeated attempts, or it passes tests but is wrong on a real scan
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Debug Rule

Diagnose why a rule or approximation behaves unexpectedly on a model — samples that won't pass after repeated attempts, a missed flow, or a spurious finding on a real scan — by tracing where taint is dropped, and decide who owns the fix: the rule, a missing library model, or the engine

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Rule `<full-id>` — the single full rule ID to trace (`<ruleSetRelativePath>.yaml:<shortId>`); fact-reachability is always per-rule, so to debug an approximation trace the rule whose sample routes taint through the approximated method
- Project model `<model-dir>` — the model where the behavior shows up. Default: `.opentaint/test-compiled/<name>` for a test project, or `.opentaint/project` for a main scan
- Ruleset `<rules-dir>` — Default: `builtin` plus `.opentaint/rules`
- Output directory `<results-dir>` — where the debug SARIF lands. Default: `.opentaint/test-results/<name>` for a test model, or `.opentaint/results` for a main scan
- Dropped external methods `<dropped-file>` — the list from the run that showed the problem. Default: `dropped-external-methods.yaml` next to that run's SARIF
- Approximation directories `<config-dir>` / `<approx-dir>` (optional) — apply when the behavior depends on them, so the debug run matches the run that showed the problem. Default: `.opentaint/config`, `.opentaint/approximations/src`

## Workflow

### 1. Precondition — library model complete

Open `<dropped-file>` from the run that showed the problem. If any method on the source→sink path is listed, STOP and model it (passThrough or dataflow), re-run, then debug — that missing model is the cause, not the engine. A method you already approximated that is still listed means the approximation isn't matching the real signature; fix it there. Debug only once no method on the path remains; if no `<dropped-file>` exists, produce one with a `--track-external-methods` run

### 2. Localize the kill — fact-reachability SARIF

```bash
opentaint dev debug-fact-reachability <full-id> \
  --project-model <model-dir> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset <rules-dir>
```

When the thing under debug is an approximation (or the flow depends on one), append `--passthrough-approximations <config-dir>` / `--dataflow-approximations <approx-dir>` so the trace runs with it applied — taint dying at the approximated call then means the approximation isn't propagating: wrong signature (still in `<dropped-file>`), empty body, or wrong from→to. Read the separate `<results-dir>/debug-ifds-fact-reachability.sarif` (not the `-o` file). For a missed detection (a `@PositiveRuleSample` that won't pass, or a flow absent from a scan): confirm a fact exists at the source — if not, the gap is in `pattern-sources` — then walk the facts to the last instruction still carrying the fact and the first where it's gone; that gap is where taint dies. For a spurious detection, do the reverse: find where a fact appears with no tainted input reaching it

### 3. Isolate an entry point (optional)

When the run misses the flow and you suspect the entry method is never reached, force analysis onto it. The entry point is positional — `*` for all methods, or a method FQN:

```bash
opentaint dev debug-run-on-entry-points "com.example.Controller#handle" \
  --project-model <model-dir> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset <rules-dir>
```

A finding that appears here but not in the full run points to entry-point discovery / reachability, not the dataflow; if it still doesn't appear, localize the kill with step 2. This command is ignored on Spring projects (the entry-point override has no effect there), so for a missed Spring-controller flow rely on step 2 instead

### 4. Classify the cause

The killing instruction decides who owns the fix:

- external library method → missing model (step 1 should have caught it; fact-reachability names the exact method)
- something the rule should handle — a mistaken sanitizer, an unmatched sink or source variant → fix the rule
- a plain instruction the engine should propagate through (assignment, cast, field read, an already-modeled call), with the rule correct and model complete → engine issue; route to report-analyzer-issue with the trace

## Output

- The diagnosis: `file:line` and instruction where taint is killed (or spuriously introduced), and which of the three causes it is
- For an engine issue, the fact-reachability trace up to the last reachable fact — report-analyzer-issue's input
- The exact debug command(s) used and the model they ran against

## Tracking

None — diagnostic, writes no tracking file

## Gotchas

- One rule per fact-reachability run; across many rules the report is unusably huge
- Debug the exact run that showed the problem — same model, rulesets, approximation dirs — or you debug something else; never swap the model mid-analysis
