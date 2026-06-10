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

- Rules `<full-ids>` — the security rule to trace AND every library rule it `refs` (source/sink), each as `<ruleSetRelativePath>.yaml:<shortId>`; fact-reachability runs only the rules you list and silently disconnects the join if a ref is missing. For an approximation, trace the rule whose sample routes taint through the approximated method
- Project model `<model-dir>` — the model where the behavior shows up. Default: `.opentaint/test-compiled/<name>` for a test project, or `.opentaint/project` for a main scan
- Ruleset `<rules-dir>` — Default: `builtin` plus `.opentaint/rules`
- Output directory `<results-dir>` — where the debug SARIF lands. Default: `.opentaint/test-results/<name>` for a test model, or `.opentaint/results` for a main scan
- Dropped external methods `<dropped-file>` — the list from the run that showed the problem. Default: `dropped-external-methods.yaml` next to that run's SARIF
- Approximation directories `<config-dir>` / `<approx-dir>` (optional) — apply when the behavior depends on them, so the debug run matches the run that showed the problem. Default: `.opentaint/pass-through`, `.opentaint/dataflow`

## Workflow

### 1. Precondition — library model complete

Open `<dropped-file>` from the run that showed the problem. If any method on the source→sink path is listed, STOP and model it (passThrough or dataflow), re-run, then debug — that missing model is the cause, not the engine. A method you already approximated that is still listed means the approximation isn't matching the real signature; fix it there. Debug only once no method on the path remains; if no `<dropped-file>` exists, produce one with a `--track-external-methods` run

### 2. Localize the kill — fact-reachability SARIF

Pass the single rule to debug as the positional `<rule-id>` — its library `refs` (source/sink) are collected and analyzed automatically, so you don't list them:

```bash
opentaint test rule reachability <full-id> \
  --project-model <model-dir> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset <rules-dir>
```

The debug output is the sibling file `<results-dir>/debug-ifds-fact-reachability.sarif`, NOT the `-o` SARIF. The `-o` file is the regular rule run (findings only); the per-instruction fact-reachability data — what shows where taint dies — lives only in the sibling. Read the sibling; the `-o` SARIF only tells you whether the rule fired, not why

When the thing under debug is an approximation (or the flow depends on one), append `--passthrough-approximations <config-dir>` / `--dataflow-approximations <approx-dir>` so the trace runs with it applied — taint dying at the approximated call then means the approximation isn't propagating: wrong signature (still in `<dropped-file>`), empty body, or wrong from→to. For a missed detection (a `@PositiveRuleSample` that won't pass, or a flow absent from a scan): confirm a fact exists at the source — if not, the gap is in `pattern-sources` — then walk the facts to the last instruction still carrying the fact and the first where it's gone; that gap is where taint dies. For a spurious detection, do the reverse: find where a fact appears with no tainted input reaching it

### 3. Isolate an entry point (optional)

When the run misses the flow and you suspect the entry method is never reached, force analysis onto it with the same `reachability` command plus `--entry-points` set to a method FQN:

```bash
opentaint test rule reachability <full-id> \
  --entry-points "com.example.Controller#handle" \
  --project-model <model-dir> \
  -o <results-dir>/report.sarif \
  --ruleset builtin --ruleset <rules-dir>
```

A finding that appears here but not in the full run points to entry-point discovery / reachability, not the dataflow; if it still doesn't appear, localize the kill with step 2. On Spring projects the flag is **additive, not restrictive**: auto-discovered endpoints stay and your method is added if absent — use it only to force-include a method the analyzer never starts from (an endpoint Spring didn't recognize); you can't narrow to a single method

### 4. Classify the cause

An engine bug is the least likely outcome by far — assume it last. Nearly every taint kill is a missing or wrong library model (an un-approximated method, or an approximation whose signature/from→to is off) or a rule defect; both are tedious to rule out, but that's not a reason to jump to "engine". Exhaust the first two before you even consider the third.

The killing instruction decides who owns the fix:

- external library method → missing or broken model. If the method is NOT in `approximated-external-methods.yaml`, step 1 should have caught it (route to analyze-external-methods + create-*-approximation). If it IS listed (a built-in claims to model it) yet taint dies here, the built-in is wrong for this case — write your own override: passthrough overrides at the rule level, so prefer a passthrough config for the specific method; a dataflow override conflicts with built-ins at load, so fall back to passthrough on that method, or if only a dataflow shape can express the propagation, treat it as an engine issue
- something the rule should handle — a mistaken sanitizer, an unmatched sink or source variant → fix the rule
- a plain instruction the engine should propagate through (assignment, cast, field read, an already-modeled call), with the rule correct and model complete → engine issue; route to report-analyzer-issue with the trace

## Output

- The diagnosis: `file:line` and instruction where taint is killed (or spuriously introduced), and which of the three causes it is
- For an engine issue, the fact-reachability trace from `debug-ifds-fact-reachability.sarif` up to the last reachable fact — report-analyzer-issue's input
- The exact debug command(s) used and the model they ran against

## Tracking

None — diagnostic, writes no tracking file

## Gotchas

- Don't reach for an "engine" verdict because ruling out a model or rule cause is tedious — a missing/wrong approximation or a rule gap is overwhelmingly more likely. Classify engine only when the killing instruction is a plain propagation (assignment, cast, field read, an already-modeled call) with the model proven complete and the rule proven correct
- One rule per fact-reachability run; across many rules the report is unusably huge
- Debug the exact run that showed the problem — same model, rulesets, approximation dirs — or you debug something else; never swap the model mid-analysis
