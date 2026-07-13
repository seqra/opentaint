---
name: create-dataflow-approximation
description: Model a method's taint propagation as code-based dataflow approximation and refine it against a test project until the sample passes. Use for a dropped method that requires code-based approximation
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Create Dataflow Approximation

A dataflow approximation is code that expresses how data moves through a method the analyzer can't trace through — an opaque call where the engine loses taint because it can't see the body. You write a small stand-in that reproduces the method's real propagation from its inputs to its outputs, so the analyzer can follow taint through it. Run it against the prepared test project and refine until the sample passes.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `batch` (required) — the batch whose `.opentaint/tracking/approximations/<batch>.yaml` provides the `dataflow` methods to model and holds tracking state
- `methods` (optional) — a specific subset of the batch's dataflow methods to (re)model; default all not yet in `build.done`

## Workflow

### 1. Understand the propagation

Find and read each dataflow method's real source — skip the ones already in `build.done` (built and verified, leave them and their source as-is). An app-internal method sits in the project's own sources, a library method's source comes from its dependency (the language reference has how to get it). Read it to see how data moves from the method's inputs (receiver, arguments) to its outputs (return value, arguments it writes into, state it stores), gather the full context you need to fully understand the function's behavior.

### 2. Write the approximation

Reproduce that propagation as code under `.opentaint/dataflow/<batch>`, one `@Approximate` class per target class. Cover every dataflow method and overload the batch lists, add new methods to the existing source rather than rewriting it. The engine is field-sensitive — taint is tracked per field — so route data field-to-field exactly as the source does rather than tainting the whole object. The test project's negative samples (if present) verify this by storing taint in one field and reading another, so an over-broad model makes them fire. The code form, annotations, and patterns are in the language reference.

### 3. Test against the test project

Run the approximation test over the compiled test project, applying this batch's sources, and iterate until the samples pass. Feedback loop: a failing sample might be caused by: the model's target class or signature doesn't match what the analyzer sees, or the body doesn't route taint from the real source to the modeled output — diagnose the mismatch, fix, and re-run, don't rationalize a non-result. When the cause isn't obvious, localize where taint dies with a fact-reachability trace before guessing further per `references/debugging.md`. On a pass, append the method to `build.done` (per Tracking).

### 4. Escalate

When the sample won't converge after ~3 fixes — whether the trace shows a faithful model still can't propagate (taint dying at a plain instruction the engine should carry through, an engine limitation) or the cause stays unclear — leave the method out of `build.done` and report it with the brief cause you found (per Output), for the orchestrator to escalate. Don't retry further.

## Output

### Artifacts

- `.opentaint/dataflow/<batch>` — the code approximation source(s), one `@Approximate` class per target class, that the scan consumes; report the path and the exact test command used
- the passing methods appended to the batch file's `build.done` (per Tracking)

### Summary

- the methods modeled and the test status (passing / non-converging)

## Tracking

`.opentaint/tracking/approximations/<batch>.yaml` — one batch's method classification, `<batch>` the plan's filename stem. Every method sits in exactly one verdict bucket, keyed with its `signature` (the JVM descriptor, always quoted so array types `[…` stay valid YAML) so overloads stay distinct:
- `passthrough`, `dataflow` — modeled carriers; each entry `{ method, signature }`
- `skipped` — terminal non-carriers; each `{ method, signature, reason }`
- `engine_issues` — a separate bucket for carriers the engine provably can't propagate (built but still dropped); each `{ method, signature, reason }`. Terminal and treated just like `skipped` — the only difference is the reason. `merge-skipped` carries it into `skipped.yaml` as its own `engine_issues` group alongside the regular skipped `methods`.

`dependencies` lists the dependency identifiers a dataflow test project needs. The `build` block tracks the build — `test_project` records each dataflow method's test-project status (`done` if a sample was written into the batch's test project, `failed` if none could be written so the method was excluded from it), and `done` holds the finished `{ method, signature }`. Keep it clear from comments

```yaml
passthrough:
  - { method: "com.foo.Wrapper#getValue", signature: "()Ljava/lang/String;" }
dataflow:
  - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;" }
skipped:
  - { method: "org.slf4j.Logger#info", signature: "(Ljava/lang/String;)V", reason: "void side-effect" }
engine_issues: []
dependencies: []
build:
  test_project:
    - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;", status: done }
  done: []
```

This skill appends each method whose sample passes to `build.done` as `{ method, signature }`. A method that still fails, or one the engine provably can't propagate, stays out of `build.done` and is reported (per Output), not marked here. Don't touch the classification buckets (`passthrough`/`dataflow`/`skipped`/`engine_issues`) or an entry already in `build.done`.

## Constraints

- Verify only with the approximation test on the test project
- Model every dataflow method and overload the batch lists, not only the ones you have a sample for
