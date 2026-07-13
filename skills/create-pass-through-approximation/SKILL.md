---
name: create-pass-through-approximation
description: Model a method's taint propagation as a passThrough approximation. Use for a dropped method whose propagation is simple copying
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Create PassThrough Approximation

Model a dropped method's taint propagation as a passThrough approximation — a config that tells the engine how data moves from a method's inputs to its outputs, so a flow the analyzer lost through the opaque call is restored.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `batch` (required) — the batch id; its `passthrough` entries live in `.opentaint/tracking/approximations/<batch>.yaml`, and you append the ones you build to that file's `build.done`
- `methods` (optional) — a specific `{ method, signature }` subset to (re)work instead of the whole passthrough bucket, when the caller needs only those

## Workflow

### 1. Understand the propagation

Take the batch's `passthrough` methods not yet in `build.done` (or the specific `methods` you were handed) and study each from its real code: read the source (per the language reference). Model each method purely from what its own code does, **independent** of how the project uses it — the config describes the method's intrinsic propagation. Answer: where does the input data go? Data that arrives on the receiver or an argument — does it come back out, through the return value, an argument the method writes into, the receiver, or an object or field it stores into? Note too whether the object holds the data between calls (a setter stashes it and a getter hands it back later, or a builder accumulates it) — that needs a virtual field. That shape is what the config expresses.

### 2. Write the config

Write one passThrough config per package under `.opentaint/pass-through` (the format and patterns are in the language reference). A method already in `build.done` is built and trusted — leave it and its config as-is. Add a new method to its existing package config rather than rewriting the file. Two ideas drive the copy:

- Cover every position — `this` and each argument: copy each to where its data flows, or to itself when it flows nowhere
- When the data lives in the object between calls, route the writer and the reader through a shared virtual field — a nominal storage location both name identically. What the writer stashes there is what the reader pulls back, if the two name it differently, the taint is lost.

### 3. Re-check your configs

Before returning, confirm you wrote a passThrough for every method you were to model, and that each config's copies actually match how the method moves data in its source — every position covered, and a writer and its reader sharing the identical virtual field. Append the written methods to `build.done` (per Tracking).

## Output

Short and concise report of what was done

### Artifacts:

- `.opentaint/pass-through/<package-kebab>.yaml` — the passThrough config(s); one per package (a dependency can span several), the file named for that package (the whole-file form is in the language reference)
- the cleanly-built methods appended to the batch file's `build.done` (per Tracking)

### Summary:

- the config paths written and the methods modeled

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

This skill only appends each cleanly-built method to `build.done` as `{ method, signature }`. A method that you failed to write stays out, so the loop comes back to it. Never touch the classification buckets or an entry already in `build.done`.

## Constraints

- Model one function per rule — never a regex/wildcard matcher or an all-arguments position to cover many at once; over-modeling copies taint through methods you never vetted and manufactures false positives
- Keep produced configs comment-free
