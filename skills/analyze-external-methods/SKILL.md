---
name: analyze-external-methods
description: Analyze and group an OpenTaint scan's dropped external methods and decide what to approximate or skip. Use when a dropped-external-methods.yaml needs turning into approximation targets
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Analyze External Methods

Read the methods where the analyzer lost track of the data, group them by library and kind, and record per group what to model and how — so the right skill can build each approximation.

Think how taint flows through each method intrinsically — which inputs (receiver, arguments) reach the result, an output argument, or the receiver — independent of this project's usages. Whether that method's data reaches a sink in this codebase, or sits on any trace, is the analyzer's job, not yours: never reason about per-project usage and never gate modeling on it

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Dropped methods `<dropped-file>` — methods where the analyzer dropped the data for lack of a model. Default: `.opentaint/results/dropped-external-methods.yaml`
- Tracking directory `<tracking-dir>` — where approximation tracking files are written. Default: `.opentaint/tracking`
- Project root `<project-root>` — sources and build files, to resolve which library owns each method. Default: current directory

## Workflow

Requires `<dropped-file>`, without it there's nothing to group

### 1. Group by package and kind

Each method is either modeled (passthrough/dataflow) or skipped. Decide kind by the method's intrinsic propagation shape:

- passthrough — data moves by a simple from→to copy: a getter, arg→result, builder, container field, collection `add`/`get`, `StringBuilder.append`, `Stream.collect`
- dataflow — data flows through a lambda/callback/functional interface or an async chain

Group by package AND kind — one tracking file per (package, kind): `<package-kebab>-passthrough.yaml` for the simple copies, `<package-kebab>-dataflow.yaml` for the lambda/callback/async ones. `<package-kebab>` is the dotted Java package with `.` replaced by `-` (e.g. `reactor.core.publisher` → `reactor-core-publisher`) so it's filesystem-friendly; the YAML `package:` field keeps the real dotted name. Kind is the only split (no finer sub-groups). Each unit is one agent's work

### 2. Model carriers, skip only non-carriers

A method is a carrier when taint on its receiver or an argument reaches its result, an output argument, or the receiver — model it. Skip (list in `skipped.yaml`) only methods that move no taint at all: boolean/int predicates and inspectors, void side-effects (e.g. loggers), one-way non-injectable transforms (e.g. hashes). Judge each on its intrinsic behavior, and when unsure, model it — over-approximating an inert method is cheap, skipping a real carrier hides findings. Skip an FQN only when every overload is a non-carrier; if any overload carries taint, model the FQN — the passThrough matcher and dataflow `@Approximate` cover all overloads by name.

Always to `skipped.yaml` goes any `toString()` (unless it overrides default `toString()` for Object)

### 3. Verify coverage

After classifying, run the bundled check from the project root — it's deterministic, no arguments, fixed paths:

```bash
python scripts/check-coverage.py
```

It lists every dropped method not yet classified into any bucket — `dropped − pending(methods:) − done − skipped`. Classify each one it prints and re-run until it reports `0 UNCOVERED`. Don't return while anything is uncovered — an unclassified method is a silent taint kill.

## Output

- One `<tracking-dir>/approximations/<package>-<kind>.yaml` per (package, kind), with top-level `type`, `stages.description: done`, and its `methods`; a dataflow unit also carries `dependencies`
- `<tracking-dir>/approximations/skipped.yaml` listing the skip methods
- `check-coverage.py` reporting `0 UNCOVERED`
- A brief summary to the caller: one line per unit (package, kind, method count) plus the skip count. Don't paste the method lists back — the tracking files hold them

## Tracking

Create one file per (package, kind); fill only the discovery-stage fields. The kind is one top-level `type` (the file is single-kind), `methods` is a plain FQN list — put any overload/signature detail in `notes`. The two kinds differ: passThrough is written and verified by the scan, dataflow is built and tested on a test project:

```yaml
# <package-kebab>-passthrough.yaml — simple copies, no test project
package: com.foo
type: passthrough
artifact: null
stages:                  # status of the methods: (pending) batch only
  description: done
  written: pending
methods:                 # FQN only; overload detail goes in notes
  - "com.foo.Wrapper#getValue"
done: []                 # the build skill moves a method here once it's cleanly written
notes: >
  DTO getters returning fields that carry the data
```

```yaml
# <package-kebab>-dataflow.yaml — lambda/callback/async, tested on a test project
package: com.foo
type: dataflow
artifact: null
dependencies:                 # exact GAV the test project needs, from the build files
  - com.foo:foo-core:1.2.3
stages:                  # status of the methods
  description: done
  test_project: pending
  tests_passing: pending
methods:
  - "com.foo.Reactor#flatMap"
done: []                 # the build skill moves a method here once tests pass
notes: >
  Reactor operators carrying data through the mapper.
  flatMap overload: flatMap(java.util.function.Function)
```

```yaml
# skipped.yaml — methods left to the engine's default; no approximation added
methods:
  - "org.slf4j.Logger#info"
  - "org.slf4j.Logger#debug"
```

`stages` track only the `methods` batch — they read `done` when that batch is built and emptied into `done`. You write `description: done` and leave the rest `pending`, the build skill drives the later stages and the `methods`→`done` move. When you append a new method to an existing unit, add it to `methods` and reset the affected stages to `pending`; never touch entries already in `done`.

## Gotchas

- Classify every method in `<dropped-file>`, and only those — each is a real place data is lost. Model carriers; move genuine non-carriers and `toString` to `skipped.yaml`. `check-coverage.py` must report `0 UNCOVERED` before you return
- Describe intrinsic propagation, never per-project flow — don't skip a carrier because its data doesn't seem to reach a sink here
- One file = one (package, kind) = one agent: passThrough and dataflow go in separate files; never put a method in two, or two agents collide
