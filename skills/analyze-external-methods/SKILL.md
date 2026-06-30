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

- Plan `<plan>` — a partition plan (`tracking/approximations/plans/<id>.yaml`) assigning this agent's methods, grouped by scope. Work only its methods and key each unit by the plan's scope
- Tracking directory `<tracking-dir>` — where approximation tracking files are written. Default: `.opentaint/tracking`
- Lib-rules directory `<lib-rules-dir>` (optional) — when set, also record possible sinks among these methods into the owning package's `rules/lib/<package-kebab>.yaml`. With none, classify propagation only
- Project root `<project-root>` — sources and build files, to resolve which library owns each method. Default: current directory

## Workflow

Classify every method the `<plan>` assigns

### 1. Work the plan, group by kind

Each method is either modeled (passthrough/dataflow) or skipped. Decide kind by the method's intrinsic propagation shape:

- passthrough — data moves by a simple from→to copy: a getter, arg→result, builder, container field, collection `add`/`get`, `StringBuilder.append`, `Stream.collect`
- dataflow — data flows through a lambda/callback/functional interface or an async chain

The `<plan>` groups its methods by scope — normally the package, or a sub-package/class when a large package was split across agents. Write one tracking file per (scope, kind): `<scope-kebab>-passthrough.yaml` and `<scope-kebab>-dataflow.yaml`, where `<scope-kebab>` is the scope key with `.` → `-` (e.g. `reactor-core-publisher`); the YAML `package` field keeps the real dotted name. Kind is the only split within a scope

### 2. Model carriers, skip only non-carriers

A method is a carrier when taint on its receiver or an argument reaches its result, an output argument, or the receiver — model it. Skip (list in your scope's `<scope-kebab>-skipped.yaml`) only methods that move no taint at all: boolean/int predicates and inspectors, void side-effects (e.g. loggers), one-way non-injectable transforms (e.g. hashes). Judge each on its intrinsic behavior, and when unsure, model it — over-approximating an inert method is cheap, skipping a real carrier hides findings. Skip an FQN only when every overload is a non-carrier; if any overload carries taint, model the FQN — the passThrough matcher and dataflow `@Approximate` cover all overloads by name.

A method that takes a function, lambda, or callback parameter is always a dataflow carrier — model it as dataflow, never skip it, even when its own propagation looks inert
Always to your `<scope-kebab>-skipped.yaml` goes any `toString()` (unless it overrides default `toString()` for Object)

A method the engine can't model — a built-in dataflow approximation you can't override, or one escalation could not make work — goes under `engine_issues` in your `<scope-kebab>-skipped.yaml`: it's a carrier the engine drops, kept apart from genuine non-carriers

When `<lib-rules-dir>` is set, also judge each method as a possible sink. Every dropped method here is already reached by source-derived taint. This is not per-project tracing — it's whether the method is itself a dangerous operation (query/command/file/path, deserialization, template/EL, LDAP/JNDI, reflection, request-out/SSRF, and more, don't focus only on those). If it is, append it to the owning package's `rules/lib/<package-kebab>.yaml` `sinks` with its `vuln_class` and the tainted argument (the method's `factPositions` from the plan row). A method can be both a carrier and a sink

### 3. Verify coverage

After classifying, run the bundled check from the project root over your plan:

```bash
uv run scripts/check-coverage.py --plan <id>
```

It lists every plan method not yet in some bucket — a unit's `methods`/`done` or your `<scope-kebab>-skipped.yaml`'s `methods`/`engine_issues`. Classify each one it prints and re-run until it reports `0 UNCOVERED`. Don't return while anything is uncovered — an unclassified method is a silent taint kill.

### 4. Re-verify the skips

Before returning, open each method you skipped and confirm from the library source or its dependency jar that it truly moves no data — the name is not good enough evidence. Move any method that on inspection touches its input into a passthrough or dataflow unit. A good result is a small, source-verified skip list: keep only methods proven non-carriers by their code

## Output

- One `<tracking-dir>/approximations/<scope-kebab>-<kind>.yaml` per (scope, kind), with top-level `type`, `stages.description: done`, and its `methods`; a dataflow unit also carries `dependencies`
- A `<tracking-dir>/approximations/<scope-kebab>-skipped.yaml` only if you skipped something — your scope's `methods` and any `engine_issues`; with nothing skipped, write no skip file (the orchestrator merges these transient files into one `skipped.yaml`, then deletes them)
- When `<lib-rules-dir>` is set, the possible sinks appended to each owning `rules/lib/<package-kebab>.yaml` `sinks`
- `check-coverage.py --plan <id>` reporting `0 UNCOVERED`
- A brief summary to the caller: one line per scope (kind, method count) plus the skip count. Don't paste the method lists back — the tracking files hold them

## Tracking

Create one file per (scope, kind) — the scope is the plan's scope key; fill only the discovery-stage fields. The kind is one top-level `type` (the file is single-kind), `methods` is a plain FQN list — put any overload/signature detail in `notes`; when a method's overloads propagate differently, record each overload's signature there so the passThrough author can target them with a per-`signature` entry. The two kinds differ: passThrough is written and verified by the scan, dataflow is built and tested on a test project:

<scope-kebab>-passthrough.yaml — simple copies
```yaml
package: com.foo
type: passthrough
artifact: null
stages:
  description: done
  written: pending
methods:
  - "com.foo.Wrapper#getValue"
done: []
notes: >
  DTO getters returning fields that carry the data
```

<scope-kebab>-dataflow.yaml — lambda/callback/async
```yaml
package: com.foo
type: dataflow
artifact: null
dependencies:
  - com.foo:foo-core:1.2.3
stages:
  description: done
  test_project: pending
  tests_passing: pending
methods:
  - "com.foo.Reactor#flatMap"
done: []
notes: >
  Reactor operators carrying data through the mapper.
  flatMap overload: flatMap(java.util.function.Function)
```

<scope-kebab>-skipped.yaml — non-carriers left to the engine's default; one per scope, written only when you skip something; the orchestrator merges these into a single skipped.yaml and deletes them
```yaml
methods:
  - "org.slf4j.Logger#info"
  - "org.slf4j.Logger#debug"
engine_issues: []
```

`stages` track only the `methods` batch — they read `done` when that batch is built and emptied into `done`. You write `description: done` and leave the rest `pending`, the build skill drives the later stages and the `methods`→`done` move. When you append a new method to an existing unit, add it to `methods` and reset the affected stages to `pending`; never touch entries already in `done`.

## Gotchas

- Classify every method in your `<plan>`, and only those — each is a real place data is lost. Model carriers; move genuine non-carriers and `toString` to your `<scope-kebab>-skipped.yaml`. `check-coverage.py` must report `0 UNCOVERED` before you return
- Describe intrinsic propagation, never per-project flow — don't skip a carrier because its data doesn't seem to reach a sink here (the possible-sink call is the method's own danger, also intrinsic)
- One file = one (scope, kind) = one agent: passThrough and dataflow go in separate files; never put a method in two, or two agents collide
