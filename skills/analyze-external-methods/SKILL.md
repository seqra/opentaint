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

- Plan `<plan>` — a batch plan (`tracking/approximations/plans/<batch>.yaml`) assigning this agent's methods, grouped by class scope. Work only its methods
- Tracking directory `<tracking-dir>` — where approximation tracking files are written. Default: `.opentaint/tracking`
- Sinks directory `<sinks-dir>` (optional) — when set, also record possible sinks among these methods into the owning package's sink unit `<sinks-dir>/<package-kebab>.yaml`. Default: `.opentaint/tracking/rules/sinks`. With none, classify propagation only
- Project root `<project-root>` — sources and build files, to resolve which library owns each method. Default: current directory

## Workflow

Classify every method the `<plan>` assigns

### 1. Work the plan, group by kind

Each method is either modeled (passthrough/dataflow) or skipped. Decide kind by the method's intrinsic propagation shape:

- passthrough — data moves by a simple from→to copy: a getter, arg→result, builder, container field, collection `add`/`get`, `StringBuilder.append`, `Stream.collect`, and so on
- dataflow — data flows through a lambda/callback/functional interface or an async chain

Write one file for the whole batch — `<tracking-dir>/approximations/<batch>.yaml`, where `<batch>` is the plan's filename stem — bucketing every method under `passthrough`, `dataflow`, `skipped`, or `engine_issues`. Each entry keeps the method's `signature` from the plan (overloads are separate entries). A passthrough entry adds a `note` listing every position taint flows through — check `this` and each argument, and name each real copy edge compactly (`arg(0) -> result, arg(1) -> this`) — not field/slot detail, which the build skill decides. A position the note omits is one the method doesn't propagate; the build skill pins those in place. Dataflow entries take no note

A dropped method may be application-internal, not only library code — the analyzer drops it when its body is opaque to it (native, abstract, generated). Classify it the same way, by its intrinsic propagation

### 2. Model carriers, skip only non-carriers

A method is a carrier when taint on its receiver or an argument reaches its result, an output argument, or the receiver — model it. Put in the `skipped` bucket (with a short `reason`) only methods that move no taint at all: boolean/int predicates and inspectors (`equals`, `contains`, `isEmpty`, `is*`, `hashCode` — the ones that merely test an object), void side-effects (e.g. loggers), one-way non-injectable transforms (e.g. hashes), and methods whose result is only a constant (the engine drops constants, so they carry nothing). Confirm the skip from the source — a `contains`/`find` that actually runs a query or lookup is a carrier or a sink, not an inspector. Judge each on its intrinsic behavior, and when unsure, model it — over-approximating an inert method is cheap, skipping a real carrier hides findings. Skip an FQN only when every overload is a non-carrier; if any overload carries taint, model the FQN — the passThrough matcher and dataflow `@Approximate` cover all overloads by name.

A method that takes a function, lambda, or callback parameter is always a dataflow carrier — model it as dataflow, never skip it, even when its own propagation looks inert
Any `toString()` always goes in `skipped` (unless it overrides default `toString()` for Object)

A method the engine can't model — a built-in dataflow approximation you can't override, or one escalation could not make work — goes in the `engine_issues` bucket: a carrier the engine drops, kept apart from genuine non-carriers

Sink-ness is a second, independent axis (deep only, when `<sinks-dir>` is set) — judge it separately from the approximation type; one verdict never decides the other. Every dropped method here is already reached by source-derived taint; the question is only whether the method is itself a dangerous operation (query/command/file/path, deserialization, template/EL, LDAP/JNDI, reflection, request-out/SSRF, and more — don't focus only on those). The two axes don't exclude each other:

- a method can be a sink AND a carrier — the engine doesn't stop tracking at a sink, so if taint also flows through it, model it (passthrough/dataflow) so the flow continues past, AND record it as a sink
- a `skipped` method can still be a sink — being a non-carrier says nothing about whether it's dangerous

Record a sink in the owning package's sink unit `<sinks-dir>/<package-kebab>.yaml` — a `dependencies` list (the owning library GAV) and a `sinks` entry `{ method, vuln_class, note, rule_id: null }`. One package can host several vuln classes, so each entry carries its own `vuln_class`. Don't pin the tainted argument — create-rule finds it from context (taint may land on a different arg after later approximation rounds). `rule_id` is filled later by create-rule. This is race-free: the partition keeps a whole package in one batch, so you're the only writer of its sink unit

```yaml
dependencies:
  - cn.hutool:hutool-core:5.8.20
sinks:
  - { method: cn.hutool.core.io.FileUtil#writeBytes, vuln_class: path-traversal, note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

### 3. Verify coverage

After classifying, run the bundled check from the project root over your plan:

```bash
uv run scripts/check-coverage.py --batch <id>
```

It lists every batch method not yet in a classification bucket of `<batch>.yaml`. Classify each one it prints and re-run until it reports `0 UNCOVERED`. Don't return while anything is uncovered — an unclassified method is a silent taint kill.

### 4. Re-verify the skips

Before returning, open each method you skipped and confirm from the library source or its dependency jar that it truly moves no data — the name is not good enough evidence. Move any method that on inspection touches its input into the passthrough or dataflow bucket. A good result is a small, source-verified skip list: keep only methods proven non-carriers by their code

## Output

- One `<tracking-dir>/approximations/<batch>.yaml` with `passthrough`/`dataflow`/`skipped`/`engine_issues` buckets; passthrough entries carry `note`, skipped/engine_issues carry `reason`. Add `dependencies` (the GAVs a dataflow test project needs) when the batch has dataflow and you know them. Leave the `build` block to the build skills
- When `<sinks-dir>` is set, the possible sinks written to each owning sink unit `<sinks-dir>/<package-kebab>.yaml`
- `check-coverage.py --batch <id>` reporting `0 UNCOVERED`
- A brief summary to the caller: per-kind method counts plus the skip count. Don't paste the method lists back — the file holds them

## Tracking

Create one file per batch — `<batch>.yaml` (the plan's filename stem). The classification buckets are yours; leave the `build` block to the build skills. `signature` distinguishes overloads (a differently-propagating overload is its own entry); `note` (passthrough only) lists every position taint flows through, not slot detail; `reason` (skipped/engine_issues) is a few words.

```yaml
passthrough:
  - { method: "com.foo.Wrapper#getValue", signature: "()Ljava/lang/String;", note: "this -> result" }
dataflow:
  - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;" }
skipped:
  - { method: "org.slf4j.Logger#info", reason: "void side-effect" }
engine_issues: []
dependencies: []
```

Append a newly-dropped method to its kind bucket; never touch the `build` block — the build skills move finished methods into `build.done`.

## Gotchas

- Classify every method in your `<plan>`, and only those — each is a real place data is lost. Model carriers; move genuine non-carriers and `toString` to the `skipped` bucket. `check-coverage.py --batch` must report `0 UNCOVERED` before you return
- Describe intrinsic propagation, never per-project flow — don't skip a carrier because its data doesn't seem to reach a sink here (the possible-sink call is the method's own danger, also intrinsic)
- One batch = one file = one agent; each method goes in exactly one bucket
