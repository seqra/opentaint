---
name: analyze-external-methods
description: Analyze an OpenTaint scan's dropped external methods and decide which of them are propagators and optionally sinks. Use when a dropped-external-methods.yaml needs classification for dropped method type
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Analyze External Methods

OpenTaint is a dataflow taint analyzer: it starts from the data a source introduces and follows it call by call until the flow stops. A flow stops for one of two reasons — the data reached a method that carries it nowhere (call `size()` on a tainted collection and its whole contents collapse into one number, so the taint is gone), or it reached a method whose body the analyzer can't see, typically an external dependency. That opaque method may itself be taint-killing (e.g. the same `size()`), or it may in fact carry the data onward — and then it needs an approximation telling the engine exactly how the data moves through the call, or every trace through it is silently cut.

You are handed the list of those dropped methods. Decide which ones actually carry data and which don't, and for each carrier determine the kind of approximation it needs, so the build stage can restore the flow.

On a deep run these same methods carry a second, independent question — whether the call is itself a dangerous operation (a sink); that pass is step 2.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `plan` (required) — path to this agent's batch plan `.opentaint/tracking/approximations/plans/<batch>.yaml`: the dropped methods to classify
- `sinks` (optional) — a flag whether to classify sinks per step 2 or not

## Workflow

### 1. Classify propagation

Take the members from the plan's `scopes`, judge each one, and write the verdict to the batch file `.opentaint/tracking/approximations/<batch>.yaml` — `<batch>` is your plan's filename stem, the batch id, reused for the coverage check below.

Always classify from the method's real code, never from its name. Start by reading the method's source — the language reference describes how to get it. Then answer, for each method: where does its input data go? Data that arrives on the receiver or an argument — does it come back out, through the return value, an argument the method writes into, the receiver, or an object or field it stores the data in? That answer picks the bucket:

- `passthrough` — the method carries the data by a plain copy from one place to another: a getter, a simple arg-to-result copy, a builder, a writer that stashes the argument into the receiver or another object, a collection put-then-get, and the like
- `dataflow` — the method carries the data through a function, lambda, or callback parameter, or an async chain. Any method that takes a function goes here
- `skipped` — the method carries the data nowhere, give a short `reason`. This is exactly where a flow ends. A few examples: a predicate or inspector that only tests, compares, or measures its input (handing back a boolean or a number); a conversion that collapses the data into a scalar that no longer holds it (a size, a parse into a number, a one-way hash — the `size()` from the preamble); a side-effect that keeps none of the data. These are illustrations of the idea, not a closed list — many methods and cases fall outside it, so decide each on what its code does

The common trap is skipping an implicit carrier — a method that moves its data somewhere other than the plain return value. A `void` method that writes its argument into the receiver or another object still carries the data: it lives on in that object and the flow continues. A sanitizer or encoder is a carrier too — it returns a transformed copy of its input, so the data flows through it; model it, never skip it (whether the transform actually neutralizes the taint is settled later by the rules, not here). When in doubt, model it: over-approximating an inert method is cheap, dropping a real carrier is a false negative the run can't recover.

An opaque external key-value store — a cache, a Redis/DB template, a session map, anything whose data lives outside the process — is a carrier too, not a dead end: a value written by a `put`/`set` survives the round trip, so a later `get` can hand attacker-controlled data back. Model both ends as `passthrough`. Only the key-only or boolean operations that move no value — `delete`, `exists`, `hasKey`, `size` — are skipped.

Every entry records the method's `signature` from the plan, so overloads stay distinct — a differently-propagating overload is its own entry. Placing each method in its bucket is all that's needed here; the build stage reads the method's own code to model exactly how the data moves.

A dropped method may be application-internal, not only library code — the analyzer drops it when its body is opaque to it (native, abstract, generated). Classify it the same way, by what its code does.

### 2. Classify sinks (deep run only)

When the `sinks` input is set, make a second pass over the same members for a different property: is the method a sink? A sink is a security-sensitive operation that turns into a vulnerability once attacker-controlled data reaches it — the call executes or interprets its input, or acts on it against a sensitive resource, in a way that can be abused: running it as a query or OS command, using it as a file path or URL, deserializing it, rendering it into output, or resolving it through reflection or a naming/directory lookup, among many others.

Judge sink-ness from the method's own code and behaviour, independent of how the project uses it — don't trace whether taint can actually reach the call, that is the analyzer's job. And judge it apart from propagation: the propagation verdict never settles sink-ness, and finding a sink never changes it. Sinks might sit among the carriers you just modeled, and a `skipped` method can be a sink too — carrying nothing onward says nothing about whether the call itself is dangerous.

Record each sink in its owning package's sink unit `.opentaint/tracking/rules/sinks/<package-kebab>.yaml` (per Tracking).

### 3. Verify coverage

After classifying, run the bundled check from the project root over your plan:

```bash
uv run scripts/check-coverage.py --batch <batch>
```

Pass your `<batch>`. It lists every batch method not yet in a classification bucket. Classify each one it prints and re-run until it reports `0 UNCOVERED`. Don't return while anything is uncovered.

### 4. Re-verify the skips

Before returning, review each method you skipped and confirm that it truly moves no data — the name is not good enough evidence. Get back to step 1 to reclassify any method that appeared to be carrier and remove it from `skipped`. Keep only methods proven non-carriers by their code

## Output

Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/approximations/<batch>.yaml` — the batch classification (per Tracking)
- `.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — the per-package sink units, when `sinks` was set (per Tracking)

### Summary:

- per-kind method counts (passthrough / dataflow / skipped) and the sink count when `sinks` was set
- that `check-coverage.py --batch <batch>` reports `0 UNCOVERED`

## Tracking

### Batch classification

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

This skill writes `passthrough`/`dataflow`/`skipped` and `dependencies`; leave the `build` block and `engine_issues` alone — they are filled later in the approximation stage.

### Sink units (only when `sinks` is set)

`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sinks` each a dangerous operation reached by the taint frontier `{ method, signature, vuln_class, note, rule_id }` — `signature` the member's JVM descriptor so overloads stay distinct, always quoted (array types contain `[`, which is invalid unquoted in a flow mapping), `vuln_class` per entry since one package can host several, `note` a few words on the danger, the tainted argument left unpinned. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - cn.hutool:hutool-core:5.8.20
sinks:
  - { method: cn.hutool.core.io.FileUtil#writeBytes, signature: "([BLjava/lang/String;)Ljava/io/File;", vuln_class: path-traversal, note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

This skill fills `dependencies` and one `sinks` entry per sink it found — `{ method, signature, vuln_class, note, rule_id: null }`, `signature` the method's JVM descriptor from the plan so overloads stay distinct, `vuln_class` per entry, `note` a few words on the danger. Leave `rule_id: null` and the `stages` for the rule-authoring stage. One unit per package; the partition keeps a whole package in one batch, so you are its only writer. Where a package already has a unit from a prior round, add to it rather than rewriting.

## Constraints

- Judge intrinsic propagation only, never per-project flow. Don't skip a carrier because its data doesn't seem to reach a sink here, and don't gate a sink on where its data goes — whether a flow reaches a sink is the analyzer's job, not yours
- Classify every method the plan assigns and only those — each is a real place data was lost, don't invent methods outside the plan. `check-coverage.py --batch` must report `0 UNCOVERED` before you return
