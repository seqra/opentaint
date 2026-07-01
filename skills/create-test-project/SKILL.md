---
name: create-test-project
description: Create an OpenTaint test project with annotated positive/negative samples for verifying a rule or approximation. Use when a rule or approximation needs a test project to check against
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Test Project

Build a minimal compiled test project whose annotated samples reproduce the flow a rule or approximation is checked against. The compiled model is the deliverable; its sources sit alongside it

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- What to test `<spec>` — a rule side's unit (its `sources` or `sinks`), or the package's methods to exercise
- Project root `<project-root>` — the real sources the requirements point into. Default: current directory
- Tracking file `<tracking-file>` — the source/sink unit or the batch approximation file this test serves. Default: `.opentaint/tracking/rules/sources/<name>.yaml` (source side) or `.opentaint/tracking/rules/sinks/<name>.yaml` (sink side), or `.opentaint/tracking/approximations/<batch>.yaml`
- Test project `<test-project>` — sources. Default: `.opentaint/test-projects/<name>` (a rule project holds a `sinks/` and/or `sources/` sub-project under it)
- Compiled output `<test-compiled>` — the model. Default: `.opentaint/test-compiled/<name>` (one model per sub-project: `<name>/sinks`, `<name>/sources`)
- Dependencies — exact Maven coordinates the samples need; default: the `dependencies` list in `<tracking-file>`; with no tracking file, derive them from the project's `build.gradle`/`pom.xml`

`<name>` is the package (`<package-kebab>`) for a rule, or the target class (`<class-kebab>`) for a dataflow approximation; the two never share a folder

## Workflow

When re-invoked over an existing `<name>` project whose surface grew (a new source/sink to exercise) or whose dependency moved, extend it with the missing samples and recompile — add to what's there rather than scaffolding fresh. Whether a still-current model needs rebuilding at all is the caller's decision, not yours.

### 1. Init the project

Pick the scaffold by shape, then pass each coordinate from the tracking file's `dependencies` as a `--dependency`:

- a rule → `test rule init` with `--sources-only` (for a source unit) or `--sinks-only` (for a sink unit) — scaffolds that one sub-project under `<test-project>` with `Taint.java` (the generic `source()`/`sink()`) and the generic marker lib rules in its `test-rules/`. You're handed one unit per invocation (sources and sinks are separate units built in separate phases), so build only that side
- a dataflow approximation → `test approximation init` (Gradle build + the test-util jar, plus `Taint.java` and the fixed `approximation-rule.yaml` the harness applies). Pass each lib at the exact pinned version from the unit's `dependencies`: this Gradle build is the approximation's own compile environment, so it must still recompile from these pins even after the main project drops that dependency

```bash
# rule source side (from a rules/sources/<name> unit)
opentaint test rule init <test-project> --sources-only \
  --dependency "org.springframework:spring-webflux:6.1.0"
# rule sink side (from a rules/sinks/<name> unit)
opentaint test rule init <test-project> --sinks-only \
  --dependency "org.mybatis:mybatis:3.5.13"

# dataflow approximation test project
opentaint test approximation init <test-project> \
  --dependency "io.projectreactor:reactor-core:3.8.5"
```

### 2. Read the real signatures, then write samples

The requirements name sources and sinks. For each new source and new sink, read its real method signature from the package jar in `.opentaint/project/dependencies` (with `javap`) — the pattern matches on that, so a sample built on the wrong signature compiles but verifies nothing. The flow is minimal, not the app's real path, and the counterpart is always the generic `Taint` marker (so types always fit — never a real source/sink):

- a **sink** sample (in the `sinks/` sub-project): assign `test.Taint.source()` to a local of the sink argument's type, then pass it in — `String t = test.Taint.source(); pkg.theSink(t);` (the generic `source()` infers the type, no cast)
- a **source** sample (in the `sources/` sub-project): call the new source, then pass its value into `test.Taint.sink(...)` — `var v = pkg.theSource(); test.Taint.sink(v);` (`sink` takes `Object`, so any type fits)

Write Java samples under `<test-project>/<sinks|sources>/src/main/java/test/`, each annotated with its expected verdict — `@PositiveRuleSample` (must flag) or `@NegativeRuleSample` (must not). `value`/`id` point at that sub-project's test join, which create-rule writes: `value = "java/security/<name>-sinks.yaml", id = "<name>-sinks"` for sink samples, `<name>-sources` for source samples (`<name>` = the package-kebab). `value` is the rule path relative to the test-rules root, `id` the short id — not the full `--rule-id` used by `opentaint scan`. One expected verdict per sample

Load and follow `references/rule.md` (for a rule) or `references/approximation.md` (for a dataflow approximation)

### 3. Compile

Compile the sub-project you built to its own model — the one rule side (`sources/` or `sinks/`); an approximation's single project once:

```bash
# rule — the side you built
opentaint compile <test-project>/sources -o <test-compiled>/sources
opentaint compile <test-project>/sinks   -o <test-compiled>/sinks
# approximation
opentaint compile <test-project> -o <test-compiled>
```

A clean compile is the deliverable. If one won't build, fix that project's samples or dependencies before handing off

## Output

- The compiled model(s) (`<test-compiled>`, per sub-project for a rule) plus their sources (`<test-project>`); report the paths and the exact `compile` command(s) used
- The test-project stage marked done (see Tracking)

## Tracking

Set only the test-project stage, `done` once it compiles. For a rule side it's `stages.test_project` in the source or sink unit (`<tracking-file>`); for a dataflow approximation it's the batch file's `build.test_projects`, keyed by the target class:

```yaml
stages:
  test_project: done
build:
  test_projects:
    com.foo.Reactor: done
```

Do not touch other stages or fields

## Gotchas

- One expected verdict per sample
- One unit per `<name>` folder — never write into another unit's project, so concurrent agents don't race
- The scaffold (`test rule init` / `test approximation init`) defaults to Java 8 — bump `source/targetCompatibility` when the samples use a library needing Java 17/21 (Spring 7, spring-data 4, Lucene 10, Jackson 3). Set `release` on the running JDK; a Gradle `toolchain{}` block fails here (only JDK 21 is locatable, with no download repo)
- A positive must route the marker `source()` into the sink — a sink whose only untrusted input is a bare method parameter with no in-sample source (e.g. `getValue(Expression e)`) can't be satisfied by any taint-flow join; feed the parameter from `test.Taint.source()` or the sample is unprovable
- For library-method behavior the requirements don't pin down (does it sanitize? propagate taint?), read the dependency or its docs rather than guessing
