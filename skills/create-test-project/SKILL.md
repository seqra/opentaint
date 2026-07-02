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

- What to test `<spec>` — a rule's requirements, or the package's methods to exercise
- Project root `<project-root>` — the real sources the requirements point into. Default: current directory
- Tracking file `<tracking-file>` — the rule or approximation file this test serves. Default: `.opentaint/tracking/rules/lib/<name>.yaml` or `.opentaint/tracking/approximations/<name>.yaml`
- Test project `<test-project>` — sources. Default: `.opentaint/test-projects/<name>` (a rule project holds a `sinks/` and/or `sources/` sub-project under it)
- Compiled output `<test-compiled>` — the model. Default: `.opentaint/test-compiled/<name>` (one model per sub-project: `<name>/sinks`, `<name>/sources`)
- Dependencies — exact Maven coordinates the samples need; default: the `dependencies` list in `<tracking-file>`; with no tracking file, derive them from the project's `build.gradle`/`pom.xml`

`<name>` is the package (`<package-kebab>`) for a rule, or the dataflow approximation unit (`<package-kebab>-dataflow`, e.g. `reactor-core-publisher-dataflow`) for an approximation; the two never share a folder

## Workflow

### 1. Init the project

Pick the scaffold by shape, then pass each coordinate from the tracking file's `dependencies` as a `--dependency`:

- a rule → `test rule init` — scaffolds a `sinks/` and a `sources/` sub-project under `<test-project>`, each with `Taint.java` (the generic `source()`/`sink()`) and the generic marker lib rules in its `test-rules/`. Pass `--sinks-only` / `--sources-only` for a package with only one side, so you get a single sub-project
- a dataflow approximation → `test approximation init` (Gradle build, plus `Taint.java` and the fixed `approximation-rule.yaml` the harness applies)

```bash
# rule test projects — both sides (this package has new sinks and new sources)
opentaint test rule init <test-project> \
  --dependency "org.springframework:spring-webflux:6.1.0"
# sink-only package
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

Write Java samples under `<test-project>/<sinks|sources>/src/main/java/test/` as plain methods (no annotations), then record their expected verdicts in a `rule-test.yaml` at that sub-project's source root (`<test-project>/<sinks|sources>/rule-test.yaml`). Each `tests:` entry carries a `rule-id` — `<rule-file-path>#<rule-id>`, the sub-project's test join that create-rule writes: `java/security/<name>-sinks.yaml#<name>-sinks` for sink samples, `<name>-sources` for source samples (`<name>` = the package-kebab) — and lists its samples under `positive` (must flag) and `negative` (must not) as JVM binary class names (nested classes use `$`), each optionally `#<methodName>` to target one method (a bare class name targets all its declared methods), e.g. `test.SqlSinkTest#vulnerable`. A sample entry may instead be an object `{ entrypoint: <id>, mode: spring-app }` to analyze it through the Spring dispatcher instead of calling the method directly (see `references/spring-multimodule.md`); a bare string is equivalent to `mode: default`. The `<rule-file-path>` is relative to the test-rules root and `<rule-id>` the short id — not the full `--rule-id` used by `opentaint scan`. One expected verdict per sample

Load and follow `references/rule.md` (for a rule) or `references/approximation.md` (for a dataflow approximation)

### 3. Compile

Compile each project to its own model — a rule's `sinks/` and `sources/` sub-projects separately; an approximation's single project once:

```bash
# rule
opentaint compile <test-project>/sinks   -o <test-compiled>/sinks
opentaint compile <test-project>/sources -o <test-compiled>/sources
# approximation
opentaint compile <test-project> -o <test-compiled>
```

A clean compile is the deliverable. If one won't build, fix that project's samples or dependencies before handing off

## Output

- The compiled model(s) (`<test-compiled>`, per sub-project for a rule) plus their sources (`<test-project>`); report the paths and the exact `compile` command(s) used
- The tracking file's `test_project` stage marked done (see Tracking)

## Tracking

In `<tracking-file>`, set only the test-project stage (`in_progress` while building, `done` once it compiles):

```yaml
stages:
  test_project: done
```

Do not touch other stages or fields

## Gotchas

- One expected verdict per sample
- One unit per `<name>` folder — never write into another unit's project, so concurrent agents don't race
- The scaffold (`test rule init` / `test approximation init`) defaults to Java 8 — bump `source/targetCompatibility` when the samples use a library needing Java 17/21 (Spring 7, spring-data 4, Lucene 10, Jackson 3). Set `release` on the running JDK; a Gradle `toolchain{}` block fails here (only JDK 21 is locatable, with no download repo)
- A positive must route the marker `source()` into the sink — a sink whose only untrusted input is a bare method parameter with no in-sample source (e.g. `getValue(Expression e)`) can't be satisfied by any taint-flow join; feed the parameter from `test.Taint.source()` or the sample is unprovable
- For library-method behavior the requirements don't pin down (does it sanitize? propagate taint?), read the dependency or its docs rather than guessing
