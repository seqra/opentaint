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
- Tracking file `<tracking-file>` — the rule or approximation file this test serves. Default: `.opentaint/tracking/rules/<name>.yaml` or `.opentaint/tracking/approximations/<name>.yaml`
- Test project `<test-project>` — sources. Default: `.opentaint/test-projects/<name>`
- Compiled output `<test-compiled>` — the model. Default: `.opentaint/test-compiled/<name>`
- Dependencies — exact Maven coordinates the samples need; default: the `dependencies` list in `<tracking-file>`; with no tracking file, derive them from the project's `build.gradle`/`pom.xml`

`<name>` is the rule name for a rule, or the dataflow approximation unit (`<package-kebab>-dataflow`, e.g. `reactor-core-publisher-dataflow`) for an approximation; the two never share a folder

## Workflow

### 1. Init the project

Pick the scaffold by shape, then pass each coordinate from the tracking file's `dependencies` as a `--dependency`:

- a rule → `test rule init` (Gradle build + the test-util jar)
- a dataflow approximation → `test approximation init` (the same, plus `Taint.java` and the fixed `approximation-rule.yaml` the harness applies)

```bash
# rule test project
opentaint test rule init <test-project> \
  --dependency "org.mybatis:mybatis:3.5.13" \
  --dependency "javax.servlet:javax.servlet-api:4.0.1"

# dataflow approximation test project
opentaint test approximation init <test-project> \
  --dependency "io.projectreactor:reactor-core:3.8.5"
```

### 2. Read the real flow, then write samples

The requirements only name the source/sink and its framework. Before writing, find that source and sink in `<project-root>` and read the actual method signatures, annotations, and how the tainted value is built. The samples must mirror that code, not a guess — a sample built on the wrong signature compiles but verifies nothing

Write Java samples under `<test-project>/src/main/java/test/`, each annotated with its expected verdict — `@PositiveRuleSample` (must flag) or `@NegativeRuleSample` (must not). `value` is the rule path relative to the ruleset root (with `.yaml`), `id` the short id from the YAML — not the full `--rule-id` used by `opentaint scan`. One expected verdict per sample. Split the samples across files however groups most logically — don't cram unrelated ones into a single class

What the positive and negative samples must contain depends on the shape — load and follow the matching reference:

- a rule → `references/rule.md`
- a dataflow approximation → `references/approximation.md`

### 3. Compile

```bash
opentaint compile <test-project> -o <test-compiled>
```

A clean compile is the deliverable. If it won't build, fix the samples or dependencies before handing off

## Output

- A compiled test project (`<test-compiled>`) plus its sources (`<test-project>`); report both paths and the exact `compile` command used
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
- For library-method behavior the requirements don't pin down (does it sanitize? propagate taint?), read the dependency or its docs rather than guessing
