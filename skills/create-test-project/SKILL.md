---
name: create-test-project
description: Create an OpenTaint test project with positive/negative samples for verifying a rule or approximation. Use when a rule or approximation needs a test project to check against
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Create Test Project

Build a minimal compiled test project whose samples reproduce the flow a rule or approximation is verified against. A sample routes data between a real library method and the generic taint marker the scaffold provides, with the one verdict it must produce — a positive that must flag, a negative that must not. The compiled model is the deliverable; its sample sources sit alongside it.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `type` (required) — what this project verifies, selecting the sample style and the identifying inputs below: `rule-source`, `rule-sink`, or `dataflow`
- for `rule-source` / `rule-sink` — `unit`: the unit id; its members and `dependencies` come from `.opentaint/tracking/rules/sources|sinks/<unit>.yaml`
- for `dataflow` — `batch`: the batch whose `.opentaint/tracking/approximations/<batch>.yaml` provides the dataflow methods to exercise and their `dependencies`

The project folder `<name>` is that identifier — the `unit` for a rule side, the `batch` for a dataflow approximation.

## Workflow

### 1. Scaffold the project

The scaffold command and sample form are language-specific — read the reference for your `type`: `references/<lang>-rule.md` for `rule-source` / `rule-sink`, or `references/<lang>-approximation.md` for `dataflow` (one self-contained reference, no need to read the other). Scaffold the project for the `type`, passing each of the unit's `dependencies` at its pinned version. The scaffold provides the generic taint marker and the fixed test rule the samples run against, so you author only the samples. If the `<name>` project already exists — re-invoked because its surface grew or a dependency moved — extend it instead: add the missing samples and recompile rather than scaffolding fresh. The init command is in that reference.

### 2. Write the samples

For a unit or batch, each entry records its `signature`; shape a faithful sample from how that callable is really used in the project. The app's real path is irrelevant, only that data flows between the boundary and the marker:

For a sink unit, the methods are nested under `groups[].sinks`, exercise every method while preserving the group boundaries for the later rule author.

- the counterpart is always the generic marker, never a real source/sink, so the sample exercises only the unit under test
- register each sample under the single verdict it must produce — a positive that must flag, and, where the type calls for it, a negative that must not — in the test's `rule-test.yaml`

The sample code, the `rule-test.yaml` form, and which verdicts a type needs are in that reference.

### 3. Compile to the model

Compile the project you built to `.opentaint/test-compiled/<name>` — a rule side compiles the one sub-project you scaffolded (`sources/` or `sinks/`) to the matching sub-model, a dataflow project compiles once:

```bash
# rule side — the one you built
opentaint compile .opentaint/test-projects/<name>/sources -o .opentaint/test-compiled/<name>/sources
# dataflow
opentaint compile .opentaint/test-projects/<name> -o .opentaint/test-compiled/<name>
```

A clean compile is the deliverable. Feedback loop: a build failure is a fixable samples-or-dependencies problem — surface the real error, fix it, and recompile. On a clean compile set the test-project stage done (per Tracking).

### 4. Escalate

When a project won't compile after ~3 fixes with no clear cause → report the failure and leave the test-project stage pending, for the orchestrator to intervene.

## Output

Short and concise report of what was done

### Artifacts

- `.opentaint/test-compiled/<name>` — the compiled test model a later stage runs against; report each path and the exact `compile` command used
- `.opentaint/test-projects/<name>` — the sample sources and the `rule-test.yaml` that records their verdicts, alongside the model

### Summary

- the number of samples written per case
- any method excluded because no sample could be written (marked `failed`), with a brief reason
- failed projects (if any)

## Tracking

This skill writes only the test-project stage back:

- a rule side → `stages.test_project: done` in the source or sink unit
- a dataflow approximation → one `build.test_project` entry per method in the batch file, `status: done` for a method whose sample made it into the project, `status: failed` for one no sample could be written for (excluded)

`.opentaint/tracking/rules/sources/<package-kebab>.yaml` — one source unit per package (a dependency can span several packages), the file named for that package with `.` → `-`. `tag` is always the reusable `untrusted-data-source` group. `dependencies` names the dependency the package comes from, `sources` each an entry point `{ method, signature, note, rule_id }` (`method` and `signature` use the exact language-specific identifiers from the plan), `stages` tracks the unit through rule authoring, and a `blocker` string is added under it when the unit can't be made to pass. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
tag: untrusted-data-source
sources:
  - { method: "<qualified-member>", signature: "<language-signature>", note: untrusted message payload, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from. `groups` partitions the package's dangerous operations by reusable sink tag; each group is `{ tag, sinks }`, and each sink is `{ method, signature, note, rule_id }`. The tag belongs to the group, never to an individual method: one rule may cover several methods and several rules may extend the same vulnerability family. `method` and `signature` use the exact language-specific identifiers from the plan. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
groups:
  - tag: path-traversal-sink
    sinks:
      - { method: "<qualified-member>", signature: "<language-signature>", note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

`.opentaint/tracking/approximations/<batch>.yaml` — one batch's callable classification, `<batch>` the plan's filename stem. Every callable sits in exactly one verdict bucket, keyed with the exact language-specific `method` and `signature` from the plan so distinct variants stay separate:
- `passthrough`, `dataflow` — modeled carriers; each entry `{ method, signature }`
- `skipped` — terminal non-carriers; each `{ method, signature, reason }`
- `engine_issues` — a separate bucket for carriers the engine provably can't propagate (built but still dropped); each `{ method, signature, reason }`. Terminal and treated just like `skipped` — the only difference is the reason. `merge-skipped` carries it into `skipped.yaml` as its own `engine_issues` group alongside the regular skipped `methods`.

`dependencies` lists the dependency identifiers a dataflow test project needs. The `build` block tracks the build — `test_project` records each dataflow method's test-project status (`done` if a sample was written into the batch's test project, `failed` if none could be written so the method was excluded from it), and `done` holds the finished `{ method, signature }`. Keep it clear from comments

```yaml
passthrough:
  - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
dataflow:
  - { method: "<qualified-member-b>", signature: "<language-signature-b>" }
skipped:
  - { method: "<qualified-member-c>", signature: "<language-signature-c>", reason: "retains none of its input data" }
engine_issues: []
dependencies: []
build:
  test_project:
    - { method: "<qualified-member-b>", signature: "<language-signature-b>", status: done }
  done: []
```

## Constraints

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis engine. It already propagates through visible application code, calls, aliases, and individual fields; custom rules and approximations model only the assigned source, sink, or opaque-method boundary. Compile-time constants and literals carry no taint, so a source or carrier whose output is only a constant introduces nothing.

- One `<name>` folder per unit — never write into another unit's test project, so concurrent agents don't race
