---
name: discover-attack-surface
description: Analyze a dependency package for potential sources and sinks not covered by the built-in rules. Use for the depth pass of attack-surface discovery, one package at a time, after triage-dependencies flags it
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Take one library the triage flagged, settle what the built-in rules already cover, and write the package's rule plan — the untrusted-data sources and dangerous sinks it introduces — for the next phase to build

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Package `<package>` — the flagged library to drill (a `pending` entry in `coverage.yaml`)
- Dependency jars `<deps-dir>` — the project's resolved dependency jars, one per library. Default: `.opentaint/project/dependencies`
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and the per-package lib units live. Default: `.opentaint/tracking`

## Workflow

### 1. Settle built-in coverage first

Before enumerating anything, see what the built-ins already match for this package — read the lib rules (`opentaint health --rules`) plus `.opentaint/rules`. Decide one of:

- **full** — the built-ins already match the package's relevant sources/sinks → write no lib unit, flip the `coverage.yaml` entry to `done` with a `builtin_coverage: full` note, and stop. Don't drill further
- **partial** — built-ins match some but miss methods/overloads/classes → plan only the missing ones (`coverage: expand`, ref the built-in for the rest)
- **none** — plan the package's surface from scratch

### 2. Enumerate sources and sinks from the package jar

Find the package's jar in `<deps-dir>` (match the artifact from the dependency GAV; `unzip -l <jar> | grep <package-as-path>` confirms it owns the package) and read its compiled API with `javap` / `unzip` — capture as many real sources and sinks as the package exposes, not just the ones the app happens to call today. `scripts/package-usages.py --package <package> --model-dir <model-dir> --output <file>` can reduce this to functions the project actually calls; use it only as a prioritization aid. Still confirm against source/API for framework entrypoints, type-only/annotation/config APIs, reflection/proxies, and library-internal behavior behind a public call. Never read the analyzer jar — only dependency jars

- **sources** — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution): a method that *returns* attacker-controlled data — HTTP/RPC request data, a message-broker payload. NOT a method that merely passes data it was handed along — that's a propagator the engine already handles, not a source. General, not class-tagged
- **sinks** — dangerous operations (query construction, command/file/path ops, deserialization, template/EL, LDAP/JNDI, reflection); tag each with its vuln class (`ssrf`, `sqli`, `path-traversal`, …)

Verify each is real before recording: a source genuinely attacker-controlled, a sink genuinely dangerous with tainted input. Don't trace a flow between them — the analyzer pairs them at scan time

### 3. Write the package's rule plan

Write `<tracking-dir>/rules/lib/<package-kebab>.yaml` — its new sources, its sinks grouped by `vuln_class`, the dependency GAV, `stages.description: done`, and each `coverage: new` or `expand`. Then flip the package's `coverage.yaml` entry to `status: done`. `<package-kebab>` is the dotted package with `.` → `-`; the `package:` field keeps the real dotted name

## Output

- A `<tracking-dir>/rules/lib/<package-kebab>.yaml` rule plan (or, for `full` coverage, none — just the coverage note)
- The package's `coverage.yaml` entry set `status: done` with a one-line `notes`
- A brief summary to the caller: the sources and sinks planned (one line each, marked `new` / `expand`). The unit holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — flip this package's entry when done:

```yaml
  - package: org.springframework.web.reactive.function.client
    status: done
    notes: WebClient request methods — SSRF sink; built-ins cover get(), expand with post()/put(); no new source
```

`<tracking-dir>/rules/lib/<package-kebab>.yaml` — the rule plan; fill only the discovery-stage fields (create-test-project and create-rule fill the rest):

```yaml
package: org.springframework.web.reactive.function.client
dependencies:
  - org.springframework:spring-webflux:6.1.0
builtin_coverage: partial      # partial | none
sources:                       # general, not class-tagged
  - idea: ServerRequest body/params/headers — untrusted request data
    coverage: new              # new | expand
    builtin: null
    rule_id: null
sinks:                         # grouped by vuln class
  - vuln_class: ssrf
    idea: WebClient.get/post/put().uri($UNTRUSTED)
    coverage: expand
    builtin: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
    rule_id: null
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

## Engine notes

- Spring projects: the analyzer auto-discovers Spring endpoints, so `network` inbound sources are largely ones the built-ins already see — focus on the sinks
- Generic projects: the analyzer treats all public/protected methods of public classes as entry points
- Stored / second-order injection (data persisted then read back) is modeled by the engine on its own — don't plan a source for the read-back or a propagator for the store→read path

## Gotchas

- Plan, don't write — record source/sink ideas only; the lib rules are written and tested in the next phase
- Don't re-declare a source or sink a built-in already matches — `coverage: expand` with only the missing methods, or fold it into `full` coverage
