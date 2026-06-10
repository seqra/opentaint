---
name: discover-attack-surface
description: Analyze project-used members of a dependency package for potential sources and sinks not covered by the built-in rules. Use for the depth pass of attack-surface discovery, one package at a time, after triage-dependencies flags it
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Take one library the triage flagged, settle what the built-in rules already cover for the package members this project uses, and write that project-used rule plan — the untrusted-data sources and dangerous sinks actually relevant to this project — for the next phase to build

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Package `<package>` — the flagged library to drill (a `pending` entry in `coverage.yaml`)
- Dependency jars `<deps-dir>` — the project's resolved dependency jars, one per library. Default: `.opentaint/project/dependencies`
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and the per-package lib units live. Default: `.opentaint/tracking`

## Workflow

### 1. Settle built-in coverage first

Before planning anything, see what the built-ins already match for this package's project-used members — read the lib rules (`opentaint health --rules`) plus `.opentaint/rules`. Decide one of:

- **full** — the built-ins already match the project-used package sources/sinks → write no lib unit, flip the `coverage.yaml` entry to `done` with a `builtin_coverage: full` note, and stop. Don't drill further
- **partial** — built-ins match some project-used methods/overloads/classes but miss others → plan only the missing used members (`coverage: expand`, ref the built-in for the rest)
- **none** — plan the package's project-used surface from scratch

### 2. Scope project-used sources and sinks

Find the package's jar in `<deps-dir>` only to confirm the dependency identity and inspect signatures/docs for members already in scope (match the artifact from the dependency GAV; `unzip -l <jar> | grep <package-as-path>` confirms it owns the package). To get the bytecode-derived list of package methods the project statically references, run this skill's bundled `scripts/package-usages.sh <model-dir> <package>` (Windows: `scripts/package-usages.ps1`; the scripts live in the skill directory, not the project) and save its output to `<tracking-dir>/usage/<package-kebab>.yaml` (create `usage/` if needed). It reads `moduleClasses`/`packages:` from `project.yaml` and disassembles the project's **own** compiled classes only — a model's `moduleClasses` can mix project + dependency jars/dirs, so when the modules carry a `packages:` list only classes under those roots are scanned, otherwise `moduleClasses` is already project-only — then prints the deduped `// Method`/`// InterfaceMethod` call sites whose owner is in `<package>`.

This catches only bytecode invocations, so it misses members reached through annotations, class literals, casts, reflection, dynamic proxies, framework/container dispatch, config strings, or generated code absent from the model. Treat the output as the main used-in-project scope, then inspect app source, dependency API/source, and framework configuration only to classify those used members and to add indirectly reached members the bytecode list cannot show. Do not enumerate the whole package API. Never disassemble the analyzer jar — only the project's own classes

- **sources** — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution): a method that *returns* attacker-controlled data — HTTP/RPC request data, a message-broker payload. NOT a method that merely passes data it was handed along — that's a propagator the engine already handles, not a source. General, not class-tagged
- **sinks** — dangerous operations (query construction, command/file/path ops, deserialization, template/EL, LDAP/JNDI, reflection); tag each with its vuln class (`ssrf`, `sqli`, `path-traversal`, …)

Verify each is real before recording: a source genuinely attacker-controlled, a sink genuinely dangerous with tainted input. Don't trace a flow between them — the analyzer pairs them at scan time

### 3. Write the package's rule plan

Write `<tracking-dir>/rules/lib/<package-kebab>.yaml` — only the project-used new sources and sinks, grouped by `vuln_class`, the dependency GAV, `stages.description: done`, and each `coverage: new` or `expand`. Then flip the package's `coverage.yaml` entry to `status: done`. `<package-kebab>` is the dotted package with `.` → `-`; the `package:` field keeps the real dotted name

## Output

- A `<tracking-dir>/rules/lib/<package-kebab>.yaml` rule plan for project-used members only (or, for `full` coverage, none — just the coverage note)
- A `<tracking-dir>/usage/<package-kebab>.yaml` package usage snapshot from `package-usages.sh`
- The package's `coverage.yaml` entry set `status: done` with a one-line `notes`
- A brief summary to the caller: the sources and sinks planned (one line each, marked `new` / `expand`). The unit holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — flip this package's entry when done:

```yaml
  - package: org.springframework.web.reactive.function.client
    status: done
    notes: WebClient request methods — SSRF sink; built-ins cover get(), expand with post()/put(); no new source
```

`<tracking-dir>/usage/<package-kebab>.yaml` — temporary-but-persisted project-used scope. Keep it next to the rule plans so resumed agents can reuse it instead of rerunning extraction:

```yaml
functions:
  - function: "org.springframework.web.reactive.function.client.WebClient#get()Lorg/springframework/web/reactive/function/client/WebClient$RequestHeadersUriSpec;"
classes:
  - class: "org.springframework.web.reactive.function.client.WebClient"
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
- Don't re-declare a source or sink a built-in already matches — `coverage: expand` with only the missing used methods, or fold it into `full` coverage
- Don't add unused package APIs just because they look security-relevant — this phase scopes rules to what the project uses or reaches indirectly
