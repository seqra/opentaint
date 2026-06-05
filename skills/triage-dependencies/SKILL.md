---
name: triage-dependencies
description: Mark which of a project's dependency libraries could introduce taint sources or sinks. Use to start attack-surface discovery
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Triage Dependencies

Read the project's dependency libraries and mark which ones touch a trust boundary — a place untrusted data can enter (source) or a dangerous operation it can reach (sink) — so depth analysis runs only on the libraries that can matter

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the project sources and build files. Default: current directory
- Project model `<model-dir>` — the built model; its `project.yaml` lists every dependency. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record is written. Default: `.opentaint/tracking`

## Workflow

### 1. List the dependencies

Read `<model-dir>/project.yaml` — its `dependencies:` is every jar on the classpath. Resolve each to the library it is. Most of a large project's jars are transitive infrastructure

### 2. Mark each library

For each library decide: could it introduce an attacker-controlled source (e.g. HTTP/RPC request data, message-broker payloads and so on) or a dangerous sink (e.g. query construction, command/file/path ops, deserialization, template/EL, LDAP/JNDI, reflection and so on)?

- clearly irrelevant — build/Gradle plugins, logging, annotations, bytecode tooling (ASM, byte-buddy), test libraries, pure data structures: dismiss
- clearly relevant — web frameworks, query/ORM libraries, HTTP clients, deserializers, template engines, LDAP/JNDI, scripting: flag
- unsure — do a brief peek: grep `<project-root>` sources for the library's package imports or call sites. If the app never references it and nothing transitive exposes it to untrusted data, dismiss; otherwise flag

A library the app references only for safe, constant, or framework-internal use is not a flag — flag where untrusted data plausibly enters or a dangerous call is plausibly reachable

### 3. Record coverage

Write `<tracking-dir>/coverage.yaml` (schema below). One `pending` entry per flagged library — these are the depth work-list. Record dismissals as a single bulk entry summarising the categories ruled out, not one row per jar; add an individual `done` row only for a library a reader might expect to be flagged but isn't, with a one-line reason

## Output

- `<tracking-dir>/coverage.yaml` — flagged libraries `status: pending`, dismissals summarised
- A brief summary to the caller: one line per flagged library (package, why) and the dismissed count. The file holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — one entry per weighed library:

```yaml
packages:
  - package: org.springframework.web.reactive.function   # flagged → depth work-list
    status: pending                                       # pending | done
    notes: WebFlux functional routing — ServerRequest request data (source); WebClient (SSRF sink)
  - package: org.springframework.data.r2dbc
    status: pending
    notes: reactive DB access — check for string-built query sinks
  - package: <infrastructure>
    status: done                                          # bulk dismissal
    notes: >
      logging (logback/slf4j), build plugins, annotations, ASM/byte-buddy, test libs,
      data structures — no source/sink surface
```

## Gotchas

- Don't grep dependency jars to decide — judge from the library's identity and the app's own usage in `<project-root>` sources
- Flag on plausibility, not certainty — depth analysis confirms or drops it; a missed library is a missed vulnerability on all other stages, an over-flag only costs one depth pass

