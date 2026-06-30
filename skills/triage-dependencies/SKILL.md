---
name: triage-dependencies
description: Mark which of a project's dependency libraries could introduce taint sources not already covered by the built-in rules. Use to start source discovery
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Triage Dependencies

Read the project's dependency libraries and mark which ones can introduce a taint source — a place untrusted data enters — that the built-in rules don't already cover, so source discovery runs only on the libraries that can matter. Sinks are found later from the taint frontier, not here

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the project sources and build files. Default: current directory
- Project model `<model-dir>` — the built model; its `project.yaml` lists every dependency. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record is written. Default: `.opentaint/tracking`

## Workflow

### 1. List the dependencies

Read `<model-dir>/project.yaml` — its `dependencies` is every jar on the classpath. Resolve each to the library it is. Most of a large project's jars are transitive infrastructure

### 2. Mark each library

For each library decide: could it introduce an attacker-controlled source — a method returning untrusted data (HTTP/RPC request data, message-broker payloads, deserialized untrusted input and so on) — that the built-in source rules don't already cover? Consult the built-ins with `opentaint health --rules`; a library whose source surface they already match is dismissed, not flagged

- clearly irrelevant — build/Gradle plugins, logging, annotations, bytecode tooling (ASM, byte-buddy), test libraries, pure data structures, and pure sink libraries with no source surface: dismiss
- clearly relevant — web/RPC frameworks, message brokers, deserializers, request clients returning response bodies: flag, unless a built-in source already covers that surface
- unsure — do a brief peek: grep `<project-root>` sources for the library's package imports or call sites. If the app never references it and nothing transitive exposes it to untrusted data, dismiss; otherwise flag

A library the app references only for safe, constant, or framework-internal use is not a flag — flag where untrusted data plausibly enters and no built-in source already names it

### 3. Record coverage

Write `<tracking-dir>/coverage.yaml` (schema below). One `pending` entry per flagged library — these are the depth work-list. Record dismissals as a single bulk entry summarising the categories ruled out, not one row per jar; add an individual `done` row only for a library a reader might expect to be flagged but isn't, with a one-line reason

When `coverage.yaml` already exists from a prior run, reconcile rather than overwrite: keep every existing entry and its `notes`, and add a `pending` entry for any newly-classpath dependency. For each library already `done`, peek its `rules/lib/<package-kebab>.yaml` verdict and the app's current usage — if there's any suspicion the usage has shifted since that verdict (new call sites, a version bump, changed imports), re-mark it `pending`. Over-marking only costs a re-examined library the later stages filter out; leaving a genuinely-changed library `done` silently loses its sources, so when unsure, re-open it

## Output

- `<tracking-dir>/coverage.yaml` — flagged libraries `status: pending`, dismissals summarised
- A brief summary to the caller: one line per flagged library (package, why) and the dismissed count. The file holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — one entry per weighed library:

```yaml
packages:
  - package: org.springframework.web.socket               # flagged → depth work-list
    status: pending                                       # pending | done
    coverage: null                                        # full | partial | none — set by the orchestrator after discover
    notes: WebSocket frame data — untrusted source
  - package: org.springframework.kafka                     # flagged → depth work-list
    status: pending
    coverage: null
    notes: message-broker payloads — untrusted source
  - package: <infrastructure>
    status: done                                          # bulk dismissal
    coverage: null
    notes: >
      logging (logback/slf4j), build plugins, annotations, ASM/byte-buddy, test libs,
      data structures — no source surface
```

## Gotchas

- Don't grep dependency jars to decide — judge from the library's identity and the app's own usage in `<project-root>` sources
- Flag on plausibility, not certainty — depth analysis confirms or drops it; a missed library is a missed vulnerability on all other stages, an over-flag only costs one depth pass

