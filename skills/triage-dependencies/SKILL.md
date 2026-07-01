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
- Tracking directory `<tracking-dir>` — where the flagged-package list is written. Default: `.opentaint/tracking`

## Workflow

### 1. List the dependencies

Read `<model-dir>/project.yaml` — its `dependencies` is every jar on the classpath. Resolve each to the library it is. Most of a large project's jars are transitive infrastructure

### 2. Mark each library

For each library decide: could it introduce an attacker-controlled source — a method returning untrusted data (HTTP/RPC request data, message-broker payloads, deserialized untrusted input and so on) — that the built-in source rules don't already cover? Consult the built-ins with `opentaint health --rules`; a library whose source surface they already match is dismissed, not flagged

- clearly irrelevant — build/Gradle plugins, logging, annotations, bytecode tooling (ASM, byte-buddy), test libraries, pure data structures, and pure sink libraries with no source surface: dismiss
- clearly relevant — web/RPC frameworks, message brokers, deserializers, request clients returning response bodies: flag, unless a built-in source already covers that surface
- unsure — do a brief peek: grep `<project-root>` sources for the library's package imports or call sites. If the app never references it and nothing transitive exposes it to untrusted data, dismiss; otherwise flag

A library the app references only for safe, constant, or framework-internal use is not a flag — flag where untrusted data plausibly enters and no built-in source already names it

### 3. Write the flag list

Write `<tracking-dir>/coverage.yaml` (schema below) — a flat list of the flagged libraries' packages, the depth work-list. Only flagged packages go in; dismissed libraries are simply absent. A package needs no status: it stops being drilled implicitly once the discover partition finds all its used members already verdicted in `classification.yaml`

When `coverage.yaml` already exists from a prior run, reconcile rather than overwrite: keep every listed package and add any newly-classpath dependency package that could introduce a source. A flagged package whose usage shifted (new call sites, a version bump) needs no re-open — the discover partition automatically plans any used member not yet verdicted. When unsure whether a package belongs, list it: an over-flag only costs one depth pass, a missed library loses its sources on every later stage

## Output

- `<tracking-dir>/coverage.yaml` — the flat list of flagged packages
- A brief summary to the caller: one line per flagged package (package, why) and the dismissed count. The file holds only the packages — the reasoning is your summary, not stored

## Tracking

`<tracking-dir>/coverage.yaml` — a flat list of the packages flagged to drill for sources; nothing else (dismissed libraries are absent, "done" is implicit once discover verdicts all a package's used members):

```yaml
packages:
  - org.springframework.web.socket
  - org.springframework.kafka
```

## Gotchas

- Don't grep dependency jars to decide — judge from the library's identity and the app's own usage in `<project-root>` sources
- Flag on plausibility, not certainty — depth analysis confirms or drops it; a missed library is a missed vulnerability on all other stages, an over-flag only costs one depth pass

