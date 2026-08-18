---
name: triage-dependencies
description: Mark which of a project's dependency libraries could introduce taint sources. Use to start source discovery
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Triage Dependencies

Read the project's dependency libraries and flag the ones that can introduce a taint source — a place untrusted data enters

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory

## Workflow

### 1. List the dependencies

Read `.opentaint/project/project.yaml` — the `dependencies:` list under each per-language projects entry (e.g. `javaProjects:`) is every third-party dependency the model resolved. Resolve each to the library it is. Most of a large project's dependencies are transitive infrastructure

### 2. Mark each library

For each library decide: could it introduce an attacker-controlled source — a method returning untrusted data (HTTP/RPC request data, message-broker payloads, deserialized untrusted input and so on)? Judge by the library's identity itself, read sources to get overviews, docs

### 3. Write the flag list

Write in `.opentaint/tracking/coverage.yaml` (per Tracking) a flat list of the flagged libraries' packages

When `coverage.yaml` already exists from a prior run, reconcile rather than overwrite: keep every listed package and add any dependency newly added to the model that could introduce a source. A flagged package whose usage shifted (new call sites, a version bump) needs no re-open — source discovery automatically plans any used member not yet verdicted. When unsure whether a package belongs, list it: an over-flag only costs one discovery pass, a missed library loses its sources on every later stage

### 4. Verify before returning

Re-check the full dependency list against your flags: confirm every dependency was judged, then re-read the ones you did NOT flag and make sure none of them can actually introduce a source. A library left out here loses its sources on every later stage and the run can't recover it. Add any package you missed to the list. This is a re-read of what you already wrote — simple grep or re-read is fine, no need to use some scripts.

## Output

Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/coverage.yaml` — the flagged packages list

### Summary:

- one line per flagged package: the package and why it was flagged

## Tracking

`.opentaint/tracking/coverage.yaml` — a flat list of the dependency packages flagged to drill for taint sources. Keep it clear from comments

```yaml
packages:
  - org.springframework.web.socket
  - org.springframework.kafka
```
