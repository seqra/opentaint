---
name: discover-attack-surface
description: Analyze a dependency package for potential sources and sinks not covered by the built-in rules. Use for the depth pass of attack-surface discovery, one package at a time, after triage-dependencies flags it
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Take one library the triage flagged and record the untrusted-data sources and dangerous sinks it introduces

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Package `<package>` — the flagged library to drill (a `pending` entry in `coverage.yaml`)
- Project root `<project-root>` — the project sources. Default: current directory
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and surface inventory live. Default: `.opentaint/tracking`
- Surface inventory `<surface>` — the running list of discovered sources/sinks. Default: `.opentaint/tracking/surface.yaml`

## Workflow

Requires a built project model — without it you can miss entry points the analyzer actually sees

### 1. Find how the project uses the package

Search through `<project-root>` sources for `<package>`'s imports and call sites. List the distinct methods of it the app calls — these, not the library's whole API, are the surface that matters

### 2. Identify sources and sinks

Among the used methods, pick out the **sources** — methods returning attacker-controlled data (HTTP/RPC request data, message-broker payloads, second-order rows read back) — and the **sinks** — dangerous operations (query construction, command/file/path ops, deserialization, template/EL evaluation, LDAP/JNDI, reflection). Catalogue each end on its own; don't trace a flow between them — the analyzer pairs them at scan time

For each, check whether a built-in rule already matches it (`opentaint health --rules` + `.opentaint/rules`); a built-in match records its ref instead of a new idea. Tag each sink with its vuln class (`ssrf`, `sqli`, `path-traversal`, …); sources aren't class-tagged

Verify each is real before recording it: a source is genuinely attacker-controlled (a request param, header, body, or message payload is; an app constant or server config is not), a sink genuinely dangerous with tainted input (string-built SQL is; a parameterized query is not)

### 3. Record into the surface inventory

Append each source and sink to `<surface>` (schema below) — for a new one, a short idea of the pattern and where it lives; for a covered one, the built-in ref. Then flip the package's `coverage.yaml` entry to `status: done` with a one-line `notes`. Write it the moment you finish so the walk resumes cleanly

## Output

- Sources and sinks the package introduces appended to `<surface>`
- The package's `coverage.yaml` entry set `status: done` with a one-line `notes`
- A brief summary to the caller: the sources and sinks found (one line each, new vs built-in-covered). The inventory holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — flip this package's entry when done:

```yaml
  - package: org.springframework.web.reactive.function.client
    status: done
    notes: WebClient request methods — SSRF sink not covered by built-ins; no new source
```

`<tracking-dir>/surface.yaml` — append what the package introduces (`builtin: null` ⇒ new, to be written next phase):

```yaml
sources:                       # general untrusted-data sources
  - package: org.springframework.web.reactive.function.server
    idea: ServerRequest body/params/headers — untrusted request data; in RouterFunctions
    builtin: null
    dependency: org.springframework:spring-webflux:6.1.0
sinks:                         # tagged by vuln class
  - package: org.springframework.web.reactive.function.client
    vuln_class: ssrf
    idea: WebClient.get().uri($UNTRUSTED); in DefaultAttachmentService / ProxyFilter
    builtin: null
    dependency: org.springframework:spring-webflux:6.1.0
```

## Engine notes

- Spring projects: the analyzer auto-discovers Spring endpoints, so `network` inbound sources are largely ones the built-ins already see — focus on the sinks
- Generic projects: the analyzer treats all public/protected methods of public classes as entry points

## Gotchas

- Describe, don't write — record source/sink ideas only; rules are written and tested in the next phase
- Don't re-declare a built-in source or sink — record its ref instead
- Don't grep dependency jars to find usage — read the app's own sources in `<project-root>`
