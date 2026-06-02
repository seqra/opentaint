---
name: assemble-lib-rules
description: Pair the unpaired sources and sinks left by discovery into join rules. Use for assembling lib rules
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Assemble Lib Rules

The per-package discovery passes each see only their own library, so a source whose sink sits elsewhere is parked unpaired. With the loose pieces from every package in front of you, pair each into a join — the place a source and a sink finally become a detectable vulnerability

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Loose pieces `<lib-pieces>` — the unpaired sources/sinks from discovery. Default: `.opentaint/tracking/lib-pieces.yaml`
- Project root `<project-root>` — the project sources, to confirm a source can actually reach a sink. Default: current directory
- Tracking directory `<tracking-dir>` — where rule requirements are written. Default: `.opentaint/tracking`

Built-in rules are available at `opentaint health --rules`

## Workflow

### 1. Read the pieces and what's already covered

Read `<lib-pieces>`, the built-in rules (`opentaint health --rules`), `.opentaint/rules`, and the join requirements already in `<tracking-dir>/rules`. A piece a built-in or an existing join already covers needs no new rule

### 2. Pair source-first

For each `pending` source, find the dangerous sinks it can reach — among the loose sinks, the built-in sink rules, and the app's own dangerous operations. Reach is a code-level question (does the source's data flow toward that sink anywhere in `<project-root>`), not a taint trace — the scan does the tracing; you decide the pairing is plausible. Then per real pairing write one join requirement `<tracking-dir>/rules/<name>.yaml`, named `<context>-<vuln-class>` in kebab-case, naming the source end and sink end (which a built-in covers, which must be written) and every library the flow crosses under `dependencies`. Set that source piece's `disposition` to the join name

### 3. Mop up sinks, then resolve every piece

A `pending` sink a source you just placed feeds is already in a join; a loose sink reached only by a built-in source gets its own join. Then resolve what's left: a source with no dangerous sink anywhere, a sink with no source in reach, or a piece a built-in already covers → set `disposition: dropped: <reason>`. Leave no `pending` entry — an unresolved piece is an un-modeled source or sink

## Output

- One `<tracking-dir>/rules/<name>.yaml` per join assembled, schema as discover-attack-surface writes it (`stages.description: done`, short `requirements`, `dependencies`)
- Every `<lib-pieces>` entry resolved — `disposition` is a join name or `dropped: <reason>`
- A brief summary to the caller: one line per join (name, source→sink) and the paired/dropped counts. The tracking files hold the detail — don't paste it back

## Tracking

`<lib-pieces>` — resolve each entry's `disposition`:

```yaml
sources:
  - role: Apache HttpClient response body — data from a server the app calls
    package: org.apache.hc.client5.http
    dependency: org.apache.httpcomponents.client5:httpclient5:5.3
    disposition: httpclient-ssrf      # the join it went into
sinks:
  - role: SnakeYAML load — untrusted YAML deserialization
    package: org.yaml.snakeyaml
    dependency: org.yaml:snakeyaml:2.2
    disposition: "dropped: no untrusted source reaches a SnakeYAML load in this app"
```

The join requirements themselves use the `rules/<name>.yaml` schema discover-attack-surface writes

## Gotchas

- Write requirements, not rule files — create-rule authors the lib source/sink YAMLs and the join from the requirement downstream
- Pair only a flow that exists in the app — a join whose source can't reach its sink wastes a test project and never converges; confirm reachability in `<project-root>`
- Reference a built-in source or sink where one fits rather than requiring a new one
- Resolve every piece — drop with a reason, never silently leave one `pending`
