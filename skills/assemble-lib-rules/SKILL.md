---
name: assemble-lib-rules
description: Group the discovered sources and sinks into per-vuln-class join rule requirements. Use after the discover-attack-surface fan-out, to describe the rules the next phase will write
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Assemble Lib Rules

The per-package passes catalogue sources and sinks but never pair them. With the whole surface inventory in front of you, describe the join rules the next phase will build — one per vuln class, each wiring every source to that class's sinks, mirroring the built-in security rules

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Surface inventory `<surface>` — the discovered sources/sinks. Default: `.opentaint/tracking/surface.yaml`
- Tracking directory `<tracking-dir>` — where the join requirements are written. Default: `.opentaint/tracking`

Built-in rules are available at `opentaint health --rules`

## Workflow

### 1. Read the surface and the built-ins

Read `<surface>` and the built-in rules (`opentaint health --rules`). Note which built-in source/sink lib rules already exist, to ref

### 2. Group sinks by vuln class

The sinks in `<surface>` carry a `vuln_class`; group them. A class needs a join requirement if it has a **new** sink, or if there's any **new** source (a new source must be wired to every class's sink group). Skip a class only when it has no new sink and there's no new source — the built-in join already covers it

### 3. Describe one join requirement per class

For each class, write one `<tracking-dir>/rules/<name>.yaml` (`<name>` = the vuln class), naming:

- every source (built-in refs + the new ones from `<surface>`) — a join aggregates them all, like the built-ins
- that class's sink group (built-in refs + new)
- every library the rule crosses under `dependencies`

A join wires only combinations with a **new** end (new source → any sink, any source → new sink); a built-in source → built-in sink pair is already covered by the built-in join, so leaving it out keeps the join from double-reporting

## Output

- One `<tracking-dir>/rules/<name>.yaml` per vuln-class join, with `stages.description: done`, its `sources`/`sinks`, and `dependencies`
- A brief summary to the caller: one line per join (class, source/sink count, which ends are new). The files hold the detail — don't paste it back

## Tracking

`<tracking-dir>/rules/<name>.yaml` — the join requirement the next phase builds and tests:

```yaml
name: ssrf                    # = the vuln class; becomes the join rule's file and id
rule_id: null                 # filled later
artifact: null
finding: null
requirements: >
  CWE-918 SSRF — join every untrusted-data source to the SSRF sink group
sources:                      # ref a built-in, or a new one to write
  - ref: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - new: ServerRequest body/params — org.springframework.web.reactive.function.server
sinks:
  - new: WebClient.get().uri($UNTRUSTED) — org.springframework.web.reactive.function.client; in DefaultAttachmentService / ProxyFilter
dependencies:
  - org.springframework:spring-webflux:6.1.0
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

## Gotchas

- Describe, don't write — emit requirements only; rules are written and tested in the next phase
- One join per vuln class, aggregating every source — don't write a separate join per source or per package
- Ref a built-in source or sink rather than re-declaring it
