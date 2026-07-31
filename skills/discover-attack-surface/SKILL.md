---
name: discover-attack-surface
description: Classify project-used dependency members and record the taint sources among them not covered by the built-in rules. Use for the source-discovery depth pass
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Discover Attack Surface

Work one assignment of project-used dependency members and pick out the taint sources among them — the methods where untrusted data first enters. The concrete inspection commands and value formats are language-specific — read `references/<language>.md` per Inputs and follow its numbered steps, which key to the ones below

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `plan` (required) — path to this agent's partition plan `.opentaint/tracking/rules/plans/<id>.yaml`: the project-used members to classify

## Workflow

### 1. Settle built-in coverage first

Before anything, for each package the plan touches see what the built-in source rules already match for its members — `opentaint health --rules` prints the built-in rules root path; browse it and the project's own rules (per the language reference). This decides whether you write a source unit:

- full — existing rules already match the project-used sources → write no unit, stop, don't drill further
- partial — some project-used sources matched, others missed → plan only the missing used members
- none — plan the package's project-used sources from scratch

### 2. Classify the plan's members

The members are the FQNs under the plan's `scopes` — the project-used scope, already extracted, and only the members not yet classified in a prior run. Confirm each package's dependency identity and inspect its signatures/docs while classifying (per the language reference); read app source, dependency API/docs, and framework config to classify the listed members.

Find the sources among them — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution and more): a method that returns attacker-controlled data. NOT a method that merely passes along data it was handed — that's a propagator the engine already handles. General, not class-tagged.

Better safe than sorry — when in doubt, record a borderline source rather than drop it: a false positive is filtered out later at the scan and triage stages, but a real one dropped here is a false negative the run can never recover. Note the doubt, and verify in the dependency when it's quick.

### 3. Write the source units

Two writes, both per Tracking: record every source under the plan's top-level `source` list, and write each package's sources into its source unit. Always write the `source` list — an empty list when the plan yields no source — so the reconcile join can tell your finished plan from one whose agent never returned (a plan still carrying `source: null` is left for re-dispatch, not merged). Where a package already has a unit from a prior run, add to it rather than rewriting — leave its existing entries and stages as-is.

### 4. Verify before returning

Re-check the full plan against your classification: confirm every plan member is accounted for, then re-read the ones you did NOT record as sources and make sure none of them is actually a source. A source left out here is a false negative the run can never recover. Add any you missed to the `source` list and its unit. This is a re-read of what you already wrote — simple grep or re-read is fine, no need to use some scripts.

## Output

Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/rules/sources/<package-kebab>.yaml` — the source unit(s), one per package the plan touched (none for a fully-covered package)
- `.opentaint/tracking/rules/plans/<id>.yaml` — your plan, with the sources recorded under `source`

### Summary:

- the sources found, one line each, and any package already fully covered
- anything blocked or left uncertain

## Tracking

`.opentaint/tracking/rules/sources/<package-kebab>.yaml` — one source unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sources` each an entry point `{ method, signature, note, rule_id }` (`signature` the member's JVM descriptor, always quoted so array types `[…` stay valid YAML in a flow mapping), `stages` tracks the unit through rule authoring, and a `blocker` string is added under it when the unit can't be made to pass. Keep it clear from comments

```yaml
dependencies:
  - org.springframework:spring-websocket:6.1.0
sources:
  - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;", note: untrusted WebSocket frame data, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

This skill fills `dependencies` (the package's dependency identifier) and one `sources` entry per source it found — `{ method, signature, note, rule_id }` with `method` + `signature` copied from the plan and `note` a few words on why the data is untrusted; leave `rule_id: null` and the `stages` for the rule-authoring stage. One unit per package the plan touched.

The plan `.opentaint/tracking/rules/plans/<id>.yaml` — read your members from its `scopes` map, record the sources you find under a top-level `source` list; the join then ledgers `source` + `safe` (members − source), keyed per method+signature so an overload stays distinct. It is regenerable and disposable, not durable state:

```yaml
id: lib-001
scopes:
  <package-kebab>:
    - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;" }
    - { method: org.springframework.web.socket.WebSocketSession#getId, signature: "()Ljava/lang/String;" }
source:
  - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;" }
```

## Constraints

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis engine. It already propagates through visible application code, calls, aliases, and individual fields; custom rules and approximations model only the assigned source, sink, or opaque-method boundary. Compile-time constants and literals carry no taint, so a source or carrier whose output is only a constant introduces nothing.

- This stage finds only sources — the methods where untrusted data enters; sinks are found later from the taint frontier.
- Work only your own plan and the source units its packages map to — never another agent's plan or unit, and never `coverage.yaml`. Plans partition packages disjointly, so each source unit has a single writer.
- Stored / second-order injection (data persisted then read back) is modeled by the engine itself — don't record a source for the read-back or a propagator for the store→read path.
- For a generic project the analyzer treats every public/protected method of a public class as an entry point.
