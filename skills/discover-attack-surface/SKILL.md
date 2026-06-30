---
name: discover-attack-surface
description: Analyze project-used members of dependency packages for potential taint sources not covered by the built-in rules. Use for the depth pass of source discovery, working a balanced plan of project-used members, after triage-dependencies flags the libraries
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Take one library the triage flagged, settle what the built-in source rules already cover for the package members this project uses, and write that project-used source plan — the untrusted-data sources actually relevant to this project — for the next phase to build. Sinks are not your job; they're found later from the taint frontier

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Plan `<plan>` — a partition plan (`tracking/rules/plans/<id>.yaml`) assigning the project-used members this agent classifies, grouped by scope; each member's owning package is its FQN's package
- Dependency jars `<deps-dir>` — the project's resolved dependency jars, one per library. Default: `.opentaint/project/dependencies`
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and the per-package lib units live. Default: `.opentaint/tracking`

## Workflow

The `<plan>` holds only members not classified in a prior run. Where a package already has a `rules/lib/<package-kebab>.yaml`, add to it rather than rewriting it, leave its existing entries and their `done` coverage as-is.

### 1. Settle built-in coverage first

Before planning anything, for each package the plan touches see what the built-in source rules already match for its members — browse the rules dir (`opentaint health --rules` prints its path) plus `.opentaint/rules`. Decide one of, and report it to the caller as the package's `coverage`:

- **full** — existing rules already match the project-used package sources → write no lib unit and stop. Don't drill further
- **partial** — existing rules match some project-used sources but miss others → plan only the missing used members
- **none** — plan the package's project-used sources from scratch

### 2. Classify the plan's members

The plan's members are the FQNs under its `scopes` map, the project-used scope already extracted — don't re-enumerate the package API. Find each package's jar in `<deps-dir>` to confirm the dependency identity and inspect signatures/docs while classifying (`unzip -l <jar> | grep <package-as-path>` confirms it owns the package). The bytecode list misses members reached through annotations, class literals, casts, reflection, dynamic proxies, framework dispatch, config strings, or generated code — inspect app source, dependency API/source, and framework config to classify the listed members and to add indirectly-reached ones the list can't show. Never disassemble the analyzer jar.

Find the **sources** among them — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution and more): a method that *returns* attacker-controlled data. NOT a method that merely passes data it was handed along — that's a propagator the engine already handles, not a source. General, not class-tagged

Better safe than sorry — when in doubt, record a borderline source rather than drop it: a false positive is filtered out later at the scan and triage stages, but a real one dropped here is a false negative the run can never recover. Note the doubt, and verify in the package jar when it's quick

Record every source you find under the `<plan>`'s `source` list — that's the only thing you write to the plan. The rest you leave: once all discover agents finish, the orchestrator's `mark-safe` script marks every member no agent flagged a source as `safe`. That `safe` ledger is only what the next run's source partition excludes, never affects sink discovery

### 3. Write the rule plans

For each package the plan touches, write its new sources into `<tracking-dir>/rules/lib/<package-kebab>.yaml` — the dependency GAV, `stages.description: done`, and each source's `builtin` ref (`null` for a fresh source, the built-in to extend otherwise). `<package-kebab>` is the dotted package with `.` → `-`; the `package` field keeps the real dotted name. Leave the unit's `sinks` section empty — analyze-external-methods appends frontier sinks there later. The `coverage.yaml` tally is the orchestrator's — leave it to the caller

## Output

- A `<tracking-dir>/rules/lib/<package-kebab>.yaml` source plan per package the plan touched (for `full` coverage, none)
- The `<plan>` with every source you found recorded under `source` (the orchestrator fills `safe` afterwards)
- A brief summary to the caller: each package's built-in `coverage` verdict (`full` / `partial` / `none`) and the sources planned (one line each, noting fresh vs extending a built-in). The unit holds the detail — don't paste it back

## Tracking

`<plan>` — read your assigned members from the `scopes` map the partition wrote; record the sources you find under a top-level `source` list. The orchestrator's `mark-safe` script fills `safe` (members − sources) after all discover agents finish:

```yaml
id: lib-001
scopes:                        # members partition assigned you, grouped by scope — read these
  org-springframework-web-socket:
    - "org.springframework.web.socket.TextMessage#getPayload"
    - "org.springframework.web.socket.WebSocketSession#getId"
source:                        # the sources you found — the only thing you write to the plan
  - "org.springframework.web.socket.TextMessage#getPayload"
# safe: filled by the orchestrator (mark-safe) — examined, not a source
```

`<tracking-dir>/rules/lib/<package-kebab>.yaml` — the source plan; fill only the discovery-stage fields (create-test-project and create-rule fill the rest):

```yaml
package: org.springframework.web.socket
dependencies:
  - org.springframework:spring-websocket:6.1.0
sources:                       # general, not class-tagged — the only side you write
  - idea: TextMessage.getPayload — untrusted WebSocket frame data
    builtin: null              # null = fresh source; a built-in ref = extend it with the missing methods
    rule_id: null
sinks: []                      # left empty — analyze-external-methods appends frontier sinks here later
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

## Engine notes

- Generic projects: the analyzer treats all public/protected methods of public classes as entry points
- Stored / second-order injection (data persisted then read back) is modeled by the engine on its own — don't plan a source for the read-back or a propagator for the store→read path

## Gotchas

- Plan, don't write — record source ideas only; the lib rules are written and tested in the next phase
- Don't re-declare a source a built-in already matches — set its `builtin` ref and list only the missing used methods, or fold it into the package's `full` coverage
- Classify only the plan's members — they are already the project-used scope; don't enumerate the rest of the package API
- Record only the sources; don't hand-list `safe` — the orchestrator's mark-safe script marks every member you didn't flag a source
