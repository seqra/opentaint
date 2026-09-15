---
name: discover-attack-surface
description: Classify project-used dependency members and record taint sources as rule-authoring units. Use for the source-discovery depth pass
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Discover Attack Surface

Work one assignment of project-used dependency members and pick out the taint sources among them — the methods where untrusted data first enters. The assigned language reference defines the concrete inspection commands and identifier formats for the workflow below.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `plan` (required) — path to this agent's partition plan `.opentaint/tracking/rules/plans/<id>.yaml`: the project-used dependency members to classify

## Workflow

Read `references/<language>.md` before starting. Its numbered steps provide the language-specific details for the workflow below.

### 1. Inspect the plan's members

The assigned plan's `scopes` contains the already-extracted project-used dependency members that still need a verdict. Inspect only those members. Confirm their dependency identity and exact signatures, then read application source, dependency source and API documentation, representative usages, and relevant framework configuration to understand how data enters the project.

### 2. Classify the plan's members

A source is the exact boundary where untrusted data first enters from a network, persistence, serialization, messaging, execution, or another external channel. For a callable member, decide whether it returns or otherwise exposes attacker-controlled data. A member that merely passes along data it was handed is a propagator, not a source.

Classify behavior rather than package or class names. For an individual member, prefer recording a borderline source with the uncertainty noted: later scan and triage can reject a false positive, while an omitted source becomes an unrecoverable false negative.

### 3. Record verdicts and source units

Complete the plan's source list in the form required by the language reference. Record every discovered source in its plan and write its source unit with `tag: untrusted-data-source`; resolving that unit to an existing or new rule happens later in `create-rule`. Non-sources create no unit. Mark an empty result explicitly so the reconcile join can distinguish it from a plan whose agent never returned. Where an owned unit already exists, merge new entries without rewriting its existing entries or stages.

### 4. Verify before returning

Re-check the full assigned scope against the classification. Re-read every rejected member and make sure it does not establish an external-input boundary. Confirm every source appears both in the completed plan and its source unit, no rejected member has a unit, and no pending/null verdict remains.

## Output

Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/rules/sources/<unit>.yaml` — each source unit required by the completed plan
- the assigned plan with the discovered sources recorded under `source`

### Summary:

- the source members found, one line each
- anything blocked or left uncertain

## Tracking

`.opentaint/tracking/rules/sources/<package-kebab>.yaml` — one source unit per package (a dependency can span several packages), the file named for that package with `.` → `-`. `tag` is always the reusable `untrusted-data-source` group. `dependencies` names the dependency the package comes from, `sources` each an entry point `{ method, signature, note, rule_id }` (`method` and `signature` use the exact language-specific identifiers from the plan), `stages` tracks the unit through rule authoring, and a `blocker` string is added under it when the unit can't be made to pass. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
tag: untrusted-data-source
sources:
  - { method: "<qualified-member>", signature: "<language-signature>", note: untrusted message payload, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

This skill sets `tag: untrusted-data-source`, fills `dependencies`, and adds one `{ method, signature, note, rule_id }` entry per source. Copy `method` + `signature` from the plan, explain why the data is untrusted in `note`, and leave `rule_id: null` and the stages for rule authoring.

The plan `.opentaint/tracking/rules/plans/<id>.yaml` — read your members from its `scopes` map, record the sources you find under a top-level `source` list; the join then ledgers `source` + `safe` (members − source), keyed by the exact method and signature so distinct callable variants stay separate. It is regenerable and disposable, not durable state:

```yaml
id: lib-001
scopes:
  <package-kebab>:
    - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
    - { method: "<qualified-member-b>", signature: "<language-signature-b>" }
source:
  - { method: "<qualified-member-a>", signature: "<language-signature-a>" }
```

`source: null` is the generated plan's unprocessed sentinel. On completion, replace it with the exact sources found, or `source: []` when there are none; `mark-safe` leaves a null plan for re-dispatch instead of incorrectly classifying all its members as safe. Every member listed as a source must also appear in its source unit.

## Constraints

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis engine. It already propagates through visible application code, calls, aliases, and individual fields; custom rules and approximations model only the assigned source, sink, or opaque-method boundary. Compile-time constants and literals carry no taint, so a source or carrier whose output is only a constant introduces nothing.

- This stage finds only sources — the boundaries where untrusted data enters, sinks are found later from the taint frontier
- Work only your own plan and the source units it maps to — never another agent's plan or unit, shared coverage/classification state, or `tags.yaml`. Plans partition their write ownership according to the language reference
- Stored / second-order injection (data persisted then read back) is modeled by the engine itself — don't record a source for the read-back or a propagator for the store→read path
