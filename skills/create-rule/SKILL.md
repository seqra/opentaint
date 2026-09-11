---
name: create-rule
description: Author and verify an OpenTaint rule. Use whenever a rule creation is needed
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Create Rule

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis engine. It already propagates through visible application code, calls, aliases, and individual fields; custom rules and approximations model only the assigned source, sink, or opaque-method boundary. Compile-time constants and literals carry no taint, so a source or carrier whose output is only a constant introduces nothing.

A unit names the source or sink members to detect. Identify an existing built-in or project library rule when it already implements the boundary, otherwise author a custom rule, then verify the unit against its test project. Every selected or created source rule must carry the unit's `untrusted-data-source` tag, and every selected or created sink rule must carry its unit group's `*-sink` tag. Production joins use those tags and are assembled later only when a new sink tag needs one.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `side` (required) — `sources` or `sinks`; the unit's side. It selects the unit file, the sample style, and the test sub-project
- `unit` (required) — the `<package-kebab>` identifying the unit. Its spec and tracking are in `.opentaint/tracking/rules/<side>/<unit>.yaml`; its test project is `.opentaint/test-projects/<unit>/<side>` and its compiled model `.opentaint/test-compiled/<unit>/<side>`
- `fix-target` (optional) — a created rule `<path>#<id>` the main scan flagged, plus the false positive or false negative to correct. When set, narrow or broaden that one rule instead of authoring from the unit

## Workflow

### 1. Check existing coverage

Browse the built-in library rules and `.opentaint/rules` to determine whether one already matches each unit entry. When one does, do not author a duplicate: set its `rule_id` in `.opentaint/tracking/rules/<side>/<unit>.yaml` to `<relative-yaml-path>#<rule-id>`. This string is tracking bookkeeping only. Do not add a `rule` reference to any production rule, production joins remain tag-based and are written later. The following command prints the built-in rules root path. Browse both roots using the language reference and search by the entry's exact language-specific identifier:

```bash
opentaint health --rules
```

Read `.opentaint/tracking/rules/tags.yaml`. A source unit must carry `tag: untrusted-data-source`, each sink unit group carries the one existing or newly registered `*-sink` tag its rules must extend.

In fix mode, don't author from the unit: go straight to that one flagged rule, adjust it by the false-positive/negative guidance per step 4, re-run this side's tests, and stop — leave the unit's other entries untouched. Otherwise, when entries already carry `rule_id`, continue from those recorded implementations and author only entries still lacking coverage. When the unit is partway (some stages `done`, some not), continue from the first unfinished stage on the artifacts already on disk rather than restarting.

### 2. Author the library rules

Derive each rule's pattern from the unit's exact member identifiers, recorded signatures, and relevant declaration metadata. Bind the tainted value to `$UNTRUSTED` and put the unit/group tag on the lib rule. A sink tag belongs to the whole semantic group, not to an individual method. One rule can cover several group methods and several rules can carry the same tag. The rule forms and locations are in the language reference.

For `side: sinks`, iterate `groups`: ensure every method under `groups[].sinks` has an implementing `rule_id`, and put the enclosing `groups[].tag` on every custom rule you create. For `side: sources`, use the unit's top-level tag.

### 3. Write the test joins

A library rule emits nothing on its own — to exercise it, wire it to the generic taint marker in a throwaway test join. Write one join for the side into the test project's marker rules, referencing the generic marker on one end and each lib `rule_id` selected for the unit on the other, so a positive sample's tainted value flows marker-to-rule (a sink side) or rule-to-marker (a source side). The test joins live only in the test project, never in the scanned rules tree. Their form, naming, and location are in the language reference.

### 4. Test until success

Run the rule tests directly as a foreground, blocking command and wait for exit — never background them or use Monitor. Load your lib rules and the test joins + markers, and iterate until every sample passes:

```bash
opentaint test rule run .opentaint/test-compiled/<unit>/<side> \
  -o .opentaint/test-results/<unit>/<side> \
  --ruleset .opentaint/rules --ruleset .opentaint/test-projects/<unit>/<side>/test-rules \
  --passthrough-approximations .opentaint/pass-through
```

`test rule run` auto-loads the built-in rules, so pass only your custom rulesets. Apply the passthrough approximations as-is, an empty one is harmless. Read the result with the bundled script — it prints the pass/fail counts and names the failing samples, so you never parse the JSON by hand:

```bash
uv run <skill-dir>/scripts/check-test-result.py <unit>/<side>
```

Fix by the verdict it reports:

- `falseNegative` → the match is too narrow, broaden it and confirm the metavariable names line up across branches and between `refs` and `on`
- `falsePositive` → the match is too broad, add an exclusion or a sanitizer
- `skipped` / `disabled` → the rule wasn't exercised; fix the sample's `rule-test.yaml` entrypoint or `rule-id`, or enable the rule

The concrete pattern operators for each fix are in the language reference.

### 5. Escalate when a positive won't converge

A positive that won't pass after ~3 rule fixes may have a cause no rule edit can fix. Localize the cause per `references/debugging.md`, then leave `stages.tests_passing: pending` and report it (per Output), rather than editing blindly.

## Output

### Artifacts

- the custom library rule file(s) under `.opentaint/rules`
- `.opentaint/tracking/rules/<side>/<unit>.yaml` — the unit's entries updated (per Tracking)

### Summary

- the implementing lib rule ids, identifying which were built-in and which were created, a one-line test summary for the side, and the exact `test rule run` command used
- if blocked at step 5: `stages.tests_passing` left pending, and the cause —
  - a dropped library method on the failing sample's flow → the methods that need a model, to be approximated before a re-dispatch
  - nothing dropped and no clear rule cause → non-convergence, for the orchestrator to intervene

## Tracking

This skill writes each unit entry's implementing `rule_id` and the unit's `stages.tests_passing`. `rule_id` is a `<relative-yaml-path>#<id>` locator for either the custom lib rule created for that entry or an existing built-in lib rule proven to cover it. Preserve the source unit's top-level `tag` and every sink `groups[].tag`, those tags are the authoring contract. A blocked unit stays `tests_passing: pending`.

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

`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from. `groups` partitions the package's dangerous operations by reusable sink tag; each group is `{ tag, sinks }`, and each sink is `{ method, signature, note, rule_id }`. The tag belongs to the group, never to an individual method: one rule may cover several methods and several rules may extend the same vulnerability family. `method` and `signature` use the exact language-specific identifiers from the plan. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - <dependency-id>
groups:
  - tag: path-traversal-sink
    sinks:
      - { method: "<qualified-member>", signature: "<language-signature>", note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

## Constraints

- Library rules MUST have `options.lib: true` and `severity: NOTE`
- Created source rules MUST carry the `untrusted-data-source` tag, created sink rules MUST carry their enclosing sink group's registered `*-sink` tag
- The test joins MUST have `metadata.cwe` and `metadata.short-description`
- In test joins, metavariable names must match across `refs` and `on` clauses or the join won't connect. Bind the tainted value to `$UNTRUSTED` in every lib source/sink rule
- Test-join `rule` paths are relative to a ruleset root: marker rules resolve under the test project's rules, lib rules under the built-in or custom scanned rules tree
- Rule IDs must be globally unique
- The custom lib rules go in the scanned rules tree; the test joins go only in the test project's marker rules
- Never scan the main project model
- Never try to edit the test project

## Gotchas

- If you think a test project is wrong — hand it back upstream
- A positive that won't pass because a library method drops taint is not a rule bug — surface it for approximation (per step 5), don't broaden the rule to force it
- Keep produced rule files comment-free
