---
name: create-rule
description: Author and verify an OpenTaint rule. Use whenever a rule creation is needed
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Create Rule

A unit names the source or sink methods of one side to detect. Write a library rule for each — reusing a built-in wherever one fits, authoring a custom one only for what none covers — and verify them against the unit's test project until every sample passes. Each rule exposes its tainted value under a consistent marker so a later stage can wire the real cross-package security joins. During this phase you write only the library rules and the throwaway joins to test them.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `side` (required) — `sources` or `sinks`; the unit's side. It selects the unit file, the sample style, and the test sub-project
- `unit` (required) — the `<package-kebab>` identifying the unit. Its spec and tracking are in `.opentaint/tracking/rules/<side>/<unit>.yaml`; its test project is `.opentaint/test-projects/<unit>/<side>` and its compiled model `.opentaint/test-compiled/<unit>/<side>`
- `fix-target` (optional) — a created rule `<path>#<id>` the main scan flagged, plus the false positive or false negative to correct. When set, narrow or broaden that one rule instead of authoring from the unit

## Workflow

### 1. Check existing coverage

Browse the built-in library rules for a source or sink you can reference — a `refs` to a built-in is cheaper and more accurate than authoring a completely new rule. The following command prints the built-in rules root path; browse it (layout per the language reference) and grep by your package's FQN:

```bash
opentaint health --rules
```

In fix mode, don't author from the unit: go straight to that one flagged rule, adjust it by the false-positive/negative guidance per step 4, re-run this side's tests, and stop — leave the unit's other entries untouched. Otherwise, when the unit's rules already exist and pass (entries carry `rule_id` and `stages.tests_passing: done`), reuse them as the baseline and extend only for what the unit newly names. When the unit is partway (some stages `done`, some not), continue from the first unfinished stage on the artifacts already on disk rather than restarting, authoring from scratch only the genuinely new sources or sinks.

### 2. Author the library rules

Derive each rule's pattern from the unit's fully-qualified names, recorded signatures, and annotations. Bind the tainted value to one consistent metavariable in every rule so the security joins assembled later reference one name. The rule forms — a built-in `refs`, a custom source rule, a custom sink rule, and where custom rules go — are in the language reference.

### 3. Write the test joins

A library rule emits nothing on its own — to exercise it, wire it to the generic taint marker in a throwaway test join. Write one join for the side into the test project's marker rules, referencing the generic marker on one end and each new lib rule on the other, so a positive sample's tainted value flows marker-to-rule (a sink side) or rule-to-marker (a source side). These joins live only in the test project, never in the scanned rules tree, so the main scan never loads them. The join form, its naming, and where it goes are in the language reference.

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

- the lib rule ids (created or referenced), a one-line test summary for the side, and the exact `test rule run` command used
- if blocked at step 5: `stages.tests_passing` left pending, and the cause —
  - a dropped library method on the failing sample's flow → the methods that need a model, to be approximated before a re-dispatch
  - nothing dropped and no clear rule cause → non-convergence, for the orchestrator to intervene

## Tracking

This skill writes only each unit entry's `rule_id` and its `stages.tests_passing`, once the lib rules exist and every sample on the side passes. `rule_id` is the created lib rule's ref, or a built-in ref when you referenced a built-in instead of authoring one. Don't add a top-level `artifact` — the path is derivable from `rule_id`. A blocked unit stays `tests_passing: pending`.

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

`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sinks` each a dangerous operation reached by the taint frontier `{ method, signature, vuln_class, note, rule_id }` — `signature` the member's JVM descriptor so overloads stay distinct, always quoted (array types contain `[`, which is invalid unquoted in a flow mapping), `vuln_class` per entry since one package can host several, `note` a few words on the danger, the tainted argument left unpinned. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - cn.hutool:hutool-core:5.8.20
sinks:
  - { method: cn.hutool.core.io.FileUtil#writeBytes, signature: "([BLjava/lang/String;)Ljava/io/File;", vuln_class: path-traversal, note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

## Constraints

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis engine. It already propagates through visible application code, calls, aliases, and individual fields; custom rules and approximations model only the assigned source, sink, or opaque-method boundary. Compile-time constants and literals carry no taint, so a source or carrier whose output is only a constant introduces nothing.

- Library rules MUST have `options.lib: true` and `severity: NOTE`
- The test joins (`mode: join`) MUST have `metadata.cwe` and `metadata.short-description`
- Metavariable names must match across `refs` and `on` clauses, or the join won't connect. Bind the tainted value to one consistent metavariable in every lib source/sink rule
- The `rule` path in `refs` is relative to its ruleset root — a marker ref resolves under the test project's marker rules, a lib ref under the scanned rules tree
- Rule IDs must be globally unique
- The custom lib rules go in the scanned rules tree; the test joins go only in the test project's marker rules
- Never scan the main project model
- Never try to edit the test project

## Gotchas

- If you think a test project is wrong — hand it back upstream
- A positive that won't pass because a library method drops taint is not a rule bug — surface it for approximation (per step 5), don't broaden the rule to force it
- Keep produced rule files comment-free
