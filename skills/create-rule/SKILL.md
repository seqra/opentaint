---
name: create-rule
description: Author and verify an OpenTaint detection rule for a vulnerability class on JVM code. Use whenever a rule needs to be created for an uncovered vulnerability, or an existing rule needs a false-positive or false-negative fix
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Rule

Per package, author the new source and/or sink lib rules the unit names, wire each to the generic `Taint` marker in a test join, and verify against the package's marker test projects until every sample passes. Author only the side the unit has — a sources-only or sinks-only unit yields just that side's rules, joins, and test sub-project (the deep workflow authors sources first, then sinks once the taint frontier has named them)

Two roles: the **main** one authors a package's lib rules from `<tracking-file>` (above); a **fix** (`<fix-target>` set) narrows or broadens one created rule the main scan later flagged. The cross-package security joins are written by assemble-lib-rules, not here

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Tracking file `<tracking-file>` — the source unit `.opentaint/tracking/rules/sources/<name>.yaml` or the sink unit `.opentaint/tracking/rules/sinks/<name>.yaml` (`<name>` = the package-kebab). In the main role this is both the spec (the sources/sinks to author) and where each rule's `rule_id` + `stages` are recorded
- Compiled test projects `<test-compiled>` — the marker models to verify against. Default: `.opentaint/test-compiled/<name>/sinks` and `.opentaint/test-compiled/<name>/sources` (`<name>` = the package-kebab)
- Test project `<test-project>` — the sources tree; the test joins go in each side's `<test-project>/<side>/test-rules` (only `test rule run` loads them, never the main scan). Default: `.opentaint/test-projects/<name>`
- Rules directory `<rules-dir>` — where the lib rules are written. Default: `.opentaint/rules`
- Fix target `<fix-target>` (optional, fix role) — a created rule (`<path>#<id>`) the main scan flagged, plus the false positive/negative to correct; when set, narrow or broaden that one rule instead of authoring from the unit
- Approximation directories `<config-dir>` / `<approx-dir>` (optional) — apply on a re-dispatch when the test project needs a library model that's now built. Default: none

Built-in rules are available at `opentaint health --rules`

## Workflow

In the fix role (`<fix-target>` set), don't author from the unit — edit only that one flagged rule per step 4's false-positive/negative guidance, re-run its tests, and stop; leave the unit's other entries untouched.

When this package's lib rules already exist (the unit's entries carry `rule_id` and `tests_passing: done`), reuse them as the baseline — expand or refine for what the unit newly names (a new sink, a widened source), never re-author rules that already pass. When the unit is partway (some stages `done`, some not), continue from the first unfinished stage on the artifacts already on disk rather than restarting. Author from scratch only the genuinely new sources/sinks.

### 1. Check existing coverage

Browse builtin rules at `opentaint health --rules` for source/sink library rules to reference. A `refs` to a built-in source/sink is cheaper and more accurate than a new one

### 2. Wire sources and sinks

Prefer referencing built-in source/sink library rules; write a custom one only when no built-in fits. Derive each pattern from the unit's fully-qualified names and annotations

Reference built-ins:

```yaml
refs:
  - rule: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
    as: servlet-source
  - rule: java/lib/spring/untrusted-data-source.yaml#spring-untrusted-data-source
    as: spring-source
```

Custom source library rule (`<rules-dir>/java/lib/generic/my-source.yaml`), if no built-in fits:

```yaml
rules:
  - id: my-custom-source
    options:
      lib: true
    severity: NOTE
    message: Custom untrusted data source
    languages: [java]
    patterns:
      - pattern-either:
          - patterns:
              - pattern: |
                  $RETURNTYPE $METHOD(HttpServletRequest $UNTRUSTED, ...) { ... }
              - metavariable-pattern:
                  metavariable: $METHOD
                  pattern-either:
                    - pattern: doGet
                    - pattern: doPost
```

Custom sink library rule (`<rules-dir>/java/lib/generic/my-sink.yaml`):

```yaml
rules:
  - id: my-custom-sink
    options:
      lib: true
    severity: NOTE
    message: Custom dangerous operation
    languages: [java]
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-either:
              - pattern: (java.sql.Statement $S).executeQuery($UNTRUSTED)
              - pattern: (java.sql.Statement $S).execute($UNTRUSTED)
          - focus-metavariable: $UNTRUSTED
```

### 3. Write the test joins (against the generic marker)

A lib rule emits nothing alone — to exercise it you need a join. Write one test join per sub-project into its `test-rules/java/security/`, wiring your new lib rules to the generic `Taint` marker. These live only in the test project (never `<rules-dir>`), so the main scan never loads them. Name each `<name>-sinks` / `<name>-sources` so the samples' `value`/`id` resolve:

- `sinks/` → `<name>-sinks`: ref the generic source + every new sink lib rule, wiring `src.$UNTRUSTED -> <sink>.$UNTRUSTED` for each
- `sources/` → `<name>-sources`: ref every new source lib rule + the generic sink, wiring `<source>.$UNTRUSTED -> sink.$VALUE` for each

```yaml
rules:
  - id: <name>-sinks
    severity: ERROR
    message: Tainted value reaches a sink under test
    metadata:
      cwe: CWE-000
      short-description: test join for the package's sinks
    languages: [java]
    mode: join
    join:
      refs:
        - rule: java/lib/test/generic-source.yaml#generic-taint-source
          as: src
        - rule: java/lib/<area>/my-new-sink.yaml#my-new-sink
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
```

The marker rules resolve from the sub-project's `test-rules` root, your lib rules from `<rules-dir>` — pass both to `test rule run`. Metavariable names must match across `refs` and `on`

### 4. Test until success

Run the tests against each compiled sub-project, loading your lib rules (`<rules-dir>`) and the test joins + markers (`<test-project>/<side>/test-rules`); iterate until every sample passes:

```bash
opentaint test rule run <test-compiled>/sinks \
  -o .opentaint/test-results/<name>/sinks \
  --ruleset <rules-dir> --ruleset <test-project>/sinks/test-rules
```

`test rule run` auto-loads the built-in rules, so pass only your custom rulesets — a literal `builtin` here would be treated as a path. When the caller passed `<config-dir>` / `<approx-dir>`, append `--passthrough-approximations <config-dir>` / `--dataflow-approximations <approx-dir>` — without them a library method the test flow relies on drops taint and the positive can't pass. Read `.opentaint/test-results/<name>/sinks/test-result.json`:

- `falseNegative` (positive didn't trigger) → patterns too narrow; broaden `pattern-either`, check metavariable names match across branches and between `refs` and `on`
- `falsePositive` (negative triggered) → patterns too broad; add `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`
- `skipped` / `disabled` → the rule wasn't exercised; fix the annotation `value`/`id`, or enable the rule

### 5. When a positive won't pass after a couple of fixes

A `@PositiveRuleSample` that won't trigger after ~2 fix attempts may have a cause no rule edit can fix — a library method on its flow killing taint. Before escalating, scan that sub-project's model with `--track-external-methods` (add the marker `test-rules` so the join resolves):

```bash
opentaint scan --project-model <test-compiled>/sinks \
  -o .opentaint/test-results/<name>/sinks/diag.sarif \
  --ruleset builtin --ruleset <rules-dir> --ruleset <test-project>/sinks/test-rules \
  --track-external-methods
```

Read `dropped-external-methods.yaml` next to it; either way leave `tests_passing: pending`:

- a dropped method on the failing sample's source→sink path → that's the cause, not the rule: report which methods need a model, to be approximated before you're re-dispatched
- nothing dropped and no clear rule cause → report non-convergence for escalation, rather than editing blindly

## Output

- The new lib rule file(s) under `<rules-dir>`, and the test join(s) under each test project's `test-rules/`
- Tracking updated: each entry's `rule_id`, `stages.tests_passing` (per Tracking)
- Report the lib rule ids, a one-line test summary per sub-project, and the exact `test rule run` command used
- If blocked (step 5): leave `tests_passing: pending` and report the cause instead

## Tracking

In `<tracking-file>` (the source or sink unit), once the lib rules exist and every sub-project's samples pass, set each entry's `rule_id` and the stage. No top-level `artifact` — its path is derivable from `rule_id`. `rule_id` is the created lib rule's ref, or a built-in ref when you referenced a built-in instead of authoring:

```yaml
sinks:
  - { method: "cn.hutool.core.io.FileUtil#writeBytes", vuln_class: path-traversal, note: "writes to an untrusted path", rule_id: "java/lib/generic/cn-hutool-core-io-path-traversal-sink.yaml#cn-hutool-core-io-file-write-path-traversal-sink" }
stages:
  tests_passing: done
```

## Constraints

- Library rules MUST have `options.lib: true` and `severity: NOTE`
- Security rules (the joins) MUST have `metadata.cwe` and `metadata.short-description`
- Source/sink metavariable names must match across `refs` and `on` clauses, or the join won't connect; bind the tainted value as `$UNTRUSTED` in every lib source/sink rule, so the security joins assemble-lib-rules writes later reference one consistent name
- The `rule` path in `refs` is relative to the ruleset root — a marker ref resolves under the test project's `test-rules`, a lib ref under `<rules-dir>`
- Rule IDs must be globally unique
- The only `opentaint scan` you run is the step-5 diagnostic over your own `<test-compiled>` model — never scan the main project model
- For simple structural patterns (no dataflow), omit `mode` (uses default mode)
- Custom library rules go under `<rules-dir>/java/lib/generic/` or `<rules-dir>/java/lib/spring/` (for Spring-specific), mirroring the built-in layout — never directly under `java/lib/`; the test joins go in the test project's `test-rules/java/security/`, never `<rules-dir>`


## Gotchas

- A wrong argument position in `(..., $UNTRUSTED, ...)` focuses the wrong parameter — point `focus-metavariable` at the tainted one
- Refine the rule, never the test project — don't edit or weaken samples here; if one is wrong, hand it back upstream
- A positive that won't pass because a library method drops taint is not a rule bug — don't broaden the rule to force it; surface it for approximation (step 5)
- Keep produced rule files comment-free
- An implicit-receiver pattern `this.method(...)` is unsupported ("Failed to transform pattern: ThisExpr") — match the unqualified call as a bare `method($X)` pattern instead
- A structural (no-source) sink and a taint-flow sink can't share one join id — the engine forbids one id being both; if a class needs both, split them into separate rules/joins
- Don't unpack or grep the analyzer JAR for built-in rules — its internals aren't a stable API; read the YAMLs from `opentaint health --rules`
