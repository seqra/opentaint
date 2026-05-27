---
name: create-rule
description: Author and verify an OpenTaint detection rule for a vulnerability class on JVM code. Use whenever a rule needs to be created for an uncovered vulnerability, or an existing rule needs a false-positive or false-negative fix
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Rule

Create a pattern rule for a vulnerability class, then test it against the prepared test project and fix it until every sample passes

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Requirements `<requirements>` — what to detect (source, sink, vuln class); either a rule tracking file or an overall description
- Compiled test project `<test-compiled>` — the compiled model to verify against. Default: `.opentaint/test-compiled/<name>` (per rule/approximation `<name>`)
- Rules directory `<rules-dir>` — where rules are written. Default: `.opentaint/rules`
- Tracking file `<tracking-file>` — the rule file. Default: `.opentaint/tracking/rules/<name>.yaml`

Built-in rules are available at `opentaint dev rules-path`

## Workflow

### 1. Check existing coverage

Browse builtin rules at `opentaint dev rules-path` for source/sink library rules to reference. A `refs` to a built-in source/sink is cheaper and more accurate than a new one

### 2. Wire sources and sinks

Prefer referencing built-in source/sink library rules; write a custom one only when no built-in fits. Derive each pattern from the requirements' fully-qualified names and annotations

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

### 3. Create the security rule (join mode)

Write it at `<rules-dir>/java/security/<name>.yaml` — name the file and `id` after the rule name from the tracking file. Wire the sources and sinks (built-in or custom) via `refs`:

```yaml
rules:
  - id: my-vulnerability
    severity: ERROR
    message: >-
      Untrusted data flows to dangerous operation
    metadata:
      cwe: CWE-89
      short-description: SQL Injection via untrusted input
    languages: [java]
    mode: join
    join:
      refs:
        - rule: java/lib/generic/my-source.yaml#my-custom-source
          as: source
        - rule: java/lib/generic/my-sink.yaml#my-custom-sink
          as: sink
      on:
        - 'source.$UNTRUSTED -> sink.$UNTRUSTED'
```

### 4. Test until success

Run the rule tests against the compiled test project; iterate the rule and re-run `test-rules` until every sample passes:

```bash
opentaint dev test-rules <test-compiled> \
  -o .opentaint/test-results/<name> \
  --ruleset <rules-dir>
```

`test-rules` auto-loads the built-in rules, so pass only your custom `<rules-dir>` — a literal `builtin` here would be treated as a path. Read `.opentaint/test-results/<name>/test-result.json`:

- `falseNegative` (positive didn't trigger) → patterns too narrow; broaden `pattern-either`, check metavariable names match across branches and between `refs` and `on`
- `falsePositive` (negative triggered) → patterns too broad; add `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`
- `skipped` / `disabled` → the rule wasn't exercised; fix the annotation `value`/`id`, or enable the rule

### 5. Refining for a false positive (suppress-FP)

The test project already pins the confirmed TPs as `@PositiveRuleSample` and reproduces the FP as a `@NegativeRuleSample` — refine only the rule. Narrow it (step 4's `falsePositive` handling) until the negative stops triggering while every positive still passes. Do not touch the samples; if one looks wrong, hand it back upstream

## Output

- The rule file(s) under `<rules-dir>`
- Tracking updated: `rule_id`, `artifact`, `stages.tests_passing` (per Tracking)
- Report the full rule id, a one-line test summary, and the exact `test-rules` command used

## Tracking

In `<tracking-file>`, once the rule exists and its samples pass:

```yaml
rule_id: java/security/my-vuln.yaml:my-vulnerability
artifact: .opentaint/rules/java/security/my-vuln.yaml
stages:
  tests_passing: done
```

## Constraints

- Library rules MUST have `options.lib: true` and `severity: NOTE`
- Security rules MUST have `metadata.cwe` and `metadata.short-description`
- Source/sink metavariable names must match across `refs` and `on` clauses, or the join won't connect
- The `rule:` path in `refs` is relative to the ruleset root
- Rule IDs must be globally unique
- For simple structural patterns (no dataflow), omit `mode:` (uses default mode)
- Custom library rules go under `<rules-dir>/java/lib/generic/` or `<rules-dir>/java/lib/spring/` (for Spring-specific), mirroring the built-in layout — never directly under `java/lib/`


## Gotchas

- A wrong argument position in `(..., $UNTRUSTED, ...)` focuses the wrong parameter — point `focus-metavariable` at the tainted one
- Refine the rule, never the test project — don't edit or weaken samples here; if one is wrong, hand it back upstream
