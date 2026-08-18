# create-rule — Java / JVM

Language reference for authoring Java source/sink library rules, keyed to the body's steps. Bind every tainted value to `$UNTRUSTED` so the joins connect on one name.

## Workflow

### 1. Check existing coverage

Built-in source/sink lib rules live under `java/lib/generic/` (framework-neutral) and `java/lib/spring/` (Spring-specific); mirror that layout for any custom rule you add.

### 2. Author the library rules

Every custom library source or sink declares its role family under top-level `tags`. Tags are exact, language-scoped strings used only to expand `join.refs`; they don't change matching or activate a library rule. Follow the built-in vocabulary: source families use `<framework>-untrusted-data-source`, and sink families use the security rule's exact `<vulnerability>-sink` tag (for example `servlet-untrusted-data-source`, `spring-untrusted-data-source`, `sqli-sink`, `ssrf-sink`, or `path-traversal-sink`). Read the built-in library and security rules before choosing.

A tag is an open extension point: adding `sqli-sink` opts the rule into every Java join that references that tag. Reuse it only when that fan-out is correct. Otherwise use a stable project-specific family such as `<unit>-untrusted-data-source` or `<unit>-<vulnerability>-sink`; the assembly stage will add the required join. Multiple custom sources can declare the same project-specific source tag, and a custom join can select the whole family with one `tag:` ref. Use an explicit `rule:` ref when only one component should be selected.

Reference a built-in:

```yaml
refs:
  - rule: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
    as: servlet-source
  - rule: java/lib/spring/untrusted-data-source.yaml#spring-untrusted-data-source
    as: spring-source
```

Custom source library rule (`.opentaint/rules/java/lib/generic/my-source.yaml`):

```yaml
rules:
  - id: my-custom-source
    options:
      lib: true
    tags:
      - servlet-untrusted-data-source
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

To make several custom sources a reusable family, repeat the same exact list-form tag on every source rule:

```yaml
tags:
  - orders-untrusted-data-source
```

A custom security join can then consume all active Java source rules in that family:

```yaml
join:
  refs:
    - tag: orders-untrusted-data-source
      as: orders-source
    - tag: sqli-sink
      as: sink
  on:
    - 'orders-source.$UNTRUSTED -> sink.$UNTRUSTED'
```

Keep the shared tag project-specific unless these sources are intentionally members of a built-in family. Tag expansion is language-scoped and includes every active matching rule, including other custom rules.

Custom sink library rule (`.opentaint/rules/java/lib/generic/my-sink.yaml`):

```yaml
rules:
  - id: my-custom-sink
    options:
      lib: true
    tags:
      - sqli-sink
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

A tainted argument bound as a query parameter is already sanitized — the placeholder (`#{}`, a `PreparedStatement` `?`) stops it breaking out — so a method that merely runs parameterized SQL is not a SQLi sink; marking one fires on every call carrying a tainted field, a flood of false positives. The sink is only where a value is spliced into the query as raw text, never where it's bound as a parameter.

### 3. Write the test joins

The join goes in the test project's `test-rules/java/security/`, named `<unit>-sinks` / `<unit>-sources` so the samples' `rule-test.yaml` `rule-id` resolves (`<unit>` = the package-kebab):

- `sinks` side → `<unit>-sinks`: ref the generic source + every new sink lib rule, wiring `src.$UNTRUSTED -> <sink>.$UNTRUSTED` for each
- `sources` side → `<unit>-sources`: ref every new source lib rule + the generic sink, wiring `<source>.$UNTRUSTED -> sink.$VALUE` for each

```yaml
rules:
  - id: <unit>-sinks
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

The marker rules resolve from the sub-project's `test-rules` root, your lib rules from `.opentaint/rules` — `test rule run` is passed both. Metavariable names must match across `refs` and `on`. Keep these test refs explicit: replacing `rule:` with `tag:` would pull every active family member into the test and stop it isolating the new component.

### 4. Test until success

The concrete operators per verdict:

- `falseNegative` → broaden `pattern-either`, and check metavariable names match across branches and between `refs` and `on`
- `falsePositive` → add `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`
- `skipped` / `disabled` → fix the sample's `rule-test.yaml` `rule-id`/entrypoint, or enable the rule

## Constraints

- Custom library rules go under `java/lib/generic/` or `java/lib/spring/`, mirroring the built-in layout — never directly under `java/lib/`
- Tags are exact strings, not display labels. Match the built-in security join's spelling, including distinctions such as `sqli-sink` versus the vulnerability class `sql-injection`
- For a simple structural pattern (no dataflow), omit `mode` — it uses the default mode
- Don't unpack or grep the analyzer JAR

## Gotchas

- A wrong argument position in `(..., $UNTRUSTED, ...)` focuses the wrong parameter — point `focus-metavariable` at the tainted one
- An implicit-receiver pattern `this.method(...)` is unsupported — match the unqualified call as a bare `method($X)` pattern instead
- A structural (no-source) sink and a taint-flow sink can't share one join id; if a class needs both, split them into separate rules/joins
