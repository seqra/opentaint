# create-rule — Java / JVM

Language reference for authoring Java source/sink library rules, keyed to the body's steps. Bind every tainted value to `$UNTRUSTED` so the joins connect on one name; star only the pattern occurrences that need whole-object scope.

## Workflow

### 1. Check existing coverage

Built-in source/sink lib rules live under `java/lib/generic/` (framework-neutral) and `java/lib/spring/` (Spring-specific); project rules use the same layout under `.opentaint/rules/java/`. For a member unit, search by the exact class and method and confirm the matching signature and focused value. Mirror the matching generic or framework-specific layout for any custom rule you add.

### 2. Author the library rules

OpenTaint is field-sensitive. A plain `$UNTRUSTED` occurrence marks or checks only the base value. Prefix-star `$*UNTRUSTED` denotes that value plus its nested fields at any depth:

- source/producer occurrence — `$*UNTRUSTED` marks the base and any-field scope; use it for a request body, deserialized object, container, array, or other value whose complete contents enter untrusted
- sink/consumer occurrence — `$*UNTRUSTED` accepts a mark on the base or any nested field/element; use it when one tainted property or element makes passing the whole object dangerous
- sanitizer occurrence — `$*UNTRUSTED` cleans the base and its nested fields; use it only when the sanitizer makes the complete object safe, while a base-only sanitizer stays plain

The star belongs to an occurrence, not the metavariable identity, so `$UNTRUSTED` and `$*UNTRUSTED` still join under the plain name `$UNTRUSTED`. The supported spelling is the prefix form `$*VAR`; don't write the retired suffix form `$VAR*`. Put stars only in pattern text. Keep `focus-metavariable`, `metavariable-pattern`, `metavariable-regex`, and join `on` names plain. A starred sink must be paired with `focus-metavariable` or its widened field check is not represented. If a `pattern-not` excludes the same position as a starred positive pattern, star that occurrence there too.

Custom source library rule (`.opentaint/rules/java/lib/generic/my-source.yaml`):

```yaml
rules:
  - id: my-custom-source
    options:
      lib: true
    tags:
      - untrusted-data-source
    severity: NOTE
    message: Custom untrusted data source
    languages:
      - java
    patterns:
      - pattern-either:
          - patterns:
              - pattern: |
                  $RETURNTYPE $METHOD(HttpServletRequest $*UNTRUSTED, ...) { ... }
              - metavariable-pattern:
                  metavariable: $METHOD
                  pattern-either:
                    - pattern: doGet
                    - pattern: doPost
```

The parameter occurrence is starred because the request object and its fields are attacker-controlled. A scalar-return source, or a source that promises only a base mark, stays plain.

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
    languages:
      - java
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-either:
              - pattern: (java.sql.Statement $S).executeQuery($UNTRUSTED)
              - pattern: (java.sql.Statement $S).execute($UNTRUSTED)
          - focus-metavariable: $UNTRUSTED
```

This SQL sink is deliberately base-only because the dangerous value is the query string itself. For a whole-object/container sink, star the focused occurrence. For example, a process argument list is dangerous when one list element is tainted:

```yaml
pattern-sinks:
  - patterns:
      - pattern: new ProcessBuilder($*UNTRUSTED)
      - focus-metavariable: $UNTRUSTED
```

A tainted argument bound as a query parameter is already sanitized — the placeholder (`#{}`, a `PreparedStatement` `?`) stops it breaking out — so a method that merely runs parameterized SQL is not a SQLi sink; marking one fires on every call carrying a tainted field, a flood of false positives. The sink is only where a value is spliced into the query as raw text, never where it's bound as a parameter.

### 3. Write the test joins

The join goes in the test project's `test-rules/java/security/`, named `<unit>-sinks` / `<unit>-sources` so the samples' `rule-test.yaml` `rule-id` resolves (`<unit>` = the package-kebab). The scaffold provides independently referenceable plain and whole-object counterparts:

- plain source: `java/lib/test/generic-source.yaml#generic-taint-source`
- starred source: `java/lib/test/generic-source-starred.yaml#generic-taint-source-starred`
- plain sink: `java/lib/test/generic-sink.yaml#generic-taint-sink`
- starred sink: `java/lib/test/generic-sink-starred.yaml#generic-taint-sink-starred`

- `sinks` side → `<unit>-sinks`: ref the plain or starred generic source + every sink `rule_id` selected for the unit, wiring `src.$UNTRUSTED -> <sink>.$UNTRUSTED` for each
- `sources` side → `<unit>-sources`: ref every source `rule_id` selected for the unit + the plain or starred generic sink, wiring `<source>.$UNTRUSTED -> sink.$VALUE` for each

Select starred only when the counterpart itself must mark or accept nested-field taint; don't load both variants into the same isolation join.

```yaml
rules:
  - id: <unit>-sinks
    severity: ERROR
    message: Tainted value reaches a sink under test
    metadata:
      cwe:
        - CWE-000
      short-description: test join for the package's sinks
    languages:
      - java
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

The marker rules resolve from the sub-project's `test-rules` root, a selected lib ref resolves from either the built-in ruleset or `.opentaint/rules`, both loaded by `test rule run`. Metavariable names must match across `refs` and `on`.

### 4. Test until success

The concrete operators per verdict:

- `falseNegative` → broaden `pattern-either`, check metavariable names match across branches and between `refs` and `on`, and add a star when a nested-field/element fact must count
- `falsePositive` → add `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`; star a sanitizer that cleans the complete object, or remove a sink star if the API consumes only base taint
- `skipped` / `disabled` → fix the sample's `rule-test.yaml` `rule-id`/entrypoint, or enable the rule

## Constraints

- Custom library rules go under `java/lib/generic/` or `java/lib/spring/`, mirroring the built-in layout — never directly under `java/lib/`
- For a simple structural pattern (no dataflow), omit `mode` — it uses the default mode
- Don't unpack or grep the analyzer JAR

## Gotchas

- A wrong argument position in `(..., $UNTRUSTED, ...)` focuses the wrong parameter — point `focus-metavariable` at the tainted one
- Writing `$*UNTRUSTED` in `focus-metavariable`, a metavariable constraint, or join `on` is invalid — those fields always use `$UNTRUSTED`
- An implicit-receiver pattern `this.method(...)` is unsupported — match the unqualified call as a bare `method($X)` pattern instead
- A structural (no-source) sink and a taint-flow sink can't share one join id; if a class needs both, split them into separate rules/joins
