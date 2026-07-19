# Rule metadata and lifecycle

Metadata controls how a rule is identified, selected, reported, reused, disabled, and presented to users. It does not change AST-pattern matching unless an option explicitly says so.

The top-level format is shared by Java/JVM and Go.

## Complete skeleton

```yaml
rules:
  - id: example-injection
    languages: [java]
    mode: taint
    message: Untrusted input reaches the example interpreter
    severity: ERROR
    tags: [example-injection-sink]
    metadata:
      cwe: CWE-000
      short-description: Example-language injection
      full-description: >-
        Untrusted input is interpreted as example-language code.
      remediation: >-
        Use a structured API or validate input against an allow-list.
      references:
        - https://example.com/security-guidance
      license: MIT
      provenance: https://example.com/rule-source
    options:
      primitive-tracking: false
    pattern-sources:
      - patterns:
          - pattern: $INPUT = source(...)
          - focus-metavariable: $INPUT
    pattern-sinks:
      - patterns:
          - pattern: sink($VALUE)
          - focus-metavariable: $VALUE
```

## `id`

`id` is required and should be stable and descriptive:

```yaml
id: sql-injection
```

A rule is identified by its ruleset-relative path plus its `id`. The separator depends on the context:

```text
java/security/sqli.yaml#sql-injection   # join refs, overrides, and rule-test.yaml entries
java/security/sqli.yaml:sql-injection   # CLI identifiers: --rule-id filters and test rule reachability
```

Changing an ID can break:

- rule filters;
- positive and negative tests;
- suppressions;
- explicit join references;
- dashboards or automation that group findings by ID.

Use a vulnerability and scope name, not an implementation detail that may change during refactoring.

## `languages`

`languages` selects the AST-pattern parser and rule strategy:

```yaml
languages: [java]
```

```yaml
languages: [go]
```

The YAML clauses are shared, but the AST pattern must use the selected language's syntax. Do not put Java and Go-shaped patterns into one rule alternative. Create language-specific rules that share a naming and metadata convention.

A rule with no supported language strategy is not executable.

## `mode`

Supported modes are:

| Value | Meaning |
|---|---|
| omitted or `search` | Run the pattern as a taint automaton: carry cross-event metavariables with rule-private marks, then report acceptance |
| `taint` | Add explicit vulnerability sources, sinks, sanitizers, and propagators |
| `join` | Compose reusable component marks into a taint rule |

Search example:

```yaml
pattern: 'tls.Config{InsecureSkipVerify: true, ...}'
```

Taint example:

```yaml
mode: taint
pattern-sources: [...]
pattern-sinks: [...]
```

Join example:

```yaml
mode: join
join:
  refs: [...]
  on: [...]
```

Other mode names are rejected. A join requires its `join` section and at least one `on` edge.

## `message`

`message` is required and appears at the finding location:

```yaml
message: Untrusted servlet input reaches a SQL query
```

A useful message states:

- what unsafe value is involved;
- what dangerous operation receives it;
- optionally, the security consequence.

Avoid API-only messages:

```yaml
# Weak
message: executeQuery called
```

Avoid claiming evidence the rule does not prove:

```yaml
# Too strong if the rule only detects a risky configuration.
message: Attackers can execute arbitrary code remotely
```

Join findings use the outer join rule's message, not the messages of its library components.

## `severity`

Severity is required. The current mapping is case-insensitive:

| Rule value | Reported severity |
|---|---|
| `HIGH`, `CRITICAL`, `ERROR` | Error |
| `MEDIUM`, `WARNING` | Warning |
| every other value, including `NOTE` | Note |

Use the repository convention:

```yaml
severity: ERROR
```

```yaml
severity: WARNING
```

```yaml
severity: NOTE
```

Recommended use:

- `ERROR`: a strong vulnerability relationship with actionable evidence;
- `WARNING`: a security weakness requiring context or a lower-confidence path;
- `NOTE`: a reusable library component or informational structural concern.

Severity filters are applied after rules are constructed.

## `metadata`

`metadata` is preserved for reports and integrations:

```yaml
metadata:
  cwe:
    - CWE-89
    - CWE-564
  short-description: SQL injection
  full-description: >-
    Untrusted data is incorporated into a SQL statement without
    parameterization.
  remediation: >-
    Use prepared statements and bind untrusted values as parameters.
  references:
    - https://owasp.org/www-community/attacks/SQL_Injection
  license: MIT
  provenance: https://example.com/source-rule
```

### CWE

`cwe` may be a scalar or list. Items beginning with `CWE-<number>` are extracted for reporting:

```yaml
metadata:
  cwe: CWE-89
```

```yaml
metadata:
  cwe: [CWE-89, CWE-564]
```

Choose the CWE that matches the evidence actually reported. A generic taint flow does not justify several speculative CWE values.

### Descriptions and remediation

Keep these consistent:

```text
message            concise finding at the location
short-description  stable finding title
full-description   why this relationship is unsafe
remediation        concrete safer behavior
```

If the rule detects a configuration rather than a confirmed exploit path, say so in all four fields.

### References, license, and provenance

References should explain the API risk or recommended mitigation. Provenance should identify the source of the rule or adaptation. License metadata should remain compatible with the repository and upstream material.

## `tags`

`tags` is a list of exact strings:

```yaml
tags:
  - servlet-untrusted-data-source
```

Tags do not change matching and do not activate a rule. They are indexed for join expansion.

Use a controlled vocabulary based on role:

```text
<framework>-untrusted-data-source
<vulnerability>-sink
```

Example:

```yaml
tags: [servlet-untrusted-data-source]
```

Other family tags follow the same convention: `spring-untrusted-data-source`, `ssrf-sink`, `sqli-sink`, `path-traversal-sink`, `command-injection-sink`, `format-string-sink`.

Adding a rule to a tag intentionally extends every join that consumes that tag. Use an explicit `rule:` reference when that open expansion is undesirable.

## `options`

### `lib`

```yaml
options:
  lib: true
```

The rule is built and registered for reuse but does not emit findings directly. Source and sink components used by joins normally use library mode.

An inline rule under `join.rules` is forced into library mode.

### `disabled`

```yaml
options:
  disabled: true
```

The presence of the `disabled` key disables the rule. Its parsed scalar value is not treated as a normal true/false toggle, so this is also disabled:

```yaml
options:
  disabled: false
```

Remove the key to enable the rule.

Disabled rules are not active tag members.

### `overrides`

```yaml
options:
  overrides: java/lib/example/base.yaml#base-rule
```

The rule replaces the referenced parsed rule. A short local ID may be resolved relative to the containing ruleset path.

Test overrides explicitly. Missing targets, ambiguous overrides, and override cycles are diagnosed. When two rules claim the same override target, the first resolved override wins after a diagnostic; do not depend on file ordering.

### `primitive-tracking`

```yaml
options:
  primitive-tracking: true
```

This generates the primitive-tracking mode variant for cases where primitive values must participate in taint flow. Enable it only with positive and negative samples that require primitive behavior; it expands analysis scope.

## Unknown properties

An unknown YAML property produces a non-blocking diagnostic and is ignored during permissive parsing. A typo may therefore allow the scan to start while silently removing the intended constraint.

```yaml
# Typo: not the supported field.
severty: ERROR
```

Always inspect rule-load diagnostics and execute behavioral tests. Successful YAML loading is not proof that every field affected analysis.

## Accepted but currently inactive or restricted fields

Some Semgrep-compatible fields can be represented in YAML but are not currently active OpenTaint behavior:

| Field | Current status |
|---|---|
| Source `exact` | Parsed, not used by current JVM generation |
| Source `control` | Parsed, not used by current JVM generation |
| Source `by-side-effect` | Parsed, not used by current JVM generation |
| Propagator `by-side-effect` | Parsed, not used by current JVM generation |
| Sanitizer `exact` | Parsed, not used by current JVM generation |
| Sanitizer focus on arbitrary argument | Does not redirect current JVM cleaning |
| `metavariable-comparison` | Not implemented |
| Rule-level `pattern-regex`/`pattern-not-regex` | Not implemented |
| Sink `requires` with metavariable map | Diagnosed and treated as unconditional |

Do not document or ship a semantic dependency on an accepted-but-inactive field.

## Metadata examples by rule role

### User-facing vulnerability rule

```yaml
id: command-injection-in-servlet-app
message: Untrusted servlet input reaches an operating-system command
severity: ERROR
metadata:
  cwe: CWE-78
  short-description: OS command injection
  remediation: Avoid shell interpretation and pass fixed arguments to a structured process API.
```

### Reusable source library

```yaml
id: servlet-untrusted-source
message: Servlet-controlled input source
severity: NOTE
tags: [servlet-untrusted-data-source]
options:
  lib: true
metadata:
  short-description: Servlet trust boundary
```

### Reusable sink library

```yaml
id: command-execution-sink
message: Operating-system command execution sink
severity: NOTE
tags: [command-injection-sink]
options:
  lib: true
metadata:
  short-description: Command execution operation
```

The outer join should own the final vulnerability message, severity, CWE, and remediation.

## Review checklist

- The ID is stable, unique in its path, and used by tests.
- `languages` matches every AST pattern in the rule.
- `mode` matches the evidence: structure, taint flow, or reuse.
- The message states only what the rule proves.
- Severity reflects confidence and impact consistently.
- CWE, descriptions, remediation, and references agree with the finding.
- Tags are intentional open extension points.
- Library components do not report directly.
- Disabled rules remove the key when re-enabled.
- Overrides have a unique, tested target.
- Primitive tracking is justified by samples.
- Rule-load diagnostics contain no ignored typo or unsupported semantic dependency.
