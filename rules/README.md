# OpenTaint Security Rules

[![GitHub release](https://img.shields.io/github/v/tag/seqra/opentaint?filter=rules/v*&label=rules)](https://github.com/seqra/opentaint/releases)

A curated collection of security rules for [OpenTaint](https://github.com/seqra/opentaint), a static analysis engine for Java and Kotlin that combines Semgrep-style pattern matching with dataflow/taint analysis.

For practical authoring guidance, start with [Writing high-quality rules](../docs/writing-rules.md), then use the focused references for [AST patterns](../docs/ast-patterns.md), [pattern clauses, taint rules, and joins](../docs/rule-pattern-clauses.md), [the whole-object star operator](../docs/star-operator.md), and [rule metadata](../docs/rule-metadata.md). Flows through external libraries may also need [pass-through models](../docs/passthrough-models.md) or [dataflow approximations](../docs/dataflow-models.md).

The repository provides:

- A logically structured set of executable security rules for real-world Java/Kotlin applications
- A shared library of reusable rule components (sources, sinks, propagators, etc.)
- A test suite that validates rule behavior and enforces coverage for all enabled rules

---

## Repository Structure

```text
.
├─ ruleset/java/
│  ├─ security/       # Executable rules run against user code (one file per vulnerability class)
│  └─ lib/            # Reusable rule fragments, not executed directly (marked as lib: true)
└─ test/
   ├─ rule-test.yaml  # Maps each rule id to positive/negative sample methods
   └─ src/main/java/
      └─ security/    # Sample code referenced by rule-test.yaml entries
```

### `ruleset/`: Executable Security Rules

All rules that are intended to run on user code live under `ruleset/`. Each file groups a *class of vulnerability*.

Example:

```text
ruleset/java/security/
  command-injection.yaml
  sqli.yaml
  xss.yaml
  xxe.yaml
```

Characteristics:

- Rules are written in **Semgrep-compatible YAML**.
- Each rule entry has an `id`, `severity`, `message`, `metadata`, `languages`, and pattern/mode fields (`mode: taint`, `pattern`, `patterns`, `pattern-either`, `pattern-sources`, `pattern-sinks`, etc.).
- Rules in `ruleset/` are considered **executable** unless:
  - `options.disabled: <reason>` — the rule is disabled
  - `options.lib: true` — the rule is a library component (should normally reside in `lib/`)

### `lib/`: Reusable Rule Components

The `lib/` directory contains rule fragments that are **not executed standalone**. They are building blocks (sources, sinks, propagators, etc.) that other rules compose via `mode: join` or standard taint rules.

Structure is by technology, example:

```text
lib/
  java/
    generic/
      command-injection-sinks.yaml
      servlet-sqli-sinks.yaml
      servlet-untrusted-data-source.yaml
      servlet-response-injection-sinks.yaml
      xxe-sinks.yaml
    spring/
      jdbc-sqli-sinks.yaml
      spring-response-injection-sinks.yaml
      untrusted-data-source.yaml
```

All library rules are marked:

```yaml
rules:
  - id: java-servlet-untrusted-data-source
    options:
      lib: true
    ...
```

Key points:

- **`lib: true`** explicitly marks a rule as non-executable; it will not be run by OpenTaint as a top-level rule.
- Library rules are typically:
  - Source definitions (`*untrusted-data-source*`)
  - Sink definitions (`*sinks*`)
  - Propagation or helper patterns shared across multiple vulnerabilities

---

## Join Mode

Many rules under `ruleset/` combine multiple library rules using **`mode: join`**.

Library rules expose their roles through tags:

```yaml
- id: java-ssrf-sink
  options:
    lib: true
  tags:
    - ssrf-sink
```

Example (from `ruleset/java/security/ssrf.yaml`):

```yaml
- id: ssrf
  languages:
    - java
  mode: join
  join:
    refs:
      - tag: servlet-untrusted-data-source
        as: servlet-untrusted-data
      - tag: spring-untrusted-data-source
        as: spring-untrusted-data
      - tag: ssrf-sink
        as: sink
    on:
      - 'servlet-untrusted-data.$UNTRUSTED -> sink.$UNTRUSTED'
      - 'spring-untrusted-data.$UNTRUSTED -> sink.$UNTRUSTED'
```

Semantics:

- `mode: join` derives a composite rule from other rules referenced in `join.refs`.
- Each `ref` selects a library rule and assigns a local alias:
  - `tag` selects every enabled rule with that tag in the join's language. Adding the same tag to a
    custom rule extends the join.
  - `rule` selects one rule by `<path>#<rule-id>`.
  - `as` defines the alias used in `on`.
- `on` correlates captures from the referenced rules. For example,
  `servlet-untrusted-data.$UNTRUSTED -> sink.$UNTRUSTED` requires dataflow from the source capture
  to the sink capture.

Built-in joins use language-scoped, per-source and per-sink tags. Use `rule` when a join must
reference one specific rule.

This join mode is **based on Semgrep's join mode**, but OpenTaint extends it with custom features (such as the `->` notation in the `on` section) to express taint-style flows across multiple rule components.

---

## Rule Semantics

Rules follow Semgrep syntax and concepts:

- **Pattern-based** rules:
  - `pattern`, `patterns`, `pattern-either`, `pattern-inside`, `pattern-not-inside`, `metavariable-regex`, etc.
- **Taint-style rules**:
  - `mode: taint`
  - `pattern-sources`, `pattern-propagators`, `pattern-sanitizers`, `pattern-sinks`
  - Dataflow through methods, fields, and variables
- **Metadata**:
  - `cwe`, `short-description`, `full-description` (where provided)
  - External references (OWASP, CWE, upstream rule sources)
  - Optional `license` and `provenance`

---

## Testing and Rule Coverage

Rule behavior is validated via Java sample code under `test/src/main/java/security/`, wired to rules by entries in `test/rule-test.yaml`:

```yaml
tests:
  - rule-id: java/security/code-injection.yaml#el-injection-in-servlet-app
    positive:
      - security.codeinjection.ElInjectionSamples$UnsafeElServlet#doGet
    negative:
      - security.codeinjection.ElInjectionSamples$SafeElServlet#doGet
```

- `rule-id` is `<ruleset-relative-path>#<rule-id>`.
- `positive` lists sample methods that **must** trigger the rule.
- `negative` lists sample methods that **must not** trigger it (typically paired with positives).

### Rule Coverage Enforcement

The CI helper `RuleCoverageCheck` (in `test/src/main/java/rules/RuleCoverageCheck.java`) enforces:

1. **YAML validity** for every file in `ruleset/`:
   - Root is a map and contains a `rules` list.
   - Each rule has a non-blank `id`.
2. **Test coverage for all active rules**:
   - Active rules are those in `ruleset/` where:
     - `options.disabled` is not `true`, and
     - `options.lib` is not `true`
   - Each such rule must have at least one `rule-test.yaml` entry whose `rule-id` is
     `<relative-path-to-rule-yaml>#<rule-id>` (e.g. `java/security/xss.yaml#xss-in-servlet-app`)
     with at least one `positive` sample.

If any active rule is not covered by a positive sample, or if any YAML is invalid, the checker:

- Prints detailed errors (uncounted rules, invalid YAML, etc.)
- Exits with a non-zero status (breaking the build/CI)

---

## Gradle Integration

This repository exposes a Gradle verification task:

- **`checkRulesCoverage`** (in the `verification` group)

Behavior:

- Runs the `RuleCoverageCheck` helper
- Ensures:
  - All rule YAMLs in `ruleset/` are syntactically valid
  - Every enabled, non-lib rule has at least one positive test sample

Usage (from the `test` subdirectory):

```bash
cd test
./gradlew checkRulesCoverage
```

On success:

- `"Rule coverage check passed: all rules valid and covered."` is printed.

On failure:

- It prints all problems (invalid YAML, uncovered rules) and fails the task.

---

## Adding or Modifying Rules

When introducing or changing rules, follow these guidelines:

1. **Choose the correct location**
   - Executable vulnerability rules → `java/security/<vuln-class>.yaml`
   - Shared sources, sinks, or helpers → `java/lib/generic/` or `java/lib/spring/`

2. **Mark library-only rules**
   - Add `options.lib: true` for library fragments in `lib/` (or exceptionally in `ruleset/` if they are not meant to be executed directly).

3. **Avoid duplicates**
   - Reuse library rules from `lib/` and compose them with `mode: join` where applicable.
   - Reference join sources and sinks by `tag`, and tag each new library source or sink.

4. **Update tests**
   - Add sample code under `test/src/main/java/security/` and reference it from a
     `test/rule-test.yaml` entry with at least one `positive` (and typically `negative`) method.
   - Reference the rule by `rule-id: <relative YAML path>#<rule id>`.

5. **Run coverage checks**
   - From the `test` subdirectory execute `./gradlew checkRulesCoverage` to ensure:
     - No YAML errors
     - All executable rules are covered by tests

---

## License

This project is released under the [MIT License](LICENSE).

The [core analysis engine](https://github.com/seqra/opentaint/tree/main/core) is released under the [Apache 2.0 License](../LICENSE.md).

Rule content may incorporate or adapt patterns originally published under various open-source licenses (for example, from community rule sets). Where applicable, original provenance and license information is recorded in rule `metadata`.
