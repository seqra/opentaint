---
name: create-yaml-config
description: Add a YAML passThrough model for an external library method that kills taint via simple from→to copies. Use to fix false negatives caused by unmodelled library methods on a real source→sink path (no lambdas — see `create-approximation`).
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.1"
---

# Skill: Create YAML Config

Create YAML passThrough propagation rules for library methods

## When a passThrough rule actually changes the scan

A custom `passThrough` entry only affects the analyzer's behavior if the target method is an **external method with no existing model**. In practice: the method must appear in `.opentaint/results/external-methods-without-rules.yaml` produced by the previous scan (see `analyze-findings` skill). That file is exactly the list of methods where the analyzer killed dataflow facts for lack of a rule — those are the FN sources you can fix.

Do not write passThrough rules for:
- Methods in `external-methods-with-rules.yaml` — already modeled by a built-in YAML passThrough. Since `--approximations-config` replaces the entire built-in list, writing a custom config means you implicitly own all passThrough coverage; adding a duplicate method entry is not a hard error, but you are now responsible for all methods previously covered by built-ins.
- Methods that appear in neither list — the analyzer never reached them on a tainted path during the scan; the rule will be a no-op until that changes.
- Application-internal methods — approximations apply only to external library methods.

**Rule of thumb**: open `external-methods-without-rules.yaml`, pick methods on a code path from a source to a sink relevant to the target vulnerability, and write passThrough rules for those.

## Prerequisites

- A baseline scan has been run with `--track-external-methods` (see `run-analysis` skill)
- `external-methods-without-rules.yaml` has been read; the methods you plan to model are in it (see `analyze-findings` skill)
- The method's propagation can be described by simple from/to copies (otherwise use `create-approximation`)

## Procedure

### 1. Create config file

Create `.opentaint/config/custom-propagators.yaml` with `passThrough:` rules.

### 2. Common patterns

**Simple getter** (taint on `this` to `result`):
```yaml
passThrough:
  - function: com.example.lib.DataWrapper#getValue
    copy:
      - from: this
        to: result
```

**Argument-to-result**:
```yaml
passThrough:
  - function: com.example.lib.Converter#convert
    copy:
      - from: arg(0)
        to: result
```

**Builder pattern**:
```yaml
passThrough:
  - function: com.example.lib.Builder#withName
    copy:
      - from: arg(0)
        to: this
      - from: arg(0)
        to: result
      - from: this
        to: result
```

**Object with internal state** (using `<rule-storage>`):
```yaml
passThrough:
  # Store taint
  - function: com.example.lib.Container#put
    copy:
      - from: arg(0)
        to:
          - this
          - .com.example.lib.Container#<rule-storage>#java.lang.Object
  # Retrieve taint
  - function: com.example.lib.Container#get
    copy:
      - from:
          - this
          - .com.example.lib.Container#<rule-storage>#java.lang.Object
        to: result
```

**Package-wide getter pattern**:
```yaml
passThrough:
  - function:
      package: com.example.dto
      class:
        pattern: .*
      name:
        pattern: get.*
    copy:
      - from: this
        to: result
```

**Conditional propagation**:
```yaml
passThrough:
  - function: com.example.lib.Parser#parse
    condition:
      typeIs:
        position: arg(0)
        type: java.lang.String
    copy:
      - from: arg(0)
        to: result
```

### 3. Run with config

`--approximations-config` is repeatable; all supplied files are merged together into a single combined config. That combined config then **replaces the entire built-in passThrough list** — not per-method, but the whole list. If the combined config is non-empty, no built-in passThrough entry is active; you own the full set.

```bash
opentaint scan --project-model .opentaint/project \
  -o .opentaint/results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --rule-id java/security/my-vuln.yaml:my-vulnerability \
  --approximations-config .opentaint/config/custom-propagators.yaml \
  --track-external-methods
```

### 4. Confirm the rule actually fired

Keep `--track-external-methods` enabled and diff the fresh `external-methods-without-rules.yaml` with the baseline one:

- Every method you added a `passThrough` for should disappear from `without-rules` (it now moves to `with-rules`)
- If a method does not move, the `function` matcher did not match — check package, class, name, and `overrides:`
- If no new findings appear even though facts now propagate, the method was not on a source→sink path and the rule had no effect on results (harmless but noise; consider removing)

## Reference

### Position values
- `this`, `result`, `arg(0)`, `arg(1)`, ..., `arg(*)`
- Position modifiers (YAML list): `.[*]` (array element), `.ClassName#fieldName#fieldType` (field), `.<rule-storage>` (synthetic state)

### Function matching
- Simple: `package.Class#method`
- Complex: `{package, class, name}` with optional `pattern:` regex

### Overrides
- `overrides: true` (default): applies to class and all subclasses
- `overrides: false`: exact class only

### Conditions
`typeIs`, `annotatedWith`, `isConstant`, `isNull`, `constantMatches`, `tainted`, `numberOfArgs`, `methodAnnotated`, `classAnnotated`, `methodNameMatches`, `classNameMatches`, `isStaticField`, `anyOf`, `allOf`, `not`

## When to use YAML vs code-based approximation

- Simple from-to propagation -> **YAML** (this skill)
- Lambda/callback invocation -> **Code-based** (create-approximation skill)
- Non-deterministic branching -> **Code-based**
- Method is not in `external-methods-without-rules.yaml` -> **do nothing**; the rule will be a no-op (or, worse, an unintended OVERRIDE of an existing model)
