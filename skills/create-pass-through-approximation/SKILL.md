---
name: create-pass-through-approximation
description: Model a library method's taint propagation as a passThrough approximation config. Use for a dropped external method whose propagation is simple copying
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create PassThrough Approximation

Write passThrough propagation rules for external library methods. There's no test project — the main scan applies the config and verifies it; if a modeled method is still dropped or the config errors, you're re-invoked to fix it

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Methods to model `<methods>` — the target method(s) and what each propagates, from the tracking file's `methods` (all `type: passthrough`)
- Tracking file `<tracking-file>` — the passThrough approximation unit. Default: `.opentaint/tracking/approximations/<name>.yaml`
- Config output `<config-file>` — where to write the passThrough approximation. Default: `.opentaint/config/<name>.yaml`

## Workflow

### 1. Write the passThrough config

Write `passThrough:` rules into `<config-file>`

Simple getter (taint on `this` to `result`):
```yaml
passThrough:
  - function: com.example.lib.DataWrapper#getValue
    copy:
      - from: this
        to: result
```

Argument to result:
```yaml
passThrough:
  - function: com.example.lib.Converter#convert
    copy:
      - from: arg(0)
        to: result
```

Builder pattern:
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

Container via a synthetic field — when a container takes the taint in one call and hands it back in another, write into a field that doesn't really exist, then read from it:
```yaml
passThrough:
  - function: org.springframework.http.ResponseEntity$BodyBuilder#body
    copy:
      - from: arg(0)
        to:
          - result
          - .org.springframework.http.HttpEntity#Body#java.lang.Object
  - function: org.springframework.http.HttpEntity#getBody
    copy:
      - from:
          - this
          - .org.springframework.http.HttpEntity#Body#java.lang.Object
        to: result
```
The naive model — copy the data onto `this`, then on read copy `this` to `result` — fails on types: `this` is the container type, not the data type (e.g. `String`), so the engine can't hang the taint on it. Routing through a field typed `java.lang.Object` (here `#Body#java.lang.Object`) sidesteps the mismatch. A synthetic per-object slot `.<rule-storage>` does the same job without naming a field — store on the taking call, read on the returning one (see Reference)

Conditional propagation:
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

### 2. Verification is the scan

There's no test project for passThrough. The main scan applies `<config-file>` (run-scan's `--passthrough-approximations`, which takes a file or a directory) and the scan agent reports back. You're re-invoked to fix the config when that scan shows:

- a method you modeled still in `dropped-external-methods.yaml` → the `function` matcher didn't match (check package, class, name, `overrides`), or the `from`/`to` doesn't land on the tainted position
- a config load / parse error → fix the YAML

Never invoke the analyzer JAR directly — always go through the CLI

## Output

- The passThrough config at `<config-file>`
- Tracking updated: `written` + `artifact` (per Tracking)
- Report the config path and the methods modeled

## Tracking

In `<tracking-file>`, once the config is written:

```yaml
artifact: .opentaint/config/<name>.yaml
stages:
  written: done
```

Do not touch other stages or fields

## Reference

Position values
- `this`, `result`, `arg(0)`, `arg(1)`, ..., `arg(*)`
- Position modifiers (YAML list): `.[*]` (array element), `.ClassName#fieldName#fieldType` (field), `.<rule-storage>` (synthetic per-object state, an alternative to a named field)

Function matching
- Simple: `package.Class#method`
- Complex: `{package, class, name}`, each with an optional `pattern:` regex — for one hard-to-name function, not for matching many at once (see Gotchas)

Overrides
- `overrides: true` (default): applies to the class and all subclasses
- `overrides: false`: exact class only

Conditions
- `typeIs`, `annotatedWith`, `isConstant`, `isNull`, `constantMatches`, `tainted`, `numberOfArgs`, `methodAnnotated`, `classAnnotated`, `methodNameMatches`, `classNameMatches`, `isStaticField`, `anyOf`, `allOf`, `not`

## Gotchas

- passThrough expresses only from→to copies — DB round-trips, lambdas, and async belong in create-dataflow-approximation
- The approximation merges with built-ins at the rule level — a provided rule overrides a built-in only if it matches one; don't redefine a method already in `approximated-external-methods.yaml`
- A wrong argument position copies the wrong value — point `from`/`to` at the tainted one
- In doubt about how a method moves taint — which argument or field reaches the result — read the library's source rather than guessing
- Model one function per rule — don't use a regex/wildcard `pattern:` matcher (e.g. `name: get.*`, `class: .*`) to cover many functions at once; it over-models, copying taint through methods you never vetted and manufacturing false positives. Write an explicit `function:` per method
