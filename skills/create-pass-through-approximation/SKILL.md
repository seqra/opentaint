---
name: create-pass-through-approximation
description: Model a library method's taint propagation as a passThrough approximation config. Use for a dropped external method whose propagation is simple copying
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create PassThrough Approximation

Write passThrough propagation rules for external library methods

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Methods to model `<methods>` — the target method(s) and what each propagates, from the tracking file's `methods` (all `type: passthrough`)
- Tracking file `<tracking-file>` — the passThrough approximation unit. Default: `.opentaint/tracking/approximations/<name>.yaml`
- Config output `<config-file>` — where to write the passThrough approximation. Default: `.opentaint/pass-through/<name>.yaml`
- Test model `<test-model>` (optional) — any compiled model to dry-run the config against for a load/parse check. Default: `.opentaint/project` if it exists, else any `.opentaint/test-compiled/*` model

## Workflow

### 1. Write the passThrough config

Write `passThrough:` copies into `<config-file>`. When an object carries taint between calls — a setter stores it and a getter returns it later, or a builder holds it — route through a virtual slot, an access path `[<base>, .<DeclaringClass>#<slot>#java.lang.Object]`:
- the slot name is nominal — the engine never resolves it, so it need not be a real field
- type it `java.lang.Object` — a concrete type can fail the read-out type-check and drop the taint
- the writer and reader must name the identical `Class#slot#java.lang.Object` triple, or the taint drops

Getter / setter pair — the writer stores into the slot, the getter reads the same slot back to `result`:
```yaml
passThrough:
- function: org.springframework.http.HttpEntity#setBody
  copy:
  - from: arg(0)
    to:
    - this
    - .org.springframework.http.HttpEntity#Body#java.lang.Object
- function: org.springframework.http.HttpEntity#getBody
  copy:
  - from:
    - this
    - .org.springframework.http.HttpEntity#Body#java.lang.Object
    to: result
```

Several writers sharing one slot — any of them taints the object, the reader pulls it back:
```yaml
passThrough:
- function: org.apache.tools.ant.types.FileSet#setDir
  copy:
  - from: arg(0)
    to:
    - this
    - .org.apache.tools.ant.types.FileSet#path#java.lang.Object
- function: org.apache.tools.ant.types.FileSet#setFile
  copy:
  - from: arg(0)
    to:
    - this
    - .org.apache.tools.ant.types.FileSet#path#java.lang.Object
```

Cross-type builder — when a builder method consumes an argument and returns a *different* type, carry the taint along both the chained receiver (for further calls on `this`) and the returned object, slot included. Four copies: arg → returned-value slot, arg → builder slot, whole builder → returned value, builder slot → returned-value slot:
```yaml
passThrough:
- function: org.springframework.ldap.query.LdapQueryBuilder#filter
  copy:
  - from: arg(0)
    to:
    - result
    - .org.springframework.ldap.query.LdapQuery#filter#java.lang.Object
  - from: arg(0)
    to:
    - this
    - .org.springframework.ldap.query.LdapQueryBuilder#filter#java.lang.Object
  - from: this
    to: result
  - from:
    - this
    - .org.springframework.ldap.query.LdapQueryBuilder#filter#java.lang.Object
    to:
    - result
    - .org.springframework.ldap.query.LdapQuery#filter#java.lang.Object
```

Builder terminal — a no-arg `build()` / `toX()` that returns a new object carrying what the builder accumulated; no argument is involved, so copy each slot from `this` to the matching slot on `result` (the setters that filled the builder slot are separate rules of their own):
```yaml
passThrough:
- function: com.google.common.collect.ImmutableMap$Builder#build
  copy:
  - from:
    - this
    - .java.util.Map#MapKey#java.lang.Object
    to:
    - result
    - .java.util.Map#MapKey#java.lang.Object
  - from:
    - this
    - .java.util.Map#MapValue#java.lang.Object
    to:
    - result
    - .java.util.Map#MapValue#java.lang.Object
```

Conditional propagation — gate a rule with a `condition` (the copy still routes through a slot):
```yaml
passThrough:
- function: com.example.lib.Parser#parse
  condition:
    typeIs: java.lang.String
    pos: arg(0)
  copy:
  - from: arg(0)
    to:
    - this
    - .com.example.lib.Parser#parsed#java.lang.Object
```

Full config — every function in one top-level `passThrough:` list (quote `[*]` — unquoted it parses as a YAML alias):
```yaml
passThrough:
- function: org.springframework.beans.MutablePropertyValues#add
  copy:
  - from: arg(1)
    to:
    - this
    - .org.springframework.beans.PropertyValue#Value#java.lang.Object
- function: org.springframework.beans.PropertyValue#getValue
  overrides: false
  copy:
  - from:
    - this
    - .org.springframework.beans.PropertyValue#Value#java.lang.Object
    to: result
- function: org.springframework.beans.PropertyValues#getPropertyValues
  copy:
  - from:
    - this
    - .java.lang.Iterable#Element#java.lang.Object
    to:
    - result
    - '[*]'
```

### 2. Optional — dry-run the config for load errors

There's no dedicated load-check command. ONLY when invoked standalone — never under the appsec-agent orchestrator, whose subagents must not run `opentaint scan` (the orchestrator's scan phase verifies the config instead): if a compiled `<test-model>` is present you can catch YAML load/parse errors early by running a quick scan with the config applied (won't verify propagation — there's no matching flow — only that the config loads):

```bash
opentaint scan --project-model <test-model> \
  -o .opentaint/test-results/<name>/passthrough-loadcheck.sarif \
  --ruleset builtin \
  --passthrough-approximations <config-file>
```

A config error aborts the scan with the parse/load message — fix the YAML and re-run. Nice-to-have, not required; skip it when no model is around

### 3. Verification is the scan

There's no test project for passThrough. The main scan applies `<config-file>` and the scan agent reports back. You're re-invoked to fix the config when that scan shows:

- a method you modeled still in `dropped-external-methods.yaml` → the `function` matcher didn't match (check package, class, name, `overrides`), or the `from`/`to` doesn't land on the tainted position
- the flow still doesn't surface though the method is no longer dropped → most often a broken channel: the writer and reader name different `Class#slot#java.lang.Object` triples, or the slot isn't typed `java.lang.Object`
- a config load / parse error → fix the YAML (an unknown `condition` key, a bad position, or a 2-part field modifier all fail to load)

Never invoke or grep the analyzer JAR — its internals aren't a stable API; for built-in rules use `opentaint health --rules`, for everything else the CLI

### 4. When the config won't converge

After ~2 fix re-invocations without a clearer cause — matcher fields and `from`/`to` checked, writer/reader slots confirmed identical, the modeled method no longer in `dropped-external-methods.yaml`, but the scan still doesn't surface the flow — don't keep guessing at the copy. Report non-convergence to the caller: a passThrough can't express this method's propagation, so the fix is a dataflow approximation for it (a custom dataflow overrides the passThrough). The orchestrator re-plans the method as a dataflow unit and removes this passThrough config before the dataflow one is tested

## Output

- The passThrough config at `<config-file>`
- Tracking updated: `written` + `artifact` (per Tracking)
- Report the config path and the methods modeled

## Tracking

In `<tracking-file>`, once the config is written:

```yaml
artifact: .opentaint/pass-through/<name>.yaml
stages:
  written: done
```

Do not touch other stages or fields

## Reference

Position bases
- `this`, `result`, `arg(0)`, `arg(1)`, …
- `any(<classifier>)` — expands to every argument matching the classifier (a cartesian product across positions, bound consistently), not a single argument. Rare — prefer an explicit `arg(N)`

Access-path modifiers (list form `[<base>, <modifier>]`)
- `.<DeclaringClass>#<slot>#<fieldType>` — a field or virtual slot; type it `java.lang.Object`. The slot name is arbitrary (a descriptive name, or the conventional `<rule-storage>` for a generic carrier)
- `[*]` — array element (no leading dot). For `java.util` collections this does *not* carry element taint; route it through the conventional `.java.lang.Iterable#Element#java.lang.Object` slot instead (as the built-in `List`/`Collection` models do)

Function matching
- Simple: `package.Class#method`
- Complex: `{package, class, name}` — for one hard-to-name function, not for matching many at once (see Gotchas)

Overrides
- `overrides: true` (default): applies to the class and all subclasses
- `overrides: false`: exact class only

Conditions (the only keys that load from YAML)
- take a `pos: <position>`: `typeIs`, `constantMatches`, `constantEq`, `tainted`
- take the position directly, no `pos:` field: `isConstant`, `isNull` — adding `pos:` fails to load
- nest other conditions: `anyOf`, `allOf`, `not`
- `constantGt` / `constantLt` load but crash the scan when actually evaluated against a constant (their string-typed bound fails an engine type-check) — avoid until fixed

## Gotchas

- The `#` comments in the examples here are for you — don't copy them into the config you write; keep produced YAML comment-free
- The approximation merges with built-ins at the rule level — a provided rule overrides a built-in only if it matches one. Don't redefine a method already in `approximated-external-methods.yaml` unless debug-rule shows the built-in isn't propagating taint here, then override deliberately
- A wrong argument position copies the wrong value — point `from`/`to` at the tainted one
- In doubt about how a method moves taint — which argument or field reaches the result — read the library's source rather than guessing
- Model one function per rule — don't use a regex/wildcard `pattern:` matcher (e.g. `name: get.*`, `class: .*`) or `arg(*)` to cover many functions at once; it over-models, copying taint through methods you never vetted and manufacturing false positives. Write an explicit `function:` per method
