# Pass-through models

A pass-through model is a small DSL that describes how data moves through an external function or method whose body the analyzer cannot see. Without a model, taint stops at such a call; with a model, the analyzer knows exactly which outputs each input influences.

The format is language-agnostic. The core of every model is a set of copy relations:

```text
copy(from position, to position[, one taint kind])
```

Java/JVM and Go specialize only the way a callable and its positions are named. The copy semantics are shared, so this guide describes the common model once and then the per-language specializations.

Three properties define the semantics:

- **A model is field-sensitive.** A `copy` keeps the taint structure of the `from` object: every marked access path below `from` is copied, with its relative field path preserved, onto `to`. It does not mean the coarse "if the source object is tainted, taint the destination object."
- **Every action applies independently and out of order.** The output of one action is never the input of another action within the same call, so every real movement must be written explicitly.
- **A model describes ordinary library behavior only.** Use a [dataflow approximation](dataflow-models.md) instead when the external operation invokes user code, such as a callback, lambda, supplier, consumer, coroutine continuation, or asynchronous stage.

The complete built-in catalogs live under [`model/java/config`](../model/java/config/) and [`model/go/config`](../model/go/config/); they are the best source of real examples.

## The common semantic model

### Field-sensitive structural copy

Consider an incoming fact on an access path:

```text
arg(0).profile.email  carries mark M
```

For this action:

```yaml
copy:
  - from: arg(0)
    to: result
```

the analyzer preserves the suffix relative to `arg(0)` and produces:

```text
result.profile.email  carries mark M
```

A fact on the source base is copied to the destination base, while a fact on a source field is copied to the corresponding destination field. With an explicit source or destination modifier, the suffix is read below that access path and attached below the destination access path.

### Actions are independent and unordered

A model is relational, not procedural. Every `copy` action is evaluated independently against the same incoming fact. Actions may be listed in any order, and the output of one action is not fed into the next action in the same external call.

This model is therefore incomplete:

```yaml
copy:
  - from: arg(0)
    to: this
  - from: this
    to: result
```

It expresses the two edges `arg(0) -> this` and `this -> result`. It does **not** derive `arg(0) -> result` during that call. If all three movements are real, write all three:

```yaml
copy:
  - from: arg(0)
    to: this
  - from: this
    to: result
  - from: arg(0)
    to: result
```

Each model entry is also independent of every other matching pass-through entry. Do not depend on file order, rule order, or action order to create a transitive chain.

### Copying all marks and copying one mark

By default a copy preserves every taint mark and the access-path structure:

```yaml
- from: arg(0)
  to: result
```

The action can restrict the relation to one mark kind with `taintKind`. This is useful for generated, security-specific configurations, but ordinary library models should omit it: a general library conversion should work for every security rule, including rules added later.

`taintKind` is a JVM capability. Hand-written Go models read `from` and `to` only.

## Common envelope

Every model file selects a language and contains a `passThrough` list:

```yaml
language: java
passThrough:
  - function: com.example.Text#normalize
    copy:
      - from: arg(0)
        to: result
```

A file whose top-level `language` key is absent, or names a different language than the scan, is silently ignored. Built-in JVM files may also contain `library` and `dependencies`; those are packaging metadata, not copy semantics.

Conceptually, each entry has:

- a language-specific callable matcher;
- zero or more language-specific matching constraints;
- one or more common `copy` relations.

## Common positions and access paths

The position vocabulary shared by both languages is:

| Position | Meaning |
|---|---|
| `this` | Instance receiver |
| `arg(0)`, `arg(1)`, ... | Zero-based explicit arguments |
| `arg(*)` | Every argument; expands to one copy per actual argument of the matched callable |
| `any(name)` | An any-argument position with a stable classifier |
| `result` | Return value, or the whole result |

A `result` position on a `void` method and a `this` position on a static function match nothing; the action is silently skipped for that callable.

A scalar denotes the base. A YAML list denotes a base followed by accessors:

```yaml
from:
  - arg(0)
  - .com.example.Input#payload#java.lang.Object
to:
  - result
  - .com.example.Output#payload#java.lang.Object
```

The common accessor modifiers are:

- `.<declaring type>#<field or virtual slot>#<field type>` — one field or named channel;
- `'[*]'` — the element accessor;
- `.*` — the any-field accessor.

Quote `'[*]'` because an unquoted `*` has YAML alias syntax. Use `.*` only when the real API loses all field identity: it deliberately widens the access path to any nested field.

Virtual slots do not have to be real fields. They are named channels. A writer and reader connect only when the declaring type, slot name, and slot type are identical:

```yaml
# writer
- from: arg(0)
  to: [this, .com.example.Box#content#java.lang.Object]

# reader
- from: [this, .com.example.Box#content#java.lang.Object]
  to: result
```

Use distinct slots for independent state. One `content` slot for every property makes unrelated setters and getters contaminate one another.

## Modeling recurring behaviors

### Pure transform or conversion

```yaml
copy:
  - from: arg(0)
    to: result
```

The whole marked structure of the argument, including nested field paths, is carried onto the result. List every input that can influence the output: a formatter that uses a template and values needs one independent `from -> result` relation per influencing input.

### Fluent mutation

Suppose `append(x)` mutates the receiver and returns it. The complete behavior normally includes old receiver state, the new value, and the returned value:

```yaml
copy:
  - from: this
    to: result
  - from: arg(0)
    to: [this, .com.example.Builder#content#java.lang.Object]
  - from: [this, .com.example.Builder#content#java.lang.Object]
    to: result
  - from: arg(0)
    to: result
```

The last relation is not redundant: `arg(0) -> this` and `this -> result` do not chain within the same call, so the direct `arg(0) -> result` edge must be explicit.

### Setter and getter across calls

```yaml
passThrough:
  - function: com.example.Envelope#setBody
    copy:
      - from: arg(0)
        to: [this, .com.example.Envelope#body#java.lang.Object]
  - function: com.example.Envelope#getBody
    copy:
      - from: [this, .com.example.Envelope#body#java.lang.Object]
        to: result
```

Here the two actions belong to different calls at different program points, so the state written by `setBody` is visible to `getBody` through the shared slot. This is different from attempting to chain two actions inside one call, which never works.

### Builder whose result has a different type

```yaml
passThrough:
  - function: com.example.QueryBuilder#build
    copy:
      - from: [this, .com.example.QueryBuilder#filter#java.lang.Object]
        to: [result, .com.example.Query#filter#java.lang.Object]
```

The suffix below the source slot is re-attached below the destination slot, so a copy can intentionally remap a field path between types. Map each logical channel separately, and add `this -> result` only if the whole receiver value genuinely influences the whole result.

### Collection, map, and array elements

Conventional JVM virtual channels include:

| Logical state | Accessor/channel |
|---|---|
| Iterable element | `.java.lang.Iterable#Element#java.lang.Object` |
| Map key | `.java.util.Map#MapKey#java.lang.Object` |
| Map value | `.java.util.Map#MapValue#java.lang.Object` |
| Optional value | `.java.util.Optional#Element#java.lang.Object` |
| Stream element | `.java.util.stream.BaseStream#Element#java.lang.Object` |

An array conversion can preserve element structure directly:

```yaml
copy:
  - from: [arg(0), '[*]']
    to: [result, '[*]']
```

Container summaries do not retain a concrete map key or collection index. If per-key or per-index correlation is essential, record that precision requirement in a negative test; a pass-through summary may be too broad.

### Output parameter

```yaml
copy:
  - from: arg(1)
    to: arg(0)
```

This is common for writers, decoders, and APIs that fill a caller-supplied buffer. The marked structure of the data argument is copied onto the buffer argument, fields included.

## JVM specialization

### Callable matching

The compact matcher is `<fully-qualified class>#<method>`:

```yaml
function: java.lang.String#valueOf
function: java.lang.String#<init>
function: java.util.Map$Entry#getValue
```

Use `$` for nested JVM classes and `<init>` for constructors. Constrain overloads with a signature:

```yaml
function: com.example.Text#replace
signature: (java.lang.String, java.lang.String) java.lang.String
```

The structured form can constrain selected parameters or the return:

```yaml
signature:
  params:
    - index: 0
      type: java.io.Reader
  return: java.lang.String
```

Complex name matchers are available for true method families:

```yaml
function:
  package: java.lang
  class: String
  name:
    pattern: replace.*
```

Prefer an exact callable and signature. A broad name regex also captures future overloads whose behavior may differ.

`overrides` defaults to `true`, so a base-type model applies to overriding implementations. Set it to `false` when only the declaring class has the behavior. This is hierarchy matching, not action ordering.

### JVM-only conditions

When a signature cannot distinguish behavior, a JVM model can add a condition:

```yaml
condition:
  anyOf:
    - typeIs: java.io.StringReader
      pos: arg(0)
    - typeIs: java.io.ByteArrayInputStream
      pos: arg(0)
```

The condition language also has boolean `allOf` and `not`, plus type, annotation, null, constant, and constant-regex checks. Prefer signatures when possible because they are easier to audit and test.

`taintCopyOnly` and `bypassVerification` appear in generated JVM files but have no effect on how copy actions are applied. Do not use them to express semantics in new hand-written models.

## Go specialization

Go uses a structured matcher:

```yaml
language: go
passThrough:
  - function:
      package: strings
      name: ReplaceAll
      receiver: false
    copy:
      - from: arg(0)
        to: result
      - from: arg(2)
        to: result
```

Receiver methods add `type`:

```yaml
- function:
    package: net/http
    type: Header
    name: Get
    receiver: true
  copy:
    - from: this
      to: result
```

A receiver model matches both pointer and value receivers automatically. Non-receiver built-ins use the package name `<builtin>`.

Multi-result functions use `result(0)`, `result(1)`, and so on. Each is a tuple slot below `result`; `result(*)` is the whole result.

Go accessors include pseudo-fields such as `.<type>#<element>`, `.<type>#<key>`, and `.<type>#<value>`. They all collapse to the common element accessor. `.<pointer>#<deref>` is an identity accessor and is removed. Ordinary struct fields keep their field name, with an unspecified field type.

Hand-written Go models support exactly the callable fields and `copy` list shown above. JVM-style signatures, conditions, `overrides`, and `taintKind` are not read, and entries without a usable function or copy action are silently dropped. A scan that starts successfully is therefore not proof that the model loaded — always validate behaviorally.

## Validation workflow

Use the smallest project that proves the relation and produces a real analyzer artifact:

```bash
opentaint scan \
  --project-model .opentaint/project \
  --ruleset .opentaint/rules \
  --passthrough-approximations .opentaint/pass-through/example.yaml \
  --track-external-methods \
  -o .opentaint/results/example.sarif
```

For repository rule tests, pass the same model to `opentaint test rule run`. Verify all of these:

1. A base fact crosses the callable.
2. A nested-field fact crosses and retains its relative field path.
3. A sibling field does not become tainted unless the model intentionally uses `.*`.
4. Every direct movement works without depending on another action in the same entry.
5. Writer/reader slots connect across separate calls.
6. Unrelated overloads, receiver types, keys, or state channels remain negative.
7. The method disappears from `dropped-external-methods.yaml` in an `opentaint scan` run with `--track-external-methods` (the flag is available on `scan` only, not on `opentaint test rule run`).

Inspect the SARIF flow, not only the test summary. If matching succeeds but taint stops, compare the exact `from`/`to` bases and every accessor component. If behavior crosses user code, replace the model with a dataflow approximation.

## Review checklist

- The external behavior is expressible as a finite set of direct copies.
- The correct language specialization matches the real callable.
- Every real movement is explicit; no action relies on rule order or same-call chaining.
- Field-sensitive suffixes are preserved, broadened, or remapped intentionally.
- Every influencing input is included and unrelated inputs are excluded.
- Stateful channels use precise, identical writer/reader slot triples.
- Arrays/elements, map keys, and map values use the appropriate distinct channels.
- JVM overload and hierarchy matching are deliberate.
- Positives and negatives validate base, nested-field, overload, and state-separation behavior in real scan artifacts.
