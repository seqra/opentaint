# Whole-object taint with `$VAR*`

The star operator controls field-sensitive taint scope. It does not make an AST pattern match more source code: `$BOX` and `$BOX*` select the same program value. The star changes which taint facts are marked or expected at that occurrence.

## Why base and field scope differ

OpenTaint is field-sensitive: a taint mark lives on an access path, not just on a variable. These are distinct facts:

```text
mark M on request             (the base value)
mark M on request.user.email  (one nested field)
```

Neither fact silently becomes the other. Field-sensitivity is what lets one rule report `sink(request.user.email)` without also reporting `sink(request.id)` — but it means every rule must say which scope it marks and which scope it expects.

Consider the two decisions separately, in mark/expect terms (a metavariable is a rule-private taint mark: a producer occurrence marks a value, a consumer occurrence expects the mark):

```java
Request request = receive();   // producer: mark the base only, or the base and every field?
store(request);                // consumer: expect a mark on the base only, or on the base or any field?
```

Plain and starred occurrences answer those questions differently:

```text
$REQUEST   = the base value
$REQUEST*  = the base value plus the any-field scope rooted at it, at any depth
```

All four combinations are meaningful and behave differently:

| Producer | Consumer | `store(request)` after `request.user.email` tainted |
|---|---|---|
| `$R = receive()` | `store($V)` | not reported: only the base was marked, and only the base is checked |
| `$R = receive()` | `store($V*)` | not reported: no field was ever marked |
| `$R* = receive()` | `store($V)` | not reported: fields carry marks, but the sink checks the base only |
| `$R* = receive()` | `store($V*)` | reported: fields carry marks and the sink accepts a mark on any field |

The star belongs to an occurrence, not to the metavariable's identity. `$REQUEST` and `$REQUEST*` refer to the same bound value, and a rule may star one occurrence of a name while leaving another occurrence plain.

Adjacency is significant:

```text
$X*       whole-object occurrence
$X * $Y   multiplication
```

`$Y*` directly followed by a non-identifier is the star operator; `$Y * z` with whitespace stays arithmetic.

### Where a star may appear

The star attaches to a metavariable occurrence in expression-like positions:

- Java/JVM: a call argument `sink($Y*)`, an assignment left-hand side `$X* = src()`, a typed declaration `String $X* = src()`, a formal parameter `$TYPE $INPUT*` inside a method-declaration pattern, and a return value `return $UNTRUSTED*;`.
- Go: a call argument `pkg.Sink($Y*)`, an assignment left-hand side `$X* = pkg.Source()`, a typed metavariable `($Y* : string)`, and a receiver position `$C*.Serve()` including typed receivers `($C* : *exec.Cmd).Run()`.

Constraint fields (`focus-metavariable`, `metavariable-pattern`, `metavariable-regex`, propagator `from`/`to`, join `on`) always use the plain name; see [Star and pattern clauses](#star-and-pattern-clauses).

## Producer and consumer semantics

Producers and consumers use whole-object scope differently:

| Role | Plain occurrence | Starred occurrence |
|---|---|---|
| Source | mark base | mark base and any-field |
| Sink | expect mark on base | expect mark on base or any nested field |
| Sanitizer | clean base | clean base and any-field |
| Propagator `from` | read base mark | read base or nested-field mark |
| Propagator `to` | mark output base | mark output base and any-field |

A starred source marks with AND semantics — both the base and the any-field scope — because it claims the complete produced object is untrusted. A starred sink expects with OR semantics — a mark on the base or on any nested field — because one tainted field is enough to make the whole-object sink dangerous. A starred sanitizer cleans with AND semantics on the same value the plain clean applies to, so no field taint survives it.

## Starred source

Use a starred source when an API returns an object whose complete contents should be treated as untrusted — a parsed request body, a deserialized message, a decoded upload.

```yaml
rules:
  - id: untrusted-box-source
    languages: [java]
    mode: taint
    message: Untrusted box field reaches a sink
    severity: ERROR
    pattern-sources:
      - patterns:
          - pattern: $BOX* = src()
          - focus-metavariable: $BOX
    pattern-sinks:
      - patterns:
          - pattern: sink($VALUE)
          - focus-metavariable: $VALUE
```

Positive — the star carries taint through a concrete field read to a plain sink:

```java
Box box = src();              // marks box and box.<any field>
String value = box.getValue();
sink(value);                  // the field read inherited the mark
```

Negative — a locally built object never receives the mark:

```java
Box box = new Box();
box.setValue("safe");
sink(box.getValue());
```

Removing the source star turns the positive into a false negative: a plain `$BOX = src()` marks only the base, and the value extracted from a field carries nothing. That is exactly the case the source star exists for.

The starred occurrence can also sit on a typed declaration or a formal parameter. A typical whole-object entry point is a handler whose bound parameter object is entirely attacker-controlled:

```yaml
pattern-sources:
  - patterns:
      - pattern: |
          @$ANNOTATION(...)
          $RET $METHOD(..., $TYPE $INPUT*, ...) {
            ...
          }
      - focus-metavariable: $INPUT
```

```java
@PostMapping("/profile")
String update(ProfileForm form) {   // $INPUT* marks form and all its fields
    return render(form.getBio());   // the field read carries the mark
}
```

Go uses the same rule role with Go-shaped patterns:

```yaml
rules:
  - id: untrusted-data-source
    languages: [go]
    mode: taint
    message: A whole-object source field reaches the sink
    severity: WARNING
    pattern-sources:
      - pattern: $X* = util.Source()
    pattern-sinks:
      - pattern: util.Sink($Y)
```

```go
// Positive: the starred source taints the object and all its fields.
d := Source()
Sink(d.Field)

// Negative: the object is built from a constant; no field is tainted.
var d Data
d.Field = "safe"
Sink(d.Field)
```

## Starred sink

Use a starred sink when passing an object is dangerous if either the object base or any nested field is tainted — storing it, serializing it, writing it to a response.

```yaml
rules:
  - id: whole-box-sink
    languages: [java]
    mode: taint
    message: Tainted data is stored by the box sink
    severity: ERROR
    pattern-sources:
      - patterns:
          - pattern: $VALUE = source()
          - focus-metavariable: $VALUE
    pattern-sinks:
      - patterns:
          - pattern: store($BOX*)
          - focus-metavariable: $BOX
```

Base positive — the sink object itself carries the mark:

```java
Box box = source();
store(box);
```

Nested-field positive — one tainted field is enough:

```java
Box box = new Box();
box.value = source();
store(box);
```

Negative — a clean object with clean fields:

```java
Box box = new Box();
box.value = "safe";
store(box);
```

A plain `store($BOX)` sink is base-only by design: it does not add the nested-field arm, so the nested-field positive above would not be reported. Star the sink occurrence when field taint must count.

Go equivalent:

```yaml
rules:
  - id: whole-box-store
    languages: [go]
    mode: taint
    message: Tainted struct field reaches a whole-object sink
    severity: WARNING
    pattern-sources:
      - pattern: util.Source(...)
    pattern-sinks:
      - patterns:
          - pattern: util.SinkBox($Y*)
          - focus-metavariable: $Y
```

```go
// Positive: a source-tainted value is written into a nested field.
var b Box
b.Value = Source()
SinkBox(b)

// Negative: the field is never tainted.
var b Box
b.Value = "safe"
SinkBox(b)
```

A typed starred metavariable keeps both the type constraint and the whole-object scope:

```yaml
pattern-sinks:
  - patterns:
      - pattern: 'storage.Store(($BOX* : *model.Box))'
      - focus-metavariable: $BOX
```

Receiver positions star the same way. A realistic command-execution sink reports when any field of the command object was attacker-influenced:

```yaml
pattern-sinks:
  - pattern-either:
      - patterns:
          - pattern: '($C* : *exec.Cmd).Run()'
          - focus-metavariable: $C
      - patterns:
          - pattern: '($C* : *exec.Cmd).CombinedOutput()'
          - focus-metavariable: $C
```

And a response-write sink where a tainted field inside the written object is the finding:

```yaml
pattern-sinks:
  - patterns:
      - pattern: $W.Write($B*)
      - focus-metavariable: $B
```

## Starred sanitizer

Use a starred sanitizer when the returned object and all of its nested contents are safe for this vulnerability after the call.

```yaml
rules:
  - id: clean-box
    languages: [java]
    mode: taint
    message: Unsanitized box field reaches a sink
    severity: ERROR
    pattern-sources:
      - patterns:
          - pattern: $VALUE = source()
          - focus-metavariable: $VALUE
    pattern-sanitizers:
      - patterns:
          - pattern: clean($BOX*)
          - focus-metavariable: $BOX
    pattern-sinks:
      - patterns:
          - pattern: sink($VALUE)
          - focus-metavariable: $VALUE
```

Positive — no sanitizer between the field write and the field read:

```java
Box box = new Box();
box.value = source();
sink(box.getValue());
```

Negative — the whole-object sanitizer clears the field taint, so the later field read is clean:

```java
Box box = new Box();
box.value = source();
Box cleaned = clean(box);
sink(cleaned.getValue());
```

The starred sanitizer cleans the result base and its any-field scope together, anchored to the same value. A plain `clean($BOX)` sanitizer cleans only the base: field taint written before the call would survive and the negative above would become a false positive of the rule's own making.

Go equivalent:

```yaml
rules:
  - id: clean-box
    languages: [go]
    mode: taint
    message: Tainted struct field reaches the sink unless the whole object is cleaned
    severity: WARNING
    pattern-sources:
      - pattern: util.Source(...)
    pattern-sanitizers:
      - patterns:
          - pattern: util.Clean($C*)
          - focus-metavariable: $C
    pattern-sinks:
      - pattern: util.Sink($Y)
```

```go
// Positive: field taint reaches the sink with no sanitizer in between.
var b Box
b.Value = Source()
Sink(b.Value)

// Negative: Clean($C*) clears the object including the nested field.
var b Box
b.Value = Source()
cleaned := Clean(b)
Sink(cleaned.Value)
```

## Starred propagators

The star on the `from` and the `to` occurrence is independent, giving four combinations. The `from:` and `to:` fields always contain the plain metavariable names; scope comes from the occurrences in the AST pattern.

### Base to base

```yaml
pattern-propagators:
  - pattern: $OUTPUT = wrap($INPUT)
    from: $INPUT
    to: $OUTPUT
```

```text
base input mark -> base output mark
```

Use this for scalar-like transformations.

```java
String raw = source();
Wrapper w = wrap(raw);   // the base mark moves to w
sink(w);
```

### Any input field to output base

```yaml
pattern-propagators:
  - pattern: $OUTPUT = summarize($INPUT*)
    from: $INPUT
    to: $OUTPUT
```

```text
base or nested input mark -> base output mark
```

```java
Request request = new Request();
request.query = source();
String summary = summarize(request);   // the tainted field influences the scalar summary
sink(summary);
```

Without the `from` star the propagator reads only the base mark, and the field-tainted request would produce a clean summary.

### Input base to whole output

```yaml
pattern-propagators:
  - pattern: $OUTPUT* = expand($INPUT)
    from: $INPUT
    to: $OUTPUT
```

```text
base input mark -> base and any-field output marks
```

```java
String raw = source();
Document document = expand(raw);       // the scalar controls the whole document
sink(document.metadata.title);         // any field read is tainted
```

### Any input field to whole output

```yaml
pattern-propagators:
  - pattern: $OUTPUT* = cloneAndFlatten($INPUT*)
    from: $INPUT
    to: $OUTPUT
```

```text
base or nested input mark -> base and any-field output marks
```

Use this only when every nested input can influence the complete output. It is deliberately the broadest combination.

Go uses the same four combinations with Go-shaped assignment patterns:

```yaml
pattern-propagators:
  - pattern: $OUTPUT* = model.CloneAndFlatten($INPUT*)
    from: $INPUT
    to: $OUTPUT
```

A propagator is rule-local. If the movement is ordinary library behavior rather than something meaningful to this specific rule, model it once as a [pass-through model](passthrough-models.md) instead.

## Star and pattern clauses

Star does not replace any pattern clause. It changes the taint scope of a metavariable occurrence selected by that clause. Which clause the occurrence sits in decides only where the pattern matches; the star decides what is marked or expected there.

### `pattern`

In a pure search rule, these bind the same program value:

```yaml
pattern: use($VALUE)
```

```yaml
pattern: use($VALUE*)
```

The star matters only when the occurrence is consumed by a taint role — a source, sink, sanitizer, propagator, or join boundary. In a rule with no taint role attached to `$VALUE`, both spellings report the same matches.

### `patterns`

Starred and plain occurrences of one name still unify:

```yaml
patterns:
  - pattern: |
      ...
      $BOX* = sourceBox();
      ...
  - pattern: |
      ...
      audit($BOX);
      ...
```

Both occurrences refer to the same `$BOX`. The producer occurrence controls whole-object marking; the `audit` occurrence remains a plain structural use. A rule that stars the source occurrence and leaves the sink occurrence plain loads cleanly and means exactly what it says: mark everything, expect on the base only.

### `pattern-either`

Set scope explicitly in every branch:

```yaml
pattern-sources:
  - patterns:
      - pattern-either:
          - pattern: $INPUT* = request.bodyObject()
          - pattern: $INPUT* = request.jsonObject()
      - focus-metavariable: $INPUT
```

Branches are independent alternatives, so a star in one branch does not carry to another. Star only one branch when the APIs genuinely return different taint scopes — for example, one API returns an attacker-controlled object and the other returns an attacker-controlled string:

```yaml
pattern-either:
  - pattern: $INPUT* = request.bodyObject()
  - pattern: $INPUT = request.queryString()
```

### `pattern-inside`

A starred produced value can be bound in an enclosing declaration or factory pattern:

```yaml
pattern-sources:
  - patterns:
      - pattern-inside: |
          $REQUEST_TYPE $REQUEST* = receive();
          ...
      - pattern: process($REQUEST)
      - focus-metavariable: $REQUEST
```

The producer occurrence inside the enclosing context carries the star; the focused name stays plain. The mark scope is decided where the value is produced, not where it is focused.

### `metavariable-pattern` and regex constraints

Constraints refer to the plain identity:

```yaml
metavariable-pattern:
  metavariable: $REQUEST
  pattern: Request
```

```yaml
metavariable-regex:
  metavariable: $METHOD
  regex: ^(receive|read)$
```

Do not write `$REQUEST*` in the `metavariable:` field. The constraint restricts which values the name can bind; the star on an occurrence elsewhere in the formula still controls taint scope for that occurrence.

### `focus-metavariable`

Focus always uses the plain name:

```yaml
patterns:
  - pattern: store($BOX*)
  - focus-metavariable: $BOX
```

Focus selects which bound value the role applies to; the starred occurrence in the AST pattern decides the scope.

## Star and negative patterns

Negative patterns remain structural exclusions. The star does not mean "search through fields" inside `pattern-not`, and a negative clause never removes taint — it removes matches.

A non-coinciding negative composes with a starred positive without interaction:

```yaml
patterns:
  - pattern: store($BOX*)
  - pattern-not: store(safeBox())
  - focus-metavariable: $BOX
```

The sink keeps its whole-object expectation — the any-field check is still generated — and the negative removes one concrete structural form from the match set.

### Coinciding positive and negative occurrences

When a positive and a negative pattern select the same position, the scopes should agree:

| Positive | Negative | Result |
|---|---|---|
| `$X` | `$X` | full structural exclusion |
| `$X*` | `$X*` | full structural exclusion |
| `$X*` | `$X` | full structural exclusion, plus a non-fatal rule-load diagnostic |

Example of the third row:

```yaml
patterns:
  - pattern: |
      @$ANNOTATION(...)
      $RET $METHOD(..., $TYPE $INPUT*, ...) {
        ...
      }
  - pattern-not: |
      @$ANNOTATION(...)
      $RET $METHOD(..., @PathVariable $TYPE $INPUT, ...) {
        ...
      }
```

In principle the mismatched pair could mean "exclude the base arm but keep nested-field taint", but that scoped complement is not supported. The combination behaves as full exclusion — identical to writing `$INPUT*` in the negative — and the loader reports a non-fatal diagnostic so the mismatch is visible. The rule still loads. Write the same scope in both occurrences when full exclusion is intended; do not rely on the diagnostic appearing for every position (some negative positions are resolved before the check runs).

The ordinary rule for negatives is unchanged: every metavariable used by a negative pattern must be introduced by a positive producer pattern. Star does not make free negative metavariables valid. See [negative clauses and metavariable domains](rule-pattern-clauses.md#negative-clauses-and-metavariable-domains).

## Star and joins

The star is written in the reusable component's AST pattern, not in the `join.on` string. `on` names select bound captures; scope was already decided at the component occurrence.

Whole-object left source component:

```yaml
rules:
  - id: object-source
    languages: [java]
    options: { lib: true }
    mode: taint
    message: Object source
    severity: NOTE
    pattern-sources:
      - patterns:
          - pattern: $INPUT* = request.bodyObject()
          - focus-metavariable: $INPUT
```

Whole-object right sink component:

```yaml
rules:
  - id: object-store-sink
    languages: [java]
    options: { lib: true }
    mode: taint
    message: Object store sink
    severity: NOTE
    pattern-sinks:
      - patterns:
          - pattern: store($VALUE*)
          - focus-metavariable: $VALUE
```

Join:

```yaml
rules:
  - id: body-to-store
    languages: [java]
    mode: join
    message: A request body object reaches the object store
    severity: ERROR
    join:
      refs:
        - rule: java/lib/example/object-source.yaml#object-source
          as: source
        - rule: java/lib/example/object-store-sink.yaml#object-store-sink
          as: sink
      on:
        - 'source.$INPUT -> sink.$VALUE'
```

The left component marks the base and the any-field scope at the selected boundary. The right component accepts the incoming mark on its base or any nested field:

```java
Body body = request.bodyObject();   // left: base + any-field marks
Record record = new Record();
record.payload = body.text;          // field-to-field movement
store(record);                       // right: any-field expectation fires
```

The `on` metavariables stay plain because star is occurrence scope, not part of the name. Mixed compositions are legitimate: a starred source component with a plain sink component means "everything in the body is untrusted, but only passing the object itself to the sink is dangerous".

Star does not change join's bipartite graph restriction and does not enable intermediate aliases.

## Star versus pass-through field copying

Star uses a coarse any-field summary:

```text
some field below input is tainted
```

It does not promise that `input.profile.email` maps to `output.profile.email`.

A pass-through copy preserves relative field structure:

```yaml
copy:
  - from: arg(0)
    to: result
```

Use `$VAR*` for security-rule scope such as "any part of this request object". Use a [pass-through model](passthrough-models.md) for external-library movement that must preserve or remap field paths.

## Review checklist

- Plain and starred occurrences are chosen deliberately from the producer/consumer table.
- Source tests distinguish base-only from nested-field propagation.
- Sink tests cover a base mark, a nested-field mark, and a clean object.
- Sanitizer tests prove both base and field cleaning.
- Propagator tests cover the exact `from`/`to` star combination used.
- Every OR branch declares its intended scope.
- Focus, constraint, propagator `from`/`to`, and join `on` fields use the plain metavariable name.
- Coinciding positive and negative occurrences use the same scope.
- Join stars live in component AST patterns, not `join.on` names.
- Pass-through models are used when exact field-path structure matters.
