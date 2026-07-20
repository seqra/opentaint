# Pattern clauses, taint rules, and joins

AST patterns are taint-based relationships. Producing metavariable occurrences
assign rule-private marks, and later occurrences expect those marks. Pattern
clauses combine these relationships. Explicit taint roles add vulnerability
marks, and join edges export and expect selected component marks to construct
a composed taint rule. Method names do not have an inherent source or sink
meaning.

These YAML semantics are language agnostic. Java/JVM and Go differ only in the [AST pattern](ast-patterns.md) written inside each clause.

## A reliable reading order

Read a formula in this order:

1. Positive clauses establish candidate matches and metavariable domains.
2. Context clauses require the candidates to occur inside a larger structure.
3. Constraint clauses narrow already bound metavariables.
4. Negative clauses subtract complete structural cases.
5. An explicit taint or join role, if present, adds vulnerability-mark semantics to the pattern's own metavariable marks.

YAML list order does not make independent clauses execute in sequence. Use one multi-event AST pattern with explicit `...` when event order matters.

## Positive clauses

### `pattern`

`pattern` contributes one AST relationship:

```yaml
pattern: dangerous($VALUE)
```

At rule top level it creates a plain/search rule. The pattern is compiled as a
taint automaton: produced metavariables receive rule-private marks, repeated
occurrences expect them, and the accepting event reports the finding. Inside
`pattern-sources`, `pattern-sinks`, `pattern-sanitizers`, or
`pattern-propagators`, the same pattern automaton additionally selects where
the vulnerability mark is created, expected, removed, or moved. The called
method name has no intrinsic source or sink meaning.

Use one top-level body form: `pattern`, `patterns`, or `pattern-either`. Do not place all three beside one another and expect an implicit conjunction.

### `patterns`: all facts must hold

`patterns` is logical AND. Shared metavariable names join the facts:

```yaml
patterns:
  - pattern: |
      ...
      $CLIENT = Client.builder();
      ...
  - pattern: |
      ...
      $CLIENT.connect($URL);
      ...
```

Both facts must exist for the same `$CLIENT`, in any order: the conjunction
matches whether the builder call comes first or last, and does not match when
the two calls happen on different clients or only one of them occurs.

The join works in any occurrence position. Two conjuncts that observe the
shared value as a call argument — `register($X)` in one, `activate($X)` in
the other — unify the same way.

Note the shape: when a conjunction contains more than one positive `pattern`,
each conjunct must be a statement sequence wrapped in **both** a leading and a
trailing `...`, as above. Each conjunct is turned into its own matching
automaton and the conjuncts are intersected; the two ellipses give a conjunct
the open boundaries that make the intersection possible. Dropping either
ellipsis — or writing a bare expression conjunct such as
`- pattern: $CLIENT.connect($URL)` — makes the rule fail to load. The bare
expression form is supported only when the conjunction has a single positive
pattern beside its `pattern-inside`, negative, and constraint clauses.

This conjunction does not require the builder call to occur before `connect`. If order is required, write one ordered pattern:

```yaml
pattern: |
  $CLIENT = Client.builder();
  ...
  $CLIENT.connect($URL);
```

Go uses the same clause with Go AST syntax:

```yaml
pattern: |
  $CLIENT := NewClient()
  ...
  $CLIENT.Connect($URL)
```

### Many metavariables are a fact schema

This pattern intentionally produces three columns:

```yaml
pattern: $RESULT = $CLIENT.convert($INPUT)
```

Use them only when later clauses need them:

```yaml
patterns:
  - pattern: |
      ...
      $RESULT = $CLIENT.convert($INPUT);
      ...
  - pattern: |
      ...
      audit($CLIENT, $RESULT);
      ...
```

Adding unused metavariables makes matching broader and creates more fact combinations:

```yaml
# Harder to reason about if $MODE and $LOGGER are never reused.
pattern: $RESULT = $CLIENT.convert($INPUT, $MODE, $LOGGER)
```

Prefer literals, types, `...`, or `$_` for positions whose identity is not part of the security relationship.

A wide fact schema also constrains where the pattern can be used later: a many-metavariable pattern placed in a negative clause needs every one of those metavariables introduced positively. See [Negative clauses and metavariable domains](#negative-clauses-and-metavariable-domains).

### `pattern-either`: any complete alternative may hold

`pattern-either` is logical OR:

```yaml
pattern-either:
  - pattern: $INPUT = request.getParameter(...)
  - pattern: $INPUT = request.getHeader(...)
```

Each branch produces the same `$INPUT` schema. That makes it safe to focus or reuse outside the OR:

```yaml
patterns:
  - pattern-either:
      - pattern: $INPUT = request.getParameter(...)
      - pattern: $INPUT = request.getHeader(...)
  - focus-metavariable: $INPUT
```

If different overloads bind different dangerous positions, keep the focus inside complete alternatives:

```yaml
pattern-sinks:
  - patterns:
      - pattern: execute($COMMAND)
      - focus-metavariable: $COMMAND
  - patterns:
      - pattern: execute($CONTEXT, $COMMAND, ...)
      - focus-metavariable: $COMMAND
```

## Enclosing context

### `pattern-inside`

`pattern-inside` requires the positive match to occur inside a larger accepted context.

Factory/builder example:

```yaml
patterns:
  - pattern-inside: |
      $CLIENT = Client.builder();
      ...
      $CLIENT.enableUnsafeRedirects();
      ...
  - pattern: $CLIENT.connect($URL)
```

The inside pattern does three jobs:

- it produces `$CLIENT` from the factory result;
- it requires unsafe configuration on that same client;
- its explicit `...` preserves the required order.

The ellipses are load-bearing in two ways. First, the shape: an inside
context must end with `...` (a method-declaration context's `{ ... }` body
plays the same role) — a bare expression or a statement without a trailing
ellipsis makes the rule fail to load. Second, the leading ellipsis is a
semantic switch:

- **Trailing `...` only** — the context starts at its first event, so the
  main pattern must match **after** it. `pattern-inside: $X.prepare();\n...`
  with `pattern: $X.fire()` matches `prepare` then `fire`, and does not match
  `fire` then `prepare`.
- **Leading and trailing `...`** — the context is any method that contains
  the event, so the main pattern may match anywhere, before or after it.
  `pattern-inside: ...\n$X.prepare();\n...` accepts both orders. The
  same-value join still holds in both forms: `prepare` on one object and
  `fire` on another never matches, and a method with no `prepare` never
  matches.

Go import and receiver example:

```yaml
patterns:
  - pattern-inside: |
      import "net/http"
      ...
  - pattern: '($CLIENT : *http.Client).Get($URL)'
```

Multiple independent `pattern-inside` clauses do not impose order on each other:

```yaml
patterns:
  - pattern-inside: |
      enableA($X);
      ...
  - pattern-inside: |
      enableB($X);
      ...
  - pattern: use($X)
```

This accepts either `enableA`/`enableB` order, but the match must lie inside
every context: `use` before one of the enables does not match, and a sample
with only one enable does not match. Put both events in one `pattern-inside`
if their order relative to each other matters.

The direct child of `pattern-inside` must currently be one AST pattern. Put `patterns` or `pattern-either` outside it and repeat the inside context for alternatives when necessary.

## Negative clauses

Negative clauses subtract structural matches. They do not sanitize taint and they do not create metavariable values.

### `pattern-not`

`pattern-not` subtracts matches from the surrounding positive relation. Its
metavariables live in the positive formula's domain, and it has two working
forms: narrowing and trace filtering.

**Narrowing** re-describes the same events in a more specific form; whatever
the specific form covers is excluded. The simplest narrowing replaces a
metavariable with a concrete value:

```yaml
patterns:
  - pattern: consume($VALUE)
  - pattern-not: consume("safe")
```

Every `consume` call is a candidate except the call of the safe literal.

A real narrowing from the built-in ruleset excludes annotations that declare
an explicit HTTP method:

```yaml
patterns:
  - pattern: |
      @RequestMapping(...)
      $RETURNTYPE $METHOD(...) { ... }
  - pattern-not: |
      @RequestMapping(..., method = $X, ...)
      $RETURNTYPE $METHOD(...) { ... }
```

Because the negative re-describes the positive's own events, its
metavariables coincide with the positive's. A fresh metavariable is fine when
it only makes the same event more specific — `$X` above exists purely inside
the narrowed annotation argument list.

**Trace filtering** repeats the positive event sequence with one additional
on-path event; an accepted trace that contains the added event on the way is
filtered out:

```yaml
patterns:
  - pattern: |
      $RESULT = decode($INPUT);
      ...
      consume($RESULT);
  - pattern-not: |
      $RESULT = decode($INPUT);
      ...
      $RESULT = $RESULT.sanitized();
      ...
      consume($RESULT);
```

The decoded value that passes through `sanitized()` on its way to `consume`
is not reported; a value that reaches `consume` without it still is. The
repeated producer may be replaced by a leading ellipsis:

```yaml
  - pattern-not: |
      ...
      $RESULT = $RESULT.sanitized();
      ...
      consume($RESULT);
```

The added event may use the tracked value in any position — as a call
receiver like `$RESULT.sanitized()` or `$MAPPER.enable(...)`, or as a call
argument like `sanitize($RESULT)`. Use `pattern-sanitizers` instead whenever
safety should apply to the rule's taint semantics rather than to one
structural match.

### `pattern-not-inside`

`pattern-not-inside` subtracts a candidate when it occurs in a forbidden enclosing context.

Safe builder configuration:

```yaml
patterns:
  - pattern-inside: |
      $CLIENT = Client.builder();
      ...
  - pattern: $CLIENT.connect($URL)
  - pattern-not-inside: |
      $CLIENT = Client.builder();
      ...
      $CLIENT.allowHost("trusted.example");
      ...
```

The positive inside pattern produces `$CLIENT`. The negative uses the same produced identity, so configuration on another client does not exclude this match.

Test all of these separately:

```java
// Positive: unsafe client.
Client client = Client.builder();
client.connect(url);

// Negative: safe configuration on the same client.
Client client = Client.builder();
client.allowHost("trusted.example");
client.connect(url);

// Positive: safe configuration belongs to another client.
Client safe = Client.builder();
safe.allowHost("trusted.example");
Client unsafe = Client.builder();
unsafe.connect(url);

// Positive: configuration happens after the dangerous operation.
Client client = Client.builder();
client.connect(url);
client.allowHost("trusted.example");
```

`pattern-not-inside` is an AST/event exclusion, not a whole-program proof. Aliases, branches, repeated configuration, and reconfiguration need their own tests.

## Negative clauses and metavariable domains

A negative clause subtracts values from the domain established by the positive formula. It cannot search an unbounded universe for values that were never introduced positively.

Introduction must be **producing**, not expecting. A metavariable is introduced only where a positive pattern defines its value:

- an assignment or declaration result: `$CLIENT = Client.builder()`;
- a typed declaration: `Client $CLIENT = ...`;
- a formal parameter in a positive declaration context;
- another positive result-producing event.

A use-site occurrence — a call argument, or a receiver observed at an expected event — only expects an already produced value. It does not introduce the value, and it cannot support a complex negative relation over that name.

This is a temporal restriction of the current rule representation. The workaround is always the same: add positive `pattern`/`pattern-inside` clauses that produce every metavariable the negative needs — provided those producers are genuinely part of the unsafe shape being detected.

### Invalid: negative-only metavariables

```yaml
patterns:
  - pattern: $CLIENT.connect($URL)
  - pattern-not-inside: |
      $FACTORY.configure($MODE);
      ...
```

`$FACTORY` and `$MODE` exist only in the negative. There is no positive fact domain to subtract from.

The failure is silent: the rule loads without an error, but the negative clause never excludes anything, and the rule reports even when the supposedly excluded context is present. Test every negative with a sample that the negative must suppress; over-reporting is the only visible symptom.

### Invalid: expecting occurrence used as an introduction

```yaml
patterns:
  - pattern: $CLIENT.connect($URL)
  - pattern-not-inside: |
      $CLIENT.allowHost($HOST);
      ...
```

`$CLIENT` does appear positively — but only as the receiver of the expected `connect` event. That occurrence expects a value; it never produces the builder/factory identity the negative reasons about. `$HOST` is negative-only. Neither metavariable is properly introduced.

### Workaround: produce the identity, then subtract

A complete rule with the producer introduced positively:

```yaml
rules:
  - id: client-connect-without-allowlist
    languages: [java]
    severity: WARNING
    message: Client connects without an allow-listed host
    patterns:
      - pattern-inside: |
          $CLIENT = Client.builder();
          ...
      - pattern: $CLIENT.connect($URL)
      - pattern-not-inside: |
          $CLIENT = Client.builder();
          ...
          $CLIENT.allowHost("trusted.example");
          ...
```

The `pattern-inside` clause produces `$CLIENT` at the factory result; the terminal pattern and the negative reuse that produced identity. The safe host is a concrete literal, so the negative introduces no new metavariable.

Repeating the producing event inside the negative is optional: the rule excludes the same samples when the negative contains only `$CLIENT.allowHost("trusted.example"); ...`. Keep the repetition when you want the exclusion visibly anchored to the creation-to-use span; it does not change which clients are excluded. What is not optional is the positive producer itself — moving `$CLIENT = Client.builder()` out of the positive formula and into the negative alone silently disables the exclusion.

Test it with the four-sample matrix shown under [`pattern-not-inside`](#pattern-not-inside): unsafe client, safely configured client, safe configuration on a different client, and configuration after the dangerous call.

### Workaround: produce every negative metavariable

Sometimes the exclusion genuinely needs two identities. Both must be produced by the positive context:

```yaml
rules:
  - id: client-built-from-untrusted-policy
    languages: [java]
    severity: WARNING
    message: Client is built from a policy that is not the trusted factory's
    patterns:
      - pattern-inside: |
          $POLICY = $FACTORY.createPolicy(...);
          ...
          $CLIENT = Client.builder($POLICY);
          ...
      - pattern: $CLIENT.connect($URL)
      - pattern-not-inside: |
          $POLICY = TrustedPolicy.createPolicy(...);
          ...
          $CLIENT = Client.builder($POLICY);
          ...
```

The broad positive factory call produces `$POLICY`, and `Client.builder($POLICY)` produces `$CLIENT`. The negative narrows those already produced values to the trusted-factory case.

This workaround is valid only when the positive producers are required by the real unsafe case. Do not add artificial positive patterns solely to satisfy the rule engine; doing so silently changes what the rule detects.

### How the negative may use a produced value

Once the metavariable is produced positively, the negative — whether a
`pattern-not` trace filter or a `pattern-not-inside` context — may use it in
any occurrence position:

- **as the receiver of the excluded call** — `$CLIENT.allowHost("trusted.example")`,
  `$RESULT = $RESULT.sanitized()`; the excluded event may lie directly on the
  value's dataflow path;
- **as an argument of the excluded call** — `check($RESULT)`;
- **as a narrowed re-description of its producing events** — the
  trusted-policy rule above repeats `$CLIENT = Client.builder($POLICY)` with a
  more specific producer for `$POLICY`.

### Validated shape summary

| Negative shape | Effect |
|---|---|
| `pattern-not`: same events, narrowed (literal, name, annotation argument — fresh metavariable allowed inside the narrowing) | Excludes |
| `pattern-not`: repeated sequence plus one on-path event using the produced value (producer repetition or leading `...`) | Excludes (trace filter) |
| `pattern-not-inside`: produced value used in the excluded call | Excludes |
| `pattern-not-inside`: narrowed re-description of the producing events | Excludes |
| Any negative with a metavariable that is not positively produced | Silently no effect |
| Safety that must span the whole rule rather than one structural match | Use `pattern-sanitizers` |

A negative whose metavariables are not positively produced loads without
diagnostics and over-reports. Give each negative a test sample that it must
suppress; a failing negative is invisible any other way.

### When there is no workaround

A negative expectation over several truly existential values — values the real unsafe case does not naturally produce — cannot currently be expressed. For example:

```yaml
pattern-not-inside: |
  $UNKNOWN_FACTORY.configure($UNKNOWN_MODE);
  ...
  $UNKNOWN_CLIENT.connect($UNKNOWN_URL);
```

There is no producer to add: the rule is trying to subtract every possible factory/client combination, and the positive case does not relate those values.

Sometimes a rewrite avoids the case entirely — enumerate the unsafe configurations positively:

```yaml
pattern-either:
  - pattern: $CLIENT = Client.builder()
  - pattern: $CLIENT = Client.builder(UnsafePolicy.defaultPolicy())
```

or replace free metavariables in the negative with concrete literals. Whether such a rewrite preserves the rule's meaning depends on the rule; some cases cannot be rewritten without changing what is detected. Keep those as a documented limitation of the rule and add a negative test for the desired behavior, so the gap is visible and covered when the restriction is lifted.

The restriction is temporary to the current rule representation, but rules written today must respect it.

## Constraint clauses

### `metavariable-regex`

Constrain an already bound metavariable:

```yaml
patterns:
  - pattern: $RUNTIME.$METHOD($VALUE)
  - metavariable-regex:
      metavariable: $METHOD
      regex: ^(exec|load|loadLibrary)$
```

Go literal-name example:

```yaml
patterns:
  - pattern: exec.Command("$SHELL", ..., $ARG, ...)
  - metavariable-regex:
      metavariable: $SHELL
      regex: ^(sh|bash)$
```

Regex meaning depends on what the metavariable captured: method name, type, string literal, annotation value, or another supported local syntax element. Test the exact capture role.

### `metavariable-pattern`

Use `metavariable-pattern` to constrain local syntax captured by an existing metavariable:

```yaml
patterns:
  - pattern-inside: |
      @$MAPPING(...)
      $RETURN $METHOD(...) { ... }
  - metavariable-pattern:
      metavariable: $MAPPING
      pattern-either:
        - pattern: GetMapping
        - pattern: PostMapping
```

Current support is limited to constraints reducible to concrete or regex conditions on the captured metavariable. Do not place arbitrary event sequences, inside clauses, focus, or comparisons inside it.

`metavariable-comparison` and rule-level `pattern-regex`/`pattern-not-regex` are not currently executable rule features. A `pattern-regex` nested inside a reducible `metavariable-pattern` may become a local regex constraint, but `metavariable-regex` is clearer.

### `focus-metavariable`

Focus selects the exact value a taint role should mark or expect:

```yaml
pattern-sinks:
  - patterns:
      - pattern: execute($OPTIONS, $COMMAND)
      - focus-metavariable: $COMMAND
```

Without focus, a call-shaped sink can be broader than intended and accept taint on another argument or receiver. Every surviving alternative must bind the focused name.

Focus uses the plain metavariable name even when its AST occurrence is starred:

```yaml
- pattern: sink($VALUE*)
- focus-metavariable: $VALUE
```

Negated focus is unsupported. Sanitizer focus does not currently redirect cleaning to an arbitrary argument; sanitizer behavior is described below.

## Rewrites that do not preserve meaning

Matching is not distributive across ordering, negation, and OR. Each
transformation below looks plausible but changes what the formula accepts —
these are the points of non-distributivity to check before refactoring a rule:

### Ordered pattern versus independent conjunction

```yaml
pattern: |
  configure($X);
  ...
  use($X);
```

is not equivalent to:

```yaml
patterns:
  - pattern: |
      ...
      configure($X);
      ...
  - pattern: |
      ...
      use($X);
      ...
```

The first requires order; the second requires two facts joined on `$X` in
either order.

### One complete negative versus several negatives

```yaml
pattern-not: |
  enableA($X);
  ...
  enableB($X);
```

excludes the complete sequence. Two separate `pattern-not` clauses exclude either event independently.

### Shared name versus renamed name

```yaml
patterns:
  - pattern: |
      ...
      create($X);
      ...
  - pattern: |
      ...
      use($X);
      ...
```

joins on identity. Renaming the second occurrence to `$Y` allows independent values and creates a Cartesian combination.

### OR and negative placement

```text
not (A or B) = not A and not B
```

This is different from `(A and not X) or (B and not Y)`. Keep a positive and negative for every branch when moving an OR across a negative boundary.

### Multiple inside clauses versus one ordered inside clause

Two inside clauses impose two contexts but no order between them — the match
must only lie inside both. One multi-event inside clause imposes order
between its events with explicit `...`. A leading ellipsis on an inside
clause removes even the context-before-match requirement; see
[`pattern-inside`](#pattern-inside).

## Taint rules

A taint rule has four independent role lists:

```yaml
mode: taint
pattern-sources: []
pattern-sinks: []
pattern-sanitizers: []
pattern-propagators: []
```

There are two mark layers:

1. Every AST pattern uses rule-private metavariable marks to implement its own
   identity and event relationship.
2. The containing taint role creates, expects, removes, or moves the
   vulnerability mark that flows between those patterns.

For example:

```yaml
pattern-sources:
  - patterns:
      - pattern: $INPUT = request.getParameter(...)
      - focus-metavariable: $INPUT
pattern-sinks:
  - patterns:
      - pattern: execute($SQL)
      - focus-metavariable: $SQL
```

The source AST pattern first reaches its own accepting state and identifies
`$INPUT`; the source role then assigns the vulnerability mark to that value.
The sink AST pattern identifies `$SQL`; the sink role expects the vulnerability
mark there. The analyzer follows ordinary program flow between those two
selected values.

### `pattern-sources`

A source marks the focused or inferred value:

```yaml
pattern-sources:
  - patterns:
      - pattern: $INPUT = request.getParameter(...)
      - focus-metavariable: $INPUT
    label: HTTP_INPUT
```

Go:

```yaml
pattern-sources:
  - patterns:
      - pattern: $INPUT := web.Query(...)
      - focus-metavariable: $INPUT
    label: HTTP_INPUT
```

`label` is optional. `requires` can make the new label depend on earlier labels.

Source fields `exact`, `control`, and `by-side-effect` are accepted by YAML but do not currently change JVM rule generation. Do not rely on them.

### `pattern-sinks`

A sink checks the focused or inferred value for the rule's taint:

```yaml
pattern-sinks:
  - patterns:
      - pattern: (java.sql.Statement $STATEMENT).executeQuery($SQL)
      - focus-metavariable: $SQL
    requires: HTTP_INPUT
```

Go:

```yaml
pattern-sinks:
  - patterns:
      - pattern: '($DB : *sql.DB).Exec($SQL, ...)'
      - focus-metavariable: $SQL
    requires: HTTP_INPUT
```

Without `requires`, the sink accepts any label introduced by the rule. Boolean label expressions support `and`, `or`, and `not`.

Sink `requires` objects containing metavariables are not currently supported; they are treated as unconditional over the rule labels after a diagnostic.

### `pattern-sanitizers`

A sanitizer removes this rule's taint from the matched call result:

```yaml
pattern-sanitizers:
  - pattern: $SAFE = validateProgram(...)
```

This makes the result safe for this rule. It does not declare the operation safe for unrelated vulnerability classes.

With `by-side-effect: true`, current JVM conversion also cleans the receiver:

```yaml
pattern-sanitizers:
  - pattern: $BUFFER.escapeInPlace()
    by-side-effect: true
```

Focus does not currently redirect a sanitizer to an arbitrary argument. `exact` is parsed but does not change cleaning.

Always use vulnerability-specific sanitizers. HTML escaping is not SQL parameterization; URL encoding is not SSRF allow-listing; path normalization is not containment validation.

### `pattern-propagators`

A propagator moves one of this rule's labels between two bound values:

```yaml
pattern-propagators:
  - pattern: $OUTPUT = securitySpecificTransform($INPUT)
    from: $INPUT
    to: $OUTPUT
```

Go:

```yaml
pattern-propagators:
  - pattern: $OUTPUT := security.Transform($INPUT)
    from: $INPUT
    to: $OUTPUT
```

Every alternative must bind both names. Propagator `by-side-effect` is parsed but does not currently change JVM propagation.

Use a [pass-through model](passthrough-models.md) for general external-library movement. Use a rule propagator only when the edge is meaningful specifically to this security rule.

### Labels as a state machine

Labels are useful when the vulnerability requires stages:

```yaml
pattern-sources:
  - pattern: $RAW = readExternal()
    label: RAW
  - pattern: $PARSED = parse($RAW)
    requires: RAW
    label: PARSED
pattern-sinks:
  - pattern: interpret($PARSED)
    requires: PARSED
```

Do not add labels merely to rename ordinary taint. Every label combination needs tests.

## Reuse with `mode: join`

A join is a composition form for a taint rule. Its edges choose which captured
metavariables become marking boundaries and which become expectations. The
referenced patterns already use their own metavariable marks internally. A
left edge exports the selected accepting metavariable as a mark; a right edge
requires that exported mark on the selected metavariable while evaluating the
right pattern.

### Library components

A reusable component is built but not reported directly:

```yaml
rules:
  - id: servlet-untrusted-source
    languages: [java]
    message: Servlet input source
    severity: NOTE
    options:
      lib: true
    tags: [servlet-untrusted-data-source]
    pattern: $UNTRUSTED = $REQUEST.getParameter(...)
```

A join composes that source with a sink component:

```yaml
rules:
  - id: example-injection
    languages: [java]
    mode: join
    message: Servlet input reaches the example interpreter
    severity: ERROR
    join:
      refs:
        - tag: servlet-untrusted-data-source
          as: source
        - rule: java/lib/example/interpreter-sinks.yaml#interpreter-sink
          as: sink
      on:
        - 'source.$UNTRUSTED -> sink.$VALUE'
```

`->` turns the left selected capture into a taint boundary and the right capture into a taint expectation. It does not compare source text.

### Explicit references and tags

A reference contains exactly one of:

```yaml
- rule: path/to/rules.yaml#specific-rule
  as: source
```

```yaml
- tag: servlet-untrusted-data-source
  as: source
```

A tag is an open, language-scoped union:

- active rules with the tag are included;
- disabled rules and other languages are excluded;
- no active target is an error;
- both tagged sides expand as a Cartesian product;
- aliases must be unique;
- a join cannot reference another join.

The built-in ruleset organizes tags into role families following the `<framework>-untrusted-data-source` and `<vulnerability>-sink` convention — for example `servlet-untrusted-data-source`, `spring-untrusted-data-source`, `sqli-sink`, `ssrf-sink`, `path-traversal-sink`, and `command-injection-sink`. Tagging your own rule with a family name extends every join that consumes that family.

Use a tag only when a new tagged member should intentionally extend every consumer.

### Aliases and renames

`as` gives a component its local join alias. `renames` can expose a component metavariable under a clearer join-facing name:

```yaml
refs:
  - rule: java/lib/example/source.yaml#source
    as: source
    renames:
      - from: $FRAMEWORK_VALUE
        to: $INPUT
on:
  - 'source.$INPUT -> sink.$VALUE'
```

Keep renames one-to-one and use simple metavariable names.

### Inline components

`join.rules` can define a component used only by that join. The loader forces inline components into library mode. Separate library rules are usually easier to test, tag, override, and reuse.

### Several left or right sides

Many sources may feed one sink:

```yaml
on:
  - 'servlet.$INPUT -> sink.$VALUE'
  - 'spring.$INPUT -> sink.$VALUE'
```

Their marks are unioned before the right component. Every edge entering the same right alias must select the same right metavariable.

One source may feed several sinks:

```yaml
on:
  - 'source.$INPUT -> sql.$VALUE'
  - 'source.$INPUT -> command.$VALUE'
```

The right components become independent composed findings.

### Matching and taint components

A matching rule can be used on either side even though its own pattern has no
taint role. On a left edge, the selected capture becomes a marking boundary.
On a right edge, the selected capture becomes a mark expectation.

A taint rule on the left:

- must define sources;
- must not define sinks;
- must join on a simple metavariable whose exact spelling equals a source label, for example `$TAINTED` with `label: $TAINTED`.

A taint rule on the right must not define sources; it inherits sources from the left.

Sanitizers and propagators apply only on the `from`/`to` edges of the composed rule — they remain on the component and edge side where they are defined:

```text
left source logic -> selected from boundary -> selected to boundary -> right sanitizer/propagator/sink logic
```

A sanitizer defined in a right-side component cleans only flows entering through that component's edge; a propagator moves marks only along its own component's side. Neither becomes a global clause for other aliases.

### Current graph restriction

Join graphs are directed and bipartite:

```text
left/source aliases  --->  right/sink aliases
```

An alias may appear on several left edges or several right edges, but not in both sets.

Unsupported chain:

```text
A.$X -> B.$X
B.$X -> C.$X
```

Only `->` composition is implemented. Equality-like operations recognized by parsing are not executable join modes.

Supporting a DAG requires defined intermediate input labels, output marks, local sanitizer/propagator ownership, topological ordering, fan-out behavior, and collision-free namespaces. Until then, flatten the stages into one taint component with labels or compose a direct left-to-right edge.

## Clause review checklist

- Positive patterns establish every value the formula needs.
- Ordered events use one AST pattern with explicit `...`.
- Every OR branch binds the values required outside it.
- Negative metavariables are produced in the positive formula.
- A negative excludes one complete intended relationship.
- Safe configuration is tested on the same and on a different object.
- Focus identifies the exact source or sink operand.
- Sanitizers are vulnerability-specific and use implemented behavior.
- General library movement lives in models, not propagators.
- Tags are deliberate open extension points.
- Join graphs remain bipartite and edge-local behavior is understood.
