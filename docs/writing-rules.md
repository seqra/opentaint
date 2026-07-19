# Writing high-quality rules

OpenTaint executes rules through taint marks. The authoring forms differ in
where those marks come from and where they are expected:

- a pattern rule uses rule-private marks to carry metavariable bindings
  between the events of the pattern;
- `mode: taint` adds explicit vulnerability sources, sinks, sanitizers, and
  propagators;
- `mode: join` connects selected marks from reusable components into a new
  taint rule.

This guide is the practical starting point. The rule format is divided into four independent references:

1. [AST patterns](ast-patterns.md) describe program structure in the target language.
2. [Pattern clauses, taint rules, and joins](rule-pattern-clauses.md) combine AST patterns and give them security meaning.
3. [The whole-object star operator](star-operator.md) chooses between a value's base and its nested fields.
4. [Rule metadata and lifecycle](rule-metadata.md) controls identity, reporting, reuse, and activation.

The YAML composition language is shared by Java/JVM and Go. Only the source-shaped text inside an AST pattern is language-specific. Each reference explains the common behavior first and then calls out Java and Go syntax where they differ. This guide follows the same convention: the workflow and the quality criteria are language-agnostic, and every code sample is labeled Java/JVM or Go.

## Read metavariables as marks

An AST pattern says where a metavariable mark is created and where that mark
must be present later. Consider an ordered pattern:

```yaml
# Java/JVM
pattern: |
  $CLIENT = Client.builder();
  ...
  $CLIENT.connect($URL);
```

```yaml
# Go
pattern: |
  $CLIENT := client.NewBuilder()
  ...
  $CLIENT.Connect($URL)
```

Read either form as:

```text
Client.builder() result  -> assign the rule-private $CLIENT mark
$CLIENT.connect(...)     -> require that mark on the receiver
final accepted event     -> report the rule
```

This is taint-based matching, not textual metavariable substitution. It is why
the same metavariable can follow a value across intermediate program events.
`$URL` is bound at the terminal event, but because this pattern does not reuse
it later, it does not establish another cross-event requirement.

The surrounding rule form can give the selected positions additional taint
meaning:

| Context | Additional mark semantics |
|---|---|
| Pattern rule | Carry rule-private metavariable marks between pattern events and report on acceptance |
| `pattern-sources` | Create the rule's vulnerability mark on the focused or inferred value |
| `pattern-sinks` | Expect a compatible vulnerability mark on the focused or inferred value |
| `pattern-sanitizers` | Remove the rule's vulnerability mark according to sanitizer semantics |
| `pattern-propagators` | Move a vulnerability mark between `from` and `to` |
| Left side of `join.on` | Export the selected component metavariable as a mark |
| Right side of `join.on` | Expect the exported mark on the selected component metavariable |

Method names such as `source`, `sink`, or `sanitize` have no special meaning
by themselves. The pattern position and surrounding rule clause determine
which marks are assigned or expected.

## Choose the right rule form

| Need | Use |
|---|---|
| Report one completed pattern relationship | Pattern rule (mode omitted or `search`) |
| Follow data from trust boundary to dangerous operation | Taint rule |
| Reuse independently maintained source and sink families | Join rule |
| Copy values through an unavailable external method | Pass-through model |
| Invoke a callback or model async/control-flow behavior | Dataflow approximation |

### Pattern rule (mode omitted or `search`)

A pattern rule has no separate clause lists: the pattern itself carries the
taint relationship through its metavariables and ellipses. Use it when the
complete evidence is one sequence of events over the same values:

```yaml
# Java/JVM
rules:
  - id: decoded-value-consumed
    languages: [java]
    severity: WARNING
    message: A decoded value reaches consume without processing
    pattern: |
      $RESULT = decode($INPUT);
      ...
      consume($RESULT);
```

```yaml
# Go
rules:
  - id: decoded-value-consumed
    languages: [go]
    severity: WARNING
    message: A decoded value reaches consume without processing
    pattern: |
      $RESULT := codec.Decode($INPUT)
      ...
      codec.Consume($RESULT)
```

Read the pattern as mark movement:

```text
$RESULT = decode($INPUT)  -> assign the rule-private $RESULT mark to the result
...                       -> unrelated events may occur; the order is enforced
consume($RESULT)          -> expect the $RESULT mark on the argument; report
```

The producing occurrence marks a value; the later occurrence expects that
mark; the ellipsis states that other events may happen in between. Because
matching is taint-based, the mark follows the value through assignments,
aliases, and calls whose bodies are available — the two events do not have to
touch the same variable name.

When the whole relationship is a single structure, the pattern is one event
and reports as soon as it matches — the degenerate case with no marks to
carry:

```yaml
# Go
rules:
  - id: insecure-tls-verification
    languages: [go]
    message: TLS certificate verification is disabled
    severity: ERROR
    pattern: 'tls.Config{InsecureSkipVerify: true, ...}'
```

The name `search` describes the rule format, not a separate non-taint
execution model. Structural negative and contextual clauses change which
automaton paths can reach acceptance.

Start its test matrix with one matching structure and one nearby structure
that must not match: for the multi-event rule above, a sample with the events
in the wrong order; for the one-event rule, a config without the insecure
field. Add a separate negative for each structural distinction the rule
relies on, such as argument position, type, annotation, enclosing
configuration, or constant value.

### Taint rule

Use a taint rule when the finding depends on a value moving between two operations:

```yaml
# Java/JVM
rules:
  - id: example-injection
    languages: [java]
    mode: taint
    message: Untrusted input reaches the example interpreter
    severity: ERROR
    pattern-sources:
      - patterns:
          - pattern: $INPUT = request.getParameter(...)
          - focus-metavariable: $INPUT
    pattern-sinks:
      - patterns:
          - pattern: Interpreter.run($CODE)
          - focus-metavariable: $CODE
```

The AST patterns locate and bind values. Their containing roles supply the
taint semantics:

```text
source pattern focuses $INPUT  -> create mark on $INPUT
sink pattern focuses $CODE     -> expect that mark on $CODE
```

OpenTaint follows the mark through assignments, fields, aliases, calls whose
bodies are available, and configured external models. A finding is produced
when a compatible mark reaches the value selected by the sink pattern.

The equivalent Go-shaped clauses change only their AST patterns:

```yaml
# Go
pattern-sources:
  - patterns:
      - pattern: $INPUT := web.Query(...)
      - focus-metavariable: $INPUT
pattern-sinks:
  - patterns:
      - pattern: interp.Run($CODE)
      - focus-metavariable: $CODE
```

### Join rule

Use a join when the patterns that select marking and expectation boundaries
are useful independently. A join is a reusable way to construct a taint rule:

```yaml
rules:
  - id: servlet-input-to-example-interpreter
    languages: [java]
    mode: join
    message: Servlet input reaches the example interpreter
    severity: ERROR
    join:
      refs:
        - rule: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
          as: source
        - rule: java/lib/example/interpreter-sinks.yaml#interpreter-sink
          as: sink
      on:
        - 'source.$UNTRUSTED -> sink.$VALUE'
```

The referenced rules contribute patterns and bound metavariables. They are not
intrinsically sources or sinks. The join gives them taint roles: the left selection
`source.$UNTRUSTED` becomes the place where taint is marked and the right
selection `sink.$VALUE` becomes the place where that mark is expected. The
arrow requests dataflow between those boundaries; it is not text equality
between metavariables.

A ref can also name a `tag:` family instead of a single rule, so the join
grows automatically as the family gains members; see
[Reusable rule design](#reusable-rule-design) below and
[Explicit references and tags](rule-pattern-clauses.md#explicit-references-and-tags).

## Define the taint relationship

This source-to-expectation step applies to explicit taint and join rules, not
pattern rules. Write down four things before writing their YAML:

1. Which selected program value should receive the mark?
2. Which selected program value should expect the mark?
3. Which operations remove or change the mark for this vulnerability?
4. Does an unavailable external method interrupt propagation?

For example:

```text
mark HTTP parameter -> SQL string -> expect mark at executeQuery argument
                                  \
                                   -> remove mark after parameterization
```

This separates responsibilities:

- a source role marks the selected HTTP-input metavariable;
- a sink role expects the mark on the selected SQL-argument metavariable;
- a sanitizer removes only the SQL-injection mark;
- a [pass-through model](passthrough-models.md) or [dataflow approximation](dataflow-models.md) describes ordinary external-library behavior.

Do not duplicate general library propagation in individual security rules.

## Build one complete taint path first

For a taint or join rule, begin with the narrowest positive path that
represents the vulnerability:

```java
// Java/JVM
void positive(HttpServletRequest request) {
    String input = request.getParameter("query");
    Interpreter.run(input);
}
```

```go
// Go
func positive(w http.ResponseWriter, r *http.Request) {
    input := r.URL.Query().Get("query")
    interp.Run(input)
}
```

Write the source and sink patterns for this case, run it, and inspect the SARIF flow. Only then add overloads, framework variants, sanitizers, or exclusions.

This order makes failures local:

- no source event means the source AST pattern is wrong;
- no sink event means the sink AST pattern is wrong;
- both events without a path usually means a missing external model or an incorrect focused value;
- an unexpected finding usually means a broad sink, broad source, or missing vulnerability-specific sanitizer.

## Test every taint boundary

A taint or join rule is not high quality until it distinguishes the vulnerable
path from nearby safe paths.

For the Java/JVM example above, add at least:

```java
void negativeConstant() {
    Interpreter.run("fixed program");
}

void negativeSanitized(HttpServletRequest request) {
    String input = request.getParameter("query");
    String safe = validateProgram(input);
    Interpreter.run(safe);
}

void negativeWrongArgument(HttpServletRequest request) {
    String input = request.getParameter("query");
    Interpreter.runWithOptions("fixed program", input);
}
```

These negatives answer different questions:

- Does the sink require taint?
- Does the sanitizer clean the correct flow?
- Is the dangerous argument position focused precisely?

Do not use one broad negative sample to stand in for all three. The matrix is
language-agnostic: a Go rule needs the same three negatives, only the sample
syntax differs.

## Grow alternatives without losing the fact schema

Suppose two source APIs produce the same logical value:

```yaml
# Java/JVM
pattern-sources:
  - patterns:
      - pattern-either:
          - pattern: $INPUT = request.getParameter(...)
          - pattern: $INPUT = request.getHeader(...)
      - focus-metavariable: $INPUT
```

Both alternatives produce `$INPUT`. That gives the surrounding focus and taint source one consistent fact schema.

Avoid an alternative that does not bind the required value:

```yaml
# Wrong: the second branch does not produce $INPUT.
pattern-either:
  - pattern: $INPUT = request.getParameter(...)
  - pattern: request.hasParameters()
```

If two overloads have different dangerous positions, use two complete sink alternatives with their own focus rather than one unfocused call pattern.

## Keep structural exclusion separate from sanitization

`pattern-not` and `pattern-not-inside` subtract AST matches. They do not remove taint from a value.

Use a negative AST pattern to exclude a structurally safe form — a narrowed version of the same event, a safe context around the tracked value, or a trace that passes through a safe receiver call:

```yaml
# Java/JVM: exclude clients that were allow-listed before connecting.
patterns:
  - pattern-inside: |
      $CLIENT = Client.builder();
      ...
  - pattern: $CLIENT.connect($URL)
  - pattern-not-inside: |
      $CLIENT.allowHost("trusted.example");
      ...
```

```yaml
# Java/JVM: filter the traces where the value was self-sanitized on the path.
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

Use `pattern-sanitizers` when data becomes safe and may continue through the program:

```yaml
pattern-sanitizers:
  - pattern: $SAFE = validateProgram(...)
```

Choose by scope and shape. A structural negative filters this rule's own matches, and its excluded event must use the tracked value as a receiver or narrow a producing event — an argument-shaped call such as `sanitize($VALUE)` does not yet anchor a structural exclusion. A sanitizer clause changes the rule's taint semantics wherever the flow goes, and handles argument-shaped safety APIs naturally.

Negative metavariables need special care. Every metavariable used by a negative pattern must be introduced by a positive pattern in a producing position—defined, as by a factory result assignment or a parameter declaration, not merely observed at a use site. The detailed rules and correct builder examples are in [Negative clauses and metavariable domains](rule-pattern-clauses.md#negative-clauses-and-metavariable-domains).

## Put ordinary data movement in models

If an external method returns a transformed copy of an argument:

```text
external normalize: arg(0) -> result
```

write a [pass-through model](passthrough-models.md). If the method invokes a mapper and returns the mapper result:

```text
container value -> mapper argument
mapper result -> returned container
```

write a [dataflow approximation](dataflow-models.md).

A rule propagator is appropriate only when the movement has meaning inside that specific security rule, such as changing label `RAW` into label `PARSED`. It is not a replacement for a general library model.

## Reusable rule design

Good reusable components have one role:

- a framework source library defines one trust boundary family;
- a vulnerability sink library defines one dangerous-operation family;
- the outer join owns the user-facing message, severity, CWE, and remediation.

Prefer tags for intentionally open families. A component declares its family
membership:

```yaml
# Java/JVM library component
rules:
  - id: servlet-parameter-source
    languages: [java]
    options:
      lib: true
    tags: [servlet-untrusted-data-source]
    pattern: $UNTRUSTED = $REQUEST.getParameter(...)
```

A join that references `tag: servlet-untrusted-data-source` picks up every
active rule carrying the tag, so adding a new tagged rule extends every join
that consumes the family. The ruleset names families by role: source families
such as `servlet-untrusted-data-source` and `spring-untrusted-data-source`,
and sink families such as `sqli-sink`, `ssrf-sink`, `path-traversal-sink`, and
`format-string-sink`. Use an explicit `rule:` reference when automatic
expansion would be unsafe. A tag with no active member fails rule loading.

Keep exclusions with the component that owns them. A safe servlet annotation belongs in the servlet source component; an SQL parameterization sanitizer belongs in the SQL sink component.

## Real-case recipes

### Factory or builder with a safe configuration

Produce the builder identity in a positive context, match the terminal
operation, and subtract the proven-safe configuration using the same produced
identity. The canonical rule and its full test matrix live in
[`pattern-not-inside`](rule-pattern-clauses.md#pattern-not-inside). The
essential negatives: the safe configuration on the same object, on a
different object, and after the terminal call.

### Several dangerous overloads

Give each overload its own complete sink alternative with its own
`focus-metavariable` on the dangerous position; do not merge overloads into
one unfocused call pattern. The canonical alternatives example lives in
[`pattern-either`](rule-pattern-clauses.md#pattern-either-any-complete-alternative-may-hold).
Test each overload positively, and give each one a negative where a tainted
value reaches a harmless argument.

### Fluent or stateful API

Use a pass-through model for values stored in and later read from a builder. Every movement through an external call must be explicit because pass-through actions do not chain within one call.

Use a rule-level propagator only when the stored state exists solely for that vulnerability's label state machine.

### Callback or asynchronous API

A rule pattern can locate a callback registration, but it cannot execute the callback. Use a dataflow approximation to expose:

- wrapper value to callback argument;
- callback result to returned wrapper;
- values from both sides of combining operations;
- runnable or consumer side effects.

### Structural finding and flow finding

Give a dangerous configuration and a source-to-sink flow separate rule IDs. They have different evidence, messages, severities, and negative matrices even when they share a CWE.

## Validation workflow

The full `opentaint test` command reference lives in the
[Usage Guide](usage.md); this section shows only the authoring loop.

Compile a project model once, then iterate on the smallest relevant rule and sample set:

```bash
opentaint compile rules/test \
  -o .opentaint/rule-doc-validation/project

opentaint test rule run .opentaint/rule-doc-validation/project \
  --ruleset rules/ruleset \
  --rule-id 'java/security/example.yaml:example-rule' \
  -o .opentaint/rule-doc-validation/result
```

Inspect both artifacts:

- `test-result.json` tells you which expectations passed, failed, or were skipped;
- `test-results.sarif` shows the matched location and actual code flow.

When a source or sink is missing, run reachability diagnostics with the same rules and models:

```bash
opentaint test rule reachability \
  'java/security/example.yaml:example-rule' \
  --project-model .opentaint/rule-doc-validation/project \
  --ruleset rules/ruleset \
  -o .opentaint/rule-doc-validation/reachability.sarif
```

For external calls, also run `opentaint scan` with `--track-external-methods` and inspect `dropped-external-methods.yaml`; the flag is available on `scan` only, not on the `test rule` commands.

## Minimum review matrix

- Every `pattern-either` branch has a positive.
- Every source and sink overload has a positive.
- Every sanitizer has a negative and an unsafe near-miss.
- Every `pattern-not` or `pattern-not-inside` has an excluded case and a nearby retained case.
- Shared metavariables identify the same logical value in every clause.
- Negative metavariables are introduced by positive producer patterns.
- Direct, interprocedural, field, alias, and modeled-library flows are covered where relevant.
- Each join fan-in and fan-out edge is covered.
- `$VAR*` rules cover base and nested-field behavior separately.
- Messages, severity, CWE, description, and remediation describe the same evidence.
- The final result is verified in JSON and SARIF, not only by successful YAML loading.
