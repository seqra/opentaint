# AST patterns

An AST pattern is the source-shaped expression inside `pattern:`,
`pattern-inside:`, `pattern-not:`, and the taint clause lists. It matches
program structure and binds values; it is not a text or regular-expression
search. It also has no inherent source or sink meaning: the surrounding search,
taint, or join clause decides how the selected value is used. OpenTaint still
implements the pattern relationship with rule-private taint marks: producing
occurrences assign metavariable marks, and later occurrences expect them.

The surrounding YAML language is shared by Java/JVM and Go. The AST pattern itself is written in the target language selected by `languages`.

## The common model

Across languages, an AST pattern can describe:

- a call or constructor;
- the value returned by a call;
- a receiver and its method call;
- arguments at exact or partial positions;
- an ordered sequence of events;
- a method/function context;
- language-specific declarations, types, imports, annotations, or composite values.

Metavariables connect these structures. Ellipses leave selected structure unconstrained.

```yaml
pattern: $RESULT = $CLIENT.fetch($URL, ...)
```

This pattern binds three facts:

```text
$RESULT  the call result
$CLIENT  the receiver
$URL     the first argument
```

If the same name appears again in the same formula, it refers to the same logical value.

## Metavariables

An ordinary metavariable begins with `$`:

```yaml
pattern: dangerous($VALUE)
```

Repeated names assert identity:

```yaml
pattern: $RESULT = replace($RESULT, $OLD, $NEW)
```

This does not mean “any assignment and any `replace` call.” The assignment destination and the first call argument must be represented by the same `$RESULT` fact.

Use distinct names when positions are independent:

```yaml
pattern: $OUTPUT = transform($INPUT)
```

Use `$_` when the value's identity is irrelevant:

```yaml
pattern: $_.close()
```

### Producer and observer positions

It is useful to distinguish how a metavariable enters a formula.

A producer occurrence defines a value and provides a position where OpenTaint
can assign the metavariable's rule-private mark:

```yaml
pattern: $CLIENT = Client.builder()
```

```yaml
pattern: $RESULT = decode($INPUT)
```

A declaration can also produce a value in an enclosing context:

```java
void $METHOD(..., Request $REQUEST, ...) { ... }
```

An observer occurrence finds a value at a use site. When the metavariable was
produced earlier in the formula, this occurrence expects the corresponding
mark:

```yaml
pattern: consume($VALUE)
```

```yaml
pattern: $CLIENT.connect($URL)
```

Both kinds participate in metavariable matching. The producer/observer
distinction becomes important for negative clauses: a negative metavariable
needs a finite positively produced mark domain. See [Negative clauses and
metavariable domains](rule-pattern-clauses.md#negative-clauses-and-metavariable-domains).

## Dataflow normal form

Compact AST patterns can contain nested calls and call chains. Internally,
OpenTaint desugars such a pattern into a sequence of single-event patterns,
introducing a metavariable for every hidden intermediate result. That
desugared sequence is the pattern's dataflow normal form.

Two properties define a normal form:

- It is itself a valid pattern. Every normal form below can be pasted into a
  `pattern:` clause and loads and matches like its compact original.
- Every ordering boundary carries an explicit `...`. The ellipsis is part of
  the normal form: it states that unrelated events may occur between
  production and consumption. What the pattern enforces is the order of the
  events; write the `...` explicitly so the pattern says what it matches
  instead of relying on that implicit permissiveness.

Use the explicit form when you need to name, constrain, focus, or extend an intermediate value. Keep the compact form when the nesting is already the clearest expression of the case.

Normal form exposes the pattern's mark movement. A producing occurrence assigns
a rule-private metavariable mark; a later occurrence with the same name expects
that mark. This is distinct from declaring a vulnerability source or sink:
`mode: taint` and `mode: join` add those higher-level mark boundaries.

### Patterns already in normal form

A pattern is already in normal form when it contains a single event and hides
no intermediate call result — there is nothing left to name and no ordering to
make explicit:

```yaml
pattern: consume($VALUE)
```

```yaml
pattern: $OUTPUT = transform($INPUT)
```

```yaml
pattern: return $VALUE
```

Their normal form is the pattern itself.

### A call used as an argument

Compact Java/JVM pattern:

```yaml
pattern: consume(produce())
```

Explicit dataflow normal form:

```yaml
pattern: |
  $PRODUCED = produce();
  ...
  consume($PRODUCED);
```

Compact Go pattern:

```yaml
pattern: consume(produce())
```

Explicit Go normal form:

```yaml
pattern: |
  $PRODUCED := produce()
  ...
  consume($PRODUCED)
```

The `...` is important: it keeps the production and consumption events
ordered while allowing other method events between them. Reusing `$PRODUCED`
states that the first event marks its result and the later event expects that
mark on its argument. Neither method is a vulnerability source or sink unless
a surrounding taint or join role makes it one.

### Multiple nested calls

Compact pattern:

```yaml
pattern: consume(parse(read()))
```

Java/JVM normal form:

```yaml
pattern: |
  $READ_RESULT = read();
  ...
  $PARSED = parse($READ_RESULT);
  ...
  consume($PARSED);
```

Go normal form:

```yaml
pattern: |
  $READ_RESULT := read()
  ...
  $PARSED := parse($READ_RESULT)
  ...
  consume($PARSED)
```

Every intermediate value has a name, and every required order boundary has an explicit ellipsis.

### Nested call among other arguments

Compact pattern:

```yaml
pattern: send($CONTEXT, normalize($INPUT), $OPTIONS)
```

Java/JVM normal form:

```yaml
pattern: |
  $NORMALIZED = normalize($INPUT);
  ...
  send($CONTEXT, $NORMALIZED, $OPTIONS);
```

Go normal form:

```yaml
pattern: |
  $NORMALIZED := normalize($INPUT)
  ...
  send($CONTEXT, $NORMALIZED, $OPTIONS)
```

The exact outer argument positions remain constrained.

### Receiver call chain

Compact Java/JVM pattern:

```yaml
pattern: $BASE.first($A).second($B)
```

Explicit normal form:

```yaml
pattern: |
  $STEP = $BASE.first($A);
  ...
  $STEP.second($B);
```

A longer chain names every result:

```yaml
pattern: |
  $STEP_1 = $BASE.first($A);
  ...
  $STEP_2 = $STEP_1.second($B);
  ...
  $STEP_2.third($C);
```

The same value relationship can be written in Go with `:=` and Go selector syntax:

```yaml
pattern: |
  $STEP_1 := $BASE.First($A)
  ...
  $STEP_2 := $STEP_1.Second($B)
  ...
  $STEP_2.Third($C)
```

### Constructor followed by a call

Compact Java/JVM pattern:

```yaml
pattern: new URL($VALUE).openConnection()
```

Explicit normal form:

```yaml
pattern: |
  $URL = new URL($VALUE);
  ...
  $URL.openConnection();
```

This form is easier to extend with a type constraint, a negative clause, or a
focused value when the pattern is later placed in a taint role.

## Ellipsis

`...` has different meanings in different AST positions. Treat each position as a separate operator.

### Between statements or events

```yaml
pattern: |
  $INPUT = produce();
  ...
  consume($INPUT);
```

This means:

1. match the production event and bind `$INPUT`;
2. allow zero or more intervening method events;
3. later match the consumption event with the same `$INPUT`.

The events remain ordered. This is not arbitrary source-text matching: expressions that do not become relevant analysis events may not create a separate step.

The pattern above matches the first method and does not match the second:

```java
// Matches: production, other events, then consumption of the same value.
void ok() {
    String input = produce();
    log("received");
    consume(input);
}

// Does not match: consumption happens before production.
void reversedOrder() {
    String cached = null;
    consume(cached);
    cached = produce();
}
```

A leading ellipsis allows earlier events:

```yaml
pattern: |
  ...
  consume($INPUT)
```

A trailing ellipsis allows later events and is common in enclosing contexts:

```yaml
pattern-inside: |
  $CLIENT = Client.builder();
  ...
```

### In an argument list

An argument-list ellipsis makes part of the call unconstrained:

```yaml
pattern: execute($COMMAND, ...)
```

`$COMMAND` is argument zero; remaining arguments are unrestricted:

```java
execute(cmd);            // matches: $COMMAND = cmd, ellipsis covers nothing
execute(cmd, env, dir);  // matches: $COMMAND = cmd, ellipsis covers the rest
execute();               // does not match: argument zero is required
```

An ellipsis before a metavariable means the metavariable may occur at a later argument position:

```yaml
pattern: exec.Command("sh", ..., $UNTRUSTED, ...)
```

Normal positional reading:

```text
argument 0 is the literal "sh"
one later argument is $UNTRUSTED
all other arguments are unrestricted
```

```go
exec.Command("sh", "-c", script)   // matches: $UNTRUSTED can bind "-c" or script
exec.Command("sh")                 // does not match: no later argument exists
exec.Command("bash", "-c", script) // does not match: argument 0 is not "sh"
```

Current Java and Go conversion supports one constrained any-position argument after the first argument ellipsis. This is supported:

```yaml
pattern: call($FIRST, ..., $VALUE, ...)
```

This is not supported because it asks for two independent unconstrained positions:

```yaml
pattern: call(..., $A, $B)
```

Use concrete positions or enumerate complete call shapes instead.

`"..."` is a string-literal wildcard, not an argument ellipsis:

```yaml
pattern: setPassword("...")
```

### In a method or function body

Java/JVM:

```yaml
pattern-inside: |
  $RETURN $METHOD(..., Request $REQUEST, ...) {
    ...
  }
```

Go:

```yaml
pattern-inside: |
  func $HANDLER($REQUEST $TYPE, ...) {
    ...
  }
```

The ellipses independently leave parameters and body events unconstrained.

For the Java/JVM form above:

```java
// Matches: a Request parameter exists at some position.
void handle(String id, Request request) { process(request); }

// Does not match: no parameter has the required Request type.
void handle(String id, String raw) { process(raw); }
```

### Java/JVM call-chain ellipsis

Java/JVM additionally supports:

```yaml
pattern: $BASE. ... .toString()
```

It expands to exactly two shapes — its own normal form:

```yaml
pattern-either:
  - pattern: $BASE.toString()
  - pattern: |
      $STEP = $BASE.$ANY_METHOD(...);
      ...
      $STEP.toString();
```

It matches zero or one intermediate invocation, not an arbitrary-length chain:

```java
base.toString();                     // matches: zero intermediate calls
base.normalize().toString();         // matches: one intermediate call
base.normalize().trim().toString();  // does not match: two intermediate calls
```

Spell out longer supported shapes explicitly.

Go does not currently provide this Java call-chain ellipsis form. Write the explicit selector-call sequence instead.

## Constraining types

Types prevent a familiar method name from matching unrelated APIs.

### Java/JVM

Typed receiver:

```yaml
pattern: (java.sql.Statement $STATEMENT).executeQuery($SQL)
```

Typed declaration:

```yaml
pattern: java.lang.String $VALUE = $REQUEST.getParameter(...)
```

Typed method context:

```yaml
pattern-inside: |
  $RETURN $METHOD(..., javax.servlet.http.HttpServletRequest $REQUEST, ...) {
    ...
  }
```

Use fully qualified types for public rules unless the enclosing pattern deliberately constrains imports or packages.

Parameterized and array types are supported in declaration and method-signature positions. Test raw, wildcard, parameterized, and array variants separately when the distinction matters.

### Go

Typed receiver:

```yaml
pattern: '($CLIENT : *http.Client).Get($URL)'
```

Typed value:

```yaml
pattern: 'util.Use(($VALUE : string))'
```

Function declaration context:

```yaml
pattern-inside: |
  func $HANDLER($REQUEST *http.Request, ...) {
    ...
  }
```

Go pointer and value receiver types are distinct constraints. Test the call-site form used by the supported API.

## Java/JVM AST-pattern specialization

Common supported Java/JVM shapes include:

```yaml
# Instance call
pattern: $CLIENT.send($VALUE, ...)

# Static call
pattern: java.lang.Runtime.getRuntime()

# Constructor
pattern: new java.io.File($PATH)

# Assignment result
pattern: $RESULT = parse($INPUT)

# Return
pattern: return $VALUE

# Annotation and method context
pattern-inside: |
  @$MAPPING(...)
  $RETURN $METHOD(...) {
    ...
  }

# Class declaration
pattern: class $ACTION implements java.security.PrivilegedAction { ... }
```

An upper-case or fully qualified static receiver is treated as a type. Prefer the fully qualified spelling when simple-name resolution could be ambiguous.

Pattern parsing is not proof that every Java construct can become an executable rule. Keep patterns centered on calls, constructors, declarations, returns, and values involved in those events.

## Go AST-pattern specialization

Common supported Go shapes include:

```yaml
# Package function
pattern: exec.Command($NAME, ...)

# Receiver method
pattern: '($CLIENT : *http.Client).Get($URL)'

# Short declaration
pattern: $RESULT := parser.Parse($INPUT)

# Assignment
pattern: $RESULT = parser.Parse($INPUT)

# Composite literal
pattern: 'tls.Config{InsecureSkipVerify: true, ...}'

# Pointer composite literal
pattern: '$CLIENT := &http.Client{...}'

# Deferred call
pattern: defer $FILE.Close()
```

`$X := call()`, `$X = call()`, and `var $X = call()` are distinct source shapes, but the rule conversion treats each as the same assignment event: a pattern written with any one of these spellings matches code written with any of them. Use the spelling that matches the idiomatic code you target — `:=` in most Go examples in these guides.

Imports can be required as enclosing context:

```yaml
patterns:
  - pattern-inside: |
      import "os/exec"
      ...
  - pattern: exec.Command($NAME, ...)
```

Alias-sensitive import example:

```yaml
patterns:
  - pattern-inside: |
      import command "os/exec"
      ...
  - pattern: command.Command($NAME, ...)
```

Multi-value assignments are not currently converted as one AST pattern: a shape such as `$A, $B := call()` fails conversion, for `:=` and `=` alike. Match the call itself or the single-result shape the API supports.

## AST-pattern review checklist

- The pattern uses the target language's syntax.
- Every repeated metavariable intentionally means the same value.
- Producer values are named when later clauses need a reliable domain.
- Nested calls and chains are understood through an explicit normal form with `...`.
- Every ellipsis is interpreted according to its AST position.
- Dangerous overloads have exact argument positions or separate alternatives.
- Types are as narrow as the supported API requires.
- Java-only call-chain ellipsis is not assumed to work in Go.
- A positive and a near-miss negative exercise each unique AST shape.
