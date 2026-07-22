# create-rule — Go

Language reference for authoring Go source/sink library rules, keyed to the body's steps. Bind every tainted value to `$UNTRUSTED` so the joins connect on one name.

Worked, repo-faithful examples for every vuln class live in `references/go-semgrep-examples.md` — read it before authoring and copy the closest shape.

## Workflow

### 1. Check existing coverage

Built-in Go rules live under `go/lib/` (source and sink library rules) and `go/security/` (the joins and structural rules); mirror that layout for any custom rule you add — never the `java/` tree. Rule ids carry no `go-` prefix.

### 2. Author the library rules

Go lib rules are `severity: NOTE` with `options: {lib: true}` and `mode: taint`, carry `languages: [go]`, use the typed-receiver pattern syntax (`($R : *http.Request)` — the `*` only where the API is pointer-receiver), and bind the tainted value as `$UNTRUSTED`.

Scope every rule to its package by wrapping the patterns in a `patterns:` block led by a `pattern-inside: import "pkg"` guard — the built-in multi-pattern lib rules all do this, so a bare call like `os.Getenv` or `exec.Command` can't fire in an unrelated file. A single-statement rule can instead inline the `import "pkg"` line into a bare `pattern: |`, as `go/lib/http-sources-requesturi.yaml` does.

Custom source library rule (`.opentaint/rules/go/lib/my-source.yaml`):

```yaml
rules:
  - id: mylib-source
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted user input originates here
    mode: taint
    pattern-sources:
      - label: "$UNTRUSTED"
        patterns:
          - pattern-inside: |
              import mylib "github.com/acme/mylib"
              ...
          - pattern-either:
              - pattern: "($C : *mylib.Ctx).UserInput($K)"
```

Custom sink library rule (`.opentaint/rules/go/lib/my-sink.yaml`) — `focus-metavariable` points at the tainted argument:

```yaml
rules:
  - id: mylib-sink
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted data reaches a dangerous operation
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import mylib "github.com/acme/mylib"
              ...
          - pattern-either:
              - pattern: "($E : *mylib.Engine).Render($TPL, ...)"
          - focus-metavariable: $TPL
```

### 3. Write the test joins

**Go deviates here.** The Go test harness has no generic taint marker and no throwaway test-rules tree: a sample wires a real source into a real sink, so what the samples run against is the *real* security join, written once under `.opentaint/rules/go/security/` and named by the `rule-test.yaml` manifest as `go/security/<file>.yaml#<id>`. There is nothing test-only to write and nothing to keep out of the scanned rules tree.

```yaml
rules:
  - id: my-ssti-lib-ext
    languages: [go]
    severity: ERROR
    message: Untrusted input reaches a template engine (SSTI)
    metadata:
      cwe: CWE-1336
      short-description: Server-side template injection
    mode: join
    join:
      refs:
        - rule: go/lib/http-sources.yaml#http-sources
          as: src
        - rule: go/lib/my-ssti-sink.yaml#mylib-sink
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
```

For a purely structural rule — a dangerous primitive used at all, such as weak hash or weak random — use `mode: search` + `pattern-either` instead of a join (see the catalog); it needs no source side.

### 4. Test until success

There is one shared Go test module and one compiled model, not per-unit `sinks/`/`sources/` sides, so the command names them directly:

```bash
opentaint test rule run .opentaint/test-compiled/go \
  -o .opentaint/test-results/go \
  --ruleset .opentaint/rules \
  --passthrough-models .opentaint/pass-through
```

`test rule run` auto-loads the built-in rules, so pass only your own ruleset — a literal `builtin` here would be treated as a path. There is no `--java-models` for Go. Read the result with the bundled `check-test-result.py`, passing `go` as the unit.

Pattern operators for each verdict:

- `falseNegative` → broaden `pattern-either`, check the receiver type (and its `*`), and confirm `$UNTRUSTED` matches across the lib rules and the join's `on:`
- `falsePositive` → narrow with `pattern-not`, `pattern-not-inside`, `pattern-sanitizers`, or `metavariable-regex`, or focus a different sink argument. Inspect the flow that fired with `opentaint summary .opentaint/test-results/go/test-results.sarif --show-findings`
- `skipped` → the manifest entry's rule-id or sample full name is wrong; fix the `rule-test.yaml` entry

### 5. Escalate when a positive won't converge

Unchanged, with one Go difference: a dropped library function on the failing sample's path routes to a Go **passThrough** (there is no dataflow approximation), and a re-dispatch applies it with `--passthrough-models`.

## Constraints

- Lib rules (source and sink) are `severity: NOTE`, `options: {lib: true}`, `mode: taint`; `severity: ERROR` belongs to the security rules — joins and structural `mode: search` rules alike
- Security joins (`mode: join`) must carry `metadata.cwe` and `metadata.short-description`
- Rule ids are globally unique and carry no language prefix; a custom join id must not collide with a built-in (`sql-injection`, `ssrf`, …) or it is dropped silently
- Custom Go rules go under `.opentaint/rules/go/{lib,security}/`, never the `java/` tree

## Gotchas

- The typed-receiver form needs the pointer where the API is pointer-receiver (`($R : *http.Request)`); a value receiver omits the `*`
- Without the `pattern-inside: import "pkg"` guard a bare call pattern fires in unrelated files
- A wrong argument position in a sink focuses the wrong parameter — point `focus-metavariable` at the tainted one
