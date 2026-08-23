# Go Semgrep rule examples

A catalog of real, working Go rules trimmed from `rules/ruleset/go/`. Each entry shows the
shape to copy when authoring a new Go rule. Use these as the concrete starting point instead
of inventing patterns. Produced rules stay comment-free — the prose here is reference only.

## Go pattern syntax cheat-sheet

- Typed receiver / variable binding: `($R : *http.Request)` — binds `$R` to a value of the
  given Go type (note the pointer `*`). Use it to pin a method/field to its receiver type.
- Metavariables: `$UNTRUSTED`, `$SQL`, `$NAME`, `$P`, `$K`, … — `$UPPER` names.
- Method / field access: `$R.Method($A)`, `$R.Field`, index `$R.Header[$K]`.
- Variadic tail: `...` matches the rest of the args, e.g. `exec.Command($NAME, ...)`.
- Lib source rules: `mode: taint`, `options: {lib: true}`, `pattern-sources` with
  `label: "$UNTRUSTED"`.
- Lib sink rules: `mode: taint`, `options: {lib: true}`, `pattern-sinks`; use
  `focus-metavariable:` to point at the tainted argument.
- Package guard: wrap the source/sink patterns in a `patterns:` block led by a
  `pattern-inside: import "pkg"` guard so bare calls don't fire in unrelated files — the
  built-in multi-pattern lib rules all do this; a single-statement rule can instead inline
  the `import "pkg"` line into a bare `pattern: |`.
- Security rules: `mode: join`, `metadata.cwe` + `short-description`, `refs:`/`on:` wiring
  `src.$UNTRUSTED -> sink.$UNTRUSTED`.
- Structural rules (no dataflow): `mode: search` + `pattern-either` — flags a call site
  regardless of taint (weak crypto/hash/random).

## Source lib rule — HTTP request data (`go/lib/http-sources.yaml`)

```yaml
rules:
  - id: http-sources
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted user input originates here
    mode: taint
    pattern-sources:
      - label: "$UNTRUSTED"
        patterns:
          - pattern-inside: |
              import "net/http"
              import "os"
              ...
          - pattern-either:
              - pattern: "($R : *http.Request).FormValue($K)"
              - pattern: "($R : *http.Request).PostFormValue($K)"
              - pattern: "($R : *http.Request).Cookie($K)"
              - pattern: $R.URL.Query().Get($K)
              - pattern: $R.URL.Path
              - pattern: $R.Header.Get($K)
              - pattern: $R.Body
              - pattern: os.Getenv($K)
              - pattern: os.Args
```

Notes: lib sources are `severity: NOTE` and bind the tainted value as the labelled
`$UNTRUSTED`. The `patterns:` block scopes matching to the imported packages via
`pattern-inside: import "..."`. Real file lists many more request accessors and framework
variants (beego); add the project-used ones, don't enumerate the whole API.

## Sink lib rule — SQL execution (`go/lib/sql-sinks.yaml`)

```yaml
rules:
  - id: sql-sinks
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted data reaches a SQL execution API
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import "database/sql"
              ...
          - pattern-either:
              - pattern: "($DB : *sql.DB).Query($SQL, ...)"
              - pattern: "($DB : *sql.DB).QueryContext($CTX, $SQL, ...)"
              - pattern: "($DB : *sql.DB).Exec($SQL, ...)"
          - focus-metavariable: $SQL
```

Notes: the `patterns:` block pairs a `pattern-inside: import "database/sql"` guard with a
`pattern-either` of the call shapes, then `focus-metavariable: $SQL` selects the tainted
argument. The receiver type `*sql.DB` pins the method. Lib sinks are `severity: NOTE`.

## Sink lib rule — OS command execution (`go/lib/cmdi-sinks.yaml`)

```yaml
rules:
  - id: cmdi-sinks
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted data reaches an OS command execution API
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import "os/exec"
              import "os"
              import "syscall"
              ...
          - pattern-either:
              - pattern: exec.Command($NAME, ...)
              - pattern: exec.CommandContext($CTX, $NAME, ...)
              - pattern: syscall.Exec($NAME, ...)
          - focus-metavariable: $NAME
      - patterns:
          - pattern-inside: |
              import "os/exec"
              ...
          - pattern-either:
              - pattern: "exec.Command(\"$NAME\", ..., $UNTRUSTED, ...)"
          - metavariable-regex:
              metavariable: $NAME
              regex: sh
          - focus-metavariable: $UNTRUSTED
```

Notes: each sink shape is a `patterns:` block guarded by `pattern-inside: import "os/exec"`.
The first focuses the command name (`$NAME`); the second matches a shell interpreter invoked
with a literal name and narrows it with `metavariable-regex` before focusing the tainted
argument (`$UNTRUSTED`). Point `focus-metavariable:` at the tainted position when it isn't
first.

## Sink lib rule — filesystem path (`go/lib/path-sinks.yaml`)

```yaml
rules:
  - id: path-sinks
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted data reaches a filesystem path API
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import "os"
              import "io/ioutil"
              import "net/http"
              ...
          - pattern-either:
              - pattern: os.Open($P)
              - pattern: os.OpenFile($P, ...)
              - pattern: os.ReadFile($P)
              - pattern: os.WriteFile($P, ...)
              - pattern: ioutil.ReadFile($P)
              - pattern: http.ServeFile($W, $R, $P)
```

## Security join — SQL injection (`go/security/sql-injection.yaml`)

```yaml
rules:
  - id: sql-injection
    languages: [go]
    severity: ERROR
    message: Tainted user input flows into SQL query (SQL injection)
    metadata:
      cwe: CWE-89
      short-description: SQL injection
    mode: join
    join:
      refs:
        - rule: go/lib/http-sources.yaml#http-sources
          as: src
        - rule: go/lib/http-sources-requesturi.yaml#http-sources-requesturi
          as: extra_requesturi
        - rule: go/lib/sql-sinks.yaml#sql-sinks
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
        - 'extra_requesturi.$UNTRUSTED -> sink.$UNTRUSTED'
```

## Security join — others (same shape, swap the sink ref + CWE)

| Class | id | CWE | sink ref |
|---|---|---|---|
| Command injection | `command-injection` | CWE-78 | `go/lib/cmdi-sinks.yaml#cmdi-sinks` |
| Path traversal | `path-traversal` | CWE-22 | `go/lib/path-sinks.yaml#path-sinks` |
| SSRF | `ssrf` | CWE-918 | `go/lib/ssrf-sinks.yaml#ssrf-sinks` |
| Reflected XSS | `reflected-xss` | CWE-79 | `go/lib/xss-sinks.yaml#xss-sinks` |
| SSTI | `ssti` | CWE-1336 | `go/lib/ssti-sinks.yaml#ssti-sinks` |

Each is one `src.$UNTRUSTED -> sink.$UNTRUSTED` join refing `http-sources` (plus the
extra header/requesturi source variants where the class needs them).

## Structural rule — weak hash / weak random (`mode: search`, no dataflow)

```yaml
rules:
  - id: weak-hash-cwe-328
    languages: [go]
    severity: ERROR
    message: Use of a weak or broken cryptographic hash
    metadata:
      cwe: CWE-328
      short-description: Weak cryptographic hash
    mode: search
    patterns:
      - pattern-inside: |
          import "crypto/md5"
          import "crypto/sha1"
          ...
      - pattern-either:
          - pattern: md5.New(...)
          - pattern: md5.Sum(...)
          - pattern: sha1.New(...)
          - pattern: sha1.Sum(...)
```

```yaml
rules:
  - id: weak-random-cwe-330
    languages: [go]
    severity: ERROR
    message: Use of a weak (non-cryptographic) random number generator
    metadata:
      cwe: CWE-330
      short-description: Insecure randomness
    mode: search
    patterns:
      - pattern-inside: |
          import "math/rand"
          ...
      - pattern-either:
          - pattern: rand.Intn(...)
          - pattern: rand.Int63()
          - pattern: rand.Float64()
```

Notes: `mode: search` flags a call site structurally — no source/sink join, no taint flow.
The structural rule still guards on `pattern-inside: import "..."` so it only fires for the
intended package. Use it for "dangerous primitive used at all" rules; use `mode: join` when
the finding requires untrusted data to reach the sink.
