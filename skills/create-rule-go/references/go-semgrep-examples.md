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
- Security rules: `mode: join`, `metadata.cwe` + `short-description`, `refs:`/`on:` wiring
  `src.$UNTRUSTED -> sink.$UNTRUSTED`.
- Structural rules (no dataflow): `mode: search` + `pattern-either` — flags a call site
  regardless of taint (weak crypto/hash/random).

## Source lib rule — HTTP request data (`go/lib/http-sources.yaml`)

```yaml
rules:
  - id: go-http-sources
    options: {lib: true}
    languages: [go]
    severity: NOTE
    message: Untrusted user input originates here
    mode: taint
    pattern-sources:
      - label: "$UNTRUSTED"
        pattern-either:
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
`$UNTRUSTED`. Real file lists many more request accessors and framework variants (beego);
add the project-used ones, don't enumerate the whole API.

## Sink lib rule — SQL execution (`go/lib/go-sql-sinks.yaml`)

```yaml
rules:
  - id: go-sql-sinks
    options: {lib: true}
    languages: [go]
    severity: ERROR
    message: SQL query execution sink
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern: "($DB : *sql.DB).Query($SQL, ...)"
          - focus-metavariable: $SQL
      - patterns:
          - pattern: "($DB : *sql.DB).QueryContext($CTX, $SQL, ...)"
          - focus-metavariable: $SQL
      - patterns:
          - pattern: "($DB : *sql.DB).Exec($SQL, ...)"
          - focus-metavariable: $SQL
```

Notes: each sink wraps `pattern` + `focus-metavariable: $SQL` in a `patterns:` block so the
focused argument is the tainted one. The receiver type `*sql.DB` pins the method.

## Sink lib rule — OS command execution (`go/lib/go-cmdi-sinks.yaml`)

```yaml
rules:
  - id: go-cmdi-sinks
    options: {lib: true}
    languages: [go]
    severity: ERROR
    message: OS command execution sink
    mode: taint
    pattern-sinks:
      - pattern-either:
          - pattern: exec.Command($NAME, ...)
          - pattern: exec.CommandContext($CTX, $NAME, ...)
          - pattern: syscall.Exec($NAME, ...)
          - pattern: "($C : *exec.Cmd).Run()"
          - pattern: "($C : *exec.Cmd).CombinedOutput()"
```

Notes: a `pattern-either` of sink shapes works when each branch's tainted position is the
first/obvious argument; use a per-branch `focus-metavariable:` (as in the SQL sink) when the
tainted argument isn't first.

## Sink lib rule — filesystem path (`go/lib/go-path-sinks.yaml`)

```yaml
rules:
  - id: go-path-sinks
    options: {lib: true}
    languages: [go]
    severity: ERROR
    message: Filesystem path sink
    mode: taint
    pattern-sinks:
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
  - id: go-sql-injection
    languages: [go]
    severity: ERROR
    message: Tainted user input flows into SQL query (SQL injection)
    metadata:
      cwe: CWE-89
      short-description: SQL injection
    mode: join
    join:
      refs:
        - rule: go/lib/http-sources.yaml#go-http-sources
          as: src
        - rule: go/lib/http-sources-requesturi.yaml#go-http-sources-requesturi
          as: extra_requesturi
        - rule: go/lib/go-sql-sinks.yaml#go-sql-sinks
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
        - 'extra_requesturi.$UNTRUSTED -> sink.$UNTRUSTED'
```

## Security join — others (same shape, swap the sink ref + CWE)

| Class | id | CWE | sink ref |
|---|---|---|---|
| Command injection | `go-command-injection` | CWE-78 | `go/lib/go-cmdi-sinks.yaml#go-cmdi-sinks` |
| Path traversal | `go-path-traversal` | CWE-22 | `go/lib/go-path-sinks.yaml#go-path-sinks` |
| SSRF | `go-ssrf` | CWE-918 | `go/lib/go-ssrf-sinks.yaml#go-ssrf-sinks` |
| Reflected XSS | `go-reflected-xss` | CWE-79 | `go/lib/go-xss-sinks.yaml#go-xss-sinks` |
| SSTI | `go-ssti` | CWE-1336 | `go/lib/go-ssti-sinks.yaml#go-ssti-sinks` |

Each is one `src.$UNTRUSTED -> sink.$UNTRUSTED` join refing `go-http-sources` (plus the
extra header/requesturi source variants where the class needs them).

## Structural rule — weak hash / weak random (`mode: search`, no dataflow)

```yaml
rules:
  - id: go-weak-hash-cwe-328
    languages: [go]
    severity: ERROR
    message: Use of a weak or broken cryptographic hash
    metadata:
      cwe: CWE-328
      short-description: Weak cryptographic hash
    mode: search
    pattern-either:
      - pattern: md5.New(...)
      - pattern: md5.Sum(...)
      - pattern: sha1.New(...)
      - pattern: sha1.Sum(...)
```

```yaml
rules:
  - id: go-weak-random-cwe-330
    languages: [go]
    severity: ERROR
    message: Use of a weak (non-cryptographic) random number generator
    metadata:
      cwe: CWE-330
      short-description: Insecure randomness
    mode: search
    pattern-either:
      - pattern: rand.Intn(...)
      - pattern: rand.Int63()
      - pattern: rand.Float64()
```

Notes: `mode: search` flags a call site structurally — no source/sink join, no taint flow.
Use it for "dangerous primitive used at all" rules; use `mode: join` when the finding
requires untrusted data to reach the sink.
