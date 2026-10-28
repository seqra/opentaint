# create-test-project — Go rule test project

Language reference for a `rule-source` / `rule-sink` type, keyed to the body's steps. The fixed counterpart is always the generic `util` marker, never a real source/sink — so the sample exercises only the rule under test.

## Workflow

### 1. Scaffold the project

`opentaint test rule init` scaffolds Java only, so write the side you are handed by hand: `rule-source` → `.opentaint/test-projects/<name>/sources`, `rule-sink` → `.opentaint/test-projects/<name>/sinks`. Each side is a Go module with `module test` and the app's Go version, the generic marker in `util/taint.go`, and the generic marker lib rules in its `test-rules/`. You are handed one side per invocation, build only that side. Require each module from the unit's `dependencies` at its exact version from the app's `go.mod` verbatim — including pseudo-versions and local `replace` directives — not a guess.

`util/taint.go`:

```go
package util

func Source() string { return "" }
func Sink(any) {}
```

`test-rules/go/lib/test/generic-source.yaml`:

```yaml
rules:
  - id: generic-taint-source
    options:
      lib: true
    severity: NOTE
    message: Generic untrusted-data marker (util.Source)
    metadata:
      short-description: Generic test taint source
    languages:
      - go
    mode: taint
    pattern-sources:
      - label: $UNTRUSTED
        patterns:
          - pattern-inside: |
              import "test/util"
              ...
          - pattern: util.Source()
```

`test-rules/go/lib/test/generic-sink.yaml`:

```yaml
rules:
  - id: generic-taint-sink
    options:
      lib: true
    severity: NOTE
    message: Generic dangerous-operation marker (util.Sink)
    metadata:
      short-description: Generic test taint sink
    languages:
      - go
    mode: taint
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import "test/util"
              ...
          - pattern: util.Sink($VALUE)
          - focus-metavariable: $VALUE
```

### 2. Write the samples

Each unit entry already records the callable's `signature` (`args:<count>`, the receiver excluded) — the callable the sample must match. To shape a faithful call, look at how the callable is used in the project. Write the samples as ordinary `.go` files in `package test` at the side's module root:

- positive sample — a minimal flow that must flag, with the real sink/source signature and no extra hops:
  - **sink** under test → `t := util.Source(); pkg.TheSink(t)` — convert the marker string to the sink argument's type when it differs
  - **source** under test → `v := pkg.TheSource(); util.Sink(v)` — `Sink` takes `any`, so any type fits
  One positive per new sink (in `sinks/`) and per new source (in `sources/`)
- negative sample — the safe (sanitized or parameterized) variant of the same, which must not flag. Keep it realistic — prefer the library's real sanitizer or validation call when the source makes one visible — not stripped to constants

The samples are plain functions; their verdicts live in a `rule-test.yaml` (below), not on the function.

```go
package test

import (
	"database/sql"

	"test/util"
)

// sinks/ side — a SQL sink fed by the generic marker source
func Vulnerable(db *sql.DB) {
	input := util.Source()
	db.Query("SELECT * FROM users WHERE id = " + input)
}

func Safe(db *sql.DB) {
	input := util.Source()
	db.Query("SELECT * FROM users WHERE id = ?", input)
}
```

Register the verdicts — write `rule-test.yaml` at the side's module root (`sinks/rule-test.yaml` or `sources/rule-test.yaml`), under the side's test-join `rule-id`: `go/security/<name>-sinks.yaml#<name>-sinks` for sink samples, `<name>-sources` for source samples (`<name>` = the package-kebab). The `<path>#<id>` is the rule path relative to the test-rules root plus its short id, not the full `--rule-id` used by `opentaint scan`. List each sample by its Go function name, `test.<Function>`:

```yaml
tests:
  - rule-id: go/security/sql-sinks.yaml#sql-sinks
    positive:
      - test.Vulnerable
    negative:
      - test.Safe
```

A method sample is named with its receiver, `(*test.<Type>).<Method>` or `(test.<Type>).<Method>`.

The test join is the side's detector: it combines the generic marker with the unit's selected lib rules, never a copy of a real source or sink. Write it in `test-rules/go/security/<name>-sinks.yaml` or `<name>-sources.yaml`:

- `sinks` side → `<name>-sinks`: ref the generic source + every sink `rule_id` selected for the unit, wiring `src.$UNTRUSTED -> <sink>.$UNTRUSTED` for each
- `sources` side → `<name>-sources`: ref every source `rule_id` selected for the unit + the generic sink, wiring `<source>.$UNTRUSTED -> sink.$VALUE` for each

```yaml
rules:
  - id: sql-sinks
    severity: ERROR
    message: Tainted value reaches a sink under test
    metadata:
      cwe:
        - CWE-000
      short-description: test join for the package's sinks
    languages:
      - go
    mode: join
    join:
      refs:
        - rule: go/lib/test/generic-source.yaml#generic-taint-source
          as: src
        - rule: go/lib/<area>/my-new-sink.yaml#my-new-sink
          as: sink
      on:
        - 'src.$UNTRUSTED -> sink.$UNTRUSTED'
```

The marker rules resolve from the side's `test-rules` root, a selected lib ref resolves from either the built-in ruleset or `.opentaint/rules`, both loaded by `test rule run`. Metavariable names must match across `refs` and `on`.

## Constraints

- Write ordinary `.go` files, not `_test.go` files — the Go project loader skips test files
- Diagnose a compile failure with `go build ./...` in the side's module
- For Go, `opentaint compile` writes a project model that points to the sample sources, not a frozen build — keep the samples fixed after compiling
- Add `--go-models <model-module>` to `test rule run` only when the flow needs an existing Go model; never add a model to force a rule to pass
