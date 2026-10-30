# create-test-project — Go rule test project

Language reference for a `rule-source` / `rule-sink` type, keyed to the body's steps. The fixed counterpart is always the generic `taint` marker, never a real source/sink — so the sample exercises only the rule under test.

## Workflow

### 1. Scaffold the project

`rule-source` → `opentaint test rule init <project> --language go --sources-only`; `rule-sink` → `--sinks-only`. Each scaffolds that one sub-project under `.opentaint/test-projects/<name>` as a Go module with module path `test`, the `taint` package (the generic `taint.Source()` / `taint.Sink()`) and the generic marker lib rules in its `test-rules/`. You are handed one side per invocation, build only that side. Pass each module from the unit's `dependencies` as a `--dependency`, taking its exact version from the app's `go.mod` verbatim — including pseudo-versions — not a guess:

```bash
# source side
opentaint test rule init .opentaint/test-projects/<name> --language go --sources-only \
  --dependency github.com/gin-gonic/gin@v1.10.0
# sink side
opentaint test rule init .opentaint/test-projects/<name> --language go --sinks-only \
  --dependency github.com/jmoiron/sqlx@v1.4.0
```

When the app replaces a module with a local directory, add the same replacement with `go mod edit -replace <module>=<dir>`.

### 2. Write the samples

Each unit entry already records the callable's `signature` (`args:<count>`, the receiver excluded) — the callable the sample must match. To shape a faithful call, look at how the callable is used in the project. Write the samples as ordinary `.go` files in `package test` at the side's module root:

- positive sample — a minimal flow that must flag, with the real sink/source signature and no extra hops:
  - **sink** under test → `t := taint.Source(); pkg.TheSink(t)` — convert the marker string to the sink argument's type when it differs
  - **source** under test → `v := pkg.TheSource(); taint.Sink(v)` — `Sink` takes `any`, so any type fits
  One positive per new sink (in `sinks/`) and per new source (in `sources/`)
- negative sample — the safe (sanitized or parameterized) variant of the same, which must not flag. Keep it realistic — prefer the library's real sanitizer or validation call when the source makes one visible — not stripped to constants

The samples are plain functions; their verdicts live in a `rule-test.yaml` (below), not on the function.

```go
package test

import (
	"database/sql"

	"test/taint"
)

// sinks/ side — a SQL sink fed by the generic marker source
func Vulnerable(db *sql.DB) {
	input := taint.Source()
	db.Query("SELECT * FROM users WHERE id = " + input)
}

func Safe(db *sql.DB) {
	input := taint.Source()
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

- `sinks` side → `<name>-sinks`: ref the generic source + every sink `rule_id` selected for the unit, wiring `src.$UNTRUSTED -> <sink>.$UNTRUSTED` for each; a sink lib rule must focus its `$UNTRUSTED` metavariable for the join to reference it
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

### 3. Check the build

There is no `opentaint compile` step for Go: `test rule run` takes the side's module directory, runs `go mod tidy` and `go build ./...` in it, and stops with the compiler output if a sample doesn't compile. Run it once to check the build:

```bash
opentaint test rule run .opentaint/test-projects/<name>/<side>
```

A `'go build ./...' failed` error is a samples-or-dependencies problem to fix. Once the run gets past the build, the rest of its result doesn't matter yet — the rules or models it needs come later.

## Constraints

- Write ordinary `.go` files, not `_test.go` files — the Go project loader skips test files
- `test rule run` reads the sample sources directly, not a frozen build — keep the samples fixed once the project is done
- Add `--dataflow-models .opentaint/dataflow` to `test rule run` only when the flow needs an existing dataflow model; never add a model to force a rule to pass
