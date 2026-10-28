# create-test-project — Go approximation test project

Language reference for a `dataflow` type, keyed to the body's steps.

## Workflow

### 1. Scaffold the project

`opentaint test approximation init` scaffolds Java only, so write the Go project at `.opentaint/test-projects/<name>` by hand: a `go.mod` with `module test` and the app's Go version, the generic marker, and the fixed rule the samples run against. Require each lib at its exact version from the app's `go.mod` verbatim — including pseudo-versions and local `replace` directives — not a guess. The model module scaffolded later takes the same pins, so the samples and the models they exercise build against one version.

`util/taint.go` — the generic marker:

```go
package util

func Source() string { return "" }
func Sink(string) {}
```

`test-rules/go/approximation.yaml` — the fixed rule, routing `util.Source()` to `util.Sink(...)`:

```yaml
rules:
  - id: approximation
    languages: [go]
    mode: taint
    severity: ERROR
    message: Test input reaches the marker sink through a Go model
    pattern-sources:
      - patterns:
          - pattern-inside: |
              import "test/util"
              ...
          - pattern: util.Source()
    pattern-sinks:
      - patterns:
          - pattern-inside: |
              import "test/util"
              ...
          - pattern: util.Sink($VALUE)
          - focus-metavariable: $VALUE
```

### 2. Write the samples

Write one sample per callable in the batch's `dataflow` bucket, across all its packages. Each `dataflow` entry records the callable's `signature` (`args:<count>`, the receiver excluded) — use it to shape the call. Look at how the callable is actually called in the project to shape the sample and pick the receiver type. Each sample is a plain exported function in `package test` at the module root — you don't author a rule; the fixed `approximation.yaml` is what the harness applies. The sample just routes `util.Source()` through the approximated callable into `util.Sink(...)`. Its verdict is recorded in `rule-test.yaml` (below), not on the function.

Mark each callable's test-project status (per Tracking): `done` once its sample is in the project. If no sample can be written for a callable, exclude it, mark it `failed`, and note it in the summary — don't let one unmodelable callable block the rest.

Positive sample — routes `util.Source()` through the approximated callable into `util.Sink(...)`, one per callable being approximated. Start every sample with `tainted := util.Source()`. When the approximated callable takes or returns another type, add a marker of that type to `util` and to the rule — the analyzer tracks the fact, not the runtime value.

```go
package test

import (
	"github.com/acme/library/text"
	"test/util"
)

func TaintReachesSink() {
	tainted := util.Source()
	routed := text.Transform(tainted) // the approximated callable
	util.Sink(routed)
}
```

Negative sample — only when the approximated callable stores its input in the object. The analyzer is field-sensitive: taint set on one field doesn't surface from another. Write a negative sample that stores tainted data into one field and reads a different one — a field-precise model keeps that read clean, so the sample must not fire. This is what forces a precise approximation instead of one that taints the whole object. For plain propagation the positive alone proves the model — skip the negative.

```go
func TaintStaysInItsField() {
	var user text.User
	user.SetName(util.Source()) // taint stored in the name field
	util.Sink(user.Email())     // a different field — must stay clean
}
```

Register the verdicts — write `rule-test.yaml` at the test-project root (next to `go.mod`), one entry under the fixed rule, listing each sample by its Go function name, `test.<Function>`. `positive` samples must flag, `negative` must not:

```yaml
tests:
  - rule-id: go/approximation.yaml#approximation
    positive:
      - test.TaintReachesSink
    negative:
      - test.TaintStaysInItsField
```

Note — a sample's receiver type fixes the dropped callable's name, and the later model targets that exact callable, so mirror the real call's receiver type. The same call off an interface-typed value (`var r io.Reader`, e.g. a parameter) resolves to `(io.Reader).Read`, off a concrete one (`bytes.NewBufferString(...)`) to `(*bytes.Buffer).Read` — match whichever the real flow uses.

When the approximated callable hands the data to a callback instead of returning it, put the sink inside the callback body: `text.Each(values, func(v string) { util.Sink(v) })`. Don't stash the value in a captured variable and sink it after the call.

## Constraints

- Write ordinary `.go` files, not `_test.go` files — the Go project loader skips test files
- Diagnose a compile failure with `go build ./...` in the project
- For Go, `opentaint compile` writes a project model that points to the sample sources, not a frozen build — keep the samples fixed after compiling
