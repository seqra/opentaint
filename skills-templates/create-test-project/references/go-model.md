# create-test-project — Go model test project

Language reference for a `dataflow` type, keyed to the body's steps.

## Workflow

### 1. Scaffold the project

`opentaint test model init <project> --language go` scaffolds a Go module with module path `test`, the `taint` package (the fixed `taint.Source()` / `taint.Sink()`) and the fixed `model-rule.yaml` the harness applies. Pass each lib as a `--dependency` at its exact version from the app's `go.mod` verbatim — including pseudo-versions — not a guess. The model module scaffolded later takes the same pins, so the samples and the models they exercise build against one version.

```bash
opentaint test model init .opentaint/test-projects/<name> \
  --language go \
  --dependency github.com/acme/library@v1.2.3
```

When the app replaces a module with a local directory, add the same replacement with `go mod edit -replace <module>=<dir>`.

### 2. Write the samples

Write one sample per callable in the batch's `dataflow` bucket, across all its packages. Each `dataflow` entry records the callable's `signature` (`args:<count>`, the receiver excluded) — use it to shape the call. Look at how the callable is actually called in the project to shape the sample and pick the receiver type. Each sample is a plain exported function in `package test` at the module root — you don't author a rule; the scaffold's fixed `model-rule.yaml` is what the harness applies. The sample just routes `taint.Source()` through the modeled callable into `taint.Sink(...)`. Its verdict is recorded in `rule-test.yaml` (below), not on the function.

Mark each callable's test-project status (per Tracking): `done` once its sample is in the project. If no sample can be written for a callable, exclude it, mark it `failed`, and note it in the summary — don't let one unmodelable callable block the rest.

Positive sample — routes `taint.Source()` through the modeled callable into `taint.Sink(...)`, one per callable being modeled. Start every sample with `tainted := taint.Source()`. When the modeled callable takes a non-string input, convert the tainted string to that type so the taint fact reaches the callable as the right type — the analyzer tracks the fact, not the runtime value.

```go
package test

import (
	"github.com/acme/library/text"
	"test/taint"
)

func TaintReachesSink() {
	tainted := taint.Source()
	routed := text.Transform(tainted) // the modeled callable
	taint.Sink(routed)
}
```

Negative sample — only when the modeled callable stores its input in the object. The analyzer is field-sensitive: taint set on one field doesn't surface from another. Write a negative sample that stores tainted data into one field and reads a different one — a field-precise model keeps that read clean, so the sample must not fire. This is what forces a precise model instead of one that taints the whole object. For plain propagation the positive alone proves the model — skip the negative.

```go
func TaintStaysInItsField() {
	var user text.User
	user.SetName(taint.Source()) // taint stored in the name field
	taint.Sink(user.Email())     // a different field — must stay clean
}
```

Register the verdicts — write `rule-test.yaml` at the test-project root (next to `go.mod`), one entry under the fixed rule, listing each sample by its Go function name, `test.<Function>`. `positive` samples must flag, `negative` must not:

```yaml
tests:
  - rule-id: model-rule.yaml#model-rule
    positive:
      - test.TaintReachesSink
    negative:
      - test.TaintStaysInItsField
```

Note — a sample's receiver type fixes the dropped callable's name, and the later model targets that exact callable, so mirror the real call's receiver type. The same call off an interface-typed value (`var r io.Reader`, e.g. a parameter) resolves to `(io.Reader).Read`, off a concrete one (`bytes.NewBufferString(...)`) to `(*bytes.Buffer).Read` — match whichever the real flow uses.

When the modeled callable hands the data to a callback instead of returning it, put the sink inside the callback body: `text.Each(values, func(v string) { taint.Sink(v) })`. Don't stash the value in a captured variable and sink it after the call.

### 3. Check the build

There is no `opentaint compile` step for Go: `test model run` takes the test project directory, runs `go mod tidy` and `go build ./...` in it, and stops with the compiler output if a sample doesn't compile. Run it once to check the build:

```bash
opentaint test model run .opentaint/test-projects/<name>
```

A `'go build ./...' failed` error is a samples-or-dependencies problem to fix. Once the run gets past the build, the rest of its result doesn't matter yet — the rules or models it needs come later.

## Constraints

- Write ordinary `.go` files, not `_test.go` files — the Go project loader skips test files
- `test model run` reads the sample sources directly, not a frozen build — keep the samples fixed once the project is done
