# create-dataflow-model — Go

The Go procedure, keyed to the body's steps.

## Workflow

### 1. Find the method's source

An app-internal function sits in the project's own sources under `<project-root>`. For a library function, run `go list -m -json <module/path>` in the project to find the module's version, replacement and source directory, and read the function there; a standard-library function is under `$(go env GOROOT)/src/<import/path>`. The batch names each callable as the analyzer does — `import/path.Function`, `(import/path.Type).Method` or `(*import/path.Type).Method` — with its `args:<count>` arity, which excludes the receiver.

### 2. Write the model source

Scaffold the model module with the same `--dependency` pins as the batch's test project (`.opentaint/test-projects/<batch>/go.mod`):

```bash
opentaint approximation init .opentaint/dataflow/<batch> \
  --language go \
  --dependency github.com/acme/library@v1.2.3
```

When a model needs a module the project doesn't pin yet, re-run `approximation init` with the full dependency list — it keeps the sources and replaces `go.mod`.

Create one Go package for each target package. The scaffold's `go.mod` declares `module opentaint`; put the model of `github.com/acme/library/text` under `.opentaint/dataflow/<batch>/github.com/acme/library/text/`, so its import path is `opentaint/github.com/acme/library/text`, and declare the target's package name. Model the exact callable from the dropped method report: keep its name, receiver, type parameters, parameter types and result types. The model body replaces the target body, and target callables you don't model keep their own. A receiver struct lists only the fields the body uses, each with the target field's name and type. Use target types through their original imports — a model of `net/http` may import `net/http` itself. Do not use an empty body, or a constant or zero result where the target propagates its input.

```go
package text

// Model: taint on the input flows to the result
func Transform(value string) string {
	return value
}

// Model: taint stored in the builder flows out of String
type Builder struct {
	buf string // the target field the bodies use
}

func (b *Builder) Append(value string) *Builder {
	b.buf += value
	return b
}

func (b *Builder) String() string {
	return b.buf
}

// Model: taint on the input flows to the callback
func Each(values []string, fn func(string)) {
	for _, value := range values {
		fn(value)
	}
}
```

### 3. Test against the test project

Run `test approximation run` over the compiled test project applying this batch's models, iterate the models until the samples pass:

```bash
opentaint test approximation run .opentaint/test-compiled/<batch> \
  -o .opentaint/test-results/<batch> \
  --go-models .opentaint/dataflow/<batch>
```

`test approximation run` applies its bundled Go source-to-sink rule. Go models are source modules: OpenTaint loads them with the target modules in one temporary Go workspace, so there is no `compile approximations` step and no Java support JAR. A model that does not type-check fails the run with exit code 252, the analyzer's generic unhandled-error code; the analyzer log names the type error.

A positive sample is a `falseNegative` until the model propagates taint. Read the result with the bundled script — it prints the pass/fail counts and names each failing sample, so you don't parse the JSON by hand:

```bash
uv run <skill-dir>/scripts/check-test-result.py <batch>
```

Fix by the verdict it reports:

- still `falseNegative` means that the target package, callable, receiver, signature, or taint path is incorrect. Use `opentaint/<exact-target-import-path>` and the exact name and receiver from the dropped method report
- `falsePositive` (a negative sample fired) → the model is over-broad: it taints a read it shouldn't, e.g. a field it wasn't stored under. Narrow the propagation until the negative stays non-firing while the positive passes
- `skipped` or `disabled` is a failure, not coverage — the sample or its rule did not run

Apply the same module to the target scan with `opentaint scan <project> --go-models .opentaint/dataflow/<batch>`.

## Key patterns

| Pattern | Usage |
|---|---|
| `opentaint/<target-import-path>` | The model package path. Remove `opentaint/` to get the target import path. |
| `package <target-name>` | The model package keeps the target package's name |
| Partial receiver struct | Lists only the fields the bodies use; an existing field keeps the target's name and type |
| Helpers | Additional functions, methods, types and fields are model support; a new field is added after the target's fields |

## Constraints

- A model may only import the analyzed project's packages, their dependencies, and the modules its own `go.mod` pins. A model that needs a type from an unpinned module is a missing `--dependency`, not a reason to weaken the model
- Use `opentaint/<exact-target-import-path>` as the package path and the target's package name in the package clause
- Every target package has one model package. Do not model the same package in more than one batch
- One model package per target package — a global bijection enforced at load across custom and built-in models: a second model of the same package fails the scan with `Go package "<target>" is modeled more than once`
- Callable signatures must match the target exactly
- Model `init` functions are ignored
- Built-in Go models (`model/go/dataflow`) load with every scan — you cannot model their target packages locally
- A Go model overrides a passThrough for the same callable — passThrough rules apply only to calls without a body, and the model gives the call one. Use a model as the fallback when a faithful passThrough cannot express the propagation
- Don't unpack or grep the analyzer JAR for built-in models or signatures — its internals aren't a stable API; go through the CLI
