# create-test-project — Go rule test project

For `type: rule-source` / `rule-sink` on a Go project. There is no Go dataflow approximation, so `type: dataflow` never reaches this language.

**Go deviates from the body in three ways.** There is one shared test module for every Go rule test — not one project per unit, and no `sources/`/`sinks/` sub-projects. There is no scaffold command and no generic taint marker: a sample wires a *real* source into a *real* sink, and the manifest names the *real* rule under test. Everything else — one verdict per sample, extend rather than re-scaffold, compile as the deliverable — is unchanged.

## Workflow

### 1. Init or extend the module

The module lives at `.opentaint/test-projects/go` and is an ordinary Go module. Extend it for each new unit rather than creating another:

- `go.mod` — `module test`, a `go` line, and for any third-party API the samples import a `require <import-path> <version>` plus a local `replace <import-path> => ./stubs/<dep>`. Stub a heavy dependency to a minimal local package rather than vendoring the library. The stub directory must itself be a **nested Go module**: `stubs/<dep>/go.mod` whose `module` line is the **exact real import path** being stubbed (e.g. `module github.com/beego/beego/v2`), holding only the API surface the samples use. A bare directory of `.go` files fails module resolution when `opentaint compile` runs `go`
- samples under a category package per unit, e.g. `security/<unit>/sample.go`. The analyzer references a function by its **import path + name** — `test/security/<unit>.PositiveSourceRequestFormValue`
- small helper source/sink funcs so each sample stays one flow — `requestForSources()` returning `*http.Request`, `envSource()` returning a tainted string, `sqlSink(v)` calling `db.Query(fmt.Sprint(v))`

### 2. Write the samples

Read the real Go source/sink API from the dependency or stdlib first, so each sample is built on the signature the rule actually matches. One function, one verdict, named by convention:

- **positive** (`PositiveXxx`) — a minimal flow that must flag, routing a real source into the real sink
- **negative** (`NegativeXxx`) — the same shape neutralized: a sanitizer between source and sink, or a safe/parameterized sink

Prefix a sample whose behaviour the engine is known not to support yet with `Unsupported` so it isn't counted a strict pass/fail.

```go
package allpatterns

import (
	"database/sql"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"os"
	"strings"
)

var db *sql.DB

func requestForSources() *http.Request {
	return &http.Request{
		URL:  &url.URL{RawQuery: "q=v"},
		Form: url.Values{"q": []string{"form"}},
		Body: io.NopCloser(strings.NewReader("body")),
	}
}

func sqlSink(value interface{}) {
	_, _ = db.Query(fmt.Sprint(value))
}

func envSource() string {
	return os.Getenv("TAINTED")
}

func PositiveSourceRequestFormValue() {
	r := requestForSources()
	sqlSink(r.FormValue("q"))
}

func PositiveSourceURLQueryGet() {
	r := requestForSources()
	sqlSink(r.URL.Query().Get("q"))
}

func NegativeSQLParameterizedArgument() {
	_, _ = db.Query("select * from users where name = ?", envSource())
}

func NegativeSQLConstantQuery() {
	_, _ = db.Query("select * from users where active = 1")
}
```

Expected verdicts go in `.opentaint/test-projects/go/rule-test.yaml`, keyed by the **real** rule-id (`go/security/<file>.yaml#<id>`, the file and id create-rule gave the join) and listing each sample by its `import-path.FuncName` full name — not the Go `package` name:

```yaml
tests:
  - rule-id: go/security/sql-injection.yaml#sql-injection
    positive:
      - test/security/all-patterns.PositiveSourceRequestFormValue
      - test/security/all-patterns.PositiveSourceURLQueryGet
    negative:
      - test/security/all-patterns.NegativeSQLParameterizedArgument
      - test/security/all-patterns.NegativeSQLConstantQuery
```

### 3. Compile to the model

One module, one model — no per-side sub-model:

```bash
opentaint compile .opentaint/test-projects/go -o .opentaint/test-compiled/go
```

The model is portable: the compile copies the module into `.opentaint/test-compiled/go/go_0` and records the relative `projectDir: go_0`, so `test rule run` resolves `rule-test.yaml` and the sample functions from that copy, not from the live sources. Recompile after every sample or manifest edit; `-o` must not already exist, so delete the old model or compile to a fresh directory. `go` must be on PATH.

## Gotchas

- The full name in `rule-test.yaml` is `import-path.FuncName` (the directory path, e.g. `test/security/all-patterns.Foo`), not the Go `package` name (`allpatterns`)
- A name that resolves to no function is fatal to the **whole run**, not just that sample: resolution is an exact `fullName` match with no fuzzy fallback, and one unresolved entrypoint aborts every test with an opaque analyzer exception and no per-sample results. After `compile`, verify every name matches a compiled function before `test rule run`
- Keep the `go.mod` `go` directive (and each stub's) at or below the installed toolchain. Under the default `GOTOOLCHAIN=auto` a newer directive makes `go` try to **download** a toolchain, which fails offline; the shared module tracks `go 1.22`
- One module serves every Go rule test, so parallel agents share `go.mod`, the sample packages, and `rule-test.yaml`. Give each unit its own category dir/package, keep `rule-test.yaml` edits append-only, and don't concurrently edit a shared helper file or the same `require`/`replace` lines
- A positive must route the helper source into the real sink — a sink fed a constant or a bare parameter with no in-sample source can't be flagged by a taint rule
