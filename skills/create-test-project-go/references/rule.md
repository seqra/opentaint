# Rule test project

## Samples

A sample is one exported function whose body wires a **real source into a real sink** (positive,
must flag) or breaks that flow (negative, must not flag). There is no generic `Taint` marker — the
counterpart is always a real Go API, so each sample reads like ordinary code the rule would match
in a real project. Keep small helper source/sink funcs (`requestForSources`, `envSource`,
`sqlSink`) so each sample stays one flow.

- **positive** — a minimal flow that must flag: `PositiveSourceRequestFormValue` routes the
  request-form source into `sqlSink`; `PositiveSourceURLQueryGet` routes the URL-query source in
- **negative** — the safe variant that must not flag: a parameterized query
  (`NegativeSQLParameterizedArgument`, the driver binds the value) or a constant query with no
  in-sample source (`NegativeSQLConstantQuery`)

The samples live under a category dir in the shared module, e.g.
`<test-module>/security/all-patterns/sample.go` — package `allpatterns`, import path
`test/security/all-patterns` (`module test` + the `security/all-patterns` dir):

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

Their expected verdicts live in `<test-module>/rule-test.yaml`, keyed by the **real** rule-id and
listing each sample by its `import-path.FuncName` full name (not the `allpatterns` package name):

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

The rule under test (`go/security/sql-injection.yaml#sql-injection`) is defined by create-rule-go;
that skill's join names the source and sink lib rules the samples above must satisfy.
