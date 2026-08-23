# analyze-external-methods — Go

## Workflow

### 1. Classify propagation

**Read the plan entry first.** A Go dropped record carries the qualified callee in `method` only; its `signature` is literally `args:<arity>` — the parameter count at the call site (it varies only for variadic calls) and holds no package, type, receiver, or name. Never read a package or type out of `signature`.

`method` comes in two shapes:

- plain function — `<import-path>.<Name>`, e.g. `net/url.ParseQuery`, `net/http.Get`. Split at the last `.`: everything before is the import path (it may hold `/` and `.`, as in `github.com/foo/bar`), the trailing segment is the name; no receiver
- method — `(<recv-type>).<Name>`, e.g. `(*net/http.Request).FormValue`. The parenthesized part is the receiver type; strip a leading `*`, then split at the last `.` for the import path and the type. The segment after `)` is the method name

That decomposition is what the build stage's `function:` matcher consumes:

```text
net/url.ParseQuery            → package: net/url,  name: ParseQuery,  receiver: false
(*net/http.Request).FormValue → package: net/http, type: Request, name: FormValue, receiver: true
```

**Getting the source.** An application-internal function sits in the project's own sources under the project root — read it directly. For a dependency, the source is source, not bytecode: it sits in the module cache (`$(go env GOMODCACHE)/<module>@<version>/…`) or in `vendor/<import-path>/` when the project vendors. Standard-library code is under `$(go env GOROOT)/src/<import-path>/`. `go doc <import-path>.<Name>` and `go doc -src <import-path>.<Name>` resolve a name and print its declaration without hunting for the file.

**Go has no dataflow approximation.** The `dataflow` bucket stays empty and `dependencies` stays `[]` — there is no dataflow builder, no test project, and no `build.test_project` entries for Go. A carrier whose data travels through a function value, a callback, or a goroutine/channel chain is still classified `passthrough`, modeled as the closest position-to-position copy, and only becomes an `engine_issues` entry the usual way: after it is built and the method still drops. Never classify it `dataflow` in the hope of a second approximation kind — there isn't one.

passthrough examples — the data is copied from one position to another:

- `strings.ToLower`/`#Join`/`#TrimSpace`/`#Replace`, `fmt.Sprintf`, `[]byte(…)` / `string(…)` conversions
- `strings.Builder#WriteString` and `bytes.Buffer#Write`/`#String`, `io.Copy`, `bufio.Scanner#Text`
- request accessors — `(*net/http.Request).FormValue`/`#PostFormValue`, `net/url.Values#Get`, `net/url.ParseQuery`
- encoding round trips that keep the data — `encoding/json.Marshal`/`Unmarshal`, `net/url.QueryEscape`/`#QueryUnescape`, `encoding/base64` encode/decode
- external key-value stores — a `Set` paired with a `Get` carries the value across the round trip; model both ends

skipped examples — the method carries the data nowhere:

- predicates and inspectors returning a bool or a number — `strings.Contains`/`#HasPrefix`/`#EqualFold`, `len`, `bytes.Equal`
- conversions that collapse the data — `strconv.Atoi`, `strconv.ParseInt`, one-way hashes
- logging and metrics that keep none of the data downstream — `log.Printf`, `log.Println`

### 2. Classify sinks (deep run only)

Unchanged in substance; the record's `method` is the Go qualified name above, and each sink entry's `signature` is the plan's `args:<arity>` string — Go has no descriptor, so overloads never need distinguishing (Go has none). Go sink shapes worth recognizing: `database/sql.DB#Query`/`#Exec` (SQL), `os/exec.Command`/`#CommandContext` (OS command), `os.Open`/`os.ReadFile`/`path/filepath.Join` (path traversal), `net/http.Get`/`#Post`/`Client#Do` (SSRF), `html/template` vs `text/template` `Execute` (XSS — `text/template` does not escape), `encoding/gob.Decoder#Decode` (deserialization).

### 3–4. Verify coverage, re-verify the skips

Unchanged — `check-coverage.py --batch <batch>` is language-independent.
