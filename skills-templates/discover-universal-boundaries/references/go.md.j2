# discover-universal-boundaries — Go

`go` must be on PATH — every signature lookup drives the Go toolchain.

## Workflow

### 1. Reconstruct every trace

Go dependencies are source on disk, not resolved jars. Locate a module's source to read a member:

- `go mod download -json <module>` prints the extracted source dir as its `Dir` field
- or `$(go env GOMODCACHE)/<module>@<version>/` — uppercase letters in a module path are case-escaped as `!<lower>`, so `github.com/Azure` is `github.com/!azure`
- or `vendor/<module>/` when the project vendors

Run `go` commands from a module directory (a `goProjects.projectDir` from `project.yaml`). `go doc <import-path>.<Member>` prints the exported signature and receiver; `go doc -src` prints its body.

Go-shaped propagation that is not ingress: a struct field read after the request was already decoded, a `map[string]string` lookup, `fmt.Sprintf`, a helper returning the value it was handed, and the `ShouldBind`/`Decode` step itself once the boundary accessor above it is identified.

### 2. Propose the source

There is no annotation to lean on: a Go boundary is identified by its receiver type and the package it comes from, so the `pattern-inside: import "pkg"` guard that scopes it is part of the condition rather than a marker on the declaration.

Built-in Go source rules are `go/lib/http-sources.yaml`, `http-sources-requesturi.yaml`, and `http-sources-header-index.yaml` — they already carry the `(*http.Request)` surface (`FormValue`, `PostFormValue`, `FormFile`, `Cookie`, `Header.Get`, `Header[$K]`, `Form[$K]`, `URL.Query()`, `URL.Path`, `URL.RawQuery`, `MultipartReader`, `Referer`, `UserAgent`) plus beego's `(*web.Controller)` and `(*context.BeegoInput)` accessors. `os.Getenv`/`os.LookupEnv`/`os.Args` are covered as a trust boundary. A boundary they already match needs no new one; the project's own rules are under `.opentaint/rules/go`.

What they do *not* cover is where a Go family's shared source usually is: the third-party router contexts — gin, echo, fiber, chi — whose accessors (`(*gin.Context).Query`/`.Param`/`.PostForm`/`.GetHeader` and their equivalents) carry the same request surface under a different receiver.

Receiver-value calls are the dominant Go idiom, so the boundary is nearly always a method on a value rather than a package-level function. Read the app source at the handler and at its registration to find that receiver — the package-level API of the dependency will not show it.

### 3. Propose the sink

Where the primitive effects live, and what the built-in `go/lib/` sinks already cover:

- command injection — `exec.Command`, `exec.CommandContext`, `(*exec.Cmd)`, `os.StartProcess`
- path traversal — `os.Open`, `os.OpenFile`, `os.ReadFile`, `os.WriteFile`, `os.Create`, `os.Remove`/`RemoveAll`, `os.Rename`, `http.ServeFile`, resolved through `path/filepath`
- SQL — `(*sql.DB)`, `(*sql.Tx)`, `(*sql.Conn)` `Query`/`Exec` and their `Context` forms
- SSRF — `http.Get`, `http.Head`, `http.Post`, `http.PostForm`, `http.NewRequest`/`NewRequestWithContext`, `(*http.Client)`
- SSTI — `template.New`/`template.Must` and `(*template.Template).Parse`, i.e. an untrusted *template*; an untrusted data model passed to `Execute` is not built in
- XSS — writes to `http.ResponseWriter`, and beego's `(*context.BeegoOutput)`

Beyond those, the primitive effect is almost always in a stdlib package (`os`, `syscall`, `net/url`, `path/filepath`, `encoding/json`, `database/sql`) even when the project reaches it through its own wrapper. Prefer the stdlib boundary and let ordinary propagation cover the wrapper — an ORM or client wrapper is a reusable library sink only when it is where the untrusted value is composed.

### 5. Identify the precision controls

Go's validation impostors: struct-tag binding (`binding:"required"`, go-playground/validator tags) and the `ShouldBind*`/`Unmarshal`/`Decode` call itself. They parse and check presence and sanitize nothing — record them as not-security-relevant validators.

Real Go controls: `net.ParseIP` plus a private-range rejection for SSRF, `filepath.Clean`/`filepath.Abs` plus a `strings.HasPrefix` containment check for traversal, an owner-scoped query for IDOR, `hmac.Equal` verification for callbacks, `html/template` in place of `text/template` for XSS, and CR/LF stripping before a `log`/`slog`/`zap` call for log injection.

Controls use the same `pattern-not`/`pattern-not-inside`/`pattern-inside` vocabulary as the boundaries. Every added branch keeps its `import` guard — without it a bare call pattern fires in unrelated files.

### 6. Write the specification

`candidate_patterns` entries take `method` as `<import-path>.<Member>` for a package-level function or `(*pkg.Type).Method` for a receiver method, with `signature` left empty — Go has neither descriptors nor overloads, so a member is identified by its name alone. The dependency identity to record on the seeded units is the Go module identity `<module-path>@<version>`, read from the project's `go.mod` rather than from the import path; a stdlib boundary has no dependency to name.

`create-rule`'s `references/go.md` and `references/go-semgrep-examples.md` hold the typed-receiver pattern shapes those units turn into.
