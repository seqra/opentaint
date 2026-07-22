# discover-attack-surface — Go

`go` must be on PATH — the member extraction and every signature lookup drive the Go toolchain.

## Workflow

### 1. Settle built-in coverage

Built-in Go source and sink rules live under `go/lib/` within the `opentaint health --rules` root — grep there for the member's package or method name (a rule is a semgrep-like pattern, not indexed by import path), then read the matched rule file to confirm it covers the member. The project's own custom rules are under `.opentaint/rules/go`.

Go untrusted-data sources are declared by those `go/lib/*-sources.yaml` rules, not by framework endpoint auto-discovery: an inbound source the built-in rules already match needs no new source, so focus on the boundaries they miss and on the sinks.

### 2. Classify the plan's members

Each plan member is `{ method, signature }` where `method` is `<import-path>.<Member>` and `signature` is empty — Go has no descriptor and no overloads, so a member is identified by its name alone.

Go dependencies are source on disk, not resolved jars. Locate a module's source to read signatures:

- `go mod download -json <module>` prints the extracted source dir as its `Dir` field
- or `$(go env GOMODCACHE)/<module>@<version>/` — uppercase letters in a module path are case-escaped as `!<lower>`, so `github.com/Azure` is `github.com/!azure`
- or `vendor/<module>/` when the project vendors

Run `go` commands from a module directory (a `goProjects.projectDir` from `project.yaml`). `go doc <import-path>.<Member>` prints the exported signature and receiver; `go doc -src` prints its body.

**The plan's scope is an entry scope, not the whole surface.** The extractor sees only package-qualified selectors (`gin.New`, `jwt.Parse`); it is structurally blind to method calls on receiver values (`c.Query(…)`, `db.QueryContext(…)`) — the dominant Go idiom and the exact shape of most accessor sources and sinks — and to members reached through interface dispatch, reflection, struct-embedding promotion, router/handler registration, config strings, or generated code absent from the source tree. Treat the plan as *which packages, constructors, and package-level functions the project touches*, then read the app source and the dependency's source to add the methods called on those values and the indirectly reached members, and classify those too. Do not enumerate the whole module API.

Classifying:

- **sources** — where untrusted data first enters from a boundary: a method that *returns* attacker-controlled data (`(*http.Request).FormValue`, a framework context accessor, a message-broker payload). Not a method that merely passes along data it was handed — that is a propagator the engine already handles
- **sinks** — dangerous operations (query construction, command/file/path ops, deserialization, template/SSTI, SSRF request building, reflection), each tagged with its vuln class

### 3. Write the source units

`dependencies` is the Go module identity, `<module-path>@<version>` (e.g. `github.com/gin-gonic/gin@v1.10.0`) — read the version from the project's `go.mod`, not from the import path.
