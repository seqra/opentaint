# discover-attack-surface — Go

## Workflow

### 1. Inspect the assigned members

- Each plan member is `{ method, signature }` — an `import/path.Function`, `(import/path.Type).Method` or `(*import/path.Type).Method` ref and its `args:<count>` arity (explicit arguments, the receiver excluded), copy both into the source tracking unit
- The members are the call sites of the project's SSA form, named as the analyzer names them — an interface call is the interface method (`(io.Reader).Read`), a concrete call the declared method (`(*bytes.Buffer).Read`)
- Locate the module with `go list -m -json <module/path>` in the project — it prints the version, the replacement and the source directory; a standard-library package is under `$(go env GOROOT)/src/<import/path>`. Read a member's signature with `go doc <import/path>.<Name>` or `go doc <import/path>.<Type>.<Method>`; for the body read the module source

### 3. Write the source units

- `dependencies` is the module's `module/path@version` (e.g. `github.com/modelcontextprotocol/go-sdk@v1.7.0`); for a module with a local `replace`, use the replacement path and say so in the source note

## Constraints

- For a Go project the analyzer treats every function and method with a body in the project's own packages, exported or not, as an entry point
