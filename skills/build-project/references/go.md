# build-project — Go specific instructions

## Workflow

### 2. Identify the build

- `go.mod` at or under `<project-root>` (within a few levels) → Go module
- the `go` toolchain must be on PATH (`command -v go`). The analyzer drives it through go-ssa-server at scan time, so a Go project cannot be analyzed without it — if `go` is missing, say so and stop rather than producing a half-model
- the installed `go` must satisfy the module's own `go`/`toolchain` directive: a project pinning a newer toolchain either auto-downloads it (needs network) or fails under `GOTOOLCHAIN=local`
- there is no classpath mode. `opentaint scan <project-root>` also compiles Go sources on the fly, so a model is a convenience for reusing a fixed project, not a precondition for scanning

### 3. Enable all modules

A Go repo has no disabled-module concept — nothing to re-enable. A multi-module repo yields one `goProjects` entry per module; confirm the autobuilder found them all.

### 4. Autobuilder

The same `opentaint compile` that builds JVM projects builds Go — it detects `go.mod` and emits a `goProjects` model. No `JAVA_HOME` and no toolchain hint apply:

```bash
opentaint compile <project-root> -o .opentaint/project
```

The autobuilder writes a portable model: it copies each module's sources into `go_<i>/` inside the model directory and records a relative `projectDir` (no top-level `projectRoot`), so the copied tree travels with the model:

```yaml
goProjects:
- projectDir: go_0
```

The model is multi-language — one `project.yaml` can hold both `goProjects:` and `javaProjects:` for a mixed repository.

On failure `opentaint compile` prints the log-file path ("For full details, check the log file:"); read it and fix the real build with the project's own commands before re-running:

```bash
go build ./...
go mod download
```

### 5. Manual model — last resort

A Go model is minimal, so the fallback is to write `.opentaint/project/project.yaml` by hand, one entry per module, each an absolute path (a relative `projectDir` resolves against the model directory, not the current directory):

```yaml
goProjects:
- projectDir: <absolute-path-to-module>
```

There is no `--package` scoping step: the Go model's scope is the module itself, and `opentaint project` is a JVM-only path. Alternatively skip the model and point the scan straight at the sources.

### 6. Verify

`project.yaml` exists, is non-empty, and lists one `goProjects.projectDir` per module the repo declares in a `go.mod`.

## Constraints

- `go` on PATH is required for both building and scanning; the bundled Java runtime does not cover it
- `opentaint pull` pre-provisions the analyzer, autobuilder, built-in rules, go-ssa-server, and bundled Java — it does not install `go`

## Gotchas

- `go` not on PATH → a Go project hard-fails at scan time; install the toolchain before building or scanning
- Unresolvable dependencies → analysis loads the module graph through the `go` toolchain (go-ssa-server calls `packages.Load` with imports and deps). A dependency that fails to resolve is logged as a warning and its types and flows go missing — findings through it are silently lost, and the scan only hard-fails when the `go` invocation itself errors. Run `go mod download` or vendor the deps, ensure network access, and set `GOPRIVATE` plus credentials for private modules
- A hand-written model does not repair a broken build — `opentaint scan` recompiles from source and hits the same error
- Missing dependencies from submodules → `git submodule update --init`
