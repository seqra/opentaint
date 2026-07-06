---
name: build-project-go
description: Build a Go project for opentaint analysis and produce a project.yaml model. Use whenever an opentaint scan needs a project model for a Go (go.mod) project
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Build Project (Go)

Build a target Go project into an opentaint project model. The model is this skill's only output

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the Go project to build (a directory holding `go.mod`). Default: current directory
- Model output directory `<model-out>` — where to write the model. Default: `.opentaint/project`
- Build constraints (optional) — the Go toolchain version the module's `go` directive needs, git submodules to initialize, `GOPRIVATE` plus credentials for private-module dependencies

## Workflow

### 1. Confirm it's a Go project and the toolchain is present

- `go.mod` at or under `<project-root>` (within a few levels) → Go project
- existing `project.yaml` under `<model-out>` → already built, reuse it
- `go` on PATH (`command -v go`) — the analyzer drives the Go toolchain through go-ssa-server at scan time, so a Go-only project cannot be analyzed without it. If `go` is missing, tell the caller and stop; don't produce a half-model
- the installed `go` must satisfy the module's own `go`/`toolchain` directive — a project pinning a newer toolchain either auto-downloads it (needs network) or fails under `GOTOOLCHAIN=local`
- `opentaint pull` pre-provisions the toolchain artifacts (analyzer, autobuilder, built-in rules, go-ssa-server, bundled Java); run it once before the first build to cache the offline pieces — it does not install `go` itself

### 2. Autobuilder

The same `opentaint compile` that builds JVM projects also builds Go — it detects `go.mod` and emits a `goProjects` model:

```bash
opentaint compile <project-root> -o <model-out>
```

The autobuilder writes a portable model: it copies each Go module's sources into `go_<i>/` inside `<model-out>` and records a relative `projectDir` (no top-level `projectRoot`):

```yaml
goProjects:
- projectDir: go_0
```

A relative `projectDir` is resolved against the model directory, so the copied `go_0/` travels with the model. The model is multi-language: one `project.yaml` can hold both `goProjects:` and `javaProjects:` for a mixed repository.

### 3. Autobuilder fails — read the log, then hand-write the model

`opentaint compile` prints the log-file path on failure ("For full details, check the log file:"); read it and fix the underlying build first (see Gotchas). A hand-written model does not repair a broken Go build.

Once the build itself is sound, a Go model is minimal — write `<model-out>/project.yaml` by hand with one `goProjects.projectDir` per Go module, each an absolute path to the module (a relative `projectDir` resolves against the model directory, not the current directory):

```yaml
goProjects:
- projectDir: <absolute-path-to-module>
```

Or skip the model entirely and point the scan straight at the source directory (`opentaint scan <project-root>` compiles it on the fly).

### 4. Verify

`<model-out>/project.yaml` exists, is non-empty, and lists the project under `goProjects:`

## Output

The project model directory containing `project.yaml` (default `.opentaint/project`, or the caller's path). Report that path back

## Gotchas

- `go` not on PATH → a Go-only project hard-fails at scan time; install the Go toolchain before building or scanning
- Compile fails → the CLI prints the log-file path ("For full details, check the log file:"); read it and fix the build. A hand-written model does not repair a broken build, and `opentaint scan` recompiles from source and re-hits the same error
- Unresolvable dependencies → analysis loads the module graph through the `go` toolchain (go-ssa-server calls `packages.Load` with imports and deps). A dependency that fails to resolve is logged as a warning and its types and flows go missing from the analysis — findings through it are silently lost; the scan only hard-fails when the `go` toolchain invocation itself errors. Run `go mod download` or vendor the deps and ensure network access; set `GOPRIVATE` plus credentials for private modules
- No autobuilder compile step is required to scan Go — `opentaint scan <project-root>` works directly on sources; the model just lets later steps reuse a fixed project without recompiling
- Multi-module repos: one `goProjects.projectDir` per module; the autobuilder discovers them, or add them by hand in the fallback
- Never hand-edit a model the autobuilder produced to "fix" analysis — rebuild it instead
