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

## Workflow

### 1. Confirm it's a Go project and the toolchain is present

- `go.mod` at or under `<project-root>` (within a few levels) → Go project
- existing `project.yaml` under `<model-out>` → already built, reuse it
- `go` on PATH (`command -v go`) — the analyzer drives the Go toolchain through go-ssa-server at scan time, so a Go-only project cannot be analyzed without it. If `go` is missing, tell the caller and stop; don't produce a half-model

### 2. Autobuilder

The same `opentaint compile` that builds JVM projects also builds Go — it detects `go.mod` and emits a `goProjects` model:

```bash
opentaint compile <project-root> -o <model-out>
```

The resulting `project.yaml` carries a `goProjects:` entry:

```yaml
projectRoot: <project-root>
goProjects:
- projectDir: <project-root>
```

The model is multi-language: one `project.yaml` can hold both `goProjects:` and `javaProjects:` for a mixed repository.

### 3. Autobuilder fails — hand-write the model

A Go model is minimal, so when the autobuilder can't run you can write `<model-out>/project.yaml` by hand with the two fields above (`projectRoot` and one `goProjects.projectDir` per Go module), or skip the model entirely and point the scan straight at the source directory (`opentaint scan <project-root>` compiles it on the fly).

### 4. Verify

`<model-out>/project.yaml` exists, is non-empty, and lists the project under `goProjects:`

## Output

The project model directory containing `project.yaml` (default `.opentaint/project`, or the caller's path). Report that path back

## Gotchas

- `go` not on PATH → a Go-only project hard-fails at scan time; install the Go toolchain before building or scanning
- No autobuilder compile step is required to scan Go — `opentaint scan <project-root>` works directly on sources; the model just lets later steps reuse a fixed project without recompiling
- Multi-module repos: one `goProjects.projectDir` per module; the autobuilder discovers them, or add them by hand in the fallback
- Never hand-edit a model the autobuilder produced to "fix" analysis — rebuild it instead
