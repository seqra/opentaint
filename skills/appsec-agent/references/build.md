# Build

Delegate build-project (Go: **build-project-go**). Inputs: `<project-root>`, model-out `.opentaint/project`, any build constraints (Java version, submodules, `--package` filters). Verify `.opentaint/project/project.yaml` exists, is non-empty, and — for a multi-module project — covers the expected module count, not just that the file is present. Set `phases.build: done`.

Go: `build-project-go` runs the same `opentaint compile` autobuilder and emits a `goProjects` model; `go` must be on PATH.
