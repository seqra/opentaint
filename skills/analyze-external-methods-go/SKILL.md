---
name: analyze-external-methods-go
description: Analyze and group a Go opentaint scan's dropped external methods into passThrough approximation targets. Use when a Go dropped-external-methods.yaml needs turning into approximation targets
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Analyze External Methods (Go)

Read the Go methods where the analyzer lost track of the data and record per package what to model — so create-pass-through-approximation-go can build each approximation. Go has only one approximation kind: passThrough. There is no dataflow approximation for Go, so there is no kind split

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Dropped methods `<dropped-file>` — methods where the analyzer dropped the data for lack of a model. Default: `.opentaint/results/dropped-external-methods.yaml`
- Tracking directory `<tracking-dir>` — where approximation tracking files are written. Default: `.opentaint/tracking`
- Project root `<project-root>` — sources and `go.mod`, to resolve which package owns each method. Default: current directory

## Workflow

Requires `<dropped-file>`, without it there's nothing to group

### 1. Read the dropped records

Each entry in `<dropped-file>` is an `ExternalMethodRecord` with `method` and `signature` strings (plus `factPositions`, `callSites`). The `method`/`signature` identify the Go function: its package, its receiver type (if any), and its name. Resolve each to a `{package, name, type, receiver}` matcher — the shape create-pass-through-approximation-go's `function:` block uses. Read the real Go signature from the dependency or the stdlib docs when the dropped strings are ambiguous

### 2. Group by package

Group methods by their Go import path (`net`, `net/http`, `database/sql`, `github.com/foo/bar`, …) — one tracking file per package: `<package-kebab>-passthrough.yaml`. `<package-kebab>` is the import path with `/` and `.` replaced by `-` (e.g. `net/http` → `net-http`, `github.com/foo/bar` → `github-com-foo-bar`) so it's filesystem-friendly; the YAML `package:` field keeps the real import path. Every method is passThrough — there is no dataflow split and no per-unit dependency/GAV list (the Go module's own `go.mod` already resolves the package)

### 3. Flag methods to skip

A few methods the engine asks about don't affect the data flow — logging, metrics (e.g. `log.Printf`). List those in `skipped.yaml` instead of an approximation group; the default call-to-return behavior is already correct for them

## Output

- One `<tracking-dir>/approximations/<package-kebab>-passthrough.yaml` per package, with `stages.description: done` and its `methods` (each `target` describing the `{package, name, type, receiver}` matcher + `type: passthrough`)
- `<tracking-dir>/approximations/skipped.yaml` listing the skip methods
- A brief summary to the caller: one line per unit (package, method count) plus the skip count. Don't paste the method lists back — the tracking files hold them

## Tracking

Create one file per package; fill only the discovery-stage fields. Every Go unit is passThrough — written and verified by the scan, no test project:

```yaml
package: net/http
artifact: null
stages:
  description: done
  written: pending
notes: >
  Request accessors carrying request data through to results
methods:
  - target:
      package: net/http
      type: Request
      name: FormValue
      receiver: true
    type: passthrough
```

```yaml
methods:
  - "log.Printf"
  - "log.Println"
```

## Gotchas

- Model every method in `<dropped-file>` — each is a real place the data is lost; the only exceptions are the obvious methods that don't move data, which you move to `skipped.yaml`
- Approximate only external library/stdlib methods — never an application-internal function. If one shows up as a candidate, drop it
- One file = one package = one agent; never put a method in two files, or two agents collide
- Go has no dataflow approximation — a method whose propagation a passThrough can't express is an engine issue, not a second approximation kind (create-pass-through-approximation-go handles that hand-off)
