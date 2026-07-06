---
name: discover-attack-surface-go
description: Analyze project-used members of a dependency module for taint sources and sinks not covered by the built-in Go rules. Use for the depth pass of attack-surface discovery on a Go project, one module at a time, after triage-dependencies flags it
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface (Go)

Take one dependency module the triage flagged, settle what the built-in Go rules already cover for the package members this project uses, and write that project-used rule plan — the untrusted-data sources and dangerous sinks actually relevant to this project — for the next phase to build

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Module `<module>` — the flagged dependency's module path (a `pending` entry in `coverage.yaml`); the version, needed only to locate the source in the module cache, comes from the project's `go.mod`
- Project model `<model-dir>` — the built model; its `project.yaml` lists the Go module dir(s) under `goProjects.projectDir`. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and the per-module lib units live. Default: `.opentaint/tracking`

`go` must be on PATH — the member extraction and signature lookups drive the Go toolchain

## Workflow

### 1. Settle built-in coverage first

Before planning anything, see what the built-ins already match for this module's project-used members — read the Go lib rules (`opentaint health --rules`, the `go/lib` source/sink rules) plus `.opentaint/rules`. Decide one of:

- **full** — the built-ins already match the project-used module sources/sinks → write no lib unit, flip the `coverage.yaml` entry to `done` with a `builtin_coverage: full` note, and stop. Don't drill further
- **partial** — built-ins match some project-used members but miss others → plan only the missing used members (`coverage: expand`, ref the built-in for the rest)
- **none** — plan the module's project-used surface from scratch

### 2. Scope project-used sources and sinks

Go dependencies are source on disk, not resolved jars. Locate the module's source to inspect signatures for members already in scope: `go mod download -json <module>` prints the extracted source dir as its `Dir` field, or it lives under `$(go env GOMODCACHE)/<module>@<version>/` (uppercase letters in the module path are case-escaped as `!<lower>` in the cache, e.g. `github.com/Azure` → `github.com/!azure`), or `vendor/<module>/` when the project vendors. Run `go` commands from a Go module dir (a `goProjects.projectDir` from `project.yaml`).

To get the source-derived list of module members the project statically references, run this skill's bundled `scripts/package-usages.sh <model-dir> <module>` (Windows: `scripts/package-usages.ps1`; the scripts live in the skill directory, not the project) and save its output to `<tracking-dir>/usage/<package-kebab>.yaml` (create `usage/` if needed). It reads the module dir(s) from `project.yaml`'s `goProjects.projectDir`, finds the project's **own** `.go` files importing the module or any package under it, resolves each import's local identifier — handling aliases and a package name that differs from the last path element via `go list` — and prints the deduped `<import-path>.<ExportedMember>` selector call sites whose owner is the module

The script sees only package-qualified selectors (`gin.New`, `jwt.Parse`) — it is structurally blind to method calls on receiver values (`c.Query(...)`, `db.QueryContext(...)`), the dominant Go idiom and the exact shape of most accessor sources and sinks — and to members reached through interface dispatch, reflection, struct-embedding promotion, router/handler registration, config strings, or generated code absent from the source tree. Treat its output as the entry scope — which packages, constructors, and package-level functions the project touches — then inspect the app source and the dependency's own source (under the located dir) to add the methods called on those values and the indirectly reached members, and append them to the usage snapshot. `go doc <import-path>.<Member>` (or `go doc <import-path>`) prints the exported signature and receiver for classification. Do not enumerate the whole module API. Never inspect the analyzer or go-ssa-server binaries — only the project's own source and the dependency's source

- **sources** — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution): a method that *returns* attacker-controlled data — HTTP/RPC request data (`(*http.Request).FormValue`, a framework context accessor), a message-broker payload. NOT a method that merely passes data it was handed along — that's a propagator the engine already handles, not a source. General, not receiver-tagged
- **sinks** — dangerous operations (query construction, command/file/path ops, deserialization, template/SSTI, SSRF request building, reflection); tag each with its vuln class (`ssrf`, `sqli`, `path-traversal`, …)

Verify each is real before recording: a source genuinely attacker-controlled, a sink genuinely dangerous with tainted input. Don't trace a flow between them — the analyzer pairs them at scan time

### 3. Write the module's rule plan

Write `<tracking-dir>/rules/lib/<package-kebab>.yaml` — only the project-used new sources and sinks, grouped by `vuln_class`, the module path + version, `stages.description: done`, and each `coverage: new` or `expand`. Then flip the module's `coverage.yaml` entry to `status: done`. `<package-kebab>` is the module path with `/` and `.` → `-` (e.g. `github.com/gin-gonic/gin` → `github-com-gin-gonic-gin`); the `package:` field keeps the real module path

## Output

- A `<tracking-dir>/rules/lib/<package-kebab>.yaml` rule plan for project-used members only (or, for `full` coverage, none — just the coverage note)
- A `<tracking-dir>/usage/<package-kebab>.yaml` module usage snapshot — the `package-usages.sh` selector list plus the receiver methods added during source inspection
- The module's `coverage.yaml` entry set `status: done` with a one-line `notes`
- A brief summary to the caller: the sources and sinks planned (one line each, marked `new` / `expand`). The unit holds the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — flip this module's entry when done:

```yaml
  - package: github.com/gin-gonic/gin
    status: done
    notes: gin.Context request accessors — new untrusted sources (PostForm/Query); ssrf sink expands the built-in
```

`<tracking-dir>/usage/<package-kebab>.yaml` — temporary-but-persisted project-used scope. Keep it next to the rule plans so resumed agents can reuse it instead of rerunning extraction:

```yaml
functions:
  - function: "github.com/gin-gonic/gin.New"
  - function: "github.com/gin-gonic/gin.Context.PostForm"
  - function: "github.com/gin-gonic/gin.Context.Query"
```

The package-qualified entries come from the script; the receiver-method entries are appended during source inspection

`<tracking-dir>/rules/lib/<package-kebab>.yaml` — the rule plan; fill only the discovery-stage fields (create-test-project-go and create-rule-go fill the rest):

```yaml
package: github.com/gin-gonic/gin
dependencies:
  - github.com/gin-gonic/gin@v1.10.0
builtin_coverage: partial
sources:
  - idea: gin.Context PostForm/GetPostForm — untrusted request data
    coverage: new
    builtin: null
    rule_id: null
sinks:
  - vuln_class: ssrf
    idea: outbound request built from a gin.Context value
    coverage: expand
    builtin: go/lib/ssrf-sinks.yaml#ssrf-sinks
    rule_id: null
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

## Engine notes

- Go untrusted-data sources are declared by the Go source lib rules (`go/lib/*-sources.yaml`), not by framework endpoint auto-discovery — a `network` inbound source the built-in Go source rules already match needs no new source; focus on the boundaries they miss and on the sinks
- Stored / second-order injection (data persisted then read back) is modeled by the engine on its own — don't plan a source for the read-back or a propagator for the store→read path

## Gotchas

- Plan, don't write — record source/sink ideas only; the Go lib rules are written and tested in the next phase by create-rule-go
- Don't re-declare a source or sink a built-in already matches — `coverage: expand` with only the missing used members, or fold it into `full` coverage
- Don't add unused module APIs just because they look security-relevant — this phase scopes rules to what the project uses or reaches indirectly
- `go` not on PATH → `package-usages.sh`, `go doc`, and `go mod download` all fail; install the Go toolchain first
