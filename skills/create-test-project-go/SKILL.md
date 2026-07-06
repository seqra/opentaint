---
name: create-test-project-go
description: Create or extend an OpenTaint Go test module with positive/negative samples and a rule-test manifest for verifying a Go rule. Use when a Go rule needs a test project to check against
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create Test Project (Go)

Build a minimal Go test module whose sample functions reproduce the flow a rule is checked
against, and a `rule-test.yaml` manifest that maps the rule to its positive/negative samples.
The compiled model is the deliverable; its sources and manifest sit alongside it

Go testing has no annotations, no `sinks/`/`sources/` sub-projects, and no generic `Taint`
marker. A sample wires a **real source into a real sink** in one function; the manifest
references the **real rule-id** directly

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- What to test `<spec>` — the rule's requirements (the source patterns, the sink patterns, the rule-id) or the methods to exercise
- Project root `<project-root>` — the real sources the requirements point into. Default: current directory
- Tracking file `<tracking-file>` — the rule file this test serves. Default: `.opentaint/tracking/rules/lib/<name>.yaml`
- Test module `<test-module>` — the Go module sources. Default: `.opentaint/test-projects/go`
- Compiled output `<test-compiled>` — the model. Default: `.opentaint/test-compiled/go`
- Dependencies — the Go modules the samples import (their `require` paths/versions); default: derive from `<project-root>`'s `go.mod`

## Workflow

### 1. Init or extend the Go module

One module serves all Go rule tests (extend it, don't make a new one per rule). It is an
ordinary Go module:

- `<test-module>/go.mod` — `module test`, a `go` line, and, for any third-party API the samples
  import, a `require <import-path> <version>` plus a local `replace <import-path> => ./stubs/<dep>`.
  Stub a heavy dependency to a minimal local package rather than vendoring the whole library. The
  stub directory must itself be a **nested Go module**: `stubs/<dep>/go.mod` whose `module` line is
  the **exact real import path** being stubbed (e.g. `module github.com/beego/beego/v2`), holding
  only the API surface the samples use. `replace <import-path> => ./stubs/<dep>` resolves only when
  that directory has its own `go.mod`; a bare directory of `.go` files fails at module resolution
  when `opentaint compile` runs `go`
- sample functions under a category package, e.g. `<test-module>/security/all-patterns/sample.go`
  (package `allpatterns`); the analyzer references a function by its **import path + name**:
  `test/security/all-patterns.PositiveSourceRequestFormValue`
- small helper source/sink funcs so each sample stays one line — e.g. `requestForSources()`
  returning `*http.Request`, `envSource()` returning a tainted string, `sqlSink(v)` calling
  `db.Query(fmt.Sprint(v))`

### 2. Read the real signatures, then write samples

Read the real Go source/sink APIs from the dependency (or stdlib) so a sample is built on the
signature the rule actually matches. Each sample is one function with exactly one expected
verdict, named by convention:

- **Positive** (`PositiveXxx`) — routes a real source into the real sink:
  `func PositiveSourceRequestFormValue() { r := requestForSources(); sqlSink(r.FormValue("q")) }`
- **Negative** (`NegativeXxx`) — the same shape but neutralized: a sanitizer between source and
  sink, or a safe/parameterized sink:
  `func NegativeXSSHTMLEscape() { w.WriteString(html.EscapeString(envSource())) }`

Prefix a sample whose behavior the engine is known not to support yet with `Unsupported` so it
isn't listed as a strict pass/fail. One verdict per function — don't make a function both

Load and follow `references/rule.md` for a complete compilable sample and its manifest entry

### 3. Write the rule-test manifest

Add (or extend) one entry per rule-id in `<test-module>/rule-test.yaml`, listing the sample
full names under `positive:`/`negative:`. The `rule-id` is the **real rule** under test — its
`go/security/<file>.yaml#<id>` (no marker, no test-join), the file path and id create-rule-go
gives the rule:

```yaml
tests:
  - rule-id: go/security/sql-injection.yaml#sql-injection
    positive:
      - test/security/all-patterns.PositiveSourceRequestFormValue
      - test/security/all-patterns.PositiveSourceURLQueryGet
    negative:
      - test/security/all-patterns.NegativeSQLParameterizedArgument
```

### 4. Compile to a model

`opentaint test rule run` needs a compiled project-model directory (one holding `project.yaml`),
not raw sources — so compile the module:

```bash
opentaint compile <test-module> -o <test-compiled>
```

A clean compile producing `<test-compiled>/project.yaml` is the deliverable. The model is
portable: the compile copies the module into `<test-compiled>/go_0` and records the relative
`projectDir: go_0`, so `test rule run` resolves `rule-test.yaml` and the sample functions from
that copy — not from the live `<test-module>`. After any edit to samples or the manifest,
recompile before re-running (`-o` must not already exist — delete the old model or compile to a
fresh directory). `go` must be on PATH. If it won't build, fix the module's samples or `go.mod`
before handing off

## Output

- The compiled model `<test-compiled>` plus the module sources `<test-module>` (samples + `rule-test.yaml`); report the paths and the exact `compile` command used
- The tracking file's `test_project` stage marked done (see Tracking)

## Tracking

In `<tracking-file>`, set only the test-project stage (`in_progress` while building, `done` once it compiles):

```yaml
stages:
  test_project: done
```

Do not touch other stages or fields

## Gotchas

- One verdict per sample function; the `Positive`/`Negative` name is the verdict — don't mix
- A positive must route the helper source into the real sink — a sink fed a constant or a bare parameter with no in-sample source can't be flagged by a taint rule
- The function full name in `rule-test.yaml` is `import-path.FuncName` (the directory path, e.g. `test/security/all-patterns.Foo`), not the Go `package` name (`allpatterns`)
- A name that resolves to no function is fatal to the **whole run**, not just that sample: resolution is an exact `fullName` match with no fuzzy fallback, and one unresolved entrypoint (a typo, wrong case, or wrong import path) aborts every test with an opaque analyzer exception and no per-sample results — not a single false negative. After `compile`, verify every name matches a compiled function before `test rule run`
- `go` not on PATH → the compile step fails; install the toolchain
- Keep the `go.mod` `go` directive (and each stub's) at or below the installed toolchain version. Under the default `GOTOOLCHAIN=auto`, a directive newer than the installed `go` makes it try to **download** a matching toolchain, which fails in an offline or sandboxed build; pin to a version the running `go` already satisfies (the shared module tracks `go 1.22`)
- One module serves every Go rule test, so parallel agents share `go.mod`, the sample packages, and `rule-test.yaml` — coordinate so they don't clobber each other. Give each rule its own category dir/package, keep `rule-test.yaml` edits append-only (add your rule-id block; don't rewrite others'), and don't concurrently edit a shared helper file or the same `require`/`replace` lines
- Keep `.go` and YAML comment-free in produced samples and manifest entries
