---
name: analyze-external-methods
description: Analyze and group an OpenTaint scan's dropped external methods and decide what to approximate or skip. Use when a dropped-external-methods.yaml needs turning into approximation targets
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Analyze External Methods

Read the methods where the analyzer lost track of the data, group them by library and kind, and record per group what to model and how — so the right skill can build each approximation

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Dropped methods `<dropped-file>` — methods where the analyzer dropped the data for lack of a model. Default: `.opentaint/results/dropped-external-methods.yaml`
- Tracking directory `<tracking-dir>` — where approximation tracking files are written. Default: `.opentaint/tracking`
- Project root `<project-root>` — sources and build files, to resolve which library owns each method. Default: current directory

## Workflow

Requires `<dropped-file>`, without it there's nothing to group

### 1. Group by package and kind

Every method in `<dropped-file>` is a place the data is lost for lack of a model — model all of them. First decide each method's kind:

- passthrough — data moves by a simple from→to copy: a getter, arg→result, builder, container field, collection `add`/`get`, `StringBuilder.append`, `Stream.collect`
- dataflow — data flows through a lambda/callback/functional interface or an async chain

Group by package AND kind — one tracking file per (package, kind): `<package-kebab>-passthrough.yaml` for the simple copies, `<package-kebab>-dataflow.yaml` for the lambda/callback/async ones. `<package-kebab>` is the dotted Java package with `.` replaced by `-` (e.g. `reactor.core.publisher` → `reactor-core-publisher`) so it's filesystem-friendly; the YAML `package:` field keeps the real dotted name. Kind is the only split (no finer sub-groups). Each unit is one agent's work

### 2. Flag methods to skip

The one exception: a few methods the engine asks about don't affect the data flow — logging, metrics (e.g. `org.slf4j.Logger#info`). List those in `skipped.yaml` instead of an approximation group; the default call-to-return behavior is already correct for them

## Output

- One `<tracking-dir>/approximations/<package>-<kind>.yaml` per (package, kind), with `stages.description: done` and its `methods` (each `target` + `type`); a dataflow unit also carries `dependencies` (the library's exact Maven GAV its test project needs)
- `<tracking-dir>/approximations/skipped.yaml` listing the skip methods
- A brief summary to the caller: one line per unit (package, kind, method count) plus the skip count. Don't paste the method lists back — the tracking files hold them

## Tracking

Create one file per (package, kind); fill only the discovery-stage fields. The two kinds differ — passThrough is written and verified by the scan, dataflow is built and tested on a test project:

```yaml
# <package-kebab>-passthrough.yaml — simple copies, no test project
package: com.foo
artifact: null
stages:
  description: done
  written: pending
notes: >
  DTO getters returning fields that carry the data
methods:
  - target: "com.foo.Wrapper#getValue"
    type: passthrough
```

```yaml
# <package-kebab>-dataflow.yaml — lambda/callback/async, tested on a test project
package: com.foo
artifact: null
dependencies:                 # exact GAV the test project needs, from the build files
  - com.foo:foo-core:1.2.3
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  Reactor operators carrying data through the mapper
methods:
  - target: "com.foo.Reactor#flatMap"
    type: dataflow
```

```yaml
# skipped.yaml — engine asks to approximate these, but they don't affect the data flow
methods:
  - "org.slf4j.Logger#info"
  - "org.slf4j.Logger#debug"
```

## Gotchas

- Model every method in `<dropped-file>` — each is a real place the data is lost; don't second-guess the list. The only exceptions are the obvious methods that don't move data, which you move to `skipped.yaml`
- Approximate only external library methods — never an application-internal class. If one shows up as a candidate, drop it
- One file = one (package, kind) = one agent: passThrough and dataflow go in separate files; never put a method in two, or two agents collide
