---
name: create-pass-through-approximation-go
description: Model a Go library function's taint propagation as a passThrough approximation config. Use for a dropped external Go method whose propagation is simple copying
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Create PassThrough Approximation (Go)

Write passThrough propagation rules for external Go functions and methods. Go has only this
one approximation kind — there is no dataflow approximation

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Methods to model `<methods>` — the target function(s) and what each propagates, from the tracking file's `methods` (each a `{package, name, type, receiver}` matcher)
- Tracking file `<tracking-file>` — the passThrough approximation unit. Default: `.opentaint/tracking/approximations/<name>.yaml`
- Config output `<config-file>` — where to write the passThrough approximation. Default: `.opentaint/pass-through/<name>.yaml`
- Test model `<test-model>` (optional) — any compiled model to dry-run the config against for a load/parse check. Default: `.opentaint/project` if it exists, else a `.opentaint/test-compiled/go` model

## Workflow

### 1. Write the passThrough config

Every config file MUST begin with a `language: go` header on its own first line, above
`passThrough:`. The loader keys on it: a file with no `language:` header — or a mismatched
one — is silently dropped whole, with no load error, so the passThrough never applies and
every function you modeled stays dropped

Each entry has a structured `function:` matcher and a list of `copy:` rules. The matcher
names the Go function by `package`, `name`, `type` (the receiver type, methods only), and
`receiver` (true for a method, false for a package-level function):

```yaml
language: go
passThrough:
- function:
    package: net
    name: JoinHostPort
    receiver: false
  copy:
  - from: arg(0)
    to: result
  - from: arg(1)
    to: result
- function:
    package: net
    type: IPConn
    name: ReadFromIP
    receiver: true
  copy:
  - from: this
    to: arg(0)
```

Multiple return values are addressed by index — `result(0)`, `result(1)`:

```yaml
language: go
passThrough:
- function:
    package: net
    name: SplitHostPort
    receiver: false
  copy:
  - from: arg(0)
    to: result(0)
  - from: arg(0)
    to: result(1)
```

### 2. Object-carried taint — field accessors

When taint rides inside a struct between calls, route the copy through an access path:
a list `[<base>, .<package>.<Type>#<field>]`. The `<field>` is either a real struct field
or a virtual slot (a nominal name the engine doesn't resolve, conventionally `<element>` for
a container's contents). The writer and the reader must name the **identical**
`package.Type#field` accessor, or the taint drops:

```yaml
language: go
passThrough:
- function:
    package: container/list
    type: List
    name: PushBack
    receiver: true
  copy:
  - from: arg(0)
    to:
    - this
    - .container/list.List#<element>
- function:
    package: container/list
    type: List
    name: Front
    receiver: true
  copy:
  - from:
    - this
    - .container/list.List#<element>
    to:
    - result
    - .container/list.Element#Value
```

Position modifiers available on an access path: a field accessor `.<package>.<Type>#<field>`,
the container slot `<element>`, and `<deref>` for a pointer's pointee. Do not use a `.*`
all-fields wildcard — always name explicit fields or slots

### 3. Optional — dry-run the config for load errors

There's no dedicated load-check command. ONLY when invoked standalone — never under the
appsec-agent orchestrator, whose scan phase verifies the config — if a compiled `<test-model>`
is present you can catch YAML load/parse errors early with a quick scan applying the config
(this only proves it loads, not that it propagates):

```bash
opentaint scan --project-model <test-model> \
  -o .opentaint/test-results/<name>/passthrough-loadcheck.sarif \
  --ruleset builtin \
  --passthrough-models <config-file>
```

A config error aborts the scan with the parse/load message — fix the YAML and re-run

### 4. Verification is the scan

There's no test project for passThrough. The main Go scan applies `<config-file>` and the scan agent reports back. You're re-invoked to fix the config when that scan shows:

- *every* function you modeled still in `dropped-external-methods.yaml`, with no load error → the whole file was silently skipped: check it starts with the `language: go` header (a headerless or mis-headered file loads to nothing)
- a *single* function you modeled still in `dropped-external-methods.yaml` → the `function` matcher didn't match (check `package`, `type`, `name`, `receiver`), or the `from`/`to` doesn't land on the tainted position
- the flow still doesn't surface though the method is no longer dropped → most often a broken channel: the writer and reader name different `package.Type#field` accessors
- a config load / parse error → fix the YAML

### 5. When the config won't converge

After ~2 fix re-invocations without a clearer cause — matcher fields and `from`/`to` checked,
writer/reader accessors confirmed identical, the modeled method no longer dropped, but the
scan still doesn't surface the flow — don't keep guessing. Go has no dataflow-approximation
fallback: a propagation a passThrough genuinely can't express is an engine issue. Report
non-convergence to the caller for escalation to debug-rule / report-analyzer-issue

## Output

- The passThrough config at `<config-file>`
- Tracking updated: `written` + `artifact` (per Tracking)
- Report the config path and the functions modeled

## Tracking

In `<tracking-file>`, once the config is written:

```yaml
artifact: .opentaint/pass-through/<name>.yaml
stages:
  written: done
```

Do not touch other stages or fields

## Reference

Position bases
- `this` (receiver, methods only), `result`, `result(N)` (return index), `arg(0)`, `arg(1)`, …
- `[*]` — slice/array element; as a list item it must be quoted (`- '[*]'`) — unquoted it parses as a YAML alias and fails to load

Access-path modifiers (list form `[<base>, <modifier>]`)
- `.<package>.<Type>#<field>` — a struct field or virtual slot; the slot name is nominal (use the real field, or `<element>` for container contents)
- `<element>` — container element slot; `<value>` and `<key>` are accepted aliases and all three collapse to the same single element accessor (key and value are not distinguished)
- `<deref>` — a pointer's pointee

Function matching — the structured `function: {package, name, type, receiver}` block. `type` is the receiver type (methods only); `receiver: false` for package-level functions

## Gotchas

- Go passThrough has **no `condition:` support** — the loader parses only `function`/`copy`/`from`/`to` and position modifiers. Don't write `condition`, `typeIs`, `isConstant`, etc.; they won't load
- User passThroughs **EXTEND** (concatenate with) Go's built-in configs — both your rule and any built-in matching the same function apply, there's no override. Check `approximated-external-methods.yaml` before modeling so you don't redundantly re-model a stdlib/library function that's already covered
- The `#` comments in the examples here are for you — keep produced YAML comment-free
- A wrong argument position copies the wrong value — point `from`/`to` at the tainted one
- In doubt about how a function moves taint — which argument or field reaches the result — read the package source or docs rather than guessing
- Model one function per matcher — don't try to cover many functions with one rule; write an explicit `function:` per method, and never the `.*` wildcard accessor
