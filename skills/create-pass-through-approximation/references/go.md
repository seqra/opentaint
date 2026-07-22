# create-pass-through-approximation — Go

Go has only this one approximation kind — there is no dataflow approximation to fall back on.

## Workflow

### 1. Read the method's source

Go dependencies ship as source, not bytecode. An application-internal function sits in the project's own sources under the project root. A dependency's source is in the module cache (`$(go env GOMODCACHE)/<module>@<version>/…`) or in `vendor/<import-path>/` when the project vendors; standard-library code is under `$(go env GOROOT)/src/<import-path>/`. `go doc <import-path>.<Name>` and `go doc -src <import-path>.<Name>` resolve a name without hunting for the file.

The plan's `method` names the callee — `<import-path>.<Name>` for a plain function, `(<recv-type>).<Name>` for a method — and its `signature` is only `args:<arity>`; the `function:` matcher below is built from the `method` string, never from `signature`.

### 2. Write the config

Each file opens with a `language: go` header line above `passThrough:` — without it, or with a mismatched one, the loader silently skips the whole file: no load error, and every function in it stays dropped. Below it, a config is one top-level `passThrough` list, one entry per `function` with its `copy` edges.

Positions (the base of any `from`/`to`)
- `this` (the receiver, methods only), `result`, `arg(0)`, `arg(1)`, …
- `result(N)` — Go returns multiple values; address them by index, `result(0)`, `result(1)`
- `[*]` — slice/array element; as a list item it must be quoted (`- '[*]'`), since unquoted it parses as a YAML alias and fails to load

Access-path modifiers (list form `[<base>, <modifier>, …]`)
- A list is ALWAYS `[<base>, <modifier>, …]` — element 0 is the base position, every later element is a modifier. It is never a list of destinations: to send one source to several destinations, write one `copy` edge per destination
- `.<package>.<Type>#<field>` — a struct field or a virtual slot. The slot name is nominal — the engine never resolves it, so it need not be a real field
- `<element>` — a container's element slot; `<value>` and `<key>` are accepted aliases and all three collapse to the same single accessor (key and value are not distinguished)
- `<deref>` — a pointer's pointee
- there is no `.*` all-fields wildcard — always name an explicit field or slot

Function matching — the structured block only:

```yaml
function:
  package: net/http    # the import path
  type: Request        # the receiver type, methods only, leading '*' stripped
  name: FormValue
  receiver: true       # false for a package-level function
```

Go has no overloads, so there is no `signature` key and no overload selection. There are no `overrides` and **no `condition:` support** — the loader parses only `function`/`copy`/`from`/`to` and the position modifiers, so `condition`, `typeIs`, `isConstant` and friends do not load.

Simplest form — a direct copy from one position to another:

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

Multiple return values — one edge per tainted return position:

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

Virtual slot — when data lives in a struct between calls, the writer and the reader route through an access path. Both must name the **identical** `package.Type#field` accessor, or the taint drops:

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

### 3. Re-check your configs

Beyond the body's checks, confirm the file still opens with `language: go` and that each matcher's `package`/`type`/`name`/`receiver` matches the `method` string it came from.

## Verification is the scan

There is no test project for a passThrough. The project scan applies the config and the scan agent reports back; the failure shapes map to distinct causes:

- *every* function in the file still dropped, with no load error → the whole file was silently skipped: check the `language: go` header
- a *single* function still dropped → the `function` matcher didn't match (check `package`, `type`, `name`, `receiver`), or `from`/`to` doesn't land on the tainted position
- the method is no longer dropped but the flow still doesn't surface → most often a broken channel: writer and reader naming different `package.Type#field` accessors
- a load / parse error → fix the YAML

After ~2 fix rounds with matcher fields and accessors verified and the method no longer dropped, stop guessing: Go has no dataflow fallback, so a propagation a passThrough genuinely can't express is an engine issue — report non-convergence for escalation to debug-rule / report-analyzer-issue.

## Gotchas

- User passThroughs **EXTEND** (concatenate with) Go's built-in configs — both your rule and any built-in matching the same function apply; there is no override. Check `approximated-external-methods.yaml` before modeling so you don't redundantly re-model something already covered
- The engine is field-sensitive: route data field-to-field as the source does rather than tainting the whole struct
