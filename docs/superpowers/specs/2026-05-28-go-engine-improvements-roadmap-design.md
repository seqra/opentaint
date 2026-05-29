# Go engine improvements — roadmap design

## Goal

Steer Go analyzer engine development by working pattern-by-pattern from OWASP-Java-converted miss patterns: each pattern has a sample, the engine's actual per-instruction fact trace, the issue, the proposed fix, and the post-fix expected trace. Engine work lands one pattern at a time with the regression test as its gate.

## Architecture — three deliverables

**A. Engine-regression test samples + paired Kotlin tests.** New `*.go` files in `core/samples/src/main/go/` (one per pattern) and `*Test.kt` files in `core/src/test/kotlin/org/opentaint/go/sast/dataflow/`. Convention: paired `001T`/`002F` per pattern. Patterns whose fix relies on bundled rules (`GoConfigLoader.getConfig()`) override `commonPassRules` to opt in — by design `AnalysisTest` disables bundled config. Commit `756edd67` lands the samples and tests.

**B. Per-statement fact dump.** Two layers:

- **Test-side `printFactsAt(entryPoint)`** in `AnalysisTest.kt` (commit `756edd67`). Mirrors the JVM `JIRTaintAnalyzer.statementsWithFacts()` query: walks `ifdsEngine.allUnits()` → `findUnitRunner` → `collectAllIntraProceduralFacts`. Dumps facts per `(blockIndex, index)` to stdout and to `/tmp/go-engine-roadmap-facts/<entrypoint>.txt`. Used to produce every "current fact annotations" block in this spec.
- **CLI-side `--debug-fact-reachability-sarif` port.** Same query API, SARIF output, plumbed from `AbstractAnalyzerRunner` → `GoProjectAnalyzer`. Mirror `JIRTaintAnalyzer.statementsWithFacts(): Map<CommonInst, Set<FinalFactAp>>` at `JIRTaintAnalyzer.kt:262-276`. Generator modelled on `DebugFactReachabilitySarifGenerator.kt:16-74`. No flow-function instrumentation. Still TBD; the test-side helper covers the test workflow for now.

**C. Per-pattern engine roadmap.** The pattern sections below. Each names the concrete change site and either references a Java analog or names the new mechanism. Sections begin with the empirical engine state (PASS / FN) determined from the per-instruction fact trace in the sample.

## Annotation notation

The fact dumps below come directly from `printFactsAt`. Each line is one IR instruction:

```
L<line> [<blockIndex>:<index>]  <ssa form>      facts: <comma-separated FinalFactAp.toString()>
```

`var(N)![taint].$` is a FinalFactAp at access-path `var(N)` with the `taint` mark. Index `N` is the SSA local-variable slot (not the Go source variable name — multiple SSA temporaries can derive from one Go variable). `var(N).f` is a field accessor; `var(N)[*]` is "any element" of a map/slice.

When a sample is followed by an inline trace, the trace is the verbatim output of `printFactsAt(...)` against the current engine. Instructions with empty fact sets are omitted by the dump — silence means the engine carries no fact at that instruction. A pattern is FN when the dump shows no fact reaching the Sink-call's argument.

Critical invariant repeated from the engine semantics: `FactTypeChecker` (the JVM `filterFactBaseType` mechanism) only DROPS facts. Every fix in this document is a fact-generator, never a fact-filter.

## Empirical baseline (run on commit `756edd67`)

Of the seven patterns originally hypothesised as engine gaps, only four are actually FN. The other three already work today:

| Pattern | Sample entry | Status | Lever |
|---|---|---|---|
| 1 | `stringsBuilderWrite001T` | **FN** | bundled config missing for `strings.Builder` |
| 2 | `containerListPushFront001T` | **FN** | bundled `container/list` rules exist but `.<element>` accessor doesn't reach `e.Value` read |
| 3 | `atomicValueLoad001T` | PASS | bundled `sync.atomic` rules + loader fix already cover Store/Load |
| 4 | `typeAssertOn{MapElem,FieldRead,CallResult}001T` | PASS (all 3) | type-assert arm already emits a fact at LHS when the operand carries one |
| 5 | `typeSwitchBinding001T` | **FN** | tuple extract works; outer-var reassign inside the case body doesn't carry the fact out |
| 6 | `nestedNamedDeep001T` | **FN** | deep nested NAMED-field chain dies after first address-of |
| 8 | `ptrNewWriteAliasRead001T` | PASS | simple forward dataflow handles `*p2 = data; p1 = p2; *p1` without alias analysis |

Patterns 3, 4, 8 are kept as regression guards — their samples and tests stay in-repo so a future engine change can't silently break them. Patterns 7 (embedded promoted field), 9 (closure return), 10 (higher-order param) remain deferred per prior decision — major changes, addressed only after the simpler FNs land.

The four engine-roadmap items follow.

---

## Pattern 1 — `strings.Builder` round-trip (FN)

### Sample (`core/samples/src/main/go/stdlib_strings_builder.go`)

```go
func stringsBuilderWrite001T() {
    data := util.Source()
    b := strings.Builder{}
    b.WriteString(data)
    out := b.String()
    util.Sink(out)
}
```

### Current fact trace (from `printFactsAt`)

```
L12 [0:1]  new strings.Builder  // b                  facts: var(0)![taint].$
L14 [0:3]  (*strings.Builder).String(b)               facts: var(0)![taint].$
```

Only two instructions surface facts. `var(0)` is the source local `data`. `WriteString` and the Sink call are silent — engine carries no fact through them.

### Issue

No bundled rule for `(*strings.Builder).WriteString` / `.Write` / `.WriteByte` / `.WriteRune` / `.String`. After commit `6c7fe566`'s `GoConfigLoader` fix, receiver-method rules with `from: arg(0), to: this` / `from: this, to: result` patterns DO load — but the `strings.Builder` type isn't in any YAML at all. The engine sees `WriteString` as an opaque external call and treats the receiver as unmodified.

### Proposed approach

Pure rule-level. Add a new `core/opentaint-config/go-config/config/go-config/strings.builder.yaml`:

```yaml
passThrough:
  - function: { package: strings, type: Builder, name: WriteString, receiver: true }
    copy: [{ from: arg(0), to: this }]
  - function: { package: strings, type: Builder, name: Write, receiver: true }
    copy: [{ from: arg(0), to: this }]
  - function: { package: strings, type: Builder, name: WriteByte, receiver: true }
    copy: [{ from: arg(0), to: this }]
  - function: { package: strings, type: Builder, name: WriteRune, receiver: true }
    copy: [{ from: arg(0), to: this }]
  - function: { package: strings, type: Builder, name: String, receiver: true }
    copy: [{ from: this, to: result }]
```

Loader fix (commit `6c7fe566`) already emits both `(strings.Builder).WriteString` and `(*strings.Builder).WriteString` matchers per rule, so value-receiver and pointer-receiver calls both fire.

### Expected post-fix trace

```
L12 [0:1]  new strings.Builder  // b                  facts: var(0)![taint].$
L13 [0:2]  (*strings.Builder).WriteString(b, data)    facts: var(0)![taint].$, var(1)![taint].$
L14 [0:3]  (*strings.Builder).String(b)               facts: var(0)![taint].$, var(1)![taint].$, var(2)![taint].$
L15 [0:4]  util.Sink(out)                             facts: var(2)![taint].$
```

`var(1)` is the Builder receiver, tainted after `WriteString`. `var(2)` is `out`, tainted after `String()`. Sink reaches.

### Deep feature description

Add the YAML. No engine changes. Re-enable `Pattern01StringsBuilderTest.stringsBuilderWrite001T` (remove `@Disabled`). Verify by re-running `printFactsAt` on the same entry point — trace should match the expected post-fix trace.

---

## Pattern 2 — `container/list` PushBack + Front + Value (FN)

### Sample (`core/samples/src/main/go/stdlib_container_list.go`)

```go
func containerListPushFront001T() {
    data := util.Source()
    l := list.New()
    l.PushBack(data)
    e := l.Front()
    v := e.Value.(string)
    util.Sink(v)
}
```

### Current fact trace (full, with bundled config opt-in)

```
L26 [0:0]  Source()                                   facts: ∅
L27 [0:1]  container/list.New()                       facts: var(0)![taint].$
L-1 [0:2]  makeinterface(data)                        facts: ∅
L28 [0:3]  (*container/list.List).PushBack(l, data)   facts: var(2)![taint].$
L29 [0:4]  (*container/list.List).Front(l)            facts: var(2)![taint].$
L30 [0:5]  &e.Value                                   facts: ∅
L30 [0:6]  *&e.Value                                  facts: ∅
L30 [0:7]  result.(string)                            facts: ∅
L31 [0:8]  util.Sink(v)                               facts: ∅
```

`var(2)` is the boxed-interface argument (`makeinterface(data)`) staying live across PushBack/Front. The list RECEIVER never gets tainted — no `this`-rooted or `<element>`-rooted fact appears. After Front no fact survives into the `e.Value` read.

### Issue — confirmed loader bug (Go pseudo-accessors unparsed)

The bundled `container.list.yaml` rules model the list element via field modifiers:

```yaml
- function: { package: container/list, type: List, name: PushBack, receiver: true }
  copy:
    - from: arg(0)
      to: [this, ".container/list.List#<element>"]
    - from: arg(0)
      to: [result, ".container/list.Element#Value"]
```

Confirmed root cause (by code inspection): the Field modifier deserialiser `fieldMatcher = Regex("""\.(.*)#(.*)#(.*)""")` (`SerializedPosition.kt:153`) requires THREE `#`-separated parts (`className#fieldName#fieldType`). Both `to` modifiers here have only ONE `#` (`.container/list.List#<element>` and `.container/list.Element#Value`). The regex `matchEntire` fails → `PositionModifier.deserialize` throws → `GoConfigLoader.parseGoPositionModifier` swallows it via `runCatching` → returns `null` → in `toPositionBaseWithModifiers`, `mods.size != strings.size - 1` so the whole position returns `null` → `toPassAction` returns `null` → both copy actions drop → `actions.isEmpty()` → the entire PushBack rule is dropped. The list element is never modelled.

The scope is broader than `container/list`. A sweep of the bundled go-config (`grep -hE '^\s*-?\s*\.[^#]+#' *.yaml | grep -vE '#.*#'`) finds two-part modifiers in `container.list.yaml`, `container.heap.yaml`, `sync.yaml`, and `builtin.yaml`:

```
.container/heap.Interface#<element>
.container/list.Element#Value
.container/list.List#<element>
.<map>#<key>
.<map>#<value>
.<pointer>#<deref>
.sync.Pool#<element>
```

These are Go-flavoured SEMANTIC pseudo-accessors emitted by the Go config generator — not malformed three-part fields. They have no JVM `PositionModifier` equivalent and must be mapped to the engine's accessor vocabulary:

| Go pseudo-accessor | Engine accessor |
|---|---|
| `.<map>#<key>` | (map key — model as `ElementAccessor`, or skip; keys rarely sink) |
| `.<map>#<value>` | `ElementAccessor` |
| `.<pointer>#<deref>` | identity (deref is modelled as `Access.Simple`, no accessor) |
| `.container/list.List#<element>`, `.sync.Pool#<element>`, `.container/heap.Interface#<element>` | `ElementAccessor` (container element) |
| `.container/list.Element#Value` | `FieldAccessor("container/list.Element", "Value", <fieldType>)` — must match the real read accessor |

### Proposed approach

Not a pure-YAML edit. Extend `GoConfigLoader.parseGoPositionModifier` to recognise the Go pseudo-accessor forms and map each to the right `PositionModifier`/accessor:

- `<map>#<value>`, `Type#<element>` (any container element) → `ArrayElement` (= `ElementAccessor`)
- `<pointer>#<deref>` → drop the modifier (identity; deref carries the whole-value fact)
- two-part `Type#field` where `field` is a real field name → a `Field` modifier; the missing `fieldType` is the problem — the engine's `FieldAccessor` equality includes `fieldType`, so `container/list.Element#Value` must resolve to the SAME `fieldType` the read site produces (`interface{}` for `Element.Value`). Either (a) make `FieldAccessor` equality ignore `fieldType`, or (b) have the loader fill a wildcard the engine treats as "any type". Decide via the diagnostic — check what `fieldAccessorFromAddr` produces for the real `e.Value` read and match it.

Confirm the round-trip end-to-end with `printFactsAt` on `containerListPushFront001T` after the loader change: PushBack should taint `l[*]` (element), Front should copy it to `result.Value`, and the `e.Value` read should pick it up.

### Expected post-fix trace

```
L27 [0:1]  container/list.New()                       facts: var(0)![taint].$
L28 [0:3]  PushBack(l, data)                          facts: var(2)![taint].$, var(1).<element>![taint].$
L29 [0:4]  Front(l)                                   facts: ..., var(3).Value![taint].$
L30 [0:5]  &e.Value                                   facts: ..., var(4)![taint].$
L30 [0:7]  result.(string)                            facts: ..., var(5)![taint].$
L31 [0:8]  util.Sink(v)                               facts: ..., var(6)![taint].$
```

### Deep feature description

Extend `core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt:parseGoPositionModifier` to recognise the Go pseudo-accessor forms per the mapping table above, before the existing `PositionModifier.deserialize` fallback. After loading, the PushBack rule taints `l[*]` (element); Front copies `this[*]` to `result.Value`; reading `e.Value` produces a fact (the existing FieldRef arm handles the read once the `.Value` fact exists); the `.(string)` assert composes (Pattern 4 path). Add a `GoConfigLoaderTest` assertion that the `container/list` PushBack rule survives loading with non-empty `copy`. Re-enable `Pattern02ContainerListTest.containerListPushFront001T`. If the FieldRef read at `e.Value` still yields nothing after the loader fix, that residual is the same store-back/field-read mechanism as Pattern 6 — consolidate there.

---

## Pattern 5 — Type-switch result merged via SSA phi (FN)

### Sample (`core/samples/src/main/go/type_ops.go`)

```go
func typeSwitchBinding001T() {
    var obj interface{} = util.Source()
    dir := "safe"
    switch v := obj.(type) {
    case string:
        dir = v
    }
    util.Sink(dir)
}
```

### Current fact trace (full)

```
L191 [0:0]  Source()                                  facts: ∅
L-1  [0:1]  makeinterface(obj)                        facts: var(0)![taint].$
L194 [0:2]  obj.(string),ok                           facts: var(1)![taint].$
L-1  [0:3]  extract #0  (binding v)                   facts: var(2)![taint].$
L-1  [0:4]  extract #1  (ok bool)                     facts: ∅
L-1  [0:5]  if (ok) then inst#9 else inst#6           facts: ∅
L192 [1:6]  phi(5: "safe", 9: %3:t3)  // dir          facts: ∅
L197 [1:7]  util.Sink(dir)                            facts: ∅
L-1  [1:8]  return                                    facts: ∅
L-1  [2:9]  jump inst#6                               facts: ∅
```

### Issue — confirmed SSA phi-node propagation gap

Correction of the earlier hypothesis. The case binding `v` (extract #0, `var(2)`) IS correctly tainted. `dir = v` does NOT lower to a store — it lowers to the SSA phi at `[1:6]`: `%6:t5 = phi(5: "safe", 9: %3:t3)`. Control flow: block 0 runs the type-assert + extracts, then `if (ok) then inst#9 else inst#6`; the `ok` edge goes through block 2 (`jump inst#6`) carrying `dir = v = %3:t3` (tainted), the `!ok` edge falls to inst#6 carrying `dir = "safe"`. The phi at `[1:6]` merges these two definitions of `dir`. One incoming operand (`%3:t3`) carries `var(2)![taint]`, yet the phi result yields ∅.

Root cause: the engine's phi handling does not propagate a fact from a tainted incoming operand to the phi result. This is fact-generating work (the phi must CREATE a fact on its result), not filtering.

### Proposed approach

Add a phi arm to `GoMethodSequentFlowFunction` (or wherever `GoIRPhiInst` / the merge instruction is handled): when any incoming operand of a phi carries a fact, emit a corresponding fact on the phi result, rebased onto the result's access-path base. Standard SSA-phi taint handling. Confirm the IR node type by grepping the Go IR for the phi instruction class used in the trace (`phi(...)`).

### Expected post-fix trace

```
L-1  [0:3]  extract #0  (binding v)                   facts: var(2)![taint].$
L192 [1:6]  phi(5: "safe", 9: %3:t3)  // dir          facts: var(6)![taint].$
L197 [1:7]  util.Sink(dir)                            facts: var(6)![taint].$
```

### Deep feature description

Locate the phi-instruction arm (or its absence) in `GoMethodSequentFlowFunction.kt`. For each incoming `(predecessorBlock, value)` pair where `value` carries a fact, generate a fact on the phi's result local. Because IFDS processes one edge at a time, the per-incoming propagation naturally unions across predecessors. Re-enable `TypeOpsTest.typeSwitchBinding001T`. This phi handling is general — it also benefits any `if/else`-merged taint, not just type-switch.

---

## Pattern 6 — Deep nested NAMED-field chain (FN)

### Sample (`core/samples/src/main/go/struct_ops.go`)

```go
type DeepL1 struct{ v string }
type DeepL2 struct{ n1 DeepL1 }
type DeepL3 struct{ n1 DeepL2 }
type DeepL4 struct{ n1 DeepL3 }

func nestedNamedDeep001T() {
    data := util.Source()
    o := DeepL4{n1: DeepL3{n1: DeepL2{n1: DeepL1{v: data}}}}
    util.Sink(o.n1.n1.n1.v)
}
```

### Current fact trace (full)

```
construction of o := DeepL4{n1: DeepL3{n1: DeepL2{n1: DeepL1{v: data}}}}:
L169 [0:0]  Source()  (data, %0)                      facts: ∅
L170 [0:1]  local DeepL4  // o (%1)                    facts: var(0)![taint].$
L170 [0:2]  %2 = &%1.n1   (&o.n1)                      facts: ∅
L170 [0:3]  %3 = &%2.n1   (&o.n1.n1)                   facts: ∅
L170 [0:4]  %4 = &%3.n1   (&o.n1.n1.n1)                facts: ∅
L170 [0:5]  %5 = &%4.v    (&o.n1.n1.n1.v)              facts: ∅
L170 [0:6]  *%5 = data    (store)                      facts: ∅
read of o.n1.n1.n1.v:
L171 [0:7]  %7 = &%1.n1   (&o.n1, fresh)               facts: var(4).v![taint].$
L171 [0:8]  %8 = &%7.n1                                facts: ∅
L171 [0:9]  %9 = &%8.n1                                facts: ∅
L171 [0:10] %10 = &%9.v                                facts: ∅
L171 [0:11] %11 = *%10                                 facts: ∅
L171 [0:12] util.Sink(%11)                             facts: ∅
```

### Issue — store does not propagate back to the root object

Correction of the earlier hypothesis (it is not "the read side fails to compose accessors"). The store `*%5 = data` writes through the deepest field-address temporary, and the engine records the resulting fact on the INTERMEDIATE TEMPORARY `%4` as `var(4).v` (i.e. relative to `&o.n1.n1.n1`), NOT back on the root allocation `o` (`%1`) as `o.n1.n1.n1.v`. The construction lowered `o := DeepL4{...}` into a chain of address-of-field temporaries (`%2=&o.n1`, `%3=&%2.n1`, `%4=&%3.n1`, `%5=&%4.v`) followed by `*%5 = data`. When the store fires, the engine attaches the fact to the nearest enclosing temporary rather than walking the `&%X.field` chain back to `%1`.

The read side then re-derives addresses fresh from `%1` (`%7=&%1.n1`, …) — `%1`/`o` never received a fact, so the chain stays ∅. The `var(4).v` fact is live but stranded on dead temporary `%4`.

Per the user's invariant: there is no fact at the read site to filter; the fix must CREATE the fact on the root object at store time.

### Proposed approach

In the store arm of `GoMethodSequentFlowFunction.kt` (handling `*%addr = value` where the stored `value` carries a fact): resolve `%addr` back through the `&%X.field` chain to its root allocation and the accumulated field path, then emit the fact on `<root>.<accumulated-path>`. Here `%5 → &%4.v → &(&%3.n1).v → … → o.n1.n1.n1.v`. Walking the chain is a local def-use traversal of the address-producing instructions (each `&%X.field` records its base `%X` and field). This is the symmetric counterpart to the read side, which already composes `&%1.n1.n1.n1.v` correctly once a fact exists at `o`'s nested path.

### Expected post-fix trace

```
L170 [0:6]  *%5 = data    (store, resolved to o.n1.n1.n1.v)  facts: var(1).n1.n1.n1.v![taint].$
L171 [0:7]  %7 = &o.n1                                       facts: var(1).n1.n1.n1.v, var(7).n1.n1.v![taint].$
L171 [0:8]  %8 = &%7.n1                                      facts: ..., var(8).n1.v![taint].$
L171 [0:9]  %9 = &%8.n1                                      facts: ..., var(9).v![taint].$
L171 [0:10] %10 = &%9.v                                      facts: ..., var(10)![taint].$
L171 [0:11] %11 = *%10                                       facts: ..., var(11)![taint].$
L171 [0:12] util.Sink(%11)                                   facts: var(11)![taint].$
```

### Deep feature description

The fix is in the store-instruction arm of `GoMethodSequentFlowFunction.kt`. Add a helper `resolveAddressChain(addr): (rootBase, accessorPath)?` that walks back through `&%X.field` (address-of-field) and `&%X[i]` (address-of-element) producers to the root local, accumulating the accessor path. When storing a fact-carrying value through `addr`, emit the fact at `rootBase` + `accessorPath` instead of (only) the immediate temporary. Bounded by the def-use chain length, which is finite per SSA function. Re-enable `StructOpsTest.nestedNamedDeep001T`. The same store-back resolution unblocks the existing 2-level `nestedStructMod001T` (already `@Disabled`), feeds the residual half of Pattern 2's `e.Value` read if the config fix alone is insufficient, and is the substrate for Pattern 7's embedded-field rewrite.

---

## Regression-guard patterns (PASS today)

Kept in-repo as regression tests so an engine change can't silently break them. Trace excerpts retained in the corresponding `.go` files.

### Pattern 3 — `sync/atomic.Value`

`atomicValueLoad001T` PASSES. Bundled `sync.atomic.yaml` ships `(*Value).Store` (`from: arg(0), to: this`), `Load` (`from: this, to: result`), `Swap` (both directions). After commit `6c7fe566`'s loader fix, the receiver-method form `(*sync/atomic.Value).Store` and value-form `(sync/atomic.Value).Store` are both registered. The type-assert `.Load().(string)` composes with the existing type-assert arm. Sink reaches.

### Pattern 4 — Type-assert on chained expression (all three variants)

`typeAssertOnMapElem001T`, `typeAssertOnFieldRead001T`, `typeAssertOnCallResult001T` all PASS. The type-assertion arm of `GoMethodSequentFlowFunction` already emits a fact at the LHS when any fact reaches the operand's access path — whether the operand is a `MapElem` (`m[*]` fact survives the index read), a struct-field read (`b.iface` fact survives the FieldRef), or a call result (interproc fact from the passthrough). The earlier hypothesis that this needed a `.(T)` accessor was wrong — the existing implementation is fact-generating, just not via the route the original spec assumed.

### Pattern 8 — `new(T)` pointer chain (deref-write + alias + deref-read)

`ptrNewWriteAliasRead001T` PASSES. Simple forward dataflow at `*p2 = data; p1 = p2; out = *p1` carries the fact through. No alias analysis or DSU port needed. The trace shows the fact survives from the deref-write through the pointer-assignment and the deref-read. Confirms the user's earlier prediction.

---

## Deferred patterns (still not in scope)

**Pattern 7 — Embedded struct promoted field** (`embeddedField001T`/`embeddedDeep001T`/`embeddedMethod001T` already `@Disabled` in `EmbeddingTest`). Touches IR field-lookup + call resolver for method promotion; address after Pattern 6's mechanism is in.

**Pattern 9 — Closure returned from callee** (`closureReturn001T` already `@Disabled`). Interprocedural closure summarisation. Defer.

**Pattern 10 — Higher-order function parameter** (`higherOrder001T` already `@Disabled`). Call-site-specific resolution. Defer.

---

## `--debug-fact-reachability-sarif` CLI port (deliverable B, CLI half)

The test-side `printFactsAt` helper (commit `756edd67`) covers the test workflow. For verifying engine fixes on benchmarks and across engine versions, port the CLI half:

- CLI flag wiring: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/AbstractAnalyzerRunner.kt:44` already exposes `--debug-fact-reachability-sarif` into `DebugOptions.factReachabilitySarif`. Thread through `runGoProjectAnalysis` to `GoProjectAnalysisOptions`.
- Data collection: add `GoTaintAnalyzer.statementsWithFacts(): Map<GoIRInst, Set<FinalFactAp>>` mirroring `JIRTaintAnalyzer.statementsWithFacts()` (`JIRTaintAnalyzer.kt:262-276`).
- Plumbing in `GoProjectAnalyzer`: when the flag is set, post-analysis, call `analyzer.statementsWithFacts()` and pipe into a new `GoDebugFactReachabilitySarifGenerator`. Mirror `ProjectAnalyzer.kt:146-149` and `:213-223`.
- Emitter: model on `DebugFactReachabilitySarifGenerator.kt:16-74`. One SARIF result per `(statement, fact)`; ruleID `s_<index>`; message = fact string; location = statement file+line. Write to `result-dir/debug-fact-reachability.sarif`.
- Usage: `opentaint --experimental scan ... --debug-fact-reachability-sarif --rule-id <single-rule>`. SARIF is then diff-able across engine versions and pattern-fix-by-pattern-fix.

## Suggested implementation order

| # | Item | Engine work | Risk | Why this order |
|---|---|---|---|---|
| 1 | Pattern 1 (strings.Builder rules) | none — config only | low | Pure rule addition; trivial first-pattern landing |
| 2 | Pattern 2 (container/list) | small-medium — loader pseudo-accessor mapping | medium | Two-part Go pseudo-accessors (`<element>`/`<map>`/`<pointer>`) span 4 bundled configs; map each to an engine accessor in GoConfigLoader |
| 3 | Pattern 5 (type-switch SSA phi) | small — phi-instruction arm | medium | Confirmed phi-propagation gap; general (helps all if/else merges) |
| 4 | Pattern 6 (deep nested NAMED-field) | medium — store-back-to-root via address chain | medium | Substrate for the deferred Pattern 7; also residual of Pattern 2 |
| — | **Benchmark checkpoint** | — | — | Rerun `bash benchmarks/scan.sh` after Pattern 6 lands; record TP delta on both go-owasp + go-sec benchmarks against the 96.7% / 20.3% baseline |
| 5 | CLI port of `--debug-fact-reachability-sarif` | small — wiring only, no engine touch | low | Unblocks benchmark-side and cross-version verification |
| 6+ | Deferred: Patterns 7, 9, 10 | medium-to-large | medium | After every simpler FN lands |

### Benchmark checkpoint after Pattern 6

Patterns 1–6 are unit-level fixes verified by the `001T`/`002F` regression tests, but the real goal is benchmark TP. After Pattern 6 lands, rerun the full benchmark suite to confirm the unit fixes translate into recall gains:

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks && bash scan.sh
```

Baseline to beat (commit `f2dcb263`, engine before these fixes): go-sec-code-mutated **96.7%** TP (175/181), go-owasp-converted-mutated **20.3%** TP (30/148). Record the per-CWE breakdown from `compare.py` in the implementing PR. Patterns 1/2 (strings.Builder, container/list) and 5/6 (phi merge, deep struct) each map to mutation families seen in the owasp misses, so the owasp number is the one expected to move; sec should hold at or above 96.7%. If a fix lands with green unit tests but no benchmark movement, investigate whether the benchmark mutation differs from the isolated sample before declaring the pattern done.

#### Result (2026-05-28, after Patterns 1, 2, 5, 6 landed)

Both benchmarks improved, every CWE category up, no analyzer exceptions:

| Benchmark | Baseline | After 1/2/5/6 | Δ TP |
|---|---|---|---|
| go-sec-code-mutated | 96.7% (175/181) | **98.3% (178/181)** | +3 |
| go-owasp-converted-mutated | 20.3% (30/148) | **24.3% (36/148)** | +6 |

owasp per-CWE: CWE-22 27.0→**35.1%** (10→13 TP), CWE-78 20.8→**25.0%** (5→6), CWE-79 16.7→**18.8%** (8→9), CWE-89 17.9→**20.5%** (7→8).
sec per-CWE: CWE-78 90.8→**95.4%** (59→62 TP); CWE-22 and CWE-89 held at 100%.

The Pattern 6 store-back fix is the broadest contributor — it lands taint on nested struct/composite fields that recur across all four owasp CWE families. The remaining owasp gap is dominated by the still-deferred patterns (7 embedded promoted fields, 9 closures, 10 higher-order) plus interface-dispatch mutations not yet sampled.

## Testing strategy

Each pattern's test class lives in `core/src/test/kotlin/org/opentaint/go/sast/dataflow/`. The `001T` is the regression test; the `002F` confirms no false positive. The diagnostic class `EngineRoadmapDiagnosticTest` calls `printFactsAt` on every `001T` — re-run it after each engine fix to verify the post-fix trace matches the expected trace in the corresponding pattern section. When a fix lands, the implementer removes the `@Disabled` from the `001T` (which becomes a permanent regression guard), updates the pattern's "current fact trace" in this spec to the post-fix trace, and notes the resolution date.
