# Go FN Cluster A / C — fix proposals

Diagnosis + fix-proposal document for the confirmed false-negative (FN) clusters
surfaced during the Go semgrep-rule benchmark. This document covers **Cluster A**
(source-shape matching) and **Cluster C** (dataflow-engine propagation gaps).

Method (mandatory order): for each FN we first dumped the produced
`GoSerializedItem` (via `TaintRuleFromSemgrep.toGoSerializedTaintConfig()`) to
separate a **rule-translation** bug from an **engine** bug, and only dropped to a
full per-statement fact dump for cases where the serialized source rule was
present and correct but still failed to propagate. Cluster A turned out to be
diagnosable entirely from the serialized output plus the engine's source-rule
application code — see each subsection.

## Combined fix ranking (by estimated FN recovery)

Seven shapes were reproduced; three turned out NOT to be FNs (already handled —
kept as regression guards), correcting the triage's per-shape attribution. The
actionable work is **one rule-layer fix with two facets** — the `$R.Field`
field-read source (A.1), reused for map-index reads (A.2/A.3) by tainting the
element position `result.[*]` and letting the existing lookup read propagate —
plus **one large engine fix**, the non-local closure (C.1), built on the JVM
type-info/`tryExtractLambdaType` blueprint in its own round.

| Rank | Shape | Cluster | Kind | Status | Est. FN recovery | Risk | Notes |
|---|---|---|---|---|---|---|---|
| 1 | `$R.Field` field-read source (A.1) | A | rule-translation (+ engine source path) | **ready** | 14 | medium | the shared Cluster-A mechanism; RawQuery recovered by tainting `result` (whole) |
| 2 | map-index reads (A.2+A.3) | A | **A.1 mechanism + `[*]` taint position** | **ready** | 19 (9 Header + 10 Form) | low | field-read source taints `result.[*]`; the existing `GoIRLookupExpr` read strips `[*]` onto the value — NO new rule kind, NO engine change |
| 3 | closure capture / higher-order (C.1) | C | engine | **own round** | ~41 | high | largest payoff; build on the JVM type-info-fact + `tryExtractLambdaType` blueprint (see C.1); also re-enables `closureReturn`/`higherOrder` |
| — | nested-struct constructor (C.2) | C | NON-FN | guard | 0 | — | already handled; regression guard |
| — | interface laundering, concrete + iface-var (C.2) | C | NON-FN | guard | 0 | — | already handled; regression guard |
| — | beego `Ctx.Input.Query` | A | NON-FN (minimal stand-in) | guard | 0 | — | minimal shape matches; real benchmark beego FNs may need real beego types (out of scope) |

Total potential recovery once all fixes land: **~74 FNs** (~41 + 14 + 19),
spanning Cluster A (33) and the closure portion of Cluster C.

**Implementation order:**
1. **A.1 field-read source** — the self-contained rule-translation + engine-source-path fix (`$R.Field` → source at `result`).
2. **A.2/A.3 map-index** — author the `$R.Header`/`$R.Form` field-read sources with a `result.[*]` (ArrayElement) taint position; the existing `GoIRLookupExpr` element read carries it. No new rule kind, no engine change — rides entirely on A.1 + existing propagation.
3. **C.1 closure** — its own focused round on the JVM blueprint (type-info-style closure-identity fact + fact-driven `resolveDynamic` + `JIRLambdaTracker`-style subscription).

---

## Cluster A — source-shape matching

Three reproductions, all under
`core/opentaint-go-querylang/samples-go/`. Each sample's `Positive_*` entry is
currently `@Disabled` in
`core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt`.

**Shared root cause.** Go taint sources are matched almost exclusively as
*method calls*. There are exactly two fact-generating source paths in the engine:

1. **Call-site sources** — fire when a callee qualified name matches a
   `GoSerializedRule.Source.function` matcher (the `.Get(...)`, `.Query(...)`,
   `util.Sink(...)` style).
2. **Global-read sources** (`GoSerializedGlobalSource`) — fire on an
   *assignment whose RHS is a package-level global read*
   (`os.Args`, etc.), detected by
   `GoMethodSequentFlowFunction.detectGlobalReadName`
   (`core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/analysis/GoMethodSequentFlowFunction.kt:460`),
   which keys strictly off `GoIRGlobalValue.global.fullName`.

A *field read on a value* (`r.URL.RawQuery`), or a *map-index read on a struct
field* (`r.Header["X-Test"]`, `r.Form["X-Test"]`), is **neither** a call **nor**
a package-level global. The rule-translation layer
(`PatternToActionListConverter`) only knows how to lower a field/selector
pattern into a *global read* when the receiver is a package identifier
(`pkg.Field`); a metavar-rooted field read (`$R.Field`) is dropped. And even if
the converter emitted a source for it, the engine has no zero-to-fact path that
fires on a `GoIRFieldExpr` / `GoIRLookupExpr`. So both layers need work.

Per-sample detail below.

> Note on `SourceBeegoCtxInput`: this is **not** an FN with the minimal
> stand-in. The rule's source `$X.Query($K)` is a method call, so it lowers to a
> normal call-site source `Source(function=Pattern((.*\.)?Query), …)` and the
> `Positive_ctx_input` entry (`c.Ctx.Input.Query("X-Test")`) reports. Its
> `GoSampleBasedTest` entry is left enabled. The benchmark's 3 beego FNs likely
> depend on the real beego types / method receivers rather than this minimal
> reproduction — out of scope here.

---

### A.1 — `r.URL.RawQuery` (string field read)

**1. Test case.**
`core/opentaint-go-querylang/samples-go/SourceUrlRawQuery/` —
`Positive_rawquery` reads `s := r.URL.RawQuery` then `Sink(s)`. Reproduced by
`GoSampleBasedTest.sourceUrlRawQuery()`, currently
`@Disabled("Cluster A: r.URL.RawQuery source not matched — see fix proposal")`.
Rule pattern-source: `$R.URL.RawQuery`.

**2. Description.**
Serialized config (verbatim):

```
source:       []
sink:         [Sink(function=Pattern(regex=(.*/)?\Qutil\E\.\QSink\E), condition=NumberOfArgs(n=1), trackFactsReachAnalysisEnd=null, id=rule.yaml:source-url-rawquery, meta=GoSinkMetaData(message=Taint from r.URL.RawQuery reaches Sink, severity=Warning, cwe=null), info=null), Sink(...)]
globalSource: []
```

The source list is **empty**. No source rule of any kind was produced for
`$R.URL.RawQuery`; only the `util.Sink` sink survived. With no source, no fact
is ever generated, so the Positive reports 0 — an FN.

**Verdict: rule-translation issue** (no engine fact dump needed — there is no
source rule to propagate). Responsible component:

- `PatternToActionListConverter.transformGlobalReadOrFail`
  (`core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/PatternToActionListConverter.kt:215`),
  dispatched from the `is SelectorExpr -> transformGlobalReadOrFail(pattern)`
  branch at
  `…/PatternToActionListConverter.kt:127`.

The parser lowers `$R.URL.RawQuery` to
`SelectorExpr(obj = SelectorExpr(obj = Metavar("$R"), sel = URL), sel = RawQuery)`
(`SemgrepGoPatternParser` selector tail loop,
`core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/SemgrepGoPatternParser.kt:579`).
`transformGlobalReadOrFail` requires `sel.obj` to be an `Identifier` with a
`ConcreteName` package (`…/PatternToActionListConverter.kt:217-219`); here
`sel.obj` is itself a `SelectorExpr`, so it throws `TransformationFailed(
"IndexExpr_recv_not_identifier")`, the whole pattern-source action list returns
`null`, and the rule pipeline emits no source. (The same branch only ever
succeeds for package-qualified `pkg.Field` reads — e.g. `os.Args` — never for a
metavar-rooted field chain.)

**3. Fix proposal.** `[rule-translation]` (primary) + `[engine]` (enabling).

- `[rule-translation]` Extend `PatternToActionListConverter` to lower a
  metavar-rooted field-read source `$R.Field` / `$R.A.B` into a *field-read
  source action* (a new `SemgrepPatternAction` variant, e.g. `FieldReadSource`,
  carrying the trailing field name `RawQuery` and optionally the receiver type
  if knowable). This is **fact-generating**: it adds a source action, it does
  not filter. Emit a corresponding new serialized item, e.g.
  `GoSerializedRule.FieldSource(field = "RawQuery", taint = [taint→Result])`
  (or reuse `GoSerializedGlobalSource` generalized to carry a field-name matcher
  instead of only a package-global name).
- `[engine]` Add a zero-to-fact source path in
  `GoMethodSequentFlowFunction` (alongside `applyGlobalReadSourceRules`,
  `…/GoMethodSequentFlowFunction.kt:404`) that fires on an assignment whose RHS
  is a `GoIRFieldExpr` (`r.URL.RawQuery` lowers to one or more
  `GoIRFieldExpr`/`GoIRFieldAddrExpr`,
  `core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/expr/GoIRExpr.kt:181,192`),
  matching the read field name against the new field-source rule and taint-ing
  the LHS register. Mirror the existing `detectGlobalReadName` structure but key
  on field name (and, when available, the receiver type) rather than a
  package-global `fullName`.

Size: medium (one converter branch + one new serialized item + one engine
flow-function path). Risk: medium — a field-name-only matcher (`RawQuery` with
no receiver-type constraint) is permissive and could fire on an unrelated
`.RawQuery` field of a different type; the same permissiveness already exists for
single-call sources like `$R.FormValue($K)`. Constraining by receiver type when
the IR exposes it lowers the risk.

**4. Post-fix behavior.** After the fix the serialized config should contain a
non-empty source list, e.g.

```
source: [FieldSource(field=RawQuery, condition=null, taint=[taint→Result], …)]
```

and the engine should generate a fact on `s := r.URL.RawQuery`, propagate it
through the local assignment, and report at `Sink(s)`. Re-enables
`GoSampleBasedTest.sourceUrlRawQuery()`. Expected benchmark FN recovery: **14**.

---

### A.2 — `r.Header["X-Test"]` (map-index on a tainted map field)

**1. Test case.**
`core/opentaint-go-querylang/samples-go/SourceHeaderMapIndex/` —
`Positive_header_index` reads `vals := r.Header["X-Test"]` then `Sink(vals[0])`.
Reproduced by `GoSampleBasedTest.sourceHeaderMapIndex()`, currently
`@Disabled("Cluster A: r.Header map-index source not matched — see fix proposal")`.
Rule has two pattern-sources: `$R.Header` and `$R.Header.Get($K)`. (`.Get(...)`
already works; the map-index read does not.)

**2. Description.**
Serialized config (verbatim):

```
source:       [Source(function=Pattern(regex=(.*\.)?\QGet\E), condition=NumberOfArgs(n=1), taint=[GoSerializedAssignAction(kind=rule.yaml:source-header-mapindex;0;_<T>_;, pos=BaseOnly(base=Result))], info=GoUserRuleFromSemgrepInfo(ruleId=rule.yaml:source-header-mapindex, relevantTaintMarks=[rule.yaml:source-header-mapindex;source_0;generated_source;1]))]
sink:         [Sink(function=Pattern(regex=(.*/)?\Qutil\E\.\QSink\E), condition=And(allOf=[NumberOfArgs(n=1), ContainsMark(tainted=rule.yaml:source-header-mapindex;0;_<T>_;, pos=BaseOnly(base=This))]), …), Sink(… ContainsMark(… pos=BaseOnly(base=AnyArgument(classifier=tainted))) …)]
globalSource: []
```

Exactly **one** source rule was produced — a call-site source on
`Pattern((.*\.)?Get)`, i.e. for the `$R.Header.Get($K)` pattern-source. The
`$R.Header` (whole-value field read) pattern-source produced **nothing**. The
Positive reads `r.Header["X-Test"]` (a map index), which is neither a `.Get`
call nor any call, so the only source rule never fires → FN.

**Verdict: rule-translation issue** (the `$R.Header` source is missing; the
map-index read shape has no matching source rule, so no fact dump is needed).
Responsible component: same as A.1 —
`PatternToActionListConverter.transformGlobalReadOrFail`
(`…/PatternToActionListConverter.kt:215`, dispatched at `…:127`). Here
`$R.Header` parses to `SelectorExpr(obj = Metavar("$R"), sel = Header)`; `sel.obj`
is a `Metavar`, not an `Identifier`, so the converter again throws
`IndexExpr_recv_not_identifier` and drops the source. (Note: this case is
distinct from A.1 only in that the dropped source is the *whole* field value
rather than a deeper chain; both die on the same `Identifier`-only check.)

**3. Fix proposal — reuse the A.1 field-read source, tainting the element `result.[*]` (READY; no new rule kind, no engine change).**

The cleanest approach reuses A.1's field-read source mechanism and lets the
*existing* lookup read do the propagation — no new rule kind, no new flow arm, no
engine-propagation change. Two pieces, both already present once A.1 lands:

1. **Field-read source taints the map's elements, not the whole map.** The
   `$R.Header` field-read source (from A.1's converter + engine `GoIRFieldExpr`
   source path) emits its taint at position **`result.[*]`** — i.e. the loaded
   `r.Header` value with an `ArrayElement` accessor — rather than at the whole
   `result`. The taint action position is just `result` + the `[*]` modifier
   (`PositionBaseWithModifiers.WithModifiers(base = Result, modifiers = [ArrayElement])`,
   the same `[*]` already used by bundled container passThroughs). This says
   "every element of `r.Header` is tainted."
2. **The existing lookup read propagates `[*]` to the looked-up value — verified, no change needed.**
   `r.Header["X-Test"]` lowers to a `GoIRLookupExpr`, which `exprToAccess` maps to
   `Access.RefAccess(base = r.Header, accessor = ElementAccessor)`
   (`GoFlowFunctionUtils.kt:146-148`). In `handleRefAssign`
   (`GoMethodSequentFlowFunction.kt:133`), a fact on `r.Header` that
   `startsWithAccessor(ElementAccessor)` (our `result.[*]`) is read via
   `readAccessor(ElementAccessor)` — stripping the `[*]` — and rebased onto the
   result register `vals`. So `r.Header.[*]` → `vals` falls out of the existing
   element-read path with zero new code.

So A.2/A.3 add **nothing beyond A.1** except authoring the `$R.Header` / `$R.Form`
field-read sources with a `result.[*]` taint position. This is strictly simpler
than a dedicated lookup-source rule kind (no `GoSerializedLookupSource`, no
`detectLookupReceiver`, no `applyLookupReadSourceRules`): the field source already
fires at the field read, the `[*]` position marks the elements, and the standard
container-element read carries it through the index. It is also more precise than
tainting the whole map — only element reads pick it up.

Size: **small** (rides entirely on A.1 + existing lookup propagation; the only
delta is the `[*]` taint position on the Header/Form field sources). Risk: **low**
— additive/fact-generating; the `…002F` negatives read a constant (no tainted
lookup) and stay clean.

**4. Post-fix behavior.** The `$R.Header` field-read source taints `r.Header.[*]`;
the `r.Header["X-Test"]` `GoIRLookupExpr` read strips `[*]` and taints `vals`;
`Sink(vals[0])` reports. Re-enables `GoSampleBasedTest.sourceHeaderMapIndex()`.
Expected benchmark FN recovery: **9** (shares the A.1 mechanism with A.3 —
combined 19).

---

### A.3 — `r.Form["X-Test"]` (map-index after `r.ParseForm()`)

**1. Test case.**
`core/opentaint-go-querylang/samples-go/SourceFormParse/` —
`Positive_form_index` calls `r.ParseForm()` then reads
`vals := r.Form["X-Test"]` and `Sink(vals[0])`. Reproduced by
`GoSampleBasedTest.sourceFormParse()`, currently
`@Disabled("Cluster A: r.Form map-index source not matched — see fix proposal")`.
Rule pattern-sources: `$R.Form.Get($K)` and `$R.Form`.

**2. Description.**
Serialized config (verbatim):

```
source:       [Source(function=Pattern(regex=(.*\.)?\QGet\E), condition=NumberOfArgs(n=1), taint=[GoSerializedAssignAction(kind=rule.yaml:source-form-parse;0;_<T>_;, pos=BaseOnly(base=Result))], info=GoUserRuleFromSemgrepInfo(ruleId=rule.yaml:source-form-parse, relevantTaintMarks=[rule.yaml:source-form-parse;source_0;generated_source;1]))]
sink:         [Sink(function=Pattern(regex=(.*/)?\Qutil\E\.\QSink\E), condition=And(allOf=[NumberOfArgs(n=1), ContainsMark(tainted=rule.yaml:source-form-parse;0;_<T>_;, pos=BaseOnly(base=This))]), …), Sink(… AnyArgument(classifier=tainted) …)]
globalSource: []
```

Identical shape to A.2: only the `$R.Form.Get($K)` call-site source survived
(`Pattern((.*\.)?Get)`); the `$R.Form` whole-value field-read source produced
**nothing**. The Positive reads `r.Form["X-Test"]` (map index), so the only
source never fires → FN. The intervening `r.ParseForm()` call is irrelevant to
the source-shape problem (it has no source rule and is not on the taint path).

**Verdict: rule-translation issue** — same component and mechanism as A.2.
`$R.Form` parses to `SelectorExpr(obj = Metavar("$R"), sel = Form)` and is
dropped by `transformGlobalReadOrFail`'s `Identifier`-only receiver check
(`…/PatternToActionListConverter.kt:217`). No fact dump needed (no source to
propagate).

**3. Fix proposal — same as A.2; READY.**

`r.Form["k"]` is the identical map-index shape as A.2 and is recovered the same
way: the `$R.Form` field-read source (A.1 mechanism) taints `r.Form.[*]`, and the
existing `GoIRLookupExpr` read strips `[*]` onto `vals`. A.3 carries no work of its
own beyond authoring the `$R.Form` source with a `result.[*]` position;
`r.ParseForm()` is irrelevant (no source, not on the path). No new rule kind, no
engine change.

**4. Post-fix behavior (with the lookup-source rule kind).** A
`LookupSource(receiver=Form field read)` rule fires at the `r.Form["X-Test"]`
`GoIRLookupExpr`, tainting `vals`; `Sink(vals[0])` reports. Re-enables
`GoSampleBasedTest.sourceFormParse()`. Expected benchmark FN recovery: **10**
(shared with A.2 under the one lookup-source rule kind — combined 19).

---

## Summary (Cluster A)

| Sample | Positive (disabled) | Verdict | Responsible (file:line) | Fix one-liner | Status | FN recovery |
|---|---|---|---|---|---|---|
| `SourceUrlRawQuery` | `Positive_rawquery` | rule-translation (+ engine source path) | `PatternToActionListConverter.kt:215` (dispatch `:127`) | lower `$R.Field` chain to a field-read source action + add engine `GoIRFieldExpr` zero-to-fact source path | **ready** | 14 |
| `SourceHeaderMapIndex` | `Positive_header_index` | rule-layer (A.1 mechanism) | A.1 field source + existing `GoIRLookupExpr` read (`GoFlowFunctionUtils.kt:146`, `GoMethodSequentFlowFunction.kt:133`) | `$R.Header` field-read source taints `result.[*]`; existing lookup read strips `[*]` onto the value — no new rule kind, no engine change | **ready** | 9 |
| `SourceFormParse` | `Positive_form_index` | rule-layer (A.1 mechanism) | A.1 field source + existing `GoIRLookupExpr` read | `$R.Form` field-read source taints `result.[*]`; same as Header | **ready** | 10 |

All three FNs share one rule-translation root cause: a metavar-rooted field-read
source (`$R.Field…`) is silently dropped because the only field/selector lowering
path requires a package-identifier receiver. None of the proposed changes is a
`FactTypeChecker`-style filter; every change adds source facts.

Notes on the recovery accounting and implementation shape:

- **A.1 (`$R.URL.RawQuery`, recovery 14)** is recovered by the field-read source
  path alone (no map-index step).
- **Header + Form (9 + 10 = 19) reuse the A.1 field-read source with a `result.[*]`
  taint position** — no new rule kind and no engine change. The field source taints
  the map's elements (`r.Header.[*]`), and the *existing* `GoIRLookupExpr` element
  read (`exprToAccess` → `RefAccess(base, ElementAccessor)`, then `handleRefAssign`
  strips the matching `[*]`) propagates it to the looked-up value. This is simpler
  and more precise than the earlier whole-map-taint + propagation approach AND than
  a dedicated lookup-source rule kind (both dropped). The per-sample 9/10 are not
  independent: both fall out of the single A.1 mechanism + the `[*]` position.
- **`$R.URL.RawQuery` is a two-level selector chain**, not a single field: it
  lowers to nested `GoIRFieldExpr` (`.URL` then `.RawQuery`, where `.URL` is an
  interface-typed field). The A.1 source keys on the trailing read field
  (`RawQuery`); matching the trailing field is the pragmatic choice, with the
  receiver type used as an additional constraint where the IR exposes it (the
  intermediate `.URL` read does not itself need a fact).
- **The new field-read source follows the existing Result-rebase convention.**
  A.1's `FieldSource` uses `pos = BaseOnly(base = Result)`, and the sample reads
  assign to a local, so the existing Return→LHS rebase path in
  `applyGlobalReadSourceRules` (`GoMethodSequentFlowFunction.kt:432`) carries it —
  it does NOT hit the unrelated `TODO("Field source with non-result assign")` at
  `:429`.

---

## Cluster C — dataflow engine FNs

Cluster C FNs are pure *engine* propagation gaps: the source and sink rules are
the standard `util.Source()` / `util.Sink()` call rules and translate correctly,
so the rule-translation layer is not involved. Diagnosis was done with full
per-statement fact dumps via
`EngineRoadmapDiagnosticTest.printFactsAt(...)`
(`core/src/test/kotlin/org/opentaint/go/sast/dataflow/EngineRoadmapDiagnosticTest.kt`),
walking *every* instruction (∅ included) to pinpoint the death instruction.

Triage hypothesised three Cluster C engine shapes (closure capture/higher-order,
nested-struct constructor return, interface laundering). On reproduction only
**one** — the closure shape — is an actual FN. The other two already PASS and are
covered in C.2 as a correction to the FN accounting.

---

### C.1 — closure capture / higher-order (factory returns a captured closure)

**1. Test case.**
`core/samples/src/main/go/closures.go`, `closureCaptureReturn001T` (lines
124–133):

```go
func makeCapturingPrefixer(prefix string) func(string) string {
    return func(value string) string { return prefix + value }
}
func closureCaptureReturn001T() {
    data := util.Source()
    addPrefix := makeCapturingPrefixer(data)   // factory returns closure capturing tainted `data`
    out := addPrefix("_suffix")                 // closure called; taint should flow via captured free var
    util.Sink(out)
}
```

Currently `@Disabled("Cluster C: closure capture/higher-order not propagated — see fix proposal")`
in `core/src/test/kotlin/org/opentaint/go/sast/dataflow/ClusterCTest.kt:10-11`.
This is the deferred Patterns 9/10 (closure returned from a factory /
higher-order) and is the dominant Cluster C FN shape in the benchmark — the
`makePrefixer` / `makeMessageGenerator` mutation wrappers recur across many FN
files.

**2. Description.**
Full per-statement fact dump (verbatim,
`/tmp/go-engine-roadmap-facts/test_closureCaptureReturn001T.txt`):

```
=== Facts at test.closureCaptureReturn001T ===
  L129 [0:0]  %0:t0 = test/util.Source()    facts: ∅
  L130 [0:1]  %1:t1 = test.makeCapturingPrefixer(%0:t0)    facts: var(0)![taint].$
  L131 [0:2]  %2:t2 = %1:t1("_suffix")    facts: var(0)![taint].$, var(1)![taint].$
  L132 [0:3]  %3:t3 = test/util.Sink(%2:t2)    facts: ∅
  L -1 [0:4]  return    facts: ∅
```

Reading it (facts shown are the in-facts holding *at* each instruction;
`var(N)` = `AccessPathBase.LocalVar(N)`, i.e. register `%N`):

- L129 `%0 = Source()` — source fact is generated *by* this call and applies to
  successors, so the line itself is ∅.
- L130 `%1 = makeCapturingPrefixer(%0)` — `var(0)` (the tainted `data`/`%0`) is
  live entering the factory call. **Parts (a) and (b) WORK:** by L131 the
  closure value `%1` carries taint (`var(1)![taint]` appears), so the factory
  correctly (a) attached the captured tainted binding to the closure value at
  its internal `MakeClosure` and (b) propagated that fact out as the call's
  return value. The closure value arrives at the call site tainted.
- L131 `%2 = %1("_suffix")` — the dynamic call. Both `var(0)` and `var(1)` (the
  tainted closure value) are live, but the **result `%2` is never tainted**.
- L132 `%3 = Sink(%2)` — `%2` is clean, facts ∅. **This is the death point:**
  the taint dies *across the dynamic call at L131* — it is present on the
  closure value entering the call and absent on the call's result.

**Death point:** L131 `%2 = %1("_suffix")` — the dynamic call on the
returned-closure value. The captured taint reaches the call (on `%1`) but does
not flow into the result `%2`.

**Responsible component — this is case (c), the dynamic call site.**
The call mode for `%1("_suffix")` is `DYNAMIC` (the callee is a register, not a
`GoIRFunctionValue`). `GoCallResolver.resolveDynamic`
(`core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/GoCallResolver.kt:52-67`)
resolves a closure call **only** by tracing the callee register back to a
`GoIRMakeClosureExpr` *defined in the current method* via
`GoFlowFunctionUtils.findMakeClosureExpr`
(`…/GoFlowFunctionUtils.kt:310-313`), which inspects the defining instruction of
the register:

```kotlin
fun findMakeClosureExpr(register: GoIRRegister, method: GoIRFunction): GoIRMakeClosureExpr? {
    val defInst = findDefInst(register, method) ?: return null
    return (defInst as? GoIRAssignInst)?.expr as? GoIRMakeClosureExpr
}
```

Here `addPrefix` (`%1`) is defined by a **`GoIRCall`** (`makeCapturingPrefixer(...)`),
not by a local `GoIRMakeClosureExpr` — the `MakeClosure` happened *inside the
factory* and was returned across the call boundary. So `findMakeClosureExpr`
returns `null`, `resolveDynamic` returns `null`
(`GoCallResolver.kt:59-66`), and the call is **unresolved**. The unresolved-call
path (`GoMethodCallFlowFunction.propagateUnresolvedCallFact`,
`…/analysis/GoMethodCallFlowFunction.kt:148`) applies only configured
pass-through rules; there is no rule for an opaque closure invocation, so nothing
connects the tainted closure value `%1` to the result `%2`, and the taint dies.

This is exactly why `findMakeClosureExpr` is intraprocedural-only: the engine
resolves a closure call only when the `MakeClosure` is *visually present* in the
same body (the working `closure001T` case at `closures.go:38-43`, where
`f := func(){...}; f()` are co-located). The contrast confirms the diagnosis:
`closure001T` PASSES (local `MakeClosure` → `findMakeClosureExpr` succeeds →
the bindings-first taint at `GoFlowFunctionUtils.exprToAccess`'s
`GoIRMakeClosureExpr` arm, `…/GoFlowFunctionUtils.kt:200-206`, plus free-var
argument mapping at `…/GoFlowFunctionUtils.kt:104-108` carries the captured
`data`). `closureCaptureReturn001T` FAILS purely because the `MakeClosure` is no
longer local once the closure is returned from a factory.

This matches the pre-existing `@Disabled` annotations in `ClosureTest.kt`:
`closureReturn001T` — "Closure returned from callee: MakeClosureExpr not visible
at dynamic call site" (`ClosureTest.kt:23-24`) — and `higherOrder001T` /
`higherOrder003T` — "DYNAMIC call on function parameter: cannot resolve without
interprocedural value tracking" (`ClosureTest.kt:28-32`). All three are the same
root cause: a closure value that is *not* the result of a local `MakeClosure`
(returned from a factory, or passed in as a parameter) cannot be resolved at its
dynamic call site.

**3. Fix proposal.** `[engine]`, fact-generating. This is the **big one** of
Cluster C (~41 FNs across the benchmark — likely the single largest Cluster C
fix). Two coordinated engine changes are needed; the second is the substantive
one:

- **Resolve closures that arrive as values, not just local `MakeClosure`s.**
  Today `resolveDynamic` only handles `GoIRFunctionValue` (direct) and a
  register traced to a *local* `MakeClosureExpr`. Extend it to resolve a closure
  that arrived as a **call return value** (and, for the higher-order case, as a
  **parameter**). Options, in increasing power:
  - **(i) Closure summary / value tracking.** Track, interprocedurally, which
    concrete `GoIRFunction` a closure-typed value can hold (the factory's
    returned `MakeClosure.fn`), so the dynamic call at the use site can be
    resolved to that body. This is the principled fix and also re-enables
    `higherOrder001T/003T` (function-parameter dynamic calls).
  - **(ii) Closure-value taint summary.** Independent of resolving the exact
    body, attach a *closure summary fact* to the closure value carrying its
    captured-taint state, and at the dynamic call site apply that summary: if
    the closure value is tainted (a captured binding was tainted) and the
    closure body's return is taint-transparent in the captured free var, taint
    the call result. This is fact-generating (it *adds* a result fact) and is
    cheaper than full value tracking, at the cost of precision (it
    over-approximates closures whose body drops the captured value — the `…002F`
    negatives must still be respected, so the summary must encode whether the
    captured free var actually reaches the return).
- **Link captured bindings to the body's free-var params at the resolved call.**
  Once the body is resolved (via (i)), reuse the existing free-var argument
  mapping: a `GoIRFreeVarValue` with `freeVarIndex` maps to
  `AccessPathBase.Argument(nonReceiverParamCount + freeVarIndex)`
  (`GoFlowFunctionUtils.kt:104-108`), and the closure's `bindings`
  (`GoIRMakeClosureExpr.bindings`,
  `core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/expr/GoIRExpr.kt:139-147`)
  supply the actual captured values. The new work is connecting the *originating*
  `MakeClosure.bindings` (captured in the factory) to the body's free-var
  parameter slots at a call site in a *different* method — i.e. propagating the
  captured-binding facts across the factory→use-site boundary so the call-to-start
  flow seeds the body's free-var argument positions.

  Size: **large.** This is genuine interprocedural closure value tracking (the
  hard part is (i) — establishing, across call boundaries, which body a closure
  value holds and threading its captured bindings to that body's free-var
  params). Risk: **high.** A closure summary that always taints the result when
  the closure value is tainted would over-approximate (false positives on
  `closureCaptureReturn002F` / `closureReturn002F` / `higherOrder002F/004F`,
  where the captured value is dropped or replaced) — the summary must be
  return-reachability-aware to keep the `…F` negatives passing. Value tracking
  (option (i)) is the lower-risk-on-precision but higher-effort route. Given the
  ~41-FN payoff this is the highest-value Cluster C fix, but also the most
  involved; it likely warrants its own focused engine workstream rather than a
  drive-by change.

**JVM reference architecture (the blueprint for option (i)).** The JVM analyzer
already solves the structurally-identical problem — a lambda created in M1,
returned to M2, invoked dynamically in M2 — and option (i) should mirror it
rather than invent a new mechanism. The JVM pipeline is type-info-fact based, not
a separate alias analysis:

1. **Carry the concrete closure identity as a fact from the creation site.**
   JVM: `TypeInfoSequentFlowFunction` (`…/jvm/ap/ifds/analysis/JIRMethodCallResolver.kt:158-168`)
   detects the lambda allocation and emits a zero-to-fact whose access path is
   `[TypeInfoGroupAccessor, TypeInfoAccessor(lambdaClassName)]` on the lambda
   value (wired at `JIRMethodSequentFlowFunction.propagateZeroToZero`, `:55-68`).
   Go analog: at the `GoIRMakeClosureExpr` site, emit a "closure-identity" fact on
   the closure value carrying the concrete `MakeClosure.fn` (the body
   `GoIRFunction`). This fact rides the normal access-path propagation — crucially,
   it survives the factory's `return` and the caller's assignment, arriving on the
   closure value at the dynamic call site (the same way the JVM type-info fact
   survives M1→M2).
2. **At the dynamic call site, read the identity off the fact and resolve the body.**
   JVM: `tryExtractLambdaType` (`JIRMethodCallResolver.kt:110-156`) reads the
   `TypeInfoGroupAccessor`/`TypeInfoAccessor` off the in-fact, looks up the lambda
   class, finds its SAM method, and registers it with `JIRLambdaTracker.addLambda`
   (which fires the pending `LambdaSubscription` to analyze the body). Go analog:
   extend `GoCallResolver.resolveDynamic` (`GoCallResolver.kt:52-67`) so that when
   `findMakeClosureExpr` fails (non-local closure), it falls back to reading the
   closure-identity fact carried on the callee register and resolves to that
   `GoIRFunction` body. This replaces the intraprocedural-only
   `findMakeClosureExpr` limitation with a fact-driven resolution that works across
   call boundaries — the exact gap diagnosed above.
3. **Thread captured vars into the body; return back.** JVM models captured vars
   as synthetic lambda-class fields read inside the synthesized body
   (`LambdaAnonymousClassFeature.kt`), so taint flows by ordinary field-read
   semantics. Go already has the free-var machinery — `GoIRFreeVarValue` →
   `AccessPathBase.Argument(nonReceiverParamCount + freeVarIndex)`
   (`GoFlowFunctionUtils.kt:104-108`) — so once the body is resolved, the existing
   free-var argument mapping threads the captured bindings; the result returns via
   the normal call-to-return flow.

This makes option (i) concrete: a Go **closure-identity fact** (mirroring
`TypeInfoAccessor`) + a **fact-driven branch in `resolveDynamic`** (mirroring
`tryExtractLambdaType`). It reuses the existing free-var threading, keeps the
`…002F` negatives correct (a closure whose body drops the captured var resolves to
a body whose return simply isn't taint-reachable — no summary heuristic needed),
and re-enables `closureReturn001T` / `higherOrder001T/003T` for free. Recommend
implementing C.1 along these lines in its own focused round. **Implementation
note:** read `JIRLambdaTracker` for the subscription/lazy-resolution pattern — a
closure value's identity fact may arrive at the call site only after the call is
first visited, so the Go side likely needs the same "resolve-on-fact-arrival"
subscription rather than a one-shot resolution.

**4. Post-fix behavior.** Expected trace after the fix:

```
  L129  %0 = Source()                      facts: ∅                (source generated)
  L130  %1 = makeCapturingPrefixer(%0)      facts: var(0)![taint]   (closure value %1 becomes tainted — already works)
  L131  %2 = %1("_suffix")                  facts: var(0), var(1)   (dynamic call resolved → captured prefix flows to body free var → tainted result %2)
  L132  %3 = Sink(%2)                       facts: var(2)![taint]   (tainted %2 reaches the sink → REPORT)
```

The dynamic call at L131 resolves to the closure body, the captured (tainted)
`prefix` free var flows through `prefix + value` into the return, and `%2`
becomes tainted, so `Sink(%2)` reports. Re-enables
`ClusterCTest.closureCaptureReturn001T` (`ClusterCTest.kt:10-11`). The same
interprocedural-closure-resolution fix should also re-enable the existing
`@Disabled` `ClosureTest.closureReturn001T` (`ClosureTest.kt:23-24`) and
`ClosureTest.higherOrder001T` / `higherOrder003T` (`ClosureTest.kt:28-32`), which
share the identical root cause. Expected benchmark FN recovery: **~41** (the
dominant Cluster C shape).

---

### C.2 — confirmed NON-FNs (kept as regression guards)

Triage attributed Cluster C engine-FN counts to three shapes; on reproduction
only the closure shape (C.1) is an actual FN. The other two **already PASS** and
are kept enabled in `ClusterCTest.kt` as regression guards:

- **`nestedStructConstructor001T`** (`ClusterCTest.kt:16`) — constructor returns
  a struct carrying tainted data; PASSES. The engine already handles
  constructor-returns-struct field taint. Triage's "nested-struct" engine-FN
  count (4) was **mis-attributed** — this is not an engine gap.
- **`interfaceLaunderingConcrete001T`** (`ClusterCTest.kt:20`) and
  **`interfaceLaunderingIface001T`** (`ClusterCTest.kt:22`) — taint laundered
  through an interface via a concrete value and via an interface-typed variable
  (multi-implementor dispatch); both PASS, with the negative
  `interfaceLaundering002F` (`ClusterCTest.kt:23`) also correctly clean. The
  engine already handles `INVOKE`-mode interface dispatch
  (`GoCallResolver.resolveInvoke`, `GoCallResolver.kt:69-79`). Triage's
  "interface" engine-FN count (3) was **mis-attributed** — not an engine gap.

**Honest FN accounting.** The previously-claimed Cluster C engine-FN totals for
nested-struct (4) and interface (3) do not reproduce. The real Cluster C engine
gap is **concentrated entirely in the closure shape (C.1)** — the dynamic call
on a non-local closure value. The other two shapes are kept as enabled tests so
the accounting correction is guarded against regression.

---

## Summary (Cluster C)

| Sample | Test (status) | Verdict | Death point | Responsible (file:line) | Which of (a)/(b)/(c) | Fix one-liner | FN recovery |
|---|---|---|---|---|---|---|---|
| `closureCaptureReturn001T` | `ClusterCTest` (`@Disabled`) | engine | dynamic call `%2 = %1("_suffix")` (L131) | `GoCallResolver.resolveDynamic` `GoCallResolver.kt:52-67` (via `findMakeClosureExpr` `GoFlowFunctionUtils.kt:310-313`) | **(c)** dynamic call site — closure value resolved only when its `MakeClosure` is local; a factory-returned closure is unresolvable | interprocedural closure value tracking / closure summary to resolve a non-local closure value at its dynamic call and thread captured bindings to the body's free-var params | ~41 |
| `nestedStructConstructor001T` | `ClusterCTest` (enabled) | NON-FN | — | already handled | — | regression guard (triage mis-attributed 4) | 0 |
| `interfaceLaunderingConcrete001T` / `…Iface001T` | `ClusterCTest` (enabled) | NON-FN | — | `GoCallResolver.resolveInvoke` already handles dispatch | — | regression guard (triage mis-attributed 3) | 0 |

The single Cluster C engine gap is the closure shape: a closure value that is
not the result of a *local* `MakeClosureExpr` (returned from a factory, or passed
as a parameter) cannot be resolved at its `DYNAMIC` call site, so taint carried
on the closure value (captured free var) never reaches the call result. Parts (a)
attach-binding-to-closure-value and (b) return-closure-value-to-caller already
work; only part (c) the dynamic call resolution is missing. The fix is
fact-generating (adds the missing result fact) but large and high-risk
(interprocedural value tracking; the summary must stay return-reachability-aware
to keep the `…F` negatives passing).
