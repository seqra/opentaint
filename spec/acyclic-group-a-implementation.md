# Implementation proposal: group A rules of the acyclic proposal

Status: PROPOSAL, 24 November 2026 (revision 2, after an adversarial
review against the code). Base: `saloed/bidirectional` at `620cd5659`.
It follows [impl-proposal-guide.md](impl-proposal-guide.md),
[proof-guide.md](proof-guide.md) and [design-guide.md](design-guide.md).

Source spec: [acyclic-convergence-proposal.md](acyclic-convergence-proposal.md),
"Final classification" (group A), §1 (decisions), §5.1 (G6 drop form),
§5.5 (EXACT cleaner on a MUST leaf). Prototype: branch
`proto/acyclic-only-20261123` (`3693de8a1`), report
`docs/reports/acyclic-only-20261123.md`. The core code at `620cd5659` is
identical to the prototype base `f8f34bf94`, so the prototype gate
results apply to this base. Proofs:
[lean/proposals/acyclic-group-a-20261124](lean/proposals/acyclic-group-a-20261124/README.md).

## 0. Summary

Group A has two rules. Both are decided semantics. This proposal lands
them in production code with their tests, their proofs and a gate.

| Id | Rule | Where it acts | What changes | Proof |
| --- | --- | --- | --- | --- |
| R1 | G6 drop form (spec §5.1) | type filter, mark policy (`ap/Filter.kt`) | At and below a boxed spine level, a mark that is not primitive-tracking is removed from the whole value, field leaves included | `G6DropForm.lean`, 15 claims |
| R2 | An EXACT cleaner does not apply to a MUST leaf (spec §5.5) | cleaner, PART row (`ap/Clean.kt`), both directions, every run | The MUST leaf stays on its layer; native moves it to DEMAND | `MustExactCleaner.lean`, 12 claims |
| T1 | Sink-route census and R2 count (gate tools, not rules) | sink witness; R2 hook | Nothing when off. When on, they log the NORMAL leaves that reach each sink, and the R2 applications, per analysis | none (diagnostic) |

This proposal does not meet requirement AC (spec §1). Group A alone
leaves acyclic demand (OWASP residual 24 with R2 alone, spec §5.5). It
adds no stop rule, no group-B rule and no new limit.

Line numbers refer to `620cd5659`. File paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`,
unless a path starts with `jvm:` (=
`core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/`)
or `test:` / `jvm-test:` (the `src/test/kotlin` trees of the same two
modules, packages `org.opentaint.dataflow.bidi` and
`org.opentaint.dataflow.jvm.bidi`).

## 1. Decisions that this proposal implements

| Date | Decision | Effect here |
| --- | --- | --- |
| 20 Nov | G6 uses the drop form | R1 |
| 21 Nov | An EXACT cleaner does not apply to a MUST fact | R2 |
| 24 Nov | The four module fixtures that R2 changes are signed off | §4.6 |
| 24 Nov | R2 is approved as semantics (group A) | R2 |
| 24 Nov | Serve every route; the sink-route census is the check | T1, §6 |
| 24 Nov | Single launch per measurement | §6 |
| 24 Nov | Robustness rule: never relax the relative caps | R1 and R2 make no fact deeper and no new fact (§2) |

Open questions for the owner are in §8 (Q1-Q4). The proposal uses the
recommended answer of each until the owner decides.

## 2. Semantic scope

**Changed (R1).** The mark policy of a type filter, at and below the first
boxed spine level of the filtered value. Native removes a mark only from
the spine leaf of a level. R1 also removes it from every leaf below the
first boxed level that drops it. R1 only removes marks. It never adds a
mark, a leaf or a fact. R1 acts wherever a type filter with a mark policy
is applied. Reversed statement summaries carry no type filters
(`interp/StatementSummary.kt:60-69`: `reversed()` passes `emptyMap()`),
so on statement edges R1 acts in forward runs only.

**Changed (R2).** The PART row of an EXACT cleaner on the any-marks of a
MUST (`[any-taint]`) leaf, in both directions and in every run (the
cleaner does not read the direction; `CleanStep.Clean.reversed()` is the
same step, `interp/RuleStatement.kt:90`). Native removes the leaf from
its layer and adds the same leaf on DEMAND (the "survivor"). R2 keeps
the leaf on its layer. The positions and marks do not change (Lean C5).
Only the layer of one row changes.

**Changed by consequence (R2): protection on NORMAL.** `ApOps.clean`
(`ap/ApOps.kt:126-135`) gives every result on the cleaner base the
selected protection (`selectedProtection`,
`ap/FlowBackedProtection.kt:128-135`): the cleaned mark becomes a
`nonSubsumable` membership. Natively the protected membership sat on the
DEMAND survivor. With R2 it sits on the kept NORMAL leaf. A protected
NORMAL membership is not removed by a FLOW cover
(`store/FlowBackedSummaries.kt:148`), is split into its own packet
(`membershipPackets`, `ap/FlowBackedProtection.kt:13`), and is read by
the run-1 origin stores and by record replay. The prototype gates ran
with this behavior. See Q4.

**Not changed in GROUP mark mode.** In GROUP mode `gone()` returns no mark
for a cleaner with a selected mark (`ap/Clean.kt:162`), so native removes
nothing there and R2 does not run. R2 acts in FULL mode only.

**Unchanged.**

- FLOW facts and `Reach` facts (the mark policy and R2 do not read them).
- The path filter (`may`) of a type filter.
- Every other cleaner row: `$` leaves, MAY and STAR leaves, BELOW and
  AT_AND_BELOW reach, the one-accessor MUST rows, the FLOW cleaner.
- The selected-protection wrapper itself (only the layer of one of its
  inputs changes, see above).
- The run-1 output policy (`ap/ApOut.kt:11-14`,
  `ap/Conclusions.kt:104-118`): it runs after the cleaner, as today.
- C2, C5, the relative caps, the field limit schedule, the handoff, the
  stop rules, the report rules.

**Hidden-change check.**

- R1 adds the class `LevelMarkPolicy` and two default methods to the
  `MarkPolicy` interface. A policy is not part of a fact. `TypeFilter`
  objects are cached per type (`jvm:bidi/interp/JIRTypeFilters.kt:20-22`).
  No equality or hash of a policy is read, except the identity check in
  `test:PrimitiveValuesTest` (`assertSame` on `TypeFilter.and`), which
  stays true. `NeutralRelationBatch.certifies`
  (`engine/NeutralRelationBatch.kt:242-243`) reads `markPolicy` only for
  null; R1 keeps null where native has null.
- R2 adds no new data type. Its output is the input leaf; the protection
  wrapper then adds the selected membership, as for every result on the
  cleaner base.
- The robustness rule (spec §1) holds: R1 removes marks; R2 keeps a leaf
  that native also keeps (on another layer). Neither makes a fact deeper
  or makes more facts.

## 3. R1: G6 drop form

### 3.1 Definition

A type filter with a mark policy acts on a TAINT tree with the static type
`τ`. The spine levels `k = 0, 1, …` are the nodes `β.[]^k`. For a level
`k`, `prim(k)` holds when the level type is primitive or boxed, and
`boxed(k)` holds when it is a class that unboxes to a primitive
(`Integer`, `Long`, `Boolean`, `Character`, …). `pt(t)` holds when the
mark `t` is primitive-tracking.

```text
keeps(t, k)      = ¬prim(k) ∨ pt(t)                 (native, unchanged)
dropsValue(t, k) = boxed(k) ∧ ¬keeps(t, k)
spine(p)         = number of leading element accessors of the path p

removedNative(t, p) = onSpine(p) ∧ ¬keeps(t, spine(p))
removedDrop(t, p)   = (∃ k ≤ spine(p): dropsValue(t, k)) ∨ removedNative(t, p)
```

`onSpine(p)` holds when `p` has only element accessors. The decision is
per mark and per position. It is the same for `$` marks and for any-tail
marks, and on both layers.

### 3.2 Native code

| Site | Lines | Behavior |
| --- | --- | --- |
| `ap/Primitives.kt` `MarkPolicy` | 18-23 | `keeps(mark, elements)` only |
| `ap/Primitives.kt` `TypeFilter.and` | 30-34 | a lambda: `a.keeps && b.keeps` |
| `jvm:bidi/interp/JIRTypeFilters.kt` `make` | 48-55 | `primitive[k]` per level; a lambda policy |
| `ap/Filter.kt` `filterFacts` | 8-21 | `markPolicyOnElements` for a `TaintTree` |
| `ap/Filter.kt` `markPolicyOnElements` | 96-122 | filters the root and the element spine leaves only |
| `interp/FormsReference.kt` `ReferenceAlgebra.passes` | 52-63 | a path with a non-element accessor passes |
| `engine/NeutralRelationBatch.kt` `certifies` | 242-243 | reads `markPolicy == null` only; not changed |

No other site reads a mark policy.

Example of the native defect (fixture M4, reduction). `x: Integer[]`; the
mark `T` is not primitive-tracking. At `K = 1` the fact is `x.[].MAY/T`,
a spine leaf of the boxed level 1: native drops it. At `K = 2` the fact
is `x.[].value.$/T`, a field leaf: native keeps it. A larger K adds a
finding (Lean `m4_native_breaks`, `native_not_prefix_closed`).

### 3.3 Code changes

Port `ap/Primitives.kt`, `ap/Filter.kt`, `interp/FormsReference.kt` and
`jvm:bidi/interp/JIRTypeFilters.kt` from `proto/acyclic-only-20261123`
(commits `8358d392e`, `4b14e086e`, squashed in `3693de8a1`). Do not port
the counters (`G6Drops.DropCounters`, `ApManager.g6DropCounters`).

**(a) The policy knows its boxed levels** (`ap/Primitives.kt`).

```kotlin
fun interface MarkPolicy {
    fun keeps(mark: TaintMark, elements: Int): Boolean
    /** The level type is a class that unboxes to a primitive. */
    fun boxedLevel(elements: Int): Boolean = false
    /** The policy drops [mark] on the whole value at the boxed level [elements]. */
    fun dropsValue(mark: TaintMark, elements: Int): Boolean = boxedLevel(elements) && !keeps(mark, elements)
}

class LevelMarkPolicy(
    private val primitive: BooleanArray,
    private val boxed: BooleanArray,
    private val primitiveTracking: (TaintMark) -> Boolean,
) : MarkPolicy {
    init { require(primitive.size == boxed.size && boxed.indices.all { !boxed[it] || primitive[it] }) }
    override fun keeps(mark: TaintMark, elements: Int) = !primitive.getOrElse(elements) { false } || primitiveTracking(mark)
    override fun boxedLevel(elements: Int) = boxed.getOrElse(elements) { false }
}

// TypeFilter.and: replace the lambda by
private class AndPolicy(val a: MarkPolicy, val b: MarkPolicy) : MarkPolicy {
    override fun keeps(mark: TaintMark, elements: Int) = a.keeps(mark, elements) && b.keeps(mark, elements)
    override fun boxedLevel(elements: Int) = a.boxedLevel(elements) || b.boxedLevel(elements)
    override fun dropsValue(mark: TaintMark, elements: Int) = a.dropsValue(mark, elements) || b.dropsValue(mark, elements)
}
```

A lambda `MarkPolicy { … }` (tests only) keeps the defaults: no boxed
level, so the native path.

**(b) The JVM policy** (`jvm:bidi/interp/JIRTypeFilters.kt` `make`).

```kotlin
val levels = generateSequence(t) { it.ifArrayGetElementType }.toList()
val primitive = levels.map { it.typeName == "java.lang.Character" || it.unboxIfNeeded() is JIRPrimitiveType }
val boxed = levels.mapIndexed { k, type -> primitive[k] && type !is JIRPrimitiveType }
return TypeFilter(checker.localFilter(t),
    markPolicy = if (true !in primitive) null
        else LevelMarkPolicy(primitive.toBooleanArray(), boxed.toBooleanArray(), ::isPrimitiveTracking))
```

`keeps` is the native lambda. Only `boxed` is new.

**(c) The runtime filter** (`ap/Filter.kt`).

```kotlin
internal fun filterFacts(m: ApManager, c: Facts, f: TypeFilter, dropForm: Boolean = G6Drops.drop): Facts? {
    ...
    is TaintTree -> {
        var result = m.taintAlg.filterPath(m, c.root, f.may)
        val policy = f.markPolicy
        if (result != null && policy != null)
            result = if (dropForm) markPolicyDropForm(m, result, policy) else markPolicyOnElements(m, result, policy)
        ...
    }
}

private fun markPolicyDropForm(m: ApManager, n: TaintNode, policy: MarkPolicy): TaintNode? {
    val spine = n.elementSpine()                                   // [e]^0, [e]^1, … as in markPolicyOnElements
    val firstBoxed = spine.indices.firstOrNull { policy.boxedLevel(it) }
        ?: return markPolicyOnElements(m, n, policy)               // no boxed level on this fact: native
    val candidates = m.taintAlg.foldAll(spine[firstBoxed], m.cancellation).let { it.exact + it.any }
    // droppedAt[j] = { t ∈ candidates | ∃ k: firstBoxed ≤ k ≤ j, boxedLevel(k), dropsValue(t, k) }
    val droppedAt = accumulate(spine.indices, firstBoxed, candidates, policy)
    // Bottom-up rebuild, from the deepest spine node:
    //   spine leaf j     := keepPolicyMarks(leaf, policy, j) − droppedAt[j]     (native, then the drop)
    //   element child    := the rebuilt node j+1
    //   field child of j := dropOnValue(child, droppedAt[j])                     (every leaf of the subtree)
    ...
}

private fun dropOnValue(m: ApManager, n: TaintNode, d: MarkSet): TaintNode? {
    val all = m.taintAlg.foldAll(n, m.cancellation)
    if (all.exact.data.none { TaintMark(it) in d } && all.any.data.none { TaintMark(it) in d }) return n   // no copy
    return m.taintAlg.mapLeaves(n, m.cancellation) { leaf -> /* leaf.exact − d, leaf.any − d; same object if unchanged */ }
}
```

The prototype code of `markPolicyDropForm` and `dropOnValue`
(`ap/Filter.kt` on the prototype branch) is the reference. Remove the
counter lines and the `normal` parameter (it fed a counter only).

**(d) The reference** (`interp/FormsReference.kt` `passes`). After the
path filter and the `markPolicy` null check:

```kotlin
val path = c.fact.path
if (dropForm) {
    val spine = path.indexOfFirst { it != ELEMENT_ACCESSOR_IDX }.let { if (it < 0) path.size else it }
    for (k in 0..spine) if (policy.dropsValue(mark, k)) return false
}
if (path.any { it != ELEMENT_ACCESSOR_IDX }) return true
return policy.keeps(mark, elements = path.size)
```

**(e) The switch** (`ap/G6Drops.kt`, new; see Q1 in §8).

```kotlin
object G6Drops {
    /** G6 drop form (spec/acyclic-group-a-implementation.md §3). Default ON; `=false` gives the native policy. */
    @JvmField val drop: Boolean = flag("org.opentaint.bidi.g6Drop", "OPENTAINT_BIDI_G6_DROP", default = true)
}
```

`flag` is defined in §5.3. `ApOps.filterG6(c, f, dropForm)` (prototype
`ap/ApOps.kt:157-159`) stays as a test entry point: tests call both forms
without the switch.

### 3.4 Properties (Lean `G6DropForm.lean`)

The model reads a path as a list of accessors (`elem` or a field). It
models `LevelMarkPolicy`, `AndPolicy`, the production accumulation and
the reference.

| Claim | Theorem | Statement |
| --- | --- | --- |
| D1a | `drop_extends_native` | R1 removes every mark that native removes |
| D1b | `native_without_boxed_level` | With no boxed level `k ≤ spine(p)`, R1 is native at `p` |
| D1c | `tracking_never_removed` | A primitive-tracking mark is never removed, natively or by R1 |
| D2 | `removed_on_region` | If R1 removes `t` at `q`, it removes `t` at every position below `q`, under A2 |
| D3 | `kept_exact_keeps_cut` | Prefix closure (ap.md S5), under A2: R1 keeps `t` on `x.p.$` ⇒ R1 keeps `t` on every cut form `x.q.MAY`, `q` a prefix of `p` |
| D4 | `monotone_in_K` | Under A2, for `K ≤ K'`: R1 keeps `t` at the cut of `K'` ⇒ R1 keeps `t` at the cut of `K`. A larger K only removes marks |
| D5 | `m4_native_breaks`, `native_not_prefix_closed`, `m4_drop_form` | Native fails D3 on M4; R1 removes `T` at `x.[].value` and at `x.[].MAY`, and keeps it at `x` |
| D6 | `conj_keeps`, `conj_dropsValue` | `TypeFilter.and` of two level policies is a level policy (`prim` and `boxed` are joined by OR), so D1-D4 hold for it |
| D7a | `impl_is_drop_form` | The production accumulation `droppedAt` equals the predicate for every candidate mark |
| D7b | `impl_non_candidate` | Production never removes a non-candidate mark beyond native |
| D7c | `drop_form_above_first` | Above the first boxed level, R1 is native whatever the candidates |
| D7d | `reference_is_drop_form` | `ReferenceAlgebra.passes` with the drop form is the negation of the predicate |

**Assumptions.** These are code readings. No test checks them directly.

- A1. `candidates` holds every mark of the subtree at `[]^firstBoxed`:
  `foldAll` unions all leaves of a subtree (`ap/TrieOps.kt:287`). Every
  position with `spine(p) ≥ firstBoxed` is in that subtree. With D7a-D7c
  this makes production equal to the predicate on every mark that is
  present.
- A2. No fact has a position strictly below a true primitive spine level
  (`int`, `char`, …; primitive and not boxed). D2-D4 need it only for a
  cut that ends exactly at such a level. The path filter rejects a field
  and an element below `int` (`jvm-test:JIRTypeFiltersTest`, rows
  `int / f` and `int[] / [].f`). It accepts a class-static accessor
  (`int / cls.f`, `int[] / [].cls`). The analyzer makes a class-static
  accessor only as the first accessor of the `ClassStatic` base: static
  field access (`jvm:ap/ifds/MethodFlowFunctionUtils.kt:51-58`,
  `StaticRefAccess`) and static alias roots
  (`jvm:ap/ifds/alias/JIRIntraProcAliasAnalysis.kt:143-145`). A
  `ClassStatic` base never has a primitive type. R1 does not change this
  case; native has it too. See Q2.
- A3. The field limit counts every accessor of the model. Production
  counts fields and elements only (`ap/AccessorTable.kt:58`,
  `isCounted`); the class-static accessor is not counted and is outside
  the model by A2.

**Differences between model and production.** The model has one mark at a
time; production filters mark sets with the same per-mark decision
(`keepPolicyMarks`, `MarkSet` minus). The model ignores the exclusion `E`
of an any leaf: `E` only removes positions from a region, so D2 holds for
the smaller region too. The model has no `may` path filter: R1 runs after
it and does not change it.

### 3.5 Tests

Every changed test asserts both forms. It selects the expectation with
`G6Drops.drop`, or calls `ApOps.filterG6` with both values. So every gate
arm (§6) passes with 0 failed tests.

| Test | Change |
| --- | --- |
| `test:PrimitiveValuesTest` | Add the prototype test "level policy knows its boxed levels and the conjunction keeps the native decision" |
| `jvm-test:JIRTypeFiltersTest` | Add "boxed element levels are known to the policy". In "field and class accessors stop the primitive policy…", the three facts below `Integer` (`value`, `value.[]`, `[].value` under `Integer[]`) are dropped with R1 and kept natively |
| `jvm-test:JIRG6DropPrefixTest` (new, port) | P1-P6 on 29 real JIR types, all paths of length ≤ 3 (no class-static accessor in its alphabet): prefix closure, boxed coherence, primitive-tracking and no-boxed types native, runtime = reference. Native has 1,114 breaks, the drop form 0. Add one multi-leaf case per boxed type for A1: a tree with leaves at `[]^k`, `[]^k.value` and a sibling field, filtered as one fact |
| `jvm-test:JIRStringChainFiltersTest` (new, port) | The decision rows of the production filters; no type breaks a cut prefix with the drop form |
| `test:G6DropFormFixtureTest` (new) | Analysis fixtures without the stop-policy code: M4 from `DecidedStopAttackTest.kt:342-410` (`proto/dt-owner-cover-20261124`); D5 (6 variants) and D6 (16 variants, the cut above the boxed level) from `DeepChainFixtureTest.kt`; the String-chain variants from `StringChainFixtureTest.kt` (the 13 breaking variants, the 189 unchanged ones, the callee recall-loss case), both on `proto/g6-drop-xsub-20261120`. Expected: R1 gives `{A}` where native gives `{A, B}` in M4, D5, D6 (`policy=true`) and the 13 String-chain variants; every other variant is the same in both forms (`docs/reports/g6-drop-xsub-20261120.md` §5.1) |

The source files of D5, D6 and the String chains also hold DECIDED-stop
checks, and they set `StopPolicy.PROPERTY`, which is not on
`620cd5659`. Port the fixture programs and their final-report
assertions only.

### 3.6 Cost

Site: once per type-filter application on a TAINT tree whose policy has a
boxed level on the element spine of the fact. Work: one `foldAll` of the
subtree at the first boxed level, and per field subtree below it one
`foldAll`; `mapLeaves` only when a mark must go. Other type-filter
applications take the native path after one `boxedLevel` scan of the
fact spine.

Measured volume, one launch each (`docs/reports/acyclic-only-20261123.md`
§8): OWASP, R1 alone: 0 applications. Stirling-PDF and Conductor were
measured only in the combination launches `AO-1` (all prototype rules):
736 and 2,075 applications, 0 marks removed. R1 was not launched alone on
these two projects.

## 4. R2: an EXACT cleaner does not apply to a MUST leaf

### 4.1 Definition

A cleaner is `κ = (β.p, reach, M)`. A TAINT leaf `λ = β.q.MUST/E` (on
layer `ℓ`, marks `μ`) is at PART for `κ` when `q` is a prefix of `p` and
the point `β.p` is in `R(λ)` (`q = p`, or `E` admits `p[|q|]`).

```text
native, reach = EXACT, PART:  λ loses μ ∩ M on ℓ;  β.q.MUST/E with μ ∩ M is added on D
R2,     reach = EXACT, PART:  λ is unchanged (layer, marks, E)
```

All other rows keep the native result.

Example (OWASP `Thing2#doSomething`). `return new StringBuilder(i).toString()`.
The propagator `$RES = (Object $*OBJ).toString()` resets the mark at
`ret` with reach EXACT. The input is `ret.MUST/T` on N. Native gives
`ret.MUST/T` on D (a DEMAND witness at 151 of the 164 open acyclic OWASP
`doPost` roots). R2 keeps `ret.MUST/T` on N (Lean `thing2_native`,
`thing2_rule`).

Trade (approved, spec §5.5): the cleaned point stays tainted inside the
MUST region. R2 can confirm a report that native keeps provisional. It
can also confirm a report that native does not have at all: fixture 1 of
§4.6 goes from no result to a confirmed result.

### 4.2 Native code

| Site | Lines | Behavior |
| --- | --- | --- |
| `ap/Clean.kt` `cleanPosAt` | 7-14 | a MUST leaf on the spine at `d < |p|` is PART when `E` admits `p[d]`; at `d = |p|` it is PART unless reach is AT_AND_BELOW |
| `ap/Clean.kt` `TaintClean.gone` | 159-164 | the removed marks; empty in GROUP mode for a cleaner with a mark |
| `ap/Clean.kt` `TaintClean.cut` | 178-205 | PART: four branches; the `else` branch (`:200`) adds the DEMAND survivor; `:204` removes the marks |
| `ap/Clean.kt` `cleanSelectedFullMask` | 75-91 | run-1 FULL cleanup; uses the same `TaintClean` |
| `ap/Reference.kt` `cleanPos`, `cleanResRaw`, `concPart` | 409-427, 442-464, 490-504 | the reference (tests only); `concPart` runs only at PART for a cleaned concrete mark |
| `ap/ApOps.kt` `clean`, `cleanSelectedFullMask` | 126-154 | callers; add the selected protection |

Every cleaner on a TAINT tree runs `TaintClean`. The callers are
`ops.clean` and `ops.cleanSelectedFullMask` in
`engine/RunMethodCallServices.kt` (lines 240, 276, 298). The leaves on the
cleaner spine go through `cut`. The leaves below the cleaner path go
through the `inside` map (`ap/Clean.kt:167-170`), but an EXACT cleaner
has no `inside` part. So one hook in `cut` covers every EXACT cleaner on
a TAINT tree.

### 4.3 Code changes

Port from `proto/acyclic-only-20261123` (source commit `7813bb6ad` on
`proto/must-cleaner-20261121`). Do not port the prototype counters
(`note`, `takeLine`, `BIDI_MUST_IGNORE`); T1 has its own count (§5.2).

**(a) Runtime** (`ap/Clean.kt`, in `cut`, first statement of `Pos.PART`).

```kotlin
Pos.PART -> {
    // R2: an EXACT cleaner does not apply to a MUST leaf. The leaf keeps its layer, marks and E.
    if (MustIgnoresExactCleaner.enabled && cl.reach == CleanReach.EXACT && tail == Tail.ANY_TAINT) {
        m.r2Count?.add(mode, c.layer)                      // T1 only; null when the census is off
        return marks
    }
    val at = m.path(path.copyOf(d))
    ...                                                    // the native branches, unchanged
}
```

`tail` is the any tail of the tree for the any-marks, and `Tail.EXACT`
for the `$` marks. A `$` mark never reaches PART under an EXACT cleaner
(`cleanPosAt`: DISJOINT above `p`, INSIDE at `p`), so the hook acts on
any-marks only.

**(b) Reference** (`ap/Reference.kt`, first statement of `concPart`).

```kotlin
if (MustIgnoresExactCleaner.enabled && cl.reach == CleanReach.EXACT && c.fact.tail == Tail.ANY_TAINT) return listOf(c)
```

**(c) The switch** (`ap/Clean.kt`; see Q1).

```kotlin
object MustIgnoresExactCleaner {
    /** R2 (spec/acyclic-group-a-implementation.md §4). Default ON; `=false` gives the native survivor. */
    @JvmField val enabled: Boolean = flag("org.opentaint.bidi.mustIgnoresExactCleaner",
        "OPENTAINT_BIDI_MUST_IGNORES_EXACT_CLEANER", default = true)
}
```

### 4.4 Properties (Lean `MustExactCleaner.lean`)

The model has one base, one selected concrete mark and one leaf. It
models the reference position (`cleanPos`), the tree position
(`cleanPosAt`), the native PART rows (`nativePart`: the rows of
`concPart`; the rows of `cut` are the same by code reading) and R2
(`rulePart`).

| Claim | Theorem | Statement |
| --- | --- | --- |
| C1 | `native_exact_must_demotes` | Native PART, EXACT, MUST: the result is the leaf on DEMAND, same path, tail and `E` |
| C2 | `rule_exact_must_keeps` | R2 gives the input leaf |
| C3 | `rule_outside_scope` | Outside (EXACT, MUST), R2 is native |
| C4 | `native_is_rule_with_demand_layer` | In scope, native = R2 with the layer set to DEMAND |
| C5 | `same_positions` | For every leaf, cleaner and position: R2 rows and native rows cover the same positions |
| C6 | `rule_keeps_layer` | In scope (EXACT, MUST), R2 rows have the layer of the input. Outside the scope R2 is native (C3), and native can demote |
| C7 | `demand_input_unchanged` | On a DEMAND input, R2 = native |
| C8 | `change_only_in_scope` | The whole cleaner changes only at PART, for reach EXACT, a MUST leaf and a NORMAL input |
| C9 | `tree_form_is_reference` | For a leaf on the cleaner spine, `cleanPosAt` = `cleanPos`. This equates the positions only. With C1-C3 (stated on `nativePart`) it shows that the runtime hook and the reference hook select the same leaves in FULL mode |
| C10 | `no_finite_form_without_point` | Why native must demote: for a MUST leaf whose region holds the point `p`, every finite set of leaves that misses `p` misses a strict descendant of `p` in the region (executable witness `fresh`). So "the region without `p`" has no finite leaf form, and no K can make the native survivor NORMAL |

**Differences between model and production.**

- The model has one selected mark. Production removes `gone(marks)`
  (`ap/Clean.kt:159-164`) and keeps the other marks of the leaf. R2
  returns `marks` unchanged, so it keeps all of them.
- GROUP mode: `gone` is empty, so the runtime hook is never reached. The
  reference has no GROUP mode. C9 holds for FULL mode.
- The model has no protection. Production adds the selected protection
  after the cleaner (§2).
- The model has no run-1 output policy. Production applies it after the
  cleaner (a non-empty `E` goes to DEMAND in run 1). R2 does not change
  it, and the reference does the same (`cleanRes(run1 = true)`).
- C10 uses an open set of accessors (natural numbers). With a closed
  alphabet `Σ` the rest would be `⋃_{a∈Σ} p.a.MUST`. The analyzer does
  not enumerate the accessors of a value (`E` names excluded accessors
  only), so the open set is the production view.
- The existing model `ApSpec/AnyTaintExDefs.lean:291` (`partX`) and
  `ApSpec/Basic.lean:606` (`concPart`) describe the native PART row (and
  drop `E` on it; production keeps `E`). After R2 lands, the ApSpec
  theorems that use these rows describe the native cleaner. They are not
  re-proved here (§7).

### 4.5 Tests

Every changed test asserts both forms and selects the expectation with
`MustIgnoresExactCleaner.enabled`. The list is the prototype gate
(`acyclic-only/unit-tests/cl-1` and `jvm-cl-1`: 12 module and 2 jvm
failures); it was not re-run on `620cd5659`.

| Test | Expectation with R2 (native expectation kept for `enabled = false`) |
| --- | --- |
| `jvm-test:JIRLoweredCleanerEffectTest` "normal must ancestor follows exact below and subtree reach rows after field lowering" | EXACT at `x.f` on `x.MUST/{g}`: `{x.MUST/{f,g} N, x.f.MUST/Empty N}` (native: `x.f.MUST` on D) |
| `jvm-test:JIRLoweredCleanerEffectTest` "must and may at the named field retain own E until the primitive root reach result" | EXACT on `x.f.MUST/{g}` N: the input (native: the input on D). The MAY row is the same in both forms |
| `test:CleanerTest` (3 cases), `test:ReferenceOperationsTest` (2 "AP 4_7" cases), `test:FieldCleanStepTest` (1) | The EXACT/MUST PART rows only: the input leaf, same layer. The other rows of each table are the same in both forms |
| `test:OneRunAcceptanceTest` "all three primitive cleaner reaches at a real call…", index 3, reach EXACT (`:226-247`) | Facts: `{x.MUST/T N}` (native: `x.MUST/T` on D). Sink layers: "at f", "below f" and "at k" all NORMAL (native: all DEMAND). All targets NORMAL. `selectedDemand` empty. This is the approved trade at unit level: the cleaned point `x.f` reaches its sink on NORMAL |
| `test:DemandLinkTest` "DLINK retains provisional sink guidance and refines its normal report by run7" (`:20-60`) | The test uses the EXACT survivor as its DEMAND maker (`:37`). With R2 it has no DEMAND link, and it ends at run 3 with the same report. Keep the native body under `enabled = false`. Under R2, assert runs `[1, 2, 3]`, the same single report, and no DEMAND link. Add a follow-up DLINK fixture with another DEMAND maker (§9) |
| `test:UniformRootCleanerTerminationTest` (2 cases), `test:DescendantCleanerTerminationTest` (1), `test:AcyclicTerminationBaselineTest.protectedGlobalCutGrowth` | The signed-off results of §4.6 under R2; the native results under `enabled = false` |

Add one runtime-vs-reference table test: for each reach and each any
tail, an EXACT cleaner at `x.f` and at `x` on `x.MUST/E` (`E` empty and
`{g}`), both layers, run 1 and restricted, FULL mode: `ops.clean` and
`cleanRes` give the same rows, with R2 on and off (`filterG6`-style test
entry `TaintClean` with an explicit `mustIgnores` argument).
`ConcreteDesignDifferentialTest` already compares the two on generated
programs.

### 4.6 Signed-off result changes

| Fixture | Native | R2 |
| --- | --- | --- |
| `UniformRootCleanerTerminationTest` "exact-root sink cannot renew permission through the root cleaner" | 3 / `NO_DEMAND_EDGE`; C = {}, P = {} | 1 / `NO_DEMAND_EDGE`; C = {root-cleaner tree sink} |
| `UniformRootCleanerTerminationTest` "uniform source exact-root selected cleanup renews the same target through run101" | 101 / `RUN_LIMIT`; P = {root-cleaner tree sink} | 1 / `NO_DEMAND_EDGE`; C = {root-cleaner tree sink} |
| `DescendantCleanerTerminationTest` "descendant exact cleaner repeats Target demand…" | 101 / `RUN_LIMIT`; P = {observe remaining T} | 1 / `NO_DEMAND_EDGE`; C = {observe remaining T} |
| `AcyclicTerminationBaselineTest.protectedGlobalCutGrowth` | 101 / `RUN_LIMIT`; P = {observe} | 101 / `RUN_LIMIT`; C = {observe} |

In the module analyses R2 also makes one analysis end earlier with the
same report (`DemandLinkTest`). Spec §5.5 says "Module: 4 report changes,
nothing else"; the 12 changed unit expectations and the earlier end are
in addition to the report changes.

### 4.7 Cost

Site: once per EXACT cleaner application on the any-marks of a MUST leaf
at PART. The check is three comparisons, and the rule removes work (no
survivor tree, no DEMAND row). Volume, one launch each: OWASP, R2 alone:
2,005 forward NORMAL applications, 0 forward DEMAND, 0 backward, 2,662 in
run 1. Stirling-PDF and Conductor only in the combination launches
`AO-1`: 24 forward NORMAL, 5 forward DEMAND, 12 in run 1 (Stirling-PDF);
64 forward NORMAL, 42 forward DEMAND (Conductor); 0 backward on both. The
combination changes the volume: OWASP forward NORMAL is 824 in `AO-1`
against 2,005 alone.

## 5. Order of work and common parts

### 5.1 Commits

1. T1 and the flag helper (§5.2, §5.3). They change no run.
2. R1 code (§3.3) and R1 tests (§3.5). Gate R1 alone (§6).
3. R2 code (§4.3) and R2 tests (§4.5, §4.6). Gate R2 alone and the pair
   R1 + R2 (§6).
4. The Lean package (added with this proposal) and the spec updates (§7).

### 5.2 T1: sink-route census and R2 count (diagnostic)

Port `engine/SinkRouteCensus.kt` from `proto/dt-owner-route-20261124`
(`f2032b5c9`, `29e5997f4`) and its leaf printer `ShapeCensus.pattern`
from `proto/must-cover-shape-20261124`. Off by default; it never changes
a run. Two changes against the prototype:

- Keep the state per analysis, in `SharedObjects`, not in a JVM-global
  object. The prototype set is global and is cleared at each analysis
  end, so two analyses in one JVM would mix.
- Add the R2 count: four `LongAdder`s (forward NORMAL, forward DEMAND,
  backward, run 1) in `ApManager.r2Count`, made only when the census is
  on. `ApManager` is one per analysis (`SharedObjects.ap`, "analysis
  owners shared across runs"), and `TaintClean` already holds it.

```kotlin
// engine/RunMethodLocalServices.kt, witness (:367), after the report id `id` is interned (forward only):
if (census != null) for (e in edges) if (e.layer == Layer.NORMAL)
    census.add(id, core.ops.leaves(e.facts))
// driver/IterationDriver.kt, analyze.end (:48), once per analysis:
census?.let { log(it.takeLine(analysisId)) }   // BIDI_SINK_ROUTES count=… digest=… r2=FN/FD/B/R1 analysis=…
```

`IterationDriver` has no `analysisId` at `620cd5659`. Port it from the
prototype (`driver/IterationDriver.kt:49` on
`proto/dt-owner-route-20261124`), and log through the driver logger, not
`AcResidual.emit` (the residual diagnostic is not ported).

A route is `rule@method:statement|leaf`. Only NORMAL leaves are recorded,
so the text has no layer. The leaf text uses accessor names, mark names,
tail and `E`. It must not contain an identity hash (an earlier census
lost a match to `@hex` text). With `-Dacyclic.out=<dir>` the sorted set
goes to `sink-routes-<analysis>.txt`; the log line has the count, a
SHA-256 digest and the R2 count.

### 5.3 Flags

```kotlin
// ap/Flags.kt (new)
internal fun flag(property: String, env: String, default: Boolean): Boolean =
    System.getProperty(property)?.toBooleanStrictOrNull()
        ?: System.getenv(env)?.toBooleanStrictOrNull()
        ?: default
```

| Flag | Default | Use |
| --- | --- | --- |
| `org.opentaint.bidi.g6Drop` / `OPENTAINT_BIDI_G6_DROP` | `true` | `false` gives the native policy, for the gate and for a regression hunt |
| `org.opentaint.bidi.mustIgnoresExactCleaner` / `OPENTAINT_BIDI_MUST_IGNORES_EXACT_CLEANER` | `true` | `false` gives the native survivor |
| `org.opentaint.bidi.sinkRouteCensus` / `OPENTAINT_BIDI_SINK_ROUTE_CENSUS` | `false` | the gate diagnostic |

The flags are read once, at class load. Default ON is the recommended
answer to Q1 (§8).

### 5.4 Test modes

The module suite and the jvm suite run in two modes: the default (R1 and
R2 on) and native (both flags `false`, set as system properties of a
second Gradle test task). Each changed test asserts the expectation of
its mode (§3.5, §4.5). So the native path keeps its unit coverage while
the flags exist.

## 6. Gate

Design-guide rules 4-6 and the decisions of 24 November. Single launch
per arm. A second launch only when one number does not decide. Hold the
lock `/drive-testcomp/opentaint-go-rules/termination-next-20261119/.projects.lock`
for every project and suite launch.

| Arm | `g6Drop` | `mustIgnoresExactCleaner` |
| --- | --- | --- |
| native | false | false |
| R1 | true | false |
| R2 | false | true |
| R1 + R2 (the landed default) | true | true |

Every project arm runs with `sinkRouteCensus=true`. No arm runs the
residual diagnostic, so the times are not comparable with spec §6 and
native is measured again here.

**Suites.**

| Suite | Pass condition |
| --- | --- |
| Module suite (2,765 tests, 314 analyses) | 0 failed tests in every arm (§5.4). Analysis reports by report descriptor and confirmed/provisional status, against native: R1 changes only the decided G6 fixtures of §3.5 (finding B lost); R2 changes only the four fixtures of §4.6; R1 + R2 the union. End runs may change only in R2 arms |
| Jvm suite (473 tests, 6 analyses) | 0 failed tests in every arm; 6 of 6 analyses identical |
| Rule suite (585 analyses) | Reports identical in every arm |

**Projects.** OWASP, Stirling-PDF, Conductor.

| Check | Pass condition |
| --- | --- |
| Results | Confirmed and provisional results and SARIF code flows identical to native |
| Time | Driver time not worse than native beyond the spread of spec §6 (OWASP 150.2-153.1 s natively there, with the diagnostic). Stirling-PDF: timeout 7,200 s; native can stall in run 11, and then the reference result is the completed native run of spec §6 (32 / 2). Conductor: every arm times out in run 8 (spec §6); compare the published results at the timeout and the time to the H7 barrier |
| Memory | Largest heap after a GC not worse than native. Weak: peak RSS saturates near the 8 GiB heap, and Conductor is at the heap limit in every arm (spec §6) |
| Routes, R1 | Route set identical to native in every analysis (R1 removed 0 marks on these projects in `AO-1`) |
| Routes, R2 and R1 + R2 | In every analysis with R2 count 0: route set identical to native. In every analysis with R2 count > 0: list the route differences in the gate report, per project; the owner signs them off (Q3) |

R1 + R2 was never measured as a pair (spec, "Final classification").
The R2 route changes were never measured alone (spec §5.5). This gate
measures both.

**Withdrawal.** A rule goes back to `default = false`, and stays in the
code behind its flag, if one of these holds in its arm:

1. a report changes outside the decided G6 fixtures (R1) or §4.6 (R2);
2. a route differs in an analysis where the rule does not act (R1: any
   analysis; R2: an analysis with R2 count 0);
3. the owner rejects a listed R2 route difference;
4. time or memory get worse beyond the spread.

## 7. Spec and model updates after the gate

- `ap.md` §4.7 and `interpreter.md` §5.1: state R2 and R1 as the cleaner
  and mark-policy semantics (today they state the native rows; the
  `MarkPolicy` comment in `ap/Primitives.kt:18-22` still calls G6 a gap).
- `acyclic-convergence-proposal.md` "Final classification" and §5.5, and
  `natural-termination-proposal.md` §9 item 1: group A landed, with the
  commit ids and the gate result.
- `ApSpec`: add a module that states `partX` with R2 (C1-C4 give the
  relation to the native row). Re-proving the ApSpec closure on the new
  row is a separate task; until then the ApSpec cleaner theorems describe
  the native cleaner.

## 8. Open questions for the owner

**Q1. Flags or plain semantics.** The spec says group A "can land behind
its flags". Both rules are decided semantics, and every later prototype
assumes them. Options: (a) flags default ON, native reachable with
`=false` for gates, two test modes (this proposal); (b) no flags, native
deleted, one test mode; (c) flags default OFF. Recommended: (a) now, (b)
after one gate cycle. (a) costs the second test mode of §5.4.

**Q2. True primitive levels (A2).** R1 acts only at boxed levels, as
decided. At a true primitive level native has the same non-monotone
shape, but only through a class-static accessor below a primitive value:

```text
x: int.  Native and R1 drop T at the spine leaf x.MAY (level 0 is int).
The path filter admits x.cls(C).f below int, and the policy keeps T there.
So x.MAY/T is dropped while x.cls(C).f.$/T would be kept.
```

The analyzer never makes this fact (a class-static accessor is only the
first accessor of the `ClassStatic` base). Recommended: no change; keep
A2 as a stated assumption. If a test should pin it, add the `int / cls.f`
row to `JIRG6DropPrefixTest` as a named native exception, outside the P1
assertion (P1 would fail on it). The alternative is to treat a true
primitive level like a boxed one in R1; that is a new semantic change.

**Q3. R2 route changes.** The R2 route changes are intended by the
decision of 24 November, but they were never measured alone, and the
census cannot tie a route to the cleaner that made it. The gate (§6)
accepts route differences only in analyses where R2 acts, and lists them
for sign-off. Recommended: this condition. Alternative: accept every
route difference in an analysis where R2 acts, with no sign-off.

**Q4. Protection on the kept leaf.** With R2 the kept NORMAL leaf gets the
selected protection of the cleaned mark (§2), because the wrapper in
`ApOps.clean` protects every result on the cleaner base. The prototype
gates ran this way. Recommended: keep it (measured). Alternative: give
the kept leaf only the protection of the input. Not measured.

## 9. Checklist and blind spots

```text
[x] Failure class and real trace: spec §4 (cleaner survivor: 151 of 164 OWASP roots; G6: fixture M4)
[x] Ablation on the real case: R2 alone takes the OWASP residual from 711-735 to 24 (spec §5.5)
[~] Native prototype: one OWASP launch per single-rule arm; Stirling-PDF and Conductor only in AO-1; the pair R1 + R2 not measured (§6 does it)
[x] Execution site and volume: §3.6, §4.7
[x] Selected semantic scope: §2 (with the protection consequence of R2)
[x] Proof scope and model differences: §3.4, §4.4 (27 claims; propext and Quot.sound only)
[x] Withdrawal condition: §6
```

- The Lean models are local. They prove the operation-level properties
  (prefix closure and monotonicity in K under A2, the layer-only change,
  equal positions, equal tree and reference positions). They do not
  prove whole-analyzer soundness or termination with the new rows.
- A1-A3 are code readings. `JIRG6DropPrefixTest` has no class-static
  accessor and mostly single-leaf facts; §3.5 adds multi-leaf cases for
  A1.
- R1 never acts on OWASP or the rule suite, and removed 0 marks on
  Stirling-PDF and Conductor in `AO-1`. Its effect is measured on
  synthetic fixtures only (M4, D5, D6, String chains).
- R2 project evidence: one OWASP launch alone (128.1 s, residual 24) and
  the `AO-1` / `AO-C5` combinations. Stirling-PDF and Conductor have no
  R2-only launch. R2 never fired in a backward run on the measured
  projects (0 backward applications).
- The sink-route census has never run on an R2-only arm, and it cannot
  attribute a route difference to a cleaner (Q3).
- The protection consequence of R2 (§2, Q4) is measured only as part of
  the prototype gates; no test isolates it.
- `DemandLinkTest` loses its DEMAND maker under R2; DLINK coverage under
  the default needs a new fixture with another DEMAND maker.
- The failing tests were read from the prototype gate, not re-run on
  `620cd5659`.
