# Implementation proposal: group A rules of the acyclic proposal

Status: PROPOSAL, 24 November 2026 (revision 4). Revision 2 followed an
adversarial review against the code. Revision 3 applies the owner
decision of 24 November: the rules land as plain semantics, with no
switch, and the landed code has no census and no counter. Revision 4
applies the owner answers to the open questions: no accessor after a
true primitive (§3.3 (e)), no separate route list (§6), keep the
protection (§2). Base:
`saloed/bidirectional` at `620cd5659`. It follows
[impl-proposal-guide.md](impl-proposal-guide.md),
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

Group A has two rules. Both are decided semantics. This proposal
replaces the native behavior with them in production code, with their
tests and their proofs.

| Id | Rule | Where it acts | What changes | Proof |
| --- | --- | --- | --- | --- |
| R1 | G6 drop form (spec §5.1) | type filter: mark policy (`ap/Filter.kt`) and path filter (`JIRFactTypeChecker`) | At and below a boxed spine level, a mark that is not primitive-tracking is removed from the whole value, field leaves included. No accessor (field, element or class-static) follows a true primitive value | `G6DropForm.lean`, 17 claims |
| R2 | An EXACT cleaner does not apply to a MUST leaf (spec §5.5) | cleaner, PART row (`ap/Clean.kt`), both directions, every run | The MUST leaf stays on its layer; native moves it to DEMAND | `MustExactCleaner.lean`, 12 claims |

The native behavior is deleted. The landed code has no switch, no census
and no counter. The whole analyzer is measured after the implementation
lands (§6).

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
| 24 Nov | Serve every route | Not a separate check for group A: G6's only route change is the decided M4 removal, and R2's route changes are intended (§6) |
| 24 Nov | Single launch per measurement | §6 |
| 24 Nov | Robustness rule: never relax the relative caps | R1 and R2 make no fact deeper and no new fact (§2) |
| 24 Nov | No switch such as `MustIgnoresExactCleaner.enabled`, and no in-code census: this is the implementation, not a prototype | §3.3, §4.3, §6 |
| 24 Nov | No field and no static can follow a true primitive value | §3.3 (e); A2 becomes a code fact |
| 24 Nov | No separate route list: the whole analyzer is measured after the implementation lands | §6 |
| 24 Nov | The kept MUST leaf keeps the selected protection | §2 |

No question is open (§8).

## 2. Semantic scope

**Changed (R1).** The mark policy of a type filter, at and below the first
boxed spine level of the filtered value. Native removes a mark only from
the spine leaf of a level. R1 also removes it from every leaf below the
first boxed level that drops it. R1 only removes marks. It never adds a
mark, a leaf or a fact.

**Changed (R1, path filter).** The path filter rejects a class-static
accessor below a value of a true primitive type (`int`, `char`, …; not a
boxed class). Today it rejects a field and an element there, but it
accepts a class-static accessor (`JIRFactTypeChecker.kt:84`). After the
change no accessor can follow a true primitive value. This only removes
facts, and the analyzer makes no such fact today (A2). R1 acts wherever a type filter with a mark policy
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
with this behavior. Decision of 24 November: keep it.

**Not changed in GROUP mark mode.** In GROUP mode `gone()` returns no mark
for a cleaner with a selected mark (`ap/Clean.kt:162`), so native removes
nothing there and the R2 check is not reached. R2 acts in FULL mode only.

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
- The path-filter change is in `JIRFactTypeChecker`, which the IFDS
  engine also uses (`jvm:ap/ifds/analysis/JIRAnalysisManager.kt:76`,
  `jvm:ap/ifds/analysis/JIRMethodAnalysisContext.kt:25`). There too a
  class-static accessor is only the first accessor of the `ClassStatic`
  base, so the change removes no fact that the IFDS engine makes. The jvm
  suite covers it.
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
keeps(t, k)      = ¬prim(k) ∨ pt(t)                 (as today)
dropsValue(t, k) = boxed(k) ∧ ¬keeps(t, k)
spine(p)         = number of leading element accessors of the path p

removedNative(t, p) = onSpine(p) ∧ ¬keeps(t, spine(p))                    (deleted)
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
| `jvm:ap/ifds/JIRFactTypeChecker.kt` `AccessorFilter.checkAccessor` | 82-133 | the path filter (`may`); a class-static accessor is accepted for every type (`:84`); a field and an element are rejected below a primitive (`:105`, `:113`) |

No other site reads a mark policy.

Example of the native defect (fixture M4, reduction). `x: Integer[]`; the
mark `T` is not primitive-tracking. At `K = 1` the fact is `x.[].MAY/T`,
a spine leaf of the boxed level 1: native drops it. At `K = 2` the fact
is `x.[].value.$/T`, a field leaf: native keeps it. A larger K adds a
finding (Lean `m4_native_breaks`, `native_not_prefix_closed`).

### 3.3 Code changes

Take the logic of `ap/Primitives.kt`, `ap/Filter.kt`,
`interp/FormsReference.kt` and `jvm:bidi/interp/JIRTypeFilters.kt` from
`proto/acyclic-only-20261123` (commits `8358d392e`, `4b14e086e`, squashed
in `3693de8a1`). Do not take the switch `G6Drops`, the counters
(`G6Drops.DropCounters`, `ApManager.g6DropCounters`), the `dropForm`
parameters or `ApOps.filterG6`.

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
level. Update the `MarkPolicy` comment (`ap/Primitives.kt:18-22`): G6 is
no longer a gap.

**(b) The JVM policy** (`jvm:bidi/interp/JIRTypeFilters.kt` `make`).

```kotlin
val levels = generateSequence(t) { it.ifArrayGetElementType }.toList()
val primitive = levels.map { it.typeName == "java.lang.Character" || it.unboxIfNeeded() is JIRPrimitiveType }
val boxed = levels.mapIndexed { k, type -> primitive[k] && type !is JIRPrimitiveType }
return TypeFilter(checker.localFilter(t),
    markPolicy = if (true !in primitive) null
        else LevelMarkPolicy(primitive.toBooleanArray(), boxed.toBooleanArray(), ::isPrimitiveTracking))
```

`keeps` is today's lambda. Only `boxed` is new.

**(c) The runtime filter** (`ap/Filter.kt`). `markPolicyOnElements`
stays as the path for a fact with no boxed level on its spine: there the
drop form and the spine-only rule are equal (Lean D1b, D7c). Rename it
`markPolicyOnSpine`.

```kotlin
internal fun filterFacts(m: ApManager, c: Facts, f: TypeFilter): Facts? {
    ...
    is TaintTree -> {
        var result = m.taintAlg.filterPath(m, c.root, f.may)
        val policy = f.markPolicy
        if (result != null && policy != null) result = markPolicy(m, result, policy)
        ...
    }
}

/** G6 drop form: a boxed value carries only primitive-tracking marks, on every leaf below the boxed level. */
private fun markPolicy(m: ApManager, n: TaintNode, policy: MarkPolicy): TaintNode? {
    val spine = n.elementSpine()                                   // [e]^0, [e]^1, …
    val firstBoxed = spine.indices.firstOrNull { policy.boxedLevel(it) }
        ?: return markPolicyOnSpine(m, n, policy)                  // no boxed level on this fact
    val candidates = m.taintAlg.foldAll(spine[firstBoxed], m.cancellation).let { it.exact + it.any }
    // droppedAt[j] = { t ∈ candidates | ∃ k: firstBoxed ≤ k ≤ j, boxedLevel(k), dropsValue(t, k) }
    val droppedAt = accumulate(spine.indices, firstBoxed, candidates, policy)
    // Bottom-up rebuild, from the deepest spine node:
    //   spine leaf j     := keepPolicyMarks(leaf, policy, j) − droppedAt[j]
    //   element child    := the rebuilt node j+1
    //   field child of j := dropOnValue(child, droppedAt[j])           (every leaf of the subtree)
    ...
}

private fun dropOnValue(m: ApManager, n: TaintNode, d: MarkSet): TaintNode? {
    val all = m.taintAlg.foldAll(n, m.cancellation)
    if (all.exact.data.none { TaintMark(it) in d } && all.any.data.none { TaintMark(it) in d }) return n   // no copy
    return m.taintAlg.mapLeaves(n, m.cancellation) { leaf -> /* leaf.exact − d, leaf.any − d; same object if unchanged */ }
}
```

The prototype functions `markPolicyDropForm` and `dropOnValue`
(`ap/Filter.kt` on the prototype branch) are the reference for the
rebuild. Remove their counter lines and the `normal` parameter (it fed a
counter only).

**(d) The reference** (`interp/FormsReference.kt` `passes`). After the
path filter and the `markPolicy` null check:

```kotlin
val path = c.fact.path
val spine = path.indexOfFirst { it != ELEMENT_ACCESSOR_IDX }.let { if (it < 0) path.size else it }
for (k in 0..spine) if (policy.dropsValue(mark, k)) return false
if (path.any { it != ELEMENT_ACCESSOR_IDX }) return true
return policy.keeps(mark, elements = path.size)
```

**(e) No accessor after a true primitive**
(`jvm:ap/ifds/JIRFactTypeChecker.kt`, `AccessorFilter.checkAccessor`,
`:84`). Split the first branch:

```kotlin
is FinalAccessor -> return FilterResult.Accept
// A value of a true primitive type has no fields, no elements and no statics below it.
is ClassStaticAccessor -> return if (actualType is JIRPrimitiveType) FilterResult.Reject else FilterResult.Accept
```

`actualType` is the type of the current level: the element filter passes
the element type to the next level (`:116-120`), so `int[] / [].cls` is
rejected too. A boxed class (`Integer`, `Character`) is not a
`JIRPrimitiveType`; it keeps its fields (`value`) and the native
class-static answer.

### 3.4 Properties (Lean `G6DropForm.lean`)

The model reads a path as a list of accessors (`elem` or a field). It
models `LevelMarkPolicy`, `AndPolicy`, the production accumulation and
the reference. It also models the deleted native rule, to show the
defect that R1 removes.

| Claim | Theorem | Statement |
| --- | --- | --- |
| D1a | `drop_extends_native` | R1 removes every mark that native removes |
| D1b | `native_without_boxed_level` | With no boxed level `k ≤ spine(p)`, R1 equals the spine-only rule at `p` |
| D1c | `tracking_never_removed` | A primitive-tracking mark is never removed |
| D2 | `removed_on_region` | If R1 removes `t` at `q`, it removes `t` at every position below `q` (side condition: `q` is not a true-primitive spine node with a position below it) |
| D3 | `kept_exact_keeps_cut`, `kept_exact_keeps_cut_admitted` | Prefix closure (ap.md S5): for every fact `x.p.$` that the path filter admits, R1 keeps `t` on `x.p.$` ⇒ R1 keeps `t` on every cut form `x.q.MAY`, `q` a prefix of `p` |
| D4 | `monotone_in_K`, `monotone_in_K_admitted` | For every admitted fact and `K ≤ K'`: R1 keeps `t` at the cut of `K'` ⇒ R1 keeps `t` at the cut of `K`. A larger K only removes marks |
| D5 | `m4_native_breaks`, `native_not_prefix_closed`, `m4_drop_form` | The native rule fails D3 on M4; R1 removes `T` at `x.[].value` and at `x.[].MAY`, and keeps it at `x` |
| D6 | `conj_keeps`, `conj_dropsValue` | `TypeFilter.and` of two level policies is a level policy (`prim` and `boxed` are joined by OR), so D1-D4 hold for it |
| D7a | `impl_is_drop_form` | The production accumulation `droppedAt` equals the predicate for every candidate mark |
| D7b | `impl_non_candidate` | Production never removes a non-candidate mark beyond the spine-only rule |
| D7c | `drop_form_above_first` | Above the first boxed level, R1 equals the spine-only rule whatever the candidates |
| D7d | `reference_is_drop_form` | `ReferenceAlgebra.passes` is the negation of the predicate |

**Assumptions and code facts.** A1 and A3 are code readings. A2 is a code
fact after §3.3 (e).

- A1. `candidates` holds every mark of the subtree at `[]^firstBoxed`:
  `foldAll` unions all leaves of a subtree (`ap/TrieOps.kt:287`). Every
  position with `spine(p) ≥ firstBoxed` is in that subtree. With D7a-D7c
  this makes production equal to the predicate on every mark that is
  present.
- A2 (code fact C-A2). The path filter admits no position strictly below
  a true primitive spine level (`int`, `char`, …; primitive and not
  boxed): it rejects a field and an element there today
  (`JIRFactTypeChecker.kt:105`, `:113`), and a class-static accessor after
  §3.3 (e). In the model this is `Admitted`; D3 and D4 hold for every
  admitted fact with no side condition. Before the change the filter
  admitted `int / cls.f`, but the analyzer never made such a fact: it
  makes a class-static accessor only as the first accessor of the
  `ClassStatic` base (static field access,
  `jvm:ap/ifds/MethodFlowFunctionUtils.kt:51-58`; static alias roots,
  `jvm:ap/ifds/alias/JIRIntraProcAliasAnalysis.kt:143-145`).
- A3. The field limit counts every accessor of the model. Production
  counts fields and elements only (`ap/AccessorTable.kt:58`,
  `isCounted`); the class-static accessor is not counted. It occurs only
  as the first accessor of the `ClassStatic` base, which has no mark
  policy, so it never meets the mark policy.

**Differences between model and production.** The model has one mark at a
time; production filters mark sets with the same per-mark decision
(`keepPolicyMarks`, `MarkSet` minus). The model ignores the exclusion `E`
of an any leaf: `E` only removes positions from a region, so D2 holds for
the smaller region too. The model has no `may` path filter: R1 runs after
it and does not change it.

### 3.5 Tests

The tests assert R1 only. No test calls the deleted rule.

| Test | Change |
| --- | --- |
| `test:PrimitiveValuesTest` | Add the prototype test "level policy knows its boxed levels and the conjunction keeps the native decision" (rename: "…keeps the level decision") |
| `jvm-test:JIRTypeFiltersTest` | Add "boxed element levels are known to the policy". In "local path checks follow first field array element object and static accessor rows", the rows `int / cls.f` and `int[] / [].cls` become `false`. In "field and class accessors stop the primitive policy…", the three facts below `Integer` (`value`, `value.[]`, `[].value` under `Integer[]`) are now dropped by the mark policy, and `x.cls` under `int` and `x.[].[].cls.f` under `int[][]` are now rejected by the path filter (rename the test: class accessors no longer pass below a primitive) |
| `jvm-test:JIRG6DropPrefixTest` (new, from the prototype) | On 29 real JIR types and all paths of length ≤ 3, with a class-static accessor added to its alphabet (A2): P1 prefix closure, P2 boxed coherence, P3 a kept cut lies above the level where the exact fact loses the mark, P4 a primitive-tracking mark is never removed, P5 for a type with no boxed level a position below a field keeps every mark, P6 runtime = reference. Drop the native comparison (the native break count is Lean D5 and the prototype report). Add one multi-leaf case per boxed type for A1: a tree with leaves at `[]^k`, `[]^k.value` and a sibling field, filtered as one fact |
| `jvm-test:JIRStringChainFiltersTest` (new, from the prototype) | The decision rows of the production filters; no type breaks a cut prefix |
| `test:G6DropFormFixtureTest` (new) | Analysis fixtures, without the stop-policy code: M4 from `DecidedStopAttackTest.kt:342-410` (`proto/dt-owner-cover-20261124`); D5 (6 variants) and D6 (16 variants, the cut above the boxed level) from `DeepChainFixtureTest.kt`; the String-chain variants from `StringChainFixtureTest.kt` (the 13 variants that lose B, the 189 unchanged ones, the callee recall-loss case), both on `proto/g6-drop-xsub-20261120`. Expected: `{A}` in M4, D5, D6 (`policy=true`) and the 13 String-chain variants; every other variant as in `docs/reports/g6-drop-xsub-20261120.md` §5.1 |

The source files of D5, D6 and the String chains also hold DECIDED-stop
checks, and they set `StopPolicy.PROPERTY`, which is not on
`620cd5659`. Take the fixture programs and their final-report
assertions only.

### 3.6 Cost

Site: once per type-filter application on a TAINT tree whose policy has a
boxed level on the element spine of the fact. Work: one `foldAll` of the
subtree at the first boxed level, and per field subtree below it one
`foldAll`; `mapLeaves` only when a mark must go. Other type-filter
applications take the spine-only path after one `boxedLevel` scan of the
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
native (deleted), reach = EXACT, PART:  λ loses μ ∩ M on ℓ;  β.q.MUST/E with μ ∩ M is added on D
R2,               reach = EXACT, PART:  λ is unchanged (layer, marks, E)
```

All other rows keep today's result.

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
has no `inside` part. So one change in `cut` covers every EXACT cleaner
on a TAINT tree.

### 4.3 Code changes

The logic comes from `proto/acyclic-only-20261123` (source commit
`7813bb6ad` on `proto/must-cleaner-20261121`). Do not take the object
`MustIgnoresExactCleaner` (switch and counters), `BIDI_MUST_IGNORE` or
the driver log line.

**(a) Runtime** (`ap/Clean.kt`, in `cut`, first statement of `Pos.PART`).

```kotlin
Pos.PART -> {
    // An EXACT cleaner does not apply to a MUST leaf: the leaf keeps its layer, marks and E (ap.md §4.7).
    if (cl.reach == CleanReach.EXACT && tail == Tail.ANY_TAINT) return marks
    val at = m.path(path.copyOf(d))
    ...                                                    // the other branches, unchanged
}
```

`tail` is the any tail of the tree for the any-marks, and `Tail.EXACT`
for the `$` marks. A `$` mark never reaches PART under an EXACT cleaner
(`cleanPosAt`: DISJOINT above `p`, INSIDE at `p`), so the check acts on
any-marks only. After this change the `else` branch (`:200`) no longer
sees a MUST leaf under an EXACT cleaner; it still makes the DEMAND
survivor for MAY leaves and for MUST leaves under the other reaches.

**(b) Reference** (`ap/Reference.kt`, first statement of `concPart`).

```kotlin
// An EXACT cleaner does not apply to a MUST leaf (ap.md §4.7).
if (cl.reach == CleanReach.EXACT && c.fact.tail == Tail.ANY_TAINT) return listOf(c)
```

Update the `concPart` comment (`ap/Reference.kt:485-489`): "the `exact`
cleaner one accessor below too" goes to DEMAND only for a non-MUST tail.

### 4.4 Properties (Lean `MustExactCleaner.lean`)

The model has one base, one selected concrete mark and one leaf. It
models the reference position (`cleanPos`), the tree position
(`cleanPosAt`), the deleted native PART rows (`nativePart`: the rows of
`concPart`; the rows of `cut` are the same by code reading) and R2
(`rulePart`).

| Claim | Theorem | Statement |
| --- | --- | --- |
| C1 | `native_exact_must_demotes` | Native PART, EXACT, MUST: the result is the leaf on DEMAND, same path, tail and `E` |
| C2 | `rule_exact_must_keeps` | R2 gives the input leaf |
| C3 | `rule_outside_scope` | Outside (EXACT, MUST), R2 equals the native rows |
| C4 | `native_is_rule_with_demand_layer` | In scope, native = R2 with the layer set to DEMAND |
| C5 | `same_positions` | For every leaf, cleaner and position: R2 rows and native rows cover the same positions |
| C6 | `rule_keeps_layer` | In scope (EXACT, MUST), R2 rows have the layer of the input. Outside the scope R2 equals native (C3), and native can demote |
| C7 | `demand_input_unchanged` | On a DEMAND input, R2 = native |
| C8 | `change_only_in_scope` | The whole cleaner changes only at PART, for reach EXACT, a MUST leaf and a NORMAL input |
| C9 | `tree_form_is_reference` | For a leaf on the cleaner spine, `cleanPosAt` = `cleanPos`. This equates the positions only. With C1-C3 (stated on `nativePart`) it shows that the runtime change and the reference change select the same leaves in FULL mode |
| C10 | `no_finite_form_without_point` | Why native had to demote: for a MUST leaf whose region holds the point `p`, every finite set of leaves that misses `p` misses a strict descendant of `p` in the region (executable witness `fresh`). So "the region without `p`" has no finite leaf form, and no K can make the native survivor NORMAL |

**Differences between model and production.**

- The model has one selected mark. Production removes `gone(marks)`
  (`ap/Clean.kt:159-164`) and keeps the other marks of the leaf. R2
  returns `marks` unchanged, so it keeps all of them.
- GROUP mode: `gone` is empty, so the R2 check is never reached. The
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
  theorems that use these rows describe the deleted cleaner row. They are
  not re-proved here (§7).

### 4.5 Tests

The tests assert R2 only. The list is the prototype gate
(`acyclic-only/unit-tests/cl-1` and `jvm-cl-1`: 12 module and 2 jvm
failures); it was not re-run on `620cd5659`.

| Test | New expectation |
| --- | --- |
| `jvm-test:JIRLoweredCleanerEffectTest` "normal must ancestor follows exact below and subtree reach rows after field lowering" | EXACT at `x.f` on `x.MUST/{g}`: `{x.MUST/{f,g} N, x.f.MUST/Empty N}` (was `x.f.MUST` on D) |
| `jvm-test:JIRLoweredCleanerEffectTest` "must and may at the named field retain own E until the primitive root reach result" | EXACT on `x.f.MUST/{g}` N: the input (was the input on D). The MAY row does not change |
| `test:CleanerTest` (3 cases), `test:ReferenceOperationsTest` (2 "AP 4_7" cases), `test:FieldCleanStepTest` (1) | The EXACT/MUST PART rows only: the input leaf, same layer. The other rows of each table do not change |
| `test:OneRunAcceptanceTest` "all three primitive cleaner reaches at a real call…", index 3, reach EXACT (`:226-247`) | Facts: `{x.MUST/T N}` (was `x.MUST/T` on D). Sink layers: "at f", "below f" and "at k" all NORMAL (were all DEMAND). All targets NORMAL. `selectedDemand` empty. This is the approved trade at unit level: the cleaned point `x.f` reaches its sink on NORMAL |
| `test:DemandLinkTest` "DLINK retains provisional sink guidance and refines its normal report by run7" (`:20-60`) | The test uses the EXACT survivor of a MUST source as its DEMAND maker (`:37`). R2 removes that maker: the analysis ends at run 3 with the same report and no DEMAND link. Rewrite the fixture with a DEMAND maker that R2 does not touch, for example a STAR or MAY source under the same EXACT cleaner (Lean C3: those rows still go to DEMAND), and keep the DLINK assertions. The builder checks that the new fixture still runs 7 runs |
| `test:UniformRootCleanerTerminationTest` (2 cases), `test:DescendantCleanerTerminationTest` (1), `test:AcyclicTerminationBaselineTest.protectedGlobalCutGrowth` | The signed-off results of §4.6 |

Add one runtime-vs-reference table test: for each reach and each any
tail, an EXACT cleaner at `x.f` and at `x` on `x.MUST/E` (`E` empty and
`{g}`), both layers, run 1 and restricted, FULL mode: `ops.clean` and
`cleanRes` give the same rows. `ConcreteDesignDifferentialTest` already
compares the two on generated programs.

### 4.6 Signed-off result changes

| Fixture | Native | R2 |
| --- | --- | --- |
| `UniformRootCleanerTerminationTest` "exact-root sink cannot renew permission through the root cleaner" | 3 / `NO_DEMAND_EDGE`; C = {}, P = {} | 1 / `NO_DEMAND_EDGE`; C = {root-cleaner tree sink} |
| `UniformRootCleanerTerminationTest` "uniform source exact-root selected cleanup renews the same target through run101" | 101 / `RUN_LIMIT`; P = {root-cleaner tree sink} | 1 / `NO_DEMAND_EDGE`; C = {root-cleaner tree sink} |
| `DescendantCleanerTerminationTest` "descendant exact cleaner repeats Target demand…" | 101 / `RUN_LIMIT`; P = {observe remaining T} | 1 / `NO_DEMAND_EDGE`; C = {observe remaining T} |
| `AcyclicTerminationBaselineTest.protectedGlobalCutGrowth` | 101 / `RUN_LIMIT`; P = {observe} | 101 / `RUN_LIMIT`; C = {observe} |

In the module analyses R2 also makes one analysis end earlier with the
same report (`DemandLinkTest`). Spec §5.5 lists both.

### 4.7 Cost

Site: once per EXACT cleaner application on the any-marks of a MUST leaf
at PART. The check is two comparisons, and the rule removes work (no
survivor tree, no DEMAND row). Volume, one launch each: OWASP, R2 alone:
2,005 forward NORMAL applications, 0 forward DEMAND, 0 backward, 2,662 in
run 1. Stirling-PDF and Conductor only in the combination launches
`AO-1`: 24 forward NORMAL, 5 forward DEMAND, 12 in run 1 (Stirling-PDF);
64 forward NORMAL, 42 forward DEMAND (Conductor); 0 backward on both. The
combination changes the volume: OWASP forward NORMAL is 824 in `AO-1`
against 2,005 alone.

## 5. Order of work

1. Commit 1: R1 code (§3.3, with the path-filter change (e)) and R1 tests
   (§3.5).
2. Commit 2: R2 code (§4.3) and R2 tests (§4.5, §4.6).
3. Pre-merge checks of each commit (§6.1).
4. After both commits land: the measurement of the whole analyzer
   (§6.2), then the spec and model updates (§7).

The Lean package was first committed in `e4ec20fd9`; revision 4 adds the
two claims for admitted facts (D3', D4').

## 6. Gate

Design-guide rules 4-6 and the decisions of 24 November. Single launch
per build. A second launch only when one number does not decide. Hold
the lock
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/.projects.lock`
for every suite and project launch.

### 6.1 Pre-merge checks

| Check | Pass condition |
| --- | --- |
| Module suite (2,765 tests) | 0 failed tests after each commit, with the expectations of §3.5 and §4.5 |
| Jvm suite (473 tests) | 0 failed tests after each commit (it also covers the IFDS use of `JIRFactTypeChecker`) |
| Rule suite (585 analyses, 786 enabled cases) | The same case outcomes as `620cd5659` after each commit |
| Lean package | `check.sh` passes |

### 6.2 Measurement of the whole analyzer after landing

The owner measures the whole analyzer after both commits land, against
`620cd5659`: OWASP, Stirling-PDF and Conductor, results, time and memory.
There is no separate route list (decision of 24 November): G6's only
route change is the decided M4 removal, and R2's route changes are the
approved semantics.

| Check | Expected (prototype evidence) |
| --- | --- |
| Results | Confirmed and provisional results and SARIF code flows identical to `620cd5659`: the prototype combination `AO-C5` (which contains R1 and R2) was identical on all three projects (spec §6), and R2 alone on OWASP |
| Time | Not worse. Prototype: OWASP 128.1 s with R2 alone against 150.2-153.1 s (both with the residual diagnostic). Stirling-PDF: `620cd5659` can stall in run 11 (spec §6). Conductor times out in run 8 in every build; compare the published results at the timeout and the time to the H7 barrier |
| Memory | Largest heap after a GC not worse. Weak: peak RSS saturates near the 8 GiB heap, and Conductor is at the heap limit (spec §6) |

**Withdrawal.** Revert a commit if a pre-merge check fails, or if the
measurement after landing shows a worse time or memory beyond the spread,
or a result change that the decided semantics do not explain. A change
that they explain is kept: a finding lost below a boxed level (R1), or a
report confirmed through an EXACT cleaner on a MUST leaf (R2).

## 7. Spec and model updates after the measurement

- `ap.md` §4.7 and `interpreter.md` §5.1: state R2 and R1 (with the
  path-filter change) as the cleaner, mark-policy and path-filter
  semantics. Today they state the native rows.
- `acyclic-convergence-proposal.md` "Final classification" and §5.5, and
  `natural-termination-proposal.md` §9 item 1: group A landed, with the
  commit ids and the measurement.
- `ApSpec`: add a module that states `partX` with R2 (C1-C4 give the
  relation to the native row). Re-proving the ApSpec closure on the new
  row is a separate task; until then the ApSpec cleaner theorems describe
  the deleted row.

## 8. Answered questions

| Question | Owner answer (24 November) | Effect |
| --- | --- | --- |
| Flags or plain semantics | Plain semantics; no switch, no in-code census | §3.3, §4.3, §6 |
| Accessors after a true primitive value: `x.MAY/T` dropped at an `int` level while `x.cls(C).f.$/T` would be kept | No field and no static can follow a true primitive | §3.3 (e); A2 is a code fact; D3', D4' |
| A separate list of R2 route changes | Not needed; the whole analyzer is measured after landing | §6.2 |
| Protection on the kept MUST leaf | Keep it | §2 |

## 9. Checklist and blind spots

```text
[x] Failure class and real trace: spec §4 (cleaner survivor: 151 of 164 OWASP roots; G6: fixture M4)
[x] Ablation on the real case: R2 alone takes the OWASP residual from 711-735 to 24 (spec §5.5)
[~] Native prototype: one OWASP launch per single-rule arm; Stirling-PDF and Conductor only in AO-1; the pair R1 + R2 alone not measured (§6.2 measures it after landing)
[x] Execution site and volume: §3.6, §4.7
[x] Selected semantic scope: §2 (with the protection consequence of R2 and the path-filter change)
[x] Proof scope and model differences: §3.4, §4.4 (29 claims; propext and Quot.sound only)
[x] Withdrawal condition: §6.2
```

- The Lean models are local. They prove the operation-level properties
  (prefix closure and monotonicity in K for every admitted fact, the
  layer-only change, equal positions, equal tree and reference
  positions). They do not prove whole-analyzer soundness or termination
  with the new rows.
- A1 and A3 are code readings. A2 is enforced by §3.3 (e) and tested by
  `JIRTypeFiltersTest` and `JIRG6DropPrefixTest` (class-static accessor
  in the alphabet); the model's `Admitted` is the statement of that
  filter, not a proof about `JIRFactTypeChecker`. §3.5 adds multi-leaf
  cases for A1.
- The path-filter change also acts in the IFDS engine; only the jvm suite
  checks it there.
- R1 never acts on OWASP or the rule suite, and removed 0 marks on
  Stirling-PDF and Conductor in `AO-1`. Its effect is measured on
  synthetic fixtures only (M4, D5, D6, String chains).
- R2 project evidence: one OWASP launch alone (128.1 s, residual 24) and
  the `AO-1` / `AO-C5` combinations. Stirling-PDF and Conductor have no
  R2-only launch. R2 never fired in a backward run on the measured
  projects (0 backward applications).
- The pair R1 + R2 without the other prototype rules, and the per-analysis
  module reports of the landed code, are measured only after landing
  (§6.2); the pre-merge checks see only test outcomes.
- The protection consequence of R2 (§2) is measured only as part of the
  prototype gates; no test isolates it.
- The DLINK fixture needs a new DEMAND maker (§4.5); the proposed STAR or
  MAY source is not tried.
- The failing tests were read from the prototype gate, not re-run on
  `620cd5659`.
