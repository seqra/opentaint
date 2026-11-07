# Implementation: intra-procedural STAR_OR_ANY initials

> Withdrawn on 7 November 2026. The user selected ordinary tails only and a
> return to the pre-implementation subsumption design. This document retains
> prototype history; it is not the current implementation plan. Use the
> [baseline](../../spec/subsumption-redesign-baseline-20261107.md) and
> [principal examples](../../spec/subsumption-principal-examples-20261107.md).

Date: 7 November 2026. Status: implementation under native validation; handoff repair not selected.
Language: ASD-STE100 Simplified Technical English.

Implement [intra-procedural STAR_OR_ANY](../../spec/intra-procedural-star-or-any.md).
The user selected both FLOW and concrete conversion, then selected this new
tail to preserve nested initial admission. Ordinary STAR input admission stays
unchanged. The [plain-STAR negative test](../reports/bidirectional-star-initial-nested-calls-20261107.md)
is a required regression, not a reason to relax its expected finding.

The runtime baseline is `7069fe2d7`. The new formal model and native
RED/GREEN gates precede landing of this patch. The earlier
26 + 12 local laws concern the plain-STAR prototype; they are not this feature's
complete proof. Do not claim that a green constructor/image test proves
whole-analyzer refinement.

The [portable new model](../../spec/lean/proposals/initial-emission/STAR_OR_ANY.md)
has 39 checked local laws: 29 design laws and 10 ND/certificate/capability
laws. The root checked all five portable modules. Native point freshness,
complete C5, ND adapters and loop-cursor equivalence remain separate validation
obligations. The native RED gate ran 23 tests: 17 failed at the selected cells.
Those 23 tests then passed. A later targeted gate passed 82 tests, including
27 selected marker tests and the reviewed independent AP/closure oracles.
The first full gate ran 2,602 dataflow tests with 24 failures, and 462 JVM
dataflow tests with no failures. The native finding regressions remain open.
The [handoff report](../reports/bidirectional-star-or-any-handoff-gap-20261107.md)
records the first loss at run-3. A separate deep-loop test loses its finding
at run-5. This patch must not land until the required behavior is selected
and these tests pass. No project campaign has started for this patch.

## 1. Explicit scope

Add one tail, restricted-initial minting/inheritance, marker-safe live
storage, and complete public-boundary normalization. These are semantic
changes. They affect initial identity and future admission, not only data
representation.

Keep field transfer, E updates, marks/modes, source/cleaner/sink rules, pass
protection, aliases, physical ports, loop growth/consumer families, stopping,
ND guards and report identity. Add no raw-input archive, grounding support,
request propagation, new mark token, cache manager or IR rewrite.

## 2. Representation and STAR behavior

Paths below are relative to `core/opentaint-dataflow-core/opentaint-dataflow/`.

```kotlin
enum class Tail {
    STAR, ANY, ANY_TAINT, EXACT,
    STAR_OR_ANY; // Append; retain old ordinal values.

    val isAny get() = this == ANY || this == ANY_TAINT
    val isStarLike get() = this == STAR || this == STAR_OR_ANY
    val dataKind get() = if (this == STAR_OR_ANY) STAR else this
    val storageKind get() = if (this == STAR_OR_ANY) STAR else this
}
```

Use `dataKind` only to choose geometry. Do not replace live Facts with a
plain STAR copy to test matching and then return that copy. The selected
actual must retain its marker for later C2. Exact TAINT slots remain exact;
the packet's nonexact tail does not annotate those slots.

| Files under `src/main/kotlin/org/opentaint/dataflow/bidi/` | Change |
| --- | --- |
| `ap/Facts.kt`, `Conclusions.kt`, `Reference.kt`, `Premise.kt`, `ApManager.kt`, `ApOut.kt` | Add the kind, preserve it in raw constructors/keys/leaf views, allow STAR-like E. Keep ZERO canonical. |
| `ap/AdmittedInitial.kt`, `Demand.kt` | S? starts S?: FLOW N, concrete D. Preserve unrelated support/loss rules. |
| `ap/EdgeApplication.kt`, `Clean.kt`, `Filter.kt`, `MarkCheck.kt`, `MarkGate.kt`, `Limit.kt` | Reuse STAR operations. Preserve the marker on correlated transport; keep true EXACT/MAY/MUST outputs and actual cuts. |
| `ap/Summary.kt`, `NativeReverseRead.kt`, scalar reference application | Match STAR geometry without erasing the offered actual tail. Keep current/saved/opposite role restrictions. |
| `ap/Groups.kt`, `SpatialCanonical.kt`, packed/diagonal adapters | Keep distinct live marker identity and fresh capability deltas; preserve literal H and E. |
| `store/DemandResultCoverage.kt` | Derive tail/result dimensions from the enum, with a separate reject slot; remove fixed four-tail/five-cell indexing. |

Compiled rule and field edges do not mint S?. Run-1 initial validation remains
unchanged. Do not replace every existing STAR initial with S?.

## 3. Initial emission and exact images

Refactor the scalar selection so the existing ordinary algorithm is reusable
without recursively invoking the new public selector.

```kotlin
fun emit(d: Pattern, a: Pattern): Pattern? {
    if (a.tail != STAR_OR_ANY) {
        val raw = emitOrdinary(d, a) ?: return null
        return raw.withTail(if (raw.tail == ANY) STAR_OR_ANY else raw.tail)
    }
    if (!starReachabilityAllows(a, d)) return null
    val raw = emitOrdinary(d, a.viewForGeometry(STAR))
        ?: if (d.tail == ANY) emitOrdinary(d, a.viewForMayAdmission()) else null
    return raw?.withTail(when (raw.tail) {
        STAR, ANY -> STAR_OR_ANY
        else -> raw.tail
    })
}
```

The two views are immutable query operands, not modified actual Facts.
`starReachabilityAllows` retains original E for an ancestor actual. The virtual
MAY view must not make an excluded descendant reachable. Keep current base,
mark, budget, ZERO, direction and static-anchor checks in the ordinary selector.
Reject an S? demand that bypassed public demand normalization.

`canEmitInitial` describes the raw selector's exact image. It must recognize
S? witnesses, including inherited marker outputs, and stop recognizing emitted
MAY initials. It must not accept ordinary STAR at the same ANY-demand head
just because a stored STAR key has an S? preimage.

```text
canStoreInitial(d, stored):
    reject stored STAR_OR_ANY
    test existing raw stored form with insideDemand
    if stored is STAR:
        also test the corresponding raw S? preimage with insideDemand
        retain the existing FLOW EXACT preimage case
```

Use structural image templates; do not enumerate hypothetical native initials
or require `emit(d, initial) == initial`. Add exact image tests at field-limit
boundaries, for both changed cells and both directions. Keep ordinary first-
field STAR, concrete terminal EXACT, MUST, mismatching marks and ZERO controls.

## 4. One complete public-pair normalizer

Extend the current complete FLOW-pair mechanism with generic S? erasure.
Keep the existing FLOW EXACT rule after that generic step.

```kotlin
fun normalizeSummary(ap: ApManager, rawP: PremiseKey, rawC: Facts): SummaryForm {
    val p = ap.premiseOf(rawP.members.map { member ->
        if (member.tail == STAR_OR_ANY) ap.initial(member.withTail(STAR)) else member
    }) // Existing ZERO, duplicate-member and singleton rules.
    val c = rawC.withStorageTailPreservingRootsMarksEAndH()
    return existingCompleteFlowExactNormalization(ap, p, c)
}

fun normalizeTargetP(ap: ApManager, rawP: PremiseKey): PremiseKey =
    eraseSpecialTailFromEveryMember(ap, rawP)
```

Apply it at `BlockRunState.summarizeInternal` before C5. Use the returned P
for native/prepared intersection, summary admission and Publication. Target
emission normalizes P before normal-target duplicate checks, acceptance and
publication. Both NORMAL and DEMAND have this boundary rule.

Extend `LoopConsumerObservation`'s enclosing DATA and Target branches to the
same public form. Adjacent/repeat C2 observations still use raw S? initials.
Retain scope, physical entry/exit, whole original, paired demand and H labels.

Persistent record stores, publication/storage admission, static guidance and
both demand DATA endpoints assert or establish the no-S? invariant. Demand
builders normalize before ownership/dedup. The common normalizer covers
concrete and ND values; do not stop after the current single-FLOW special case.
Do not normalize only the key inside a store which returns Facts alone.

Normal-rule contributor inputs remain scoped intra-procedural data. Preserve
their marker through existing storage/replay. A rule result still passes the
common public summary normalizer before it leaves the method/block interface.
Rule-derived source/sink seed edges retain their identity and contain no S?.

The run-2 shared static carry must use the same emitted-image contract at
C5. A stored STAR key can come from an admitted S? under a MAY carry entry.
At a one-field budget it has no requested-STAR witness. Select one existing
virtual family row; do not save actual-input history or change C2.

```kotlin
fun staticCarryForSummary(member: InitialAp, policy: RestrictedInitialPolicy): DemandPattern? {
    val stored = member.toPattern()
    val direct = staticCarry(stored) ?: return null
    if (stored.fact.tail != STAR || policy.canStoreInitial(direct.entry, stored)) return direct
    val may = direct.entry.copy(tail = ANY, E = Empty) // Query operand only.
    return if (policy.canStoreInitial(may, stored)) DemandPattern(may, may) else direct
}
```

Use this adapter only for the existing C5 carry route. C2 still builds its
row from the actual input. The existing permission check rejects a false
preimage; the stored P and candidate C keep their E and literal H. The paired
row keeps one static position and mark. The checked 13-law local adapter
model covers capped recovery and equal output restriction for Empty-E STAR
versus MAY at that position. It does not select a handoff or loop repair.

## 5. Live storage, application and loops

```text
point has ordinary STAR; S? arrives -> retain/deliver the new S? capability
point has S?; ordinary STAR arrives -> S? remains available

stored STAR summary + offered S? -> STAR geometry, live S? result
stored STAR summary + offered MAY/D -> MAY/D result
```

Start with distinct live headers/group keys. Do not add cross-header marker
subsumption. Unsupported packed cases use the existing scalar fallback before
erasing any marker or protection. Summary-only packed paths see canonical
STAR endpoints. Prove scalar/packed equality on supported paths and fallback
preservation on the rest.

Adapt `LoopRestrictionSession` only after proving its earlier-cut witness
returns the same complete labelled raw initial/layer under the new policy.
Do not merely replace the old ANY/D guard with a STAR comparison. Keep the
complete observer/trial fallback when the certificate cannot prove a skip.

## 6. Implementation sequence and tests

1. Check the new constructive model: C2/image/layers, whole-pair normalization,
   marker-preserving admission, E rejection and wrapper-chain induction.
2. Add the enum/STAR geometry support without minting it in the native emitter.
   Run meaningful RED tests for marker C2, publication and original recovery.
3. Add the C2 selector/image, generic normalizer and storage/cursor handling.
   Require those RED tests to turn GREEN without weakening observations.
4. Run the full core/JVM native gates. Review every changed old expectation
   against this spec; do not relabel an unrelated failure as a new contract.
5. Commit implementation, then build/package/freeze the actual project runtime.
   Run the four fixed project experiments and publish their post-landing report.

Required native coverage includes the original loop/getter finding, one/two
wrappers and wrappers on both getters, concrete-only guarded conversion,
empty/nonempty E, both marker/STAR arrival orders, protected literal headers,
summary application, ND/Targets, contributor replay, physical block ports,
prepared/native C5 and no marker in public storage/demand. Keep the exact-T
root-versus-descendant negative control. Report actual terminal run labels;
natural convergence and finding identity are the oracles, not fixed callback
counts or an arbitrary fixed iteration count.

## 7. Post-implementation experiments

Use the unchanged four project configurations and direct `runProjectAnalyzer`:
FULL, 16 GiB, aliases/statics on, limits `1,1,2,...`, saved IFDS/outer budgets.
Reuse the f945 reference. Package all selected runtime artifacts before the
classpath freeze. No old baseline is rerun.

Measure exact finding identities, every iteration time/frontier, reached /
complete / accepted labels, memory pressure/OOM and CPU/allocation profiles.
Take an OOM heap only on the existing MemoryManager/JVM event. Retain raw
captures until derived evidence is checked; then use an explicit owned cleanup.

Repeat the fact-shape investigation. Count live STAR/S?/MAY by mark/layer,
marker admissions, marker deltas, packed fallbacks, raw versus normalized
summary shapes, protected exclusion families and reasons relations are not
subsumed. Public summary/demand S? counts must be zero.

Trace the exact dominant facts through point storage, loop restriction, call
subscription/application, C5 and publication. Determine whether extra work is
before normalization, in repeated observations or in summary delivery. Compare
Stirling/Conductor and Thingsboard separately. A recovered small test is not
the cause of the missing License identity. The strict fixed-baseline quality
gate remains open until the measured result and its cause support closure.
