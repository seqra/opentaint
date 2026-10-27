# Correlated concrete initials and general FLOW replacement: implementation proposal

Date: 26 October 2026. Validation update: 27 October 2026.
Status: **implemented; local checks, fixed-project measurements and run-1 census complete**.
Known failed gates are recorded in the validation and performance reports.
Language: ASD-STE100 Simplified Technical English. Technical names follow the source.

Contract: [correlated concrete specification](../../spec/run1-correlated-concrete-initials.md).
Proofs: [implementation proof dossier](../../spec/correlated-concrete-implementation-proofs.md).
Documentation parent: `1c927f358`. Baseline runtime core tree:
`e3ede1a36d3b04d79a23cc93285f385ecd968dbf`.
The latest measured Thingsboard result is **run-2 HARD_TIMEOUT; run-1 COMPLETE
and accepted**, at the configured 12 GiB heap. The
[performance report](../reports/bidirectional-correlated-concrete-performance-20261026.md)
records the exact runtime, commands and outcomes. The earlier
[16 GiB experiment](../reports/bidirectional-run2-16g-memory-20261026.md)
is historical evidence, not the current measurement.

The two behavior decisions are now incorporated in section 11: persist
NORMAL FLOW with nonempty E, and use semantic input alias closure to remove
identity-only alias work. The local proofs and Kotlin adapter tests pass. The
[local validation report](../reports/bidirectional-correlated-concrete-validation-20261026.md)
records the full suites and unchanged baseline failures. The required
[section 13 census](../reports/bidirectional-correlated-concrete-run1-shapes-20261026.md)
is complete. Project gates have separate outcomes: known PDF native-location
misses, OWASP raw-count mismatch, incomplete real-project run-2 and an OWASP
run-1 regression remain explicit. They are not marked successful.

## 1. Selected semantic changes

```text
Before: I(x.*/E, T) -> x.[any]/T, DEMAND
After:  I(x.*/E, T) -> x.*/E/T,    DEMAND
```

STAR preserves the original input suffix. A selected mark is an independent
property. The operation has no run-number, direction or FULL/GROUP gate.
Concrete STAR seeds remain DEMAND. Other seed rows retain their current layer.

| Selected change | Implementation consequence |
| --- | --- |
| Preserve the concrete seed's suffix | Admit STAR in typed TAINT headers; remove mark-only W2 erasure |
| Preserve suffixes through copies and summaries | Add STAR transfer/selection cases; keep actual ANY widening sites |
| Apply FLOW replacement in all runs | Enable summary owners in every run; accept valid initial E and current atoms |
| Remove the alias-class guard | Remove both scalar and packed identity restoration in summary normalization |
| Preserve dependent marked work | Apply existing flag rules in all runs and carry flags through records |
| Keep batching effective | Make existing diagonal packets carry the actual output tail |
| Persist NORMAL FLOW with nonempty initial E | Remove the old Empty-E native eligibility restriction and preserve E in views |
| Omit identity-only alias expansion | Establish positive input alias closure; do not add a runtime closure cache |

Do not introduce a source/field validation layer, GroundingSupport, a new
mark table, new alias rules, new static routing, a new request index, added
facts, IR storage changes or cache-manager changes. Do not change ND premise
sets after run-1. Keep the current queue/barrier policy.

Run-1 E remains Empty. A full overwrite kills; a disjoint field survives.
Only the existing exclusion-needing residual uses its E-free DEMAND cover.
Later strong field operations retain their current exclusions. The new
representation must not apply the run-1 cover to later runs.

## 2. Source map and ownership

All `ap/`, `store/`, `engine/` and `driver/` paths below are relative to:

```text
core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/
  org/opentaint/dataflow/bidi/
```

| Files | Change or audit |
| --- | --- |
| `ap/Conclusions.kt`, `ap/ApManager.kt`, `ap/ApOut.kt`, `ap/LeafViews.kt` | Admit and preserve concrete STAR, E and protection |
| `ap/Demand.kt`, `ap/Reference.kt` | General STAR identity start; remove unconditional concrete STAR -> ANY |
| `ap/EdgeApplication.kt`, `ap/Summary.kt`, `ap/Groups.kt`, `ap/Clean.kt` | Implement STAR transfer, selectors, deduplication and cleaner residuals |
| `ap/FlowBackedCoverage.kt` | General counterpart and two output-coverage cells |
| `store/FlowBackedSummaries.kt`, `store/DiagonalRelations.kt` | Normalize STAR/ANY; remove alias identity exceptions; retain late flags |
| `ap/DiagonalDelta.kt`, `engine/NeutralRelationBatch.kt` | Carry the output tail through packet admission and decode |
| `store/AddedFacts.kt`, `engine/CalleeSubscriptions.kt` | Audit existing exact caller-input grouping and replay; retain the complete tail/E key |
| `store/ConjunctionStore.kt`, `store/KaryJoin.kt` | Replay late annotations on existing semantic join members |
| `ap/ApOps.kt`, `engine/RunMethodLocalServices.kt` | Remove run/FULL gates from existing protection rules |
| `store/RecordStore.kt`, `engine/ProtocolContracts.kt`, `engine/SubscriptionManager.kt`, `engine/RunMethodCallServices.kt`, `ap/Reference.kt`, `ap/Summary.kt` | Transport protection through native/reversed record readers, callback contracts and application |
| `engine/RunMethodAnalyzer.kt`, `engine/RunManager.kt`, `engine/SummaryStorage.kt`, `engine/PublicationIndex.kt`, `store/RunSummaries.kt` | Enable general summary admission; keep local concrete processing |
| `engine/Run1StaticService.kt`, `engine/Run1PointResume.kt`, `engine/RunMethodCallServices.kt` | Separate independent pool values from selected correlated initials |
| `driver/HandOff.kt`, `store/DemandStore.kt` | Retain the existing direction-specific handoff; close the export case in section 11 |

Runtime scalar reconstruction uses `ap/ApManager.kt: factsOf` and
`taintTree`. Packet reconstruction uses `engine/NeutralRelationBatch.kt:
decode`, `decodePacked` and `fromDiagonal`, and `store/DiagonalRelations.kt:
decode`. Caller input accumulation uses the existing complete `GroupKey`
in `store/AddedFacts.kt`; `engine/CalleeSubscriptions.kt` owns its replay.
There is no runtime `StoreValues` owner.

`StoreValues.pack` is a test helper in
[MethodEdgeStoreTest.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/MethodEdgeStoreTest.kt).
Its scalar packing must also retain the actual tail and E. It is not a new
runtime store or a second caller-input owner.

One existing `FlowBackedSummaries` instance is one logical owner. Its FLOW,
diagonal and fallback buckets have the same scope. Raw summaries, selected
demands and publications have separate owners. Do not compare them directly.
Do not add an owner object or caller coordinate to every stored edge.

Equal owner scope does not require new cross-bucket TAINT normalization.
The selected STAR/ANY diagonal admission cells retain their stated law;
EXACT/must/cross-atom fallback rows keep their existing explicit representation.
The same-premise table in section 5.3 is not a new claim that a diagonal ANY
bucket must normalize those unsupported fallback buckets.

## 3. Typed representation

Keep the existing two TAINT leaf payloads. `exact` contains EXACT marks.
The physical `any` payload contains nonexact marks, whose tail comes from
`TaintTree.anyTail`. Keep these names to limit the patch.

```kotlin
class TaintTree(/* existing fields */) : Facts {
    init {
        check(anyTail in setOf(STAR, ANY, ANY_TAINT))
        check(exclusion == Empty ||
            (root.hasAny && anyTail in setOf(STAR, ANY_TAINT)))
        // Keep the existing nonzero-base/nonempty-root checks.
    }
}
```

This is a header extension, not a third mark payload or a new mark kind.
Exact-only roots retain their current canonical Empty-E/ANY_TAINT header;
that header does not make an exact leaf a must leaf.

```kotlin
fun taintTree(base, layer, root, exclusion, anyTail, nonSubsumable): TaintTree {
    val tail = if (root.hasAny) anyTail else ANY_TAINT
    val fields = if (!root.hasAny || tail == ANY) Empty else intern(exclusion)
    return TaintTree(base, layer, root, fields, tail,
        nonSubsumable?.intersectExactMemberships(root))
}
```

`GroupKey`, equality and hashing already include the nonexact tail and E.
Retain both. Never merge STAR, ANY and must roots under a common header.
Continue to exclude protection from ordinary fact equality; admit annotation
deltas explicitly. Runtime mark projection must map the protection payload
as well as the ordinary payload and retain the supplied field tail.

```kotlin
val ordinary = projectAtoms(f.root, mode)
val protected = f.nonSubsumable?.let { projectAtoms(it, mode) }
return taintTree(f.base, projectedLayer, ordinary, f.exclusion,
    f.anyTail, protected)
```

Do not reconstruct a DEMAND value through a constructor's default ANY tail.
Pass the tail at start, transfer, summary graft, packet decode, protection
replay and static selected-initial reconstruction.

## 4. Generic start and normalization

`ap/Demand.kt: initialFacts` keeps its current signature. Its concrete branch
uses the selected initial's tail explicitly:

```kotlin
val layer = when (i.tail) {
    STAR, ANY -> DEMAND
    EXACT, ANY_TAINT -> NORMAL
}
val payload = if (i.tail == EXACT)
    taintLeaves(markSetOf(t), EMPTY_MARKS)
else taintLeaves(EMPTY_MARKS, markSetOf(t))
return taintTree(i.base, layer, prepend(i.path, payload),
    if (i.tail == STAR || i.tail == ANY_TAINT) i.exclusion else Empty,
    anyTail = if (i.tail == EXACT) ANY_TAINT else i.tail,
    nonSubsumable = null)
```

ZERO keeps `Reach.NORMAL`; abstract STAR keeps its current FLOW start.
The mode wrapper can project atoms but does not select a different tail.
The caller still validates each run's initial grammar and field bound.

Update both scalar `startFact` and `normalize` in `ap/Reference.kt`:

```kotlin
fun normalize(f: PathFact, e: ExclusionSet, demand: Boolean): Conclusion =
    when (f.tail) {
        ANY -> Conclusion(f, Empty, demand = true)
        EXACT -> Conclusion(f, Empty, demand)
        STAR -> Conclusion(f, e, demand)
        ANY_TAINT -> {
            check(f.mark is Concrete)
            Conclusion(f, e, demand)
        }
    }
```

Keep existing well-formedness checks. This is not permission for a pool,
source or GEN producer to label independent suffixes STAR. That producer
must select its actual tail before calling `factsOf`.

## 5. AP transfer and observation

### 5.1 Concrete transfer

In `EdgeApplication.taint`, distinguish all three nonexact headers. The
ancestor-hit row still loses correlation. The matched-node STAR-target row
must no longer send every non-must mark to ANY.

```kotlin
when (c.anyTail) {
    STAR -> {
        val e = c.exclusion.union(ce.exclusion)
        if (mode.run1 && e != Empty)
            put(DEMAND, STAR, marks, Empty)
        else put(c.layer or edgeDemand, STAR, marks, e)
    }
    ANY -> put(DEMAND, ANY, marks, Empty)
    ANY_TAINT -> currentMustRow(c, ce, marks)
    else -> error("nonexact header")
}
```

This sketch is the row at `fromPath`. Keep the existing child/below-prefix
row: append the known remainder and retain the input tail/E. Do not union
a first-accessor exclusion again after a known remainder has consumed it.
The ancestor row uses ANY/D, or an EXACT target, as before.

```kotlin
val payload = when (tail) {
    EXACT -> taintLeaves(marks, EMPTY_MARKS)
    STAR, ANY, ANY_TAINT -> taintLeaves(EMPTY_MARKS, marks)
}
val fields = if (tail == STAR || tail == ANY_TAINT) exclusion else Empty
// Existing run-1 E-free policy still applies to the selected residual.
```

Keep explicit may targets, field cuts, fixed exact/must source targets,
mark gates and the original field grammar. Do not recover STAR from an ANY
input even if an equal-path FLOW summary exists.

### 5.2 Summary selection and compilation

`ap/Summary.kt: taintTails` must honor its `star` selector for STAR payloads.
It currently ignores that selector because concrete STAR did not exist.

```kotlin
fun taintTails(m: ApManager, a: TaintTree) =
    if (a.anyTail == STAR) SummaryTails<TaintLeaves>(
        exclusion = a.exclusion,
        anyExclusion = Empty,
    ) { leaf, star, _, exact ->
        m.taintLeaves(if (exact) leaf.exact else EMPTY_MARKS,
            if (star) leaf.any else EMPTY_MARKS)
    } else currentMayOrMustTails(m, a)
```

A STAR summary output uses shared STAR exclusions in its compiled edge:

```kotlin
val fromOwn = if (j.tail == ANY_TAINT) j.exclusion else Empty
val shared = (if (j.tail == ANY_TAINT) Empty else j.exclusion).union(g.exclusion)
edge(toTail = STAR, toMark = Concrete(t), sharedExclusion = shared,
    fromOwnExclusion = fromOwn, toOwnExclusion = Empty)
```

Do not put STAR E into the existing must-only `toExclusion` field.
Keep exact and must summary compilation unchanged. Graft results with their
computed tail and transported protection. Selection/restriction must retain
STAR geometry when they keep the whole correlated row; they must not treat
it as must-taint or manufacture a new binder at a demand intersection.

### 5.3 Same-premise storage and duplicate work

`TaintGroup.subtract` needs explicit tail cells. Merely allowing STAR in the
constructor is insufficient: the current `coversAny` test does not deduplicate
STAR spans and can re-emit an unchanged protection mask.

```text
Stored output tail    Offered STAR    Offered ANY     Offered must
ANY                   prefix cover    prefix cover    existing may cover
STAR                  same-path/E     no              no
must                  no              no              existing must cell
```

Keep exact-payload subtraction separate. STAR cannot remove an independent
EXACT result merely because its output path is equal. ANY retains its current
exact-prefix behavior. Do not apply the must descendant rule to STAR.

For each complete typed membership, compute actual new bits:

```kotlin
val newOrdinary = offeredOrdinary - coveredStoredOrdinary
val newProtected = offeredProtected - coveredStoredProtected
val delta = newOrdinary + newProtected
if (delta.isEmpty) return null
storeOrdinary += delta
storeProtected += newProtected
emit(delta, protected = newProtected)
```

Use the correct tail/path/E coverage for both subtractions. Protection
remains a subset of ordinary storage. A late plain-to-protected upgrade is
work. Repeating the protected value after that upgrade is not work.
This is a required termination property of the new STAR storage cell.

### 5.4 Cleaners and type filters

The STAR same-root BELOW row leaves an EXACT root:

```kotlin
if ((tail == STAR || tail.isAny) &&
    cleaner.reach == BELOW && depth == cleaner.pathSize) {
    put(inputLayer, at, EXACT, survivingSelectedMarks)
} else currentSpatialCase()
```

Keep full kills, disjoint rows and partial covers. Apply the existing later
strong exclusion row only where the current transfer defines it. GROUP
selected cleaners still request and cannot remove the group. RemoveAllMarks
can kill. No `isAny` replacement should make STAR mean universal must-taint.

Type/CM selection still tests location overlap, selected atoms and the
current layer rule. It returns the supplied STAR tail. Concrete observations
do not propagate run-1 mark requests.

## 6. General summary replacement

Generalize `flowInitialForCoverage` only to well-formed counterpart shapes:

```kotlin
val i = premise as? InitialAp ?: return null
if (i.manager !== m || i.isZero || i.mark !is Concrete) return null
if (i.mark.mark == ZERO_MARK || i.tail !in setOf(STAR, ANY)) return null
return m.initial(i.base, i.path, i.tail, i.exclusion, MarkSlot.STAR)
```

There is no FULL/GROUP or Empty-E gate. Preserve complete initial geometry.
Exact/must/ND premises retain the existing scalar residual because no legal
FLOW counterpart is selected for them.

Header eligibility is explicit:

```kotlin
fun eligible(f: FlowTree, t: TaintTree, atom: TaintMark): Boolean =
    f.base == t.base && f.tail == t.anyTail &&
    f.tail in setOf(STAR, ANY) && atom !in f.markExclusion &&
    (f.layer == NORMAL || t.layer == DEMAND) &&
    (f.tail != STAR || f.exclusion.isSubsetOf(t.exclusion))
```

The owner already establishes run/view/method/endpoint/collection scope.
Compare the diagonal output atom to the input atom. Protected memberships
are retained. No identity/alias class is passed to this function.

```kotlin
when (tail) {
    STAR -> removePlainMarksAtEqualAnnotatedPaths(taint, flow, protection, atom)
    ANY -> removePlainMarksAtCoveredPrefixes(taint, flow, protection, atom)
    else -> keepOriginal()
}
```

For STAR, never carry a `coveredAbove` Boolean down the trie. A proper prefix
is not a cover. Reuse the current ANY traversal for may-prefix coverage and
its conservative protection handling. Follow shared trie nodes with an
identity memo; do not materialize a FLOW-path by TAINT-path product.
Keep cancellation checks in all loops.

The STAR walk is an equality walk, not a call to the ANY prefix subtractor:

```kotlin
// `eligible` checked the common headers; T is the one diagonal atom.
val stack = dequeOf(Frame(taint.root, flow.root, protection, expanded = false))
val memo = IdentityTupleMap<NodeTriple, TaintNode?>()
while (stack.isNotEmpty()) {
    cancellation.checkpoint()
    val f = stack.last()
    if (memo.containsKey(f.key)) { stack.removeLast(); continue }
    if (f.flow == null) {
        memo[f.key] = f.taint
        stack.removeLast()
        continue
    }
    if (!f.expanded) {
        f.expanded = true
        for ((accessor, child) in f.taint.children)
            pushIfUnseen(child, f.flow?.child(accessor), f.flags?.child(accessor))
        continue
    }
    val coveredHere = f.flow?.leaf == FLOW_LEAF
    val protectedHere = T in f.flags?.leaf?.any.orEmpty()
    val leaf = if (coveredHere && !protectedHere)
        taintLeaves(f.taint.leaf.exact, f.taint.leaf.any - T)
    else f.taint.leaf
    memo[f.key] = rebuildOrNull(leaf, childResultsFrom(memo, f))
    stack.removeLast()
}
return memo[rootKey]?.let(facts::withRoot)
```

`NodeTriple` uses node identity in its hash/equality. `pushIfUnseen` uses
that memo and the current postorder stack. There is no inherited
`coveredAbove` or `protectedAbove` bit for STAR: another field path has a
different suffix relation. Exact payloads and their protection stay in the
scalar residual. The existing ANY walk keeps its separate prefix/protection
state. The proof packet decoder always preserves this tail distinction.

`FlowBackedSummaries.normalize` becomes one normalization call. Remove the
`run1SummaryParts` identity split there:

```kotlin
if (!replaceCovered || facts !is TaintTree || facts.anyTail !in setOf(STAR, ANY))
    return facts
val counterpart = flowInitialForCoverage(m, premise) ?: return facts
return removeFlowCovered(m, premise, facts,
    groups[counterpart]?.allFlow().orEmpty(), facts.nonSubsumable)
```

Keep `run1SummaryParts` in call handling. Also remove the packed store's
same-path identity restoration in `DiagonalRelations.compact`. These are
separate bypasses; deleting only one does not remove the selected guard.

Also remove the old STAR/Empty-E initial gate from packed compaction; it
uses the exact generalized counterpart key. Do not relax the current initial
grammar or interpret an exact/must initial as a FLOW initial.

A FLOW arrival normalizes current explicit rows and packed rows indexed by
its exact initial shape. A TAINT arrival normalizes before admission. A flag
upgrade bypasses ordinary coverage and is stored/published. No removed plain
TAINT archive or tombstone set is needed. The proposal's residual model
proves this behavior for each certified coverage membership.

## 7. Typed diagonal storage and batching

Keep geometry sharing when STAR replaces the old ANY seed. Add a tail/E tag
to the existing diagonal header rather than storing one geometry per mark.

```kotlin
data class Header(
    val initialShape: InitialAp, // Complete FLOW-shaped initial, not a new query.
    val base: AccessPathBase,
    val layer: Layer,
    val tail: Tail,              // STAR or ANY.
    val exclusion: ExclusionSet,
)
```

The scalar fallback remains for exact/must/cross-atom/mixed unsupported rows.
A packet requires a diagonal initial/output atom and exact membership masks.
It must not interpret a packed mark set as every mark on every input/output
combination. Each decoded atom recreates its own concrete initial.

The admission law in section 5.3 also applies across tail/E headers in the
same initial/base/layer scope. An existing TAINT ANY can cover a later TAINT
STAR. Equal STAR roots can merge their exclusions under the scalar law.
Checking only an identical `Header` is insufficient. Keep the same-header
fast path. For a conflicting atom in a sibling header, restore that atom's
current rows into a temporary `TaintGroup`, apply its admission law, and
encode the changed current rows back into shared masks. A packet must select
this scalar path before mutation. Retain no scalar snapshot after admission.
This is TAINT-to-TAINT deduplication; FLOW-to-TAINT replacement still requires
equal output tails. Do not compact an older STAR merely because ANY arrives
later; retain the existing scalar arrival policy.

```kotlin
fun decode(h: Header, geometry: FlowNode, atom: TaintMark, flags: FlowNode?) =
    taintTree(h.base, h.layer, scalar(geometry, atom), h.exclusion, h.tail,
        flags?.let { scalar(it, atom) })
```

Add the same fields to `DiagonalDelta`. The storage packet can carry current
FULL or GROUP atoms and legal STAR/ANY initial geometry; do not leave its
old FULL/Empty-E/STAR-only storage assertion as a semantic admission gate.
The pure-transport batching certification remains scoped separately below.
Include the fields in ordinary packet keys
and work identity. `NeutralRelationBatch.fromDiagonal` uses the delta tail
instead of hard-coded ANY. `toDiagonal` preserves the actual supported tail
and E; unsupported headers select the existing scalar fallback before mutation.

For packet admission/overlap/subtraction, dispatch on the output tail:
STAR uses equal output paths, ANY uses the current prefix cell. Do not reuse
ANY `subtractCovered` or protected-descendant expansion for STAR as if it
had independent suffixes. Keep per-mark protection and split partially
protected geometries without retaining their old scalar trees.

The run-1 FULL pure-transport certification, actor quantum and queue priority
stay unchanged. Extending the packet header is necessary to preserve that
path for new STAR work. GROUP and later runs can use the exact scalar path;
that is a representation fallback, not a semantic replacement gate.

## 8. Existing protection in every run

Remove phase/FULL checks from protection, not from requests or field policies.
Use the current runtime atom in the following operations. Project the
trigger, assigned and original atoms before comparison if a caller still
passes full rule marks to a GROUP-mode operation; an already canonical atom
keeps its current immutable representation:

```kotlin
fun ruleFlag(old: Boolean, original: TaintMark?, trigger: TaintMark,
             assigned: TaintMark): Boolean =
    old || assigned == trigger ||
        (assigned == original && assigned != trigger)
```

`trigger` is the conclusion mark of the fact which fired the rule. Do not
substitute the edge's original premise mark for it. Summary composition
keeps incoming and summary flags and protects a restored original atom.

For ordinary later ND/predicate combinations, compute the action's flag
from every accepted contributing input. Keep the exact combined premise;
do not enumerate new origin products or convert the ND result to unary.
Flag upgrades must enter standing join inputs as observable metadata, since
ordinary `Facts.equals` ignores the flag. Admit a new annotation on the
existing literal/member key. It is not a new join member: OR the current bit
and replay the already-owned semantic combinations which use that member.
`ConjunctionStore` uses the existing `KaryJoin.replace` operation to recompute
these completed tuples from standing members. It does not retain a new
Cartesian-product archive. `NdSummaryJoin` uses its existing completed list.
The equal-key check keeps the member and product sets unchanged. If a work
key carries the bit, keep that work key separate from join-member identity. Do not add compiler/source metadata to ordinary fact equality.

The selected-cleaner wrapper protects the surviving selected atom in any
run; current GROUP cleaning remains no-kill. A full all-mark kill has no
surviving marked result. Summary and field transport move existing masks
with the same operation, without repeating rule/source/sink observations.

### 8.1 Native and reversed records

Normal records already retain a `Facts` conclusion with its mask. Native
application uses that mask through the ordinary summary operation. Reversed
views currently drop it because `RecordLeafView` has only a premise/result.
Carry one invocation Boolean for the scalar native leaf when reading a view:

```kotlin
fun Record.forEachReversedAt(actual: Pattern,
    emit: (RecordLeafView, Boolean) -> Unit) {
    for (nativeLeaf in leaves(conclusion)) {
        val view = reverseRecordLeaf(direction, premise.toPattern(), nativeLeaf)
            ?: continue
        emit(view, isProtectedMembership(conclusion, nativeLeaf))
    }
}
```

`isProtectedMembership` reads the exact scalar coordinate:

```kotlin
val at = (conclusion as? TaintTree)?.nonSubsumable
    ?.nodeAtExactPath(nativeLeaf.fact.path) ?: return false
val atom = (nativeLeaf.fact.mark as Concrete).mark
return if (nativeLeaf.fact.tail == EXACT) atom in at.leaf.exact
       else atom in at.leaf.any
```

This is a mask lookup, not a mark census or a retained scalar record copy.
The callback Boolean is a required invocation argument so the compiler finds
every call site which must transport it. It is not added to semantic record
or edge equality. A flagged native delta remains a real annotation update.

Forward that Boolean through `SubscriptionManager`, `MethodCallServices`
and `applyRecordLeaf`. Protect the actual results of that scalar view; do not
change `RecordLeafView` semantic equality or add a second protection scheme.
Use the same composition-cycle check with the caller's original premise.
Keep the existing must read-view demotion and its layers/exclusions.

Concrete STAR starts are D, and ordinary transfer never promotes D. Thus
this feature does not by itself create native normal concrete-STAR inputs.
Keep normal-layer, singleton and direction checks. Remove the Empty-E
restriction for abstract STAR normal records as required by section 11.
This does not promote concrete STAR seeds or ND rows into native records.

## 9. Static value boundaries

A region/mark pool membership has no writer-to-reader suffix binder. Encode
it explicitly as independent; do not rely on generic W2 erasure:

```kotlin
fun poolValue(region: Pattern, atoms: MarkSet): Facts {
    val tail = if (region.fact.tail == EXACT) EXACT else ANY
    return pack(region.fact.copy(tail = tail), atoms, Empty, DEMAND)
}
```

After the current protocol selects its canonical concrete initial, use
`ops.startFact(initial)` for its correlated point input. An existing saved
FLOW image then controls whether the result stays STAR or widens to ANY.
Keep raw membership matching and selection before this boundary.

Apply this distinction at `Run1StaticService.facts`, `knownStaticInput`,
direct and packed point replies, `materializeScalarImages` and static call
summary input selection. Do not globally retag every pool result STAR.
Keep exact class markers exact; do not introduce concrete root/class-wide
STAR marks. ZERO activation still retains the static original in run-1;
later calls require an actual static fact.

Writer registration, computed supplies, temporary supply union, the three
request sets, static summary erasure and implicit static guidance remain.
Run producer hooks before summary normalization so coverage cannot erase a
supply or a request required by that protocol.

## 10. Store and publication pipeline

```kotlin
val summaries = RunSummaryStore(ap, flowBacked = true)
val publications = PublicationIndex(ap, ops, flowBacked = true)
// Existing run-1-only local compression and scheduling gates stay unchanged.
```

The method-local store still retains marked observation/progress memberships.
Processing concrete input is necessary for CM, source/cleaner guards and
sinks even when a FLOW summary will replace its eventual output.

```text
Selected initial -> typed seed -> local admission/queue
  -> statement/rule/call processing -> producer hooks and current field cut
  -> raw summary admission/coverage
  -> current restriction/selection -> selected/publication admission/coverage
  -> caller notification or later replay
```

FLOW arriving after a marked delta may erase a current summary residual.
Normalize detached publication batches before delivery. Do not retract old
caller work or add a historical accepted-edge archive. Callback/delta counts
can depend on arrival order; the fixed-point represented relation and late
protected memberships must satisfy the stated admission laws.

Native record persistence reads the normalized raw collection at the current
barrier. Handoff reads normalized selected demands after persistence, as now.
Do not compare raw and selected owners to manufacture cross-collection coverage.

## 11. Persistence, handoff and alias closure

### 11.1 Persist NORMAL FLOW with nonempty E

The selected behavior is: **a valid NORMAL summary with nonempty E must be
persisted**. Run-1 still emits Empty E. Later runs can carry nonempty input
and output exclusions. Do not export an extra FLOW demand instead and do
not retain the covered T demand for this case.

The current `checkNativeRecord` incorrectly requires Empty E on an abstract
STAR initial. Remove that restriction:

```kotlin
// Current abstract initial arm:
is MarkSlot.Star -> premise.tail == STAR && premise.exclusion == Empty
// New abstract initial arm:
is MarkSlot.Star -> premise.tail == STAR
```

Keep the existing other native shape, singleton, normal-layer and backward
ZERO/must checks. A concrete STAR initial starts D and cannot become N by
ordinary same-original transport; no new native concrete-STAR initial is
produced by this change. Existing normal concrete/must records retain E.

Store both exclusions on their existing owners:

```kotlin
Record(method, direction,
    premise = initial,      // Retains initial.exclusion Ei.
    conclusion = normal)    // Retains conclusion.exclusion Eo.
```

Keep `PersistentRecordStore` path indexes as candidate indexes. Full AP
matching still checks the native premise. Do not use path-index membership
as proof that an excluded suffix satisfies the record.

For a normal STAR FLOW record, its pair relation admits the same suffix
through both Ei and Eo. Generic reversal can use the existing shared
exclusion encoding:

```text
Stored:  I(a.p.*/Ei, F) -> b.q.*/Eo/(F minus X), N
View:    I(b.q.*/Empty, F) -> a.p.*/(Ei union Eo)/(F minus X)
```

The view retains both field filters in the shared result exclusion. The
AP kernel applies that shared exclusion at the appropriate STAR side.
`native_star_view_exact` proves the reversed pair equality. The existing
above-prefix query can still take a DEMAND approximation; this is not a
new record-layer policy. Keep the must-specific read view unchanged.

The driver already persists records before `HandOff.of`. Retain that order.
For every removed marked DEMAND, the covering FLOW has one of these exports:

1. FLOW is D: selected demand/handoff retains it under the ordinary rule.
2. FLOW is N: its initial cannot be ANY, whose start is D and whose ordinary
   transport remains D. The selected initial is STAR, and its NORMAL FLOW
   record is persisted with any legal E before handoff.

This covers every selected initial tail without StrongQueries or a new
request. The new `normal_covered_flow_has_record` theorem checks the layer
and initial-shape case split. Whole-premise emission/restriction remains.

Forward-to-backward retains its STAR -> ANY entry-pattern cover and atom.
Backward-to-forward keeps its current endpoint construction. The native
record retains the more precise exclusions independently of those patterns.

### 11.2 Establish input alias closure

The selected behavior is: **identity-only alias candidates are redundant**.
Do not restore the dropped subsumption guard, add an alias-effect flag on
FLOW, replay covered T summaries, or change the call classifiers.

The invariant is positive semantic coverage at the call input:

```text
If a concrete T is present at an input location p,
and q is a genuine alias for that mark location,
then q/T is already represented by the input closure.
```

“Represented” includes an admitted FLOW instance or an AP approximation. It
does not require a separate queued T leaf for every alias. “Genuine” means
an alias on the concrete witness path, not every extra may-alias candidate.
This proof permits removal of false/duplicate alias candidates.

Establish the invariant by the order of the two relevant events:

```java
// Alias definition after mark arrival.
p = source();
q = p;             // The existing copy transfer supplies q/T.
identity(p);       // No new T is created; q/T is already represented.
```

```java
// Mark arrival after alias definition.
q = p;
assignMarkT(p);    // The existing source/write alias transfer supplies q/T.
identity(p);      // Repeating that identity-only alias expansion is redundant.
```

Field/array copies and binding projections use the same argument per
concrete suffix. The existing AP copy and producer transfer cover those
suffixes even when the finite field limit produces ANY. Strong overwrites
use the current environment at the concrete witness; an old false alias is
not an obligation. A selected cleaner cannot require a newly created T;
its surviving protected dependencies retain their existing marked guide.

At method entry, actual caller inputs and source inputs use their existing
projection/producer contract. A newly introduced alias name uses its
existing copy/definition transfer. A newly introduced mark uses the current
producer alias transfer. Source/GEN occurrences remain observable before
summary normalization and are not replaced by plain diagonal FLOW.

This is a fixed-point coverage invariant. Do not add a call barrier which
waits for all alias facts, assert that every actor queue is already closed,
or build a new closure store. An alias fact may arrive later through its
existing producer. Fair processing of that producer and the original
request/demand path supplies the needed observation.

A method can also have other effects. Its identity arm is not a claim that
the whole call is side-effect-free. Actual new marks and alias definitions
are handled by their retained effect summaries and source/assignment rows.

The proof model uses a concrete alias address map, actual mark predicate
and a represented-fact cover. It proves initialization, definition/copy,
mark arrival, cleaning and finite-trace preservation. `input_alias_closure`
and `identity_alias_is_redundant` then show that a required alias conclusion
of an identity-only arm is already covered.

Kotlin correspondence checks must exercise both event orders through actual
call stages and def-site transfers, including field aliases and later marked
demands. The semantic map is proof data, not a new runtime class. The proof
uses the existing alias producer contract; if that adapter misses a genuine
alias, fix/report the baseline adapter separately instead of changing this
proposal silently.

For run-1, ANY/ANY coverage retains an alias-enabled FLOW arm, and equal-path
STAR/STAR has the same raw identity shape. The problematic later N-FLOW/D-T
identity case is covered by the closure argument above. Backward alias
stages retain their current transfer. The JVM plan's separate BIND_BACK arm
preserves the direct result; it is not used as proof of alias closure.

## 12. Implementation order and verification

Each step below is a reviewable patch. Do not enable global replacement
before its producers, protection and export paths are ready.

1. Add scalar/typed STAR invariants, start and normalization, then transport
   and selectors. Test round-trip headers and every geometry cell.
2. Add STAR same-premise deduplication, cleaner rows, flag projection and
   packet tail tags. Prove repeated protected offers produce no delta.
3. Extend protection to current atoms in all ordinary/source/ND/cleaner/call
   paths, then native/reversed records. Verify late-flag replay.
4. Generalize the two coverage traversals and exact packet compaction. Remove
   both alias identity exceptions. Keep local semantic deletion disabled.
5. Persist nonempty-E normal FLOW records and verify their native/reversed
   views. Establish the alias-closure correspondence cases, then enable summary
   owners in every run/direction. Audit both handoffs without StrongQueries.
6. Run the focused engine tests and the existing mandatory analyzer checks.
   Then use the selected fixed project commands. Do not run a performance
   ablation or change the heap limit as part of this implementation by default.
7. After implementation, complete the run-1 edge-shape investigation in
   section 13. Include its results in the implementation report.

Required tests include:

- STAR/ANY/EXACT/must starts, FULL/GROUP, E Empty/nonempty, limits 1 and higher.
- Copy, above-prefix read, below-prefix copy, explicit may target and field cut.
- Full/disjoint/partial overwrite; every cleaner reach and GROUP selected no-kill.
- Identical ordinary/protected repeats, late flag after FLOW, cross-atom cycles,
  later ND and record reversal with a protected scalar leaf.
- Scalar/packet equality, actual STAR headers, partial flags and mark masks
  without input/output Cartesian products.
- STAR equal-path/E-subset positives and negatives, ANY prefix positives,
  initial shape mismatches, exclusion gates, unsupported exact/must/ND fallbacks.
- FLOW first/last publication, source/sink observation preservation and static
  raw-value versus selected-initial resumption.
- Both handoff directions and the nonempty-E normal FLOW export case.
- Alias-stage guard-removal examples, including a later demanded alias target.

For the future project report, record each run's time, status, latest reached,
completed and accepted iteration. Record STAR/ANY/must/exact memberships,
covered/flag-blocked rows, publications, demand pairs and peak/retained bytes.
Compare fixed source revisions and commands. This proposal claims no measured
speedup, memory reduction or completion at run-2.

## 13. Post-implementation run-1 edge-shape investigation

After implementation and correctness checks, repeat the investigation used
in the [run-1 protection/coverage census](../reports/bidirectional-run1-protection-coverage-20261026.md)
and the [uncovered-edge examples](../reports/bidirectional-run1-uncovered-examples-20261026.md).
Use those reports as the investigation method, not as measurements of the
new implementation. Focus on Thingsboard, and include Conductor, Stirling-PDF
and OWASP under the selected fixed project commands and settings.

This investigation is a required post-implementation step. Passing the code
and proof checks does not complete the performance validation. The report
must give a before/after answer to each of these questions:

- Which edge shapes remain after run-1, and how many memberships have each shape?
- How many memberships were subsumed, and how many remain non-subsumed?
- How many retained memberships are blocked only by the non-subsumable flag?
- Why are the other memberships not subsumed? Show representative concrete
  edges and all relevant FLOW candidates for each major reason.
- How do these changes affect summary publications and demands for run-2?

Capture a read-only census at the completed, joined **run-1 barrier**. Record
the exact analyzer revision, core tree, configuration and coverage-checker
version. Each report must include the latest reached, completed and accepted
iteration, such as `run-2 / run-1 / run-1`. Keep a run-1 diagnostic capture
separate from the full timed run if they are different executions.

### 13.1 Stored shapes and actual replacement

Count scalar output memberships, not just packed rows or canonical AP objects.
A membership is one output path/tail/layer/atom under its method, initial
premise and collection owner. Decode shared geometry and mark masks exactly.
Report raw summaries and selected/published summaries separately; do not add
their counts. Keep method-point facts, NORMAL records and run-2 demand pairs
in separate tables when included.

Required breakdowns are:

- FLOW and concrete TAINT totals, with and without non-subsumable annotations.
- Input/output tail pairs: STAR, ANY, EXACT and must. Show the new STAR/STAR
  population and remaining STAR/ANY population explicitly.
- Initial/output bases: static, nonstatic and ZERO where applicable. State
  whether a static share refers to the initial, output or either endpoint.
- Layers, same-atom versus cross-atom relations, and output field-chain shapes.
- Largest methods, field paths and mark groups by retained memberships and
  publication/processing workload. Keep stored counts separate from work counts.

Run the implemented normalizer on temporary values to partition the retained
concrete memberships:

| Category | Definition |
| --- | --- |
| Removable now | The normalizer removes the membership with protection honored |
| Blocked only by protection | It remains normally, but removing only the protection mask on a temporary copy makes it removable |
| Not covered for other reasons | It remains even with protection cleared |

These categories must be disjoint and sum to the retained concrete total.
Flag presence is a separate count: a flagged edge can also lack any covering
FLOW relation. A geometric match alone is not proof that the flag is the
only blocker. One actual FLOW output must pass all remaining tests together.

At a completed normalized summary boundary, `Removable now` should be zero.
Investigate a nonzero result as a possible admission/compaction/checker
mismatch. Do not weaken the coverage rules to force that count to zero.
Check that every run-1 E is Empty and that erased static-static summaries
have not returned to storage.

Also measure memberships already removed by FLOW during run-1. Distinguish
covered-offer rejections from compaction of stored memberships. These are
event counts and can include repeated offers; do not label them globally
distinct subsumed edges. Do not retain a full removed-edge history to obtain
this statistic. A barrier census alone cannot recover that history.

### 13.2 Explain why retained edges are not subsumed

Break down `Not covered for other reasons` with the actual updated predicates:

- No FLOW counterpart for the complete initial geometry and owner.
- Unsupported initial or output kind, ZERO/ND premise, or cross-atom result.
- Different output bases or tail kinds.
- STAR output path inequality, including a proper-prefix mismatch.
- No annotated FLOW prefix for an ANY output; a trie branch is not an output.
- FLOW excludes the selected atom or has insufficient layer strength.
- Insufficient suffix admission by FLOW. Nonempty E in run-1 is an invariant
  failure, not a legitimate new run-1 rejection category.

Several candidate FLOW rows can fail different tests. Record a stable primary
reason for additive totals and secondary reasons where useful. Do not combine
the geometry of one FLOW output with the mark/layer headers of another.
Alias identity/effect mismatch is no longer a valid subsumption blocker; flag
it as an implementation regression if the old exception remains.

For the largest categories, provide representative real examples with:

1. The code under analysis, method and statement when relevant.
2. The complete concrete edge: initial, output, tail, E, atom, layer and flag.
3. All FLOW candidates under the matching initial in the same owner, with
   their headers and annotated output paths. Label other-initial rows separately.
4. The exact failed test, or the covering FLOW witness for a flag-only blocker.

Put large complete candidate lists in the machine-readable evidence and state
any display truncation. For tail mismatches, identify the operation which
introduced ANY: a deeper read, field cut, explicit may target or binder loss.
Use sampled replay if needed; do not add permanent per-edge provenance.

### 13.3 Compare and report the result

Report before/after counts and shares for retained concrete memberships,
STAR/ANY shapes, actual removals, protection-only blocking and each major
rejection reason. Bind every comparison to its source and predicate version:
the earlier checker had an ANY-only cell and an alias identity exception.
Do not silently reuse its classifications for the new mechanism.

Explain whether the expected effect occurred: more same-suffix concrete STAR
outputs covered by FLOW, fewer marked summary publications and fewer run-2
T demands. Correlate the remaining shapes with retained bytes and processing
counts; a membership reduction alone does not prove a time or memory saving.

Write a report in `docs/reports/` with machine-readable counts and reproducible
diagnostic commands. Reconcile each table with that execution's ordinary
completion census. Keep diagnostic time out of the timed engine comparison.
Rank any remaining workload opportunities by measured impact and distinguish
necessary marked dependencies from avoidable propagation. Do not implement
another optimization as part of this investigation without a separate proposal.
