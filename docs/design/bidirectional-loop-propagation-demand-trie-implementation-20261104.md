# Loop propagation and demand tries: implementation proposal

4 November 2026. Proposal only. Do not change the analyzer as part of this
document task.

The selected specification is
[Loop propagation with demand tries](bidirectional-loop-propagation-demand-trie-proposal-20261104.md).
The reference runtime is `e558b496acf82de6ff136325d58f3d90ee5b8559`.
The [latest measurements](../reports/bidirectional-joined-state-loop-consumers-packed-guidance-performance-20261103.md)
reached Conductor **run-6**: completed run-5, accepted run-5. They reached
Stirling-PDF **run-8**: completed run-7, accepted run-7. Those are measured
results of the reference runtime, not results of this proposal.

## 1. Contract and expected effect

Reduce repeated demand work at loop boundaries. Keep the same admitted
summaries, applied results, first accepted loop cuts, Targets and findings.
There is **no selected major semantic change**.

| Part | Current implementation | Proposed implementation |
| --- | --- | --- |
| Prepared C5 | Select owner-wide output row IDs; scan the prepared entry rows; restrict the packet for each selected row | Check entries once; group equal accepted output functions; query their trie; enumerate each packet stream once |
| C2 candidates | A positional trie selects patterns; native C2 checks them | Add mark-profile payloads and ANY witnesses to shared path geometry; retain native C2 checks |
| Loop prefix search | Compute the complete raw observation, then observe each shorter budget in order | Keep that search; use a native C2 witness to prove that a range of early budgets must fail |
| Local publication delivery | Visit new rows against all standing inputs; some matches repeat for every output scalar | Select positional candidate inputs, restore their native order, then match each complete input/premise once |
| Saved views | Reverse queries can revisit irrelevant output positions and enumerate their marks | Select existing output positions before enumerating marks; preserve record/view order and native matching |
| Block boundary liveness | Check at summary emission and again after application and on output routes | Prepare allowed output routes before publication; application uses the prepared routes |

Reuse these mechanisms without a policy change:

- Saved NORMAL summaries apply before current demand admission. An empty
  current demand does not suppress saved replay.
- C2 uses `RestrictedInitialPolicy`. C5 checks complete paired rows and
  restricts NORMAL and DEMAND results before admitted storage.
- Field reads, writes, exclusions, marks, primitive tracking, protection,
  source permissions and alias policy keep their current behavior.
- Real ND application requires every arm. Unary ND information remains query
  metadata only. Run-1 still emits no real ND relation.
- Zero, Target, static write shortcuts, physical ports, the selected backward
  exceptional-Zero correction and real method boundary handlers stay intact.
- Store an instruction result after its producer statement. Keep the existing
  child completion key and fresh-delta delivery policy.

Do not add routing, trie IDs or plan ordinals to `Facts`, `InitialAp`,
`PremiseSet`, `Pattern`, `Record` or report equality/hashing. These are private
query or routing data. Do not introduce a new mark table, rule census, global
queue, demand rule or unbounded raw-result cache.

## 2. Terms and ownership

The method body is a tree. A region has the form `B = BL ; L ; AL`.
After L, the adjacent region is AL forward and BL backward. Each region can
contain another such tree. All blocks use the original method registers.

Keep the body relation `I -> O` separate from its applied result `P -> F`.
I is the child initial. P is the complete enclosing original, including every
ND member. Application must not replace P with I. FL counts concrete fields
and array elements; `FL(Zero) = 0`.

| State | Owner / lifetime | Organization and purpose |
| --- | --- | --- |
| Incoming paired demand | `DemandStore`; one immutable run snapshot | Existing paired rows, ports, controls and run-2 static completion remain authoritative |
| Entry demand trie | Each immutable method/scope demand index | Shared paths; terminal pattern IDs by required mark; C2 candidates and ANY witnesses |
| Output plan | Exact demand view, policy, actual exit, normalized whole original | Accepted output functions and their trie; no rejected tickets retained |
| Plan/C2 cache | Existing `LoopQueryScratch`; one owner work quantum | Keep the current 32-plan and 32-admission bounds; clear in `finally` |
| Current summaries | Existing block stores and publication indexes | Only C5-admitted, live rows and their fresh deltas |
| Standing inputs | Existing `LocalInputDirectory` | One cumulative value per exact link/group; add positional candidate postings |
| Saved views | Immutable record snapshot plus owner-local view adapter | Existing record identity; selected positions and oriented output routes |
| Prepared routes | Method runtime, direction, layout, scope, exit and output base | Share allowed route IDs or an allowed-target mask; no copied fact history |
| Restriction session | One scalar query | Raw observation, optional labelled-key set, trie cursors and trial buckets; release on return |
| Completion store | Existing parent block | Existing `(parent entry, child, completion exit, whole P, result group)` key |

Do not add `LocalLink` to the completion key. Different offers that produce
the same completion must still collapse. Keep the link in the delivery
context, where it already belongs.

## 3. Source changes

Paths in this table are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.
New type and method names below are proposed APIs, not claims that the
reference runtime already has them.

| File | Change |
| --- | --- |
| `store/DemandStore.kt` | Build entry trie; prepare accepted output programs; retain native controls/static fallback |
| `store/FrozenDemandTrie.kt` — new | Immutable shared geometry, mark payloads, ordered candidates and precision cursors |
| `store/PreparedOutputPrograms.kt` — new | Accepted-program grouping, output trie and bounded selection buckets |
| `store/PreparedLocalDataPlan.kt` | Keep the existing capability; add optional precision access; implement program plans |
| `ap/Demand.kt` | Factor the unchanged native selection/packing helpers for scalar/program batching |
| `ap/DemandScalarStreams.kt` — new | Protected-first enumeration and native program finalization |
| `engine/LoopQueryScratch.kt` | Keep bounded cache ownership; add work counters, not standing query history |
| `engine/LoopRestrictionSession.kt` — new | Bind complete observation context and produce a certified first budget |
| `engine/LoopOutputRestriction.kt` | Accept an optional certificate provider; retain native ascending search fallback |
| `engine/BlockBoundaryDemandView.kt` | Delegate DATA precision to the physical view; preserve Zero/Target adaptations |
| `engine/MethodBlockRuntime.kt` | Use the session and prepared C5 path; prepare routes; retain native actual routing and observers |
| `engine/BlockRuntimeBinding.kt` | Expose owner-local prepared restriction and exit-routing capabilities |
| `engine/BlockRunState.kt` | Use prepared C5 where supported; check live routes before summary storage/publication |
| `engine/BlockSummaryLinks.kt`, `engine/JoinedLocalInputs.kt` | Index publication/input candidates; reuse matches; carry route metadata outside AP keys |
| `store/RecordStore.kt` | Add positional read-view capability; preserve direct/reverse modes and record identities |

No IR, generated loop function, real-call suffix, Spring, rule-provider or
field-transfer change is required.

## 4. One propagation algorithm

This is the complete control sequence. Helper implementations follow it.
**CALL** reuses the function-call/AP policy. **LOCAL** adapts that policy to
shared registers and method-owned block links. **LOOP** is loop-specific.
The callbacks below run under the existing method work reservation.

| Mechanism | Relation to function calls |
| --- | --- |
| Saved → demand → current order; C2/C5 policies; AP composition | **CALL:** reuse the same policy and native operations |
| Real ND AND, protection, marks, layers and Target meaning | **CALL:** reuse the same semantics; keep the complete witness |
| Parent/child link, join owner, work queue and completion point | **LOCAL:** same delivery principle under one method owner and exact block ports |
| Shared registers; saved MUST/reverse views | **LOCAL:** no argument/return binding or call alias/action suffix; commit local pending demotion |
| Pre-publication liveness and prepared destinations | **LOCAL:** block boundary adaptation; no repeated applied-output liveness test |
| Decomposition, repeat/leave and growing-summary gate | **LOOP:** retain the existing loop-specific control and restriction policy |
| Trie witness and certified prefix range | **LOOP:** new lookup acceleration for that unchanged gate |
| Output-program trie and stream batching | New general C2/C5 query work; usable with **CALL** policy, not a new loop semantic rule |

```text
ON_INPUT(link, wholeP, offered):
    # CALL order; LOCAL saved views, ports and bindings.
    for view in savedViews.candidates(link.child, offered):
        APPLY(link, wholeP, offered, view, saved=true)
    replaySavedTargetsNormally(link, wholeP, offered)

    if not run1:
        initials = C2(link.child, offered)
        if initials.empty: return
    fresh = standingInputs.merge(link, wholeP, offered)
    if fresh exists:
        for candidate in currentPublications.candidates(link, wholeP, fresh):
            enqueue APPLY(link, wholeP, fresh, candidate, saved=false)
    if run1: emitRun1InitialsNormally(link, wholeP, offered)
    else: startNewInitialsNormally(link.child, initials)

ON_BODY_EXIT(scope, exit, I, rawO):
    # LOCAL: actual instruction and boundary-rule processing has finished.
    routes = preparedExits.getOrPrepare(scope, exit, rawO.base)
    if routes.isDeadData: return
    for row in C5(scope, exit, I, rawO):
        delta = bodySummaries.addAdmitted(scope, exit, row.P, row.F)
        if delta exists: batchPublish(scope, exit, row.P, delta, routes)

ON_PUBLICATION(scope, exit, batch):
    for row in currentPublications.addAll(batch):
        # Snapshot selected cumulative inputs in native insertion order.
        for (input, member) in standingInputs.candidatesInNativeOrder(row):
            matched = matchNativeLocal(input.link, input.P, input.F, row,
                                       member, saved=false)
            if matched exists:
                enqueue APPLY_MATCHED(matched, row)

APPLY(link, wholeP, offered, view, saved):
    # CALL: native matching/MUST/reverse modes. LOCAL: no real-call suffix.
    matched = matchNativeLocal(link, wholeP, offered, view, saved)
    if matched exists: APPLY_MATCHED(matched, view)

APPLY_MATCHED(selected, view):
    link = selected.link
    # Real ND waits for all arms. Keep requests and Target callbacks.
    for effect in nativeApplicationOrCompleteNdJoin(selected, view):
        if effect is Request: deliverRequestNormally(effect); continue
        if effect is Target: deliverTargetNormally(effect); continue
        routes = preparedExits.forActualOutputGeometry(effect)
        if routes.isDeadData: continue        # no liveness predicate here
        for bounded in globalLimit(effect.F):
            if not ordinaryLoopExit(link.child, effect.exit) or
               run1 or bounded is Reach or not grows(effect.storedGeometry):
                retained = {bounded}
            else:
                retained = exactAnnotatedUnion(
                    RESTRICT(newSession(link, effect.P, effect.exit), scalar)
                    for scalar in annotatedScalars(bounded))
            for fact in retained:
                point = existingCompletionPoint(link, effect.exit)
                delta = completions.add(point, effect.P, fact)
                if delta exists:
                    enqueue routePreparedExit(link, effect.exit, routes,
                                              effect.P, delta)

RESTRICT(session, raw):
    baseline = OBSERVE(session, raw)
    if baseline.empty: return nothing
    if raw.fieldDepth <= 1: return raw
    first = session.certifiedFirstBudget(raw, baseline) or 1
    for budget = first .. raw.fieldDepth-1:
        cut = nativeLimit(raw, budget)         # ANY, DEMAND for a proper cut
        if OBSERVE(session, cut) == baseline: return cut
    return raw

OBSERVE(session, F):
    adjacent = labelledC2(session.adjacentViews, F)
    enclosing = empty exact annotated union
    for saved in session.savedAdjacent.candidates(F):
        for result in nativePureApplication(saved, session.P, F):
            if result is Target:
                enclosing += nativeObservedTargetFilter(result)
            else if not result.preparedRoutes.isDeadData:
                adjusted = existingObservedBoundaryMetadata(result)
                enclosing += C5(session.parent, result.exit, result.P, adjusted)
    enclosing += existingSavedTargetObservation(session, F)
    repeat = labelledC2(session.repeatViews, F)
    return completeExactSignature(adjacent, enclosing, repeat)

C5(scope, exit, wholeP, raw):
    prepared = existingSummaryFiltersAndFlowNormalization(scope, exit, wholeP, raw)
    if prepared.empty: return nothing
    (P, F) = prepared
    if run1: return {Summary(P, F, exit)}
    plan = prepareOrReuseOutputPlan(scope, exit, P)
    if plan unsupported:
        return rows(P, nativePairedIntersection(scope, exit, P, F), exit)
    buckets = empty separate protected/plain program buckets
    for stream in nativeProtectedThenOrdinaryStreams(F):
        for scalar in nativeLeaves(stream.packet):
            for program in plan.trie.candidates(scalar):
                selected = nativeRestrictConclusion(scalar, program.fullExit)
                if selected exists: buckets[program, stream] += selected
                if bucketReferenceBudgetExceeded:
                    discardBuckets()
                    return rows(P, nativePairedIntersection(scope, exit, P, F), exit)
    result = empty ExactDemandResults
    for program in firstAcceptedProgramOrder:
        packets = nativePackAndAttachProtection(buckets[program])
        for packet in packets:
            for limited in nativeLimit(packet, program.fieldBudget): result.add(limited)
    return rows(P, result.all(), exit)
```

The real implementation uses the existing queued `Delivery` records. It does
not recurse through this sequence. Keep cancellation checkpoints in trie
walks, row preparation, packet enumeration, queue drain and prefix trials.
`matched` is a native local match envelope. It carries the selected link and
whole original, immutable offered/matched value, selected premise member and
matching lane/mode. It retains the existing run-1 static-control adapter:
`suppliedStaticInput` changes a certified Zero/Reach offer into its canonical
static initial, with DEMAND layer and that selected original. Plain AP
matching of Reach against a static premise cannot replace this adapter.
API sketches below omit unchanged members and implementation bodies.
The C5 orchestration returns complete normalized rows. The normalized P must
be used for storage, publication and the enclosing observation signature too.
For example, normalizing `p.$/FLOW -> ret.$/FLOW` to
`p.*/FLOW -> ret.*/FLOW` must not leave `p.$` as the stored key. Lower-level
plan APIs can still return Facts after their owner has normalized that key.

The growth test uses the stored relation, or its native reversed view:
`FL(output) > FL(member)` for **every** premise member. Do not use the length
of an applied caller suffix. Reach, non-growing relations, run-1 and typed
negative exits keep their current gate bypass.

## 5. Frozen demand trie

### 5.1 Data layout and construction

Use one geometry tree per base. Freeze it with the incoming demand snapshot.
Keep mutable builders private to snapshot construction.

```kotlin
internal class FrozenDemandTrie<P : Any> private constructor(
    private val roots: Map<AccessPathBase, Node<P>>,
) {
    internal class Node<P : Any>(
        val children: Int2ObjectMap<Node<P>>,
        val nativeChildOrder: IntArray,
        val terminals: Map<MarkSlot, List<Terminal<P>>>,
        val anyWitness: Map<MarkSlot, Witness<P>>,
    )
    internal data class Terminal<P>(val nativeOrdinal: Int, val payload: P)
    internal data class Witness<P>(val path: IntArray, val terminal: Terminal<P>)
}
```

`MarkSlot` is the full native required mark, including its existing exclusion
data. It is not a new mark abstraction. Store one reference for a terminal in
its profile. Do not duplicate all rows under every runtime mark. For precision
witnesses, include real ANY patterns with empty field exclusion only. A parent
records a witness from its own terminal or a child; choose deterministically
by the native terminal ordinal.

Keep existing paired rows and typed controls. The C2 entry trie includes
distinct DATA entry patterns from both DATA/DATA rows and DATA/control rows.
For example, `p/T -> Target` still contributes the C2 entry `p/T`. A trie
built from DATA/DATA rows alone is incomplete.
Witness paths reference their immutable pattern data. Do not copy a complete
path array into every ancestor node.

Preserve `PathTrie` traversal order. Prefix nodes are visited from root to
query position. Subtree nodes use the reference child-map traversal and LIFO
order, recorded when the tree is frozen. At a node, merge the selected mark
payload lists by their original terminal insertion ordinal. Rebuilding child
maps with a different capacity must not silently change this order.

### 5.2 Two distinct candidate relations

```kotlin
internal enum class DemandQueryKind { INITIAL_C2, OUTPUT_C5 }

internal interface DemandCandidates<P> {
    fun visitNativeOrder(actual: Pattern, kind: DemandQueryKind, visit: (P) -> Unit)
}
```

C2 chooses mark profiles with native `markSub`. C5 chooses them with native
`marksMeet`. Do not share one predicate between these operations. In
particular, a FLOW output can meet an allowed concrete T demand at C5 even
when the same FLOW input cannot admit that concrete initial at C2.

Candidates include comparable prefix paths and the native descendant cases.
Every returned candidate still passes `emitAdmission` or
`restrictConclusionOnly`. These native operations decide tails, exclusions,
layers and mark rendering. False-positive candidates are permitted;
false-negative candidates are not. Unsupported profile cases can select all
profiles at the relevant nodes. This is a finite candidate fallback, not an
admission fallback that returns true.

### 5.3 Precision cursor

Add an optional capability to the prepared scope view. A view that cannot
provide it returns null. Keep `BlockBoundaryDemandView`'s control handling
outside this DATA capability.

```kotlin
internal interface EntryPrecisionView {
    fun precisionCursors(actual: Pattern, policy: RestrictedInitialPolicy): List<AnyDemandCursor>?
}

internal interface AnyDemandCursor {
    val label: AdmissionLabel       // exact scope and ADJACENT/REPEAT family
    fun follow(accessor: AccessorIdx): AnyDemandCursor?
    fun subtreeWitness(): Pattern?  // actual native ANY row, not a depth estimate
}
```

Only pass cursors from scope views whose existing entry guard allows the
actual base. In particular, retain the native
`keepLocalConclusion(scope.block, scope.entry, actual, count=false)` guard.
A dead local from an old demand snapshot cannot justify a prefix certificate.
Cuts preserve the base, so this guard need not be repeated for each budget.

Follow the raw path through compatible cursors. At the first missing child,
retain that field. With demands `f` and `f.g`, raw `f.g.h.k` has boundary 3:
retain `f.g.h`. With demands `f` and `f.g.z`, retain h too. Cutting at g could
admit z. Keep shorter terminals; the longer path only controls a possible
rejection certificate.

The first implementation certifies ordinary nonstatic counted fields and
array elements only. Class/static anchors, unknown policy adapters or a
missing witness yield no certificate. C2 itself still uses its native logic
for those inputs. A cursor query must not enumerate descendant terminals.

## 6. Prepared C5 output programs

### 6.1 Preserve eligibility before sharing

Keep the current preparation guard: run-3 or later, supported DATA query,
no run-2 static completion/shared carry, nonempty supported templates and no
Zero template. Retain the current 2,048 combined template/row-occurrence
limit. A rejected or oversized preparation returns null and uses native C5.

For each original member, visit native entry-prefix candidates for the exact
scope/exit. Call `EntryRestrictionTicket.prepare`, including
`policy.canStoreInitial`, for **each** occurrence. This keeps the
FLOW EXACT-to-STAR normalization preimage and native entry policy.

Only accepted tickets enter this map:

```kotlin
internal data class OutputProgramKey(
    val fullExit: Pattern,
    val fieldBudget: Int,
)

internal class OutputProgram(
    val ordinal: Int,
    val key: OutputProgramKey,
    val representative: AcceptedEntryOutput,
)

// Fixed plan context: snapshot, method/scope, direction, actual exit,
// policy/catalog, whole original and its exact normalized templates.
val programs = LinkedHashMap<OutputProgramKey, OutputProgram>()
// After each individual ticket has passed:
programs.getOrPut(key) { OutputProgram(programs.size, key, acceptedOutput) }
```

`AcceptedEntryOutput` is a private capability derived from the accepted native
ticket. Its constructor is not public. Its output function depends on the full
exit Pattern and `min(globalLimit, FL(exit)+1)`. Entry/member IDs are needed for
eligibility, not for output selection after that check. Keep one accepted
representative and diagnostic occurrence counts; do not keep rejected rows
in the executable plan.
A row with a null DATA exit creates no output program. Its native C2 entry
and any separate control handling remain available.

The plan ordinal is the first **accepted** occurrence in native
member → prefix → terminal-row order. It is not the minimum method-wide row
ID. Distinct raw rows and ND members still receive their own eligibility
checks before equal output functions collapse.

Build the output trie from these programs only. Then `emptyForBase(base)` is
an O(1) base-index check. Do not query the method-wide `byExit` index or build
the current owner-wide `HashSet<Int>` on this path.

### 6.2 Enumerate streams once; preserve native packing

Factor the body of `EntryRestrictionTicket.restrict` into internal native
helpers. Retain it as the reference adapter. The batched plan calls the same
`restrictConclusionOnly`, normalization, packing and protection code.

```kotlin
internal class ProgramBucket {
    val protectedSelections = LinkedHashSet<Conclusion>()
    val ordinarySelections = LinkedHashSet<Conclusion>()
}

// Proposed factoring of existing Demand.kt helpers, with unchanged bodies.
internal fun packRestrictedSelections(ops: ApOps, selected: Iterable<Conclusion>): List<Facts>
internal fun packProgramStreams(ops: ApOps, bucket: ProgramBucket): List<Facts>
```

Native `transportProtection` runs the **protected part first**, then the
ordinary packet. The protected part can have a different tail/header and
field exclusion from the raw packet. Enumerate each with its own header.
For each program, retain input scalar order and remove duplicate selected
conclusions with the native `LinkedHashSet` rule.

`packProgramStreams` performs the native protected pack, records those masks
with `ProtectionOutputs`, performs the ordinary pack, then attaches the exact
masks. Use the existing `packRestricted` body: normalize each conclusion,
construct Facts and merge by exact `GroupKey`. Apply the program's field cut
**after** this packing. Finally add packets in first-program order to
`ExactDemandResults`, which keeps first-key order and OR-merges protection.

Do not pack each scalar independently and do not attach one protection
boolean to the whole packet. A representative native case has exact T at the
root and MUST T at `.g`, with raw field exclusion `{f}` and only the root T
protected. Native restriction can produce a protected exact root packet with
empty E and an unprotected `.g.[any-taint]/T` packet with E=`{f}`. A single
raw-header bucket would change that result.

Use a query-local reference budget of 2,048 unique selected
`(program, stream, Conclusion)` entries. On overflow, discard the unfinished
buckets and call native C5 for the whole query **before returning a result**.
This is pure query work, so fallback repeats no rules, requests or reports.
Keep this bound separate from AP limits. It can change costs, never output.

### 6.3 Use the same plan for observation and body publication

`MethodBlockRuntime.intersect` already uses prepared plans for observation.
`BlockRunState.retainSummary` must use that same owner-local service where it
is available. Do not add a second standing plan cache.

```kotlin
internal interface BlockRuntimeBinding {
    // Existing members remain.
    fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? = null
    fun prepareExit(exit: PortId, base: AccessPathBase): PreparedExit
}

internal interface MethodRootRouting {
    // Existing members remain.
    fun intersectSummary(exit: PortId, original: PremiseKey, raw: Facts): List<Facts>? = null
}
```

Null means unsupported; an empty list is an exact empty answer. In
`retainSummary`, use the binding/root service after the existing summary
normalization. Its fallback calls `DemandStore`/`ScopeDemandView` directly,
not `retainSummary`, so there is no recursion. A method without block routing
keeps the native path. Outside a work quantum the prepared service can return
null. Normal and demand candidates both follow the same restriction path.

## 7. Certified loop prefix search

Keep `LoopOutputRestriction`'s current complete observer and its ascending
first-safe-cut contract. A trie boundary alone is not a safe final cut.

```kotlin
internal class LoopRestrictionSession<R>(
    val observe: (Facts) -> LoopObservation<R>,
    val precision: List<AnyDemandCursor>?,
    // Captures exact P, scopes, ports, snapshot and policy.
) {
    fun certifiedFirstBudget(raw: Facts, baseline: LoopObservation<R>): Int?
}
```

The certificate procedure has these checks:

1. Compute the full native raw observation first. Empty still means drop.
2. Get boundary b and a real compatible ANY witness. Require `1 < b <= depth`
   to skip trial budgets; no certificate is needed otherwise.
3. Check the supported geometry and existing admission guard. The witness
   path extends the prefix of length `b-1`. Thus every positive earlier MAY
   cut is an ancestor of that same demand.
4. Use native `emitAdmission` on the representative cut at `b-1`. Retain its
   rendered mark, tail and layer, plus exact scope/family. Do not construct an
   `InitialAp` merely to test this hypothetical command.
5. Check that labelled key against the complete raw observation's labelled
   admissions. If absent, all earlier cuts add a new key and cannot equal the
   raw observation. Begin native trials at b.
6. If the key is present, the native emission is empty, a guard is unknown or
   any prerequisite fails, begin at 1. Continue every remaining budget in
   order, with the full native observer, and return raw if none succeeds.
   If `b == depth`, the certificate rejects every proper prefix. The remaining
   trial range is empty and the algorithm returns raw after its baseline.

Build a query-local set of `(scope, family, Pattern, Layer)` from baseline
admissions only if a witness needs membership lookup. Do not intern
hypothetical initial keys. A GROUP requirement can render a submitted full T;
use native rendering rather than the witness's stored group token.

The precision forest can use a supported direct-local ANY subset. A native
C2 local emission remains in its final union even when run-2 virtual/static
lookups add other initials. Therefore an extra labelled key still proves
inequality. The **baseline** must remain the complete native observation;
do not replace it with that subset. Unsupported run-2/control adapters return
no certificate.

Do not skip trials merely because a deeper demand exists. For raw
`x.f.g.[any]/T` and demand `x.f.g.[any]/T`, cutting at f can already produce
the same admission. Its witness key is in the baseline. The certificate must
fail and the original trial at 1 must remain possible.

Keep these observer components:

- All adjacent and repeat C2 families, with exact scopes and ports.
- Saved adjacent native DATA application, complete enclosing original and
  parent paired C5 after the current pure boundary metadata/filter adapter.
- Targets produced by that DATA application, including backward Zero-to-Target,
  through their native Target acceptance path.
- Saved Target metadata through its existing separate path.
- Full marks, tails, E/mx, layers, protection masks and Target IDs.

The observer runs no rules, subscriptions, supplies, reports or mark-request
effects. Hypothetical outputs cannot enter actual storage. Reuse the existing
`LoopAdmissionBundle`; do not duplicate its adjacent/repeat queries to build
the new labelled set.

## 8. Local inputs, saved views and native application

### 8.1 Index inputs without a second input store

Extend `LocalInputDirectory` with a stable insertion handle and positional
postings. The existing link/group map keeps the sole cumulative Facts value.
Duplicate/protection upgrades update that value at the same handle. Add
postings from the fresh positional delta only.

For a current initial, select these positional candidates:

| Initial / run | Candidate positions |
| --- | --- |
| run-1 | Prefixes and extensions of the initial path |
| Later run | Prefixes; also extensions if the initial mark is FLOW or its tail is STAR |
| Zero premise | All native compatible Reach input groups, not just Zero-original links |
| run-1 static premise | Add the existing certified Zero/Reach static-control lane |

Native matching remains mandatory. Collect candidate handle/member pairs,
deduplicate those pairs, restore input insertion order and ascending member
order, and take immutable cumulative input snapshots before callbacks. The
publication order remains **row → input → member**. Do not use a call index's
different iteration order directly.

If there is no fresh published row, return without an input snapshot. When
inputs move to `JoinedLocalInputs`, move the same authoritative values and
links. Release candidate-only postings when closed publication delivery no
longer needs them; do not retain the live actor through a query callback.

### 8.2 Match once, preserve all effects

For unary current delivery, match a complete premise/input once, then pass
the same native matched value to `LocalRelationApplication.applyMatched` for
each output scalar. For saved direct records, share the record match and
native MUST-lane split where the complete input/premise is identical.
Reverse views retain `record=true` and their transient premise; do not intern
a MUST initial to reuse the forward helper.

Real ND joins keep their current key:
`(parent scope, boundary point, exit, complete premise set, output layer)`.
Keep binding/protection upgrades, prior conclusions and complete original
union. A join callback can emit a prior conclusion with a different base from
the row that woke it. Choose prepared routes from **that emitted geometry**,
not from the triggering row.

Sharing matching does not share or suppress actual output callbacks. Retain
mark requests, Target emission, pending MUST demotion and work wakes.

### 8.3 Select saved output positions before mark enumeration

Add an optional positional query to the existing record read view. It yields
`(Record, output position handle)`. A handle includes its full root-to-node
path and native position ordinal. A DAG node pointer is not sufficient:
one node can occur at two different prefixes.

For reversed records, select comparable output positions first, then call the
existing reverse-leaf constructor and enumerate marks/protection at those
positions only. Preserve native first-record discovery and each record's
view order. Direct records keep their existing entry lookup. Unknown read
views use the current enumerating path. Do not build a global
mark × position index or change persisted records.

## 9. Prepare liveness and destinations before publication

### 9.1 A private routing result

```kotlin
internal sealed interface PreparedExit {
    data object DeadData : PreparedExit
    class Routes(val catalog: RouteCatalog, val allowedIds: IntArray) : PreparedExit
    class ActualStarts(val allowedTargets: InstructionMask) : PreparedExit
    class Terminal(val nativeExit: PortId) : PreparedExit
}

internal class PreparedExitDirectory {
    // Key: layout/snapshot identity, direction, scope, exit, output base.
    fun getOrPrepare(scope: BlockScope, exit: PortId, base: AccessPathBase): PreparedExit
}
```

Prepare the result before a block DATA summary enters admitted storage. Reuse
the same native endpoint exceptions and `BlockLiveLocals` masks. If no
permitted route remains, discard the dead local summary. Nonlocals and typed
terminals retain native dispatch. A missing liveness mask means keep, as it
does now; it does not mean dead.

For a shared normal loop exit J, use **all** its current directed physical
routes. Do not filter by the producer branch. A local can remain live only on
repeat; then the prepared route set contains repeat only. The selected common
exit join, including its accepted false positives, remains unchanged.

Store a route reference in a private local publication/view wrapper or look it
up by oriented exit/base. `PublicationIndex` still merges AP rows by its native
keys. After a merge, select metadata for each actual emitted geometry.

### 9.2 Empty blocks and late reached entries

An empty block with a logical entry currently routes to its **actually
admitted** `Entry.starts`. That set can grow. Do not freeze its current list
when the identity summary is first published, and do not deliver to every
possible CFG target.

Prepare allowed-target membership from the finite physical/normal interface
universe. Routing later intersects current actual starts with that prepared
membership. If a small interface universe is unavailable, prepare a bitmap
over the finite instruction IDs once per direction/output local, using the
same native `mayEnter` and endpoint overrides. A synthetic negative port is
not an empty successor set.

This keeps late actual entry discovery and makes no new seed. At application
time, membership and actual-reachability checks are routing operations;
they do not recompute boundary liveness.

### 9.3 Saved, reversed and effect-producing application

Prepare saved views for the **current orientation** before replay. Reverse
views use their reversed exit and their result base, which is the stored
premise base. Never reuse the forward conclusion's mask for that reverse
output. Prepare each enclosing block's newly formed summary independently.

Remove the boundary predicates from `onApplied` and ordinary `routeCompleted`
DATA routing. Use prepared route references there. Keep C2 entry guards and
pure enclosing-summary guards; they protect different admission points.

Preparing a dead DATA route does **not** authorize skipping a mutable AP
application that can emit a request or Target. Run that application with its
normal callbacks; its DATA sink discards using `PreparedExit.DeadData`.
Only an existing pure, effect-free capability can omit the whole application.
Thus no mark-request behavior is hidden in this liveness optimization.

Ordinary DATA AP composition, pending layer demotion, protection transport and
field limiting preserve the oriented output base. Target conversion is a
separate typed path. Verify this adapter invariant with native tests; do not
assume it for arbitrary call actions or aliases. Real calls keep their own
call suffix and alias behavior.

## 10. Lookup costs and bounds

Let h be input path length, r selected mark/context cursors, K visited entry
row occurrences, k accepted occurrences, s distinct accepted output programs,
L total scalar memberships in the native protected/ordinary streams, chi
selected scalar/program pairs, v visited subtree nodes, and d maximum trial
depth. Packing/output width is charged separately.

| Operation | Cost and limit |
| --- | --- |
| Snapshot trie construction | O(sum of inserted path lengths + terminal references + per-node witness-profile entries); no full mark × all rows product |
| Mark-profile selection | Native compatibility checks over relevant stored profiles; charge this work separately from path probes |
| Ordinary candidate walk | Expected O(h + v + payloads), plus terminal-order merge, O(c log(1+r)) for c selected terminals |
| Precision boundary | Expected O(r·h) child/witness probes; no descendant payload scan |
| Plan eligibility | Native entry-prefix traversal and K native entry checks; first-accepted grouping of k into s programs |
| C5 query | One enumeration of each native stream; trie lookup and chi native selections; O(s) program finalization plus exact packing/cut/output costs |
| Prefix search | One complete baseline; one witness emission/key lookup; d-b remaining trials after a certified boundary b, otherwise d-1 trials |
| Publication/input candidates | Positional lookup, candidate handle/member set and native-order restoration; exact matching only on selected pairs |
| Prepared liveness | Once per oriented scope/exit/output base; routing later uses prepared membership |

Do not claim that the trie removes broad ANY scans. Comparable broad inputs
can select many descendants. Do not claim a universal twofold speedup. The
target workload reduction is fewer full packet walks per C5 row, fewer
irrelevant input/row matches and fewer complete observations of prefixes
that are provably rejected.

Keep the existing 32-entry quantum plan/admission caches, the 128-result
admission-cache limit and the 2,048 plan limit. Add the query bucket bound in
section 6. Oversized or unsupported work uses the native pure path; never
truncate its answers. Query data must not escape through saved views,
completion rows or joined-state binders.

## 11. Proofs and model-to-code obligations

Follow [proof-guide.md](../../spec/proof-guide.md). Constructive Lean models
precede runtime changes. No `sorry`, new axiom or classical choice is allowed.
Each finite existence claim supplies an executable witness.

The existing checked models are:

- [Row/scalar factorization](../../spec/lean/proposals/loop-edge-query-pipeline-20261104/README.md):
  20 theorems. Whole accepted-row selection, stable scalar regrouping and
  arbitrary native packing/cutting preserve the exact ordered output list.
- [Trie geometry and rejection certificate](../../spec/lean/proposals/demand-trie-loop-restriction-20261104/README.md):
  46 theorems. The cursor boundary matches maximum shared-prefix geometry;
  supported native C2 images have constructive witnesses; a certified rejected
  range preserves first-accepted search. It also proves why raw ANY can defeat
  an unconditional boundary cut.

The implementation-specific proof delta is
[Loop propagation implementation model](../../spec/lean/proposals/loop-propagation-demand-trie-implementation-20261104/README.md).
It passes **45 theorems** with **104 audited declarations**. It covers stable
output-program deduplication after eligibility, finite
protection-mask union, candidate-pair selection and oriented boundary-filter
placement. Read its report for exact assumptions and executable negative
examples. It is not a proof of the full Kotlin analyzer.

The end-to-end argument has these steps:

1. **Eligibility.** Each original paired occurrence passes the unchanged
   entry predicate. Grouping happens afterwards. No rejected member can grant
   another row its entry permission.
2. **Equal output functions.** For fixed context, accepted tickets with equal
   full exit Pattern/budget execute the same output operation. Repeating that
   operation adds no new ordinary key or protection bit. Keeping its first
   accepted occurrence preserves ordered exact union.
3. **Transpose.** The candidate index omits only cells with native selection
   `none`. Each program receives the same selected stream in the same order.
   Its unchanged whole-program pack, mask attachment and cut give identical
   output. No limit-distributes-over-union assumption is used.
4. **Prefix range.** Each skipped earlier cut emits the same native labelled
   command which is absent from the complete baseline. Thus none can be the
   first equal observation. All remaining candidates are checked unchanged.
5. **Application pairs.** The inverse input index selects a superset of native
   compatible pairs. Restore row/input/member order and snapshots, then use
   the same matcher and complete ND join. Sharing a match does not suppress
   its effects.
6. **Routing.** For an oriented DATA output, AP composition/cuts keep its base.
   The prepared predicate therefore selects the same actual destinations as
   the old per-route predicate. Dynamic empty-block routing intersects the
   same actual starts. Typed effects remain on their native paths.
7. **Composition.** At each owner event, admitted deltas, real effects and
   queued destinations agree. The same fresh-delta stores then preserve the
   native execution. Query counters can change; semantic results cannot.

Native obligations must be closed by differential tests before replacement:

| Obligation | Required evidence |
| --- | --- |
| Trie completeness and order | Native `PathTrie`/linear pattern oracle on all supported tails, marks and path relations |
| Program key sufficiency | Accepted native ticket result equals program result for the same full exit, budget and fixed context |
| Stream/header preservation | Native protection packing, including different protected/raw headers and partial masks |
| Witness soundness | Native `emitAdmission` agrees with the supported model; every skipped budget differs from baseline |
| Observer completeness | All current adjacent, enclosing, repeat and typed Target branches compare equal |
| Oriented base/route capability | Direct, reverse, MUST, ND and empty-block native applications keep prepared DATA routes; other effects are retained |
| Storage/lifetime | Existing completion equality, input identity, join transfer, work accounting and cache release tests |

If a counterexample reveals a missing native invariant, extend the model and
tests first. An unsupported adapter can keep the native fallback. Do not
change fields, mark layers, source permissions, ND semantics or port identity
to make the proof pass. A required major behavior change needs a separate
user decision with a code/fact trace.

## 12. Test-driven implementation plan

1. **Pin and check the reference.** Validate the three proof-package receipts
   and their input hashes. Run the new implementation-delta checker. If an
   earlier model changes, check it in a new versioned package; do not overwrite
   an archived receipt that another package pins.
   Keep the current native C2, C5, loop restriction and route predicates as
   test oracles. Freeze a small deterministic fixture set before replacing
   them. Do not run a new project baseline.
2. **Add frozen trie and oracle tests.** Build the entry view, including
   DATA-entry control rows. Test mark-profile selection and native traversal
   order. Add the optional precision capability with no skipping enabled.
3. **Add output-program preparation.** Test every entry decision and
   first-accepted program order. Replace owner-wide output IDs only on the
   existing supported prepared path. Then add stream batching and bounded
   native fallback. Compare complete ordered packets and masks.
4. **Use prepared plans at body C5.** Add owner-local delegates, with null
   capability fallback. Test NORMAL/DEMAND rows and publication deltas. Check
   that no unrestricted raw candidate enters a new retained store.
5. **Add the restriction session.** First use native start budget 1. Then
   enable witnessed range skipping and compare every final result and first
   accepted budget with the old algorithm.
6. **Prepare routes and saved views.** Move liveness preparation before
   publication; add repeat-only, late empty-entry and reversed-output tests.
   Keep typed and request effects. Remove repeated DATA boundary predicates.
7. **Index local inputs and saved positions.** Preserve native order,
   snapshots, real ND joins, MUST lanes and the joined-input ownership move.
   Compare candidate delivery streams against the current nested-loop oracle.
8. **Run required native suites.** Then build the runner and run the selected
   project campaign. Investigate each result or workload difference before
   accepting the change.

Extend existing tests in `src/test/kotlin/org/opentaint/dataflow/bidi/`:

| Suite or new test | Principal cases |
| --- | --- |
| `DemandStoreTest`, `DemandStorageDifferentialTest`, new `FrozenDemandTrieTest` | Prefix/equal/descendant/sibling positions; empty paths; C2/C5 mark differences; E/mx; control DATA entries; native order |
| `PreparedDemandPlanTest`, `DemandRelativeRestrictionTest`, `FlowBackedProtectionTest` | Rejected entries; equal exits after different entries; normalized premise used for storage; distinct budgets; protection upgrade; exact/MUST header split; pack-before-cut; oversized fallback |
| `LoopOutputRestrictionTest`, `LoopConsumerObservationTest` | Nested and sibling demands; raw ANY witness already in baseline; b=depth certificate with no trial; no witness; dead-local guard; complete signature; saved effects that require a later cut |
| `BlockSummaryLinksTest`, `LocalRelationApplicationTest` | Publication-first/input-first; fresh-only current replay; complete ND AND; per-scalar output effects; reverse record mode; pending MUST demotion |
| `BlockBoundaryLocalFilterTest`, `BlockLiveLocalsTest`, `LoopBlockEmptyReverseJoinTest` | Dead local before publication; repeat-only live local; late actual starts; negative interface; oriented saved views; real endpoint overrides |
| `LoopBlockSavedTargetWorkTest`, `LoopBlockNearestStaticTest`, `BlockBoundaryDemandViewTest` | Target from DATA versus saved Target; static shortcut; exceptional-Zero correction; no new backward NormalTarget behavior |
| `LoopQueryScratchTest`, `LoopBlockLifecycleTest`, `ScopedBlockStorageTest` | Snapshot/policy/exit separation; protection-aware cache keys; cancellation; cache clear; joined values moved once; no completion-key expansion |

Add a native request-producing saved application with dead DATA output. Its
DATA remains discarded and its request remains delivered. Add a real ND
callback that wakes on one output but emits a prior output with another base.
Both close important gaps in a route-only test suite.

Run common dataflow and JVM dataflow tests with the repository's existing
Gradle tasks, then the runner build. The reference campaign passed 2,431
common and 461 JVM tests; this is a prior receipt, not a new validation result.
Add tests that distinguish a failed certificate from an absent consumer;
do not test only the successful prefix example.

## 13. Remove replaced work

After equivalence tests pass, remove these paths from the supported prepared
implementation:

- Owner-wide output-ID collection and `HashSet<Int>` membership scans in
  `prepareLocalDataPlan.intersect`.
- Executable plan rows with null tickets and repeated output work for equal
  accepted full exit/budget programs.
- Re-enumeration of the whole protected/ordinary packet for each program.
- Repeated unary matching for each scalar of the same input/premise.
- Full standing-input scans for each new publication when the inverse
  candidate selector is available.
- Boundary liveness predicates after application and on each prepared route.

Retain native fallback implementations for controls, run-2 static completion,
unknown adapters and oversized queries. Retain the full observer and native
ascending prefix search. They are correctness paths, not unused entities.
Do not remove the ordinary positional indexes that those paths still use.

## 14. Post-implementation experiments

Use only the current selected project configurations: FULL marks, 16 GiB,
statics and aliases enabled, field limits `1,1,2,...`, and configured timeouts.
Use `runProjectAnalyzer` directly. Follow the existing OWASP workflow and the
selected Conductor, thingsboard and Stirling-PDF campaign. Do not add another
configuration to improve a result. Reuse the saved fixed quality baseline;
do not rerun it. Clean the previous campaign's snapshots/profiles before the
new campaign, as `task.md` requires.

Focus analysis on Conductor run-4/run-6 and Stirling-PDF run-6/run-7/run-8.
The reference report found observation at 94.28% of Conductor run-6 Java CPU
and 93.16% of Stirling run-7 Java CPU. Stirling run-7 had 502.471 million C5
row attempts with 99.972% entry memo hits. Conductor's prepared output-ID set
was a major allocation site. These measurements motivate work elimination;
they do not establish this proposal's speedup.

Every report must include latest **reached / completed / accepted iteration**
for every project, even after timeout or OOM. Report each iteration engine
time, transition time, NORMAL/DEMAND/Target frontier and exact finding diff.
Use accepted snapshots for quality comparisons and identify partial snapshots
separately. Explain any loss against both the fixed quality baseline and the
reference runtime; do not silently waive an existing or new gap.

Add diagnostic counters behind the existing statistics option:

| Area | Measurements |
| --- | --- |
| C2/trie | Logical/native queries, profiles inspected, path probes, subtree visits, candidates and exact admissions |
| C5 plan | K checked occurrences, k accepted occurrences, s programs, duplicate-program ratio, cache hits and unsupported/oversized reasons |
| C5 execution | Native packet/stream enumerations, selected scalar/program pairs, packing/cut counts, bucket peak and fallback count |
| Prefix gate | Raw baselines, empty drops, trial observations, successful/failed certificates by reason, budgets skipped, first accepted budget |
| Local pub/sub | Offered and fresh input groups, publication rows, candidate versus full pair counts, native match calls, actual ND combinations |
| Saved views | Positions selected/enumerated, full marks enumerated, direct/reverse/MUST lanes, typed Target callbacks |
| Routing/storage | Pre-publication liveness preparations, dead summaries, repeat-only routes, late starts, completion fresh/duplicate deltas, cache/join release |

Separate time in the mandatory baseline observation from trial-observation
time. Capture CPU and allocation profiles under sustained load and near the
configured limit. Capture and analyze a heap snapshot if the memory manager
reports OOM; do not infer retained-memory layout from allocation samples.

After the campaign, inspect fact shapes again. Count scalar memberships and
packed groups; classify field depth/tail, mark, layer, protection, block/exit,
direct/reverse relation and growing/non-growing body geometry. Distinguish:

1. Actual intra-procedural growth before a boundary, then collapse at C5.
2. Repeated observer/plan work for a small fixed packet and unchanged demand.
3. Saved reverse-view enumeration or real interprocedural joins.
4. Real output width or ND combinations that this proposal does not remove.

Compare input/summary candidate reductions with total runtime. A lower query
counter alone does not prove success. If the full baseline observer remains
dominant, report its native sub-operations and representative facts. Propose
any further algorithm separately; do not extend analyzer semantics during
this implementation.
