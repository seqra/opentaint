# Implementation proposal: canonical facts, NORMAL relations, and directional STAR matching

Date: 5 November 2026. Status: implementation and validation in progress.
The user added the transitive-coverage clarification during implementation.
Reviewed runtime: `52f32dd437d438aec4a700a02c18d94c31d58093`.

Correction, 6 November 2026: the user selected **keep STAR; repair demand
guidance**. The [producer correction](bidirectional-demand-guidance-retention-implementation-20261106.md)
keeps explicit FLOW/DEMAND/ANY positions through cold, warm and fresh-delta
admission. It revises the guidance part of the canonicalization contract below.
It keeps the scalar emitter and concrete TAINT/data normalization unchanged.
The correction is committed as `4182adae6`. It passes 3,009 native tests.
The four configured project commands have ended; quality and performance
review remain open. The shared-loop reproducer still fails its finding check.

A further selected [storage clarification](../../spec/concrete-demand-guidance-retention.md)
keeps supplied concrete TAINT/DEMAND/ANY positions and forbids all storage
subsumption of protected coordinates. It also forbids pass rules from adding
protection. Its local prototype is under review. These rules supersede the
protected-prefix/flag-fill clauses below; their older proofs keep their stated
historical scope. C2, fields and layers are unchanged. The native example
still completes run-5 with zero NORMAL reports.

This document implements the three selected changes from the
[field-path design](bidirectional-flow-antichains-and-demand-discharge-20261104.md)
and the [relation and matching audit](../reports/bidirectional-normal-star-subsumption-direction-policy-20261105.md).
It follows the [implementation guide](../../spec/impl-proposal-guide.md) and
the [proof guide](../../spec/proof-guide.md). Code is Kotlin pseudocode.
The changes apply to all iterations, in both directions.

## 1. Selected behavior and semantic boundaries

| Part | Current behavior | New behavior |
|---|---|---|
| MUST/MAY facts | Some packets and arrival orders retain covered descendants | Keep a canonical set under the selected prefix laws, including one-packet and broad-after-narrow cases |
| FLOW/DEMAND/ANY guidance correction | Prefix coverage can discard a position that selects a finer next-run initial | Retain each explicit guide position; deduplicate equal coordinates and keep existing same-point header laws |
| C2 initial emission | Redundant descendant facts can produce distinct refinement initials | Use canonical facts only; do not retain the discarded leaves as refinement history |
| MUST exclusions | Some admitted descendants and complete excluded children remain separate | Cover admitted descendants across exclusion headers; fill an excluded field only with a complete immediate MUST child |
| Reverse MUST selection | An incomparable exclusion set can reject a same-path overlap | Accept the overlap for a reversed MUST reader; keep its typed native result and layer |
| Aligned NORMAL FLOW STAR relations | Keep both `p.u.* → q.v.*` and `p.u.r.* → q.v.r.*` | Keep the actually present covering relation; remove the covered specialization from future selection |
| Strict ancestor STAR matching | Current, saved-direct and opposite records can contribute | Only an opposite-direction record can contribute through this branch |
| Measurement | Existing pre-change field-path captures | Repeat the same investigation on the landed runtime and compare exact pipelines |

The C2 change and the reverse MUST correction are explicit semantic decisions.
The STAR policy removes native matches. It is not an exact callback optimization.
Relation subsumption preserves concrete correlated pairs in its stated domain;
literal AP packets, refinement demand and diagnostic counts can change.
Loop observations also use the canonical basis. Removing a redundant MUST
descendant can remove an old reverse-reader row with a different growth
classification. Keep the growth formula; do not promise equality of the old
literal observation set or add a new growth rule to recover it.

Keep these mechanisms: instruction transfer, field read/write behavior, aliases,
mark exclusions, mark modes, source and cleaner actions, protection, typed
ZERO/Targets, complete ND joins after run-1, run-1 origin splitting, static
supply, field-limit schedule, physical entry/exit ports, loop growth test,
loop consumer families, demand-relative C5, and the empty-demand stopping rule.
Run-1 still cannot publish an ND edge. Keep caller order: saved summaries,
current demand admission, current summaries and subscription.

Do not introduce grounding support, a raw-fact archive, a rejected-input store,
dependency retraction, ancestor-reader batching, a new alias policy, a different
loop growth test, or a stop test based on stable counts. These are separate
changes. No compiler/index metadata is added to AP equality or hashing.

### 1.1 Latest measured iterations

These are existing results, not results of this proposal. Labels mean latest
reached / completed / accepted forward report.

| Project | Latest labels | Outcome |
|---|---|---|
| OWASP | run-5 / run-5 / run-5 | Complete |
| Conductor | run-6 / run-5 / run-5 | Timeout |
| Thingsboard | run-1 / none / none | Timeout during static completion |
| Stirling-PDF | run-9 / run-8 / run-7 | Timeout |

The [campaign report](../reports/bidirectional-loop-demand-trie-performance-20261104.md)
contains the full configuration and quality limits. Stirling already has three
missing fixed-baseline identities. Thingsboard has no accepted report, so its
quality is censored. Do not claim that the fixed-baseline no-FN gate already passes.

## 2. Terms and owner boundaries

```kotlin
// Not new semantic data classes. These names describe existing values.
MAY  = Tail.ANY       // [any]: an unknown field suffix
MUST = Tail.ANY_TAINT // [any-taint]: definite uniform taint below this prefix
STAR = Tail.STAR     // *: a suffix shared by the endpoints of a FLOW relation
EXACT = Tail.EXACT   // $: the exact position

// E excludes immediate fields after the known prefix.
// mx excludes concrete marks from a FLOW value.
// P is the complete premise, not only a base or a field path.
FactCell = (owner, scope, physicalPorts, P, base, layer, markKind, marks, mx)
```

A packet can contain a tree of known field paths. A leaf is one path and its
typed payload. Removing a leaf does not remove its sibling paths or marks.
Coverage must preserve the complete premise, owner, layer and interface.
Do not merge data from different call contexts or physical ports.

| Owner | Authoritative data | Derived data |
|---|---|---|
| Method/block actor | Current post-statement and admitted summary relations | Work queue and publication lookup |
| Fact group | Current canonical facts for one complete premise/base | Trie interners and traversal memo |
| Summary owner | Admitted canonical relation at one entry/exit interface | Relation-family and publication indexes |
| Run barrier | Frozen canonical NORMAL records | Direct-entry and reverse-exit record indexes |
| Demand owner | Existing selected paired demand | Entry and C5 query plans |

Keep one current authority per relation. A lookup index must not retain an
obsolete second relation. Read an actor-owned borrowed view before its next
mutation. Freeze and rebuild persistent indexes only after the existing owners
have joined. Do not add a concurrent index writer.

## 3. Canonical MUST/MAY facts

The DATA coverage laws in this section exclude real FLOW/DEMAND/ANY guide
positions after the 6 November correction. Those positions use coordinate
freshness, not proper-prefix denotational coverage. The packed TAINT adapter's
temporary FLOW geometry still uses the DATA laws. No discarded TAINT input
history is restored for C2.

### 3.1 Selected coverage and exclusion laws

Apply new spatial coverage only to compatible leaves with the same tail kind.
Keep the existing MAY-to-other-tail rules where they already apply. Do not add
MUST-to-STAR, MUST-to-EXACT, cross-layer, or cross-premise subsumption.
Every concrete mark bit is checked separately. A protected bit requires a
protected covering bit. Preserve the existing ordinary/protected mask split.

```text
MAY:
    x.u.[any] covers x.u.r.[any]

MUST, same path:
    x.u.[any-taint] / E1 covers x.u.[any-taint] / E2
    when E1 is a subset of E2

    union of x.u.[any-taint] / E1 and x.u.[any-taint] / E2
        = x.u.[any-taint] / (E1 ∩ E2)

MUST, proper descendant:
    x.u.[any-taint] / E1 covers x.u.f.r.[any-taint] / E2
    when f is not in E1
    // E2 can differ. E1 already guarantees the whole admitted f subtree.

Fill an excluded field:
    {x.u.[any-taint] / (E ∪ {f}), x.u.f.[any-taint] / {}}
        -> x.u.[any-taint] / E
    // Other headers and protected coverage must support this exact union.

Not a complete fill:
    x.u.f.g.[any-taint] / {}   // Does not cover all of x.u.f.
    x.u.f.[any-taint] / {h}   // Leaves a hole below f.
```

For example, `x.[any-taint] / {f}` covers `x.g.[any-taint] / {h}` when
`g != f`. The result remains `x.[any-taint] / {f}`. If the complete immediate
`x.f.[any-taint] / {}` also exists, the result is `x.[any-taint] / {}`.
The fill rule is an exact union, not a generalization from a deeper path.

Keep mark-exclusion compatibility in every comparison. A FLOW leaf that
excludes T cannot remove a leaf that supplies T. A fill cannot restore a
mark absent from the supporting child. An implementation can partition exact
mx headers first; do not weaken mx to enable a merge.

For concrete masks, a fill is per mark: parent `{T,U}` with E={f} plus complete
child f carrying only T gives parent T with E={} and parent U with E={f}.
Do not clear E for U. Normalize ordinary and protected masks separately, then
restore any ordinary coordinates required by native protection-mask inclusion.
Those coordinates support retained protected data; they are not raw C2 history.

Use native catalog-aware `MarkExclusions.isSubsetOf` for cross-mx coverage.
At one output coordinate with equal E, two FLOW cohorts have an exact union
with `mx = mx1.intersect(mx2)`. Keep nonshared coordinates under their original
headers. This can make their shared immediate child a complete supplier. Do
not combine different E and different mx without a separate exact-union law.
For a FLOW fill, require the child to supply every mark allowed by the parent;
equal canonical mx is the simple supported case. Keep any extra child marks.
If a child supplies only part of the parent's FLOW complement, keep that pair
unless an exact native representation is proved. Do not enumerate MarkTable,
introduce positive-only FLOW marks, or turn a FLOW conclusion into TAINT to
force a partial fill. Concrete bit masks can use the per-mark split above.

### 3.2 One canonical authority, including one arriving packet

```kotlin
fun addCanonical(offered: Facts): Change {
    val before = current
    // Include both old and offered data. Incoming-only subtraction is insufficient.
    val combined = unionWithExistingAnnotationRules(before, offered)
    val after = canonicalize(combined)
    current = intern(after)
    return Change(
        fresh = newlySupportedMemberships(before, after),
        current = current,
        changed = before != current,
    )
}

fun canonicalize(cell: CompatibleCell): CompatibleCell {
    var value = normalizeEqualPathPayloads(cell)
    // Bottom-up: a complete immediate child can fill an excluded field.
    value = fillCompleteMustChildren(value)
    // Top-down: remove descendants covered by the retained prefix/masks.
    return pruneCoveredMayAndMustDescendants(value)
}
```

The executable scalar oracle for one compatible mark/protection cell is:

```kotlin
fun mergePair(a: Region, b: Region): Region? {
    if (a.completeKey != b.completeKey) return null
    if (a.path == b.path) return a.withE(a.E intersect b.E)
    if (a.path.isProperPrefixOf(b.path)) {
        val f = b.path.firstAfter(a.path)
        if (a.tail == MAY || f !in a.E) return a
        if (b.path == a.path + f && b.E.isEmpty()) return a.withE(a.E - f)
        return null
    }
    if (b.path.isProperPrefixOf(a.path)) return mergePair(b, a)
    return null
}
// Reference only: repeatedly replace a mergeable pair by its exact union.
// Production uses packed trie passes and the FLOW/mask guards above.
```

Run the operations until their local fixed point. Filling a child can make
its parent complete, which can fill an excluded field in its own parent.
A bottom-up pass followed by top-down pruning can implement that closure.
Preserve a distinct protection mask if ordinary coverage is stronger than
protected coverage. Do not fabricate protection on the parent during a fill.

Canonicalization must work for all arrival orders:

```text
add {root, descendant} in one packet -> canonical root
add descendant; add root           -> remove old descendant
add root; add descendant           -> no fresh descendant
add root/E{f}; add child f/E{}      -> strengthen root to E{}
repeat the final packet            -> no new support
```

The final authority is canonical even if older work is already queued.
Filter detached publications on their owner against final current membership
before notification. Notifications already queued can finish once through the
existing handlers. Do not create a downstream retraction or membership-query
service. Results already delivered remain subject to ordinary post-statement
deduplication, C5 and handoff.

### 3.3 C2 uses the canonical packet

```kotlin
fun initialOffers(actual: Facts, demand: DemandView): Sequence<AdmittedInitial> {
    val canonicalActual = canonicalizePacket(actual)
    return restrictedInitialPolicy.emit(demand, canonicalActual)
}
```

Use this view for physical calls, block entry and loop observation. Do not
rerun C2 on removed leaves or retain an old packet to recover their initials.
An already owned canonical packet needs no second whole-packet normalization.

```text
Demand:  x.[any]/FLOW
Before:  {x.[any-taint]/FLOW, x.f.[any-taint]/FLOW}, NORMAL
C2 now:  {x.[any-taint]/FLOW, x.f.*/FLOW}, NORMAL
C2 new:  {x.[any-taint]/FLOW}, NORMAL
```

The user selected this change. Do not claim equality with the old literal C2
output. The proof target is the selected canonical-input policy, including its
effect on demand and observation. Do not canonicalize away a paired demand
merely because its entry field shape has a shorter prefix. Different Dp values
can set different C5 budgets and effects.

### 3.4 Reverse MUST matching

For a saved MUST conclusion, reversal creates a reader whose result already
uses the old premise with its existing loss of suffix correlation. Its
eligibility must test overlap, not require one incomparable E to include the
other.

```text
Saved NORMAL:
    P -> q.[any-taint]/FLOW, E={h}
Actual in opposite direction:
    q.*/FLOW, E={g}, g != h

Current same-path query: rejected by the exclusion subset test
New same-path query:     overlap exists; use the existing reverse DEMAND at P
```

The root q is a constructive overlap witness. For a descendant query, every
known step must pass the corresponding exclusion at that prefix. A field
excluded by the saved MUST is not restored. Apply ordinary mark, base, layer,
scope and port checks before emitting anything. No new mark is inferred from
partial overlap. Retain the native inverse result and its existing layer
computation. In the FLOW example above that result is DEMAND; this does not
add a blanket demotion of other typed record variants.

This is a selected correction to reverse MUST matching. It does not change
forward STAR identity matching or an ordinary field-read micro-edge. The
direction gate in section 5 still applies: a strict-ancestor STAR contribution
requires an opposite record.

Use an explicit transient native-read kind when constructing the inverse from
the original record. `RecordLeafView(premise,result)` alone does not retain the
old MUST provenance. Do not infer it from STAR/ANY geometry. Keep the stored
Record and AP equality unchanged; include the read kind in the transient
`seenViews` key so readers with different eligibility do not collapse.

```kotlin
class NativeRead internal constructor(
    val view: RecordLeafView,
    val kind: NativeReadKind,
    val mayUseMustOverlap: Boolean, // Trusted constructor AND old G.tail == MUST.
) {
    fun semanticKey() = NativeReadKey(view, mayUseMustOverlap)
}
data class NativeReadKey(val view: RecordLeafView, val mustOverlap: Boolean)
// seenViews semantic key is (view, mayUseMustOverlap) in its exact query scope.
// Constructor kind/source headers validate the capability; they add no unused key fields.

fun matchOpposite(actual: Facts, read: NativeRead, producer: Direction): Sequence<Facts> = sequence {
    require(producer != mode.direction)
    val old = matchSummary(actual, read.view.premise, mode,
        nativeRecordRead = true, role = OPPOSITE_RECORD)
    if (old != null) yield(old)
    if (!read.mayUseMustOverlap) return@sequence

    // Extract only STAR memberships at the exact reader prefix, with full payload.
    // Do not replace E on the whole packed packet or select its first mark/path.
    val at = selectSamePathStar(actual, read.view.premise) ?: return@sequence
    val aE = at.exclusion
    val rE = read.view.premise.exclusion
    if (aE.isSubsetOf(rE) || rE.isSubsetOf(aE)) return@sequence
    // Comparable E already had the STAR AT contribution in the old native selector.
    val projected = retainProtection(actual, at.withExclusion(aE.union(rE)))
    val added = matchSummary(projected, read.view.premise, mode,
        nativeRecordRead = true, role = OPPOSITE_RECORD)
    if (added != null) yield(added)
}

for (matched in matchOpposite(actual, nativeRead, record.direction))
    applyExistingRecordLeafPart(matched, nativeRead.view, nativeProtection, mode, out)
```

The transient E union is the overlap region. It makes the existing native
selector and application operate on that region. Keep ordinary matching as the
first lane and add at most one same-path projected lane per compatible actual
header. Both actual replay and pure loop observation use these lanes. A mixed
packet can have an old match at one mark/path and a newly admitted same-path
STAR at another; a global `if (old != null) return old` would miss it. Exact
duplicate output work still uses existing stores and merged requests. Do not use
plain Facts equality to discard a lane: it can omit a protection upgrade.

The existing FLOW-MUST constructor also accepts an old MUST premise with a STAR
conclusion. That branch alone does not give the new overlap capability. Derive
the capability in the trusted inverse constructor from the old MUST conclusion,
and include it in transient view deduplication. Keep original headers available
for validation; do not add raw Record identity to the key. Physical and
positional reverse readers must construct the same capability.
Preserve the existing `seenViews` false-to-true protection upgrade. A previously
seen plain view must not suppress a later protected contribution with the same
semantic key. Original source metadata remains transient and outside AP equality.

For a concrete native EXACT premise with a MUST conclusion, keep its existing
EXACT inverse result and composition layer. For an old MUST premise, keep its
existing ANY/DEMAND inverse. FLOW-MUST inverse results remain ANY/FLOW DEMAND.
The new projection neither changes those outputs nor converts a projected
DEMAND input into NORMAL. MAY/MUST/EXACT actuals get no new projected lane.

## 4. Aligned NORMAL relation subsumption

### 4.1 Exact selected domain

```text
S NORMAL: p.u.*   / FLOW -> q.v.*   / FLOW
L NORMAL: p.u.r.* / FLOW -> q.v.r.* / FLOW
Result: retain S; L adds no concrete correlated pair.
```

Start with singleton nonzero nonstatic FLOW STAR endpoints, empty field
exclusions at both endpoints. The covering output must admit every mark that
the covered output admits: `short.mx.isSubsetOf(long.mx)` in the same native
mark catalog. Equal canonical mx is one case of this rule.
Keep the same owner, method context, direction, scope, physical entry and exit.
Do not compare protected concrete relations, ND, Targets, ZERO or static special
relations with this new law. They keep their existing handling.

Both endpoints must contain the same extra suffix r. These rows are not covered:

```text
p.* -> q.*      versus p.f.* -> q.*    // Removes f.
p.* -> q.*      versus p.* -> q.f.*    // Adds f.
```

Empty E is an initial implementation boundary for this relation rule only.
The MUST exclusion rules in section 3 are broader. Equal nonempty endpoint E
does not prove aligned STAR coverage because the exclusions act after different
known prefixes.

### 4.2 Packed relation index and scalar reference

The coverage relation is transitive. In particular:

```text
A NORMAL: p.*   /FLOW -> q.*   /FLOW
B NORMAL: p.f.* /FLOW -> q.f.* /FLOW
C:        p.f.* /T    -> q.f.* /T, with no protection

A covers B; B covers C; therefore A covers C.
Do not require B to remain stored or to have arrived at all.
C then A -> C is removed; A then C -> C is not admitted.
```

Apply this rule in both summary backends and publication storage. Point stores
keep concrete facts for rule observations under their existing policy. At the
persistent barrier, merge current and saved rows under the same coverage law.
Current owners do not import rows from a different saved authority.

The mx subset guard is an explicit extension of the earlier equal-mx boundary.
It is required for transitivity with native same-input FLOW joins. For example,
A/mx={} covers B/mx={T}; if B covers an aligned longer row C/mx={T}, A must also
cover C. Keep the Empty field-E and interface guards. A protected C, or a C
whose mark is excluded by A, is not covered.

Production keeps packed output DAGs. It indexes concrete input prefixes. A
shorter input fixes one shared residual r. Graft r onto the shorter output DAG,
then subtract only equal output coordinates from the longer packet. Select
compatible output bases and native mx subsets. Never enumerate output paths to
allocate a row for each logical leaf. Preserve native same-input FLOW joins
before and after cross-input reduction. Only actually admitted rows supply
coverage.

The following scalar equal-mx index remains a reference for the geometry law.
Its family factoring is not the physical packed storage layout:


```kotlin
data class FamilyKey(
    val exactInterface: SummaryInterface, // owner/context/direction/scope/ports
    val inputBase: Base,
    val outputBase: Base,
    val inputCore: FieldPath,
    val outputCore: FieldPath,
    val exactMarkHeaders: MarkHeaders,
)

fun factor(row: NormalStarRow): Factored {
    val residual = longestCommonSuffix(row.input.path, row.output.path)
    return Factored(
        key = FamilyKey(row.interface, row.input.base, row.output.base,
            row.input.path.removeSuffix(residual),
            row.output.path.removeSuffix(residual), row.markHeaders),
        residual = residual,
        actualRow = row,
    )
}

fun admitAligned(row: NormalStarRow): RelationChange {
    val f = factor(row)
    val trie = families.getOrPut(f.key) { ResidualTrie() }
    if (trie.hasTerminalPrefix(f.residual)) return NoChange
    val removed = trie.removeTerminalDescendants(f.residual)
    trie.putTerminal(f.residual, row) // Store the actual admitted row.
    return RelationChange(publish = row, removed = removed)
}
```

In the scalar reference, the common-suffix factor is only an index. Never create a row at the empty
residual unless that row was actually admitted. If only L exists, retain L.
A raw S rejected by C5 cannot cover L. Apply this antichain after existing
restriction and normalization, before current summary publication.

Each current helper sees its owner's admitted current rows. If S exists only
in the saved snapshot and that run derives current L, L can still be published
in that run. The persistent barrier merges both and removes L for future
reads. Do not import saved rows into a current owner or add a cross-owner
lookup in this first implementation. Report this limit when measuring savings.

### 4.3 Preserve FLOW-backed concrete compaction

The current FLOW-backed store queries an exact FLOW premise shape when it
removes covered concrete memberships. Removing L must not hide that coverage.
Use a private transient specialization of retained S for that query:

```kotlin
interface NormalStarRelations {
    fun add(initial: InitialAp, packet: FlowTree): RelationUpdate
    fun all(): Sequence<Pair<InitialAp, FlowTree>>
    fun borrowExact(initial: InitialAp): Sequence<FlowTree>
    fun retainCurrent(initial: InitialAp, packet: FlowTree): FlowTree?
    fun visitSpecializedCovers(shape: InitialAp, emit: (FlowTree) -> Unit)
}

fun compactConcreteAt(shape: InitialAp, concrete: Facts): Facts? {
    val covers = existingUnsupportedExactFlowAt(shape)
    normalStarRelations.visitSpecializedCovers(shape) { flow -> covers.add(flow) }
    return existingRemoveFlowCovered(concrete, covers) // Existing protection rules.
}
```

For `S: p.u.* → q.v.*` and queried shape `p.u.r.*`, the transient cover is
`q.v.r.*`. This follows S's shared suffix. It is not a newly admitted relation
or an old-row archive. Never publish, persist or hand off these temporary cover
views. Revisit the offered and affected old concrete-shape groups when S removes
L. Keep protected, exact/MUST and cross-mark dependencies under existing rules.

### 4.4 Current and saved readers must use the same basis

```kotlin
fun publishCandidate(candidate: SummaryCandidate) {
    for (admitted in c5.restrict(candidate)) {
        val change = summaries.addCanonical(admitted)
        detachedBatch.add(change.fresh) // Ordinary fresh Publications only.
    }
}

fun publishDetachedBatch() {
    // SummaryStorage retains its existing lock and notification ownership.
    val (delta, recipients) = underExistingStorageLock {
        // PublicationIndex independently maintains its canonical current relation.
        // Normalize returned rows against final batch membership before notification.
        publicationIndex.addAll(detachedBatch) to subscribers.toList()
    }
    notifyExistingSubscribers(delta, recipients)
    // Already queued notifications can finish through the existing handlers.
}

fun freezeAtExistingRunBarrier(completedRun: JoinedRunResult) {
    // Precondition: existing driver lifecycle has already joined the owners.
    records.persistCompleted(direction, completedRun.publicRows, completedRun.scopedRows)
    // Root/scoped direct and reverse indexes use the same current authority.
    handoff.fromFinalAdmittedRelations()
}
```

`PersistentRecordStore.merged` alone is not the current record query result:
the existing indexes keep historical delta Record objects. Update that lifecycle.
Rebuild the relevant indexes from canonical authoritative rows at the barrier;
do not leave covered L records reachable by `byEntry`, `byExit`, or output-position
selection. Preserve all unrelated saved rows, scopes and physical port labels.

Batch public and scoped ingestion into one barrier rebuild. Stage copies of
only touched owner relations, with shared immutable DAG payloads. Build their
complete replacement indexes, then swap one `(authority, indexes)` state root
after the last cancellation check. A canceled batch must not become visible
when cancellation is later cleared. Standalone mutations use the same law:

```kotlin
interface RecordStore {
    // Default preserves existing clients. PersistentRecordStore overrides it.
    fun persistCompleted(direction, publicRows, scopedRows) {
        persist(direction, publicRows)
        persistScoped(direction, scopedRows)
    }
}

// In PersistentRecordStore:
override fun persistCompleted(direction, publicRows, scopedRows) {
    val stagedAuthority = ingestCanonicalCopy(state.authority, direction, publicRows, scopedRows)
    val next = buildAllCurrentIndexes(stagedAuthority)
    cancellation.checkpoint()
    state = State(stagedAuthority, next) // Expose one complete authority/directory.
}
```

Standalone `add`, `persist` and `persistScoped` keep immediate
standalone behavior and update the same authority. Do not rebuild all indexes
for each scalar insertion in a completed-run batch. The read-only `view()` must
explicitly reject the new mutator as well; interface delegation must not forward
it to the writable owner. Release old directory objects and backing arrays
after the root swap. A `.clear()` call alone does not prove that release.

If L was applied before S arrived, its earlier ordinary DEMAND outputs are not
retracted. S is published normally; future selection uses the new basis. This
bounded implementation does not promise that every old derived demand vanishes
in the same run. Measure residual work instead of adding a hidden provenance store.

### 4.5 Principal application example

```java
Box copy(Box p) { return p; }
// NORMAL relations possible across iterations at the same interface:
// S: p.*   /FLOW -> ret.*   /FLOW
// L: p.f.* /FLOW -> ret.f.* /FLOW
```

```text
Read these saved FORWARD records in a BACKWARD run:
    S view: ret.*   -> p.*
    L view: ret.f.* -> p.f.*

Offer: ret.*/FLOW, NORMAL
Old:   S -> p.*/FLOW NORMAL
       L -> p.f.[any]/FLOW DEMAND through strict-ancestor matching
New:   keep S only -> p.*/FLOW NORMAL
Both are opposite views, so the new direction gate alone would keep both.

Offer: ret.f.g.$/T, NORMAL
Old:   both S and L can produce p.f.g.$/T
New:   S produces the same correlated p.f.g.$/T
```

The extra old ANY result is an approximation, not a missing concrete pair.
Do not add a scalar rule saying `ret.*` covers every `ret.f.[any]`; this
proposal removes a covered producer relation instead.

## 5. Direction-limited strict-ancestor STAR matching

### 5.1 Explicit role, separate from existing record mode

```kotlin
enum class SummaryMatchRole { CURRENT, SAVED_DIRECT, OPPOSITE_RECORD }

fun roleOf(record: Record, active: Direction): SummaryMatchRole =
    if (record.direction == active) SAVED_DIRECT else OPPOSITE_RECORD

fun allowStrictAncestor(actualLeaf: Leaf, role: SummaryMatchRole): Boolean =
    actualLeaf.tail != STAR || role == OPPOSITE_RECORD

// In the spine callback only: actual.path is a proper prefix of query.path.
fun selectStrictAncestor(actualLeaf: Leaf, query: InitialAp, role: SummaryMatchRole) {
    if (allowStrictAncestor(actualLeaf, role))
        nativeInsideSelection(actualLeaf, query)
}
```

Pass the role as an invocation argument. Do not infer it from the run direction,
`restricted`, `run1`, or `record=true`. A current backward summary has CURRENT
role. Keep the existing `record` mode's other matching behavior separate.

Add a summary-only `ApOps.matchSummary` entry point. Require its role argument;
do not give it a permissive default or change every use of `satisfying` globally.
Keep `checkMark`, instruction predicates and rule guards on their old operation
path. The existing record-native flavor and the new role are separate:

```kotlin
fun matchSummary(actual, query, mode, nativeRecordRead, role): Facts? =
    satisfyingPart(actual, query, mode,
        record = nativeRecordRead,
        allowStrictAncestorStar = role == OPPOSITE_RECORD)
        ?.let { retainProtection(actual, it) }

// Only insidePart's strict spine changes:
root.walk(query.path) { depth, node ->
    spine += tails.select(node.leaf,
        star = allowStrictAncestorStar && tails.exclusion.admits(query.path[depth]),
        any = tails.anyExclusion.admits(query.path[depth]),
        exact = false)
}
// The existing AT-node and applicable/below branches stay separate.
```

Preserve the saved MUST-lane secondary query that uses `record=false`, and the
Target lane's existing native-record flavor. Their supplying role remains
explicit; do not turn every query in a saved call into `record=true`.

The selected test uses the incoming leaf's tail. It applies to FLOW and concrete
T, NORMAL and DEMAND, even when the deeper premise is EXACT. It does not filter
an entire mixed TAINT packet because one of its leaves has STAR tail.

```text
Current run: FORWARD; actual p.*/T DEMAND; reader p.f.$/T
CURRENT or saved FORWARD record: reject this strict-ancestor contribution
Saved BACKWARD record, read in reverse: retain the native contribution

Equal path p.f.* versus p.f.*: unchanged in every role
Actual below reader, p.f.g.$ versus p.f.*: unchanged
Actual MAY or MUST: unchanged by this policy
Ordinary field read x=p.f: unchanged
```

### 5.2 All callers of the matcher

| Consumer | Role |
|---|---|
| Current physical-call summary | CURRENT |
| Current local block/loop summary | CURRENT |
| Saved direct physical or local summary | SAVED_DIRECT |
| Saved reversed physical or local summary | OPPOSITE_RECORD |
| Pure loop consumer saved observation | Same saved role as actual replay |
| ND arm selection and Target AP premise | The supplying row's role |
| Current static writer binding | CURRENT; preserve exact canonical static prefix |
| Predefined summary transfer and instruction micro-edge | Existing transfer path; no summary-spine filter |

Keep operation-local correspondence in `StaticBoundaryInputRequests` unchanged.
It is not reverse record delivery. `OwnedJoinedStaticWriterBinding` does match a
current writer publication and therefore uses CURRENT. This distinction prevents
the summary policy from changing the static request-slot contract.

Filter each ND arm before the existing complete binding join. Do not treat one
surviving arm as an executable whole ND summary. Keep existing NormalTarget
NORMAL-only composition, backward exclusion and persistence deduplication.

Ordinary run-1 nonstatic originals have an empty known path. Their current
summary premises therefore have no deeper path to match through this branch.
The new all-run rule is vacuous for those rows. Test static pool adapters too:
canonical named-field inputs must not accidentally become broad root/class
STAR supplies. Do not silently add a run-1 exemption.

### 5.3 Matching and canonicalization pipeline

```kotlin
fun offerToCallOrBlock(raw: Facts, context: Context) {
    val actual = canonicalizePacket(raw)
    for (saved in savedSelection(actual, context)) {
        val role = roleOf(saved.record, context.direction)
        val matched = nativeMatch(actual, saved.view, role)
        applyExistingSavedTransfer(matched, saved, context)
    }
    val admitted = demand.emitInitials(actual, context) // Canonical packet only.
    if (admitted.isEmpty()) return
    deliverInitialsUsingExistingEntryStorage(admitted)
    applyCurrentAndSubscribe(actual, admitted, role = CURRENT)
}
```

Use this policy in the pure loop observer as well. Saved replay still precedes
current C2; removing current demand cannot by itself suppress a saved NORMAL
transfer on an already offered input.

## 6. Source changes and removal

Let B be
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.
File names below are relative to B. New helper names are proposed interfaces.

| File/group | Required implementation |
|---|---|
| `ap/Groups.kt` | Canonical spatial authority, incoming-packet and broad-after-narrow handling, excluded-child fill, ordinary/protected masks |
| `ap/Trie.kt` and relevant algebra helpers | Coverage-aware DAG traversal; retain sharing and cancellation |
| `store/DiagonalRelations.kt` | Use the same laws for supported packed cells; retain scalar fallback for unsupported MUST layouts |
| `store/FlowBackedSummaries.kt` | Canonical facts; opt-in NORMAL STAR relation families for summary/publication owners; keep existing FLOW-backed concrete coverage |
| `store/RunSummaries.kt`, method-edge stores | Route all supported additions and reads through canonical current views |
| New `store/NormalStarRelationIndex.kt` | Common-suffix family key, residual prefix trie, exact current membership |
| `engine/PublicationIndex.kt`, `SummaryStorage.kt`, `BlockSummaryLinks.kt` | Remove obsolete postings, normalize detached batches, keep future replay canonical, publish broader rows ordinarily; queued deliveries settle |
| `store/RecordStore.kt` | Canonical persistent authority; barrier rebuild of root/scoped direct and reverse postings |
| `ap/Summary.kt`, `ApOps` matcher entry points | Explicit role at strict-spine selection; separate reversed-MUST overlap selection |
| `engine/PersistedSummaryReplay.kt`, `LocalRelationApplication.kt` | Pass stored producer direction and correct reader role |
| `engine/RunMethodCallServices.kt`, `MethodBlockRuntime.kt` | Same saved-before-demand pipeline for physical and local calls |
| `engine/LoopConsumerObservation.kt`, saved selectors | Match exactly the replay policy; no independent permissive STAR path |
| ND, Target and static writer adapters | Pass supplying-row role; preserve all existing nonmatching effects |

Remove or replace the overlapping incoming-only descendant pruning paths and
obsolete record-delta postings. Remove no public semantic type merely to simplify
these indexes. Keep the existing scalar reference matcher as a test oracle for
unchanged cells; add a separate expected oracle for the selected new cells.
No IR, rule-provider, cache manager, weak cache or field-transfer rewrite belongs
to this iteration.

`MethodEdges` also uses `FlowBackedSummaries(replaceCovered=false)`. Do not enable
cross-premise aligned relation reduction for that point-store use. Spatial
canonicalization remains within its complete P; the new relation-family index
is opt-in for summary, publication and persistent authorities only.

## 7. Lookup costs and expected saved work

Let n be the number of leaf occurrences, d their maximum field depth, w the
number of retained terminals in one aligned family, and k the terminals removed.
Count mark-mask word operations separately from field-trie navigation.

```text
Spatial scalar oracle:     O(n² * d) pair search per merge round;
                          naive repeated pair reduction can take O(n³ * d)
Spatial trie plan:         bottom-up fill + top-down coverage visits
                          O(visited (node, coverage-state) pairs + mask work)
Scalar reference factoring: O(inputDepth + outputDepth)
Scalar reference lookup:    O(residualDepth)
Scalar reference insertion: O(residualDepth + k), plus posting removal
Packed current lookup:      input-prefix candidates × visited DAG pair states
Packed broader insertion:   input-descendant candidates × visited DAG pair states
                            plus removed postings and compatible-header work
Saved index rebuild:       O(canonical saved memberships and index postings)
Direction gate:            O(1) per native strict-spine contribution
```

A shared DAG node can occur under different ancestor masks. Memoize by
`(nodeId, relevant ancestor coverage state, header cell)`, not nodeId alone.
Do not claim a linear bound in distinct DAG nodes when the coverage states differ.
Do not flatten a packed field tree or marks into all scalar products in production.

Expected savings are fewer stored and selected spatial leaves, fewer aligned
relation producers and reverse output positions, fewer C2 refinement initials,
and fewer selected strict-STAR branches. Measure each separately. The diagnostic
Stirling run-5 inventory has 919/1,220 current MUST memberships spatially covered;
run-7 has 2,830/3,490. These are candidates from a separate diagnostic trajectory,
not predicted runtime reductions or all eligible rows under the final guards.

The direction gate alone does not bound path width. Existing opposite-record
seeding followed by MAY equal-length rewrites can still visit `2^L` paths at
depth L. It also retains the measured forward run-5 records read in reverse in
backward run-6. Do not promise that these three changes remove every explosion.

## 8. Proofs, counterexamples and implementation gates

The constructive proof package is
[`flow-antichains-directional-matching-20261105`](../../spec/lean/proposals/flow-antichains-directional-matching-20261105/README.md).
The package states its model-to-Kotlin boundary. It does not claim a kernel
proof of the complete driver, project convergence, resource limits or no-FN.

The implementation follow-up kernel check passes **175 theorems in five modules**,
with 249 explicit definitions/theorems audited. The only dependencies are
`propext` and `Quot.sound`; there is no Classical choice or proof placeholder.
Run `python3 spec/lean/proposals/flow-antichains-directional-matching-20261105/implementation-check.py`.
The [implementation receipt](../../spec/lean/proposals/flow-antichains-directional-matching-20261105/implementation-checks.json)
pins the checked models, proposal, checker and native source snapshot. It pins
Kotlin sources; it does not prove Kotlin correspondence.

`Implementation.lean` adds 13 laws for packed-index input-prefix eligibility,
transitive geometry and mark coverage, FLOW-backed unprotected marks without
an admitted intermediate row, protection/excluded-mark negatives, and cofinite
support union. The original four modules and their 162 laws remain unchanged.
The original `check.py` and [proposal receipt](../../spec/lean/proposals/flow-antichains-directional-matching-20261105/checks.json)
retain their reviewed `52f32dd` unchanged-runtime boundary; use that checker on
the reference tree, not on the implemented worktree.

### 8.1 Spatial coverage and exact union

Let `Cone(u,E)` contain u and every path `u.f.r` with `f ∉ E`.
A MUST leaf guarantees its supported mark at every position in this cone.
MAY prefix coverage uses the existing existential unknown-suffix meaning.

```text
Cross-E descendant:
    f ∉ E -> Cone(u.f.r,H) ⊆ Cone(u,E)
    Witness: append f.r and the descendant suffix to u.

Same-path union:
    Cone(u,E1) ∪ Cone(u,E2) = Cone(u,E1 ∩ E2)
    A child is excluded from both operands exactly when it is in both E sets.

Immediate fill, f ∈ E:
    Cone(u,E) ∪ Cone(u.f,{}) = Cone(u,E \ {f})
    The added operand is the entire missing f subtree.
```

The laws apply independently in each compatible mark/protection/header cell.
Union fills are not justified by a single covering old leaf: the proof must use
both old operands. A model that requires every new row to have one old covering
row cannot prove this fill and must be refined to region-union semantics.

The canonicalizer must preserve that union and be idempotent. Packet grouping
must not change spatial-union answers in its selected cells; this does not
require equal list order or identical byte serialization. Unsupported cells remain unchanged.
Kernel proofs establish the stated executable spatial model; packed DAG and
mark-mask correspondence remains a native adapter test obligation.

### 8.2 NORMAL correlated relations and finite concrete paths

For each concrete L pair, choose `sigma = r ++ tau`:

```text
L pair: (p.u.r.tau/T, q.v.r.tau/T)
S pair: (p.u.sigma/T, q.v.sigma/T)
```

Both pairs are identical. Reversal preserves this inclusion. Removing the same
residual from both endpoints also preserves the forward and backward growth
comparison. This proof does not apply to a fixed P with only its output changed.

`Relations.lean` proves common-suffix reconstruction, exact equivalence of the
family/residual-prefix query to aligned cover, online antichain preservation,
no invented relation, full concrete relation-union preservation, and equal
below-prefix payload application. The canonical residual row is always an
actually supplied admitted row.

`Reachability.lean` composes that result: every finite concrete path through the
NORMAL relation basis has the same intermediate positions, marks and source/sink
endpoint predicates after canonicalization. The same explicit position list is
the constructive witness. This is a relation-semantics theorem, not a theorem
about the native approximation, C2/C5, scheduling or convergence.

### 8.3 Matching policy and reverse overlap

`Matching.lean` defines executable path ancestry, explicit producer/reader roles,
ordered native-eligible filtering and complete ND binding products. It proves:

- Only native-eligible members can remain; no payload is changed by the filter.
- Opposite-role selection equals the old eligible list.
- AT, non-STAR, MAY, MUST and non-strict matches are unchanged by this gate.
- All STAR layers/mark payloads use the same policy; no run-number exemption.
- Complete ND products retain every required arm; rejection cannot create a
  partial executable binding.
- An empty run-1 query path has no strict ancestor contribution.

Native marks, exclusions and protection in this model are immutable supplied
eligibility payloads. This policy proof does not establish whole-driver finding
equivalence after removing saved-direct matches. In particular, do not assume
that every saved-direct record has an opposite-direction counterpart.

The reverse-MUST model must separately prove an explicit overlap witness and
reject excluded known descendants. Its native adapter must carry the original
MUST read kind and exclusions. Do not infer that provenance from an ANY result.
Keep the inverse's typed native output and layer rules.

### 8.4 What the existing controls establish

The [direction control evidence](../reports/data/bidirectional-star-inside-direction-controls-20261105.json)
contains eight completed finite-driver outcomes. Both pure-getter and mark-changing
programs retain their early and late findings, complete/accepted at run-7.
The mutants changed restricted runs only. Thirty-six scalar policy cells
distinguish all-STAR from FLOW-only or premise-STAR policies. Eight opposite-seeded
width controls retain the `2^L` width for L=1..8. These are finite controls,
not a universal no-FN proof or a project speed measurement.

Seven new standalone native AP overlap controls pass on the unchanged runtime.
The [portable evidence](../../spec/lean/proposals/flow-antichains-directional-matching-20261105/native-overlap-evidence.json)
includes source, output and hashes. The controls exercise three FLOW cases and
four concrete cases, both concrete actual layers and protection. The E-union
projection passes the existing selector and compiled application; concrete
EXACT inverse results retain the incoming native layer, while MUST inverse
results remain ANY/DEMAND. These are BACKWARD-mode AP controls at field limit 5,
not completed analyzer iterations or a real-project campaign. The
[adapter detail](../../spec/lean/proposals/flow-antichains-directional-matching-20261105/native-overlap-adapter.md)
records construction, positional-selection and transient deduplication APIs.
The extra FLOW MAY/MUST comparison cells do not authorize projecting those
actual tails; only same-path STAR gains the selected overlap lane.

The [C2 controls](../reports/data/bidirectional-grouped-demand-c2-controls-20261104.json)
show why the canonical-input decision changes literal initials. Keep those
controls as explicit before/new-expected cases. The old
[NORMAL relation audit](../reports/data/bidirectional-normal-star-relation-cover-audit-20261105.json)
supplies the earlier 17-law geometry result; the new package extends it with
the executable index and antichain.

### 8.5 Required native RED/GREEN tests

| Test group | Required cases |
|---|---|
| Spatial antichain | Same packet, every arrival order, broad-after-narrow, repeated add, all supported tails and layers |
| Exclusion union | Cross-E admitted descendant; equal-path E intersection; direct empty-E child fill; deeper/nonempty-E child non-fill |
| Masks/protection | Distinct full marks, mx differences, protected child under ordinary parent, partial protected fill, immutable payloads |
| Packed tries | Shared subtree under different coverage states; compare to the new scalar oracle without flattening production data |
| C2 | Selected canonical-only examples; calls, blocks and loop observer use the same packet; no raw refinement lane |
| Reverse MUST | Incomparable E overlap, same-path witness, excluded descendant rejection, changed mark rejection, exact physical ports |
| Aligned relation | Aligned S/L both arrival orders; L-only does not invent S; unaligned/shrinking/growing negatives; rejected candidate S cannot cover L |
| Publication | L then S in one detached batch suppresses stale L notification; already queued L can settle; future reads canonical; broader S delivered ordinarily |
| Persistent basis | No obsolete L in root/scoped entry, exit or output-position indexes; unrelated directions/ports preserved; index rebuild after owner join |
| Role matching | CURRENT and saved-direct denial; opposite allowance; mixed exact/STAR leaves; both layers; deeper EXACT premise; AT/below/MAY/MUST preservation |
| Complete joins | ND arms filtered before AND; Target rules/layers and persisted report IDs unchanged |
| Loop/call parity | Same saved role and native projection in physical replay, local replay and pure observer; run-1 static grammar cases |
| Driver regressions | All saved finite controls, source/cleaner survivors, reverse source→Target paths, loop-contained calls and delayed callers |

Add only tests that distinguish a wrong implementation of these laws. Use the
native AP constructors; reject impossible injected facts as invalid tests.
The selected matcher narrowing needs real-driver and project quality gates
in addition to the local proof. Do not label the missing whole-engine theorem
as already proved by a filter-subset lemma.

## 9. Implementation sequence

1. Freeze reference source and compile the constructive models. Add failing
   native controls for packet order, excluded-child fill, reverse MUST overlap,
   aligned relations and every role/tail cell. Use existing tests and harnesses.
2. Implement spatial canonicalization and canonical-input C2. Cover FLOW,
   concrete masks and protection. Keep complete premises and physical interfaces.
3. Implement the selected reversed-MUST overlap correction. Verify the former
   reverse exclusion counterexample and unchanged disjoint cases.
4. Implement admitted NORMAL relation families, current publication updates,
   and canonical saved index rebuilding. Add no derived-demand retraction.
5. Pass explicit matching roles through physical calls, blocks, observers,
   ND/Target and static adapters. Gate only the strict ancestor STAR channel.
6. Run focused AP/store/native driver regressions, then required repository
   tests. Commit the implementation after those gates pass.
7. Run the configured project campaign and the bounded exact field-path
   investigation in section 10. Report limits and next targets from evidence.

If a native counterexample needs a new field, layer, source-permission, growth,
or stop rule, stop that design extension and ask for a decision. A new proof
of changed semantics is not permission to add that semantics.

## 10. Post-implementation experiments and field-path investigation

### 10.1 Same configured campaign

Use the landed source and a clean built runner. Pin the source revision, runtime
archive hash, rules/config hashes, JDK, workers, project revisions and commands.
Use the existing `runProjectAnalyzer` Gradle task directly for OWASP, Conductor,
Thingsboard and Stirling-PDF. Keep FULL marks, 16 GiB heap, statics/aliases on,
field limits `1,1,2,...`, IFDS timeout 1,000 s for OWASP and 1,080 s for the other
projects, and the existing 1,200 s outer bound. Use the saved project-specific
configuration and OWASP CI inputs. Do not add an alternative configuration.

Reuse the fixed quality baseline `f945f92c5ae554ff4f5fc7696ee5a269210478bb` and
the saved `52f32dd` performance campaign. Do not rerun those baselines. Distinguish
fixed-baseline findings from equality to the latest accepted report. Compare
source/sink locations, rule and report identities, including NormalTarget IDs.
Batch-dependent diagnostic callback counts may vary. No new FN is acceptable;
list inherited missing and censored identities separately.

For every project and diagnostic, always state latest reached, latest completed
and latest accepted run. A timeout run has no completed frontier. Record run-1
engine time separately from prescan and transition. Record each later engine
time, transition time, input/output demand, NORMAL/DEMAND and Target counts,
method keys, scoped loop rows, memory, GC, OOM and timeout status.

Capture a 30-second CPU/allocation profile after about one minute under workload,
and another near the bound where the process remains active. Capture a heap
when the analyzer memory manager reports OOM. Preserve hashes/portable data,
then remove only artifacts and processes owned by this experiment. Do not remove
the user's debugging directories or files.

### 10.2 Repeat the same exact-fact investigation

Prioritize Stirling run-5/6/7 and Conductor run-3/4/5. Include Thingsboard's
latest reached run, even if it has no completed frontier. If terminal iterations
change, investigate the corresponding last slow backward/forward runs too.
Do not compare a partial trace as if it were a full inventory.

```kotlin
data class TraceSample(
    val run: RunLabel,
    val ownerAndPhysicalPorts: ExactInterface,
    val premise: CompletePremise,
    val input: FullAnnotatedFact,
    val record: ExactStoredRecord?,
    val role: SummaryMatchRole?,
    val matchBranch: MatchBranch, // AT, below, strict ancestor
    val output: FullAnnotatedFact?,
    val storedGrowth: GrowthClassification?,
    val c2Initials: List<AdmittedInitial>,
    val c5DemandPairAndBudget: C5Trace?,
    val finalAdmissionOrDrop: AdmissionReason,
)
```

Capture before/after pipelines, not only shape totals:

```text
offered packet
  -> canonical retained/removed leaves and exact covering witness
  -> saved direct/opposite selection and match branch
  -> applied output and stored growth classification
  -> loop consumer family / C2 / prepared C5
  -> restricted edge and cut path
  -> post-statement admission, summary publication, subscription delivery
  -> saved record and next-run paired demand
```

For each hot method/base/family, count:

- Physical packets, scalar leaf memberships, logical relations, record objects,
  output positions, match attempts, applications and fresh outputs separately.
- MUST/MAY prefix drops, excluded-field fills, protection-only residuals,
  cross-E matches and blocked coverage reasons.
- Aligned S/L families: eligible, covered, removed before publication, removed
  after publication, same-batch stale notification suppressed, prior queued
  delivery and derived DEMAND retained through ordinary settlement.
- Canonical-input C2 initials removed or retained, and exact next-run paired
  demand. Do not infer loss or correctness from a smaller count alone.
- CURRENT/SAVED_DIRECT/OPPOSITE selection by incoming tail, layer and mark kind;
  accepted/rejected strict-STAR contributions; AT/below preservation.
- Field depth and width by complete premise, base, tail, layer, scope and port.
  Include same-depth distinct paths and growing/equal/shrinking stored rows.
- Intraprocedural queue/store work versus summary pub/sub, saved replay,
  C2/C5, loop observation, static completion, allocations and retained memory.

For the main explosive families, embed representative code and exact facts:
the writer/source, reader/sink, all relevant NORMAL shorter relations, the
longer generated relations, demand in both directions, application roles,
field limits, C5 budgets and deduplication results. Show a concrete chain from
one operation to repeated work. State why each shorter relation did or did not
remove that work under the selected guards.

Include residual binary-width/MAY rewrite cases and reverse MUST observer
cases. Determine whether remaining work is intraprocedural, interprocedural,
or repeated consumer observation. Distinguish copied packets from new paths.
Do not attribute all time to loops from a high cyclic-instruction percentage.

Store reports and full portable evidence in the repository. Include skipped,
budget-dropped and incomplete captures with their denominators. Keep main
performance timings separate from instrumented diagnostic timings. Publish
exact source/config/artifact hashes and enough raw facts to reproduce every
claim; external-only `shape-probe-results` links are insufficient.

### 10.3 Acceptance and next decision

The implementation is acceptable only after the constructive checks and native
adapter regressions pass, and the configured campaign has a documented quality
comparison. Do not label a project timeout or censored report as a quality pass.
Explain whether each selected change removed the intended workload, which
pipeline is now largest, and whether any new bottleneck replaced it.

If the remaining family is not removed by these laws, write a separate proposal
with exact old/new handling and estimated operation-count reduction. Do not add
that optimization to this implementation without selection.
