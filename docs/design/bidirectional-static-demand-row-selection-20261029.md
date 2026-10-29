# Next iteration: select static labels before visiting them

Date: 29 October 2026.
Reviewed runtime: `bb74cef6cf483db167c161020a8a4cca576ca005`.
Status: proposal only. No production code changes are included.

The current thingsboard campaign reaches **run-2** and completes **run-1**.
Run-2 ends on TIMEOUT after 367.234 s. Its accepted forward report is run-1.
The closed run-2 counters show:

| Counter | Value | Meaning |
|---|---:|---|
| Owner evaluations | 603,417,178 | Completed first family tests inside individual views |
| Owner memo hits | 154,086,432 | Repeated family tests inside the same view |
| Memo arrays | 2,536,847 | Query-local visible views that allocated a memo |
| Memo byte payload allocated | 41,639,806,658 | Cumulative byte-array payload allocation; not live retained memory |
| C5 fixed-right rejects | 412,725,931 | Failed predicate invocations; not distinct rejected semantic states |
| C5 duplicates | 19,812,741 | Duplicate-state admissions |
| C5 popped states | 1,531,587 | Processed queue states |
| C5 composition attempts | 20,819,778 | Enumerated predecessors that reached composition |

In the closed restricted-run CPU evidence, static completion has 41.66% of
samples, C5 has 30.08%, C2 has 13.99%, and owner eligibility has 11.69%.
`MarkTable.isGroup` is a leaf in 4.48%. These inclusive families overlap.
The profile is not a proof that all fixed-right rejects are mark mismatches.
A right endpoint can also fail the raw emitter geometry or field-budget test.

The whole run-2 JFR window has 104,604 Java execution samples. C2 contains
58.24%, call-graph reachability 47.68%, and C5 17.41%. Call-graph reachability
also contains 50.94% of the sampled allocation weight. Java samples and the
late native CPU window above have different denominators. Do not add their
shares. Sampled allocation is traffic, not retained memory.

This whole-phase evidence makes the frozen owner-visibility index a
high-priority second stage. First select relevant rows, then measure which
owner questions remain. Build the extra index only if that measured work
still justifies its fixed cost.

The selected current P1 avoids expanding impossible states. It still visits
packed labels to discover that they are impossible. Current P2 avoids repeated
owner-family graph questions only within one view. A new view starts again.
These are two separate sources of avoidable work.

## 1. Scope and ranking

1. **Select FLOW and compatible mark rows before the row loop.** This removes
   unrelated labels, owner tests, decoding and mark-table calls. It applies to
   C2 and C5. Exact output relations and complete pairs must remain equal.
2. **Conditional follow-up: build one immutable owner-visibility index.** First
   measure the selector change. If necessary owner graph work still dominates,
   this index removes repeated graph traversals and per-view memo allocation.
   It uses the same common-method reachability law. It does not add a new
   reachability approximation. Do not pay its fixed build/memory cost before
   this new measurement supports it.

The first change has a direct finite-work proof. The second change has a fixed
snapshot memory bound and replaces query-dependent repeated graph work with one
construction. Neither change authorizes different demand, initial facts,
summary edges, group semantics, field transfer, source/sink identities or stop
policy. No core implementation is selected by this draft.

## 2. A direct C2 waste: FLOW-only adjacency visits every colored label

`FrozenStaticCompletion.View.rows` currently has this unfiltered path:

```kotlin
for (i in row.labels.indices) {
    val allowed = if (inherited) eligible(row.owners[i]) else isOwnRow(id, i)
    if ((!flowOnly || row.labels[i] == 0L) && allowed)
        yield(row.geometry.edge(row.labels[i]))
}
```

The owner test happens before the FLOW-label test. `flowStarts` and `flowEnds`
select a geometry that has a FLOW row. They do not identify its single FLOW
ordinal. `StaticEntryLookup` uses this path in `flowTargets`,
`incoming(flowOnly = true)` and `outgoing`.

Therefore, a geometry with one FLOW label and 100 colored labels can perform
101 owner tests to return at most one FLOW edge. P2 can cache some answers in
that view. It still receives those questions, and each new view starts again.

Freeze the single FLOW ordinal once:

```kotlin
private class BridgeRows(
    val geometry: GuidanceGeometry,
    val labels: LongArray,
    val owners: List<Owners>,
    val flowOrdinal: Int, // -1 if no label is FLOW; otherwise exactly one.
    val outputs: OutputSelectorIndex,
)

private fun flowRows(id: Int): Sequence<StaticGuidanceEdge> = sequence {
    val rows = bridges[id]
    val i = rows.flowOrdinal
    if (i < 0 || !allowed(rows.owners[i], id, i)) return@sequence
    yield(rows.geometry.edge(GuidanceMarks.Flow))
}
```

Use this direct operation for all FLOW-only adjacency. A label is unique inside
its geometry, so there is at most one `0L` label. Keep the original owner family
of that row. Do not apply a colored row's owner set to the FLOW row.

This change removes the other 100 questions. Skipping their graph scratch
updates is safe: the scratch computes a pure reachability Boolean. Its partial
search history changes cost, not the final Boolean for a later real question.

## 3. Select mark labels by the question

### 3.1 Preserve the exact selector domain

Freeze metadata only for selectors already present in static guidance. A query
can inspect a new actual mark's immutable key once. Do not enumerate all marks,
bind more rules, create group atoms, modify MarkTable, or restore `knownMembers`.

```kotlin
sealed interface Selector {
    data object Zero : Selector // Private nullable endpoint selector, not a mark group.
    data class Full(val atom: TaintMark, val group: GroupId) : Selector
    data class Group(val atom: TaintMark, val group: GroupId) : Selector
}

// Existing coversAtom law. Two full marks in one group are still different.
fun covers(guide: Selector, actual: Selector): Boolean =
    guide == actual ||
        guide is Selector.Group && actual != Selector.Zero &&
        guide.group == actual.group

fun composable(a: Selector, b: Selector): Boolean = covers(a, b) || covers(b, a)
```

Use direct immutable fields in this helper. The pseudocode's common `group`
access needs an ordinary typed helper in Kotlin. ZERO has no group. Null must
never mean wildcard.

FULL is still exact. `Full(T,G)` and `Full(U,G)`, T != U, are not composable.
A `Group(G)` selector can cover T or U. This matches the current asymmetric
`coversAtom` and symmetric label-composition test.

### 3.2 Output-selector index for one geometry

Keep complete packed `(input, output)` labels. Add ordinal indexes; do not
project away the input label or combine independent input and output sets.

```kotlin
private class OutputSelectorIndex(
    val full: Map<TaintMark, IntArray>,       // Rows whose output is that FULL atom.
    val group: Map<GroupId, IntArray>,       // Rows whose output is that GROUP selector.
    val fullInGroup: Map<GroupId, IntArray>, // Full rows in a group; needed for a GROUP query.
    val zero: IntArray,                     // Local ZERO endpoint cases only.
)
```

A static/static bridge has no ZERO endpoint. `packBridgeMarks` already requires
nonnull selectors there. Local W/R rows can have a genuine ZERO endpoint, so
the typed query contract must retain it. Do not store ZERO as a group ID.

For a Full(T,G) query:

```text
outputs that COVER T:      full[T] plus group[G]
outputs COMPOSABLE with T: full[T] plus group[G]
```

For a Group(G) query:

```text
outputs that COVER Group(G):      group[G]
outputs COMPOSABLE with Group(G): group[G] plus fullInGroup[G]
```

The distinction is required. A concrete full T cannot cover a GROUP demand;
it can compose with a GROUP selector in the other direction. Do not reuse one
of these candidate operations for both questions.

Every resulting ordinal still goes through the full existing `keep` callback
and geometry join. The index supplies a necessary mark condition, not the full
C2/C5 predicate. Owners are checked only for selected ordinals. Decode the final
edge only after selection and ownership.

Preserve original ordinal order within a selected union if diagnostic ordering
is useful. Use a sorted ordinal union, rather than concatenate buckets with
unknown duplicates. The semantic proof requires equal relations, not equal
counts of rejected callback invocations.

### 3.3 Reject impossible mapped geometry once

A wrong full mark is not the only reason for a fixed-right rejection. The raw
emitter image can also reject the path, tail, E or field budget. All mapped
labels of one bridge row share that right geometry.

For a legal current FULL original member M, a conservative precheck can use its
own concrete mark as the demand mark. This keeps the concrete-mark shape and E,
but removes possible mark incompatibility:

```kotlin
fun mayHaveMappedRight(member: InitialAp, geometry: Pattern): Boolean {
    val mark = member.mark as? MarkSlot.Concrete ?: return true // Conservative fallback.
    if (!catalog.isFull(mark.mark) || geometry.fact.base == ZERO) return true
    val compatible = geometry.copy(fact = geometry.fact.copy(mark = member.mark))
    return policy.canStoreInitial(normalizeDemandFieldExclusion(compatible),
        member.toPattern())
}
```

Derive `isFull` from the member's one immutable selector descriptor, rather than
call MarkTable for each row. The shown fallback is deliberate: do not prune an
unproved ZERO, abstract or unusual selector case. For legal FULL members and
nonzero targets, prove this implication:

```text
original mayKeep(member, rightWithMappedOutputQ)
  implies mayHaveMappedRight(member, rightGeometry).
```

`canEmitInitial` checks the same raw initial legality, base, path, tail, E and
budget after replacing Q by M. Its rendered-mark and containment mark checks
now match M with itself. The mark value does not change the concrete/abstract
kind. Thus a false precheck rules out every mapped output Q at that geometry.
It creates no hypothetical AP key and no submitted fact.

Run this precheck once per right geometry and original member before mapped
label enumeration. When it fails, omit the mapped ordinals but retain the FLOW
ordinal. Do not reuse this concrete-kind check to reject a FLOW row: an abstract
right descriptor has a different raw-emitter image, and the existing FLOW repair
path remains in scope. A stronger all-kind geometry prune is a separate proof.

For target seeds, use the precheck on each spatial geometry. A right Mapped state
has already passed the final fixed-right check. For predecessors of a FLOW right
state, compute this permission once from the fixed `state.to` geometry before
selecting incoming mapped ordinals. Keep the complete final `keep` callback on
every retained row. Do not use the target precheck on isolated source/writer
preflight rows.

### 3.4 C5 has three exact questions

An arbitrary `StaticCandidateFilter` callback cannot expose its lookup key.
Add a narrow internal query descriptor to the existing C5 capability. Keep the
callback as the final guard and keep public/reference fallback behavior.

```kotlin
sealed interface LabelSelection {
    data object FlowOnly : LabelSelection
    data class OutputCovers(val actual: Selector) : LabelSelection
    data class OutputComposesWith(val requiredInput: Selector) : LabelSelection
    data object FlowOnlyForAbstractInitial : LabelSelection
}
```

FLOW is an independent row option, rather than a member of the selector index.
For C5 target/predecessor operations below, union the single FLOW ordinal with
the mapped selected ordinals. Final `mayKeep` still checks geometry, budget and
canonical raw-emitter preimages.

| C5 point | Necessary mapped-row selection | FLOW row |
|---|---|---|
| Target seeds for concrete original M | Output covers M | Keep |
| Target seeds for abstract FLOW original | No mapped row can render an abstract initial | Keep |
| Incoming predecessor when right state is `Mapped(U,T)` | Left output composes with U | Keep |
| Incoming predecessor when right state is FLOW, concrete original M | Left output covers M | Keep |
| Incoming predecessor when right state is FLOW, abstract original | No mapped row | Keep |

The right state `Mapped(U,T)` must first pass the existing fixed-right test for
T. An incoming mapped predecessor changes U, but cannot change T. A FLOW right
state is different: a mapped predecessor can supply its final mark. Keep that
repair path; do not filter the entire FLOW state as unmarked.

```kotlin
val selection = when (val right = state.marks) {
    GuidanceMarks.Flow -> outputCoveringOriginal(member)
    is GuidanceMarks.Mapped -> OutputComposesWith(selector(right.input))
}
for (left in view.selectedIncoming(state.from, selection, keepIncoming)) {
    existingCompose(left, state)?.let(::admit)
}
```

Use the same selection in target existence preflight and target enumeration.
Do **not** apply the target mark selection to isolated source/writer existence
preflight. An earlier writer can have a different mark that a later mapping
changes to the requested mark. The current source preflight stays conservative.
Primitive complete local `pairs` can use output coverage of the current member
before full C5. Do not project them into a source/target Cartesian product.

### 3.5 C2 entry selection must happen before owner eligibility

Current `View.entries(actual)` yields spatially related entries and checks
inherited entry owners before `InitialDemandResults.offer` rejects a wrong mark.
`policy.emit` always requires this necessary condition:

```kotlin
markSub(entry.fact.mark, actual.fact.mark, catalog)
```

Move that test before ownership. A first small step can filter existing entry
candidates there. The complete work-removal design also groups entry rows by
mark-free geometry and indexes their output selectors, like bridge labels:

```kotlin
private class EntryGeometryRows(
    val geometry: PatternGeometry, // base, full chain, tail and E; no runtime mark.
    val flowOrdinal: Int,
    val selectors: OutputSelectorIndex,
    val owners: List<Owners>,
)
```

The path trie stores geometry IDs. It no longer returns every mark row at the
same path. A marked actual T selects the FLOW entry and entries whose selector
covers T. An abstract actual selects only abstract FLOW entries. Genuine ZERO
uses its private exact selector and the existing ZERO demand path. Never call
`groupOf(ZERO)`.

After selection, reconstruct the full entry mark before demand E normalization.
A mark-free placeholder with STAR tail is metadata. Normalizing it first could
erase the field E of a concrete entry. Then use the unchanged `policy.emit`.

Local W/R entries remain attached to their complete MethodKey. Add equivalent
mark selection inside that attachment; do not move them into a common-method
or global pool. Coverage envelopes can use the same necessary selector index,
but keep every structural emitter family that can still produce an initial.
The early-stop test must not become vacuously true because the index lost a
GROUP or FLOW candidate.

`hasMarkedOutput` already has a mark question but currently scans every label
of each spatially selected bridge. Use the output-covering selector lookup
there too. `markedOutputs(mark)` already has exact and GROUP buckets; retain
that behavior and use it as an existing reference for the directional lookup.

## 4. Annotated code example

The method copy has no source rule. It can receive 100 different full marks
across the run-1 input set. The actual read/writer protocol creates its
corresponding FLOW and marked guidance.

```java
void copy() {
    C.b = C.a;
    // FLOW relation: C.a.*/FLOW -> C.b.*/FLOW.
    // Marked relations after requested actual writes:
    // C.a.*/T0 -> C.b.*/T0, ...,
    // C.a.*/T99 -> C.b.*/T99.
}
// Static/static guidance is kept for the run-1 -> run-2 handoff.
// The live caller procedure does not relay all these static/static summaries.
```

At run-2, take an actual backward marked input `C.b.$/T7`.

```text
C2 FLOW-only route question:
  Need only bridge C.a/FLOW -> C.b/FLOW.
  Current rows(flowOnly=true): test owners for FLOW,T0,...,T99; return FLOW.
  New flowOrdinal: test only FLOW's owner; return the same FLOW relation.

C2 direct-entry question:
  Current: visit FLOW,T0,...,T99 entries and test their owners;
           emitter rejects every concrete mark except T7.
  New: select FLOW and T7 before owner tests, then run the same emitter.

C5 target question with original C.b.$/T7:
  Current P1: decode/test all101 labels; wrong mapped outputs fail mayKeep.
  New: select FLOW and T7, then run the same mayKeep/owner/geometry tests.

C5 incoming question for a right state Mapped(T7,T7):
  Current: inspect all101 labels, reject incompatible mapped inputs.
  New: inspect FLOW and rows with output T7 (plus covering GROUP if present).
```

| Work for one spatial geometry with 100 unrelated full labels | Current | New |
|---|---:|---:|
| FLOW-only label/owner visits | 101 | At most 1 |
| Direct C2 entry owner candidates for T7 | 101 | At most 2 |
| C5 seed label tests before final predicate | 101 | At most 2 |

A matrix `Ti -> Uj` can have many rows with the same output Uj. Keep **all** of
those input/output pairs. If there are K input marks and K output marks, an exact
output lookup selects K relevant rows instead of K squared rows. It does not
collapse K distinct dependencies to one. GROUP rows can broaden these selected
sets according to the existing coverage law.

These are exact example counts. Current thingsboard needs a histogram of labels
per selected geometry and a reject-reason split before a project factor can be
claimed. The 412,725,931 fixed rejects include repeated tests and non-mark
failures; they are not 412,725,931 unique avoidable labels.

## 5. Second stage: one owner-visibility index per snapshot

First apply selective label enumeration and measure the remaining owner tests
and graph visits. Select this index only if those necessary questions still
justify its construction and fixed memory. The bounds below describe a viable
alternative; they do not make eager construction the default next change.

### 5.1 Existing law

The current visible view asks:

```text
eligible(method, family) =
    method is in family.outsideGraph
    OR some family.graphId is reachable from method in the detached call graph.
```

Reachability is reflexive. A method can use its own B rows. Local direct views
use owner equality, not transitive reachability. W/R attachments keep their exact
MethodKey. These three scopes must remain separate.

The snapshot has 51,953 graph vertices, 117,581 edges and 16,414 owner families.
The graph and family sets are immutable during run-2. Repeating the same graph
question in 2,536,847 views is unnecessary.

### 5.2 SCC family propagation

Build strongly connected components once. Use an iterative constructive SCC
algorithm; do not use JVM recursion for an unbounded call chain. Collapse the
graph to a DAG. For each component, seed a bit for each family with at least one
owner in that component. Then process the DAG in reverse topological order:

The family universe includes both freeze sources: bridge-label owners and
projected-entry owners. Use the existing complete family IDs. An index built
only from bridge labels would omit some C2 entry visibility.

```kotlin
for (family in ownerFamilies) {
    for (owner in family.graphIds)
        visibleFamilies[component[owner]].set(family.id)
}
for (component in reverseTopologicalOrder) {
    for (calleeComponent in dag[component])
        visibleFamilies[component].or(visibleFamilies[calleeComponent])
}
```

This is graph propagation of **owner-family bits**, not static edge closure.
It does not enumerate static compositions or materialize method demand products.

A visible query becomes a bit lookup:

```kotlin
fun eligible(commonMethod: CommonMethod, family: Owners): Boolean {
    cancellation.checkpoint()
    val id = graph.id(commonMethod)
    if (id != null) return visibleFamilies[component[id]].get(family.id)
    return family.id in outsideFamiliesByMethod[commonMethod].orEmpty()
}
```

`outsideFamiliesByMethod` is exact owner membership. A method absent from the
graph had an empty reachability scratch before this change; it does not acquire
transitive successors. An outside owner cannot be reached through an indexed
graph vertex, so the indexed-method bit lookup does not need that fallback.

Keep local view `ownRows` and exact W/R attachment lookup unchanged. Do not use
the transitive bit table for local owner equality. Method contexts still do not
enter the B visibility graph, exactly as now. They still enter W/R ownership.

Remove the per-view byte memo and graph scratch only after the immutable table
is complete and published. Keep the detached graph until its other handoff
queries no longer need it. Release the table with the run-2 static completion;
run-3 and later retain local-only demand behavior.

### 5.3 Fixed resource bound

With S SCCs and F owner families, a dense row has `ceil(F/64)` longs.
For the observed upper bound S <= V = 51,953 and F=16,414:

```text
F words per row:                 257 longs
word-rounded row bytes:          2,056
all rows, before headers:        106,815,368 bytes = 101.867 MiB
raw bit count before rounding:   852,756,542 bits
DAG propagation OR operations:   <= 117,581 * 257 = 30,218,317 long ORs
```

SCC compression and duplicate DAG-edge removal can reduce these values. Add
component IDs, DAG adjacency, row headers and outside-owner indexes to the
measured retained total. Do not compare this 107 MB fixed payload with 41.64 GB
as if the latter were retained memory. The latter is cumulative allocation in
millions of now-dead view arrays. The proposed table removes that allocation
stream and repeated graph traversal.

Build cost is O(V+E+owner memberships+E_DAG*ceil(F/64)). Storage is
O(S*ceil(F/64)+V+E_DAG+outside memberships). It does not grow with query count.
Report table construction time as a distinct transition phase; it cannot be
hidden inside a claimed faster engine. Keep cancellation checkpoints in every
vertex, edge, owner and word loop. Publish no partial table after interruption.

A sparse representation is a later technical option. It is not needed to state
or prove the work-removal mechanism, and it must not introduce an unbounded
per-query answer cache.

## 6. Required equivalence proofs

Follow `spec/proof-guide.md`. The following are design proof arguments, not a
claim of a newly checked Lean artifact. Before implementation, use finite
constructive models and executable witnesses.

### 6.1 Selected rows equal the old filtered rows

For each bridge geometry, prove that packed label uniqueness gives at most one
FLOW ordinal. Direct FLOW selection returns the old filtered list's same row
with the same owner family. For concrete selectors, prove:

```text
row is in outputCovering(q)  iff old coversAtom(row.output,q)
row is in outputComposable(q) iff
    old coversAtom(row.output,q) OR old coversAtom(q,row.output)
```

Handle FULL/FULL inequality within one group, GROUP/FULL asymmetry, GROUP/GROUP
and genuine ZERO explicitly. The construction witness is the exact old ordinal.
The new query cannot substitute another row with the same output mark but a
different input mark or owner set.

For C2, `markSub` is necessary before every successful `policy.emit`. A removed
wrong-mark entry cannot emit an initial. Keep the final emitter for field/E,
tail and budget tests. Prove the coverage-family envelope retains every possible
emitter image. Preserve GROUP-to-full binding without creating a group atom.

For C5, first prove the FULL-member mapped-geometry precheck implication. Keep
its conservative fallbacks and FLOW row. Then prove the three questions in
section3.4 are necessary conditions of the exact
existing `composeMarks` and `mayKeep` functions. Every productive old state or
predecessor has the same selected ordinal witness. Keep FLOW repair states and
the complete `Mapped(input,output)` relation. Final geometry and raw-emitter
preimage checks remain in place. No target filter is applied to the isolated
source preflight.

Every selected row then uses the same owner Boolean. Thus C2 initial sets,
C5 selected pieces, protection, demand frontiers and source/sink identities are
equal after quiescence. Callback/reject counters can fall. Do not use equal
counter values as an equivalence requirement.

### 6.2 SCC family bits equal original reachability

Prove SCC membership gives a finite path between any two members. Prove the
condensation graph is acyclic and its edges preserve caller-to-callee direction.
Use reverse topological induction:

```text
family bit f is set at component c
iff an owner of f is in c
    OR a successor component has bit f
iff a graph path from c reaches an owner of f.
```

A set bit must yield an executable owner/path witness. A graph path to an owner
must set the bit by this recurrence. Include a zero-length self path, recursive
SCCs, empty owner families and several owners in one family. Outside-graph
membership is a separate exact case.

This proves the same Boolean as every completed `Reachability.reachesAny`,
regardless of prior query scratch progress. Removing scratch updates and memo
hits therefore changes only work. It cannot grant W/R visibility or merge
MethodKey contexts. Publication is atomic after the joined build, and read rows
are immutable for the entire receiving run.

### 6.3 Finite-work proofs

Prove the FLOW query visits at most one label per spatial geometry. Prove exact
mark lookup visits only its compatible row ordinals plus the FLOW row. Give a
finite matrix example with K squared full labels and K selected output rows.
For visibility, prove each DAG edge is processed once and each family lookup is
one bit test. Compare this with Q independent graph scratch traversals; do not
assume all old queries traverse the whole graph.

## 7. Implementation and measurement gates

1. Model selectors, row selection and SCC family visibility in Lean. Prove the
   equivalence and finite-work statements constructively. Do not assume the
   mark compatibility law or a correct SCC implementation as an unexplained
   oracle.
2. Add reference-differential tests. Keep the old full label loop and BFS owner
   predicate in test-only code. Test C2, C5 and both local/visible views through
   final outputs, not only candidate counts.
3. Use FULL and GROUP snapshots. Include T and U in one group, a GROUP selector,
   mixed FLOW/mapped rows, ZERO endpoints, field exclusions, exact class
   markers, raw canonical initial preimages, mark-changing chains and cycles.
4. Test a FLOW right state repaired by a mapped predecessor. Test a source
   preflight with the wrong immediate mark that a later mapping converts.
   Test exact-context W/R isolation even when common methods are equal.
5. Test SCCs, self edges, disconnected components, outside methods, empty owner
   arrays, many owner families, cancellation during build and no partial
   publication. Verify one snapshot table is released after run-2.
6. Count old labels visited, selected labels, wrong-mark rejects, other fixed
   rejects, owner questions and graph vertices/edges visited. Count all repeated
   invocations separately from distinct geometry/label pairs.
7. Repeat the fixed project campaign on one pinned source. Preserve baseline
   rule/source/sink identities. Capture normal and restricted-run profiles and
   transition time. Include latest reached, complete and accepted runs.

The source and thingsboard counters justify this direction. The next selection
must still state the expected saved work from actual label-width/reject-reason
counts. No benchmark has been run for the proposed index. Do not promise a
2x end-to-end gain from an inclusive CPU share or from an illustrative matrix.
