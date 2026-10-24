# Concrete relations backed by FLOW

Date: 24 October 2026. Status: **implemented and locally checked; project measurements pending**.

This specification selects cross-premise FLOW reuse, exact concrete relation
compression, and FLOW priority in run-1. Read the
[proof dossier](run1-flow-backed-concrete-relations-proofs.md) with this document.
It replaces section 3 of the
[next-iteration proposal](../docs/design/bidirectional-rule-selection-next-iteration-20261024.md).

The reference runtime is `40e20d16f03ab046df75a53a489bb331b065a9c1`.
The current documentation parent is `8e7084b492d7d827ab93c8d3d686a9e59a159a38`.
The latest Thingsboard measurement reached **run-1 OOM**. It has no COMPLETE
or accepted forward run. No new project run was made for this specification.

Terminology: **protection is the non-subsumable flag**. These names refer to
the same per-output-leaf/per-FULL-mark Boolean. There is no second protection
mechanism, support label or dependency graph.

## 1. Selected changes and unchanged behavior

The objective is to remove duplicate relation storage and propagation. Making
one scalar AP operation faster is not the objective.

| Mechanism | Current behavior | New behavior | Proof obligation |
| --- | --- | --- | --- |
| Cross-premise summaries | Separate FLOW and concrete premise rows can represent the same relation | A proved FLOW instance replaces an unprotected same-mark concrete part, including its redundant T demand | Pair coverage, original AP application, demand replacement |
| Concrete geometry | Marked premises repeat input/output geometry | One immutable geometry can serve an exact set of FULL marks | Exact decode; no cross-mark products |
| Rule dependencies | No protection flag is needed because marked relations remain | A protected marked result cannot be removed by FLOW | Assignment, cleaner, local/call cycle, sticky merge |
| Work order | Nonzero FLOW and TAINT share the changed lane; unchanged TAINT can run first | FLOW has priority in the current nonzero phase | Same enabled work and barriers; finite-key progress |
| Layers | Run-1 forces TAINT to DEMAND | A covered part can use the existing NORMAL FLOW proof; other parts keep their original layers | No blanket TAINT upgrade; preserve caller-layer composition |

**The removal of a marked demand is a major change to the handoff contract.**
It needs the proof in section 8. Storage compression alone does not authorize
this removal. Protection is also a new part of admission and propagation.
It is not part of a mark name or an AP path.

The following mechanisms retain their current contracts:

- FULL mark ownership, primitive properties, selected executable rules and
  metadata rules. FULL remains the default run-1 mode.
- Field limit 1, field reads/writes, empty run-1 field exclusion E, cuts,
  alias application, exact/ANY/MUST tails and source/cleaner actions.
- CM truth, source guards, all-ZERO tests, all contributing run-1 origins,
  sink seeds, exit rules and report occurrence identities.
- Static micro-edge producers, read activation, requests, supplies, static
  summary erasure and the existing later-run static adapter.
- ZERO/control phases, actor ownership, cancellation and actor quantum.
- Later-run direction/limits, normal record persistence and original AP
  demand-driven emission and restriction.

There is no new grounding support, rule specialization, added-fact store,
answered-request archive, global routing graph, IR representation, soft-reference
manager or mark census. GROUP mode can use the unchanged scalar path. This
specification proves the new path for **FULL run-1**.

## 2. Terms and valid shapes

`I -> O, L` is a relation with initial I, conclusion O and layer L.
`*` in the mark slot is FLOW. T and U are complete owned FULL marks.
`*/E`, `[any]`, `$` and MUST refer to field tails. Mark exclusion `mx`
is separate from field exclusion E.

```text
F: I(p, STAR, *) -> q/ANY/(* minus X), DEMAND
E: I(p, STAR, T) -> q/ANY/T,           DEMAND
```

FLOW preserves the input mark. It does not prove that an actual T input
exists. A source or the existing supply/request mechanism must supply T.

All existing initial grammar checks remain. In particular, no new run-1
initial has an ANY tail. A broad concrete STAR initial can start with an
ANY DEMAND conclusion. Named static fields and EXACT global class markers
retain their separate cases; broad concrete root/class statics are not
introduced in run-2. Unsupported shapes use the existing representation.

A comparison key includes method/context, node or summary endpoint,
normal/exceptional exit, complete premise geometry and the applicable call
stage. It also includes resume address, cleaner phase, original caller
scope, identity/alias effect class and layer annotations when these affect
transfer. Equality of base
names alone is insufficient.

## 3. Two distinct uses of FLOW

### 3.1 Semantic replacement

Let `lift(F,T)` be the original AP relation of F on input mark T. A concrete
part E is eligible for replacement only if all these tests pass:

```kotlin
// This implementation handles the proved run-1 ANY output case.
fun canReplaceAny(e: MarkedPart, f: FlowTreePart): Boolean =
    e.inputMark == e.outputMark &&
    !e.nonSubsumable &&
    sameRelationScope(e, f) &&
    sameInitialShapeIgnoringMark(e, f) &&
    e.finalBase == f.finalBase &&
    e.finalTail == ANY &&
    f.fields.anyPrefixOf(e.finalFields) { leaf ->
        leaf.tail == e.finalTail &&
        leaf.admits(e.outputMark) &&
        enoughLayerStrength(f, leaf, e)
    }
```

`sameRelationScope` keeps the method/context, point/endpoint, call stage and
applicable effect class described in section 2. Initial shapes must agree
in base, concrete field path, tail and E; only their marks differ. Output
bases and field tail kinds must agree. The FLOW output's location set must
**contain** the TAINT output's location set. Containment includes equality.

For ANY tails this is exactly the prefix test above:

```text
FLOW x.[any]     contains TAINT x.f.[any]
FLOW x.f.[any]   contains TAINT x.f.[any]
FLOW x.f.[any]   does not contain TAINT x.[any]
FLOW x.f.[any]   does not contain TAINT x.g.[any]
```

The FLOW conclusion contains a concrete **field tree**. The tested TAINT
conclusion has one concrete field path. Coverage requires **any one** eligible
FLOW output path from that tree to prefix the TAINT path:

```text
FLOW tree paths: {x.f, x.g.h}, each with an ANY output
TAINT path:      x.g.h.k
Result:         covered by x.g.h
```

The FLOW tree need not be a single path or equal the TAINT path. It need
not cover the entire TAINT tree either: test each TAINT output path/mark.
One qualifying FLOW path is sufficient. Its tail, mark exclusion and layer
checks must all pass at that same path. An internal branch node with no
FLOW output annotation is not a covering output. A prefix which excludes
T does not prevent another eligible prefix from covering T.

`anyPrefixOf` walks the TAINT field path through the FLOW trie and checks
the output annotations at the root and each reached prefix node. It stops
at the first qualifying output. It does not enumerate all FLOW paths or
compare every FLOW/TAINT path pair. The existing single-path proof applies
to the selected FLOW path; the FLOW tree denotes the union of its outputs.

This means spatial containment, not a longer textual path containing a
shorter path. For EXACT tails only the same point is contained. A correlated
STAR tail also requires its input/output suffix relation; a prefix test
alone is not sufficient for it.

The former name `provedApplicationAndHandoffCell` meant a case of the AP
operation table for which design-time proofs exist. It was a specification
placeholder, not an extra runtime mechanism. The explicit shape checks above
replace it. Unsupported tail cells retain the exact fallback. No theorem
search, per-edge proof object or derivation history is required at runtime.

The mandatory cell is an **ANY/ANY** pair with canonical STAR/Empty initials
and T not in X. Both relations are DEMAND. If the output paths are equal,
the existing AP reducer gives equal concrete applications, including facts,
requests and result layers. If the FLOW path is a proper prefix, its existing
broader image contains the marked image; the results need not be equal
headers. The prefix proof also checks original demand emission at a narrower
marked requirement. The equal-path local equality holds when the summary
layers are equal and NORMAL. A stronger NORMAL FLOW proof
can replace a DEMAND marked part only under the original normal-record
contract. DEMAND FLOW cannot replace a NORMAL proof.

The implementation can add other cells only with their application and
handoff proofs. EXACT/MUST variants and differing field tails use the exact
fallback until those proofs exist. In particular:

```text
FLOW:  p.*/* -> x.*/*, NORMAL
TAINT: p.*/T -> x.[any]/T, DEMAND
```

These relations have different suffix constraints. The FLOW cannot replace
the whole TAINT relation. An actual `p.left/T -> x.right/T` pair can belong
to the latter and not the former. Do not convert STAR to ANY, or ANY to
EXACT/MUST, to make the test succeed.

Evaluate coverage per output leaf and mark. Keep uncovered leaves and
protected marks. Do not require a whole concrete premise tree to be covered.

CM does not exclude T from FLOW. A selected-mark cleaner can exclude T.
If T is excluded at the tested FLOW leaf, that leaf does not cover T.

### 3.2 Geometry compression

When semantic replacement fails, geometry can still be shared. The row must
decode to the original relation, with its original layer and marked premise.

```text
template = p.*/* -> x.*/*, NORMAL
row      = (template, {T,U}, concreteHeader=STAR -> ANY, DEMAND)
decode   = { p.*/T -> x.[any]/T, DEMAND,
             p.*/U -> x.[any]/U, DEMAND }
```

The NORMAL template does not prove a NORMAL marked row here. T and U still
have their original demands. A mask `{T,U}` is diagonal. It never means
T-to-U, U-to-T or an arbitrary product of marks.

If no suitable FLOW geometry exists, keep an explicit TAINT row. Equal
explicit geometries can also use exact masks. Preserve real cross-mark
input/output correlations in separate rows. A compact header must not hide
a second complete conclusion tree.

## 4. Non-subsumable conclusions

The non-subsumable flag, also called protection, belongs to one logical edge
output leaf and FULL mark. It does
not affect CM, the ordinary fact key, the mark interner, layer or field
geometry. It only prevents FLOW replacement and carries a required marked
dependency to the handoff.

### 4.1 Rule assignment

Compare the assigned mark with the **conclusion that triggered the rule**.
Do not use only the original premise mark. For a projected original I and
an accepted input conclusion with mark U:

```kotlin
fun assignedProtection(
    old: Boolean,
    origin: FullMark?,       // mark in original I, if I has a concrete mark
    triggering: FullMark,   // U in I -> position/U
    assigned: FullMark,     // V
): Boolean = old || triggering == assigned ||
    (origin == assigned && triggering != assigned)
```

Thus `I/K -> p/T`, followed by assigning T to q, protects `I/K -> q/T`
even when K differs from T. The final clause also protects a **local**
T-to-U-to-T cycle. The user selected cycle protection for local rules and
summary application.

Use actual accepted rule contributions. An unrelated T in a packed tree
does not make an action a same-T assignment. For a multi-input rule, OR
the contribution flags and matching triggering-mark tests. Apply the cycle
test for each emitted original. Keep all required origins and the complete
guard binding. Emit ZERO only when a complete cube has all-ZERO support.
This specification does not change origin projection or enumerate origin
products.

### 4.2 Cleaners

Treat a surviving selected-T result as an assign-back of T. This includes
a same-base selected-T residual which the cleaner cannot remove. It is
therefore protected by the triggering-conclusion test. A complete kill
emits no result. Other bases and unselected marks pass as before.

This rule is necessary even when the concrete position is spatially
disjoint: the current nonstatic FLOW cleaner can exclude T for that base.
Do not change that cleaner operation or its requests. For RemoveAllMarks,
keep the existing spatial kill/residual operation. Its surviving results
can use the same conservative assign-back adapter; otherwise that adapter
must keep marked residuals when it cannot certify neutral FLOW replay.
There is no new CM-definiteness test.

### 4.3 Calls, ordinary transport and merge

```kotlin
// Caller I/T -> arg/U; callee U -> result/V.
fun appliedProtection(
    origin: FullMark?, incoming: FullMark, outgoing: FullMark,
    inputProtected: Boolean, summaryProtected: Boolean,
): Boolean = inputProtected || summaryProtected ||
    (origin == outgoing && incoming != outgoing)

fun mergeProtection(old: Boolean, offered: Boolean): Boolean = old || offered
```

Ordinary copies, filters, field cuts, aliases, returns and static promotion
carry the input flag on each surviving output. A kill removes its membership
and flag together. An ordinary same-mark FLOW pass does not set a new flag.
A protected summary conclusion protects each result of its application.

Identical edges collapse to one protected edge if either copy is protected.
The result is the same in both arrival orders. For masks, keep a protected
subset; do not protect U because the same leaf contains protected T.

A callee summary describes its canonical hypothesis. Do not put caller
protection on the callee's globally shared initial. Keep input protection
with the caller subscription/N2 input and apply it when composing the
summary. Similarly, the static service publishes actual mark availability;
it does not make T a globally protected mark. Keep protected writer
dependencies under their original origins. A static read can establish its
existing canonical static origin without retaining the writer's provenance.

### 4.4 Protection-only work

```kotlin
data class MarkDelta(val newMarks: FullMarkSet, val newlyProtected: FullMarkSet)

fun admitMetadata(old: Row, offered: Row): MarkDelta {
    val fresh = offered.marks - old.marks
    val protected = offered.protected - old.protected
    old.marks += offered.marks
    old.protected += offered.protected
    return MarkDelta(fresh, protected)
}
```

New protection is work even when the ordinary facts are equal. It must
reach all successors, stored rule contributions, callers, summaries and
the handoff. If FLOW already removed the plain summary copy, a later
protected offer recreates the marked residual and demand.

Keep ordinary equality/hash and occurrence keys. A metadata update does
not create another report or source/sink occurrence. Annotation propagation
must still update outputs of a previously accepted rule binding. Do not
hide this update behind `ordinaryFactsUnchanged` or the unchanged-work seen
set. A separate annotation delta is sufficient; a new semantic fact kind
is not required.

Ordinary TAINT subsumption must not erase new protection either. For example,
an existing plain `x/[any]/T` can contain a newly protected `x/$/T` offer.
The ordinary AP delta can be empty, but the protected region is new. Retain
that region separately, or conservatively protect the containing T leaf and
propagate its upgrade. Compare protected masks only within the same complete
row geometry. Do not subtract T from a protected offer merely because some
other row already contains ordinary T.

## 5. Storage and ownership

The following is a contract sketch, not a required Kotlin class layout:

```kotlin
data class ConcreteHeader(
    val scope: RelationScope,
    val inputShape: InitialShape,  // complete tail/path/E, without diagonal T
    val outputTags: LeafTags,     // original ANY/EXACT/MUST and layer
)
data class BackedRow(
    val geometry: FlowRelationRef,
    val header: ConcreteHeader,
    val marks: FullMarkSet,
    val protected: FullMarkSet,   // subset of marks
)
class Relations {
    val flow: FlowStore
    val backed: BackedConcreteStore
    val explicit: ExplicitConcreteStore
    val localProgress: MarkProgress // method points only; current memberships
}
```

| Owner | Stored state | Purpose |
| --- | --- | --- |
| Method actor / MethodEdgeStore adapter | FLOW geometry, exact marked memberships, protected subsets, explicit residuals and per-stage progress | Keep marked rule observations while avoiding duplicate geometry |
| RunSummaryStore raw collection | FLOW and normalized concrete residuals | Persistence and end-of-run results |
| RunSummaryStore selected-demand collection | FLOW guidance and required concrete residuals | Build the original handoff |
| PublicationIndex and caller publication state | Current FLOW coverage and residual marked publications | Prevent future subscriptions from replaying removed marked payloads |
| Worklist and saved continuation | Immutable geometry, fresh mark mask, fresh protection mask and complete address | Process each required membership/flag update |
| Existing static service | Existing write/read/request/supply state | Actual mark availability; no new store in this proposal |

Use one authoritative admission law for a logical member. Two candidate
FLOW templates must not admit it twice. `FlowRelationRef` points to stable
immutable geometry retained by its existing owner. It must not retain a
borrowed form, temporary delta or mutable old store snapshot.

K6 remains: an ordinary FLOW premise has a FlowTree; an ordinary marked
premise has a TaintTree. Do not erase the mark from InitialAp equality or
put a TaintTree under a FLOW key. The compact representation has an exact
decoder through its owning ApManager. Foreign/native adapters decode to
the existing typed values unless they have the same proved interface.

At method points, keep current marked membership for CM/rules even when
transport geometry is shared. At summary owners, removed plain parts need
no retained marked membership archive. A fresh protected offer is sufficient
to restore a residual. The history in the Lean model is proof data only.

## 6. Admission, publication and late arrival

```kotlin
fun offerMarked(at: Address, offered: MarkedOffer) {
    val delta = localProgress.admit(at, offered)
    enqueueOriginalMarkedEvaluation(at, delta) // same interpreter stages/observers
    val residual = removeProvedFlowCoverage(offered)
    storeBackedOrExplicit(residual)
    attachCertifiedTransport(delta, residual) // exact mask or scalar fallback
}

fun offerSummary(offered: SummaryOffer) {
    runRequiredProducerEffects(offered)        // including actual static supplies
    val residual = removeProvedFlowCoverage(offered)
    val fresh = summaries.admit(residual)
    publish(fresh)
}

fun offerFlow(delta: FlowOffer) {
    admitAndPublishFlow(delta)
    compactNowCoveredPlainParts(delta)        // raw, selected, publication owners
}
```

Each boundary must execute required mark-dependent effects before it removes
duplicate transport. Do not treat all rule interpretation as repeatable
after pruning. Preserve existing producer and observation identities.
Method-point admission schedules the original interpreter stages; it does
not execute a sink, rule or cleaner early. The queued evaluation still
includes covered fresh marked memberships and protection-only updates.

FLOW-first is not required for correctness. If TAINT arrives first, store
it, then compact after FLOW arrives. This migration is not fresh semantic
work. Do not replay old reports or rule actions. Expose a genuinely new
NORMAL FLOW proof through the existing normal publication path.

A subscription must see either current FLOW coverage or the required
concrete residual in every arrival order. Normalize raw summaries,
selected demands and publication indexes. Removing only an actor-local
copy does not remove caller candidates. An already queued immutable scalar
item can finish once; it must not recreate a removed unprotected payload.
Future reads use normalized state. No retraction of an emitted report is
required.

For certified neutral transfers, apply geometry once to an exact fresh mask.
Do not construct k full scalar trees and then classify them. At a source,
cleaner, CM, filter, ND join, call stage, static operation or observer,
use a proved batch adapter or the exact scalar decoder. The shared mark
mask does not authorize skipping mark-dependent evaluation.

Summary application also has non-AP effects. Match complete call-stage and
identity/alias behavior, or keep a residual. In particular, the current
TAINT no-memory-effect test can ignore a tail kind which the FLOW test
keeps. Equal AP pairs alone do not prove equality of those classifications.
This proposal does not change `hasNoMemoryEffect`. Unsupported identity
cells use the fallback. The selected ANY/ANY cell with different input and
output bases has the same nonidentity classification. For a same-base output,
the TAINT path must differ from the initial path. Both cells then have a
memory effect. A TAINT output at the initial path has no memory effect, while
the ANY FLOW output has one under the current classifier. Keep that identity
output as a marked residual. Apply this test per output path, including when
other outputs in the same tree are eligible. The AP coverage and application
proofs already allow equal input and output bases; the proof dossier also
checks this identity-class gate.

## 7. FLOW priority

Keep the current ZERO/control phase policy. Within work which is permitted
in the current **nonzero** phase, use this priority:

```kotlin
fun removeNonzero(): Work? =
    flowUnchanged.removeOrNull() ?:
    flowChanged.removeOrNull() ?:
    taintUnchanged.removeOrNull() ?:
    taintChanged.removeOrNull()
```

Use both changed and unchanged FLOW lanes. A TAINT unchanged burst must
not bypass pending changed FLOW. Preserve the repeat-set lifetime across
the combined unchanged burst; do not clear it merely because one partition
is empty. The repeat key must distinguish an unpropagated protection
upgrade from an ordinary duplicate. Packing, splitting or migrating a row
does not reset its progress.

There is no global FLOW barrier. TAINT can create FLOW later. Continue to
obey actor quantum and cancellation. All ready masks, rule/alias/call
continuations, publications and protection updates count as work. Request
and static commits use the existing barrier only after these lanes drain.
Standing subscriptions are not work. This rule does not add a pending-memory
threshold or a new commit policy.

For a fixed logical key, ordinary membership is admitted once and protection
can grow once. Repeated protected delivery creates no new delta. Thus the
new flag does not create an unbounded cycle on the same key. This is not
a proof of whole-project termination with an unbounded key domain.

## 8. Run-2 and later runs

Use original [AP sections 6 and 9](ap.md), including its whole-premise
restriction gate and normal record rules. Do not use general StrongQueries
admission, starts from arbitrary current marked inputs, or an unrestricted
response permission to justify this optimization.

At the completed run-1 handoff:

```text
covered plain concrete part:  retain FLOW demand or NORMAL FLOW record
protected concrete part:     retain ordinary FULL marked demand
uncovered/cross-mark part:   retain original ordinary FULL marked demand
geometry-only compressed:   decode original marked demand
```

A DEMAND FLOW remains DEMAND. Its reverse guide has an abstract mark.
Original AP emission starts that guide's FLOW form. A concrete caller
requirement can instantiate a returned FLOW summary. It does not need a
separate concrete callee query for pure mark-preserving transport.

Why can its marked guide disappear? An unprotected diagonal derivation
contains no concrete generation or surviving selected cleaner on its
dependency path. Same-T assignment would protect it; restoring T after
another mark would protect it locally or at a call. Protection in any
contributing derivation would survive OR merge. The constructive extractor
in the proof dossier returns the remaining transport recipe. The existing
FLOW guide and records can replay this recipe with the original AP gates.

In contrast, T-to-U source generation is not mark-preserving and remains.
Same-T generation and surviving selected-T cleanup are protected. Their
concrete guides make the marked backward analysis available. Sinks retain
their concrete seeds. Original executable rules remain in later runs; no
source rule is deleted on the basis of coarse run-1 coverage.

For each supported later witness, replace only its removed pure transport
segments. Keep its generation, cleaner-dependent, source, sink, ZERO and
call binding boundaries. Original AP C2 constructs each demand-selected
entry; C5 keeps each requested summary pair and its layer. No new start or
publication permission is needed. Recursive finite witnesses use induction
on their finite derivation trees, not a bounded call-depth assumption.
The proof is relative to the original supported AP/static/source contracts;
it does not repair their separately documented unsupported cases.

NORMAL FLOW coverage uses the existing normal record and its reverse in
place of a marked demand. Do not drop that record, its applicable/inside
tests, or must-record demotion. Caller DEMAND remains DEMAND when a NORMAL
summary is applied.

At the handoff, remove only the protection annotation. Retain the protected
relation's FULL marked guide. Later runs need no new mark identity. Existing
static-specific query completion remains within its selected named-field /
EXACT-marker scope; it is not a general fallback for nonstatic T queries.

## 9. Principal examples and edge cases

### 9.1 Pure transport with an ANY image

```java
Object get(Object p) { return p.f; }
```

```text
FLOW:      I(p,*,*) -> ret/[any]/*, DEMAND
Marked:    I(p,*,T) -> ret/[any]/T, DEMAND, plain
Before:    store/publish both; reverse both as guidance
After:     keep FLOW; CM(ret,T) still gets real marked arrivals;
           backward ret/T uses the FLOW guide and instantiates p/T
```

This broad relation is the canonical run-1 image, not a new ANY initial.
For `return p`, the usual NORMAL STAR result has a different correlation
from the broad marked ANY result. Share its geometry, keep the marked guide
unless an additional cell proves replacement.

### 9.2 A field-sensitive same-T source

```java
Object x = p.right;
// rule: CM(p.left,T) -> assign T to x
return spread(x);
```

```text
coarse FLOW: p.*/* -> ret/[any]/*
rule path:   p.*/T -> x/T -> ret/[any]/T, protected
```

The rule is triggered by T and assigns T. The marked guide remains even
though another coarse FLOW image covers its output. Run-2 can distinguish
p.left from p.right. No CM-definiteness metadata is needed.

### 9.3 Cross-mark generation and cycles

```java
// rule A: CM(p,T) -> assign U to x
// rule B: CM(x,U) -> assign T to result
```

T-to-U is cross-mark and stays. Restoring T protects T-to-T even though
the second triggering mark is U. The same test applies when rule B is a
callee summary. A protected copy merged with a plain branch protects the
whole identical output member.

### 9.4 Cleaner residual hidden by another branch

```java
if (b) { x = p.left; removeTBelow(x); }
else   { x = p.right; }
return spread(x);
```

The cleaner excludes T from the left FLOW path, but can keep exact root T.
The right FLOW/ANY output can cover that marked output after the merge.
The surviving selected-T result is an assign-back and is protected. Its
marked demand therefore remains. A complete selected-T kill has no result
to protect. This case is checked with the original cleaner in Lean.

### 9.5 Static writes and supplies

```java
void put(Object p) { C.f = p; }
Object make() { return sourceT(); }
void main() { put(make()); consume(C.f); }
```

If `p.*/* -> C.f/[any]/*, DEMAND` covers a plain diagonal
`p.*/T -> C.f/[any]/T`, use the same test as for nonstatics. Keep required
local writer registration and actual computed T supply before pruning.
FLOW itself must not supply T. `ZERO -> C.f/T` has a different origin and
is retained. `S.* -> S.*` is not a proof of the ANY relation. Already erased
static/static summaries remain erased; this optimization does not restore
their propagation or register call-created write points.

### 9.6 Partial coverage and late protection

```text
offer T row:       {x/T plain, y/T plain, z/T protected}
FLOW covers x,z:   keep {y/T plain, z/T protected}; remove x/T transport
late protected x: restore x/T and its ordinary T demand; propagate flag once
```

The same final normalized state results when FLOW or protection arrives
first. Separate normal/exceptional endpoints, caller contexts, EXACT/MUST
tags and mark exclusions are never merged by this operation.

## 10. Expected savings and implementation gates

The [latest local snapshot report](../docs/reports/bidirectional-thingsboard-flow-taint-coverage-20261024.md)
finds 10,631 covered output memberships among 11,752 in eight selected
summary stress stores, before protection. Only 36 of 1,157 concrete rows
are wholly covered; 887 are partly covered. This requires leaf-level
pruning. The sample is biased and has no protection flags. It is not a
whole-project deletion percentage or a speedup prediction. Latest measured
iteration remains **run-1 OOM**.

A row here is one method's concrete initial/premise group, not one output
edge. One row can contain a return output and many static-field outputs:

```text
before: I(p,T) -> {ret/T, C.f/T, C.g/T, C.h/T}
FLOW covers the three static outputs but not ret/T
after:  I(p,T) -> {ret/T}                // one partly covered row remains
```

| Sampled concrete rows | Meaning before non-subsumable flags |
| --- | --- |
| 36 wholly covered | Every output membership passes the coverage test; candidate to remove the whole row |
| 887 partly covered | Remove covered output memberships; keep each row's remaining outputs |
| 234 not covered | No output membership passes that test |

Those 1,157 rows hold 11,752 output memberships. Removing the 10,631
candidates would leave 1,121 memberships before flags. The count of retained
premise keys can therefore remain large while output payload/transport falls
sharply. These measurements used equal paths; they do not measure the extra
prefix-containment candidates added by this clarification.

We expect less retained output geometry and less summary publication/caller
application work if many candidates remain unprotected. FLOW priority should
let the engine omit such work before publication. Partial row pruning alone
does not remove all premise-key lookups or their mark-matching cost. Actual
static supplies and local rule checks also remain required. The snapshot
does not measure the protected fraction or establish a two-times engine
improvement, successful run-1 completion, or resolution of the OOM.

For one eligible geometry used by k marks, exact backing uses one geometry
and a mask instead of k geometry containers. Certified neutral transfer
uses one geometry application instead of k. Semantic replacement also
removes the eligible concrete summary publication and caller candidate.
Mark masks, required observations, protected/cross-mark residuals and
unsupported tails remain costs. No two-times engine result is established.

Implement in this order, with each step reviewable:

1. Add protection masks and metadata-only deltas. Test triggering-conclusion
   assignment, local/call cycles, cleaner residuals, both merge orders,
   protected EXACT inside plain ANY, rule-binding upgrades and callee-origin
   ownership.
2. Add exact compact rows and scalar decoder. Differentially compare all
   marks, paths, kinds, layers, requests and original keys, including empty
   masks, partial leaves, cross-mark residuals and primitive filters.
3. Add the proved ANY/ANY coverage cell at all summary/publication owners.
   Test Taint-before-FLOW, late protection, late NORMAL, old/new subscriptions,
   original AP C2/C5 admission with general StrongQueries disabled, and
   static producer-before-prune order. Unsupported cells must stay scalar
   or geometry-only.
4. Add certified neutral batched transfers and FLOW priority. Test both
   changed/unchanged lanes, ZERO phases, protection-only work, barrier drain,
   actor quantum, cancellation and continuation addresses.
5. Compare completed logical rule/source/sink observations and later supported
   witnesses with the reference. Packet callback counts can vary. Do not
   change ordinary equality/hash or occurrence identities.
6. Measure Thingsboard FULL run-1 with the same flags, heap and timeout.
   Report latest reached/COMPLETE/accepted iteration, engine time, protected
   fraction, residual memberships, published candidates, AP geometry
   applications, static supplies, heap/GC and outcome. Keep an OOM or timeout
   censored. Do not extrapolate a completed time from it.

The checked models establish the concept and the local optimization laws.
The runtime adapter tests above remain implementation gates. They do not
authorize a field, source, static or query-policy redesign to make a test pass.
