# Reuse FLOW relations for concrete FULL marks in run-1

Date: 24 October 2026. Status: **section 3 specified; remaining proposals unselected**.
Measured runtime: `40e20d16f03ab046df75a53a489bb331b065a9c1`.
Clarification: prefer FLOW coverage over independent concrete-mark transport.
The design uses the original demand-driven AP emission/restriction, without
StrongQueries. The latest [Thingsboard run-1 comparison](../reports/bidirectional-thingsboard-flow-taint-coverage-20261024.md)
measures ANY/ANY overlap. Same-mark generation and mark cycles use the
selected non-subsumable annotation in section 3.7; no CM definiteness test
is required.
The [complete FLOW-backed specification](../../spec/run1-flow-backed-concrete-relations.md)
and [proof dossier](../../spec/run1-flow-backed-concrete-relations-proofs.md)
supersede section 3. They include triggering-conclusion assignment protection,
cleaner assign-back, local and call cycle protection, and original AP handoff
witnesses. The analyzer implementation remains unchanged.
All fixed-project commands, profile scopes and six required OOM owner
scopes are closed. This proposal uses the corrected candidate measurements.
It changes no analyzer code. Read the
[performance report](../reports/bidirectional-rule-selection-performance-20261024.md).

The target is a complete run-1 engine in 60 seconds. Prescan and report
barriers are outside that target. Prior proposals are historical inputs.

## 1. What remains after rule reduction

| Project | Corrected run-1 engine | Latest reached / COMPLETE / accepted |
| --- | ---: | --- |
| Thingsboard | 197.026 s, OOM including 29.620 s heap capture | run-1 / none / none |
| Conductor | 13.640 s, COMPLETE | run-2 OOM / run-1 / run-1 |
| PDF | 25.269 s, COMPLETE | run-2 OOM / run-1 / run-1 |
| OWASP | 84.465 s, COMPLETE | run-11 COMPLETE / run-11 / run-11 |

The current Thingsboard heap has 1,687 global initial descriptors, but
6.7 million ConclusionGroups and 12.2 million TaintTrees across owners.
A small initial vocabulary does not imply few retained method/point/origin
relations. Current processing repeats the same geometry under many scalar
initial marks. Final TaintTree packing cannot cross those initial keys.

The exact MethodEdgeStore retained union is 2.558 GB. CalleeSubscriptions
retain 0.920 GB; the broader summaries/subscriptions union is 2.405 GB.
These overlap and are not an additive saving budget. Inside MethodEdgeStore,
disjoint shallow HashMap, ArrayList and Object-array classes use 1.131 GB
(44.21% of that one retained set). Removing repeated whole relation rows
can avoid their containers and payloads together. Small-container tuning
alone is not the selected proposal.

The current static service/point union is 0.485 GB, versus 0.877 GB at the
reference OOM. These unequal-prefix snapshots are consistent with request
reduction; they do not isolate a retained-byte saving. Only 1,126 global writer rows remain on the
reference. Writer factoring is not the large current lever. In the current
last 30 seconds before heap capture, GC pauses occupy 24.370 seconds. The
MemoryManager policy is inherited. Retained-state reduction must come first.

### Complete current input-axis census

Method stores have 875,915 premise rows: 793,890 concrete (90.64%),
81,244 FLOW and 781 ZERO. Concrete rows use 21,558,635 of 25,251,733
statement slots (85.37%). Within each method, erasing only the initial mark
gives 48,254 complete input geometries: 16.45 marks per geometry on average.
There are 33,851 width-18 families and 4,987 width-28 families. In all,
786,885 concrete rows belong to families of width at least two.

Concrete origins are 268,373 ARG, 332,820 STATIC and 192,697 THIS. This is
not only static handling. Static origins can appear on ordinary local
facts after a static read; they are different from propagating facts with
static bases. ZERO is not the dominant stored-input family.

The 745,636 potentially repeated input rows are only an input-header upper
bound. It does not establish identical output relations or saved operations.
The complete key retains manager, base, path, tail and field exclusion.
Only the mark axis is removed for this census.

### Complete output check within a bounded stress cohort

The current probe selects eight high-width stores with at most 64 statements:
1,735 premise arrays, 62,165 possible slots and 9,996 occupied cells. It
fully decodes 15,631 TAINT headers and 5,417 trie nodes, with zero unknowns.

Of 9,584 concrete cells, 9,548 have exact whole-image T-to-T relations.
Those images form 420 cohorts after aligned input/output mark substitution,
with up to 28 marks per cohort. The other 36 concrete cells have nonidentity
marks; 412 cells are FLOW. The decoder retains every output base, field,
leaf exact/any kind, layer, tail, exclusion, full mark and original premise.

This proves a local snapshot opportunity of 22.73 times fewer image rows,
with all member marks retained. It does not prove global eligibility, bytes
saved, eliminated historical operations or an engine-time gain. The cohort
is deliberately biased toward high-width stores. Equal current images do
not certify that a future type filter, guard or primitive rule is mark-blind.

A separate historical reference probe tests a different idea: sharing an
exact current caller Facts image after erasing only its caller premise.
It finds 1,867 duplicate component images among 20,261 entries in four large
directories (9.21%, maximum width five). Pointer-unequal structural matches
are unknown. This is weaker evidence for generic exact-image join factoring.
It keeps the current full mark, so it does not measure aligned mark-relation
batching in caller storage and cannot bound that adapter's opportunity.

## 2. Ranked choices and evidence gate

| Rank | Proposal | Current → new | Expected impact and limit |
| --- | --- | --- | --- |
| 1 | Subtract covered concrete summary effects; share residual geometry; process FLOW first | Repeat marked summary outputs → keep the covering FLOW and only uncovered marked residuals; use exact masks for residual geometry | The biased eight-method sample has local FLOW/ANY coverage for 10,631 of 11,752 marked summary memberships. This is not a global saving estimate or a completed handoff proof. |
| 2 | Keep execution facts only at required boundaries of plain linear regions | Store changed/touched intermediate values and enqueue per-statement work → apply the same plain steps locally and store boundary results | Can remove actual intermediate admissions and queue operations. Unchanged emission already bypasses MethodEdgeStore. Required boundary coverage and the eligible retained fraction are not measured yet. |

These are algorithmic work-removal proposals. Neither has a measured
two-times whole-engine result yet. Do not infer that result from the global
mark-family sizes or from 97 million form accesses. The second choice also
affects some state targeted by the first choice, so their byte savings cannot
be added. Current input weights and the bounded output probe support rank 1. A global
output/operation estimate remains a separate gate. Prioritize rank 1; rank 2
needs its own eligible-point measurement before selection.

Do not select a MemoryManager rewrite, IR storage change, new mark-eligibility
filter, or another static writer index from these measurements. The slow
Thingsboard tail is inherited full-GC pressure. Reduce the admitted state
which causes that pressure.

## 3. Concrete relations backed by FLOW

### 3.1 The three storage cases

The primary optimization is to reuse an existing FLOW relation. A DEMAND
FLOW/ANY relation can also subsume a same-mark DEMAND TAINT/ANY relation;
coverage is not limited to NORMAL FLOW. Batching
equal TAINT relations is a second step. `TaintTree` already packs conclusion
marks, but scalar marked premises still duplicate geometry and its containers.

| Corresponding FLOW | Concrete relation | Retained representation |
| --- | --- | --- |
| NORMAL or DEMAND, with proved summary coverage and handoff replacement | Represented by the mark-preserving FLOW relation and its normal record or demand | No separate TAINT summary or T demand. Required marked intraprocedural observations still run. |
| NORMAL or DEMAND, with reusable geometry but without the proof above | Keeps its original TAINT annotations and any required marked demand | FLOW reference plus an exact FULL mark set and the original TAINT header; no duplicate geometry. |
| No corresponding reusable FLOW geometry | Cannot use a FLOW reference | Explicit TAINT relation. Equal residual relations can still share geometry and an exact mark set. |

Apply this classification per covered part, not only per whole tree. If FLOW
covers one output leaf or some marks, retain the remainder in compact or
explicit form. A DEMAND FLOW edge cannot replace a NORMAL TAINT proof.
In the measured eight-method summary scope, 887 of 1,157 marked premise rows
are partly covered and only 36 are wholly covered. Whole-tree tests are
insufficient.

**Proposed semantic amendment to the previous proposal:** the current core
forces every run-1 `TaintTree` to DEMAND. The new design permits a concrete
relation to use the NORMAL status that its corresponding NORMAL FLOW
relation already proves. It then needs no independent marked demand. This
is a coverage rule, not a blanket removal of `forceRun1Layer`. Static-origin
relations stay DEMAND. Field cuts, field writes, source actions and cleaners
retain their existing semantics.

A NORMAL summary does not make a DEMAND caller input NORMAL. Summary
application still combines the input layer and the summary layer as today.
Nor does FLOW establish that a particular mark is available: a real marked
input or the existing request/supply mechanism must establish that fact.
DEMAND/ANY subsumption needs no NORMAL strengthening. Its covering FLOW
remains DEMAND. Omitting a covered T demand requires the original AP handoff
proof described below; it is not justified by StrongQueries.

### 3.2 Subsumption and geometry sharing are different tests

For a FLOW relation `F`, let `lift(F, T)` be its mark-preserving concrete
relation for FULL mark `T`, using the existing AP semantics. A concrete
relation `E(T)` is covered only when every input/output pair of `E(T)` is
in `lift(F, T)`, with sufficient layer strength. NORMAL coverage also
requires that the lift is NORMAL for the relevant concrete input.

```text
I(p, STAR, *) -> q/ANY/(* minus X), DEMAND
I(p, STAR, T) -> q/ANY/T,           DEMAND
T not in X: local pair inclusion holds across these initial keys.
```

The new [local Lean model](../../spec/lean/ApSpec/Run1FlowTaintCoverage.lean)
proves this inclusion in the existing AP denotation. It does not by itself
prove that every marked rule dependency can disappear from the next run.

This is cross-premise semantic coverage. It is not the existing same-premise
`ConclusionGroup` subsumption test. Compare the same method/context and
point or summary endpoint. Keep original input/output path correlation,
tails, exact/MUST leaves, field exclusions and mark exclusions. `F` must
admit `T`. Preserve canonical initial identities and all contributing origins.
An excluded mark, a mark-changing action or a different origin is not
covered merely because the bases and field chains agree.

```text
FLOW:          p.*/* -> x.*/*, NORMAL
Valid instance: p.q/T -> x.q/T, NORMAL       // same suffix q

Not an instance: p.left/T -> x.right/T       // suffix changed
```

In particular, the current broad initial `I(p,*,T)` can produce
`x/[any]/T DEMAND`. Equal unmarked base/path names alone do not prove that
this broad relation is covered by `p.* -> x.* NORMAL`. Do not relabel its
`[any]` leaf as NORMAL or replace it with a MUST leaf. Keep its marked demand
if the AP coverage test cannot prove coverage. The proof must account for
the canonical run-1 marked-initial grammar; it must not assume a new exact
initial shape. The notation above describes relation instances, not new
run-1 initial facts.

This does **not** require storing that TAINT geometry in full. For storage,
the FLOW input/output geometry can serve as an immutable template while a
small TAINT header preserves the different tails and layer:

```text
F0 = I(p,*,*) -> x.*/*, NORMAL
row = (F0, marks={T,U}, original TAINT header=DEMAND/[any])
decode(row) = { I(p,*,T) -> x/[any]/T DEMAND,
                I(p,*,U) -> x/[any]/U DEMAND }
```

The original premise tail/exclusion and per-leaf exact/any annotations must
also be recoverable. Share only geometry that agrees exactly; split the row
or leave a residual when required. This compression does not use the FLOW
layer as a TAINT proof and does not authorize reusing a mark-dependent
transfer result. Thus even a NORMAL FLOW template can back a compact TAINT
DEMAND row when semantic subsumption is unavailable.

### 3.3 Storage organization

Use the same classification in method-point and summary storage. One
immutable FLOW geometry can serve many marks. A compact mark set records
membership and progress; it does not recreate a conclusion trie per mark.

```kotlin
// Contract pseudocode; keys remain scoped to the owning ApManager.
data class FlowBackedMarks(
    val flow: FlowRelationRef,  // stable, complete relation at this endpoint
    val marks: FullMarkSet,     // exact same-mark input/output membership
    val header: ConcreteHeader, // original premise, tails, layer, E and leaf tags
)

class ConcreteRelations {
    val flow: FlowRelationStore
    val backed: Map<Pair<FlowRelationRef, ConcreteHeader>, FullMarkSet>
    val explicit: ExplicitTaintStore

    fun admit(edge: ConcreteOffer) {
        val (subsumed, remaining) = flow.partitionByProvedCoverage(edge)
        val (shareable, remainder) = flow.partitionByGeometry(remaining)
        observeRequiredMarkedEffects(edge) // before removing redundant transport
        recordCoveredEffects(subsumed)     // no duplicate summary or T demand
        admitBackedMarks(shareable)       // preserve its original TAINT header
        explicit.admit(remainder)         // existing merge/delta laws
    }
}
```

`partitionByProvedCoverage` needs an executable semantic/handoff witness for each
accepted part. `partitionByGeometry` needs an exact reconstruction witness,
not a NORMAL proof. Decoding a compact row must recover its complete old
relation, including the original marked premise. If the reference and small
header cannot recover a tail or annotation, that part remains explicit.
Do not retain a second complete tree inside `ConcreteHeader`. For NORMAL
coverage, the FLOW relation itself supplies the transfer; do not enumerate
every possible mark into a summary-side membership set. Intraprocedural mark
progress is still required where actual marked arrivals can cause rule work.

The proof witnesses do not require retained derivation histories or support
labels on runtime edges.

Use one authoritative delta admission across compact and explicit values.
Several possible FLOW references must not admit the same concrete member
several times. Preserve the existing annotation-change and subsumption delta
laws, not only set subtraction on mark masks. Moving an existing member
between representations must not make it new work.

`FlowRelationRef` points to an immutable, retained relation, not a borrowed
form, transient delta or mutable store row. Its owner remains the existing
method actor or summary storage. Publishing to another owner uses immutable
values and the existing subscription protocol. No global dependency graph
or new request store is required by this proposal.

Keep the existing typed `InitialAp`/`Facts` invariant: do not put a TAINT
tree under a FLOW premise in `MethodEdgeStore`, or erase the mark from
`InitialAp` equality. The compact relation is a separate representation
with an exact decoder through the owning ApManager.

Within every mark set, input `T` maps to output `T`. `{T,U}` never means
`T -> U` or `U -> T`. FULL owners and primitive properties stay exact; the
mask is not a new mark token or GROUP wildcard. Partition primitive filters
exactly or use the scalar path. Keep differing images in separate rows and
split a row when only some marks gain an output. Cross-mark residuals retain
their actual input/output mark relation.

### 3.4 FLOW-first processing, with late arrivals

Prefer FLOW transport before concrete transport at the same permitted
logical phase. This makes the covering relation available before admitting
many scalar concrete summaries. It is a scheduling optimization, not a
correctness prerequisite.

```kotlin
fun chooseWithinCurrentPhase(): Work =
    flowWork.removeNextOrNull() ?: concreteWork.removeNext()

fun onFlowAdded(delta: FlowRelation) {
    publishNewFlow(delta)
    compactCoveredExplicitParts(delta) // no replay of old semantic effects
}

fun onMarkedArrival(input: MarkedInput) {
    val fresh = markedProgress.admit(input)
    if (!fresh.isEmpty()) enqueueMarkedWork(fresh)
}
```

Use this simple local priority inside the current nonzero phase: take FLOW
while it is available, then TAINT. Keep the existing actor quantum and
cancellation; do not add a global completion barrier. Preserve ZERO/control
phases and the unchanged repeat-set contract. The
policy must consider FLOW in both changed and unchanged lanes; a TAINT
unchanged burst must not always bypass pending FLOW changed work. FLOW generated by a
later concrete rule or another method can arrive after TAINT. Do not wait
for a global “all FLOW complete” barrier. Store the explicit relation first,
then compact it when coverage becomes available. Migration changes storage,
not semantic novelty; it must not re-enqueue old outputs or repeat reports.
If late NORMAL coverage replaces a demand-only representation, expose that
new stronger coverage through the normal publication protocol.
For late DEMAND coverage, preserve the FLOW demand and retire only proved
redundant T demands. Apply the relation admission law at raw summary,
selected-demand and publication owners. Removing an actor-local payload
alone leaves the published copies and future caller candidates intact.

Both old/new subscriptions must see the FLOW coverage or the residual
concrete relation regardless of arrival order. For a marked caller input,
the existing NORMAL FLOW summary must be usable without first creating a
separate marked callee summary. Validate this path explicitly.

For certified plain operations, process one geometry with a mask of fresh
marks instead of applying the same structural transfer once per mark.
Only new membership or new geometry/annotation is work. Rules, conditions,
cleaners, ND joins, static operations and observations remain evaluation
boundaries unless an exact batch adapter is proved. NORMAL FLOW coverage
removes duplicate transport/storage; it does not remove marked rule checks.
Do not construct one complete scalar edge per mark before classifying it.

`ProcessingAddress` still includes node and complete logical stage. Keep
resume site, cleaner step/phase, caller layer, identity candidate and pending
demotion separate. A packed work item owns immutable geometry and an exact
mask. All continuations remain counted work and must drain before existing
request/static commit barriers. Standing subscriptions are not queued work.

### 3.5 Examples

```java
Object pass(Object p) {
    Object x = p;
    return x;
}
```

For a real exact `p.q/T` input, `p.* -> ret.* NORMAL` already returns
`ret.q/T` with the input's layer. Before: a marked analysis can additionally
store and publish a T-specific relation. After: use the FLOW summary directly
for its covered part. A sink check on `x/T` still runs when T really arrives.
The broad synthetic initial discussed in §3.2 needs its own coverage test.

```java
Object writeThenPass(Object p) {
    p.f = clean();
    return p;
}
```

The run-1 rule moves `p.*` to DEMAND and keeps E empty when the write would
update E. It does not become a NORMAL pass. Where that DEMAND FLOW covers
T/U transport, retain one reference with `{T,U}` instead of two TAINT
geometries. Handoff still exposes the FULL T and U demands. Keep any uncovered
geometry explicit. If the complete demand-replacement proof applies, the
FLOW demand replaces the covered T/U demands too. Otherwise this is geometry
sharing only. The field-write rule itself is unchanged.

```java
Object generate() {
    return sourceT();
}
```

`ZERO -> ret/T` creates T; it is not a mark-preserving FLOW instance.
Keep the explicit source relation with its current layer policy. Likewise,
`I(p,T) -> ret/U` is not covered by a T-preserving FLOW relation. This
proposal does not change source guards, all-ZERO tests or action semantics.

### 3.6 Handoff and expected savings

Persist NORMAL FLOW summaries under the selected record contract. Keep
DEMAND FLOW as guidance. A proved covering FLOW relation can replace both
the T summary and its T demand. The covering relation need not be NORMAL.
For residuals which only share geometry, preserve the original FULL marked
demands. Do not substitute a GROUP demand.

Use original AP section 6.3 and 6.4: an abstract demand starts its FLOW form;
a caller's concrete input instantiates the returned FLOW relation. No
StrongQueries admission, actual-input fallback or unrestricted response
permission may be an assumption of the proof. Source/sink observation
obligations remain. Static query policy stays within its separately selected
scope; do not revive static-to-static propagation.

The source-dependency argument is precise for `T != U`: a conditional source
retains its original T premise and emits U. FLOW preserves the input mark,
so it cannot subsume T-to-U. Keep that dependency and the backward T path.
Sinks keep their T seeds. CM itself does not exclude T; mark-removal actions
do, and a FLOW result excluding T cannot subsume T.

The local Lean model checks a read of `p.right` plus
`CM(p.left,T) -> assign T to x`: run-1 FLOW can contain the generated image
while the rule adds a real pair absent from the read. The selected protection
rules below retain this dependency. Do not infer that a source rule may be
deleted in later runs just because its coarse run-1 output is contained in
FLOW. Keep original rule evaluation; protected demands make the necessary
marked analyses available. The new proof dossier gives constructive transport
extraction and original AP C2/C5 handoff witnesses for the selected scalar
scope. Runtime adapter correspondence remains an implementation gate;
general StrongQueries is not a proof assumption.

The latest run-1 comparison measures local same-path FLOW/ANY coverage:
18,869 of 29,151 method-point memberships and 10,631 of 11,752 summary
memberships in the same eight stress stores. It also separates STAR-only
residuals. These are snapshot measurements, not a global savings estimate
or a certificate for future-rule redundancy.

### 3.7 Non-subsumable concrete conclusions

Use one annotation per logical output leaf/mark. This annotation belongs to
the edge, not to the global mark T. It changes FLOW-subsumption eligibility,
not CM truth, the FULL identity, the layer or the field geometry. No CM
definiteness check, grounding history, new rule-provider mark or MarkTable
entry is needed.

The selected rules are:

1. A rule assigns T and its accepted triggering conclusion has mark T:
   the T conclusion is non-subsumable. Apply this to every concrete-mark
   generating rule action, including source, conjunction and end-fact paths
   where that origin is retained. A surviving selected-T cleaner result is
   an assign-back of T and is protected too. Other bases, unselected marks
   and complete kills keep their original behavior. A plain `* -> *`
   transfer is not an assignment of T.
2. A summary has a non-subsumable conclusion: its application produces a
   non-subsumable conclusion. Ordinary transport also preserves protection
   already present on its input.
3. Composing `T -> U` with `U -> T`, for `U != T`, produces
   non-subsumable `T -> T`. Apply this to local rule composition and summary
   application. Compare with the original premise mark in this cycle test;
   the assignment test above uses the triggering conclusion.
4. Identical edges merge by OR on this annotation. A non-subsumable copy
   dominates a subsumable copy, in either arrival order.

```kotlin
fun onRuleAssignment(
    origin: FullMark?, triggering: FullMark, assigned: FullMark, old: Boolean,
): Boolean = old || triggering == assigned ||
    (origin == assigned && triggering != assigned)

fun onSummaryApplication(
    origin: FullMark?, incoming: FullMark, outgoing: FullMark,
    inputProtected: Boolean, summaryProtected: Boolean,
): Boolean = inputProtected || summaryProtected ||
    (origin == outgoing && incoming != outgoing)

fun canRemoveT(edge: MarkedLeaf, flow: FlowRelation): Boolean =
    !edge.nonSubsumable && flow.coversMarkedRelation(edge)

fun mergeSameLeaf(old: MarkedLeaf, offered: MarkedLeaf): MarkedLeaf =
    old.copy(nonSubsumable = old.nonSubsumable || offered.nonSubsumable)
```

For packed output marks, store the protected subset of each leaf's mark set.
Its members must remain in the full set. Preserve membership-specific
protection when splitting or merging masks; one protected T must not protect
unrelated U. Keep the annotation through assignments, alias effects, cuts,
calls and static summaries. A real kill removes the killed membership and
its annotation. Projection/packing cannot clear surviving protection.

Protection-only growth is a delta, even if the ordinary T fact already
exists. It must reach successors, summaries, publication storage and the
handoff barrier. If the old unprotected copy was already subsumed, a later
protected copy must recreate the required marked residual and demand.
Flag-only work must not create a second ordinary report/source/sink identity.
The ordinary observation key remains unchanged; its metadata gains protection.
The annotation grows only from false to true, so identical repeat delivery
does not create an endless work cycle.

The handoff keeps protected T as an ordinary FULL marked demand. Later runs
need no special mark identity or StrongQueries rule to read it. The selected
static query adapters remain separately scoped. Static T relations use the
same coverage/protection rule: there is no general static exemption. Actual
pool supply effects must still execute before redundant transport is removed.

Current heap measurements do not contain this annotation. The 90.46% local
summary overlap is a candidate count before protection, not the final number
of deletable outputs. Measure the protected fraction before predicting a
project-wide saving.

For one eligible relation used by k marks, the target is one geometry and
an exact mask instead of k premise/conclusion containers. NORMAL coverage
also removes separate concrete summary publication and subscription work.
DEMAND coverage retains mark membership but shares geometry and certified
plain transfer work. Without FLOW, exact same-mark batching remains possible;
unsupported residuals use the scalar store. Mask cost still grows with its
representation, and mark-dependent boundaries still perform required work.

For an eligible operation fraction f of average width k, ideal shape-work
reduction is `1 / (1 - f + f/k)`. This is not a measured engine speedup.
Count eliminated geometry applications, stored cells and joins rather than
only wider packets. No whole-project two-times result is established yet.

## 4. Plain linear regions

### Current and new behavior

```java
void copy(Object p) {
    this.left = p;
    this.right = p;
    this.extra = p;
}
```

For `I(p,*,T)`, each assignment creates a field relation. With the current
LIFO queue, a new `this.left/T` delta can walk the following writes before
the p delta creates the right/extra relations. Each walk performs form,
queue and store work. The store can pack fields after they arrive, while
the worklist still processes separate packets.

The proposed engine enters a certified plain region once for the current
batch, applies the same transfers in CFG order, and retains the required
boundary relation. It does not keep every intermediate point value merely
to feed a single known successor. Field writes keep their existing rules:
an exclusion update moves the edge to DEMAND with empty E, an overwritten
exact field is killed, and a disjoint field passes unchanged. No field
information is replaced by `[any]` as a scheduling optimization.

```text
Before: node1 admission -> queue -> step1 -> node2 admission -> queue
        -> step2 -> node3 admission -> queue -> step3 -> boundary admission

After:  region-entry admission -> step1 -> step2 -> step3
        -> boundary admission
```

The steps remain. The intermediate durable store cells and queue protocol
are avoided. A stronger AP composition can be considered later; it is not
part of this first proposal.
Current untouched emission already skips MethodEdgeStore, so those events
can contribute queue savings but not another store-cell saving.

Do not defer the existing cut to the region exit. For a valid FLOW input
`I(p,*,*) -> p.* NORMAL`, the code `p.f = clean; return p.f` moves the root
to DEMAND with empty E at the write. Keeping an intermediate `{f}` exclusion
until the region ends can instead kill the read and lose guidance. The new
region must execute the old layer/exclusion decision before the read.

### Required boundaries

Keep entries, exits, joins, loop boundaries and every possible direct resume
point. Calls, source/sink checks, predicates, cleaner continuations, static
operations, exceptional control flow and unknown callbacks are boundaries
until the adapter proves otherwise. A one-predecessor/one-successor test
alone is insufficient. The selected executable and metadata forms determine
effects; raw JVM syntax alone cannot prove a node plain.
Likewise, base-not-touched is not sufficient: FormApplier's untouched branch
still invokes reached, conjunction and source hooks.
Every SCC, including a non-returning one, needs a deduplicated boundary.
For example, fusing `while (true) { x = x; }` into an internal loop must not
turn finite solver saturation into endless region execution. Keep the
existing repeat suppression and cancellation semantics.

MethodEdgeStore's current runtime consumers use admission; `edgesAt` is
used by tests in the inspected source. Before implementation, verify all
production consumers again, including trace and debug adapters. Preserve a
constructive expansion path for any semantic observer of an internal point.
Do not silently remove a future trace/proof requirement.

## 5. Semantic scope and required proofs

The proposed changes are FLOW-first scheduling, cross-premise summary
subtraction and replacement of proved redundant marked demands. Today the
stores keep FLOW and TAINT under separate initial keys. The new representation
can omit an effect supplied by the covering FLOW, including DEMAND/ANY FLOW.
It keeps residual geometry/marks and the covering layer. The NORMAL-covered
case may also use the existing NORMAL proof instead of a forced marked
DEMAND, but replacing DEMAND by NORMAL on path similarity is outside scope.

FULL stays the default. Keep initial grammar, field limits, primitive rules,
field updates/exclusions, all origins, exact all-ZERO admission, selected
conditions/actions, static-pool transitions, controllers and exit rules.
Later runs use the original AP demand-driven emission and restriction,
without StrongQueries. Their guidance can omit only unprotected concrete
relations whose replacement has the required original-AP proof. Rule
conditions and actions remain in the program; no new later-run rule deletion
is part of this design. The new annotation prevents the same-mark dependency
loss without changing field processing or testing CM definiteness.
Plain-region execution is still an exact optimization, without an additional
layer or field-transfer change.
Do not put transfer-support state into MethodEdgeStore or revive
GroundingSupport. Compiler labels must not alter configuration equality.

Follow the [proof guide](../../spec/proof-guide.md) before implementation.
The constructive models must provide executable decoders and witnesses:

1. Construct the mark-preserving FLOW lift from the existing AP operations.
   The coverage witness preserves input/output suffix correlation and the
   canonical marked-initial grammar. It admits only marks allowed by FLOW
   exclusions, and cannot create mark availability or strengthen a DEMAND
   input. Include RED controls for `p.left/T -> x.right/T`, broad MAY versus
   correlated STAR, excluded T, different origins and mark-changing GEN.
2. Geometry-backed decoding and explicit residuals preserve the complete
   concrete relation. NORMAL-covered parts are supplied by NORMAL FLOW.
   The combined representation preserves semantic coverage and observation
   identity, not necessarily the raw old list of redundant TAINT demands.
   It never creates cross-mark pairs or combines origins into an ND edge.
3. Every certified plain operation commutes with decoding/coverage,
   including kills, layer changes, exact/any tails and primitive filters.
   A FLOW-covered marked arrival still triggers required rule evaluation.
4. FLOW-first and mixed compact/scalar admission reach the same finite
   semantic closure regardless of arrival order. Test FLOW-before-TAINT,
   TAINT-before-FLOW, late NORMAL coverage, recursive calls and late
   subscribers. Migration must not replay old observations. Fair batching
   must not hide pending work from global termination. Masks,
   decoded members and region continuations remain in counted fact work,
   cancellation, quantum and zero-phase accounting. They must drain before
   the existing request/static commit barriers, not only before the final
   termination check. Stored current masks and standing unanswered
   subscriptions are not queued work and must not keep a completed solver
   alive.
5. At each rule/observation boundary, preserve complete binding identities,
   all contributing origins and the all-ZERO cube test. Preserve source,
   sink and report occurrence identity; callback counters are separate.
6. A linear-region step expands to an executable old step sequence. Every
   external resume and observable point has a retained boundary or an exact
   replay witness. Preserve exceptional and non-returning paths.
7. For every retired marked demand, construct its original-AP replacement:
   a permitted NORMAL record or a retained FLOW demand, its FLOW-form
   emission, restricted callee response and ordinary marked caller
   application. Equal concrete starts are not required, but every required
   observation and source-hit path must survive. Prove T-to-U preservation,
   same-mark assignment protection, summary inheritance, cycle protection
   and protected-duplicate dominance. Include protection-only deltas and
   late reappearance after earlier subsumption. No
   StrongQueries premise or unproved future-query completion is allowed.
   All remaining FULL marked demands decode exactly.
8. Prove reduced operation counts for explicit finite eligible workloads.
   State the scope and bitset cost. Do not claim a whole-project 2x bound.

These are proof obligations, not completed Lean claims. If a proof requires
a changed field, source, cleaner, static or exit contract, stop and specify
that major change before implementation. An approximation is not an exact
batch adapter.

## 6. Implementation and acceptance plan

The corrected measurements are sealed. Add a representative, weighted
coverage census at method points and summary endpoints: NORMAL semantic
coverage, geometry sharing with NORMAL/DEMAND templates, and explicit
residuals. Report covered leaves/mark memberships, retained geometry and
operation counts separately. Preserve tails, exclusions, layers and origin
correlation during the census. A match
after erasing only the mark is not a coverage result. Measure the share at
certified plain points separately for rank 2. A top-store sample is not a
global saving estimate. Reject a proposal whose eligible share is small.

Then build the constructive model and RED controls. Cover same-mark versus
cross-mark pairs; full mark owners; primitive/nonprimitive filters; ZERO;
field overwrite/disjoint/prefix cases; NORMAL/DEMAND; late point resumes;
recursive calls; conditional sources; cleaners; ND origins; and marked
run-2 guidance. Compare decoded logical relations and observation multisets.

Implement one adapter at a time behind a run-1 gate: coverage classification
and residual admission, compact method-point rows, summary query/publication,
then FLOW-first scheduling and certified mask transfers. Scheduling alone
must not be needed for correctness. Keep the old path for unsupported cases.
Measure shape applications, queue items, retained cells, marked publications,
joins, decoded scalar boundaries and peak bytes. Do not count a wider packet
as less work if its implementation still repeats every old operation.

Finally repeat the fixed FULL/statics-ON/default-AA project campaign with
the same heap/time limits. Require unchanged finding identities and
occurrences, complete latest-run labels, under-load profiles and exact OOM
owners. The important target remains Thingsboard run-1 completion; a local
two-times kernel result alone does not meet that target.

## 7. Evidence

The current snapshot is Thingsboard **run-1 OOM**, with no COMPLETE or
accepted forward run. The input census and output probe bind that exact
heap and source epoch:

- [Complete input-axis census](../../../run1-rule-selection-equality-fix-20261024/validation/heap-candidate-thingsboard-mark-axis-maps/input-axis-summary.json).
- [Complete bounded output relation probe](../../../run1-rule-selection-equality-fix-20261024/validation/heap-candidate-thingsboard-full-cohort/full-cohort-diagonal-summary.json).
- [Exclusive MethodEdgeStore container control](../../../run1-rule-selection-equality-fix-20261024/validation/heap-candidate-thingsboard-mark-axis-owners/exclusive-method-store-class-controls.json).
- [Profile comparison and actual iteration windows](../../../run1-rule-selection-equality-fix-20261024/validation/profile-analysis/comparison-summary.json).
- [Six final OOM scopes and source-bound validation](../../../run1-rule-selection-equality-fix-20261024/validation/heap-reference-corrected-comparison.json).

The performance report keeps the failed acceptance gates: Thingsboard has
no accepted result; PDF misses two strict main return locations; OWASP
exports 9,179 entries versus CI's expected 4,112 despite matching all main
locations. These proposals target run-1 workload. They do not claim to fix
those separate trace/export contracts or the later run-2 memory failures.
