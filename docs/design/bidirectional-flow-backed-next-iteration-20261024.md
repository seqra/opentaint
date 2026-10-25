# Next iteration after FLOW-backed concrete relations

Date: 25 October 2026. Measurements: 24 October 2026.
Status: proposal; not implemented or selected. All 12 fixed project commands,
profile analyses and all six source-bound physical heap analyses are closed.

Base implementation: `5ec1b30be614a0cfdc31ec3102bfa2f9301ee21e`.
Use the [fresh project report](../reports/bidirectional-flow-backed-concrete-performance-20261024.md),
not an earlier performance report. Thingsboard completes **run-1 in
392.439 s**, then reaches **run-2 OOM**. Its latest COMPLETE engine and
accepted forward report are **run-1**. The run-1 engine target remains 60 s.
Conductor and Stirling-PDF also reach **run-2 OOM**, with **run-1 COMPLETE
and accepted**. This proposal focuses on the remaining run-1 work.

## Scope and intended behavior

The next change must avoid redundant computations. It must not change field
transfer, initial fact grammar, mark identity, selected rule conditions,
cleaner behavior, static request closure, source/sink identity, normal
records or the run-2 handoff. It must retain the selected non-subsumable
flags and their metadata-only progress. No new grounding mechanism, global
answered archive, static routing graph, IR storage change or reference
manager rewrite is proposed.

For the primary call-pipeline proposal, decoding each pending packet and
stored row must yield the original scalar relations and flags. All pending
work stays counted and drains at the required barriers.

For the static supply proposal, current and new pending membership maps
must be equal at every existing commit. Its new path skips only a pure
projection whose output is already in that map. It keeps the executed
writer, rule and caller-binding effects. Thus this proposal changes work
and allocation, not the selected semantic relation.

## Ranked proposals

| Priority | Proposal | Expected work reduction and evidence limit |
| --- | --- | --- |
| 1 | Carry exact diagonal mark masks through caller joins and call stages | Targets the large per-mark call pipeline. Caller subscription scopes account for 40.48% of Thingsboard run-1 Java samples, with overlap. The eligible call cohort width still needs a census; no engine speedup is established. |
| 2 | Reject impossible concrete premise marks before publication decoding | Can omit all wrong-mark payload decodes in a cohort. Publication candidate selection has 6.55% of samples and borrowing has 5.18%, included in that work. The actual rejected fraction is not measured. |
| 3 | Avoid duplicate entry notifications and canonical seed offers | Reuses existing admission and can omit repeated request/entry processing. The 18.99% notification bound is conditional. Initial admission already prevents repeated body analysis. |
| 4 | Avoid duplicate static supply projection | Has the strongest duplicate count, but only 1.53% of Java CPU samples in the known-input binding scope. Direct scalar composition has 8.70% of sampled allocation weight. It is an allocation optimization, not the main CPU solution. |

These priorities are based on the completed **Thingsboard run-1**. Its latest
reached iteration is **run-2 OOM**, with run-1 COMPLETE and accepted. Shares
are inclusive Java sample shares and overlap; do not add them or turn them
directly into wall-clock savings. The
[profile receipts](../../../run1-flow-backed-20261024/validation/profiles-analysis.json)
validate the windows and separate native GC work from Java samples.

## Carry exact diagonal masks through the call pipeline

The current implementation shares diagonal geometry in method-point and
summary storage. A plain body statement can apply one geometry to a mark
mask. Calls still use the scalar fallback, create caller-qualified N2 inputs,
match summaries, run return stages and then meet successor admission. Thus
compact storage does not remove the per-mark call pipeline.

N2 already merges TAINT marks under the **same exact CallerRef**: its GroupKey
does not contain the concrete mark. Do not propose that existing merge again.
The new diagonal store cohort spans CallerRefs whose original FULL premise
marks differ while all other coordinates agree. Its decoder must restore
each distinct original premise. ZERO/FLOW-origin multi-mark rows can already
be packed and are not counted as this opportunity. Different FLOW mark
exclusions remain different headers; this proposal does not discard them.
Canonical callee seeds keep their current plain metadata. Caller protection
stays in the caller input owner and is applied during composition; it must
not become a global property of a callee hypothesis. Normal and exceptional
return ports also keep their separate handling.

```java
Object pass(Object p) { return p; }
Object caller(Object p) {
    Object x = pass(p);
    return x;
}
```

For an eligible cohort at the same caller statement and call stage:

```text
I(p,T1) -> local p/[any]/T1, protected or plain
...
I(p,Tk) -> local p/[any]/Tk, protected or plain
call result: I(p,Ti) -> local x/[any]/Ti for each i

before: k call-form borrows, k binding traversals, k N2 geometry containers,
        k equal FLOW-summary geometry applications, k return/bind-back walks
after:  one call-form borrow and one geometry traversal per eligible stage,
        exact mark masks for the k diagonal relations and their flags
```

This is exact batching, not a new mark abstraction. Decode must restore
`I(p,Ti) -> result/Ti` for each i, with no `Ti -> Tj` product. Keep different
callers, original initial shapes, contexts, statements, stages, layers,
identity/alias classes and continuation addresses separate. Protection is
an exact output mask and metadata-only growth remains work.

The first design should keep an immutable logical packet:

```kotlin
data class DiagonalCallPacket(
    val callerInitialShape: InitialShape,
    val callee: MethodKey,
    val callerRefShape: CallerRefShape,
    val stage: ResumeAddress,
    val inputGeometry: Geometry,
    val marks: MarkSet,
    val protectedMarks: MarkSet, // first cell: uniform flag over the geometry
    val layer: Layer,
    val identityCandidate: Boolean?,
    val pendingDemotion: Boolean,
)
```

Extend the existing caller input owner and its indexes. Do not add a second
added-fact store. Admit masks before scalar construction. Borrow a call form
only while executing a stage; do not pin it in a queued packet. A FLOW
summary that preserves each input mark can operate on this packet once.
Cross-mark, unsupported geometry, source/sink rules and dependent stages
keep their original scalar processing. The packet can resume bulk handling
after such a boundary only if its exact diagonal decoder is restored.
Partial per-output protection also uses fallback until the packet carries
an exact mask at each output. Do not promote one protected output into a
flag on all unrelated outputs merely to make a packet uniform.
Operand and result type filters can also depend on a mark's primitive
tracking policy. Apply their exact eligible-mark masks or use scalar fallback;
equal AP geometry does not make all FULL atoms interchangeable.

Use a method-owned pending call queue to merge equal eligible continuations
before execution. A method's ordinary queue becoming empty is a possible
flush barrier; pending calls must then drain before request/static commit
and global quiescence. Quantum yield retains all packet remainders as counted
work. Measure the resulting packet widths; storage width alone does not
show that these marks arrive in one batch.

**Measurement gate before implementation:** count eligible diagonal N2 and
call-stage cohorts by the full key, their mask widths, cross-mark residuals,
protection shape and stage fallbacks. The 13.04 summary storage ratio is not
this call cohort width; the current body batches average only 2.015 marks.
An incomplete reference run-1 heap can identify unchanged N2 layouts and
examples, but cannot establish the candidate's completed-run cohort rate.
The 17.48% call-plan construction scope is a separate cost. Ordinary form
borrows already hit a cache, so k borrows do not imply k constructions.
Measure rebuilds before claiming that batching removes that construction.

Prove exact decoding for admission, existing/future summary replay, request
climbs and both source orders. Prove each bulk stage equals the decoded
scalar pipeline, including original premises, guards, layer OR and all
required demands. Pending packets count as work before quantum yield and
request/static commit. Keep ZERO phases and rule occurrence identities.
If a stage cannot meet this law, fall back there; do not alter its field,
cleaner or rule semantics to create a wider batch.

The local work reduction can be k geometry operations to one. The current
profile identifies the call pipeline as a large target; it does not prove
that all of that pipeline is eligible or predict a two-times engine gain.

A stronger redundant pattern combines this packet with mark-aware summary
selection. Suppose a helper has k same-geometry protected summaries
`p/Ti -> ret/Ti`, and its caller has the k diagonal inputs above. Today the
position-only replay can visit k concrete premise keys for each input:
up to k² candidate payloads, followed by rejection of the wrong marks. FLOW
backing does not delete these protected dependencies. A shape/mask join can
instead intersect the input and summary mark masks and apply the shared
geometry to that exact intersection. For k=50 this example changes 2,500
concrete candidate decodes to one mask join plus the 50 required membership
results. It must not produce any Ti-to-Tj relation. Cross-mark summaries
stay separate. This is an algorithmic work reduction in the example;
measure how often it occurs in Thingsboard before predicting its benefit.

## Avoid duplicate static supply projection

This is the strongest measured duplicate-count candidate. Its small CPU
share keeps it below the caller pipeline. It can still avoid substantial
allocation. A duplicate count is not a CPU percentage.

Thingsboard run-1 visits 20,765,066 output leaves in the known-static-input
supply branch. It offers 20,954,625 temporary supply memberships. Only
879,697 are fresh in their current temporary actor batches. Therefore
20,074,928 offered members, or **95.80%**, are rejected as duplicates.
The collector already deduplicates them. The avoidable work occurs before
that collector.

These are cumulative temporary-batch coordinates. A later batch or another
method can need to publish the same field/mark again. Do not compare them
with the final global pool's 145 regions and 2,117 memberships as if all
three counts had the same keys and lifetime.

### Current versus new pipeline

Current code in `Run1PointResume.computedGroups`:

```kotlin
if (core.hasKnownStaticGroupInput(premise)) {
    val initial = premise as InitialAp
    val actual = core.knownStaticInput(initial)
    for (leaf in core.ops.leaves(value)) {
        val scalar = core.ap.factsOf(leaf.fact, leaf.exclusion, value.layer)
        core.composeStaticSummaryWithActualInput(initial, scalar, actual) {
            core.staticBatch.supplies += core.staticSlices(it)
            // StaticSupplies rejects an already pending member here.
        }
    }
}
```

Each duplicate in the known-input branch has already paid for scalar construction, AP matching and
summary composition, layer/limit handling and output slicing. Sharing or
removing the enclosing summary row does not avoid this producer effect:
`retainSummary` must publish computed supplies before static/static erasure.

Proposed first change:

```kotlin
if (core.hasKnownStaticGroupInput(premise)) {
    val initial = premise as InitialAp
    var actual: Facts? = null
    for (leaf in core.ops.leaves(value)) {
        val candidate = canonicalFullSupply(initial, leaf, value)
        if (candidate != null &&
            core.staticBatch.supplies.contains(candidate.region, candidate.atom)) {
            statistics.skippedPendingSupplyProjection()
            continue
        }

        // Fresh or unsupported: keep the exact current path.
        val input = actual ?: core.knownStaticInput(initial).also { actual = it }
        val scalar = core.ap.factsOf(leaf.fact, leaf.exclusion, value.layer)
        core.composeStaticSummaryWithActualInput(initial, scalar, input) {
            core.staticBatch.supplies += core.staticSlices(it)
        }
    }
}
// Keep the enclosing computedGroups requestWork() and the rest of retainSummary.
```

Add `contains` to the existing `StaticSupplies` owner. Do not add another
history map. It tests the current canonical profile only. GROUP and the raw
ordered API keep their current path. Do not insert a speculative seen bit
before a projection succeeds.
The certified cell requires FULL input and output atoms, not only FULL
configuration. A retained GROUP selector or mixed input uses the old path.

### Complete key and ownership

```kotlin
// Canonical FULL profile only. STATIC, STAR selector and Empty E are checked.
data class CanonicalSupply(val region: Pattern, val atom: TaintMark)

// region keeps either:
//   named static field: class accessor + field accessor + exact current tail
//   global marker:      one class accessor + EXACT tail
// atom keeps the complete FULL rule owner and full mark identity.
```

Do not merge EXACT, ANY, MUST or a supported raw STAR region. Do not turn
an exact class marker into a class-wide field. Preserve the current shape
validator and invalid-input behavior. The query does not use global reach,
processed or request membership as a permission to skip an actor effect.

The temporary map is owned by one method actor. A commit freezes it and
replaces the batch. A member in the next batch is fresh temporary work even
if it was present before the replacement. Keep that lifetime unchanged.

### Code under analysis and annotated operations

```java
void main() {
    C.in = sourceT();
    copy();
}
void copy() {
    Object a = C.in;
    checkT(a);        // ordinary request handling supplies the real T input
    C.out = a;
    C.out = a;
    C.out = a;
}
```

After the existing static service answers the request for T:

```text
canonical input: (S, C.in,  STAR, {}, T)
known actual:    (S, C.in,  ANY,  {}, T), DEMAND
three results:   (S, C.out, ANY,  {}, T), DEMAND
pending key:     region(S, C.out, ANY, {}, *) -> {T}

before:
  write 1 -> producer effects -> scalar/AP/limit/slice -> add T
  write 2 -> producer effects -> scalar/AP/limit/slice -> reject duplicate T
  write 3 -> producer effects -> scalar/AP/limit/slice -> reject duplicate T

after:
  write 1 -> producer effects -> scalar/AP/limit/slice -> add T
  write 2 -> producer effects -> pending lookup -> omit pure projection
  write 3 -> producer effects -> pending lookup -> omit pure projection
```

All three local write-presence/writer effects still run. All ordinary caller
bindings, sources, cleaners, summary erasure, raw admission and publication
retain their current handling. The shortcut belongs inside the computed
supply branch, not around `retainSummary`.

If input T produces U, query output U. An EXACT output has a different
region from an ANY output. An equal name under another rule owner has a
different FULL atom. Non-subsumable metadata remains on the original
relation; the existing static pool stores membership, not that local flag.

### Required projection proof

Define `R(initial, leaf)` as the current AP composition, bound and slice
pipeline. `canonicalFullSupply` is valid only in a proved cell:

```text
R(initial, leaf) = {(candidate.region, candidate.atom)}
```

The constructive proof must bind the actual original AP implementation:

1. A canonical field initial has STAR, Empty E and a concrete FULL input
   atom. Its known actual has the same field/atom and ANY/DEMAND. An exact
   class marker retains its existing EXACT input case.
2. The composition has an empty relative input suffix. It selects the
   declared output atom, including a cross-mark output. It introduces no
   rule effect or abstract-mark request. Keep the output tail exactly.
3. The static output is already bounded at run-1 limit 1 with Empty E.
   The second limit and cover preserve it. Layer is already DEMAND and is
   not a static supply-key coordinate.
4. The existing static slicer removes the output mark from its region
   selector and returns that same complete FULL atom. FULL atom conversion
   is identity.

The existing relay model provides region and target preservation laws.
It is a useful starting point, not a completed FULL Kotlin adapter proof.
Unsupported or uncertain cells return null and execute the old pipeline.

Let P be the current temporary membership map. If the candidate is already
in P, the old `StaticSupplies.plusAssign` subset branch leaves P and key
insertion order unchanged. Omitting R therefore gives the same P. Otherwise
the new path executes R. Induction over producer visits gives the same map
at each original commit. Keep the other commit lanes and `requestWork`
unchanged. The existing positive static-service closure then receives the
same memberships. Thread timing and packet diagnostic counts can vary;
logical rule occurrences and source/sink identities must not vary.

Under the one-leaf/one-supply identity, at least
`20,765,066 - 879,697 = 19,885,369` direct leaf visits currently finish in an
already pending member. This gives a conditional lower bound on removable
site computations. It does not establish a two-times whole-engine speedup.

### Optional second step after the first adapter passes

Read bounded static TAINT leaf masks directly, subtract the pending mask,
and decode only fresh members. This can avoid scalar Pattern construction
for duplicate members as well as their AP replay. Preserve exact tags and
complete FULL atoms. Reuse the same map; no second archive is needed.

Do not silently replace all fresh AP computations with direct output
insertion. That stronger change needs a complete adapter equality for every
accepted output tag and validation path. The first version deliberately
keeps fresh and unsupported computations on the existing reducer.

### Validation and measurement gates

- Prove the exact FULL projection cell with original AP operations. Check
  field and exact class inputs; EXACT, ANY and MUST outputs; cross-mark
  outputs and mixed owners. Keep broad inputs and nonempty E on fallback.
- Compare complete temporary maps, insertion order and commit effects for
  duplicate, fresh and partial masks. A batch replacement must make a later
  duplicate fresh again.
- Test late read, late request, late writer, local source, caller-bound supply,
  quantum yield, cancellation and static/static erasure. Preserve flags on
  the ordinary relation and both normal/exceptional scopes.
- Add counters for certified projections, skipped pending projections,
  fresh materialized projections and fallback. Record them per iteration.
- Repeat only the fixed project campaign after the implementation commit.
  Compare strict locations, result occurrences, COMPLETE/accepted iteration,
  run-1 engine time, allocation and GC. Keep later OOMs explicit.

## Other candidates and unresolved evidence

### Reject impossible concrete premise marks before decoding publications

This is a source-supported candidate. Its run-1 CPU share and ranking are
pending. `PublicationIndex.candidates` indexes members by base and path. It
then borrows and decodes their publications before `satisfying` checks the
complete premise. A concrete T input can therefore construct publications
under unrelated concrete U premises. `CalleeSubscriptions.candidates` has
the symmetric position-only candidate lookup for newly published summaries.
That delivery arm borrows retained input Facts; it already has the publication
and cannot save the same publication-decode work as the replay arm.

```java
Object helper(Object p) {
    // Selected conditional rules at this method boundary:
    // CM(p,T1) -> assign T1 to return
    // ...
    // CM(p,T50) -> assign T50 to return
    return p;
}
void caller() {
    Object x = sourceT7();
    sink(helper(x));
}
```

Same-mark rule assignments retain their non-subsumable outputs:

```text
callee rows: p/T1 -> ret/T1, ..., p/T50 -> ret/T50, protected
caller input: arg0/[any]/T7

before:
  position lookup -> all 50 members -> decode 50 publication payloads
                  -> satisfying rejects the 49 wrong concrete premise marks

after:
  position lookup -> premise-mark filter -> decode only the T7 payload
  also retain every applicable abstract STAR/FLOW premise
```

For a FULL run-1 TAINT input, a safe coarse mark filter is:

```kotlin
// Guard: FULL run-1 TAINT input with FULL atoms only; other inputs use old path.
val inputMarks = allMarks(part.added) // once, across its full TAINT tree
fun mayMatch(member: Member): Boolean =
    when (val mark = member.premise.member(member.index).mark) {
        is MarkSlot.Star -> true
        is MarkSlot.Concrete ->
            manager.marks.isGroup(mark.mark) || mark.mark in inputMarks
    }
```

Use the incoming conclusion's marks, not the caller's original premise or
the publication's output mark. The full spatial and layer predicate still
runs after this coarse filter. A global union is safe even if a mark occurs
on the wrong input path; the later predicate rejects that extra candidate.

FLOW input keeps the existing path, including its concrete mark requests.
Keep ZERO, static control subscriptions, conditional members, GROUP and all
later runs on their current path until their own laws are checked. Do not
infer a concrete group supply from an abstract FLOW input.

The first version can reject a member before borrowing/decoding its payload.
It still walks the position postings. A mark-keyed posting partition could
also avoid those scans, but its memory and update cost need a separate
design. Do not claim an O(1) index query from a post-lookup filter.

The proof obligation is a necessary-condition law: if the original FULL
`satisfying` accepts a FULL concrete member T against a TAINT input of FULL
atoms, then T belongs to that input's mark union. A GROUP selector can match
members without appearing in that union; keep its original matching path.
Therefore the rejected FULL members have no original
application or request effect. Prove both replay directions and keep new
metadata-only results. Test cross-mark outputs, multi-mark input trees,
late publications, late inputs, partial coverage and static ZERO behavior.
Count members scanned, members rejected before decode, payloads decoded and
real applications. Fifty-to-one in this example is a decode-work ratio,
not a measured Thingsboard or engine speedup.

### Reuse existing entry admission

The [source note](../../../run1-flow-backed-20261024/validation/entry-work-avoidance-source-note.md)
finds two smaller or less measured opportunities. Existing N2 admission
rejects an exact duplicate subscription, but `enterCallees` still sends its
`LinkIn`. Expose the existing admission and send only an admitted fresh
delta. Do not add another cache. Keep the full callee, CallerRef, call stage,
original premise, layer and input-header key, including protection growth.
Register N2 before input delivery and preserve both request arrival orders.
Prove that the fresh deltas emit the same union of canonical callee seeds,
and that the first LinkIn is counted and reliably delivered. Keep every
resolved callee target and admitted protection-only growth.

For one caller origin at one call stage:

```text
first  I/T -> arg0/[any]/T: N2 admits -> LinkIn -> entry handling
second I/T -> arg0/[any]/T: N2 rejects -> LinkIn -> repeated entry handling
new second handling:       N2 rejects -> no LinkIn
```

The 2,430,221 difference between input arrivals and accepted N2 deltas is a
conditional 18.99% notification opportunity, subject to verifying the same
call-site scope. It is not a measured skip counter or CPU share.

The same note proposes combining nonstatic request answers into separate
root-EXACT and nonroot-STAR mark masks before canonical seed construction.
For input `arg0.{f/T,g/T}`, both paths currently offer `arg0/*/T`; one offer
is enough. If root EXACT/T is also present, retain both `arg0/$/T` and
`arg0/*/T`. Subtract only the current actor's admitted initial memberships.
Keep the caller N2 records and future request climbs: a callee seed cannot
stand in for a new caller's required concrete input.
Do not apply this seed filter to R storage, FLOW-to-T climbs or first DEMAND
input-presence bookkeeping.

The current initial set already prevents 20,475,387 of 21,324,749 candidate
calls from re-running the body. The opportunity is to avoid their earlier
projection/admission work. It is incorrect to call them 20 million repeated
method analyses. Rank this change only if profiles show a material cost.

The ranking is a work-target priority, not a measured speedup forecast.
A high admission-attempt count alone does not prove a large saving or a safe
omission. Start the next selected implementation with the named cohort and
mismatch census, then prove and implement the supported cells. Keep the
fallback if the measured eligible scope is small.

The run-2 OOMs and the PDF export-location fault need separate contracts.
Do not fix them inside a run-1 projection optimization. The next iteration
must name any proposed semantic change before implementation, as required
by [the proof guide](../../spec/proof-guide.md).
