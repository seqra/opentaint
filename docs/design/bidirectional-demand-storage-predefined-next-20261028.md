# Next iteration: remove repeated demand and static work

Date: 28 October 2026. Base: `2273c824510ed9366ccd2aa65935f8d3561c38d1`.
Status: proposal for selection. These changes are not implemented.

Use the [current project report](../reports/bidirectional-demand-storage-predefined-performance-20261028.md)
and its embedded data. Earlier runtime reports are not the measurement base.

| Project | Outcome | Latest reached | Latest complete | Accepted forward |
|---|---|---|---|---|
| OWASP | TIMEOUT | run-12 | run-11 | run-11 |
| conductor | OOM | run-4 | run-3 | run-3 |
| thingsboard | TIMEOUT | run-2 | run-1 | run-1 |
| Stirling-PDF | TIMEOUT | run-6 | run-5 | run-5 |

## 1. Ranking and scope

Rank by the observed phase and the amount of work that the change can remove.
The rank is an engineering estimate. It is not a measured speedup.

| Rank | Proposal | Current work | New work | Expected impact and limit |
|---|---|---|---|---|
| 1 | Match one caller input against a batch of static writer outputs | Repeat input selection and premise matching for each output | Select and match once per complete owner/original batch, then apply its outputs | Thingsboard binding takes 239.536 s, with 222,365,480 candidate visits; matching is 39.91% of Java samples. Batch widths are not measured yet. |
| 2 | Prune C5 prefixes with an impossible fixed target | Extend a prefix even when its fixed target cannot admit the original member | Reject the entire impossible prefix subtree before queueing it | Thingsboard run-2 has 4,603,109 C5 states; C5 is 48.96% of Java samples and 62.01% of late native CPU weight. The rejected fraction is not measured yet. |
| 3 | Route STATIC facts across certified identity CFG regions | Revisit every neutral instruction for each unchanged STATIC fact | Visit the first relevant instructions through a compact graph route | Stirling run-5 has repeated unchanged and instruction-classification work. Eligible visit count is not known. This does not remove current persistent point rows. |
| 4, conditional | Skip irrelevant pure FULL cleanup blocks after run-1 | Execute each selected cleaner and protection wrapper on another base | Keep the exact input and skip the whole identity block | Later call/protection work is material, but the share caused by base-mismatched cleanup is not measured. Select only after the count gate. |

Start with ranks 1 and 2 for thingsboard. Rank 3 addresses the different
Stirling pattern and needs a small graph adapter proof. Rank 4 is a narrow
follow-up, not a reason to enable the whole run-1 cleanup kernel on later runs.

No major analyzer semantic change is proposed. The required contract is equal
decoded relations, protection masks, summary layers, rule observations and
finding identities when no work remains. Internal packet sizes, traversal order and
batch-dependent callback counts can differ under the accepted diagnostic
contract. The proofs below are required before implementation. They are not
claims that the future adapters are already verified.

Keep these parts unchanged:

- AP transfer, all field tails and field/mark exclusions.
- Normal persistence, concrete protection and FLOW subsumption.
- Static pool supplies, read activation, write-point ownership and exit rules.
- FULL/GROUP meaning, rule selection, source/cleaner semantics and mark sets.
- Call order, full method context, actual-input matching and ZERO rules.
- Whole ND originals on restricted runs; run-1 still has no ND edges.
- Predefined methods and their selected boundary-rule policy.
- Form cache policy, managed references, MarkTable and IR storage.

Ranks 1 and 2 belong to run-1 handoff and incoming run-2 only. They must not
add transitive demand lookup to run-3 or later. Ranks 3 and 4 are explicitly
restricted-run changes; they must keep the run-1 lane unchanged.

## 2. Match a batch of static outputs

### 2.1 Current and proposed processing

Current source:

```text
bidi/engine/JoinedStaticWriterBinding.kt
bidi/engine/CalleeSubscriptions.kt: visitJoinedCandidates
bidi/engine/SubscriptionManager.kt: matches
bidi/store/KilledStaticWriteStore.kt: StaticWriteKey
```

The current writer key contains a complete original and one raw static
output. `complete()` borrows inputs, creates a fresh visited-input set, and
matches the original for each output. The candidate index already uses
prefix and extension lookup. The repeated work is between output keys.

```java
void set(Box p) {
    C.a = p;
    C.b = p;
    C.c = p;
}
void caller(Box q) { set(q); }
```

Run-1 guide facts, with all omitted field exclusions empty:

```text
owner = complete MethodKey(set)
original = p.* / FLOW
outputs = { C.a.* / FLOW, C.b.* / FLOW, C.c.* / FLOW }, DEMAND
one actual input = caller original J, actual p.* / FLOW
```

Before:

```text
output C.a: borrow candidates; match p.*; apply C.a; publish bound result
output C.b: borrow candidates; match p.*; apply C.b; publish bound result
output C.c: borrow candidates; match p.*; apply C.c; publish bound result
```

After:

```text
batch (owner, p.*): borrow candidates; match p.* once for each actual input
    apply all three output values to that matched actual
    publish exactly the resulting leaves, with the same caller original J
```

This does not replace writers with a class-wide value. It keeps each named
field and output relation.

### 2.2 Storage and algorithm

Use one pending bucket per complete owner and original. Reuse exact write-key
IDs for lifetime deduplication. Drain only the current output delta. A new
recursive caller-bound output can queue another delta for that bucket.

```kotlin
data class BindKey(val owner: MethodKey, val original: InitialAp)

class PendingOutputs {
    val admittedIds: IntSet        // each complete raw output membership once
    var delta: ExactOutputPacket   // full headers; no conclusion subsumption
    var queued: Boolean
}

fun offer(owner: MethodKey, id: Int) {
    val row = writeKeys.row(id)
    require(row.original.base != STATIC) // static originals belong to B
    val bucket = buckets.getOrPut(BindKey(owner, row.original))
    if (!bucket.admittedIds.add(id)) return
    bucket.delta.addExact(row.result)
    enqueueOnce(bucket)
}

fun drain(key: BindKey) {
    val bucket = buckets[key]
    bucket.queued = false          // BEFORE a callback can offer a late output
    val outputs = bucket.detachDelta()
    // Reentrant output admission writes to a NEW delta.
    val visited = HashSet<CompleteInputKey>()
    borrowCurrentInputs(key.owner, key.original) { part ->
        if (!visited.add(completeInputKey(part))) return@borrowCurrentInputs
        if (!validExistingZeroCell(key.original, part)) return@borrowCurrentInputs
        val actual = matchOriginal(part, key.original) ?: return@borrowCurrentInputs
        val out = existingGuideNormalizer { callerOriginal, leaf ->
            publishBoundGuide(part.ref.caller, callerOriginal, leaf)
            if (callerOriginal.base != STATIC)
                offerCallerBoundWriter(part.ref.caller, callerOriginal, leaf)
        }
        // Use scalar outputs first. Pack only after the typed union proof.
        for (conclusion in outputs.scalarOrProvedPackets()) {
            if (part.zeroOnly) out.result(conclusion)
            else ops.applySummary(actual, key.original, conclusion, mode, out,
                                  original = part.ref.premise)
        }
    }
}
```

`borrowCurrentInputs` is a premise-only adapter over the same immutable
current input index. It must not change candidate membership. The complete
input key still includes `CallerRef`, complete `GroupKey` and `zeroOnly`.
Do not merge calls or contexts with equal base/path alone.

An output packet partitions by base, type, tail, layer, field exclusion and
raw mark exclusion. Keep the raw FLOW `mx` until actual matching/application
finishes. The live exclusion operation already emitted its mark request.
Guide-only binding adds no new request. Guide normalization can discard
irrelevant `mx` only at the same point as now.

First prove the selection/matching factorization while applying scalar
outputs. Packed AP application is a second step, under the typed union proof.
This separates repeated-match savings from output-packet savings.

Do not retain all matched inputs or 28 million output callbacks in a new
cache. Borrow one current input at a time. Keep only exact admitted output
memberships, queued output deltas and one batch's input deduplication scratch.
Do not feed composed B paths back into writer binding. The finite write-key
space and exact admission keep the existing fixed point finite.

### 2.3 Correctness argument and required proofs

Let `M(P,I)` be existing matching for original `P` and actual input `I`.
Let `A(I,P,O)` be the complete typed AP image, including guide normalization.
For a fixed complete owner/original and immutable input snapshot:

```text
scalar result = union over O, I with M(P,I) of A(M(P,I), P, O)
batched result = union over I with M(P,I) of
                   union over O of A(M(P,I), P, O)
```

Finite union order does not change the decoded result. Matching does not
inspect `O`. A finite output delta can therefore share matching. Induction
over admitted output deltas preserves the full caller-bound fixed point,
provided late outputs queue new work and every recursive bound writer is
still offered.

Constructive Lean models must prove this finite factorization, reentrant
delta completeness and finite admission. The Kotlin adapter tests must prove
the same input index and ZERO cells are used. Packed output application needs
an additional distributivity proof for every supported typed header; compare
decoded scalar paths and mark/protection memberships, not wrapper counts.

Test ZERO actuals and originals, FLOW and TAINT, exclusions and raw `mx`, all
tails, EXACT class markers, different call stages/contexts, recursive callers,
late outputs, cancellation, and output deltas created while draining. Native
normal persistence, rules, call suffixes and alias expansion remain outside
this guide-only operation.

### 2.4 Measurement

Count distinct owner/original buckets, outputs per drained bucket, batch
count, input candidate visits, match calls, typed AP applications and peak
pending memberships. Compare exact final W/B/R relations and outgoing demand
to the scalar oracle. A bucket with `m` outputs and `k` candidate inputs needs
`m*k` match opportunities before, and `k` for one drained batch after. Later
deltas add further batches. This is a workload formula, not a guaranteed
project speedup. The run-1 engine's 354.334 s is outside this binding phase.

## 3. Prune impossible C5 prefix subtrees

### 3.1 Current and proposed processing

Current source: `bidi/store/StaticPairLookup.kt` and
`bidi/ap/Reference.kt: insideDemand, restrict`.

C5 walks from a rightmost row toward its possible left prefixes. It keeps
the correlated source and target. The target location does not change on a
left extension. Once the relation is mapped, its target mark also does not
change. The current walker can still extend a state whose target cannot
admit the original member passed to `restrict`.

```java
Box read(Box p) {
    C.a = p;
    C.b = C.a;
    if (hasT(C.a)) C.b = sourceU();
    return C.b;
}
```

The principal relation trace is:

```text
W:      p.* / FLOW   -> C.a.* / FLOW
Bflow:  C.a.* / FLOW -> C.b.* / FLOW
Bmark:  C.a.* / T    -> C.b.* / U
R:      C.b.* / FLOW -> ret.* / FLOW

C5 original member J = ret.* / FLOW
raw backward result = p.[any] / FLOW, DEMAND
```

Before:

```text
R can extend through Bflow and W to a useful FLOW pair.
R extended through Bmark becomes C.a/T -> ret/U.
insideDemand(ret/FLOW, ret/U) is false: no restricted result.
The current walker still explores all compatible earlier prefixes of C.a/T.
```

After:

```text
Keep the FLOW state and its valid prefixes.
Reject C.a/T -> ret/U before queue admission.
Skip every earlier prefix that retains the same impossible ret/U target.
```

### 3.2 Admission rule

```kotlin
fun admit(state: StaticGuidanceEdge, member: InitialAp) {
    checkpoint()
    val j = member.toPattern()
    val target = normalizeDemandFieldExclusion(state.to)

    if (!insideLoc(j, target)) return
    if (state.marks is GuidanceMarks.Mapped &&
        !insideDemand(j, target, ap.marks)) return

    if (seen.add(state)) pending.addLast(state)
}
```

Apply the rule to seeds and composed states. Keep existing owner/visibility
rules, static anchors and middle-edge overlap tests. Apply it separately for
each member of a whole ND original; do not replace that original with one
member when emitting results.

The target test is directional. A GROUP target can contain FULL T in that
group; FULL T does not contain a GROUP member. Use `insideDemand` as written.
Do not use the symmetric middle-edge mark compatibility test.

Keep a FLOW state even if its current abstract target cannot admit a concrete
member. An earlier mapped prefix can color it correctly. Also do not prune
the current source because it does not match the raw backward result: an
earlier writer can change that source.

Counterexample to that source shortcut:

```text
W: p/T -> C.a/U
R: C.a/U -> ret/V
query original ret/V, raw p/T

R's source C.a/U does not match raw p/T.
W + R gives p/T -> ret/V and is required.
```

### 3.3 Correctness argument and required proofs

One left composition changes only the mark of `right.to`; its base, field
path, tail and normalized demand geometry remain fixed. For a mapped right
relation, left FLOW keeps its mapped pair, and left mapped composition keeps
the right output mark. Induction gives a fixed target for every descendant.

`Reference.restrict` first requires `insideDemand(originalMember, entry)`.
Every descendant of a rejected mapped state fails that same condition. No
raw output, refined tail, layer or protection bit can result. For a FLOW
state, only the normalized location test is fixed; its mark remains eligible
for later coloring. Canonical FLOW guidance has the required empty abstract
field exclusion. Do not change actual or native exclusions to obtain this
property. Canonical ZERO endpoints remain ZERO on composition.

Prove target-geometry preservation, mapped-target preservation, rejection
closure, kept-path completeness and equal restricted typed outputs in Lean.
Use executable finite path witnesses. Then compare the optimized search with
the existing exhaustive walker on finite graphs, including cycles, mixed
own/inherited paths, ZERO W/R, exact class anchors, nontransitive overlaps,
FULL/GROUP direction, concrete exclusions, multiple ND members and protection.
Include the source-shortcut counterexample and a FLOW target made useful by
an earlier mapped prefix.

### 3.4 Measurement

Count candidates rejected by fixed geometry and fixed mapped output, states
admitted, predecessor visits, restrictions and peak query scratch. Keep all
existing C2 behavior unchanged. No global result cache or new static closure
is needed. Repeated incoming paths can still cost work before the prune; this
proposal does not claim to solve all C5 traversal.

## 4. Route STATIC facts through identity regions

### 4.1 Current and proposed processing

Scope: run-2 and later, using the run's actual graph direction. All calls,
entry/exit boundaries and relevant rule/static effect sites remain ordinary
processing points.

```java
void work(boolean again) {
    int a = 0;
    int b = a + 1;
    while (again) { a = b; b = a + 1; }
    consume();
}
```

Assume that the local instructions have no configured rules or static effect.
An unchanged STATIC input has complete original `J` and payload `F`, for
example `C.f.* / FLOW`, NORMAL, with its actual E and mx.

```text
before: J->F at each local instruction and loop node, then at consume()
after:  J->F routed to consume() and every other first relevant CFG target
```

A neutral closed cycle with no relevant successor emits nothing in either
algorithm. Exception and normal exit routes must follow actual CFG paths.
No static call-order approximation or method-level bypass is added.

### 4.2 Certificate and storage

`STATIC !in touched` is insufficient. The untouched statement branch still
evaluates sources and conjunctions. For example, a source can check
`CM(C.f,T)` and assign `x/U` even when only `x` is in `touched`.

Use a conservative certificate over the oriented form:

```kotlin
fun staticIdentity(s: StatementSummary): Boolean =
    STATIC !in s.touched &&
    s.sources.isEmpty() && s.conjunctions.isEmpty() &&
    s.staticOperations.isEmpty() &&
    STATIC !in s.targets && STATIC !in s.typeFilters &&
    STATIC !in s.resultFilters &&
    s.edges.none { e ->
        e.isSource || e.conjunctive || e.actionId != null ||
        e.edge.from.base == STATIC || e.edge.to.base == STATIC
    }
```

Also require no method boundary and no call. The engine `reached` hook is a
no-op only after run-1. With process/cut observers, use the original route.
The boundary inventory must include frontend exceptional exits in backward
mode, where `context.isExceptionalExit` alone is insufficient.

Store a lazy method/run/direction graph index with integer nodes, certificates,
neutral SCC/chain regions, immediate region edges and visitation stamps.
Keep no forms, bound rules or extra IR objects. Store no all-pairs frontier
table. The persistent index is `O(V+E)` for discovered graph metadata.
Read forms only in their current scoped cache callback.

```kotlin
fun emitUnchanged(item: EdgeDelta) {
    runExistingCurrentNodeExitRuleHandling(item)
    if (!run1 && item.facts.base == STATIC && observersAbsent()) {
        routes.firstRelevantSuccessors(item.node) { target ->
            addUnchanged(item.copy(node = target)) // SAME original and payload
        }
    } else {
        enqueueImmediateSuccessorsAsBefore(item)
    }
}
```

Keep the current run-1 STATIC special route before this branch. Keep changed
result admission, `edges.add`, cuts and `emitAfter` unchanged. Existing
`emitUnchanged` already avoids persistent point-store writes; the saving is
queue visits, instruction classification and form work. Do not claim that
this deletes all physical static tree or point-map rows from the heap.

Keep existing protection-aware `addUnchanged` deduplication and its epoch.
Do not add a permanent fact/region seen set. Keep work counted until all
route targets are enqueued. Check cancellation while discovering and walking
regions; never publish a partially built region as complete.

### 4.3 Required proofs and tests

Before implementation, prove local identity with no observation; constructive
CFG route soundness and completeness; finite SCC routing; exact preservation
of whole originals, field geometry, tails, E, mx, layer and protection; and
equal relevant-node observations. Every jump needs an executable original
path witness. Retain or reconstruct it for later trace use.

Test straight regions, diamonds, neutral cycles with and without exits,
forward/backward exceptional paths, source/conjunction observations despite
an untouched base, field/alias effects, predefined calls, all boundary rules,
observer fallback, a second unchanged epoch, cancellation and form rebuilding.
An uncertain certificate makes the node relevant; it must not skip the node.

First measure eligible visits, retained calls/rules/boundaries, region sizes,
queue admissions and metadata bytes. A region of `m` neutral nodes reached
by `k` inputs can remove its repeated `m*k` interior visits after metadata
discovery. A branching graph can still require routing work per input. The
current snapshot does not establish `m`, `k` or an overall speedup.

## 5. Conditional narrow FULL cleanup change

Scope: pure selected FULL cleanup blocks after run-1, including correctly
reversed return actions. Keep FIELD, Kill, RemoveAll, GROUP, static-specific
actions and geometry changes as barriers.

```text
cleanup block: remove T; remove U; remove V at Argument(0), same geometry
input: STATIC C.f/[any]/T with existing layer, E and protection

before: three cleaner calls; each tests another base and keeps the same input
after:  one base mismatch test; keep the exact same PlanFact; skip the block
```

```kotlin
if (!mode.run1 && block.isPureSelectedFull &&
    input.facts.base != block.geometry.base) {
    keepSamePlanFact(input)
    continueAt(block.end)
} else {
    existingScalarOrRun1BlockPath()
}
```

Restricted collectors are identity and make no mark requests. On a base
mismatch, each pure scalar cleaner is identity. Their composition is therefore
identity, including the original, layer, E, mx and protection. Prove this for
the actual wrappers and reversed raw step indexes before implementation.

Do not apply the shortcut to run-1: its STATIC collector can route an input
to the exit even on a cleaner base mismatch. Do not simply remove the run-1
guards on the whole bulk kernel. Its existing proof has empty E and forced
DEMAND assumptions that later inputs need not satisfy.

Gate selection on current mismatched block counts, block widths and CPU in
their cleaner/protection wrappers. High total protection samples alone do
not prove this branch dominates. This narrow proposal changes neither
same-base TAINT cleanup nor its survivor flag.

## 6. Correctness work outside the optimization selection

Keep the three strict Stirling missing identities as failing gates. The D23
unconditional receiver reset has an accumulated-mark loss mechanism, but the
current campaign has no per-edge first-loss ledger. A correction changes
source/cleaner policy and requires a separate semantic proposal. The Simple
exit exporter also needs a real return witness to establish a missing return
path; choosing another display return does not prove that path.

Do not add a blanket ZERO-only exit restriction or filter the generic
method-end XSS rules as a performance shortcut. Both can remove observations.
The 5,075 extra thingsboard candidates require a precision investigation,
not an assumption that all are false positives.

## 7. Validation and stop conditions

Follow [proof-guide.md](../../spec/proof-guide.md). Build constructive models
before runtime changes. Distinguish the algebraic concept from each Kotlin
index, packet, queue and graph adapter. Audit equality/hashing and protection
outside ordinary fact equality. None of these proofs authorizes an additional
field, mark, source/sink or layer change.

Implement and measure proposals separately before combining them. First use
finite differential tests against the current scalar/reference paths. Then
run the required module and application checks, with the known cleaner
precision failures visible. Finally repeat only the four fixed project
configurations with the saved baseline, profiles and OOM capture policy.

For every result, report reached, completed and accepted iterations, run-1
engine time, joined time, run-2 time, later local-only counters, strict missing
and added identities, work removed, peak RSS and reachable heap when captured.
Do not infer success from a lower row count with fewer accepted iterations.

Reject a change if final demand, typed AP outputs, protection, layers, rule
identities or summary observations differ without a selected semantic reason.
If a major semantic change becomes necessary, stop that implementation path,
show the code/fact counterexample and obtain the intended contract. No runtime
change from this proposal is authorized by the current performance report.
