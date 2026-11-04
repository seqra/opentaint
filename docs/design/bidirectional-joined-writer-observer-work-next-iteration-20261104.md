# Avoid repeated joined-writer and loop-observer work

4 November 2026. **Proposal only. No runtime change in this document is
implemented or selected.** Base analyzer:
`52f32dd437d438aec4a700a02c18d94c31d58093`.

Use the [completed measurement report](../reports/bidirectional-loop-demand-trie-performance-20261104.md).
Latest reached/completed/accepted labels: OWASP run-5/run-5/run-5; Conductor
run-6/run-5/run-5; Thingsboard run-1/none/none; Stirling-PDF run-9/run-8/run-7.
The implementation must follow [the implementation guide](../../spec/impl-proposal-guide.md)
and [the proof guide](../../spec/proof-guide.md) after selection.

## 1. Scope and priority

The proposed contract has **no new analyzer semantics**. Remove computations
whose exact semantic result is already available or proved empty. Keep native
matching, full premises, field limits, layers, protection, physical ports,
requests, source authority, Targets, boundary rules, aliases and saved replay.
Do not add a new widening, group policy, field rule or loop-admission rule.

| Priority | Proposed change | Current → new | Expected impact and evidence |
| --- | --- | --- | --- |
| 1 | Reuse joined-writer input selection and matching by complete owner and premise | Repeat selection/matching per static output → reuse an ordered match plan while applying every output | Thingsboard run-1 static completion: selection/matching is 70.25% of Java samples and about 75.25% of allocation weight. Benefit depends on repeated complete premises and plan reuse. This is a phase opportunity, not a measured whole-run speedup. |
| 2 | Reject proved empty DATA applications in the pure loop observer | Apply saved DATA then discover no enclosing output → prove empty before that application | Stirling run-9: direct/reverse observer AP is 25.44% of Java samples; eligibility within this region is not yet measured. C2, real replay and Targets remain active. |
| 3 | Finalize only selected C5 output programs | Allocate/scan all programs for each query → retain/finalize selected ordinals only | Conductor run-6 has 11.28% Java samples in the wider bookkeeping region, but only part is the dense scan. Array allocation itself is only about 0.24% of allocation weight. This is a smaller option, not a factor-two claim. |

The rank is provisional until the stated coverage counters are collected.
The Thingsboard diagnostic captures 32 complete outputs but drops its queued
writer/input samples. Its 32 parent initials are distinct. It does not measure
repeated complete writer-premise width or establish a plan hit rate. Collect
that census before selecting the match-plan constants or claiming a large win.
The first proposal addresses Thingsboard static completion, not its earlier
678.522 s engine phase. That phase also has substantial real-call replay and
subscription work. Do not claim that fixing one join completes run-1 in 60 s.

## 2. Reuse joined-writer matches

### 2.1 Current ownership and repeated work

Relevant files are under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`:

```text
engine/OwnedJoinedStaticWriterBinding.kt  FIFO writer rows and native binding
engine/JoinedBindingLease.kt             detached caller/local input owners
engine/JoinedStaticGuidance.kt           exact owner/port seed construction
engine/JoinedLocalInputs.kt              moved cumulative local input table
engine/CalleeSubscriptions.kt            indexed root caller selection
store/KilledStaticWriteStore.kt          exact raw writer keys
```

The lease is frozen after live runner jobs join. A complete writer row has
one owner, a complete initial I and one raw static output O. For each row,
the binder selects candidates, deduplicates input keys, checks ZERO authority,
matches I, applies O, and emits exact parent guidance. Parent results can add
new writer rows to the queue.

Root selection uses I's base/path. Detached local selection scans its whole
input table. Neither selection nor `satisfying(actual,I,mode)` depends on O.
Both operations repeat for equal complete I with different output columns.

```java
void set(Box p) {
    C.f = p;
    C.g = p;
}
void caller(Box q) { set(q); }
```

```text
writer rows in one exact owner:
  I = p.*/FLOW -> C.f.*/FLOW
  I = p.*/FLOW -> C.g.*/FLOW
actual input: caller premise q.* with actual p.suffix

Before: select/match I for C.f; select/match I again for C.g.
After:  select/match I once; apply C.f and C.g separately in original order.
Result: both caller/q -> C.f and caller/q -> C.g guidance still exist.
```

This is a minimal showcase. It is not an asserted Thingsboard source method.
Use the actual writer diagnostic in the report for measured shapes.

### 2.2 Proposed scratch plan

Keep the writer queue, row admission and seed order unchanged. Reuse a
short-lived ordered plan over the **same frozen input lease**. Its exact key
is `(lease, OwnedScope, complete InitialAp, ApMode)`. The lease/mode may be
implicit fields of one binder. Do not replace full owner or I with a base,
field prefix, mark group, hash alone or transient writer/row object identity.
The existing canonical `InitialAp` identity is valid within the same manager;
use that key as is. No structural copy or new equality rule is needed.

Each plan stores an ordered reference to each accepted input descriptor and
its exact native matched Facts. Keep its parent owner, complete original,
typed actual packet, ZERO-only status and native input key. Retain immutable
Facts references; do not copy the caller/local storage or retain an actor.

```text
complete():
    scratch = boundedMatchPlans(frozenLease)
    try:
        while writerQueue is not empty:
            W = writerQueue.removeFirst()         // unchanged FIFO
            K = (W.owner, W.completeInitial)
            if scratch has complete plan K:
                for match in plan.nativeInputOrder:
                    applyOneOutput(W, match)       // unchanged native code
            else:
                recording = scratch.tryBegin(K)
                nativeVisitCandidates(W.owner, W.completeInitial): input ->
                    run existing input-key dedup and ZERO-authority test
                    matched = existing native satisfying(input.actual, I)
                    if matched exists:
                        recording.tryRemember(input, matched)
                        applyOneOutput(W, input, matched)
                recording.finishOnlyIfComplete()
    finally:
        scratch.clear()                           // before lease close

applyOneOutput(W, input, matched):
    native applySummary(matched, W.I, W.rawOutput, original=input.original)
    existing run1Cover -> global field limit -> run1Cover
    existing onBound(exact parent owner, complete original, static result)
    existing offer of each derived parent writer
```

The first row streams exactly as before; it does not prefetch all matches
before output application. If recording exceeds its explicit scratch limit,
discard that incomplete plan and continue the same native visit. Do not replay
the already processed row. Later rows use native visits until a complete plan
can be retained. Eviction changes cost only. Negative complete plans can avoid
repeated empty scans. Never install a partially visited plan, including on
timeout, cancellation or exception.

A proposed initial budget is 128 plan keys and 2,048 matched-input references
in total per binder, including all plans. These are scratch limits, not limits
on admitted requests, inputs, outputs or semantics. Measure reuse and rejection
before choosing final constants. A hot premise that exceeds the reference
budget falls back; do not replace its actual matches with an approximation.

New output columns for an old I still visit its plan. Every column retains its
raw field exclusions and FLOW mx through native application. Static-original
rows stay in the existing bridge graph. ZERO requires the existing actual
ZERO-origin Reach authority; a Reach under another origin is insufficient.

### 2.3 Correctness obligations and tests

For a frozen lease L and exact owner/I, define `M(L,owner,I)` as the ordered
native accepted inputs with their full match results. Existing binding is an
ordered fold of `applyOneOutput(W,m)` over M for each FIFO W. A complete plan
is that same executable list. Substituting the list preserves the ordered
seed/parent-offer stream for W. Induction over the dynamic FIFO then preserves
each later row and the final guidance. Cache eviction reinstates the same
native fold. This is the required proof, not an assumption that arbitrary
writer reordering is harmless.

Before implementation, construct the finite Lean model with dynamic FIFO,
complete plans, incomplete-plan rejection and executable native fallback.
The native adapter must establish frozen inputs, O-independent selection and
matching, exact input order, and correct whole-key equality/hashing.

Native RED/GREEN cases must cover:

- Two and many outputs under one I; interleaved owners and unequal I.
- Field E, FLOW mx, NORMAL/DEMAND and protection differences in actual inputs.
- True ZERO input versus Reach under nonzero origin; zero-only inputs.
- Root indexed selection and detached local scans, including duplicate paths.
- A late derived column for a previously visited I; recursive parent offers.
- Empty match plans, eviction, recording overflow and cancellation.
- Exact final per-owner/port guidance and seed order versus native execution.

For k output columns, selection cost Q, matching cost M and per-column
application A, the reusable part changes from `k*(Q+M+A)` to `Q+M+k*A` while
the plan remains resident. No saving is promised for k=1 or rejected plans.
Add cache hit/miss/overflow/eviction counts, references, native candidate and
match counts, columns per exact premise, and final seed deltas. Report local
and root owners separately. Never use pool reachability as output coverage.

## 3. Prove empty observer DATA before applying it

The pure `LoopConsumerObservation` computes a signature used to compare the
raw fact with a possible prefix cut. It performs adjacent/repeat C2, saved
DATA replay followed by enclosing C5, and saved Target checks. It does not
execute the real program transfer. Its empty-output shortcut is currently
restricted to some same-direction, non-root cells.

### 3.1 First supported cell: root output is not a summary base

```text
saved relation, in its selected orientation:
  I = ret.* / FLOW -> O = local(7).* / FLOW
applied input:
  ret.f.* / FLOW
native observer application would produce:
  local(7).f.* / FLOW
root summary filter rejects local(7), so enclosing output is empty.

Before: match/apply, create DATA, adjust metadata, reject local output.
After:  prove output base local(7) is not a summary base, omit this pure DATA
        application; keep adjacent/repeat admissions and Target processing.
```

Direct orientation uses the record conclusion base. Reverse orientation uses
the old premise base. Require a DATA output base other than ZERO and a proved
base-preserving native application/metadata path. The base test uses the same
root interpreter predicate as the later filter. It can also hold under whole
original ZERO: the proof is about output DATA, not source authority. Unsupported
native variants use the existing path.

Do not skip reversed `ZERO -> ret/T`: its oriented output is ZERO and it can
produce DemandTarget. Do not skip saved NormalTarget/DemandTarget processing,
Reach, actual source permissions, requests, boundary rules or real saved replay.
Keep C2 labels, actual loop entries and physical output ports.

### 3.2 Second supported cell: complete paired C5 plan has no output base

After complete whole-premise eligibility, a prepared C5 plan can prove
`emptyForBase(orientedOutputBase)`. Extend the existing shortcut to root and
proved reverse/MUST cells only where the same native plan is valid. The plan
includes the full owner, physical exit, complete original, normalized templates
and policy. No plan, ZERO-oriented output or unsupported representation means
native fallback. An empty mark/base intersection must not be inferred from
field geometry alone.

```text
R = ret.* / FLOW -> arg(0).* / FLOW, in the selected orientation
complete parent C5 outputs are only ret / T and Target
prepared.emptyForBase(arg(0)) = true

Before: native AP produces arg(0).suffix, then C5 returns {}.
After:  omit this pure DATA application; enclosing DATA stays {}.
```

This check is separate from actual saved application. A saved NORMAL summary
must still execute where the real propagation policy requires it, even with
no current demand.

### 3.3 Proof and measurement

Model the full observation as `(adjacent labels, repeat labels, enclosing
DATA, Targets)`. Native application is base-preserving for the supported
DATA cell. Root-public-base rejection or a complete empty-base C5 plan gives
an executable proof that this cell contributes no enclosing DATA. Removing
that cell leaves every observation component equal. Equal raw/trial
observations preserve the first accepted cut and the kept fact. This proof
does not permit skipping the real application or the whole observation.

Constructive Lean controls and native tests must cover direct/reverse output
bases, ZERO source conversion, root metadata drops/demotions, MUST inputs,
full ND originals, protected packets, real requests despite empty observer
DATA, late saved Target checks and first-accepted-cut equality.

Count selected saved views, native matches, native applications, each proved
rejection reason, unsupported fallbacks, and emitted observation components.
Measure eligible cells within the 25.44% Stirling run-9 AP region. That entire
region is not removable; the percentage is an opportunity bound only.

The old path already rejects root-local DATA before C5 and an empty base
before C5 scalar packing/cuts. Moving the proof earlier saves AP grafts,
metadata and query setup. It does not remove the field-cut allocation pool
from these already empty cells.

## 4. Sparse C5 output-program finalization

Current `store/PreparedOutputPrograms.kt` allocates an s-slot bucket array
before scalar/program selection, then visits all s programs if selection does
not overflow. Many buckets can be empty. Bucket objects are already lazy.
An overflowing query allocates the array but skips the dense final scan.

```text
selected = ordered scalar selection using the existing frozen output trie
buckets = sparse ordinal -> unchanged protected/plain ProgramBucket
for every selected native scalar/program image:
    add to its existing exact bucket streams
    enforce the existing 2,048 unique-reference limit
if reference overflow:
    return native whole-query fallback; publish no partial result
for ordinal in sorted(buckets.keys):              // original program order
    run unchanged packProgramStreams, field limit and ExactDemandResults
```

Sort by the original program ordinal, not first encounter. For example,
encountered keys `[2,0]` must emit programs `[0,2]`, as the dense loop does.
Maintain protected/plain order, annotation union, packing and fallback. Empty
queries do not allocate an s-slot array or finalize s empty buckets. Empty
bucket diagnostics may use aggregate skipped counts; they are not semantic
rejections and no longer execute per-row sample construction.

Memory/scan cost changes from O(s) to O(k), plus O(k log k) ordering, where
k is the selected nonempty program count and k ≤ 2,048. If k≈s, sorting can
be slower. Measure s/k and retain a justified dense path if needed; do not
guess a winning threshold from total row counts.

The finite conditional model proves ordered sparse finalization equal to the
dense fold when sparse keys are exactly the nonempty native buckets. It has
23 theorems and 38 audited declarations, with no Classical axiom. It does not
prove the Kotlin collector or AP emitter. Its executable key certificate
detects missing/duplicate ordinals. Native equivalence and allocation controls
are still required before implementation.

The [model, checker and receipt](data/loop-demand-trie-candidates-20261104/sparse-c5-program-finalization-20261104/README.md)
are checked in. Its source note pins the current adapter obligations.
The model is conditional evidence for this candidate, not a native test pass.

Conductor run-6 bucket-array allocation is about 0.243% of sampled allocation;
Stirling run-9 about 0.275%. The wider bookkeeping regions include unchanged
selected bucket work. Do not claim removal of all 11.28% Conductor Java work
or 6.51% Stirling Java work. This option can accompany a larger work reduction.

## 5. Ideas not justified for this iteration

The first 4,096 Conductor diagnostic events have 339 distinct growing keys
and 393 distinct full observations. Exact-memo simulations have zero hits.
Do not select an exact decision cache on the basis of 39.71% non-fresh
completion results: broader coverage can cause those results.

Only 32 of 339 growing frames are covered by an earlier broad ANY completion.
An early coverage shortcut needs proof that every possible kept prefix is
covered, not only the raw result. Keep it for a later proposal if whole-run
frequency justifies it. Do not filter container model paths by their names.

Do not add a global static pool approximation, remove writer dependencies,
change output order, bypass paired demand, bypass ZERO admission, or alter
FLOW/TAINT subsumption to make these optimizations easier.

## 6. Implementation and experiment gates

After selection, model each chosen optimization constructively, add native
RED tests, implement it separately, and run the appropriate common/JVM suite.
Pin a commit for each atomic change. Do not combine them into an unexplained
new analyzer contract. Keep the current semantic controls and document any
unselected behavior needed by an implementation before making that change.

Repeat the same four FULL/16 GiB configurations. Reuse the fixed f945 quality
baseline and use 52f as the performance control. Report reached, completed
and accepted labels for every project and diagnostic. Compare full iterations
only; separate extra remaining timeout budget from throughput.

The extended experiment must trace workload through the whole pipeline:

```text
submitted input -> saved replay -> C2 -> current subscription/publication
-> native application -> global cut -> loop observation/cut
-> completion delta -> post-statement storage -> C5 -> next-run demand
```

For representative slow owners, retain complete facts: every premise member,
field tree, tail, E, mark/mx, layer, protection, owner and physical ports. Join
operation counts to fresh results. Record raw baselines, tested cuts and
equal/covered completions separately. A small early trace is not a whole-run
duplicate estimate.

Capture Java and all-thread CPU with distinct denominators; retain sampled
allocation and GC/RSS data. Capture a heap if MemoryManager reports OOM.
An allocation weight is not retained memory. Embed representative code and
full fact traces in the report and check in the needed tables/data.

Priority checks are Thingsboard run-1 engine versus joined completion,
Conductor runs 4–6 and Stirling runs 6–9. State whether work moves to another
phase. Compare semantic finding identities versus 52f at the same accepted
iteration or comparable precision. If the new analyzer advances beyond 52f's
timeout, classify and validate findings from those extra iterations separately.
Retain the existing f945 gaps as open quality failures. Canceled Thingsboard
quality remains censored until a report is accepted. A speedup on an empty
diagnostic does not meet the acceptance test.
