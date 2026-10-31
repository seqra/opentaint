# Reduce repeated demand and summary work

Date: 31 October 2026. Proposed base:
`c4a71246519ee5432879ce82518823f1703f3aa4`.
This is a candidate-selection proposal. It is not an implementation
authorization or a completed implementation spec.

The [current performance report](../reports/bidirectional-target-zero-performance-20261031.md)
uses FULL, 16 GiB, and limits `1,1,2,3,…`. OWASP completes run-5.
Conductor reaches run-4, thingsboard run-2, and Stirling run-8; their last
accepted forward reports are run-3, run-1, and run-7. No project has an OOM.

## 1. Selected scope of this proposal

The candidates change how often the same semantic operation is performed.
They must preserve the completed result of the c4 base under a fair work
schedule. They do not authorize fewer reports, fewer demand permissions,
or broader NORMAL facts. Time-limited output may improve because more
work can finish. It cannot be assumed equal at the same timeout.

The following contracts stay unchanged:

```text
Call offer:
  replay saved summaries on every offer
  use current demand to select admitted initials
  if admitted: use and subscribe to current summaries

Initial admission:
  concrete MAY can answer concrete EXACT with an EXACT/DEMAND hypothesis
  retain the actual caller image for summary matching
  preserve separate NORMAL and DEMAND admission memberships

Summary publication:
  use the complete paired C5 predicate
  preserve field tails, marks, exclusions, layers and protection

Targets:
  NormalTarget(id) composes only with NORMAL support
  ignore NormalTarget backward
  preserve DemandTarget routes and physical source/sink seeds

Static completion:
  run-1 -> run-2 only
  run-3 and later use local demand
```

No proposal changes field transfer, run-1 rule-origin splitting, source
permission, static writer activation, the rule provider, or report IDs.
No proposal adds GroundingSupport, durable added-fact history, a new IR
store, WeakIdentityCache, or a SoftReferenceManager rewrite. A new equality
key must include all metadata that can change observable behavior. In
particular, plain `Facts.equals` does not describe protection equality.

## 2. Priority and expected impact

| Rank | Candidate | Main measured cost | Expected work reduction | Evidence limit |
|---|---|---|---|---|
| 1 | Select terminal static origins from the provided output | Thingsboard run-2: 92.8% of Java samples in terminal traversal | Avoid unrelated terminal-origin searches and repeated graph expansion | Query-key repetition and useful-endpoint counts are not recorded |
| 2 | Pack compatible fresh publications before delivery | Conductor run-4: 72.3% of Java samples in delivery; 93.7% late | One input scan and packed transfer per compatible header instead of one per delta | Batch widths and distinct-header counts are not recorded |
| 3 | Share joined-writer input selection and guide-only bindings | Thingsboard joined phase: 225.956 s, 222.6 million input visits | One selection per complete owner/premise; avoid call-site distinctions unused by guidance | Distinct premise and quotient counts are not recorded |
| 4 | Identify and remove repeated native application output | Stirling run-6: 312.047 s; run-8 timeout after 716.925 s | Target repeated AP transfer, action stages, and storage admissions | Per-fact values and fresh-output ratios are not recorded; selection needs one more diagnostic |

The first three candidates remove repeated operations rather than make
one operation 20% faster. No factor-of-two claim is justified yet. The
implementation gate must measure the multiplicity removed. A candidate
with little multiplicity should not proceed as the main performance fix.

Rank 4 is an investigation and a constrained candidate, not permission
to skip saved replay. It is listed separately because ranks 1–3 do not
directly cover the slow Stirling backward runs.

## 3. Select terminal static origins from the provided output

### Current behavior and cost

`DemandStore.intersect` calls `visitControlPairs` for a ZERO original.
The derived part starts `StaticPairLookup.walkTargetOrigins` from every
static terminal reader. It follows predecessors before its callback tests
whether the origin can restrict the supplied raw conclusion.

```kotlin
// Current conceptual order.
for (rawSummary in publications) {
    for (origin in walkAllTerminalOrigins(method)) {
        testPairedC5(original = ZERO, raw = rawSummary, origin)
    }
}
```

Thingsboard run-2 performs 1,174,034,530 C5 compositions and 1,147,998,193
duplicate-state admissions. The source has a fresh query-local seen set,
so an individual search is finite over its finite state space. The same
graph work can occur again for the next publication. Owner checks and
composition also run before an already-seen predecessor is rejected.

### Proposed behavior

Pass the provided-output family to the terminal query. Use existing
local indexes and the same exact acceptance predicate. Test local explicit
rows first. Stop when the supplied raw result is fully covered.

```kotlin
// Proposed interfaces are pseudocode, not new runtime APIs yet.
fun terminalPairs(method, original, raw, policy, result) {
    offerExistingLocalControlRows(method, original, raw, policy, result)
    if (result.covers(raw)) return

    val graph = run1To2Completion ?: return
    if (!original.isZero) return // unchanged derived-terminal scope

    val selector = originSelector(raw, policy)
    // Selector is a conservative prefilter. Exact paired C5 still decides.
    for (scope in localThenVisible(method)) {
        if (!scope.hasPossibleOrigin(selector)) continue
        scope.visitTerminalRoutes(selector) { completePair ->
            restrictWithExistingC5(completePair, original, raw, result)
            !result.covers(raw)
        }
        if (result.covers(raw)) return
    }
}
```

The selector has three principal cases:

| Supplied raw conclusion | Required route | Safe starting filter |
|---|---|---|
| ZERO reach | A derived `(Target, ZERO)` pair | Local ZERO-origin writer family, then bridges and terminal |
| Nonstatic data at `p` | A derived `(Target, p/…)` pair | Compatible local writer-source family at `p` |
| Named static data | A derived `(Target, C.f/…)` pair | Matching static origin; a bridge-only path can suffice |

An absent local writer family can reject the first two cases only after
the frozen builder invariant is proved: every composed nonstatic/ZERO
origin enters through that method key's writer boundary. Do not apply
this filter to static origins. Local and inherited bridge owner visibility
must retain the current order and full method-context distinctions.

C2 ZERO admission needs only the existence of an eligible Target/Zero
entry, not every derived origin. Reuse that existence result. Do not
build a list of all origin rows to answer a Boolean question.
Keep this predicate separate from C5's `(Target, ZERO)` test. A
`(Target, C.f/T)` pair can admit ZERO at C2 without a ZERO-origin writer.
It does not authorize a `ZERO -> Target` result at C5. A shared cache must
not confuse these two questions.

For relevant routes, use an output-directed forward search from selected
writers, or a bidirectional search with the terminal inputs. An immutable
view can share equivalent adjacency or reachability work. First choose a
canonical graph/query family; do not retain an all-origin closure for
every supplied Fact. Report the number and memory size of retained cache
entries. Reuse existing indexes where they answer the query.

### Example and fact trace

```java
// Rule: toT(arg) checks U and assigns T to ret.
// Rule: sinkT(arg) checks T.
void route(Box p) {
    C.a = p;           // W: p/U -> C.a/U, DEMAND guidance
    convertStatic();
    checkStatic();
}
void convertStatic() {
    C.b = toT(C.a);    // B: C.a/U -> C.b/T, DEMAND guidance
}
void checkStatic() {
    sinkT(C.b);        // R: C.b/T -> DemandTarget
}
```

For a backward raw result `ZERO -> p/U`, C5 needs the complete derived
pair `(Target, p/U)`. Before: walk every terminal origin, then find this
pair. After: select the `p/U` writer family, follow the U-to-T bridge,
and test the same pair. Unrelated writer families at `q` are not visited.
Filtering terminal readers to U would be wrong: this reader uses T.

### Proof and measurement gates

Prove that every path accepted by the old query has a selected writer or
static-origin witness in the new query. Prove both directions of emitted
paired-row equivalence. The witness must retain mark-changing bridges,
FLOW bridges, named static fields, EXACT class markers, tails, exclusions,
owner visibility, and ZERO/Target types. Prove local-first and full-cover
early exit against the same emission set, including MAY and MUST cells.

Measure query calls, distinct complete selector families, selected writer
counts, graph states, unique adjacency expansions, compositions, owner
checks, fresh kept results, and temporary/retained bytes. Use per-owner
or sampled counters outside the inner atomic loop. The current atomic
statistics consume 27.7% of the late thingsboard CPU samples; do not add
another hot atomic counter for every duplicate transition.

## 4. Pack compatible fresh publications before delivery

### Current versus new

Current summary storage merges and deduplicates contents. However,
`PublicationIndex.addAll` can return a separate fresh publication for each
input delta. `onDelivery` repeats candidate selection and application for
each returned row. The method already detaches a publication batch; no
new batching barrier is required.

```kotlin
// Before: fresh rows retain delta boundaries.
val fresh = publicationIndex.addAll(detached)
notify(fresh)

// After: preserve storage admission and final FLOW-backed normalization.
val fresh = publicationIndex.addAll(detached)
val packed = packCompatible(fresh) // same premise + complete Facts header
notify(packed)
```

Use the existing canonical conclusion union. The grouping key is the
complete premise, including full ND membership where legal, and the
complete compatible `Facts.groupKey`. Do not merge layers, bases, kinds,
field exclusion headers, or FLOW mark-exclusion headers. Preserve every
protection upgrade when merging marked paths. Keep typed Targets and
native saved-record messages in their existing lanes.

### Example and fact trace

```java
Box pack(Box p) {
    Box r = new Box();
    r.a = p;             // I/T -> ret.a/T
    r.b = p;             // I/T -> ret.b/T
    r.c = p;             // I/T -> ret.c/T
    return r;
}
```

Assume all three new results have compatible DEMAND headers in one
detached batch. Before: three publication rows each scan the same callee
input family. After: one publication carries the three paths in the
existing field tree and scans that family once. All three output paths
and their protection remain. If the rows have different headers, they
remain separate.

The packing is ephemeral. It must not add a durable caller-input history
or change saved replay from every-offer to fresh-only replay.

### Proof and measurement gates

Prove union distribution for candidate matching, summary transfer,
field-limit cutting, action stages, paired C5 restriction, and protection
transport over compatible packed Facts. Compare expanded semantic sets,
not callback counts. Preserve source/sink occurrence identities.

Prove the subscription race: if an earlier callback registers a new input,
that input still gets all applicable results through the existing
register-then-replay protocol. A single packed candidate snapshot must
not lose what the old later delta snapshot would have seen. Keep runner
ownership and counted-delivery completion unchanged.

Measure `P = fresh rows` and `H = compatible premise/header groups` per
detached batch, candidate scans, transfer calls, packed path widths, and
fresh post-statement memberships. The input-scan component changes from
`P * inputs` to `H * inputs`; its reduction is `P/H`. The current profile
does not supply P/H. A matching-only cache covers too little measured
conductor work to be the main proposal.

## 5. Share joined-writer input selection and guide-only bindings

### Current versus new

The joined phase uses one scalar `(owner, initial, static result)` writer.
Selection depends on owner and complete initial, not on the selected
static result. It repeats selection and matching for each result.

```kotlin
// Before.
for (writer in scalarWriters) {
    for (input in frozenInputs(writer.owner, writer.initial)) {
        bind(writer, input)
    }
}

// After, in the same joined fixed point.
for ((owner, initial, freshResults) in writerGroupsWithNewOutputs()) {
    withFrozenMatchingInputs(owner, initial) { inputs ->
        for (input in inputs)
            bindCompatibleResultDeltas(initial, freshResults, input)
    }
}
```

Keep the complete initial, raw actual image, mark mapping, actual field
exclusions, and FLOW mark exclusions. Do not use the admitted exact image
as the actual image. ZERO writers still require the existing ZERO/reach
guards. Static-to-static bridge rows still do not enter writer binding.
Every new caller-bound writer result must re-enter the same fixed point.
Only fresh output deltas are processed; a packed group is not a reason
to replay all its old results.

Candidate enumeration can borrow a frozen directory view. Do not copy
the complete matched-input list into a new durable store for every
premise. Measure view/cache cardinality before retaining shared results.

### Example and fact trace

```java
void write(Box p) {
    C.f = p;              // p/U -> C.f/U
    C.g = p;              // p/U -> C.g/U
    C.h = p;              // p/U -> C.h/U
}
void caller(Box x) {
    write(x);             // Caller original I, actual p/U
    write(x);             // Same I and actual, different call location
}
```

Before: each of three writer rows scans both call references. After:
select inputs once for `(write, p/U)` and apply the compatible result
delta. In this guide-only phase, both call references export the same
relations `I -> C.f/U`, `I -> C.g/U`, and `I -> C.h/U` to the same caller.

The joined export contains no return continuation, suffix stage, alias
application, or live sink callback. Thus a second possible reduction is
to quotient guide-only inputs by:

```text
caller full MethodKey
caller full initial
complete compatible actual geometry / marks / E / mx / tail
existing ZERO-only eligibility
```

Call location and stage can be dropped only after proof that the
guide-only forced-DEMAND Pattern output does not observe them. Layer and
protection may be erased only after proof that this projection commutes
with transfer, cover, field cutting, and Pattern export. Until then,
retain those distinctions. The quotient must never be used in live
pubsub, where the continuation location matters.

### Proof and measurement gates

Prove the same seed-set least fixed point, including recursive callers,
all primitive observed writes, killed-write guidance, and final selected
summaries. Prove selection independence from output geometry. Then prove
packed-output transfer and the guide-only quotient separately. A failed
quotient proof must not block the smaller selection-sharing change.

Measure scalar writer rows versus complete owner/initial groups, full
caller refs versus quotient members, candidate scans, matching calls,
new output memberships, writer offers versus new writer admissions, and
temporary bytes. The old `duplicateInputs=0` uses the full call/stage
key and cannot answer these questions.

## 6. Stirling: measure native outputs before selecting a skip policy

Run-6 and run-8 have 98.90% and 99.48% empty current-demand call offers.
Saved matches still exceed 2.8 million and 6.5 million. This is permitted
by the selected policy: saved NORMAL summaries run before current-demand
gating. Current pubsub and static completion are negligible here.

Use a bounded diagnostic of existing runs' principal stages in the next
selected campaign:

```kotlin
// Count at existing owner boundaries. No fact-value retention by default.
recordNativeMatch(recordHeader, actualHeader)
recordActionStage(kind, inputLeafCount, protectionClass)
recordOutputAdmission(statement, offeredMemberships, freshMemberships)
// protectionClass: NONE, WHOLE, PARTIAL
```

Header-only counters are histograms. To establish equal-input work,
sample complete input and record identities within their owner/call scope.
These identities include geometry, marks, tails, exclusions, layers, and
protection, not only the header. Keep the sample bounded and release it
with the diagnostic owner. Do not retain a full cross-run fact history.

A small closed source trace must then distinguish:

```text
same input + same record -> identical transfer computed repeatedly
different inputs -> different output, already covered at storage
different inputs -> new output that must still be processed
```

Do not infer the first case from a low initial-key count. Do not add a
fresh-only replay cache. For equal complete actual images in one existing
work batch, pure record transfer may be shared, but every original caller
premise, cycle-protection step, source-to-Target discharge, and continuation
must remain. That is a later selection after multiplicity is measured.

One narrower candidate can be modeled immediately:

```kotlin
// Current protection transport.
operation(protectedPart, maskCollector)
operation(fullInput, attachCollectedMask)

// Candidate only when the mask equals the complete input.root.
operation(fullInput, markTaintOutputsProtected)
```

The mask-collector pass suppresses user-visible effects. Prove that the
one-pass branch preserves mark requests exactly once, all result geometry,
cycle protection, and non-taint outputs. Keep the two-pass implementation
for partial masks. Prove each operation has no hidden state that depends
on the suppressed first pass. Test ordinary and protected-input equality
separately because ordinary Facts equality omits protection.

WHOLE means equal complete taint memberships: all mark sets and exact/ANY
leaf kinds at every path, with the same input header. Formally, the
non-subsumable mask equals the complete `input.root` under the canonical
tree equality. Equal field geometry alone is insufficient. If each path
contains T and U but the mask protects only T, that input is PARTIAL.

This removes a pure traversal for wholly protected inputs. It is not yet
a proven large workload reduction. The broad protection stack includes
callbacks and cannot be used as the saved percentage. Measure the WHOLE
population and the direct AP traversal work before selecting it as a
main optimization.

## 7. Proof-first implementation and acceptance

After candidate selection, write the complete implementation spec and
constructive Lean model under [the proof guide](../../spec/proof-guide.md).
Use the c4 algorithm as the finite reference. An optimized run must yield
the same expanded paired demand, initial emissions with layers, summaries,
Target identities, and physical observation seeds. Every removed operation
needs an executable witness for an equivalent retained operation.

The implementation order should be:

1. Pin c4 and build small failing-work controls. Include mark-changing
   static paths, ZERO writers, partial masks, late subscriptions, recursive
   callers, and mixed NORMAL/DEMAND admission order.
2. Prove the semantic projection and complete worklist invariants. Separate
   optional sharing or quotients from the underlying algorithm.
3. Add meaningful multiplicity counters at owner boundaries and run the
   selected configuration. Do not put new atomics in the hot inner walk.
4. Implement one selected reduction. Compare semantic sets with the finite
   reference and run focused source/sink regression tests.
5. Run required core/JVM checks. Commit. Repeat the four-project campaign
   with the same selected limits, heap, inputs, and saved baseline.
6. Report per-run engine, joined transition, barrier, demand frontiers,
   complete/accepted iteration, finding differences, memory, and the exact
   number of operations removed. Collect a statistics-disabled validation
   only if that additional configuration is selected.

No proposal silently relaxes C5, changes a cleaner, skips an unresolved
exact demand, removes a non-subsumable flag, or makes NormalTarget usable
with DEMAND support. If an implementation needs one of those changes,
stop that design branch and expose the semantic decision.

The known missing baseline findings and Stirling exit-trace/location
changes remain acceptance issues. Fixing report attribution is a separate
correctness work item. It must not be hidden in a performance patch.
