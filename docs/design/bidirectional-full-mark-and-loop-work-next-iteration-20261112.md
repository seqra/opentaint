# Next iteration: avoid repeated FULL-mark and loop work

Status: proposal only. Runtime under study:
`472288cf34ddf75290e3fab4d6f5cbc0a366646c`.
Use the [current measurements](../reports/bidirectional-work-reduction-performance-20261112.md).
They replace earlier timing reports as evidence for this decision.

| Project | Latest reached | Latest completed | Accepted forward | Main observed limit |
| --- | --- | --- | --- | --- |
| Thingsboard | run-1 | none | none | OOM; concrete point relations and subscriptions |
| Conductor | run-8 | run-7 | run-7 | timeout; scalar local callbacks and loop observations |
| Stirling-PDF | run-11 | run-10 | run-9 | timeout; saved relation images before shallow restriction |
| OWASP | run-11 | run-11 | run-11 | run cap; expensive early form construction |

## 1. Scope and rank

No semantic change is selected here. All proposals must preserve the present
FULL-mode decoded relations, selected loop cuts/DROP/raw fallback, source/sink
observations and persisted-summary-first call policy. This includes replaying
saved summaries on **each offer**, even with empty current demand. Keep the
current field grammar/limits, C2/C5 rules, static protocol, cleaner behavior,
primitive policy, alias rules, literal protected/plain memberships and
nearest-boundary ownership. Do not use the run-11 cap to prove redundancy.

A private representation or compiler cache must not change public equality,
hashing, occurrence identity or join ownership. GROUP mode keeps its existing
fallback/known limitations. Do not add GroundingSupport, change field writes,
rewrite SoftReferenceManager, add WeakIdentityCache or change IR storage.
If a native equivalence proof needs different transfer semantics, stop that
candidate and obtain a separate behavior decision.

Rank is by the expected work/memory scope, not a promised speed factor:

| Rank | Proposal | Current -> proposed | Why it can matter / evidence limit |
| --- | --- | --- | --- |
| 1 | Keep exact FULL mark masks through neutral processing | Scalar original-mark work between packed stores -> one geometric transfer for an exact relation delta | Thingsboard has 12.02M concrete point memberships; caller pairs are 98.11% diagonal. Body sharing width is not yet measured. |
| 2 | Share complete loop-consumer queries; then select their images before expansion | Millions of scalar baselines/trials and saved images -> shared exact queries and certified consumer images | Conductor has >6.1M scalar queries/13.9M trials in two contexts; Stirling selects 24.15M saved records in one actor. Full-key multiplicities are unknown. |
| 3 | Reuse immutable lowering and completed form payloads | Repeated graph/plan construction -> reusable pure data with distinct occurrence wrappers | OWASP run-1/run-2 Java CPU is 47.54%/56.30% under form payload paths. Retention can increase heap. |
| 4 | Repair completed-probe cache integration | Complete stream reused only in its trial -> also becomes an old-cache provider | Source-proved missed reuse; identical-query frequency and total gain are unmeasured. |
| 5 | Compact remaining exact directories | Object-heavy postings/local inputs/pending images -> compact exact indexes | Measured byte owners; this saves representation, not a proved number of analyzer operations. |

The finding-location gap in section 7 is a separate correctness task. It is
not waived by these performance proposals. The broad native suite also has
20 known failures; preserve their assertions and track them separately.

## 2. Exact FULL mark processing

### 2.1 Change

The current caller backend already packs geometry and exact mark pairs. It
still exposes scalar source handles, reconstructs whole native snapshots and
runs later consumers through their existing handlers. Method point scopes
and local block inputs retain many separate original-mark memberships.

Extend exact packing to suitable local/point relations, then keep exact mark
relations through certified neutral transfer stages. This is **not** GROUP
abstraction. T and U stay different full marks. No new public fact/tail kind,
synthetic FLOW initial, companion analysis or cross-mark product is allowed.

For one complete geometry/header g, use:

```text
R[g] = (diagonal: MarkSet, byTarget: targetMark -> sourceMarkSet)
decode(R[g]) = {(g,s,s) | s in diagonal}
             union {(g,s,t) | s in byTarget[t]}

(T1 -> T1), (T2 -> T2), (T1 -> U)
  => diagonal={T1,T2}, byTarget[U]={T1}
  => T2 -> U remains ABSENT
```

The geometry contains original/conclusion bases and paths, tail/slot, E/mx,
layer, literal H, method/block/context, physical point/port, actor and call
stage/resume scope. Mark identity/metadata remain exact. If a transform reads
primitive metadata, cycle/protection state or any other varying property,
partition by that property or call its native scalar handler. Never use a
hash alone as the key.

Start with immutable, source-preserving neutral transforms already covered
by native execution guards: local copies, certified field transfer and
canonical delivery/deduplication. Existing bulk handling remains the baseline;
the change is to avoid splitting/reconstructing colors between these stages.
Calls/rules/cleaners/aliases are not automatically certified by storage packing.
Changing-mark composition can be added only after a relational-join proof:
`(s,u) join (u,t)` uses the **same actual u**, never all source/target pairs.

```text
processNeutral(scope, geometricDelta):
    split on every header/metadata property used by the native operation
    if no certificate for this operation and header:
        run existing handlers in existing logical order
        return

    transformedGeometry = nativeGeometryTransfer(geometricDelta.geometry)
    exactDelta = transportExactPairs(geometricDelta.pairs, transformedGeometry)
    fresh = existingPointUnion.addExactDelta(scope, exactDelta)
    deliver fresh through the existing queue/deduplication protocol
    # At the first non-certified consumer, restore COMPLETE native packets,
    # original handles and fresh/current distinctions before its callback.
```

Do not add a new batching barrier or combine arbitrary queued events. First
batch only an existing packet/delta. Keep actual logical handle order and
ownership at observable scalar boundaries. Do not retain a second standing
scalar mirror; temporary snapshots are allowed.

### 2.2 Example and safety obligations

```java
Object forward(Object p) {
    Object x = p;
    Object y = x.f;
    return y;
}
```

```text
Exact inputs at the same legal geometry: p.*/T1, p.*/T2, p.*/T3
Before: apply the same copy/read geometry separately for each original mark.
After:  evaluate geometry once; transport exactly {T1->T1,T2->T2,T3->T3}.
At a rule CM(y,T2): the native handler still receives the exact T2 witness.
An assignment U from T2 adds only T2->U, with the same protection decision.
```

This schematic example uses the current native field operation as its oracle;
it does not assert that every STAR read is legal or NORMAL. Keep the operation's
actual exclusions, tail and layer in every decoded result.

Required constructive laws:

```text
decode(encode(S)) = S
decode(add(R,delta)) = nativeUnion(decode(R),delta)
decode(fresh(R,delta)) = nativeFresh(decode(R),delta)
for certified op: decode(batchOp(R)) = nativeOrderedOp(decode(R))
```

The final law must include semantic effects and order where native consumers
observe order, not just a set of APs. Source AND joins must still await the
whole condition; run-1 emits all contributing origins and ZERO only for a
complete ZERO-supported cube. A selected cleaner survivor and T->U->T cycle
must make the same protection decision. Pass rules must not create protection.
Protected/plain memberships cannot subsume or upgrade each other. Unsupported
ND/control/static/request/alias/rule operations keep native fallback.

Use the existing CallerMarkRelations model as a component, not proof of the
new point/processor binding. Add constructive Lean transfer/compose/freshness
models first; prove the new native boundary with differential TDD. Tests must
cover two positions with different marks, changing pairs, primitive partitions,
H/layers, E/mx, source and cleaner effects, late publications/requests, both
arrival orders, independent scopes and release/queued snapshot safety.

Before projecting a speedup, collect body geometry width and count how many
neutral operations become one geometric operation. Caller mean width 13.54
is not a prediction of 13.54x body or memory savings.

## 3. Complete loop-consumer planning

### 3.1 Fixed observation

For every scalar lane and tested prefix, preserve the complete observation:

```text
O(q) = (adjacent C2 families,
        repeat C2 families,
        enclosing results after saved adjacent composition + paired C5)
```

Keep the existing C2 descriptor equality: scope, physical entry, family, full
pattern and layer. Keep H in the lane/query context and in enclosing DATA
keys where it already exists; do not add H to AdmittedInitial or change public
C2 equality. Keep all companions, typed controls and every original ND member.
Do not union different lanes before comparing raw and trial observations:
an extra result in one lane must not hide behind another lane's baseline.
Keep all current ZERO/Reach/run-1/non-growing and source/control bypasses.

Current code prepares C5 plans but still executes them millions of times.
Proposed step A shares exact query cells and complete components within the
existing frozen owner quantum. A key includes demand/record view identity and
epoch, direction, method/context, block/ports, complete original premise,
actual pattern/header, E/mx, marks, layer, H and policy. If a key cannot be
proved complete, use the current scalar path. A candidate MAY cut can match
off-path records that the raw fact cannot match: record selection must cover
all tested prefixes, not just the raw path.

```text
restrictPacket(packet, P, frozenViews):
    apply the unchanged bypass tests
    lanes = nativeScalarLanes(packet)
    plan = prepareCompleteConsumers(P, frozenViews)
    cells = internExactQueryKeys(raw and existing proper cuts for each lane)
    c2 = completeNativeC2OnceForEach(cells)   # includes empty/companion answers

    for lane in original order:
        raw = cells.raw(lane)
        viable = []
        for k in existing proper-prefix order:
            trial = cells.cut(lane,k)
            if witness e in c2[trial] with e not in c2[raw]:
                reject only this k with that exact witness
            else:
                viable += trial

        if c2[raw] is nonempty and every proper cut was rejected:
            select raw                       # O(raw) cannot be empty
            continue
        baseline = fullObservation(plan,raw,reuse=c2[raw])
        if baseline is empty:
            DROP this lane
        else:
            select first viable trial with
                fullObservation(plan,trial,reuse=c2[trial])==baseline
            if none: select raw
    union results through the unchanged canonical accumulator
```

This removes duplicate complete queries and, in an all-bad case, the raw
saved/enclosing observation. It does not change the selected budget or need
monotonicity of bad budgets. Missing-only or enclosing-only differences still
require full equality. Retain the saved Target observer and actual saved replay.

For n lanes, b proper trial budgets and v consumer views, the current path
can perform O(n*(b+1)*v) admission queries plus saved/C5 work. Sharing needs
O(n*(b+1)) exact-key references and evaluates u unique native queries, where
u<=n*(b+1)*v. The extra one is the raw baseline.
It improves work only when equal keys/components occur, or negative
certificates skip enclosing observation. No current counter measures u.
Plan/key storage must be released at the existing quantum/packet boundary.

### 3.2 Avoid enumerating long images

Step B is the larger opportunity. Compose a saved relation family with the
complete consumer plan before enumerating each long applied path. Emit the
exact observation components needed by step A. Preserve raw/lane identity and
all distinct consumer images, even if one C5 output is identical:

```text
Stirling run-9: two different depth-7 path words
  ret.content.content.content.bytes.bytes.bytes.bytes.[any]/T91
  ret.content.content.content.bytes.<string-bytes>.<string-bytes>.bytes.[any]/T91
both have C5 image ret.content.[any]/T91 under one output row.

This alone is NOT a removal certificate.
Compare their adjacent, repeat and ALL enclosing components independently.
Share a component only after exact complete-key/effect equivalence.
```

First implement this as a pure observer optimization with native fallback.
The larger extension to real saved replay requires the stronger law:

```text
fastObserve(plan, relation, input) == nativeObserve(nativeApply(relation,input))
fastRealReplay(...) == nativeRealReplay(...)     # results AND semantic effects
```

Real replay can issue requests, trigger rules and feed another loop step.
Do not suppress it because the current DATA selector is empty. Method-entry
source rules can convert DATA to Target/Zero before restriction. Preserve the
cookie/descendant-entry-source regression. Keep the root/source/control guards
until the entire path has a native proof. A fixed output base is insufficient.
An optional first pure prefilter can be restricted to certified nonroot,
source-free DATA readers; same/opposite-direction readers need separate proofs.
If the certificate is not available, retain the complete native path.

### 3.3 Proof status and counterexamples

Seven constructive local laws are supplied in
[ObservationPlan.lean](../../spec/lean/proposals/loop-observation-work-20261112/ObservationPlan.lean):
extra witness membership/absence, rejection, first-choice preservation,
all-bad/no-cut, nonempty-C2 raw return and exact-key congruence. They prove
finite selection mechanics. **Native program factoring, key completeness,
component sharing and real replay equivalence remain open.** No runtime
activation is authorized by those local laws alone.

Native TDD must cover complete primary/companion families, empty baseline,
late extra, missing-only and enclosing-only differences, all-bad and
non-monotone budget tables, MAY/MUST/STAR/EXACT, E/mx, H/layers/ports,
source/Target conversion, both saved directions and ND origins. Differential
checks must compare each lane and selected budget, not only the final union.
Measure raw/trial cells, unique complete keys, baseline/enclosing work avoided,
actual saved applications, C5 work, allocation/GC and retained plan size.

## 4. Reuse form construction

Current engine and report guards clear the `bidi-method-forms` managed group
on every successful exit, including low-memory runs. Later reverse payload
misses reconstruct forward forms first. Providers cache resolved rules;
compiled predicate graphs are a separate cost. OWASP is the principal case.

Two independent changes are proposed:

1. Let a targeted analysis-owned group of **completed immutable form payloads**
   survive successful guard exit. Retain existing pressure eviction and
   explicit analysis close/release. Keep other manager groups unchanged.
   Retain no builder closures, old actors, packets or run-1 setup catalog.
   Do not rewrite SoftReferenceManager or add WeakIdentityCache.
2. Share pure lowering data and ordered predicate DAGs where complete keys
   are equal after site-dependent basic evaluation. Keep separate native
   occurrence wrappers/IDs. Remove a repeated normalization only when its
   producer explicitly supplies the canonical form and parity is proved.

The first change can remove later reconstruction, not first-run compilation.
The second can remove equivalent first-run lowering. A key must preserve rule
view/epoch, binding/basic-fold context, generated/primitive marks, result base,
source actions, literal order/ordinals, TemporaryKey/OperationId/stage data and
all other inputs. Unsupported keys stay unshared.

`RulePredicate`, SinkRule and source occurrences have identity-sensitive users.
Do not intern those public wrappers or change their equality/hash. Joins remain
keyed by the existing occurrence, statement, actor and scope. Share private
immutable graph data only. Backward sink plans must remain: ZERO source seeding
uses their occurrence lookup. Never drop backward lowering as unused.

Proof/tests: erase shared metadata and get the same ordered lowered program;
rebuild after pressure eviction equals the old payload; distinct occurrences
remain distinct join/report owners; guard success, pressure cleanup, cancellation
and analysis close release the correct owners. Weak-reference tests must show
that surviving forms do not keep released run state alive. Measure first builds
versus rebuilds, unique DAGs, compile/reverse work, engine time and retained bytes.
Do not trade the Thingsboard OOM for a larger pinned cache without measuring it.

## 5. Complete-probe cache repair

The current complete pure stream bypasses the cache writer used by ordinary
full observation. Same-trial reuse works; cross-query reuse can be lost.
Use the same key, capacity and lifetime as `LoopQueryScratch.admissions`:

```text
on a probe that completes ALL consumers:
    keep (view,policy,actual,orderedCompleteEmissions) for each native query
    keep explicit empty completed answers too
    when materializing a completed answer for the bundle:
        if size<=128: remember under the existing 32-key quantum cache policy
on partial/aborted/unsupported stream: do not insert an incomplete answer
on liveness-skipped consumer: do not invent an empty native answer
on quantum end: clear as now
```

Cache insertion must not count a second query, change native answer order or
replace the exact view/policy/H identity. Oversized answers remain only in
their per-observation bundle. A flat list of nonempty descriptors lacks the
necessary provenance and cannot reconstruct a complete empty view.

Test two identical completed queries: current native starts=2; repaired
starts=1/hits=1, with the same full observation. Also test complete-empty,
later-consumer abort, late extra, oversize, H/view/policy changes, eviction
and clear. The proof is memoization of the same pure native function.
Measure repeated exact keys before estimating the gain; 39.69M native starts
are not all caused by this omission.

## 6. Smaller storage and measurement work

These candidates are independent of changing the analysis algorithm:

| Candidate | Current -> proposed | Native boundary / measured limit |
| --- | --- | --- |
| Caller source postings | Primitive maps containing LinkedHashSet objects -> exact inline/single-cell or compact primitive postings | 568.64 MB in current source-posting owners; preserve order, deltas, handles and multi-cell cases. Not all bytes are reclaimable. |
| Local block input packing | 931,888 scalar groups -> the same exact family/pair representation where eligible | 407.16 MB retained. Reuse proven snapshots/order/fallback; no new input subsumption. Can share the storage stage of proposal 1. |
| Pending static images | Mark->equal immutable root entries -> exact header/root->mark-set buckets plus mark lookup | 139.45 MB point maps; 92.50% of pending entries lie in one-root rows. Different mark images stay separate; PointReady removes before callback. |
| Unused replacement indexes | Point stores eagerly allocate indexes although replaceCovered=false -> lazy allocation only when the native path uses them | Across ALL modes the indexes/sets total about 501 MB; per-mode reclaimable bytes are not measured. Preserve used summary indexes. |
| Profiling samples | Per-method sample deques -> a declared global diagnostic sampling budget/top-k view | Copied samples retain 434.99 MB. Change measurement sampling only, not fact retention or pending requests. Report the lost sample coverage. |

The profiling proposal is a bound on optional copied diagnostics, not a bound
on pending semantic state. Keep exact global counters. Do not use changed
sampling to claim a transfer-work reduction. Collect a separate representation
proof for each store; the current caller model does not prove a new index layout.

## 7. Separate finding provenance repair

Stirling's shared synthetic exit does not retain the witness return, and the
current exporter has no path. Eight exact baseline return locations therefore
have different current return candidates; eight additional full-method keys
remain unclassified. The report does not establish exact-location parity.

Propose retaining actual witness return/provenance through nearest-boundary
Target summaries and report export. Keep report IDs, transfer and confirmation
rules unchanged. A last/first-return heuristic is insufficient. Add a minimal
method with success/error/null return arms and distinct source witnesses;
assert the actual return region and source path. Prove that added metadata
does not change edge equality, subscriptions or sink identity. If it must change
report identity, specify that semantic/report contract separately first.

## 8. Delivery and experiment plan

Use proof-first constructive Lean models, then red native differential tests,
then the narrow optimization, then the full suites. Preserve failed attempts
and source bindings. Do not activate a wider fallback-free scope on the strength
of a generic set theorem. No proof may rely on the temporary iteration cap.

Land candidates independently so a regression has a clear cause. A practical
first sequence is: repair completed-cache insertion; census exact body widths
and query multiplicities; implement certified FULL neutral batching; implement
shared pure loop queries; add consumer-image pushdown only after its proof;
then form/cache lifetime work and the smaller storage changes. Rank and landing
order differ because the cache repair is narrow and independently testable.

Repeat only the configured FULL project scans and source Gradle rules pipeline.
Reuse the fixed baseline. Collect profiles with explicit phase labels and dump
the heap on guard OOM. Optional per-feature diagnostic controls require a
separate selected experiment; no new configurations are assumed here.

| Question | Required evidence |
| --- | --- |
| Did we remove mark-level work? | Native equality plus geometry executions versus logical source pairs, body width, scalar fallback, fresh deltas and decoded snapshots. |
| Did we remove loop work? | Same raw/trial selected results; unique query cells, complete components, observer/replay applications, C5 row attempts and GC. |
| Did we avoid long-path enumeration? | Exact same consumer/effect trace; pre-expanded versus emitted paths, path/depth/mark/H/layer distributions. |
| Did we improve memory? | Retained owner bytes and live qualified memberships, source postings/local inputs, profiler bytes separated from core state. |
| Did we preserve findings? | Exact rule/URI/region and witness validation; confirmed/provisional states at common completed frontiers. Keep Stirling's eight open location cases visible. |
| Did the run advance? | Latest reached, latest completed, accepted forward, stop reason and all per-run engine/barrier/frontier values. |

Use operation removal as the acceptance target. A twofold workload reduction
must be shown by actual avoided native operations at an equivalent completed
frontier; sample percentages, packed pair counts or a smaller final demand set
alone do not establish it. Timeouts/OOM and cap stops must remain explicit.
