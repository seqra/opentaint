# Prepare and reuse loop consumer queries

Date: 3 November 2026. Status: **SELECTED DESIGN — no implementation selected**.
Reference source: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
This is point 2 of the next proposal. Points 1 and 3 have separate owners.
Follow [impl-proposal-guide.md](../../spec/impl-proposal-guide.md) and
[proof-guide.md](../../spec/proof-guide.md).

## Scope

Selected major semantic changes: **none**. Keep the complete loop observation,
restriction choice, native saved application, work accounting and output order.
Change only repeated query work. No ZERO, Target, source permission, layer,
protection, field, C2/C5, mark-owner, report or publication policy changes occur.
Do not change equality/hash fields of Facts, DemandPattern, Record or PremiseKey.
Private plan/key objects carry the new metadata.

Use two mechanisms:

1. Compute each scope's C2 admissions once. Use that ordered result for both
   labelled and unlabelled families. Add a bounded synchronous C2 memo for the
   current method-owner quantum.
2. For a fixed complete original, actual exit, policy and frozen local view,
   check each C5 entry predicate once. Retain a private checked ticket or rejected
   decision. Apply the unchanged output restriction for every new raw output.

Do not cache complete LoopObservation/enclosingResults values in this design.
They may be large; their hit rate is unknown. Full-query result caching is
**deferred**. The selected mechanisms remove duplicate C2 calls and repeated
fixed-entry checks even when every complete raw-output query key is different.
They do not promise a project speedup.

## Current native path

`MethodBlockRuntime.observe` builds adjacent and repeat ScopeDemandViews from the
run's frozen DemandStore. It calls each family through `initials`, then calls both
again through the labelled-admission callback. `LoopConsumerObservation.observe`
also composes saved adjacent records through LocalRelationApplication, applies
the enclosing metadata adapter, normalizes the full pair, runs enclosing C5, and
checks saved Target metadata. All three families enter LoopObservation equality.

`DemandStore.intersect` keeps paired rows and actual scope exit. For each original
member it visits by-entry row IDs that match the current raw output's by-exit IDs.
`offerDataPair` calls `ops.restrict` and then applies the row's existing budget:

```text
budget = if exitDepth >= policy.fieldLimit then policy.fieldLimit else exitDepth + 1
```

`ApOps.restrict` calls Demand.kt `restrictFacts`. Protection transport invokes the
plain restriction on its parts. `restrictRaw` calls Reference.kt `restrict` for
each leaf. That scalar function first calls the raw-output-independent predicate
`policy.canStoreInitial(d.entry, member.toPattern())`, then calls the already
existing `restrictConclusionOnly`. This repeats the entry test across leaves,
protection parts and new raw outputs of the same fixed original/row.

## Owner quantum and bounds

Use the existing `MethodBlockRuntime.work(quantum)` ownership interval. A private
scratch object is active only during that call; clear and detach it in `finally`.
The work reservation stays held. No new queue, deferred action, coroutine, weak
cache, global cache, rejected-fact archive or pending-work counter is added.
If observation occurs outside an active owner quantum, execute the native path
synchronously. Do not add a new assertion or failure for that case.

Use separate insertion-ordered scratch maps. On capacity exhaustion clear the
map on the owner thread before inserting the current entry. A miss always runs
the native query/plan creation now. A failed/oversize preparation returns the
native fallback now; it never publishes a partial plan.

| Scratch | Entry limit | Per-entry admission limit | Lifetime |
| --- | ---: | ---: | --- |
| C2 answers | 32 | 128 AdmittedInitial references | one owner quantum |
| C5 entry plans | 32 | 2,048 candidate member/row references | one owner quantum |

C2 stores at most 4,096 admission references. C5 stores at most 65,536 row
decisions/references. These are reference-count bounds, not byte or GC bounds.
A C2 answer above the limit is used for this observation but is not retained.
An oversize C5 plan is discarded and uses native intersect; a bounded negative
plan marker may prevent a repeat preparation attempt in the same quantum.
Do not copy DemandPattern rows or retain raw output/result histories in a plan.

Every logical query keeps its entry cancellation checkpoint, including hits.
Exceptions and cancellation propagate through the same owner call. The scratch
is then discarded. Cache work does not add, remove or postpone actor work units.
The existing ready/pending/link queues and `used++`/completion checks stay intact.

## C2: one ordered answer bundle

Use the existing ScopeDemandView.initials API. Change only the internal
LoopConsumerViews admission callbacks to a `beginAdmissions(actual)` factory.
It returns a private per-observation `C2Answers` with `adjacent()`, `repeat()` and
`labels()` getters. Each family getter executes its scope loop once and stores
that family's unlabelled set plus labels. The label getter concatenates those
two ordered label sets. It does not issue another C2 query. Keep the observer's
current phase order: adjacent getter, saved AL/Target work, repeat getter, then
labels getter. This avoids moving the repeat query ahead of saved application.

Create this bundle even without an active quantum memo. A family result above
the memo weight limit still supplies both projections within its current
observation. The scratch limit controls reuse across observations, not whether
the two projections share the current native answer. No extra result history
survives the observation.

Preserve the current native AdmittedInitial order and layer. Each family getter
builds both projections from the same ordered native answers before freezing:

```kotlin
for ((scope, view) in adjacentDemands) {
    val answer = quantumC2?.getOrCompute(view, policy, exactKey(actual)) {
        view.initials(actual, policy)
    } ?: view.initials(actual, policy)
    for (admitted in answer) {
        adjacent += admitted
        labels += LoopLabelledAdmission(scope, ADJACENT, admitted)
    }
}
// Repeat the same loop for repeatDemands, filling repeat and REPEAT labels.
```

This is proposed pseudocode, not an implementation. The cache returns a present
empty answer as a hit; it must not use empty or null as a miss marker. Cached
answers use an unmodifiable LinkedHashSet copy after the size check. Keep exact
first-occurrence order when building both unlabelled and labelled sets. A match
in adjacent does not skip repeat, enclosing composition or Target metadata.

A C2 memo key has the exact frozen ScopeDemandView identity, policy identity,
method-owner quantum identity and complete input packet key. Identity wrappers
compare references with `===`; hash collisions alone never establish identity.
A packet key contains ordinary Facts equality **plus** the full
TaintTree.nonSubsumable mask. A non-null Boolean is not enough: two positive masks
can protect different memberships. Ordinary equality already includes layer,
shape/tail, fields, full mark payload, field E and FLOW mx. Do not erase them.
Use immutable canonical objects; never mutate a packet/key after insertion.

## C5: actual fixed-entry planning

The new APIs are private/internal capabilities. They do not add methods to the
public FrozenCompletion/StaticDemandView/ScopeDemandView contracts. Point 3 may
change frozen storage while preserving those contracts and iteration order.

### Checked AP ticket

Add an internal factory beside Demand.kt's restriction functions. Its ticket has
a private constructor and immutable `(memberPattern, pair, policy, AP/catalog)` fields.
It is accepted only by the **same** existing predicate:

```kotlin
EntryDecision prepareEntry(ops, memberPattern, pair, policy) {
    return if (!policy.canStoreInitial(pair.entry, memberPattern)) Rejected
           else Accepted(EntryRestrictionTicket(memberPattern, pair, policy, ops.manager))
}
```

Do not replace `canStoreInitial` with `canEmitInitial`, `insideDemand`, an initial
membership lookup or a new preimage test. `canStoreInitial` restores the existing
NORMAL FLOW EXACT preimage of a stored STAR summary key. Keep that fallback.

Factor the existing native body, without changing it:

```text
restrictRawAfterAcceptedEntry(ticket, part):
    for leaf in ops.leaves(part), in the same order:
        restrictConclusionOnly(Conclusion(leaf.fact, leaf.exclusion,
                                        part.layer == DEMAND), ticket.pair.exit, ap.marks)

restrictFacts(ticket, raw):
    transportProtection(raw) { part ->
        pack exactly as current restrictPlainFacts:
            restrictRawAfterAcceptedEntry(ticket, part)
            normalizeFlowSummaryConclusion
            factsOf + existing GroupKey mergeAddDelta
    }
```

Keep transportProtection outside the same plain-part packing operation. Do not
replace it with a protected/unprotected flag. The existing scalar `restrict` and
ordinary non-prepared callers retain their entry guard. Only the private accepted
ticket may call the factored no-entry body. A rejected decision returns the same
empty selection without walking leaves/protection parts.

### DemandStore local plan factory

Implement preparation inside DemandStore, where Query, MethodDemandIndex,
ScopedDemandIndex and rowPorts are already private. It can read these exact
native structures without a new graph/preimage API. An internal capability on
its anonymous scope-view object exposes preparation to the internal consumer.
An unknown view returns `NoPlan`, then calls its original intersect.

Prepare only when `policy.run >= 3`, `!hasStaticCompletion` and
`!hasSharedStaticCarry`. Keep exact native fallback for run 2, static carry or
completion, unsupported views, ZERO/control originals and Reach/Target queries.
These are performance gates, not permission gates. Unsupported cells still run
the identical native operation. No static closure is built eagerly.

For eligible DATA, bind the actual normalized **complete** original, method,
physical scope, actual exit, policy/catalog and frozen snapshot identities. This
occurs after the current enclosing metadata adjustment and
`normalizeFlowSummary(ap, original, adjusted)` call. Keep the raw complete original
for native saved application/cycle protection and enclosing-result headers.
Do not merge different originals solely because a summary normalizes to STAR.
Ordinary post-application preparation takes each actual normalized member's
`toPattern()`. The pre-application shortcut below uses Pattern-only templates and
checks that the actual normalized member has the same pattern before it uses a
ticket. It does not call `ap.initial` for a hypothetical result.

Build ordered plan entries as follows:

```text
for member in completeOriginal.forEachMember order:
    for id in local.byEntry.lookupPrefixes(member.base, member.path) order:
        retain the current exact scope/rowPorts exit test
        row = local.rows[id]                       // keep original row reference
        store (member, id, row, existing exit guard,
               prepareEntry(ops, member.toPattern(), row, policy))
        stop and return NoPlan if the row-reference bound is exceeded
```

Do not collapse IDs, members or normalized keys. A row reached through two ND
members keeps both positions. Keep nullable/typed-ZERO exit guards and their
current outer `offer` behavior; only ordinary DATA exits use a prepared ticket.
The plan key includes the actual complete normalized original, actual exit,
view/snapshot identity, policy identity and owner. Plan equality adds no field to
DemandPattern or the row's existing equality/hash.

### Apply to each raw output

For each apply, run the unchanged RuntimeDataDomain guard and native control
handling. Compute `outputIds` from the existing by-exit visitAround calls on the
new raw output leaves. Walk the plan in native member/row-ID order and test
`id in outputIds`. This preserves output-dependent prefix compatibility; entry
preparation is not a geometry hit or C5 permission shortcut.

For each output-matched plan row, keep the current outer statistics/sample hook,
paired row and row-specific budget. Rejected decisions take the existing rejected
row result path. Accepted tickets call the factored restriction above, then apply
the **same** FL+1 clamp, `ops.limit`, protection-aware ExactDemandResults insertion
and sample hooks. Data must exhaust every row; do not add a first-hit stop.

This plan stores entry decisions even for rejected rows so diagnostic row-attempt
order/meaning can stay unchanged. Native entry-check counts now differ; add
explicit plan-check/hit/miss/fallback counters. C2 native-call counters remain
native-call counters; logical query counts and cache hits use separate counters.
Do not interpret fewer callbacks as fewer semantic rows or actor work units.

### Root and BlockBoundaryDemandView composition

Root plans use the same DemandStore Query(method) as root intersect. Non-root
plans use the exact physical scope and exit. BlockBoundaryDemandView retains its
physical-then-normal ExactDemandResults composition. ZERO/control originals and
all `acceptsTarget` calls use the current native path, including its normal-output
port union, exceptional normal-ZERO HACK and run-2 static-shortcut checks. No DATA
port alias or new ZERO route is introduced. This explicit fallback avoids a new
control planner while optimizing later local DATA C5.

### Empty local DATA plan before saved replay

An entry-rejected row cannot produce C5 DATA for any raw output. A plan with no
accepted DATA row for a known output base therefore has an empty DATA result for
every output path, layer, field E, mark and protection mask at that base. This is
an entry proof, not a failed output lookup or a new field-preimage algorithm.
Retain exact paired IDs and actual enclosing ports in this certificate. If one
relevant plan is unsupported, oversize or nonempty, replay natively for that port.
Do not treat `NoPlan` or a cache miss as an empty certificate.

Use the certificate to omit saved-record AP application only in this first
DATA-only cell:

```text
run >= 3; local C5 with no static completion/carry
non-root enclosing scope; adjustEnclosingData is the native identity adapter
record.direction == mode.direction; record.premise.tail != ANY_TAINT
original is non-ZERO; actual is FlowTree or TaintTree
every original member is non-ZERO
actual kind agrees with complete original.isFlow
record is an admitted native DATA record, with valid K6 kind and non-ZERO base
record conclusion is FlowTree or TaintTree; its output base is known
every relevant exact enclosing-port DATA plan has an empty certificate
```

Here `Summary.kt.leafKinds` compiles every edge to the record conclusion's base.
`EdgeApplication`/`Results` preserve that non-ZERO base for DATA results. Grafting
and protection attachment keep the DATA kind. With no MUST or run-1 policy lane,
the LocalRelationApplication sink cannot turn this cell into Reach or Target.
The observer's `markRequest` callback has no effect; actual replay is unchanged.
These native adapter facts are source-backed design obligations, not a claim
that Lean verifies the Kotlin code. `RuntimeDataDomain.packet` checks legal
bases; the K6 record kind check is in `RecordStore.checkNativeRecord`.

Before AP application, make only immutable Pattern templates for the complete
parent original. If the guarded input/output kind is FLOW, change its single
EXACT member tail to STAR, as `normalizeFlowSummary` does. Keep its base, path,
mark and E. Otherwise keep the complete non-FLOW/ND original unchanged. Call the
exact `canStoreInitial` predicate on these templates. Do not intern hypothetical
InitialAp, Facts, query roots or graph nodes. Plan membership uses each template
in the same native member order; member geometry is unchanged by this tail step.
If application runs, compare the actual normalized member patterns with the
templates before using their tickets, and pass the actual normalized whole
premise into EnclosingResults. A failed validation takes the native guarded
restriction path; it does not drop an output.

Keep native replay for reversed views, MUST records, Reach/Target-capable cells,
ZERO originals, root metadata adapters and any unknown kind/output base. In
particular, backward non-ZERO Reach can become DemandTarget in the native sink;
an empty DATA plan gives no permission to suppress that callback. Saved Target
iteration, adjacent/repeat C2 and their labels always run, even if every DATA
replay has an empty certificate. Keep their order. The per-record cancellation
checkpoint and dedup position still run before the shortcut. Count the shortcut
separately from native application calls.

Preparation can inspect entry rows that no raw output would visit. It can cost
more on a one-off all-miss query. The bounds limit that work; a negative marker
only avoids repeated failed preparation. The proven work reduction applies to
duplicate C2 projections and repeated eligible entry checks/empty DATA replay,
not every call or the total project run.

## Saved AL application and complete observation

Do not replace saved-record application with a matching Boolean or C5 plan.
Keep LocalRelationApplication.applyRecord/applyRecordView, native MUST lanes,
pending demotion, opposite-direction record views, cycle protection and the
**whole** B original. Keep `(RecordLeafView, protected)` dedup and each real
record/enclosing exit. The observer's markRequest callback remains a no-op;
actual replay keeps its ordinary request behavior.
The preceding empty-DATA certificate is the sole permission to omit an observer
application in this design. Its narrow cell does not alter these native paths.

Saved ND Target arms are metadata only. Actual local ND execution still joins all
arms through applyCombination. Saved ZERO -> NormalTarget adds no new effect.
NormalTarget still needs FORWARD, NORMAL and the current not-already-saved test.
DemandTarget still needs exact enclosing paired acceptance through native target
APIs. Preparing a DATA C5 row does not grant Target or publication permission.

Keep EnclosingResults headers `(scope, exit, complete original)` and exact
`LoopObservedMember(pattern, layer, nonSubsumable)` union. Do not use Facts.equals
as full observation equality or drop protection before union. All adjacent,
enclosing, repeat and labelled families remain in the signature. The existing
LoopOutputRestriction still drops an empty observation, tests positive budgets
in ascending order, chooses the first equal complete signature and otherwise
keeps raw. Bounds, bypasses and Work completion remain unchanged.

## Proof and implementation gates

The [constructive model](../../spec/lean/proposals/loop-consumer-query-reuse-20261103/README.md)
proves entry factoring for arbitrary native output/protection/normalization
functions, ordered row equality, exact C2 projections, complete signature
preservation, bounded synchronous memo correctness and finite adaptive-query
program equivalence. Its CEGAR witnesses cover normal FLOW preimages, crossed
pairs, ND metadata versus AND execution, masks omitted by Facts.equals, complete
cycle originals, ZERO/Target and fallback gates. It proves Pattern-template
equality under the explicit kind guard and empty-DATA replay removal while
exhibiting the Target-capable counterexample. No unique-hit premise is used.

The finite model does not kernel-verify Kotlin AP stores, native concurrency or a
future adapter. During implementation, use native tests first for all witness
cells and fixed-context plan/public/native fallback differential checks. Include
multiple compatible rows/exits, multiple original members, varying FL+1 depths,
all protection masks/layers and exception cleanup. Check memo all-miss/eviction/
oversize/empty-hit cases and both owner-quantum boundaries. Then run the required
DATA-only empty-plan differential tests, native Target-capable/MUST/reverse/root
fallback controls and exact template/actual normalization tests. Then run the
required native suites and project quality/performance gates. No Kotlin implementation,
Gradle/analyzer run, profile experiment or commit is part of this design work.
