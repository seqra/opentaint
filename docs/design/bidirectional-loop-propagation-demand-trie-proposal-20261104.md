# Loop propagation with demand tries

4 November 2026. Unified proposal. No analyzer implementation change.

Reference runtime: `e558b496acf82de6ff136325d58f3d90ee5b8559`.
Latest measurements: Conductor reached run-6 / completed run-5 / accepted
run-5; Stirling-PDF reached run-8 / completed run-7 / accepted run-7.

## 1. Purpose and scope

Reduce repeated work when a fact crosses a loop boundary. Use demand tries to
select relevant rows, share identical output restrictions, and skip prefix
cuts that are known to fail.

Keep the current analysis semantics: saved summaries apply before current
demand admission; summaries are restricted before storage; real ND rules
require all arms; growing loop results use the first cut whose complete
observation matches the raw result. Fields, marks, layers, exclusions,
protection, Target handling and source permissions keep their current rules.
There is no selected major semantic change. New query metadata does not change
Facts, premise or record equality/hashing.

A region is `B = BL ; L ; AL`. The adjacent region after L is AL forward and
BL backward. It can contain another block hierarchy. One method analyzer owns
all blocks, which share the original registers and physical control ports.

Keep these two edges separate:

- The loop summary `I -> O` describes one body traversal.
- Applying it to an offered fact produces `P -> F`, where P remains the whole
  enclosing original. P is not replaced by the loop-local initial I.

C2 returns initial commands allowed by demand. C5 intersects a complete
proposed summary with paired entry/exit demand. FL counts fields and array
elements. A local link identifies the parent scope, boundary point, whole
original/layer and child entry scope.

## 2. State and indexes

| State | Contents and use |
| --- | --- |
| Incoming demand | Immutable paired entry/exit rows for the current run |
| Entry demand trie | Entry patterns, including DATA entries from control/Target rows; used by C2 admission |
| Prepared output plan | For a fixed whole original and actual exit, accepted paired rows grouped by identical full exit pattern and budget; its trie selects output programs |
| Saved summaries/Targets | Immutable NORMAL records and Target metadata, with native direction and ports |
| Current loop summaries | Live, C5-admitted rows; only fresh deltas are published |
| Standing inputs | Current admitted input groups for the exact parent/child entry link; new publications join these inputs |
| Completion store | Applied, retained results; only fresh deltas are routed |
| Query session | Temporary plans, scalar buckets and observation data for one restriction; no persistent raw-fact history |

Every index belongs to its exact method, entry scope, direction and snapshot.
C5 also fixes the actual exit and whole original. Current summaries, inputs and
ND joins are mutable. Demand and saved-summary query data are immutable during
the run. Existing bounded plan caches remain optional accelerators.

### Demand trie

Share field-prefix nodes across marks. A node has child accessor edges,
terminal payload lists by required mark, and one subtree ANY-demand witness
per required-mark profile. Terminals refer to existing patterns/programs.
Keep a shorter terminal even when the node has deeper children.

C2 selects mark profiles with native `markSub`; C5 uses native `marksMeet`.
They are different rules. Native predicates still validate tails, exclusions
and policy. A selected trie payload alone grants no permission.

The precision walk follows the raw fact's path through compatible ANY-demand
cursors. At the first missing child, retain that field and stop. This gives
the longest shared demand prefix plus one distinguishing field. Reaching the
raw end keeps the raw tail/layer. It does not force a same-path ANY fact.

Only include scopes whose existing admission guards allow this base. A dead
local cannot supply a witness. The walk does not scan descendant payloads.
Unsupported accessors or unknown adapters supply no skipping certificate.

### Boundary liveness belongs to summary emission

Check the conclusion base of the block summary before it enters admitted
summary storage or publication. This check uses the summary's own block,
direction and exit. Applying an already published summary in an enclosing
context does not repeat that boundary check.

A shared normal loop exit can lead to both repeat and leave routes. Compute
its permitted routes before publication: a local can be live on repeat and
dead on leave. Preserve those destinations as block/exit/base routing metadata,
separate from AP equality and hashing. Application uses that prepared route
information without testing boundary liveness again.

Prepare saved summaries for the current direction in the same way before
replay. For a reversed view, use its reversed exit and conclusion base. Do not
assume that forward-output liveness proves backward-output liveness, and do
not modify the persisted record.

Each enclosing block checks its own newly emitted summary before publication.
C2 entry guards and pure observer view guards keep their existing roles.

## 3. Relation to function-call handling

**CALL** means the same call/AP rule or primitive is reused. **LOCAL** means
that mechanism has a small block-specific adaptation. **LOOP** means handling
with no ordinary function-call counterpart. These labels describe reuse;
they do not imply that every LOOP mechanism is newly introduced here.

| Mechanism | Category | Reuse or difference |
| --- | --- | --- |
| Saved summaries before demand, then current summaries | **CALL** | Same admission/replay order as restricted function calls |
| C2 initial emission and paired C5 intersection | **CALL** | Same native policies, predicates and per-demand field budget |
| AP summary composition, full marks, layers and protection | **CALL** | Same AP operations and complete-original transport |
| Real ND AND joins and Target meaning | **CALL** | Same complete-witness and NORMAL/DEMAND rules |
| Prepared output programs and demand payload trie | **CALL** | New general lookup optimization for those same C2/C5 operations; also applicable to function calls |
| Input links, publication delivery and ND join ownership | **LOCAL** | Parent/child block scopes and ports under one method owner replace caller/callee service ownership |
| Register binding and aliases | **LOCAL** | Registers remain shared; no call argument binding, return binding or call-action/alias suffix is added |
| Native saved/MUST/reverse application | **LOCAL** | Same native matching; local delivery commits provisional MUST demotion without a call return-action suffix |
| Boundary liveness and result destinations | **LOCAL** | Check the block's output before publication; prepare local exit routes once rather than recheck after application |
| Completion deduplication | **LOCAL** | Same fresh-delta principle, at a child completion point rather than a real caller statement |
| BL/L/AL decomposition and repeat/leave dispatch | **LOOP** | Internal block hierarchy and directed loop transitions |
| Stored-summary growth test and growing-result restriction | **LOOP** | Ordinary calls do not compare raw and prefix-cut loop observations |
| Adjacent/repeat consumer observation and trie rejection witness | **LOOP** | New precision lookup and certified budget skipping accelerate the existing loop-only restriction policy |

The same AP operation does not mean the entire call service is reused.
Local ownership and boundary adapters remain explicit. No new field, source
or alias policy is hidden in these adapters.

New general work is the prepared output-program/trie lookup and shared packet
enumeration. New loop-specific work is the precision witness and certified
budget skipping. Decomposition, growth testing and complete observation
already exist and keep their current policy.

## 4. Fact propagation algorithm

This is the single propagation algorithm. Its handlers run under the existing
method owner. `scope` includes the actual entry port; rows keep their exits.
The native helper contracts are stated below.

```text
ON_LOOP_INPUT(link, P, F):
    # CALL order; LOCAL links. Saved views already have prepared live routes.
    for row in saved.applicableViews(link.child, F):
        APPLY_AND_ROUTE(link, row, P, F, saved=true)
    replaySavedTargetsNormally(link, P, F)

    if not run1:
        initials = C2(link.child, F)
        if initials.empty: return
    delta = standingInputs.merge(link, P, F)
    if delta exists:
        for row in currentSummaries.candidates(link, P, delta):
            enqueue APPLY_AND_ROUTE(link, row, P, delta, saved=false)
    if run1: emitRun1InitialsNormally(link, P, F)
    else: startNewInitialsNormally(link.child, initials)

ON_BODY_EXIT(scope, exit, I, O):
    # LOCAL: called after actual instruction/end rules.
    routes = liveOutputRoutes(scope, exit, O.base)
    if routes.empty: return
    for row in INTERSECT_SUMMARY(scope, exit, I, O):
        delta = bodySummaries.addAdmitted(scope, exit, row)
        if delta exists: batchPublish(scope, exit, delta, routes)

ON_PUBLICATION(scope, exit, rows):
    for row in currentSummaries.mergePublishedBatch(scope, exit, rows):
        for input in standingInputs.candidates(scope, row.premise):
            enqueue APPLY_AND_ROUTE(input.link, row, input.P, input.F, saved=false)

APPLY_AND_ROUTE(link, row, P, F, saved):
    # Native matching, real ND joins, MUST/reverse lanes and requests remain real.
    for result in nativeSummaryApplication(link, row, P, F, saved):
        if result is Target:
            deliverTargetNormally(link, result)
            continue
        for bounded in globalLimit(result.F):
            if not ordinaryLoopOutput(link.child, result.exit) or
               run1 or bounded is Reach or not grows(result.storedGeometry):
                kept = {bounded}
            else:
                kept = exactUnion(RESTRICT_LOOP_SCALAR(link, result.P, scalar)
                                  for scalar in annotatedScalars(bounded))
            for fact in kept:
                point = existingCompletionPoint(link, result.exit)
                delta = completions.add(point, result.P, fact)
                if delta exists:
                    enqueue routePreparedExit(link, result.exit, result.routes,
                                              result.P, delta)
    # Routing uses the ordinary repeat/adjacent/enclosing block machinery.
    # Relevant instructions store results AFTER the producer statement.

RESTRICT_LOOP_SCALAR(link, P, raw):
    # LOOP: unchanged first-safe-cut policy, accelerated by the trie.
    baseline = OBSERVE(link, P, raw)
    if baseline.empty: return nothing
    if raw.fieldDepth <= 1: return raw

    first = 1
    (b, witness) = entryDemandTries.precisionBoundary(link, raw)
    if b > 1 and witness certifies the constant native ANY-ancestor emission:
        key = C2.emitOne(witness, limit(raw, b-1))  # includes scope/family/layer
        if key exists and key not in baseline.labelledAdmissions:
            first = b                            # every earlier cut adds this key

    for budget = first .. raw.fieldDepth-1:
        candidate = limit(raw, budget)             # native cut, ANY/DEMAND
        if OBSERVE(link, P, candidate) == baseline: return candidate
    return raw

OBSERVE(link, P, F):
    adjacent = labelledC2(adjacentEntryViews(link), F)
    enclosing = empty exact annotated union
    for savedRow in savedAdjacent.applicableViews(link, F):
        for output in nativePureApplication(savedRow, P, F):
            if output is Target:
                enclosing += nativeObservedTargetFilter(link, output)
                continue
            adjusted = existingObservedBoundaryMetadata(output)
            enclosing += INTERSECT_SUMMARY(parentScope(link), output.exit,
                                           output.P, adjusted)
    enclosing += existingSavedTargetObservation(link, P, F)
    repeat = labelledC2(repeatEntryViews(link), F)
    return exactSignature(adjacent, enclosing, repeat)

INTERSECT_SUMMARY(scope, exit, P, F):
    # CALL semantics; new generic output-program/trie lookup.
    prepared = existingSummaryFiltersAndFlowNormalization(scope, exit, P, F)
    if prepared.empty: return nothing
    (P, F) = prepared
    if run1: return row(P, F, exit)                  # no incoming demand
    plan = prepareOrReusePlan(scope, exit, P)
    if plan unsupported: return nativePairedIntersection(scope, exit, P, F)
    # Preparation checked each row's entry before grouping equal exit functions.
    buckets = empty per-program plain/protected selections
    for scalar in nativeScalarStreams(F):          # plain/protected, once each
        for program in plan.outputTrie.candidates(scalar):
            buckets[program] += nativeOutputSelection(program, scalar)
    result = empty exact annotated union
    for program in original program order:
        for packed in nativePackAndAttachProtection(buckets[program]):
            result += nativeLimit(packed, program.exitDepthBudget)
    return rows(P, result, exit)
```

## 5. Helper contracts

**Real application.** Saved views use their native direction, ports and
matching mode. Current ND application waits for every arm. Matching can be
shared across outputs of the same complete premise and input snapshot; each
output still performs its real effects. `storedGeometry` is the actual stored
or native reverse-view relation. It grows when its conclusion FL exceeds
every premise member FL; `FL(Zero)=0`. Applied caller suffix depth does not
decide this test.
Each applied geometry carries its prepared exit destinations as local routing
metadata. AP composition and field limiting preserve its conclusion base, so
the block-boundary liveness decision made before publication remains valid.
No post-application boundary liveness test is performed.
`ordinaryLoopOutput` means a loop child with an ordinary nonnegative exit
port. Nonloop blocks and typed method/exception/static-shortcut exits bypass
the loop gate, as today.

**Summary restriction.** Each complete paired row passes its own entry check.
Only then can equal full exit patterns and budgets share an output program.
Scalar selection stays in separate program buckets. Use the native plain and
protected processing order, pack before cutting, and union exact results.
Selections retain their plain/protected stream label. Exact unions keep
distinct layer/header groups; they do not merge NORMAL into DEMAND.
The budget is `min(globalLimit, FL(demand exit)+1)`. NORMAL rows are restricted
too. Unsupported controls, run-2 static completion or native views keep their
existing intersection.

**Publication and routing.** Candidate indexes select existing input/summary
pairs; native application decides compatibility. Preserve input snapshots,
publication batch order, complete ND joins and scheduling wakes. Completion
deduplication follows restriction, at the existing parent/child/completion-exit
point and whole original. It does not add the whole input link to the key.
Repeat results can first become enclosing
L summaries before re-entry; leave results enter the directed adjacent block.
No direct jump bypasses these ordinary summary operations.
`liveOutputRoutes` prepares the existing CFG or terminal destinations from the
summary's scope, direction, exit and output base. An empty result drops a dead
local before admission/publication. Typed terminal exits retain their native
dispatch even when they have no CFG successor. Reversed saved views prepare
their own oriented output once before replay. ND delivery uses the destinations
of the conclusion geometry it actually applies.
Preparation preserves existing endpoint exceptions: required real method
entry/exit handlers still run.
`currentSummaries` denotes the existing DATA and typed Target publication
services; their stores and matching rules remain separate. Body-exit DATA
uses the output-program trie. Typed Target emission and run-1 static/control
delivery retain their existing paths through the native services.
`enqueue` uses the existing method-owned delivery queues and work reservation.
Candidate input values are immutable snapshots. This is not a new queue or
recursive propagation path.

**Pure observation.** Include all configured adjacent and repeat scopes, saved
adjacent compositions, enclosing paired C5 results and Target metadata. Apply
the C2 entry-view guards and the enclosing summary's admission filters. Saved
views already carry their prepared destinations; do not recheck their boundary
after application. Compare complete originals, scopes, ports, paths,
marks, exclusions, layers, protection and Target IDs. The query executes no
rules, subscriptions, requests, static supplies or reports. Its hypothetical
results are never published as actual execution results.
Targets produced by saved DATA application, including backward ZERO-to-Target
conversion, pass their native observer acceptance check. They are separate
from saved Target metadata. Both paths remain in the complete signature.

**Prefix certificate.** A real ANY witness names one guarded native C2 family.
For every positive earlier budget, the MAY cut remains an ancestor of that
need and emits the same initial command. Use native `emitAdmission`, including
its rendered mark and layer. If its labelled key is absent from the full raw
baseline, each earlier cut adds a new key and must fail equality. Unknown or
failed certificates skip nothing. The full observer still checks all remaining
budgets in order. This preserves the exact first-safe-cut decision.

## 6. Principal cases

Assume compatible full mark T and the existing global field bound.

| Raw fact / consumer | Trie result and handling |
| --- | --- |
| `x.f.g.h.k.*`; needs `x.f.[any]` and `x.f.g.[any]` | Retain `x.f.g.h`. Earlier cuts emit a new ANY initial; test `x.f.g.h.[any]`, DEMAND. Both terminal consumers remain active. |
| `x.f.g.h.k.*`; needs `x.f.[any]` and `x.f.g.z.[any]` | Also retain h. Cutting at g would admit the previously nonmatching z branch. |
| `x.f.g.[any]`; need `x.f.g.[any]` | The earlier-cut witness key can already be in the baseline. No range certificate; ordinary ascending checks decide. |
| Saved adjacent read removes `.k` before reaching `ret.f.[any]` demand | Its precision is checked through actual saved application and enclosing C5. Do not treat `ret` demand depth as an input depth on x. |
| Local `tmp` is dead at the block exit | Drop its summary before publication; an old frozen demand for tmp cannot become a witness. |
| A loop-carried local is live only on repeat | Publish with the repeat destination; omit the dead leave destination. Application uses these prepared destinations. |
| Non-growing loop summary, run-1 or Reach | Keep the existing gate bypass and ordinary delivery. |

Thus, the longest shared demand prefix determines a useful cut boundary. It
does not delete shorter demands or replace the complete consumer check.

## 7. Lookup costs and expected savings

Let h be path length, r compatible context/mark cursors, L the packet's scalar
memberships, s eligible distinct output programs, and chi the selected
scalar/program candidate pairs.

| Operation | Proposed cost / work avoided |
| --- | --- |
| Precision boundary | Expected O(r·h) child probes; no descendant scan |
| Ordinary demand candidates | Path probes plus visited subtree nodes/payloads and order restoration; broad ANY can still visit many rows |
| Prepared C5 | One packet enumeration plus program-local lookup and chi native selections; then separate packing/cuts/union |
| Identical accepted output functions | One program instead of repeated whole-packet restriction |
| Certified prefix range | One witness emission and baseline-key check can replace several complete observations |
| New input/publication join | Indexed candidate pairs, followed by exact application; real matches and ND combinations remain |
| Boundary liveness | Once per emitted output geometry/exit, or oriented saved view; no repeated check for each application context |

The trie replaces owner-wide output-ID scans and full entry-plan scans on the
prepared path. It also avoids re-enumerating the packet for each program.
Finalizing all s programs still costs O(s); using only touched programs needs
an empty-bucket proof and stable ordinal restoration. Count that cost.

Shared geometry, terminal references and subtree witness maps use memory
bounded by inserted path lengths and payloads. Do not create a mark × all-rows
matrix, enumerate all saved-summary/demand compositions, or retain an unbounded
history of raw facts. The full observer remains a cost when certificates fail
or saved effects require more precision. No whole-run speed ratio is promised.

## 8. Correctness and validation

Four arguments justify the organization:

1. Accepted entries with identical full exits execute the same output function
   on the same packet. Native exact union is idempotent and OR-merges duplicate
   protection. Keep first program order and each original entry check.
2. Scalar/program regrouping gives each program the same complete ordered
   selections. Its unchanged packing, protection and field cut therefore give
   the same result. No distributivity of limiting over a union is assumed.
3. A witnessed admission absent from the baseline proves every skipped cut
   differs. Remaining cuts are checked by the same observer in the same order.
   Empty-baseline drop and raw fallback are unchanged.
4. Block liveness depends on the oriented summary's output base and exit
   routes. Ordinary local AP application and cuts preserve that base. Preparing
   allowed routes before publication therefore preserves the same destinations
   without repeating the predicate for every input context. Reverse views use
   their reversed interface; typed outputs keep their existing dispatch.

The constructive [row/scalar model](../../spec/lean/proposals/loop-edge-query-pipeline-20261104/README.md)
passes 20 theorems. The [trie/certificate model](../../spec/lean/proposals/demand-trie-loop-restriction-20261104/README.md)
passes 46 theorems. These prove their stated finite models, not Kotlin AP,
index completeness, full observer equivalence or project speedups.

Before implementation, validate native adapters against the current pipeline:
exact paired rows and program order; full protection; C2/C5 mark differences;
DATA-entry control rows; dead-local guards; nested and sibling needs; failed
certificates; saved reverse/MUST and Target paths; run-2 completion; real ND
AND joins; cancellation and bounded-plan fallback. Preserve actual effects
and work accounting. No new field or source policy may be hidden in an adapter.
Verify pre-publication liveness, repeat-only locals and oriented saved views
against the current guarded routing. The finite models above do not prove
this native liveness-placement adapter.

After implementation, repeat the existing Conductor and Stirling FULL/16 GiB
experiments. Record reached/completed/accepted runs, exact findings, demand
frontiers, observer calls, skipped budgets, candidate pairs, program/scalar
visits, CPU and allocation. Separate baseline-observation cost from trial cost.
