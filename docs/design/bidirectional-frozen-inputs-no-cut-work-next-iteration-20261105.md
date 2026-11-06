# Avoid repeated work on frozen inputs and bounded facts

Status: proposal only. No change in this file is implemented or selected.

The measured analyzer is `8331bf9e326ddd1bd5083dbc50456963d6b26b52`.
The latest reached/completed/accepted iterations are OWASP run-5/run-5/run-5,
Conductor run-15/run-14/run-13, Thingsboard run-1/none/none, and
Stirling-PDF run-16/run-15/run-15. Conductor has two new missing findings.
Resolve that regression before accepting the measured revision as a quality
baseline. Finer external control B restores R3 refinement guidance and all
seven expected native R5 report projections by disabling only proper-prefix
subtraction in `canonicalSpans`. A, same-point removal off alone, remains at
five. This isolates a sufficient proper-prefix intervention, not an accepted
fix. Later B2 captures trace closed point/summary-store removals and the
complete frozen explicit demand view. The later C2/report causal chain is
not proved.
Performance proposals 1 and 2 below remain
unimplemented and unselected; neither claims to fix the missing findings.

## 0. Correctness first: preserve required refinement guidance

**Priority0 is an acceptance obligation; its repair is UNDESIGNED/UNSELECTED.**
The [Conductor investigation](../reports/bidirectional-conductor-canonical-quality-regression-20261105.md)
and [portable evidence](../reports/data/bidirectional-conductor-canonical-quality-regression-20261105.json)
show that the verified external rollback changes only `canonicalSpans`' final
root result and `canonicalRegions`' below-coordinate subtraction. It also
restores packet-local same-coordinate MAY+EXACT bits. NORMAL relation and
transitivity, header/E/mx joins, protection and opposite-only STAR matching
remain enabled; other Group and `canonicalTaintState` pruning remains.
C2 call sites and its emission policy are unchanged, but the overridden
normalizer now returns raw coordinates. The actual class-load and executable
delta checks are retained.

The control restores WFDef STAR/Graal outgoing DemandTargets at R3 in
DeciderService.startWorkflow and both relevant decide methods. R5 then has
seven authoritative native ROOT-ZERO report entries, including ScriptEvaluator
instruction12/source253 and PythonEvaluator instruction58/source63. The native
rule/full-method-signature projection has zero missing or added versus the
expected seven. This is not diagnostic SARIF-fingerprint equality. All R5
collections are complete; four late R3 INPUT collections are whole-DROP and
are not interpreted as empty. The main8331 quality result remains five versus
seven and FAIL.

The earlier control establishes a causal contribution of the two-place
coordinate-removal bundle. The finer A/B controls narrow the sufficient
intervention to one expression in `canonicalSpans`: B replaces
`samePoint(minus(key.node.leaf, key.above))` with `samePoint(key.node.leaf)`.
Same-point removal, cross-header `canonicalRegions` behavior, NORMAL relations
and opposite-only STAR remain on; same-header state callers inherit B's
helper change. A replaces the expression with `minus(key.node.leaf, key.above)`
and does not recover the reports. Native cold checks show A restores an
EXACT/FLOW NORMAL initial, but warm state/group logic still drops that exact
coordinate; it is not a blanket rollback of MAY-over-EXACT subsumption. Each
capsule has 60 passing native checks. A has 66 complete collections/zero drops;
B has 62 complete/four late R3 INPUT drops with all R5 collections complete;
both reach run-6/run-5/run-5. These are diagnostic scopes, not new historical
full-suite counts or SARIF-fingerprint equality.

The later unchanged-code B2 capture now records a concrete proper-prefix
state removal in four-argument `getTasksToBeScheduled`, Empty context and ROOT
scope. Under full `ret.Element.[any]/FLOW` premise with empty E/mx, existing
`arg1.taskDefinition.[any]/FLOW D` is covered when root-only
`arg1.[any]/FLOW D` arrives. Both output headers have empty E and the exact
unsafe-jackson FULL exclusion set J 10–65. Live merged-state subtraction and
five matching point-store closes prove this broad-after-narrow change;
the incoming packet itself does not contain both paths.

The stopped attempt ends at run-2/run-1/run-1: five paired removals, 40 completed
windows, one whole deadline drop and no B2 snapshot. The earlier extra frozen
row has empty mx and exact HashMap context. Source `guidancePattern` erases
FLOW mx during handoff projection. The first stopped attempt has no B2
export; its point evidence remains valid and partial. The [full point-store
witnesses](../reports/bidirectional-conductor-canonical-quality-regression-20261105.md#actual-b2-point-store-subtraction)
preserve all headers, catalogs and censoring. The completed cold follow-up
now closes B2 with seven paired point/summary removals and all five planned
collections complete, zero drops, at run-3/run-2/run-1. Its typed HashMap and
Empty SUMMARY transactions remove the child under the same actual mxJ; their
final admitted stores remain root-only. In the complete outgoing direct DATA
view, Empty 64 plus typed 49 totals113 rows, with one root pair and no explicit
child pair in each context. Thus the summary-to-frozen-view bridge is observed
in one attempt, including native empty-mx projection. A root pair may still
cover the child denotationally. No later C2 rejection or report-loss chain is
proved; this evidence does not select a repair. See the [completed cold
bridge](../reports/bidirectional-conductor-canonical-quality-regression-20261105.md#completed-cold-b2-summary-and-guidance-bridge).
The earlier NORMAL-off and matching-only controls fail to recover
through R5; that does not exclude interactions. The [native NORMAL-cover/C2
countercell](../reports/bidirectional-normal-cover-opposite-c2-countercell-20261105.md)
shows why denotational relation cover alone is not an initial-progress theorem,
but is not the traced Conductor mechanism. The [organic CFG controls](../reports/bidirectional-normal-cover-cfg-progress-control-20261105.md)
recover their findings and do not reproduce the project loss.

The earliest captured input-demand difference is now before run-3 transfer.
Control B has an extra `arg1.taskDefinition.[any]/FLOW → ret.Element.[any]/FLOW`
pair in getTasks4's typed context, plus two `This.taskMappers.[any]/T → Zero`
control rows. These are frozen query-view differences, not observed first
removals. They do not select a C2 repair or prove which row causes recovery.
The appendix retains the native rows and the correction from an earlier
readable `Target` label to the actual `Zero` control exit.

The [new direct two-method reproducer](../reports/bidirectional-canonical-prefix-refinement-reproducer-20261106.md)
now shows the operational difference: removing the B2 child MAY coordinate
prevents the deeper F3 initial and delays the NORMAL finding from run-3 to
run-5. Both variants converge with the finding. The dedicated checkpoint test
is RED on current code and passes the proper-prefix-off control. A proposed
repair must account for this concrete progression case. Do not infer permanent
loss or select a C2 repair from it: the Conductor first-loss chain is still open.

The [later actual call-admission capture](../reports/bidirectional-conductor-call-admission-20261106.md)
ends at run-4/run-3/run-3 in both variants. All 1,218 matching full run-3
offers return the same initial sets and ordering. The 470 B-only input keys
differ before that comparison. This does not identify a rejected required
initial in `getTasksToBeScheduled`, or compare packets with equal denotation
but different coordinates. Trace the first input divergence before selecting
a repair. No new behavior decision follows from this capture.

The [wider upstream capture](../reports/bidirectional-conductor-upstream-admission-20261106.md)
now identifies a real run-3 admission difference. On the same NORMAL
`workflowDefinition.MUST/Graal` input, `createAndEvaluate` starts only the
STAR/FLOW form in Current. B also starts MUST/FLOW and later uses that initial
as a ROOT call premise. The [uniform-source regression](../reports/bidirectional-uniform-prefix-refinement-reproducer-20261106.md)
repeats that distinction in two methods: Current first reports in run-5, B in
run-3, and both converge with one finding. This confirms loss of uniform
precision during admission. It does not yet establish which lost initial
causes either final Conductor miss. Preserve this test when designing a repair;
the repair remains unselected.

The [first-field MUST candidate](bidirectional-first-field-must-admission-candidate-20261106.md)
makes one possible repair reviewable. It would keep a known uniform head when
forward C2 reaches that head in one field step, with the actual field exclusions.
This is a new admission policy: concrete NORMAL input can start NORMAL MUST
work where Current starts DEMAND STAR work. Method, block, loop, and C5 entry
behavior are affected. The document also lists retaining STAR with repaired
guidance and additive STAR/MUST admission as distinct contracts. No contract is
selected. Global required-effect preservation and Conductor recovery remain
open; this candidate does not replace the measured results or select a fix.

A separate [direct loop convergence test](../reports/bidirectional-loop-boundary-normality-loss-20261106.md)
now exposes a shared coverage gap with one mark and no ND condition. Both
current and prefix-off code stop at run-5 with zero reports for a valid path.
The actual NORMAL `s.f.g.$/T` packet is rewritten to a DEMAND packet before
AL; the same frozen AL admission also selects a coarse DEMAND initial from
the uncut packet. A correctness design must preserve progress and a NORMAL
report across this internal block boundary. A current-run observation-equality
check alone does not prove that obligation. The new optional convergence
assertion is RED in both versions. No change to C2, loop restriction, Target
routing or stopping is selected from this observation alone. The exact
Conductor first-loss chain is still a separate obligation.

The user behavior decision is pending between:

- allowing required implied C2 refinements from canonical facts, revising the
  earlier choice that permitted initial images to disappear; and
- retaining current C2 outputs while repairing other guidance.

Neither branch is selected. A C2/demand-geometry repair is a possible candidate,
not a design or implementation in this proposal. Consulting removed/raw
coordinates, keeping separate refinement labels, or changing permitted C2
images would go beyond the current canonical-only decision and needs an
explicit semantic design. Do not introduce any of those mechanisms as a
performance optimization.

Before performance acceptance, establish the required operational preservation
contract for the chosen repair: full premise, scope/ports, mark/tail, E/mx,
layer and protection must remain accounted for through native application,
C2 and Target/observer effects. A denotation-only canonicalization theorem is
insufficient. Ground the repair in a meaningful native counterexample and
constructive proof, then validate the exact finding identities on the required
fixed configurations. The rollback itself is not silently adopted.

## 1. Scope

Performance proposals 1 and 2 keep the approved semantic contract. They do not
change C2 initial admission, C5 restriction, field limits, layers, protection, summary roles,
alias handling, static supplies, or report identity. They do not introduce an
input history, a second request authority, or a general identity cache.
Priority0 is separate: its possible repair may require the explicit behavior
decision above. No such semantic change is selected here.

The order below uses the measured avoidable work, not a promised wall-time
speedup. Sample shares are not seconds and are not retained-memory shares.

| Priority | Change | Measured evidence | Work to remove |
| --- | --- | --- | --- |
| 0 | Preserve required refinement guidance; repair undesigned/unselected | B restores R3 guidance/native R5 seven; actual B2 summary removal and complete frozen explicit view are traced, but later C2/report chain is open; main still fails | Correctness gate, not a performance claim |
| 1 | Canonicalize frozen joined inputs once | Thingsboard's observed run-1 static-completion window: 440.336 s; 33,403 Java samples; canonical packet/state work 48.97% of samples and 51.07% of weighted allocation bytes | Repeated normalization of the same immutable joined input for different writer visits |
| 2 | Return bounded packets before protection transport | Conductor's logged top-24 method rows at run-12: 4,944,767 limit offers, zero over-limit offers; the run-12 capture contains 5,196 of 10,466 sample weights under `ApOps.limit` | Splitting, walking, and reattaching protection when the field limiter returns the original packet |

The run-12 capture can span phase boundaries. Its inclusive sample counts
overlap. The logged 24 methods are not a global census. A final implementation
experiment must use exact phase windows and count the fast-path eligibility.

## 2. Canonicalize frozen joined inputs once

### Current behavior

The live run ends. `RunManager.prepareJoined` requires callback quiescence,
captures exports, moves local and caller input directories, and releases the
runners. Static-writer binding then borrows these directories.

`LocalInputDirectory.visitCanonical` calls `canonicalPackets(input.value)` on
every visit. `candidates` also constructs canonical packets for each selected
input. `OwnedJoinedStaticWriterBinding.complete` calls `canonicalPackets` again
before its full-premise match. Real-call joined input selection has the same
need to return canonical current packets.

```java
void writeTwo(Box p) {
    C.f = p.value;
    C.g = p.other;
}
```

The binding phase can visit the same caller input for both primitive writers,
then revisit it for other write results. The input can contain a large packed
field DAG. No static fact is propagated through the method body by this join.
The repeated operation is normalization of the fixed nonstatic caller packet.

```text
Before, at each visit:
    raw current input -> canonical packet(s) -> complete match -> apply writer

After:
    move/adopt:       raw current input, with no normalization
    release execution
    first visit:      raw input -> canonical packet(s), replace owned payload
    later visits:     ready packet(s) -> complete match -> apply writer
```

### Proposed organization

Reuse the existing moved input directory as the owner. Adoption moves the raw
payload and does no normalization. Release closed execution first. The first
joined binding query for an owned row computes its canonical packets and
replaces that row's raw payload. Later queries read the ready payload. Unvisited
rows pay no canonicalization cost. This is one state variant under the existing
handle, not a separate cache or an input history.

```kotlin
sealed interface JoinedPayload {
    class Raw(val value: Facts) : JoinedPayload
    class Ready(val packets: List<Facts>) : JoinedPayload
}

fun detachJoinedInputs(lease: JoinedBindingLease): JoinedInputs {
    requireIdle()
    requireNoPendingCallbacks()
    val directory = takeInputDirectory()
    // Adoption must close the moved directory if registration fails.
    // No checkpoint or canonicalization occurs before that adoption.
    return lease.adopt(directory)
}

fun OwnedJoinedRow.canonicalPackets(ap: ApManager): List<Facts> {
    requireExecutionReleased()
    return when (val owned = payload) {
        is JoinedPayload.Ready -> owned.packets
        is JoinedPayload.Raw -> {
            checkpoint()
            val packets = ap.canonicalPackets(owned.value)
            // Install only the complete result. On failure, Raw remains owned.
            payload = JoinedPayload.Ready(packets)
            packets
        }
    }
}

fun JoinedInputs.visitLocal(emit) {
    requireExecutionReleased()
    // Local candidate postings are already released at the ownership move.
    for (handle in directory.currentRows()) {
        for (packet in handle.canonicalPackets(ap)) {
            emit(handle.link, packet) // Binder does not canonicalize again.
        }
    }
}
```

The once-only operation runs during the existing static-binding query, after
execution release. It is not moved into the pre-release detach loop. Keep the
current timing boundary: adoption belongs to joined sealing/release; lazy
normalization belongs to static binding. No new stage clock is implied.

If the list contract returns several packets, retain the complete ordered list
under the same input handle. Do not retain an additional raw row payload after
success. Shared native interners or other stores can still reference common DAG
nodes; replacing the row does not prove those nodes are freed and must not
invalidate any other owner.

Keep the full original caller premise, method context, scope, ports, group,
zero-only mode, and protection mask. Local joined inputs keep their current
full-row visit. Caller directories keep their existing candidate selection;
their old position postings can remain as a conservative superset. The complete
current match still rejects false candidates. Do not use an index as proof of
a match. This proposal adds no new local candidate index.

Add a joined-only lazy payload operation to `AddedFactAccumulator` for real
caller inputs. A temporary snapshot is not the owning row. The operation must replace the value under the existing stable handle, release
the raw row payload, and keep link/header order. Its use is invalid before the
directory ownership move and execution release.

Keep live offer/delta admission unchanged. The optimization starts only when
the existing ownership transfer prevents further updates. Check cancellation
before and during first-use normalization. On failure, close all adopted rows
as part of the existing failed joined phase. A row changes from Raw to Ready
only after its complete packet list is available. Do not return a partial list
or publish a partially completed export.

### Complexity

Let `N_i` be the canonicalization work for frozen packet `i`, and `V_i` the
number of visits to that packet. Current work is `sum(V_i * N_i)`. The proposed
work is `sum_{V_i > 0}(N_i)` plus iteration over the already canonical packets.
Unvisited rows retain Raw until closure and add no normalization work. Matching
and writer application are unchanged. The old path can normalize twice per
visit; this expression suppresses that constant. A one-visit row need not give
a material saving; count distinct visited rows and repeated visits before
predicting an improvement.

### Proof obligations

1. The moved directory cannot receive a new input or a protection upgrade.
2. A visit before and after sealing returns the same ordered canonical packets
   and the same link. Normalization is pure over the frozen value. Some current
   paths apply `C` in directory selection and again in the binder. Prove native
   annotated idempotence `C(C(v)) = C(v)`, including protection, before removing
   that second call. Do not assume an unproved law from ordinary region coverage.
3. Candidate selection remains complete when its index contains removed
   descendant positions. A complete match still uses the frozen packet.
4. No raw descendant history can enter C2 or the binding phase after sealing.
5. All packet headers and protection masks survive the ownership transfer.
6. Cancellation cannot expose a partially normalized packet list or a failed
   joined phase as a completed export. All adopted Raw and Ready rows close.
7. First-use normalization occurs only after execution release. Replacing the
   owned payload keeps native aliasing and other store/interner lifetimes valid.

For a frozen value `v`, directory selection returns `C(v)` and some paths
canonicalize its packets again in the binder. With the annotated idempotence
obligation above, the final old stream is `C(v)`. The first new visit stores
exactly `C(v)` and later visits read it, so each visit returns the same stream. This equality is
stronger than equal reachability. It does not require a new admission rule or
a change to the final approved canonicalization law. Here `C` must be the
normalizer accepted after Priority0; this work-equivalence argument does not
prove that8331 canonicalization preserves required analysis progress.

### Tests and measurements

Use local and real-call inputs, duplicate writer visits, packed DAGs, mixed
output headers, ZERO, and protection upgrades before ownership transfer. Include
unvisited rows and cancellation before first use, during normalization, and
after Ready installation. No canonicalization may run before execution release. A mutation after
sealing must fail. Compare all bound writer outputs and final demand identities.
Count sealed packets, visits, canonicalization calls, logical memberships, and
weighted allocation bytes. Measure run-1 body and static completion separately.

## 3. Return bounded packets before protection transport

### Current behavior

`ApOps.limit` first calls `transportProtection`. For a protected concrete packet,
that operation extracts its protected part, limits it, collects exact and
nonexact masks, limits the ordinary packet, and attaches the resulting mask.

The inner `limitTrie` already tests `root.boundedDepth <= fieldLimit` and returns
the original root. The outer protection work has already occurred at that point.

```text
Input: protected p.f.$/T, NORMAL; field limit 8
Before: split protection -> limit two parts -> attach protection -> same packet
After:  depth <= 8 -> return the original packet, including its mask
```

### Proposed code boundary

```kotlin
fun limit(c: Facts, fieldLimit: Int, out: ApOut) {
    require(fieldLimit >= 1)
    cancellation.checkpoint()
    if (c is Reach || c.rootCountedDepth() <= fieldLimit) {
        out.result(c)
        return
    }
    transportProtection(c, out) { part, sink ->
        limitFacts(manager, part, fieldLimit, sink)
    }
}
```

`rootCountedDepth` means the existing cached `boundedDepth`, with exactly the
current counted-accessor definition. Do not count class/static descriptors as
new ordinary fields. Do not replace this check with the number of raw trie
arcs. On overflow, use the existing code without changes.

### Proof obligations

If the ordinary root fits, every protected coordinate fits because the mask
is a subset of that root. Both inner limits are identity operations. Splitting
and attaching therefore returns the same ordinary fields, marks, headers,
layer, and protection mask as `out.result(c)`. It emits no request. Keep the
positive-budget check and cancellation checkpoint before the fast return.

Check exact and nonexact leaves, all tails, mixed concrete marks, nonempty
field exclusions, FLOW mark exclusions, protected packets, static descriptors,
and deep shared DAGs. Compare the protection coordinates explicitly:
`TaintTree.equals` omits `nonSubsumable`, so ordinary equality alone does not
prove this fast path preserves the mask. Include one-over-limit controls: they must use the old
cut path and produce byte-equivalent semantic outputs.

## 4. Possible later step: share the complete frozen match

This step is not part of proposals 1 or 2. First measure distinct complete
writer premises and repeated input pairs. In the same Thingsboard window,
`CURRENT matchSummary` has 24.10% of Java samples and 31.27% of weighted
allocation bytes. This is evidence of cost, not evidence of how many matches
are equal.

If multiple primitive writers have the same complete `(owner, original)` and
borrow the same frozen input, their matching result is independent of the
static output field. A joined-phase worklist could select that input once and
apply each writer to the selected packet. The key must contain the full owner,
premise, caller link, packet header, ports, and mode. Never group by `C.f` or
by a mark alone. A separate design must cover late writer admission and cycles.

## 5. Acceptance

First resolve Priority0 and the explicit behavior choice; no C2 repair has
been selected by this document. Then prove the selected
work-removal laws in Lean before implementation. Run native identity and
cancellation controls, then repeat the four fixed real-project configurations.
Keep FULL, 16 GiB, `1,1,2,...`, aliases and statics. Reuse the fixed quality and
performance controls. Compare exact findings and demand identities, not counts
alone. Report reached, completed, and accepted run labels on every project.

Do not call these changes successful from a shorter timed-out prefix. Report
which stage completed, the observed prefix of an incomplete stage, and profile
coverage. A new missing finding blocks acceptance even if more iterations fit
within the time limit.
