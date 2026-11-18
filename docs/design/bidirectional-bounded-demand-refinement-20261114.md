# Bounded demand refinement

14 November 2026. Proposed approach under
[proof-guide.md](../../spec/proof-guide.md). Production remains unchanged.
This replaces the full-guard admission candidate in the
[earlier investigation](../reports/bidirectional-may-may-progress-investigation-20261114.md).

**Keep truncation. Refine the query regions, not the field limit.**
Do not archive or compose discarded suffixes. Do not enumerate paths hidden
by MAY. The method-only and BB references below terminate after **run-5**,
with a preserved NORMAL finding and no iteration hard limit.

**Revision: no artificial field exclusions.** G belongs to a frozen local
admission plan, not to an AP fact or summary. The earlier `p.* {exclude G}`
encoding is withdrawn. Real exclusions produced by the program's writes
and cleaners keep their existing meaning.

## 1. Approach

Use four rules together:

1. Preserve deeper, already truncated demand heads for next-run refinement.
   Semantic MAY union must not erase those heads.
2. Prepare complete child queries at **one observed next field** and
   delegate their input cases locally. Use deeper demand heads and eligible
   retained NORMAL input guards. Apply this in both directions.
3. Keep an explicit admission binding when an uncertain input is refined.
   An assumed field prefix cannot produce a NORMAL concrete witness.
4. Before a relative C5 cut, omit a duplicate NORMAL relation if an already
   retained NORMAL provider covers it. Continue to cut actual caller facts.

This changes admission and the refinement frontier. It is not a
representation-only optimization. It does not add a new tail kind or allow
MAY/NE premises.

The unchanged bounds are:

```text
FL(new initial) <= min(global limit, FL(its demand Dc) + 1)
FL(published conclusion) <= min(global limit, FL(its paired Dp) + 1)
```

Every published new summary still passes C5. A covered duplicate is not
published or stored. The retained provider was already legally persisted.
No unrestricted candidate archive is needed.

## 2. Two views of bounded summaries

For each method and generated block, keep:

```text
execution summaries: existing canonical, executable summary storage
refinement view:    bounded qualified demand rows for the next handoff
```

Insert a DEMAND candidate into the refinement view **after C5 and
normalization, before executable MAY coverage can absorb its head**.
The refinement view stores only admitted bounded rows, with shared premise
objects and packed mark sets. It stores no raw candidate, submitted-input
history or discarded field suffix.

This is not an instruction to keep every captured DEMAND row at handoff.
Apply valid NORMAL-backed removal and proved refinement-service compaction
to the final basis. Only location-set coverage by a broader MAY is
insufficient to erase a deeper refinement head.

Example, same original premise and protection class:

```text
ret.* -> p.MAY,  D
ret.* -> p.f.NE, D
```

The executable MAY union can cover the second output. The refinement view
keeps both heads: the second permits a more precise next initial. Same-head
MAY/NE duplicates can still be compacted when their **complete C2/C5
services** are covered. Set inclusion of output locations alone does not
justify removing a deeper refinement head.

Build the next DemandStorage from this view. Stopping also uses its outgoing
DEMAND rows, including DemandTarget. Do not carry old demand rows forward
merely because they existed: each run must produce its own frontier.
NORMAL persistence and normal summary delivery remain unchanged.
Preserve all other existing handoff-origin selection, seed and Target
handling; the new capture supplements the bounded demand that semantic
MAY union can hide.

### Local refinement versus caller delivery

For compatible rows with the same P, mark, E/mx, layer and protection class:

```text
local refinement view:   P -> a.MAY,D  AND  P -> a.f.NE,D
caller-visible delivery: P -> a.MAY,D
```

Yes: perform executable subsumption before delivering to callers. Keep the
callee's bounded refinement rows before that compaction. Next-run call
admission reads the full qualified **callee** demand store, even though the
caller's data came from the coarser publication. A MAY offer can still
start the child's query; a wrapper STAR offer uses the explicit possible
binding in §4. Never reconstruct callee demand from caller-visible rows.

This may delay precision in the caller; its intermediate demand frontier
need not match a run that delivered both rows. When a finer result becomes
NORMAL, it is not covered by the DEMAND MAY row. Deliver and persist that
NORMAL row through the ordinary policy. Keep all other subscription and
saved-replay rules unchanged.

Use the existing publication batch and filter pending deltas against the
current executable basis. If the fine row was delivered before the broad
row existed, that work cannot be undone. Final visible membership can be
arrival-independent without requiring identical callback counts.

### Subsumption rules

Every comparison keeps complete owner/direction/ports, mark constraints,
legal E/mx, layer requirements and literal protection memberships. Plain
and protected memberships remain separate. A protected T is not removed
by plain FLOW backing.

| Rule | Executable storage | Refinement view |
| --- | --- | --- |
| Aligned NORMAL FLOW: `a.u.* -> b.v.*` covers `a.u.r.* -> b.v.r.*` | Keep the existing rule. The same r shifts both endpoints. | A valid retained NORMAL service discharges the redundant relation; do not keep a new demand merely to preserve its old head. |
| FLOW-backed diagonal T | Keep existing same-tail/geometry, mark-exclusion and protection checks. NORMAL FLOW can cover NORMAL or DEMAND T as already specified. | Apply the same valid removal to outgoing guidance. Capturing the row earlier must not restore its T demand. |
| Same-head MAY covers NE | Keep same-premise/mark/layer/H coverage. | May remove NE when its complete updated C2/C5 service is covered and the paired Dp is preserved. |
| Ancestor MAY covers a deeper MAY/NE output | Keep executable location coverage where already valid. | Do not infer removal from location inclusion. Preserve the deeper head/budget unless a retained service proves it redundant. |
| MUST canonicalization | Keep its existing mark/layer/H and exclusion rules. | No new blanket MUST-to-MAY/NE removal. An offer-specific MUST admission is not permanent edge subsumption. |
| ND guidance | Preserve executable AND semantics. | Remove an ND origin only when retained witnesses cover every projected member and leaf under the updated admission plan. |

The difference between same-head and deeper-head coverage matters:

```text
same Dp = ret.*:
    Dc1 = p.MAY
    Dc2 = p.f.NE
submitted = p.f.g.$/T

Dc1 initial bound: 1 field      -> p.f.*/FLOW
Dc2 initial bound: 2 fields     -> p.f.g.$/FLOW
```

The deeper row authorizes an additional refinement step. The parent MAY
contains its locations but does not provide that same admission service.
Keeping just the guard `f` while deleting the deeper row is insufficient:
the parent still has only its original `FL(Dc1)+1` bound.

Subsumption is transitive and independent of arrival order. Check the final
retained basis: if A replaces B and B covered C, rebind C's proof to A.
Do not keep a removed B as a provider. Build next-run guard tries from
that final basis. Coverage is always checked in its own domain: executable
relation coverage does not automatically imply refinement-service coverage.

There is no new Target subsumption: a NORMAL sink witness does not erase
an anonymous DemandTarget from another unresolved witness.

## 3. One-step admission plan

Group rows only when they have equal owner, direction, physical ports,
required mark class/protection context and **the same complete paired Dp**.
Do not borrow another row's output permission or field budget.

For a MAY row at `p`, use next fields from:

- compatible deeper heads in the current refinement demand trie;
- native NORMAL record input guards in the current read direction, when
  ordinary application from this coarse STAR region would use an unknown
  field. Use a retained NORMAL read view, not a DEMAND reverse-MUST view.

Read only the **first field after p**. If a NORMAL record has premise
`p.f.g.h.*`, it contributes `f`, not `f.g.h`. Do not recursively refine
the new `p.f` start during the same row's preparation. Guards are snapshotted
from the current demand and prior retained records; no future-run data is used.

With observed next-field set G, the ordinary queries are:

```text
p.$                    // only if ordinary admission supplies the empty case
p.*                    // unchanged real E; no G on this fact
for each f in G:
    p.f.$
    p.f.*
```

G is local routing information: a coarse unknown-field read for f can be
delegated only when the corresponding child point and suffix queries are
admitted, or the complete case has an independent coverage proof. A retained
NORMAL child relation can select f; that relation alone does not certify
every branch which reads f. The full child query must analyze those branches.

The coarse `p.*` fact remains ordinary. When a supported operation would
produce MAY/DEMAND by reading f from its correlated symbolic suffix, omit
only that coarse result if the child case is certified. A known-prefix read
from `p.f.*` runs normally. An unknown g not in G runs normally. Do not turn
delegation into a claim that f is untainted or into logical false for a
rule condition. Unsupported consumers keep ordinary processing.

Keep original EXACT commands; do not manufacture a root EXACT command
from a STAR-only or NE-only offer. Such an offer can still supply the
child point `p.f.$`: its nonempty suffix can end immediately after f.
With an NE selector, keep the existing prohibition on the original-head
EXACT command. A child EXACT has a nonempty extension and remains legal.

Normal transfers, field writes and cleaners run unchanged. No artificial
G is added to their result. Every result that routing emits is the ordinary
unmasked transfer result; NORMAL results are forwarded unchanged. Do not
strip genuine E when exporting a summary, and do not infer a new NORMAL
fact from a skipped contribution.

The routing plan is owned by the method/block admission mechanism. It is
not stored on facts, AP initial keys or MethodEdgeStore. Freeze one safe
delegation mask per raw initial for the run. If multiple row plans share
that initial, a field is delegable only when **all** consumers that need
the coarse contribution have a child-coverage proof. Otherwise process the
coarse result normally. Do not add the mask to initial identity or change
a mask after deduplication has discarded its earlier work.

Keep only regions compatible with the actual offer. Keep the dedicated
MUST commands already justified by the existing C2 table. A MUST command
can replace a coarser command **for this offer** only when it covers that
offer's relevant region. It is not a general subsumption of arbitrary STAR
relations. A mark uniform only at `p.f.g` never becomes uniform at `p.f`.

Use a deeper row's prepared family to replace a coarse overlapping family
only with complete region coverage and the same Dp. Otherwise retain the
uncovered coarse region. Keep the EXACT child, including when a deeper NE
row itself does not request that child point.

Existing real E and mx remain binding constraints. Check child admission
against them; do not restore excluded fields or marks. Initials keep the old
mark selection and seed-layer rules. An EXACT concrete point guessed from
MAY, NE or an uncertain STAR descent is DEMAND. FLOW probes are conditional
NORMAL hypotheses, not concrete-mark evidence.

### Why this does not enumerate field paths

For k observed next fields, the plan has at most `2 + 2k` queries, all at
depth p or p+1. There is no product of fields and no recursive expansion of
new starts. Share prefixes and packed marks in the existing demand trie.
An over-limit child is not generated; retain the corresponding unresolved
coarse processing instead.

The bound is linear in the **already observed local frontier**. The proposal
does not claim that all bounded AP sets in arbitrary programs are small.
The original truncation remains the control on those sets.

## 4. Original offers and admitted bindings

Saved NORMAL replay still uses the original offer first. Current summaries
are considered only after demand admission.

One wrapper case needs an explicit semantic change:

```text
current demand: p.f.NE or p.f.MAY
submitted:      p.*
```

The selected table rejects an ancestor STAR today. Permit a bounded
**possible refinement** for MAY/NE demands and their prepared child queries
only. The path must come from the frozen demand trie or the one-field
plan in §3. A child keeps its original row's paired Dp and initial budget;
it does not acquire a new, deeper demand budget. Do not apply this exception
to an unrelated precise STAR or EXACT demand.

- For a MAY demand at the refined head, the residual can be empty or
  nonempty: admit EXACT and STAR, provisionally for concrete marks.
- For NE, admit its nonempty STAR branch.
- Respect the original input E, mx, mark and layer.
- Keep the original offer on the resume path. Store only the bounded query
  descriptor and the fact that its field binding is possible.

This authorizes application only for a current summary matched to that
prepared query. It does **not** enable unrestricted same-direction
STAR-inside matching over current summaries. Ordinary matching and the
opposite-direction inside rule remain as before outside this binding.

If a guessed prefix loses suffix correlation, use the existing MAY/DEMAND
result of that loss. Do not return a NORMAL exact marked fact. NORMAL
Target composition still requires NORMAL support; a possible binding
cannot confirm it. Concrete EXACT projections from such a binding also
start on DEMAND, even if the incoming STAR happened to be NORMAL.

This prevents a wrapper from blocking a child demand solely because its
incoming MAY was represented by a STAR query. It does not bypass an
unsatisfied precise demand. No field evidence is composed across calls.

## 5. Publication and pipeline

Use NORMAL precoverage for supported unary FLOW relations, including a
verified uniform image. Apply existing qualified mark, E/mx, direction and
scope requirements. A known writer `p.* -> ret.f.*` covers its NORMAL
specialization `p.f.MUST -> ret.f.f.MUST`.

The comparison must cover the complete native service, including existing
alias-closure obligations. Output-fact equality alone is insufficient.
Do not precover a DEMAND result, a protected result, a Target, a generated
mark relation or an unsupported ND service. Keep those cases unchanged.
Apply exit observations before this publication check.

There is no new coverage oracle. Use the following conservative case:
S is a prior unary NORMAL FLOW STAR-to-STAR record in the same qualified
scope; S's input path is a prefix of P; its input E/mx accept the **whole**
P region; and native transport of P's suffix/tail through S gives exactly
C's qualified geometry. Require C to retain P's tail kind, with the verified
MUST-to-MUST uniform case included. The image must fit the current global
limit. This is a correlated specialization, not general MAY containment.
Use the already selected input-alias-closure invariant for identities.
If any check fails, keep the candidate and run C5 normally.

```text
offer(original):
    applyPersistedNormalSummaries(original)             // unchanged
    rows = demand.lookup(original, uncertainDescentPolicy)
    if rows.empty: return

    plan = prepareOneStepCover(rows, priorNormalInputGuards)
    // A plan cell retains its complete originating row and raw initial kind.
    // Never expand a freshly created cell again in this preparation.
    admitted = plan.select(original)
    admitted = removeOnlyProvedCoveredQueries(admitted, original)
    emitFreshInitialSupport(admitted)                    // existing entry dedup
    applyAndSubscribeCurrent(admitted, original)         // query-scoped bindings

onOrdinaryTransfer(initial, operation, fact):
    result = ordinaryTransfer(operation, fact)           // genuine E unchanged
    f = firstUnknownCorrelatedSuffixField(initial, operation)
    if result.isMayDemand
       and frozenPlan[initial].delegatesForEverySharedConsumer(f):
        // Complete child queries cover this operation's input case.
        // No contribution here; this is not a false rule condition.
        return
    emit(result)                                        // exact ordinary result

onRawSummary(P, C):
    // This result has passed the existing global in-procedure bound.
    if supportedNormalFlow(P, C)
       and priorNormalCorrelatedSpecializationCovers(P, C):
        return                                         // duplicate publication

    for ownRow in plan.rawEntryWitnesses(P):
        result = pairedC5(P, C, ownRow)                 // same output limit
        if result.empty: continue
        if result.isDemand:
            refinementView.add(result)                 // before MAY union
        executionSummaries.add(result)

handoff():
    persistNormalSummariesAsBefore()
    normalBasis = finalRetainedNormalBasis()
    origins = existingHandoffOrigins() union refinementView
    guidance = compactByProvedServices(origins, normalBasis)
    // Includes valid FLOW-backed T removal; not ancestor-MAY inclusion alone.
    nextDemand = project(guidance)                      // all qualified members
    return nextDemand

priorNormalCorrelatedSpecializationCovers(P, C):
    for S in priorNormal.inputAncestors(P):
        if not sameQualifiedScopeAndUnaryFlow(S, P, C): continue
        if not S.isStarToStar or C.tail != P.tail: continue
        if not wholeInputRegionAccepted(S, P): continue // E/mx, no guessed bind
        shift = P.path.removePrefix(S.input.path)
        if shiftedOutputLength(S, shift) > globalLimit: continue
        image = nativeCorrelatedImage(S, P, shift)      // one bounded transport
        if image == C: return true                     // tail/E/mx/ports included
    return false
```

The prepared plan supplies both C2 and C5's constructive raw-entry image.
Check raw EXACT/STAR before normalization. Do not replace that check with
normalized-key compatibility or an offer-history cache.

Actual facts still pass the global cut. A real long writer result stays
NE/DEMAND, even if its transfer relation already has a NORMAL provider.
Its sink witness still creates DemandTarget. Skipping a duplicate
conditional summary is not permission to remove that actual cut.

## 6. Required example, from run-1

Code, with no loops, recursion, aliases, statics or ND:

```java
void main(boolean flag) {
    Box a = sourceAtF();        // T uniformly at a.f and below.
    Box b = choose(a, flag);
    Box c = choose(b, flag);
    sinkAnywhere(c);           // CM(c.MAY, T).
}
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;    // Also test longer p.f.g.h... reads.
    Box q = new Box();
    q.f = p;
    return q;
}
```

N = NORMAL, D = DEMAND, U = MUST, F = FLOW. Demands are written `[Dc ; Dp]`.

**Run-1, forward, limit 1.** The ordinary abstraction learns
`p.*/F -> ret.f.*/F,N`. The unknown reader still gives MAY demand. Run-1
abstraction is unchanged. The writer is the only NORMAL provider required
by the new run-2 plan; a complete NORMAL reader is not assumed.

**Run-2, backward, limit 1:**

```java
// Published D reader rows have conclusion p.f.NE/F.
// Their premises are ret.* and ret.f.*; E is empty in this example.
// Retained NORMAL: ordinary reverse writer ret.f.* -> p.*.
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;    // Inverse prepends f.g; cut to p.f.NE,D.
    Box q = new Box();
    q.f = p;                  // ret.*: delegate the unknown-f MAY result locally.
                              // ret.f.$ / ret.f.*: known reads run normally.
    return q;
}
// Demand [ret.MAY/F ; p.*/F]. Submitted ret.MAY/T,D.
// FLOW initials: ret.$, ret.*, ret.f.$, ret.f.*; all N, all genuine E empty.
// Only ret.*'s local admission command delegates f; no fact carries G.
// All initial field lengths <= 1. No backward MUST initial.
```

Unlike the old trace, the writer's inverse cannot erase the reader's
refinement with `p.MAY`. Next admission has `p.f.NE`.

**Run-3, forward, limit 2:**

```java
// Demand entry p.f.NE/F. Paired exits include ret.* and ret.f.*.
// First actual p.f.U/T,N -> existing initial p.f.U/F,N.
// Other actuals: p.U/T,N -> p.f.U/F,N;
//                p.f.f.U/T,N -> p.f.f.*/F,N.
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;    // p.f.U reads g uniformly: ret.U,N.
                              // p.f.f.* cannot read f.g: f != g.
    Box q = new Box();
    q.f = p;                  // p.f.U -> ret.f.f.U,N: covered by saved W
                              // before relative C5 could cut it.
                              // p.f.f.* -> ret.f.f.f.*: real global cut.
    return q;
}
// NORMAL reader learned now: p.f.U/F -> ret.U/F.
// Remaining D rows: p.f.f.*/F -> ret.f.NE/F or ret.f.f.NE/F.
```

Original-offer replay gives main `c.U/T,N`, `c.f.U/T,N` and
`c.f.f.NE/T,D`. Both NormalTarget and DemandTarget remain. **Do not stop
after run-3:** the real global cut still needs refinement.

**Run-4, backward, limit 3.** In the method-only body, the reverse reader's
`p.f.g...` result is incompatible with the required `p.f.f.*` output;
the reverse writer is already covered. Helper demand becomes empty.
Ordinary reverse writer replay still reaches the source and renews its
permission. Main keeps its backward Target guidance.

The **BB version has an extra effect**, which is retained:

```text
readBB's forward NORMAL record: p.f.U -> ret.U
its existing weak reverse view: ret.* -> p.f.MAY, D
method C5 with Dp=p.f.f.*:     ret.f.* / ret.f.f.* -> p.f.f.MAY, D
```

This is not a backward MUST seed or a naive swap of uniform endpoints.
The extra method demand is allowed to remain after run-4.

**Run-5, forward, limit 4:**

```java
// Method-only: no current DATA demand or initial. Saved replay still runs.
// BB method: entry demand p.f.f.MAY; actual p.f.U/T,N
//            -> existing rebased p.f.f.U/F,N query.
Box choose(Box p, boolean flag) {
    if (flag) {
        readBB: { return p.f.g; }
        // No current readBB demand. Its saved f.U reader cannot apply
        // to the method's f.f.U query: uniform f.f does not prove uniform f.
    } else {
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // NORMAL ret.f.f.f.U fits the global limit.
        // Saved W covers it before relative C5; no fresh method demand.
    }
}
// Inner block DEMAND: none. New method DEMAND: none.
```

For actual calls, the saved method reader is applied **before** this
current admission. It still produces `b.U` from the real `a.f.U` input.
The second call yields `c.U`, `c.f.U` and `c.f.f.f.U`, all NORMAL and all
within limit 4. Main emits NormalTarget only. The combined frontier is
empty and both references naturally finish after **run-5**.

The long-read generalization does not need the full read prefix as an
initial. Run-2 still cuts to `p.f.NE`. Run-3 starts at `p.f.U` and every
subsequent read is uniform. There is no unfolding of all `f.g.h...` paths.

## 7. Safety checks

| Risk | Required rule |
| --- | --- |
| Lose the field-root witness when splitting | Keep `p.f.$` as well as the nonempty child. Delegate only a completely covered child case; otherwise retain ordinary processing. |
| Export a query partition as an exclusion | G is local plan metadata. All emitted results retain their ordinary genuine E; no artificial G enters a fact or summary. |
| Share an initial between incompatible plans | Freeze a safe common delegation mask. Every sharing consumer must have coverage, or the coarse operation runs normally. |
| Reject a needed coarse wrapper offer | Admit a possible bounded STAR refinement for MAY/NE only; bind current results through that admitted query. |
| Confirm a guessed point | Concrete guessed EXACT and STAR support is DEMAND. Possible bindings cannot compose NormalTarget. |
| Change a precise selector | Ancestor STAR still cannot satisfy precise STAR/EXACT demand. |
| Clean away a needed descendant | Cleaner transfer and protection are unchanged; do not use EXACT-only admission. |
| Reverse uniform summaries unsoundly | No backward MUST initial; retain the existing DEMAND reverse view, as in BB run-4. |
| Let MAY union erase next-step progress | Separate bounded refinement heads from executable output coverage. |
| Reintroduce field enumeration | One observed field per row, no recursive plan expansion, both original bounds enforced. |
| Lose a real cut demand | Never suppress actual global cuts or their DemandTargets. |
| Cross-pair output permissions | Combine coverage only within identical complete Dp groups; C5 keeps each original row. |
| Skip hidden method observations | Precover only duplicate publication, after observations, with a whole-service NORMAL provider. |

## 8. Proof and activation scope

The [constructive Lean package](../../spec/lean/proposals/bounded-refinement-frontier-20261114/README.md)
checks the one-field covers and query-count bound, unchanged initial/C5
depth bounds, concrete projection layers, exclusion/mark guards, precise
selector rejection, no backward MUST starts, the complete five-run neutral
prefix reference, source permission replay and the extra BB weak-MUST view.
It does not assume a completed NORMAL reader before starting the trace.
`LocalRouting.lean` is the current no-artificial-E reference. It proves that
routing changes no emitted transfer result and forwards NORMAL results
unchanged. Its fixtures check the unmodified initial keys, the absent new
root-EXACT start for a STAR-only offer, a full NORMAL reader which must
transport an f descendant, and the retired promotion-ban example's middle
`q.f = p.h` branch. Both method-only and BB traces still finish at run-5.
The earlier E-based constructors in `Frontier.lean` and `Pipeline.lean`
remain historical geometry/trace references, not the proposed fact encoding.
The subsumption addendum checks the semantic-cover/admission-image
distinction, the unchanged parent bound, same-head coverage, valid NORMAL
discharge, transitivity and arrival-independent captured-head membership.
The publication addendum checks separate local/visible views, precise
callee admission from coarse MAY and wrapper STAR, NORMAL refinement
delivery and protection/mark isolation. These are component results; they
do not assert unchanged caller iteration counts or prove the whole native
call graph by location inclusion alone.

These are design proofs for a declared AP scope, not a binary correspondence
proof for an unimplemented engine change. Native integration must bind the
same qualified admission and NORMAL service predicates to the existing
matcher, aliases, ND and port handling. Keep existing behavior for a case
whose cover/service proof is unavailable. No production change is authorized
by this document.

Local delegation is operational pruning, not a representation-only move of
G. A field set alone is insufficient to justify it: the native operation
must have a complete child-service cover. This reference establishes that
cover for its neutral prefix transfers. It does not prove a blanket ban
for mark observations, negative conditions, cleaners, aliases or arbitrary
ND rules. Those mechanisms keep their ordinary work unless separately
proved covered. Removing G from the fact is not permission to discard G's
old constrained results and export them as unrestricted NORMAL facts.

The approach prevents the supplied stationary cycles without increasing
field limits. An
[ordinary-code counterexample](../reports/bidirectional-bounded-refinement-ordinary-cycle-20261114.md)
has two reads or two writes and two calls. Rebased MUST queries create
new global NE cuts before precoverage; helper heads keep growing and the
same root DemandTarget is regenerated indefinitely. It uses standard
whole-object source/sink rules, no pass rules, loops, recursion or aliases.
The current proposal therefore does not guarantee termination even for
ordinary acyclic code.

The separate [NORMAL uniform NE coverage addition](bidirectional-normal-uniform-ne-coverage-20261114.md)
closes that ordinary-code recurrence in the checked positive field-transfer
references. It also retraces the old method-only and BB cases and preserves
the wrapper/cleaner finding routes. Its new subsumption law is an explicit
semantic proposal; it is not part of the unchanged baseline described here.

A separate
[straight-line counterexample](../reports/bidirectional-bounded-refinement-acyclic-nontermination-20261114.md)
uses the unchanged, permitted `AnyField` pass-target rule: its intrinsic
MAY renews `ZERO -> DemandTarget` indefinitely even without loops or
recursion. The current plan provides no retirement rule for this case.
It is not a general termination decision procedure for
arbitrary recursive programs. Do not retire an unresolved demand merely
because no new count or NORMAL row appeared. Supported refinement must
advance a bounded head, obtain a provider, or keep the unresolved region.

Native acceptance checks are: uncapped method-only and BB regressions;
the longer-reader variant; exact-child preservation; the selected-cleaner
survivor; the historical wrapper/child-demand finding; the precise-selector
rejections; both NORMAL/DemandTarget arrival orders; and field/mark/H/port
isolation. Record actual latest reached and completed runs, findings and
peak facts. A successful run-11 cutoff is not a termination result.

No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**. The **run-5** result here is the checked
reference experiment, not a project timing measurement.
