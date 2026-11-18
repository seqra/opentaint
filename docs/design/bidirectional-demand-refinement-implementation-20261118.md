# Demand refinement and termination implementation proposal

Implement the [active specification](../../spec/demand-refinement-and-termination.md)
against the FULL core at `8da26aa135809354c584ebac202d5438302b9229`.
The review used `e342cdfba0bcab1bc2915d394056ac677f21e5ab`, which has
the same production code. The snippets below are pseudocode. Follow
the [proof guide](../../spec/proof-guide.md) for each implementation step.

## 1. Scope and implementation order

| Step and rules | Current behavior | Proposed behavior |
| --- | --- | --- |
| 1. R01–R03, R13, R29/R30 | A field cut gives MAY. An EXACT input can retain a strict child during a nested overwrite. | A real cut gives nonempty MAY (NE) in all FULL runs. Reject the strict-child keep and retain the same-head keep. Preserve literal protection and complete ND application. |
| 2. R04–R10, R20–R22, R32 | Same-head MAY offers start STAR. C5 checks the normalized premise. | Split the MAY admission family, prepare one level of children and admit backward run-2 STAR relay. Test the raw C2 image first, then normalize and restrict with the same row. |
| 3. R11/R12, R14–R16, R18/R19, R23–R25, R34 | Saved-first replay and ordinary reply delivery are native. A saved same-direction descendant STAR guard can fail on a shorter STAR offer. | Add NE and the possible saved reply. Deliver the coarse and child results. Keep distinct admitted NE guidance and recheck native compaction. |
| 4. R26/R31/R35/R36 | Selected EXACT cleaning can demote concrete MUST. Partial cleanup can keep coarse DEMAND. Disjoint FLOW leaves can inherit mark masks. | Keep concrete MUST support for selected EXACT, with the specified precision tradeoff. Partition restricted NORMAL MUST residuals. Mask only intersecting FLOW leaves. |
| 5. R27/R28/R33 | FLOW-first scheduling and native typed handoff. | Prioritize ready exact, NORMAL and control work per owner. Project NE through the existing typed and static handoff. |

The semantic changes can change starts, guidance and report timing.
Selected EXACT cleaning of MUST can keep the cleaned point as a
possible observation with its original layer. Reuse the native field
schedule, GROUP policy, alias effects, block liveness, rule conditions,
run-1 singleton-origin approximation, source permissions and typed
control processing. R37–R40 are [future work](../../spec/demand-target-retirement.md).

**Activation.** Select the policy before run-1. Enable the revised
C2/C5 bundle and its tail semantics only within a scope whose comparative
proof covers the actual transfers, boundary routes and stop test.
Use the native protocol for the whole connected analysis when that
proof is incomplete. A per-call fallback would need a proved bridge
for earlier history and incoming DATA, including NE rows. Use policy
injection for native comparisons during development. This gate requires
no runtime proof search or second analyzer pass.
[Comparative activation contract](../../spec/demand-refinement-no-loss-audit.md#5-joint-proof-and-activation)

## 2. Access paths and field transfer

Add NE to `Facts.kt` and to the existing FLOW and TAINT leaf
representations. A DATA actual or conclusion with NE has layer D and
empty field exclusion E. NE is also legal in frozen entry selector
Dc. Reject it at owned initials, executable premises and saved NORMAL
record endpoints. Keep the native grammar for EXACT class markers.

```text
cut(leaf, budget):
    if FL(leaf.head) <= budget: return leaf
    head = prefixBeforeFirstDiscardedCountedAccessor(leaf.head, budget)
    return leaf at head with tail NE, layer D, E empty // keep mark, mx, H
```

Reuse the trie walk and remaining-budget memoization in `Limit.kt`.
Class anchors cost zero fields. Keep within-limit MAY leaves separate
from cuts. At each leaf preserve the literal protection H and layer.
Test scalar and packed decode equality, including mixed MAY/NE and
plain/protected memberships. Pass rules transport H.

Use explicit tail cases in the AP transfer and matching paths.
A known read consumes the named field and keeps NE. An unknown read
from NE can exhaust the suffix and gives MAY/D. A write that prepends
f to a MAY tail gives `x.f.M` while f fits and `x.NE,D` when f is cut.
Exact-root conditions reject NE at the same head. Strict descendants
can match on D. For R13, filter an EXACT actual out of the strict-child
overwrite keep per leaf. Apply the parallel same-head keep with its real
overwrite exclusion. For example, after `x.f.g = new Node()`, the raw
`x.$/FLOW,N` produces `x.$/FLOW{f},N` and no `x.f.M/FLOW,D` child.

## 3. C2 and bound offers

Extend `RestrictedInitialPolicy` with the family in
[spec §2](../../spec/demand-refinement-and-termination.md#2-field-transfer-and-c2).
Use the same operator for method entry, block entry and loop admission.
Extend entry postings to include the eligible strict-descendant M/NE
rows, including R06. Revalidate existing pruning and coverage tests
in `DemandResultCoverage` and prepared loop probes against the full
family, including companions.

At equal heads, the table gives the primary raw identities. Filter
illegal static anchors, base, marks, E and bounds before admitting
them. The MUST column is forward only.

| Dc | EXACT actual | STAR actual | MAY actual | NE actual | MUST actual |
| --- | --- | --- | --- | --- | --- |
| Concrete EXACT | EXACT | ∅ | EXACT/D | ∅ | EXACT |
| Precise STAR | EXACT | STAR in backward run-2, ∅ otherwise | EXACT/D | ∅ | EXACT |
| MAY | EXACT | STAR | EXACT and STAR | STAR | MUST |
| NE | ∅ | STAR | STAR | STAR | MUST |

For a deeper actual, EXACT rejects. Precise STAR admits only the
backward run-2 identity with its selector E. MAY/NE use the first
new counted field. At that child, take the actual's exact and
nonempty cases. If the actual is deeper still, use child STAR.
For a deeper Dc, EXACT actual rejects. MAY/NE leave a possible
MAY at Dc, and a permitted MUST descent stays uniform. STAR can
descend only for the named possible M/NE or prepared-child query.
Check the excluded first field for all descents.

FLOW starts have N support. Concrete STAR starts have D support.
Concrete EXACT and MUST need definite N input for N support.
Each successful concrete STAR authorizes its FLOW STAR companion.
A deeper accepted actual under MAY also authorizes the exact FLOW
prefix probe. NE forbids exact starts at its own head, including
that probe. R07 copies nonempty E from a STAR or MUST actual to
eligible same-head empty-E STAR commands under concrete demand,
including their FLOW companions. R08 then handles the deeper case.

```text
offer(boundOffer, owner, entryPort):
    applySaved(boundOffer.originalActual)  // even when C2 is empty
    plan = []
    for row in entryPostings(owner, entryPort, boundOffer.actual):
        primaries = scalarTable(row.Dc, boundOffer.actual)
        family = primaries + authorizedFLOWCommands(primaries, row, boundOffer)
        family = applySameHeadMaskThenDeeperHead(family, row, boundOffer) // R07, R08
        family += prepareOneFieldChildren(row, family, boundOffer.actual)
        plan.add(boundedCommands(family, row, boundOffer))
    if plan is empty: return
    submitUniqueStarts(plan)
    applyCurrentAndSubscribe(boundOffer, plan)
```

Each command retains its raw AP, starting support and qualified row.
The owner can deduplicate starts by raw AP and support. The caller
keeps each required binding. Reuse the delivery in
`RunMethodCallServices`, `BlockSummaryLinks` and `MethodBlockRuntime`.
Use the original actual for saved and ordinary current application.
For R06, use the possible match only for its raw query, qualified row
and real continuation. Carry its binding support as D. Any
normalization witness belongs to the scoped current publication.

For R09/R10, gather distinct next counted fields from either compatible
deeper frozen rows with the same complete Dp or eligible saved NORMAL
guards.
A guard `p.f.g.*` contributes f only. Check masks, marks, path and
physical route. When the eligible parent family has a same-head STAR,
derive the child's exact and nonempty residuals from the original
actual. Use the parent's cap and keep ordinary companions. New child
commands cannot choose fields or start grandchildren. Both coarse
and child results use ordinary application and effect delivery.

| Input | Current starts | Proposed starts |
| --- | --- | --- |
| `Dc=p.M/T`, actual `p.M/T,D` | `p.*/T,D; p.*/FLOW,N` | Same starts plus `p.$/T,D`. |
| Same row, actual `p.f.g.h.MUST/T{k},N`, K≥3 | `p.f.*/T,D; p.f.*/FLOW,N; p.$/FLOW,N` | `p.f.g.h.*/T{k},D; p.f.g.h.*/FLOW{k},N; p.$/FLOW,N`. NE omits the prefix probe. |
| `Dc=p.f.M/T`, actual `p.*/T{f},D` | Empty | Empty. The mask excludes f. |

### Field limits

| Boundary | Bound |
| --- | --- |
| Instruction, replay and offer interfaces, including run-1 | Global K. Count concrete field and array accessors. |
| C2 starts, companions, prepared children and backward run-2 STAR relay | `min(K, FL(Dc)+1)` at the originating row. |
| R08 C2 exception | Restricted forward FULL only. For a concrete M/NE row, eligible primary empty-E STAR commands and their FLOW companions may move to the strictly deeper head of a same-mark NORMAL MUST actual with nonempty E. Copy E at that head. Keep K. A child or EXACT probe cannot use this exception. |
| Fresh C5 DATA outputs, including NORMAL and virtual static/block rows | `min(K, FL(Dp)+1)` at the selected pair. No relative exception. |

R08 replaces commands and keeps their count. There is no second +1
for preparation. Run-1 fresh summaries have no incoming pair.
Saved records and predefined summaries use K on delivery. A fresh
result in the caller still passes C5. The loop own-ZERO exception
skips the extra growth gate. Count R08 overruns and assert all paired
output budgets independently.

## 4. C5, publication and replay

In the revised path of `BlockRunState.retainSummary`, pass the raw
premise to `DemandStore` before FLOW normalization. Return admitted
premise-and-result pairs internally. Adapt the prepared, static and
loop selectors to that interface. Keep run-1's existing boundary
policy and the existing typed control functions.

```text
restrict(rawP, rawPacket, owner, exitPort):
    admitted = exactSet()
    for row in pairedPostings(owner, exitPort, rawP, rawPacket):
        if controlEndpoint(row) or controlResult(rawPacket):
            admitTypedPair(row, rawP, rawPacket, admitted) // same row
            continue
        if no rawP.member passes rawImage(row, member): continue
        for rawC in scalarLeaves(rawPacket):
            P, C = normalizeSingletonFLOWPair(rawP, rawC)
            selected = selectExit(C, row.Dp)
            if selected is absent: continue
            bounded = cut(selected, min(K, FL(row.Dp)+1))
            admitted.add(normalizeSingletonFLOWPair(P, bounded), row)
    return admitted
```

Use the scalar selector in
[spec §3.3](../../spec/demand-refinement-and-termination.md#33-raw-entry-witness-and-paired-output).
A member can authorize an ND summary, and publication keeps the whole
original. The DATA endpoint of a mixed control pair uses the same raw
entry test or scalar exit selector. A concrete selector can authorize
its FLOW companion on entry. An NE result at an EXACT exit's own
head fails, whereas a strict descendant can consume its nonempty
suffix. Normalize only the complete singleton FLOW-to-FLOW pair.
Transport masks and actual overwrite exclusions.

The exit test requires the same base and intersecting mark slots.
Keep the candidate's mark, mx, layer and H. For Dp normalize E on
abstract FLOW STAR only. Use these tail choices after the geometry gate.

| Candidate tail at Dp's head | Dp EXACT | Dp STAR | Dp MAY or MUST |
| --- | --- | --- | --- |
| EXACT | Keep | Keep | Keep |
| STAR | Keep correlation | Keep correlation | Keep correlation |
| MAY | EXACT | MAY | MAY |
| NE | ∅ | NE | NE |
| MUST | EXACT | MUST with union E | MUST |

For a strict descendant candidate, keep it if Dp admits the suffix.
If the candidate is an ancestor, EXACT gives nothing and STAR keeps
the whole correlated relation where descent is admitted. MAY/NE give
EXACT at Dp for an exact selector and MAY there otherwise. MUST
gives EXACT at Dp for an exact selector and MUST there otherwise.
Apply the selector E to the descended MUST only for STAR. Concrete
EXACT has empty E. Incomparable paths give nothing.

**Raw image.** Implement inverse branches of the same C2 family
generator. For each branch, compare the raw command to its output
shape and solve its constraints on the actual. Use the legal actual
domain of the row. The test reference enumerates that domain at
small bounds.

```text
rawImage(row, rawCommand):
    for case in inverseCases(row.Dc.tail, rawCommand.tail, phase):
        constraints = case.bindOutput(row, rawCommand, frozenGuardView)
        witness = chooseLegalBoundedScalarOffer(constraints)
        if witness exists and case.emitsRaw(row, witness, rawCommand):
            return true
    return false
```

| Branch | Shape of the witness to construct |
| --- | --- |
| Equal-head primary | Dc head. Try the scalar table's input tail and support alternatives. For a copied mask use the command's E on the actual. |
| Actual below Dc | The command's first-field head for a one-field refinement. Check both an actual at that head and a strict extension when the branch requires it. For a run-2 STAR relay or point probe, choose an admitted real field below Dc. |
| Actual above Dc | A strict prefix of Dc, including the compatible static anchor if legal for the mark. Select a legal tail and an E that allows the known first field. Require the possible-field guard for STAR. |
| FLOW companion | Reconstruct the primary with the concrete selector mark and the same allowed geometry. For an exact FLOW prefix probe, require a deeper actual that emits at least one primary. |
| R08 or prepared child | R08 uses the command's full head and E on a NORMAL MUST actual. Child inversion uses its frozen child field, parent's cap and the tail choices for the residual at the child. Verify the parent's qualifying family against the same witness. |

Use the row, raw command and prepared field to constrain known
prefixes. For an existential remainder use the required minimum
depth of that branch, and choose a real legal accessor allowed by its
mask. An invented accessor can pass an impossible static or
field-limit case. Resolve finite tail and layer choices and compare
the inverse with the full proposed C2 family in both directions.
No hypothetical path product or offer history is needed at runtime.

Run C5 even if a saved NORMAL edge covers the uncut candidate.
Its paired cap can yield a new DEMAND leaf. Store admitted deltas
only. The current publication index can attach a sparse reference
to the qualified raw query for possible application. A new qualifier
can enable a waiting binding when the ordinary public row already
exists. Handle it as a separate delivery delta with the same admitted
payload. Release qualifiers with their scoped current store. Keep a
single public summary identity and retain no raw exit archive.
Prepared output caches must distinguish raw membership and pair
budgets. Saturation requires coverage of every remaining capped
result.

Extend `Summary.kt` and `PersistedSummaryReplay.kt` with the matching
and result cases in [spec §3.2](../../spec/demand-refinement-and-termination.md#32-match-and-apply-scalar-summaries).

- An explicit NE result keeps its written output head and independent
  suffix. A correlated STAR result transports the known residual
  followed by NE. A descent inside an unresolved NE suffix can
  leave MAY/D at the selected head. Use the existing inside and
  effect guards and complete ND joins.
- Keep definite MUST for actual uniform support and applicable
  provisional replies on D. R34 adds a fallback only after a failed
  ordinary saved same-direction unary NORMAL FLOW STAR-to-STAR
  read on a strict ancestor STAR actual. Check E and native effects.
  `p.f.*→ret.*,N` on `p.*,N` gives `ret.M,D`. The same record on
  `p.*{f},N` gives nothing.
- Keep applicable DEMAND replies beside ready NORMAL replies.
  In `SummaryStorage` and publication indexes, retain qualified
  NE beside wider MAY or NORMAL MUST. Keep native same-layer MUST
  folding and aligned NORMAL FLOW subsumption under their guards.

For P qualified pairs, M original members and L output leaves, use at
most P×M raw image tests and P×L scalar selections. C2 adds at most
`4 + 3·fields` commands per scalar row and offer before deduplication.
Reuse the frozen row and saved guard indexes. Measure scanned postings,
live qualified bindings, output growth and publication fanout.

## 5. Cleaners, scheduling and handoff

Implement the cleaner cases at the normal `Clean.kt` transfer before
repacking and the ordinary cut.

```text
cleanConcreteMUST(leaf, action):
    if disjoint: return {leaf}
    if selected EXACT point is in leaf:
        return {leaf with native cleaner-survivor H}
    if eligible restricted NORMAL partial ALL or selected BELOW:
        for field on relative cleaner path:
            if field already excluded: keep remaining leaf; return
            emit MUST at current head with field added to E
            descend to child with empty E
        if selected BELOW: emit surviving boundary EXACT
    else: use native cleaner
```

The residual has at most depth+1 pieces. Retain the native removal
when the whole region is cleaned. Matching nonuniform EXACT can still
die. In R31 partition the FULL nonstatic FLOW packet by suffix-cone
disjointness. EXACT intersects when the input head prefixes the
cleaner point. BELOW/ALL are disjoint for incomparable prefixes.
Use the normalized suffix cone even for an abstract point probe.
Keep native requests and set the selected marks in mx only on the
intersecting group. At most two packets. For NE keep a D/NE cover
when a partial survivor is unrepresentable.

In the per-owner worklist and publication queues, take ready EXACT,
NORMAL and control work before other uncertain work. Use FLOW first
within each lane. Split mixed packets at the lane boundary while
preserving the logical memberships. Reuse quantum accounting,
cancellation and pending delivery. Validate the same closure for scalar
and packed processing without an inter-owner phase barrier.

Keep `HandOff`, `BlockHandOff` and the driver sequence. Project
admitted D, ND and backward singleton ZERO, plus outgoing DT. Reverse
physical ports and clear the native demand masks. Carry each NE
conclusion at its own head. Persist admitted NORMAL as before.
In `HandoffCompactor`, share identical complete pairs. Revalidate
other DATA compaction against same-entry C2 and same-port paired
C5. Check every projection of an ND origin against the final
retained basis. Missing coverage keeps the row. Keep the native
frontier stop test and report policy.

Extend `StaticGuidance`, `StaticPairLookup` and `C5StaticDemandView`
for run-2. Reuse the frozen static routes, selectors, budgets and
existing shared carry. Require a common point with a nonempty suffix
at every NE endpoint. A named NE writer cannot meet a same-head
EXACT observer. Check C2, C5, Target, preflight and frontier
equivalence on legacy shapes and validate NE ports and anchors.
Keep lookup lazy and later runs local. Keep the reached backward
exceptional ZERO borrow at its genuine normal invocation address.

## 6. Proof and validation plan

Run the constructive proofs before coding each step. Add tests at
the normal entry points and compare complete logical results.

| Obligation | Proof and implementation check |
| --- | --- |
| Field transfer and C2 | A real cut removes a nonempty word. Its old point lies in NE; an unknown read can consume the whole word. The MAY split distinguishes ε and nonempty suffixes. One prepared level adds at most one field. R07 keeps the head and mask together. R08 is the only relative entry overrun, with K still enforced. Check masks, layers and the complete start family against the [scalar proofs](../../spec/lean/proposals/demand-spec-clarification-20261118/README.md). |
| C5 and bounds | For inverse soundness execute C2 on the constructed witness. For completeness take a legal actual that emits the command and identify the inverse case and its constraints. Exercise legal accessor existence, companion and raw EXACT/STAR cases. The same pair witnesses both endpoints and its output budget. FLOW lifting preserves correlation and the real write exclusion. [Rule proofs](../../spec/lean/proposals/demand-refinement-spec-20261117/README.md) |
| Delivery and handoff | Preserve each qualified binding, layer, H and whole ND derivation. Substitute final retained witnesses for each removed projected service. Check offered-before-published and published-before-offered orders, empty current C2 with saved replay, NE static joins and the borrowed ZERO ports. A typed DT still counts in the completed frontier. [Pipeline checks](../../spec/lean/proposals/demand-refinement-implementation-20261118/ImplementationPipeline.lean) |
| Cleaners | The selected EXACT-on-MUST coarsening preserves its region. Each retained subtree point either first differs at a cleaner field or is the BELOW boundary point. Each disjoint FLOW suffix is clean of the selected action. Validate the positive and negative controls in the [rule proofs](../../spec/lean/proposals/demand-refinement-spec-20261117/README.md). |
| Comparative activation | Substitute finite constructive derivations for affected native actions. Cover every required DATA, source permission, control and observation use in the complete retained basis. Check extraction against executed native actions, seeds and physical ports. Scalar proofs alone leave integration and activation obligations open. [Joint service proof](../../spec/lean/proposals/demand-no-loss-audit-20261117/README.md) |

Run the core bidirectional tests and Java adapter tests from source.
Extend existing AP, prepared plan, summary delivery and handoff suites.
Compare the pinned native and proposed policies from the cold start.
Verify the marking-point, full-mark and observer tracks as well as
reports. Include the Conductor MUST route, loop-exit backward ZERO,
two-source same-observer, nested static overwrite and protected input
controls. Record native results separately from references and adapters.
Use the catalogue for termination and soundness controls. The MAY
pass case is outside its active termination scope. Keep stops that
require R37–R40 attributed to that reference bundle.
[Catalogue validation and test command](../reports/bidirectional-termination-fix-validation-20261117.md)

## 7. After implementation: investigate run-11 cutoffs

Run OWASP, Conductor, Stirling-PDF and ThingsBoard, the bidirectional
regressions and the rule-test suites with the production cutoff first.
Record the revisions, rules, heap, timeout, active policy and field
schedule. Compare engine and handoff times, DATA and Target counts,
R08 exceptions, and confirmed/provisional findings. Report latest
reached, completed and accepted forward runs separately. Use the same
inputs and settings for the native and revised measurements.
[Project runs](../reports/bidirectional-work-reduction-performance-20261112.md#3-configuration-and-measurement-units) ·
[Local Gradle procedure](../rule-testing.md) ·
[Bidirectional Java rule runner](../reports/bidirectional-rule-runner-validation-20261109.md)

Verify that cutoff samples used the bidirectional driver. Legacy
runner results are a separate regression gate.
Investigate every completed `RUN_LIMIT` scan or test with remaining
demand. A timeout or OOM in run-11 is an incomplete run. Its earlier
completed handoffs can still be examined. Compare retained H7, H9 and
H11 rows after compaction by method and generated block. Include the
intervening backward handoffs and earlier evidence when needed.
Decode stable row keys with direction, owner, scope, physical ports
and both selectors. Attach producer marks, masks, layers, H and
original ND members. Keep causal links separate from key equality.

```text
for case in completedRun11Cutoffs:
    for rowGroup in H11 grouped by owner and ports:
        trace H9 -> run10 offer/C2/replay/C5 -> H10
                 -> run11 offer/C2/replay/C5 -> H11
        record every producer of the selected row and its actual binding
        compare raw and admitted outputs, cut budget, Target/seed effects,
                and the retained basis from compaction
        locate the first step that renews the obligation or makes progress
        evaluate rule guards on that exact step
        record the classification and reproduction
```

Start with a frontier snapshot. Reuse the existing loop-pipeline
trace and C5 counters for focused reruns. Add diagnostic-only events
if a producer link is missing. Scope the capture by owner and run.
Track dropped or sampled events so a capture gap cannot count as an
absent producer. The final forward barrier builds H11
before returning `RUN_LIMIT`. Compare full post-handoff pairs and
observed causal links; equal counts alone cannot identify a cycle.
Start with FLOW, then plain concrete marks, Targets and remaining
rows. Keep large captures in the [external archive](../reports/EXTERNAL_DATA.md).

| Classification | Required evidence and action |
| --- | --- |
| **Implemented rule, likely bug** | Identify an enabled rule whose full guard holds on the trace. Find the first step that differs from its specified output or from the proved recurrence break under the same assumptions. Extract a regression for that step. |
| **Known LOOP/REC case, rule pending** | Match the trace to the known witness and its LOOP/REC rule guard. Record which rule is deferred or still lacks activation, such as a relevant R37–R40 rule. Compare with that exact reference bundle. The presence of a loop or recursive call is insufficient. |
| **New or uncovered case** | Identify the renewal that falls outside the known guards. Extract a minimal cold-start native test that preserves the renewal and mark-to-observer behavior. Add the trace and status to the [termination investigation](../../term-task.md). |
| **Refinement still making progress** | Trace the changing service, or show a later diagnostic barrier with a genuinely empty frontier. Record the latest run and the evidence of progress. |

If H9 and H11 both carry
`ret.*/FLOW→p.f.NE/FLOW,D`, inspect the raw start and cut. A raw
`p.f.$/FLOW` admitted by that same-head NE row violates R05/R20.
If the starts are valid and the same cut recurs, trace the paired
exit and next DATA or Target consumer before assigning a rule.

Lift or extend the cutoff only in diagnostic tests. Prove an uncapped
recurrence with a constructive invariant over the growing-limit
schedule and check within-run closure. A finite repeat is evidence
for investigation. For each extracted test show per-run demand,
submitted facts, initials and published summaries at each owner,
with the annotations reversed in backward runs. Report each cutoff,
its renewing row groups, applicable rule, disposition, reproducer or
capture gap, and latest reached/completed run.
