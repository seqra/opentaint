# Work reduction: C2, loop probes, diagnostics and handoff compaction

12 November 2026. **Specification; no production change.** The investigation
campaign remains stopped. This is the combined specification for handoff
compaction and the two selected proposals from the
[run-11 next-iteration document](../docs/design/bidirectional-run11-next-iteration-20261109.md):
**Prune impossible C2 candidates and reject losing loop probes early**, and
**Remove the disabled unresolved diagnostic archive**. It does not reopen
the campaign or authorize changes to AP transfer. FULL caller-input packing
is explained in §15; it is not selected for implementation here.

The rules in §§4–6 have the stated existing operator proofs. The general
MAY rule in §7 has a checked request-language proof, but its native
eventual-refinement proof is incomplete. **Do not enable that rule without
the additional proof in §10.** An ND certificate that uses that MAY rule has
the same restriction. An ND certificate using only the exact query rules
does not have this extra gate.

The two added work-reduction features (§§12–14) preserve the current complete
per-run semantic results. They do not use the weaker eventual-findings
contract of generalized MAY coarsening. Their local proofs and source
correspondence are in §16. They can be developed independently of §7.

## 1. Contract and semantic scope

Let `j = i+2`. Compact after run-j completes, during the transition to
run-(j+1). Never remove an edge from run-i in response to its repetition at
run-j. Repetition is useful evidence; it is not a required algebraic guard.

The selected correctness contract is:

```math
For each sink identity s:
  s has a finite refined finding derivation without compaction
    ⇔ s has a finite refined finding derivation with compaction.
```

Assume no iteration limit, fair processing and completion of each run used
by the derivation. A permanent resource limit is not a proof of redundancy.
This contract does not require termination on every input.

**Major change:** generalized MAY coarsening can change intermediate
initials, frontiers, confirmation timing and the number of iterations.
The exact query rules have the stronger existing service-equivalence proof.
The current run-11 limit is unchanged in production; its provisional results
and confirmation status are not covered by the weaker eventual contract.

| Part | Current behavior | Specified behavior |
| --- | --- | --- |
| Saved NORMAL relations | Persist eligible admitted records; existing stores compact some relations. | Compact old and new eligible NORMAL records with the native relation rules. |
| Outgoing guidance | Project every selected final origin; the demand builder deduplicates rows. | Select a checked retained origin basis before building demand. |
| Concrete EXACT/STAR DEMAND conclusions | Can project two equivalent late point requests. | Keep one representative under §5. |
| ND guidance | Project every conclusion leaf against every premise member. | Omit an origin only when every such row has retained service witnesses. |
| General MAY coverage | No Y-only native refinement proof. | Define the candidate order, but require the §10 proof before activation. |
| Local C2 candidate lookup | Visit strict-descendant terminals which STAR/EXACT actuals always reject. | Skip only those empty-emission visits; preserve the complete ordered emission stream. |
| Loop prefix trial | Build a full observation even after an extra admission makes equality impossible. | Reject that budget on its first exact extra admission; preserve the chosen cut and fallback. |
| Disabled unresolved-call diagnostic | Allocate a run-1 archive and retain full facts before a no-op JVM callback. | Expose disabled state and skip archive creation, updates and callbacks. Enabled observers keep their existing protocol. |
| Completed-run observations | Report, source hits, NORMAL contributors and normal Targets are collected independently. | Preserve these collections and their commit rules. |

The handoff compactor applies to **FULL late local handoffs**, where the next
run is at least run-3. It handles both methods and generated method-inner
blocks, in either direction when the native origin shape is legal. The
campaign's measured cuts were later forward handoffs, at least run-5; those
measurements do not establish counts for other barriers. Bypass this new
compactor for run-1→run-2 and for GROUP mode. Keep their existing processing.

Keep these mechanisms unchanged: C2 initial emission and its FLOW companions;
C5 summary restriction and field budgets; field transfer; cleaners; full
marks; aliases; protection; the opposite-direction STAR-inside policy;
source permissions; Target kinds and report identities; loop liveness and
growth gates; the field-limit schedule. Do not close a proof gap by silently
changing one of them.

For §§12–14 there is **no selected analyzer semantic change**. Trie-work and
probe counters, allocation IDs and elapsed time can differ. On common
completed frontiers, decoded initials, summaries, demand, Targets, findings
and confirmation status must agree. A faster run can reach a later frontier
under the same time limit. The observer change does not change enabled
diagnostic callback counts: the optional broader enabled-archive removal
from the old proposal is out of scope.

## 2. Frozen inputs and identities

Only use demands, admitted summary edges and submitted initial facts already
available when run-j joins. The rules below need positive retained edges;
they do not need a missing-offer argument or an earlier-run capture.
Do not inspect an actual run-(j+1) offer, source code, CFG properties, JVM
types, finding counts or an iteration limit to decide a pattern.

```text
Γ       full method/context, stored direction, block and physical ports
H       literal non-subsumable membership: plain or protected
P       complete initial: one member or the complete ND set
C       conclusion packet, possibly with several concrete paths
N       old saved NORMAL records ∪ new eligible NORMAL records
O       every current origin selected for outgoing guidance
G(X)    complete native next-demand projection of origin X
K       final retained guidance origins, a subset of O

$ = EXACT; * = STAR; MAY = [any]; MUST = [any-taint]
E = field exclusions; mx = FLOW mark exclusions; T = full concrete mark
```

Compare decoded identities, not allocation numbers or unchecked hashes.
Keep protection memberships separate: plain cannot cover protected, and
protected cannot cover plain. If identical geometry has both memberships,
keep both. Metadata for a proof must not enter runtime equality or hashing.

There are two separate results:

```text
Native relation cover: saved applications of removed X are supplied by N'.
Guidance cover:        C2 admission and paired C5 restriction survive in K.
```

An equal guidance projection does not prove native relation cover. A
NORMAL record does not supply an outgoing demand row merely by existing.
Use a NORMAL provider to discharge refinement only in an already proved
native FLOW-backed cell. Do not infer a new such bridge here.

## 3. Projection and services

Compute G with the current handoff operators, before deleting anything:

```text
G(P → C) = union over leaf c in C and member p in P:
               (next owner/ports, entry=g(c), paired output=g(p))
```

Reverse block ports exactly as today. `g` changes MUST to MAY and clears
its E; clears FLOW mx and FLOW/STAR E; preserves other legal coordinates.
For DemandTarget, use the existing typed Target entry and ZERO/DATA paired
output. NormalTarget is not outgoing refinement demand.

O includes the origins currently selected by `RunSummaryStore.demandEdges`,
including forward NORMAL ND origins, plus the existing outgoing Target
origins. A normal singleton not selected by that predicate is not added to O.
Backward summaries remain single-premise. Preserve the rule that run-1
cannot retain an ND original.

Each projected row supplies two services:

```text
C2(entry, offer)       -> complete initial family and support profile
C5(entry, output, raw) -> admitted original and restricted output profile
```

C2 includes layers, FLOW companions, owner/port support and MAY precision
information. C5 keeps the complete original, its physical exit and the
relative field budget. If a member of an ND original admits that original,
do not replace the original by just that member.

Projection is available now. Calling it does not run the next iteration.
An expression involving hypothetical offers in a universal operator proof
is also different from inspecting future observed offers.

## 4. Saved NORMAL relation compaction

Apply these rules only to actual eligible native records in N, in the same
complete Γ and H. Do not start persisting DEMAND or multi-premise records.
Keep NORMAL FLOW records with legal nonempty initial E. Keep the current
backward-ZERO and backward-MUST persistence restrictions.

### 4.1 Literal payload inclusion

```math
X=(Γ,P,C_X,NORMAL,H), Y=(Γ,P,C_Y,NORMAL,H)
LiteralLeaves(C_X) ⊆ LiteralLeaves(C_Y)
────────────────────────────────────────
Y covers X
```

Compare the full P and literal path/tail/mark/E/mx/H of each output leaf.
The existing per-leaf application produces the same removed replies from
Y, including the opposite view. No correlation or layer changes.

Example after run-j:

```text
X: p.*/FLOW → ret.f.*/FLOW, NORMAL
Y: p.*/FLOW → {ret.f.*/FLOW, ret.g.*/FLOW}, NORMAL
Keep Y. Its real f leaf supplies X in both read directions.
```

### 4.2 Correlated NORMAL FLOW specialization

```text
S: a.u.* / EiS   → b.v.* / EoS, NORMAL FLOW
L: a.u.r.* / EiL → b.v.r.* / EoL, NORMAL FLOW

ES = EiS ∪ EoS; EL = EiL ∪ EoL
require same Γ, same H, same bases and same shift r at BOTH endpoints
require mxS ⊆ mxL
if r is empty: require ES ⊆ EL
else:          require ES admits r's first counted field
```

S covers L. A suffix `τ` used by L has the executable witness `r ++ τ`
in S. Preserve legal named-static anchors. Check each packed output path
against an actual retained path; do not form input/output Cartesian products.
Use the current overlap matcher and opposite-only STAR-inside policy.

```text
S: p.*   → ret.*,   NORMAL FLOW
L: p.f.* → ret.f.*, NORMAL FLOW
actual: p.f.g.$/T
Both produce ret.f.g.$/T. Keep S.
```

The existing FLOW-backed diagonal concrete cells can also compact native
records under their current mark, geometry, layer and H guards. In
particular, an actual NORMAL FLOW provider can cover its plain T
specialization when T is not excluded. This rule is transitive: a factored
view of S can witness the T specialization without retaining L. Never
publish a fabricated intermediate relation.

These are existing laws from
[the AP subsumption spec, §3](edge-subsumption-initial-emission-demand-intersection.md#3-relation-subsumption).
This document does not add arbitrary NORMAL postcondition weakening.

## 5. Exact DEMAND subsumption rules

These rules remove **outgoing guidance contributions**, not saved NORMAL
transfers. Every compared row keeps its full owner, ports, typed kinds,
mark and H. Conclusions below are individual leaves of a complete packet.

### 5.1 Weaker same-head premise, identical conclusion

```text
X: a.f.MUST/T → C, DEMAND
Y: a.f.*   /T → C, DEMAND

G(X): (g(C); a.f.MAY/T)
G(Y): (g(C); a.f.*  /T)
```

Require empty E on the compared projected DATA selectors and otherwise
identical headers. Keep Y. Every fact satisfying X's premise also satisfies
Y's premise. More strongly, the two projected selectors have the same
current C5 program. Their entries are identical, so C2 also agrees.

This is B1. It does not justify substituting a stronger MUST premise for a
weaker NORMAL premise during live execution.

### 5.2 Concrete same-head EXACT/STAR conclusion

```text
X: P → a.p.$/T, DEMAND
Y: P → a.p.*/T, DEMAND
```

Require the identical complete P and full T. The projected EXACT entry
must have empty E; the projected STAR entry can have any legal E under the
existing late concrete-point policy. Supported executable bases are This,
Argument, Return, LocalVar, Exception and legal ClassStatic anchors.
Exclude literal-backed and cleaner-temporary bases. Do not use this rule
for FLOW or GROUP entries.

Both entries emit the same concrete EXACT initial family with the same
actual-derived layer and no STAR primary/FLOW companion. Their C5 entry
images agree. Keep Y; X adds no service. Same-head MAY or STAR submitted
facts can give provisional EXACT starts; the claim concerns emitted
initials, not a requirement that the submitted fact already be exact.

This is B2. Raw native `$` and `*` outputs can still apply differently;
that does not invalidate the handoff-only result.

## 6. General exact-service certificate, including ND

The two rules above are instances of a retained-service basis. Use this
more general check when different retained rows supply the two services:

```text
entryKey(q):
    normalize legal late FULL concrete STAR/EXACT entry to same-head EXACT
    otherwise preserve the entire typed entry
outputKey(q):
    normalize empty-E DATA MAY selector to same-head STAR
    otherwise preserve the entire typed output

C2Cover(q,z):
    same complete entry owner/port and entryKey(q) == entryKey(z)
C5Cover(q,y):
    same complete owner/exit/outputKey
    and (entryKey(q) == entryKey(y)
         or proved first-counted point-to-MAY C5 containment)
```

The last adapter permits an empty-E full-concrete MAY entry at the point's
own path or immediately before its first counted extension. That extension
has zero or more CLASS accessors followed by one FIELD/ELEMENT and no
later accessor. It supports ordinary This, Argument, Return and LocalVar;
it does not extend to Exception or ClassStatic. Retain the same field-limit
and legal-shape guards. The complete checks and operator proof are in
[retained demand service basis](retained-demand-service-basis.md).

```text
coveredOrigin(X,K):
    rows = G(X)                         # complete, nonempty projection
    for q in rows:                      # every output leaf AND ND member
        require some z in G(K): C2Cover(q,z)
        require some y in G(K): C5Cover(q,y)
    return true
```

The witnesses can be different origins. Neither can be removed from final
K. A row code without a literal retained provider is insufficient.

### 6.1 ND summary guidance

```math
X: {I_1,...,I_n} → C
∀k, ∀c∈leaves(C), ∃ retained C2 and C5 witnesses for (g(c);g(I_k))
───────────────────────────────────────────────────────────────────
Omit X's outgoing guidance contribution
```

The simple same-conclusion case is:

```text
X: {p.$/T, q.$/U} → ret.$/V, DEMAND
Y:  p.$/T        → ret.$/V, DEMAND
Z:         q.$/U → ret.*/V, DEMAND

G(X) has BOTH (ret.$/V; p.$/T) and (ret.$/V; q.$/U).
Y supplies the first; Z supplies the second by the point-entry rule.
Keep Y,Z. Omit X's guidance. Keeping Y alone fails.
```

A broader form allows different Ck when each supplies the required
services. The proposed semantic form is
`Req(C) ⊆ intersection_k Req(Ck)` with one matching retained arm per Ik.
An arm that relies on generalized MAY coverage must pass §7/§10 too.
The request-language inclusion alone is not a native C2 proof.

**This does not replace live AND execution by OR.** Keep complete ND
originals, caller binding, normal rule contributors and report metadata.
A NORMAL ND origin can lose its guidance contribution if the certificate
passes. It does not become a persisted unary record. A NORMAL unary row
which supplies no outgoing projection is not automatically an arm witness.
Ordinary Horn implication alone does not establish the guidance theorem.

### 6.2 Split-service example

All these origins exist after run-j:

```text
X: b.*/U → a.f.$/T, DEMAND    qX = (a.f.$/T; b.*/U)
Z: c.*/U → a.f.$/T, DEMAND    qZ = (a.f.$/T; c.*/U)
Y: b.*/U → a.MAY/T, DEMAND    qY = (a.MAY/T; b.*/U)

Keep Z,Y. qZ supplies qX's C2 family; qY supplies its paired C5 program.
```

This is the accepted C1 certificate. Z is a sufficient exact-admission
witness. The old proof does not establish that Z is intrinsically necessary.
Removing X using only Y is the broader rule below.

## 7. Proposed generalized DEMAND conclusion coverage

Fix Γ, full mark, H, legal static anchor and the identical complete P.
Initially use empty E for this new adapter. Nonempty-E native relation
subsumption in §4 stays available; it does not prove this demand adapter.

```math
Req(a.p.$/T) = Req(a.p.*/T) = {a.p.$/T}
Req(a.p.MAY/T) = {a.p.s.$/T | s is a legal suffix}

X=(Γ,P,Cx,DEMAND,H), Y=(Γ,P,Cy,DEMAND,H)
Req(Cx) ⊆ Req(Cy)
─────────────────────────────────────────────────
Candidate: Y covers X's refinement obligation
```

For packets, require a real retained covering leaf for each removed leaf.
The two DEMAND origins must already exist. Do not invent a broader Y.
This gives the following algebraic order:

```text
same-head STAR covers EXACT                 # exact-service proof available
ancestor MAY covers descendant EXACT/STAR   # native progress proof open
ancestor MAY covers descendant MAY          # native progress proof open
ancestor STAR does NOT cover deeper EXACT   # late concrete point policy
```

Do not use this as NORMAL relation containment. STAR is a correlated
suffix in native transfer and a late point request here; MAY is an uncertain
refinement obligation. Do not coarsen marks or merge typed controls.

### 7.1 Handoff example and the outstanding native step

```text
X: b.*/U → a.f.g.$/T, DEMAND
Y: b.*/U → a.MAY/T,   DEMAND

The point a.f.g.$/T belongs to Req(a.MAY/T).
Proposed result: keep Y, omit X, without an independent exact C2 witness.

Hypothetical NORMAL offer: a.f.g.$/T
C2 using X: a.f.g.$/T, NORMAL
C2 using Y: a.f.*/T, DEMAND, plus current FLOW companions
C5 using Y does not accept the literal deep initial a.f.g.$/T in this step.
```

The request order is proved. Native C2 is not extensional in that order:
it stops after the first new field. Thus the change needs a contextual
refinement/progress proof, not a claim that current initial families are
equal. The missing initial is not itself a demonstrated lost sink.

Even a one-field case can differ on coarse or uniform inputs:

```text
demand a.f.$/T; actual a.f.MUST/T,N -> a.f.$/T,N
demand a.MAY/T; same actual       -> a.f.*/T,D + FLOW companions
```

The user selected eventual refined findings as the contract for these
differences. That selects the theorem to prove; it does not establish it.
Keep the §6 certificate, including its C2 witness, until §10 is discharged.
Do not alter initial emission or field handling to make the proof pass.

## 8. One handoff procedure

```text
compactHandoff(j, completedRun, savedRecords):
    require all workers joined and completedRun.status == COMPLETE
    observations = prepareOrdinaryReportsSeedsTargetsAndContributors(completedRun)
    O = freezeAllSelectedMethodAndBlockOrigins(completedRun)
    G = projectEveryLeafAndEveryMember(O)      # before any NORMAL compaction
    N = savedRecords union eligibleNewNormalRecords(completedRun)

    if unsupportedNewCompactionScope(j):
        return ordinaryHandoff(N, O, observations)

    Nfinal = nativeNormalBasis(N)              # §4; actual final providers
    K = O
    for X in stableDecodedEdgeOrder(O):
        trial = K minus {X}
        certificates = rebindAllRemovedOrigins(O, trial)
        # Check all earlier removals too. Every witness ends in trial.
        if allExactServiceCertificatesPass(certificates):
            K = trial
        # A generalized MAY certificate may be used only after §10 passes.

    require every removed origin is covered by the SAME final K
    demand = buildNativeDemand(union(G[Y] for Y in K))
    counts = successfulNativeInsertCounts(demand)  # not raw-origin counts
    prepareNormalPersistence(Nfinal)
    preserve observations and other ordinary handoff state
    commit using the existing cancellation/report protocol
    apply the ordinary stop/continue test to the actual compacted demand
```

Both saved views and next-demand views must be complete before release.
Do not mutate the live summary stores during analysis. Do not project O
from Nfinal: it would lose legitimate NORMAL ND guidance and control rows.
Preserve the current seed-index and NORMAL-contributor construction even
when a summary's guidance is redundant.

Recheck all affected certificates when a witness is removed. Transitivity
allows `A covers B` and `B covers C` to become `A covers C`, but the final
witness must be A, not absent B. No permanent witness pin prevents that
rebinding. No self-witness, empty representative set or mutual deletion.

Stable ordering by full decoded values makes the plan independent of
arrival order. This is a deterministic sufficient basis, not a minimum
edge-set claim. Handoff is too late to undo current-run delivery; savings
apply to saved storage and subsequent work.

### 8.1 Complete state example

```text
NORMAL: N0 p.*→ret.*, N1 p.f.*→ret.f.*                 # FLOW
DEMAND: X b.*/U→a.f.$/T; Z c.*/U→a.f.$/T; Y b.*/U→a.MAY/T

§4: persist N0; omit N1.
§6: omit X's guidance using Z for C2 and Y for C5.
Result: saved {N0}; next rows {G(Z),G(Y)}.
```

No future offer is needed to compute this plan. A later Y-only plan would
have a different proof obligation (§7).

### 8.2 Why individual removals cannot be unioned

```text
A: a.f.*/T → ret.MAY/T,  DEMAND
B: a.f.*/T → ret.MUST/T, DEMAND
G(A) = G(B)

Either origin is redundant alone. Keep at least one in the joint plan.
```

This is a projected equality, not raw MUST/MAY transfer equality. Retain a
NORMAL provider separately if it is required by persistence.

## 9. Guards and counterexamples

| Required guard | Example if it is removed |
| --- | --- |
| Same H | A plain FLOW route cannot erase a protected T dependency. A protected-only provider cannot erase the plain membership either. |
| Same full mark | `ret.$/T` does not provide `ret.$/U`; an input with only U loses its request. |
| Same physical ports | Loop repeat→repeat and entry→exit rows deliver to different continuations even if their APs are equal. |
| Complete ND projections | Removing `{p/T,q/U}→ret/V` using only the p arm removes the q-output demand row and its source/refinement service. |
| Literal retained provider | Deleting both A and B in §8.2 leaves no query. A proof cycle emits nothing. |
| Demand-specific order | Late demand `a.*/T` rejects deeper `a.f.$/T`; demand `a.f.$/T` admits it. Ancestor STAR is not ancestor MAY. |
| Correlation in NORMAL cover | `p.*→q.*` maps p.f.$ to q.f.$; `p.f.*→q.*` maps it to q.$. Different endpoint shifts cannot be removed by §4.2. |
| Both exclusions | `p.*→q.* {f}` cannot cover `p.f.*→q.f.*`: its output excludes that branch. |
| Native provider eligibility | Persisting a DEMAND Y as NORMAL would turn an approximation into a guarantee. ND records are not made persistable by this spec. |
| No future data guard | No observed offer after j can justify a decision made at j. Use the universal operator law and current edge witnesses. |

Keep exact typed equality for ZERO/Target services. Do not merge NormalTarget
IDs, use a DATA prefix to cover Target, or infer a ZERO seed from an empty
AP projection. Existing sink identity and backward rules remain in force.

## 10. Proofs, open obligation and activation gates

The constructive model is
[HandoffCompaction.lean](lean/proposals/in-handoff-compaction-20261112/HandoffCompaction.lean).
Its finite checker stores actual final provider values and a witness for
every ND arm. It proves complete request-language coverage, with typed
controls and full-header equality. It also proves the separate abstract
retained-service theorem used by the exact C2/C5 rule.

| Claim | Proof and native correspondence | Status |
| --- | --- | --- |
| Literal payload cover | Per-leaf constructive theorem; native per-leaf union/application. | Proved component. |
| Correlated NORMAL cover, exclusions, FLOW-backed cells | Existing AP spec §3 and its operator/proof package. No added native case here. | Reused in its existing scope. |
| DS-PRE and DS-POINT | Complete canonical C2/C5 profiles, existing RQS proof and isolated native controls. | Proved in stated late FULL scope. |
| Complete ND exact-service cover | Project every member/leaf, apply retained-service cover to every row, union replies. Complete originals stay intact. | Proved composition of existing operator laws. |
| MAY request order | Constructive prefix witnesses; order is transitive. | Proved semantic component. |
| Joint plan and transitivity | All witnesses are final retained values; checked plan preserves the complete semantic union. Exact service basis uses the same final-provider rule. | Proved component. |
| Eventual refined findings for exact-service cuts | Equal service oracles preserve each continuation with unchanged state; hence all finite derivations. No iteration cutoff premise. | Existing RQS continuation proof, reused. |
| Eventual refined findings for Y-only MAY cuts | Need native contextual simulation and progress through C2, C5 and later handoffs. | **Open; activation blocked.** |

For the open bridge, prove the following for any surrounding retained edge
set, not only the displayed example:

```text
simulate(fine derivation using X, retained Y):
    construct a finite coarse derivation using Y
    keep source permissions, required ND members and typed control reachability
    account for every first-field C2 projection and paired C5 relative cut
    show that a required finite suffix either remains available via NORMAL
        replay or is exposed by finitely many refinement steps
    preserve protection, cleaner survivors, block ports and static anchors
    prove the ordinary empty-demand stop cannot discard that pending derivation
    produce the same valid sink identity, possibly at a later iteration
```

Prove both inclusion directions for final refined findings. Request-set
inclusion alone does not rule out either lost refinement or a spurious
stable finding. A finite rank on an isolated suffix is insufficient unless
the native transitions preserve that rank argument and its permissions.

No native whole-engine counterexample to the general MAY proposal has been
established. This document also does not claim its missing proof is complete.
The activation gate is a proof requirement, not a request to change transfer
semantics. If it cannot be proved, keep §6 or present a traced counterexample
and request a separate behavior decision.

The new model has 17 checked claims; its successful audit uses only
`propext` and `Quot.sound`. No `Classical`, `sorry`, `native_decide` or
extra axiom is used. See the
[proof package](lean/proposals/in-handoff-compaction-20261112/README.md).
The request-language model is explicitly not a full Kotlin analyzer model.

## 11. Required validation and complexity

Before implementing, bind decoded native origins and query keys to the
formal checker. Test missing ND members, wrong marks/ports/H, packet leaves,
literal controls and final-provider rebinding. Test every native application
direction used by a removed saved record. Preserve exclusion overlap and
input-alias closure from the existing AP spec.

Before enabling a new rule, use small real-code cases with source/sink
rules: exact/STAR pairs, field-shifted NORMAL pairs, both ND members,
selected cleaners, named statics, nested calls and loop blocks with
ZERO/Target. Compare valid eventual findings under natural completion with
no hard iteration limit. Missing one intermediate initial alone is not a
sink-loss case. Also compare intermediate profiles for the exact-service
rules, which claim the stronger contract. Test every arrival order and a
three-edge transitive chain; confirm no stale removed row is published.

Index first by full Γ/H/mark and complete premise/paired selector keys.
Exact-query lookup is hash lookup plus full-key comparison. A conclusion
prefix trie can propose MAY candidates in `O(path length + matches)`; it
does not supply the open proof. ND checking costs one pair of lookups per
projected member/leaf. Do not enumerate premise subsets or origin products.
The reference global recheck can be quadratic or worse; an implementation
may index affected certificates, while preserving the same final-basis test.
No reduction factor follows from origin counts alone.

No new project scan was run for this spec. Latest original evidence:

| Project | Latest reached | Completed | Accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

The stopped campaign has 8,915 individual redundant-origin classifications
and a separate 6,955-origin joint plan; 19,716 targets remain unresolved.
Those are guidance counts, not removable NORMAL-record counts. The evidence
and scope are in the [pattern catalog](../docs/design/bidirectional-demand-edge-redundancy-patterns.md).
Large samples remain in the [external archive](../docs/reports/EXTERNAL_DATA.md).

## 12. Prune impossible local C2 descendants

The current `FrozenDemandTrie.visitCountedNativeOrder` visits ancestors of
the actual path, then the same node and its subtree. The current
`RestrictedInitialPolicy.emit` has this strict-descendant branch:

```text
demand.path strictly extends actual.path:
    primary exists only if actual.tail is MAY or MUST
    # Additional mark, E, budget and legal-shape guards can still reject.
```

`emitAdmissions` returns immediately when the primary is absent. It cannot
emit either FLOW companion after that failure. Therefore all such visits
are useless for a STAR/EXACT actual, in either direction and either layer.

```text
visitCandidates(actual, kind, visit):
    node = root(actual.base)
    if node is absent: return
    for accessor in actual.path:
        visitValuesWithExistingMarkProfilesAndOrdinalOrder(node, visit)
        node = node.child(accessor)
        if node is absent: return

    if kind == INITIAL_C2 and actual.tail in {STAR, EXACT}:
        visitValuesWithExistingMarkProfilesAndOrdinalOrder(node, visit)
        return                             # skip STRICT descendants only
    existingDepthFirstVisit(node, visit)    # unchanged for MAY/MUST and C5
```

Use raw path-prefix order, including CLASS accessors. A demand strictly
below the actual cannot also be its ancestor or same-path demand. Do not
change the original child order, same-node ordinal order or mark-profile
selection. Cancellation checkpoints remain on the surviving traversal.

| Actual | Local demand terminals | Before | After |
| --- | --- | --- | --- |
| `x.*/FLOW,N` | `x.MAY/FLOW`, `x.f.MAY/FLOW`, `x.f.g.MAY/FLOW` | Visit three; emit only `x.*/FLOW,N`. | Visit the root; emit the same initial. |
| `x.$/T,N` | `x.$/T`, `x.f.$/T` | Same-path exact emits; child rejects. | Same-path exact emits; child is not visited. |
| `x.MAY/T,D` | `x.f.$/T` | Emit `x.f.$/T,D`. | Unchanged; descendants remain enabled. |
| `x.MUST/T,N` | `x.f.$/T` | Emit `x.f.$/T,N` if E admits f. | Unchanged; E still filters each result. |

Apply the filter to the two production INITIAL_C2 visitors: `offer` and
run-2 `requireFamily`. Neither receives a contribution from an empty
family. Run-2 direct/static-carry/transitive completion stays on its current
path. Reach/ZERO admission stays on its control path. DATA entries of a
control pair use the same C2 law. Run-1 does not use restricted C2.

Do not prune OUTPUT_C5 or change `precisionCursors`. A cursor can refer to
a deeper MAY demand even when the current STAR/EXACT C2 primary is empty.
This specification preserves C2 results, not arbitrary side effects of a
user-supplied enumeration callback or exception timing for corrupt inputs.

For an actual path of length h and D strict-descendant nodes, a local
STAR/EXACT query visits the ancestor spine and same node instead of that
spine plus D nodes. It also removes their profile tests and rejected emitter
calls. MAY/MUST query complexity is unchanged.

The loop probe also needs a stoppable **internal** C2 traversal. The current
Unit callback cannot stop the DFS by returning from the callback. Add one
native traversal primitive whose callback returns CONTINUE or STOP and
whose result distinguishes COMPLETED from STOPPED. Ordinary `offer` and
`requireFamily` adapters always return CONTINUE. The probe returns STOP on
the first extra emission. Keep one traversal implementation and preserve
its order/profile logic; do not add a second approximate candidate walker.
STOP is not cancellation. Propagate cancellation normally, and run the
existing query-count finalization on either normal traversal outcome.

## 13. Reject losing loop prefix trials on an extra admission

Keep all current loop bypasses, scalarization, prefix order and the three
consumer computations. The complete `LoopObservation` contains four exact
set components:

```text
adjacent initials; repeat initials; labelled admissions; enclosing results
```

Enclosing results still include saved composition, normalization, liveness,
paired C5 and typed Target handling. Their complete scope, exit, original,
layer and H remain part of equality. Query execution must stay side-effect
free: no actual subscriptions, requests, sources, statics or publication.

### 13.1 Compare exact descriptors before interning

For a real local C2 emission, use this descriptor:

```text
(consumer scope including physical entry,
 ADJACENT or REPEAT,
 emitted Pattern = base + full path + tail + full mark/mx + E,
 emitted layer)
```

Obtain the baseline descriptor from `admitted.initial.toPattern()` and its
layer; attach the same existing scope/family label. Obtain the candidate
descriptor from **every** result of `policy.emitAdmissions`, including its
FLOW companions. Apply exactly the existing consumer-view liveness check
to the candidate before querying that view. An admission has no separate H
coordinate; candidate packet H and the complete original remain in the
query context and in enclosing observation, not silently erased.

For every legal emitted pattern p, the current interner has the structural
round trip `ap.initial(p).toPattern() == p`. It interns path/exclusion
identity without changing their contents. Thus descriptor membership agrees
with the current `AdmittedInitial` set, without allocating hypothetical
initials. Do not compare allocation IDs, bare field paths, cursor witnesses
or demand terminals instead of actual emissions.

Use labelled comparison only when the native view exports that exact
scope/family. A generic view with only aggregate admissions uses the full
observer. Run-2 transitive/static-completion queries also use the full
observer. The fast trial path is for supported frozen local DATA views at
run-3 and later, in either direction.

### 13.2 One trial pipeline

```text
restrictLoopResult(raw, storedSummary, original, consumerViews):
    apply existing run-1, ZERO and non-growing-summary bypasses
    baseline = completeObserver(raw, original, consumerViews)
    if baseline.isEmpty: return DROP
    baselineKeys = decodeExistingLabelledAdmissions(baseline)

    for budget in existingProperPrefixOrder(raw):
        candidate = existingLimit(raw, budget)
        completedFamilies = []
        losing = false
        if supportedFrozenLocalDataViews(candidate, consumerViews):
            for V in existingAdjacentAndRepeatViewOrder:
                if not existingLivenessAllows(V, candidate):
                    completedFamilies += emptyFamily(V)
                    continue
                family = newTrialLocalDescriptorSet(V)
                for d in prunedLocalC2Candidates(V, candidate):
                    for emission in policy.emitAdmissions(d, candidate, candidate.layer):
                        key = descriptor(V.scope, V.family, emission)
                        if key not in baselineKeys:
                            losing = true; break all local-query loops
                        family.add(emission)
                completedFamilies += family
        if losing:
            discard trial scratch
            continue                         # reject THIS budget, not the fact

        observed = completeObserver(candidate, original, consumerViews,
                     reuseCompletedFamilies=completedFamilies)
        if observed == baseline: return candidate
    return raw
```

A real extra admission is sufficient for rejection because current
observation sets only add exact memberships. Later C2 families and enclosing
results cannot remove it. Plain/protected enclosing memberships are also
kept separately; there is no later OR-upgrade which cancels a member.

Absence of an extra admission is **not** acceptance. A candidate can omit a
baseline member or change only an enclosing result. Keep the complete
comparison. Do not revive `certifiedFirstBudget`, skip a range of budgets,
use a longest-demand shortcut or stop the whole loop analysis.

If a probe finishes without an extra witness, reuse each completed C2
family in `LoopAdmissionBundle` for adjacent, repeat and labelled views.
Materialize each admitted initial only when needed by the full comparison.
Do not perform a second complete C2 traversal. An existing quantum-cache
answer can be decoded instead. Do not cache partial families after an early
abort or retain trial scratch across owner turns/iteration handoffs.

### 13.3 Principal negative and fallback examples

The reconstructed Conductor run-8 probe, field limit 7, has:

```text
raw: x.MapValue.Iterable.Element.*/FLOW,N
complete local baseline family (all FLOW,N):
    x.$; x.MapValue.*; x.MapValue.$; x.MapValue.Iterable.Element.*

budget-1 candidate: x.MapValue.MAY/FLOW,D
demand:            x.MapValue.MapValue.MAY/FLOW
real emitted start:x.MapValue.MapValue.*/FLOW,N
```

That start is extra in the same scoped family. Reject budget 1 immediately;
the reconstructed full trial has 466 starts. This is not a measured live
query-frequency claim, nor a complete enclosing observation capture.

Conversely, baseline `{a,b}` and candidate local family `{a}` have no extra
member. They are unequal; run the full comparison and reject the candidate.
The same geometry with another scope, family or layer is an extra member,
not equality. An extra companion found after an acceptable primary also
rejects the budget.

## 14. Remove work for a disabled unresolved-call observer

Currently `JIRInterpreter` implements `UnresolvedCallObserver` even when
`externalMethodTracker == null`. `SharedObjects.unresolvedObserver` exposes
that object. Every run-1 call-service owner eagerly allocates `observed`;
an unresolved TAINT input is retained there before `reached` returns without
doing anything. This archive is not used by transfer or summary handling.

Expose a stable capability for the observer's lifetime:

```kotlin
fun interface UnresolvedCallObserver {
    val enabled: Boolean get() = true  // preserve existing generic observers
    fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan)
}

// JIRInterpreter: immutable configuration; callback semantics are unchanged.
override val enabled: Boolean get() = externalMethodTracker != null

// SharedObjects: return the same observer object when enabled.
val unresolvedObserver: UnresolvedCallObserver?
    get() = (interpreter as? UnresolvedCallObserver)?.takeIf { it.enabled }
```

Initialize the call-service diagnostic store to null. Only create it for
the first enabled, reached unresolved TAINT input:

```text
observeUnresolved(ctx, facts):
    observer = shared.unresolvedObserver ?: return   # before any archive work
    if ctx has no existing unresolved ADDED stage: return
    for fact in facts:
        if fact is not TAINT: continue
        archive = observed ?: createExistingAddedFactAccumulator()
        observed = archive
        ref = existingCallerRef(ctx, fact)           # all old coordinates
        if archive.add(ref, fact.layer, fact) has no delta: continue
        observer.reached(ctx.call, fact.base, ctx.plan)
```

The existing run-1/ADDED call-site guard remains. `freeze` releases any
enabled archive as before. With disabled JVM tracking, allocate no archive,
add no qualified facts, compute no diagnostic mark-tree deltas and make no
callback. Preserve the ordinary unresolved call's AP transfer and rules.

Enabled tracking keeps the old full-fact deduplication, callbacks, positions,
pass-rule OR state and ignored-method behavior. Keep generic observers
enabled by default, including their callback contract. Do not infer a
disabled generic observer from missing JVM state. Runtime toggling is not
part of this capability; JVM configuration is immutable.

```java
void send(Node p) { unknownLibrary(p); }
// T reaches the unresolved stage. External tracking is disabled.
// Before: archive p/T, invoke the no-op callback, continue AP transfer.
// After:  skip diagnostic work, continue the identical AP transfer.
```

Do not remove `AddedFactAccumulator` itself: caller subscriptions and enabled
observers still use it. Do not remove enabled deduplication or replace it
with a diagnostic-payload key in this iteration. Those are broader changes
from the old proposal. No data-class/key equality or report identity changes.

## 15. Clarification: FULL input packing versus FLOW subsumption

Packing is an exact representation proposal, **not selected here**. Its
decoder must retain every original full-mark membership and provenance:

```text
{ p.*/T1 → arg.*/T1, p.*/T2 → arg.*/T2 }
    ↔ template(p.*, arg.*), exact full-mark mask {T1,T2}
```

Neither scalar input covers the other. A hypothetical FLOW input is not a
substitute: it does not say that T1 or T2 actually arrived. A NORMAL FLOW
summary describes the result for a supplied input; it is not that input's
mark witness. Likewise a shared geometry template is not an emitted FLOW
initial and grants no new CM permission.

```java
Object copyAndLabel(Object arg) {
    // Source rule: CM(arg, T2) assigns U to the returned value.
    return arg;
}
Object caller(Object p) { return copyAndLabel(p); }
```

At one fixed call owner, assume these qualified inputs actually arrived:

```text
p.*/T1 → arg.*/T1
p.*/T2 → arg.*/T2

NORMAL summary arg.*/FLOW → ret.*/FLOW
    supplies diagonal T1→T1 and T2→T2 return transport.
    Such plain diagonal SUMMARY rows may be FLOW-subsumed.

Later summary arg.*/T2 → ret.$/U, DEMAND
    must find the stored T2 input; T1 does not satisfy it.
    The FLOW summary cannot supply the mark-changing U result.
```

Existing FLOW-backed subsumption deliberately preserves concrete witnesses
needed by CM/source hooks and request/call protocols. It does not erase
the exact caller input archive. `CalleeSubscriptions` uses an
`AddedFactAccumulator`, not `FlowBackedSummaries`; its complete `CallerRef`
contains the original premise, call, caller layer, stage and scope.
Deleting an input after one diagonal summary is applied would also remove
its witness for future publications and mark requests.

If existing subsumption prevents a redundant qualified input from being
offered, that input needs no packing. Measure the residual population.
For residual distinct T inputs, packing can share geometry without losing
their exact marks. Removing that mask would be a different protocol change
which needs its own proof, not an application of summary subsumption.

The old snapshot contains 3,437,574 subscription inputs. Its identity-mark
screen covers 2,904,846 rows in 299,300 templates, with 532,728 scalar
fallbacks. These are potential representation counts, not counts proven
redundant by FLOW, not native packing eligibility counts, and not byte or
speed savings. This spec selects neither packing nor a new input-deletion
rule.

## 16. Combined proof, source correspondence and experiments

[WorkReduction.lean](lean/proposals/in-handoff-compaction-20261112/WorkReduction.lean)
adds 23 checked constructive claims, separate from the 17 handoff claims.
The [source audit](lean/proposals/in-handoff-compaction-20261112/work-reduction-source-correspondence.md)
and [receipt](lean/proposals/in-handoff-compaction-20261112/work-reduction-receipt.json)
pin the inspected revision. They identify the native bridge for each law:

| Law | Constructive argument | Native obligation |
| --- | --- | --- |
| C2 pruning | Blocked primary implies an empty family. Removing only empty families preserves the complete ordered emission list. | Preserve the ancestor/same-node walk, profile/order guards, and both `offer`/`requireFamily` visitors. |
| Descriptor comparison | Decode(materialize(key))=key gives exact membership correspondence. | Use legal `InitialEmission` patterns; preserve all fields/layer and native scope/family labels. No interner-ID comparison. |
| Early trial rejection | The first real extra descriptor supplies a witness of unequal full sets; later union cannot erase it. | Retain exact set union, complete baseline, liveness and routing; stream the actual complete emission family. |
| Chosen prefix | Every fast trial returns the same accept/reject decision; the first accepted budget and raw fallback are equal. | Keep prefix order, bypasses and the complete enclosing comparison. |
| Disabled diagnostics | Old and new disabled traces have equal external output; new traces retain no diagnostic archive. Enabled steps are identical. | Capability must describe an inert disabled callback; diagnostic storage is not read by transfer. |
| Semantic state | Product-state projection is independent of the diagnostic transition. | Keep transfer/rules/subscriptions/Targets independent of `observed`. |

These are local operator/control proofs with explicit source bridges, not
a new full native trie or Kotlin analyzer formalization. Native tests must
bind those bridges before implementation lands. Generalized MAY progress
remains the separate open gate in §10; these technical changes do not close
or depend on it.

The isolated native controls pass 182 assertions for empty-E ordered C2
families, descriptor interner round trips and positive MAY/MUST cases;
see the [native receipt](lean/proposals/in-handoff-compaction-20261112/work-reduction-native-receipt.json).
They do not test a production trie/observer rewrite, which has not been made.

Required focused controls: complete C2 families/order for STAR/EXACT/MAY/MUST,
FLOW/concrete marks, E, both layers and directions; run-2 completion and
requireFamily; unchanged C5/cursors; descriptor interner round trips;
late-extra companions; scope/family/layer differences; missing-only trials;
different enclosing results; unsupported-view fallback; ZERO/non-growing
bypasses; and at most one local C2 traversal for a non-rejected trial.
For diagnostics, test disabled absence of stores/updates/callbacks, enabled
callback parity, generic observers, ignored methods and identical semantic
outputs. Keep the observer a usable Kotlin/Java SAM with its default-enabled
behavior. Preserve existing real finding assertions and known test failures.

After each independently landed mechanism, repeat the baseline FULL project
configuration without changing limits, aliases, statics or rules. Record
visited C2 nodes/profiles/terminals, emission equality, early witnesses,
avoided full observations/saved applications, reused trial families and
initial allocations. Confirm zero disabled diagnostic archives and exact
enabled diagnostics. Do not claim a factor-of-two gain from sample shares.

Validate the technical changes with the same handoff-compaction setting on
both sides. Their equality claim does not mean that enabling handoff
compaction must retain identical raw demand counts: §§4–6 intentionally
change that representation while preserving its proved services.

The run-11 profiles attribute 83.85% of Conductor run-8 execution samples to
loop-observer C2. A reconstructed STAR-root query falls from 4,666 compatible
terminals to two; it is not a measured query distribution. Thingsboard
run-1 has 656,046 disabled diagnostic entries, separate from its subscription
population; archive-exclusive retained bytes are not known. These features
remove that work rather than make its inner operations faster.

The early probe avoids enclosing saved applications only for rejected loop
trials. It does not remove actual saved replay outside the observer. That
scope accounts for 56.12% of Stirling run-9 samples and 42.80% at run-11;
its optimization remains a separate unselected proposal.

Always compare common completed frontier findings and confirmed/provisional
status, plus final outcomes and latest reached/completed/accepted-forward
labels. The baseline table in §11 applies: Conductor reached run-8, completed
and accepted run-7; Stirling reached run-11, completed run-10, accepted run-9;
OWASP completed/accepted run-11. Thingsboard reached run-1 and OOMed before
any completed or accepted forward run. No new project experiment was run
for this specification. Run heavy validations sequentially.
