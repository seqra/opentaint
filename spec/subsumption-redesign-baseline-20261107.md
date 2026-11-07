# Baseline contract for the subsumption redesign

7 November 2026. Status: **frozen contract summary for example review**.
This records the proposal before the task's implementation. It is not a new
implementation proposal, a rollback, or a claim that a redesigned analyzer
passes. Review the [principal examples](subsumption-principal-examples-20261107.md)
before drafting the combined subsumption/C2/C5 redesign.

## 1. Exact versions and authority

| Role | Revision |
| --- | --- |
| Exact pre-implementation task state | `52829d5890ec3b3145cc996a1d8162d85cb8ceda` |
| Analyzer reviewed by that proposal | `52f32dd437d438aec4a700a02c18d94c31d58093` |
| Original proposal introduced | `57bd199df6305eb55dd8a4710e3f3c6d049b4f31` |
| First implementation, outside this baseline | `8331bf9e326ddd1bd5083dbc50456963d6b26b52` |

The entire `core` Git tree at 528 equals that at 52f:
`6a3e587954faf5a5f9bcaf34f47e919edf69b95b`. The original proposal is unchanged
between 57bd and 528. Its Git blob is
`0388fdfb716346b249d838e9045d273257c20c6d`.
The task's f945 fixed quality comparator is a separate reference; it is not
the pre-implementation analyzer revision.

Use the byte-exact [archive and manifest](baselines/subsumption-20261105/README.md).
The primary authority is the
[original implementation proposal](baselines/subsumption-20261105/original-implementation-proposal.md).
Its [field-path design](baselines/subsumption-20261105/original-field-path-design.md)
and [relation/matching audit](baselines/subsumption-20261105/original-relation-and-matching-audit.md)
state the preceding scope. The existing
[FLOW-backed law](baselines/subsumption-20261105/original-flow-backed-spec.md)
and [correlated-concrete extension](baselines/subsumption-20261105/original-correlated-concrete-spec.md)
are part of the baseline context. Historical headers in those files keep
their historical scope. No new runtime or campaign result is claimed here.

## 2. Shared domain and unchanged mechanisms

A fact has a base, known field path, tail, mark, layer and field exclusion E.
`mx` is a FLOW mark exclusion; it is separate from E. H is the per-mark,
per-output-coordinate protection flag. `P` is the complete original premise.

The four tails are EXACT, correlated STAR, MAY/ANY and uniform MUST/ANY_TAINT.
A concrete STAR initial already starts with the same correlated STAR fact on
DEMAND in every run. Run-1 has no ANY initial; later ANY initials remain legal
under the original scalar policy. A universal no-ANY-premise rule is a new
redesign decision, not part of this baseline.

Keep owner method/context, direction, scope, point or summary endpoint,
physical entry/output ports, full P, base, layer and compatible typed headers.
Do not merge independent owners or call stages. Keep source/cleaner/field
transfer, aliases, mark modes/exclusions, ZERO, typed Targets, complete ND joins,
static handling, limits, loop growth/consumer families and the stopping rule.
Keep saved replay, then current C2 admission, then current subscriptions.

## 3. Original spatial MUST/MAY laws

Apply the new spatial rules within compatible same-tail cells, per mark and
protection class. Existing cross-tail MAY rules retain their own scope; the
proposal adds no MUST-to-STAR/EXACT, cross-layer or cross-premise rule.

```text
MAY: x.u.ANY covers x.u.r.ANY.

MUST at one head:
    x.u.MUST/E1 covers x.u.MUST/E2 when E1 ⊆ E2.
    union(MUST/E1, MUST/E2) = MUST/(E1 ∩ E2).

MUST at a deeper head:
    x.u.MUST/E1 covers x.u.f.r.MUST/E2 when f ∉ E1.
    E2 can differ: the ancestor already covers the admitted f subtree.

Exact field fill:
    {x.u.MUST/(E∪{f}), x.u.f.MUST/{}} -> x.u.MUST/E.
    x.u.f.g.MUST/{} or x.u.f.MUST/{h} cannot fill all of f.
```

Fill and cover are per concrete mark. A complete child for T cannot clear a
hole for U. A FLOW child must supply every mark required by the parent;
equal canonical mx is the simple supported fill case. Use native catalog-
aware mx compatibility. Do not enumerate marks, invent positive-only FLOW,
or convert FLOW to TAINT to complete a partial fill.

The original H condition is a protected covering bit for a protected bit.
Protected-prefix coverage can therefore remove a protected descendant under
that original rule. Normalize ordinary/protected masks separately and restore
payload carriers required by mask inclusion. A fill cannot invent protection
at a parent. This differs from the later literal-H decision in section 8.

Canonicalization combines current plus offered data, joins equal-head payloads,
fills complete immediate children, and prunes covered descendants to a local
fixed point. It works on one packet and both arrival orders:

```text
{root,child} in one packet -> root
child then root -> remove child
root then child -> no fresh child
root/E{f} then complete f child -> root/E{}
repeat final packet -> no new support
```

Fresh deltas include new support after header changes. Filter detached batches
against the owner's final authority. Already queued deliveries can finish;
there is no retraction service or historical fact archive.

## 4. C2 and paired C5 in the original proposal

C2 reads only canonical actual facts at calls, block entry and loop observation.
It does not rerun on discarded leaves. This is an explicit semantic choice:
for `x.ANY/FLOW` demand, a root MUST plus covered child MUST formerly selected
a root MUST and a child STAR initial. Canonical-input C2 retains only the root
MUST result. Equality of old literal initial sets is not the claimed law.

The proposal does not redesign the scalar emitter. In particular, later
ANY emission remains possible. A new ordinary-STAR/no-ANY initial contract
must be added explicitly in the combined redesign.

Keep complete paired demand rows. Entry shape alone cannot remove another
row whose paired exit gives a different C5 restriction or field budget.
Existing C5 intersects the actual output under that same row and uses its
exit-relative limit. Preserve actual support layers, E/mx/H and complete ND
execution. An entry ticket does not authorize another exit or an automatic
NORMAL result. The original proposal does not prove whole-driver progress
from fact-set inclusion.

## 5. Aligned NORMAL FLOW relation law

The new relation antichain initially has this exact scope:

```text
S, NORMAL: p.u.STAR/FLOW   -> q.v.STAR/FLOW
L, NORMAL: p.u.r.STAR/FLOW -> q.v.r.STAR/FLOW
S exists and covers L: retain S, remove L from future selection.
```

Require singleton, nonzero, nonstatic FLOW STAR endpoints, Empty field E,
equal canonical native mx headers and the same complete interface. The extra
suffix r must occur on both endpoints. A relation which adds or removes r on
only one side is not covered. ND, Targets, ZERO, static special relations and
protected concrete relations are outside this new relation-antichain domain.

Coverage uses an actually admitted S. If only L exists, keep L. A rejected S,
a shorter path key or a factored empty suffix is not a provider. Do not create
a universal S-to-S identity. If S is only in a saved owner, the current owner
can still publish L; the barrier later merges their authorities.

## 6. Existing FLOW-backed concrete compaction and transitive use

The baseline correlated-concrete extension already applies existing replacement
cells in all runs and directions. Require the same interface and initial
shape ignoring mark, a diagonal T-to-T membership, compatible output base,
tail, layer/E/mx and no protected membership being removed.

- ANY output uses a covering FLOW output prefix, including equal head.
- STAR output uses equal output coordinates and its correlated suffix/E law;
  the ANY prefix test does not apply to STAR.
- A FLOW output excluding T cannot cover T. NORMAL is strong enough to cover
  NORMAL or DEMAND; DEMAND is not strong enough to replace NORMAL.
- EXACT/MUST, cross-mark and protected parts keep their existing rules.

Removing L must not remove its ability to cover a concrete specialization.
Retained S can supply a private transient specialization at `p.u.r`, with
output `q.v.r`. It is a view of S, not a stored/published/handoff relation or
proof that L ever existed. Recheck old and offered concrete groups in both
arrival orders. Thus the original design already requires the transitive
use of S's correlated geometry for concrete compaction.

The first implementation later states A-covers-B-covers-C explicitly and
extends equal-mx relation comparison to native mx subsets. That extended mx
contract is not silently substituted for the original equal-mx boundary.

Current/publication/persistent stores use one admitted authority. Freeze at
the existing joined barrier and rebuild direct, reverse and positional indexes
from it. Covered historical delta records must not remain queryable. Keep all
unrelated scopes and ports. Earlier delivered results are not retracted.

## 7. Directional inside and reverse MUST

For a strict-ancestor STAR actual, allow the inside contribution only when
reading an opposite-direction saved record. This applies to FLOW STAR and
concrete STAR/D alike. CURRENT and SAVED_DIRECT do not gain that branch.
Equal-head, applicable-descendant and ordinary instruction operations retain
their existing behavior. Pass the matching role explicitly.

A separate selected reverse-MUST correction accepts same-head overlap for
incomparable E. The transient overlap is their E union. Its trusted native
constructor retains the old MUST-conclusion provenance and native inverse
result/layer. An old MUST premise alone does not create the capability.
Keep old matches plus the new lane, exact protection upgrades, per-header
selection and physical scope/ports. This changes no field-read rule or
blanket layer/demotion policy.

## 8. Later decisions are separate inputs to the redesign

| Later decision | Difference from the original baseline |
| --- | --- |
| Transitive/mx clarification during 8331 implementation | Explicit no-intermediate A/B/C compaction, mx-subset relation guard and same-coordinate cofinite joins extend the original equal-mx boundary. |
| Keep STAR; retain guide coordinates (4182) | Explicit FLOW/DEMAND/ANY heads survive prefix data coverage. Canonical denotation alone cannot discard operational refinement positions. |
| Concrete guide retention (7069) | The selected concrete DEMAND/ANY positions also survive. This was not an exception in the original spatial antichain. |
| Protected memberships cannot be subsumed (7069) | Literal typed protected coordinates survive even protected-prefix coverage; exact typed duplicates merge. The old protected-prefix law is superseded. |
| Passes cannot add H (e6fb) | Pass effects transport supplied H. They do not create protection. This is an explicit later producer contract, not a proof of an observed baseline pass failure. |
| Nov7 initial-emission redesign | No ANY analysis premise, ordinary STAR instead of new tails, concrete-only admission and retained STAR-demand descendant rejection are later requirements to integrate. |

These decisions are neither folded into the frozen baseline nor revoked by
starting from it. The combined design must state what it retains or revises.
The [standalone C2/C5 candidate](plain-star-initial-emission-and-demand-intersection.md)
is superseded working material. It must not become normative before the
principal examples are traced against one complete redesigned contract.

Local historical proofs and unit checks keep their stated finite scope.
This baseline summary supplies no new native execution, quality comparison,
project convergence, performance or whole-engine correctness claim.
