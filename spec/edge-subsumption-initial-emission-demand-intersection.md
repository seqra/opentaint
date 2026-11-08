# Subsumption, initial emission and demand intersection

7 November 2026. Finalized 8 November 2026 for FULL-mode implementation.
No analyzer implementation change is part of this document.
Use the pre-implementation core at `52829d5890ec3b3145cc996a1d8162d85cb8ceda`,
which equals the reviewed `52f32dd4` core. The
[frozen baseline](subsumption-redesign-baseline-20261107.md) defines the exact
versions. Follow [proof-guide.md](proof-guide.md).

This document defines the rules. The [principal catalog](subsumption-principal-examples-20261107.md)
contains programs and historical traces, including the two missed Conductor
findings in E29. The [proof package](lean/proposals/subsumption-initial-demand-20261107/README.md)
states what is checked and what still needs native validation. A local proof
is not a proof that the new analyzer recovers every project finding.

The [8 November gap audit](subsumption-loop-and-gap-audit-20261108.md)
retraces the latest emitter through run-5. Run-2/run-3 now close publication
and saved-replay feedback with the same seven/three paired demand sets.
Its corrected run-4 trace closes saved replay to an ANY fixed point. The
older one-body catalog is not a proved reached program fixed point.
This revision selects three further changes: keep plain and protected
memberships separate; widen selected partial STAR cleaner survivors to ANY;
and bypass the extra loop gate for summaries with their own ZERO premise.
The checked loop route reaches run-5; the cleaner route reaches run-3.
The Conductor-shaped late route is checked; full-project recovery and
native integration remain implementation acceptance checks.

## Finalization and known-gap status

**No further unresolved FN-producing counterexample is currently known in
the reviewed FULL-mode cases under this finalized specification.**

The three identified design gaps have selected resolutions: keep both
protection classes, widen the selected partial STAR cleaner survivor, and
bypass the extra loop gate for an own-ZERO summary. The Conductor-shaped
uniform example has a checked NORMAL route in run-5. Its missing run-3
MUST initial demonstrates delay, not a remaining permanent-FN example.

| Reviewed issue | Final status |
| --- | --- |
| Exact plain/protected duplicates | Keep both; class-specific publication and delivery are checked |
| Selected partial STAR cleaner survivor | Selected ANY/DEMAND repair; checked NORMAL route through run-3 |
| Own-ZERO loop source output | Selected extra-gate bypass; checked NORMAL route through run-5 |
| Conductor-shaped missing MUST probe | Later NORMAL reader and child demand are derived; NORMAL route at run-5 |
| Further confirmed FULL-mode FN counterexample in the reviewed cases | None currently known |

This is the current evidence status, not a universal no-FN theorem. Native
implementation correspondence, real-project quality checks, the general
DATA-premise loop proof and natural convergence remain validation work.
The historical Conductor misses remain mandatory regression checks; their
recovery by the new implementation has not been measured. No further
semantic repair is selected on the basis of those uncompleted checks.
Known GROUP-mode issues are outside this FULL-mode finalization.

## 1. Changes and fixed behavior

| Part | Before this review | Revised rule |
| --- | --- | --- |
| NORMAL relation subsumption | Nonstatic endpoints, Empty E and equal mx | Legal static endpoints are allowed. Compare both endpoint exclusions and the admitted marks. Use the common-suffix rule in §3. |
| Same-head summary matching | Some incomparable field exclusions reject | Match the overlap of STAR/MUST actuals with a STAR endpoint. Union their exclusions; retain the actual support. This is a matching change. |
| Protection classes and delivery | The prior draft kept one OR-upgraded row and separate plain coverage | Keep both exact memberships: H=false and H=true. Deduplicate, subsume, persist and publish each class independently. There is no cross-class OR collapse. |
| Ancestor STAR admission | A STAR actual could sample a deeper exact/STAR demand | Reject an ordinary STAR actual strictly above the demand. Wait for a matching-head/deeper fact or an ANY/MUST actual. |
| Restricted initial emission | Primary plus its concrete-STAR FLOW companion | If ANY demand admits a strictly deeper actual, also emit an EXACT/FLOW/NORMAL identity at the demand head. Keep every existing emission. |
| C5 entry check | Existing normalized expanded-C2 image | Keep that predicate. The new raw prefix seed normalizes to a key already in its image; its raw C2 image proof must include the extra seed. |
| Selected cleaner survivor | A partial concrete STAR/T result stayed STAR/T, DEMAND, protected | Change only that survivor conclusion to ANY/T, DEMAND, protected, with Empty E. Keep its complete premise. Section 6.1 gives the exact guards. |
| Loop output gate | A ZERO-to-DATA row could enter the growth gate because FL(ZERO)=0 | A row with its own effective ZERO premise bypasses the extra loop gate. DATA rows keep the existing growth test. C5 and the global field limit still apply. |
| FLOW demand completion | Earlier draft proposed endpoint-prefix self-pairs and a paired-head permission | Unselected. E21 identifies a loop gate which omits an existing saved NORMAL repeat continuation; it does not establish a need for completion. E28's identity is handled in run-1. |

These three changes modify retained edges, publication and refinement.
They are semantic changes, not storage-only optimizations. Their proof
obligations are P02/P04/P27/P32, P31/P36, and P14/P15/P33-P35.

Keep ordinary field transfer, FLOW cleaner requests/exclusions, full kills,
EXACT/MAY/MUST cleaner results, aliases, complete ND conditions, source
permissions, Target IDs, liveness and stopping rules. Keep the existing
DATA-premise loop gate and its observation. Sections 2.1 and 6 state the
only changes to protection storage, cleaner survivors and loop delivery.
Run-1 keeps its existing abstraction and static layers. The new companion
rule applies to restricted runs, from run-2. It does not make run-1 statics
NORMAL. The FULL schedule remains `1,1,2,3,4,...`; directions alternate.
The optional GROUP mode retains its stated known issues.

The exact prefix probe is a change to initial admission. It can change the
available summaries, loop observations and iteration frontier. It reuses the
existing field-transfer, write-exclusion and FLOW normalization rules.

Never emit ANY as an initial or owned premise. Add no tail kind, grounding
state or discarded-fact archive. `trackFactsReachAnalysisEnd` stays empty.

## 2. Facts and the protection flag

Write a fact as `base.path / tail / mark / E`. E excludes fields immediately
after the known path. FLOW means an unknown mark; its separate exclusion
`mx` lists marks which it does not carry. N and D mean NORMAL and DEMAND.

| Tail | Meaning |
| --- | --- |
| EXACT, `$` | This exact position |
| STAR, `*` | One suffix correlated between the edge's premise and conclusion |
| ANY, MAY | An independent unknown suffix; legal on actuals, conclusions and demand selectors |
| MUST, `[any-taint]` | Definite uniform taint in the region outside E |

A stored edge also has its method/context, direction, block scope and
physical entry/exit ports. `P` means its complete original premise. An ND
premise is an AND of all its members. ZERO and Target are control slots,
not field paths. A static class anchor counts as zero fields; its named
static field counts as one and must remain attached to its class.

### 2.1 Protection classes and delivery

**H is the existing non-subsumable flag on a concrete membership.** A
coordinate means the exact edge and conclusion to which that flag belongs:
owner/ports, complete P, conclusion base/path/tail/mark/E and support layer.
It is not another access-path component or a new analysis mechanism.

```text
same geometry, H=false then H=true -> keep and publish both memberships
same geometry, H=true then H=false -> keep and publish both memberships
same geometry, same flag again     -> no fresh work
parent ANY without H, child with H -> neither subsumes the other
parent ANY with H, child without H -> neither subsumes the other
parent ANY with H, child with H    -> ordinary same-flag coverage applies
pass an unprotected edge          -> still unprotected
```

H protects a marked dependency which plain FLOW coverage must not erase.
For example:

```java
Object m(Box p) {
    Object r = p.right;
    // Source rule: CM(p.left, T) assigns T to r.
    return r;
}
```

The ordinary FLOW comes from p.right. T can instead come from the rule on
p.left. At a coarse limit their images can overlap. A rule triggered by a
T-marked conclusion and assigning T marks that concrete result protected.
Removing it because a plain coarse FLOW image covers it can lose the
left-to-result dependency needed by the next backward run. Keep the
existing assignment, cleaner-survivor and mark-cycle flag producers.
A pass carries an existing flag and never creates one. ZERO and Target
have no protection class; keep their existing control/report deduplication.

Retain canonical plain edges in U and protected edges in H. Apply
subsumption separately within each class. An H=true edge never subsumes
an H=false edge, or the reverse. Protected edges can cover protected edges
when all ordinary coverage tests pass.

If an exact geometry belongs to both classes, store and expose both
memberships. Geometry payloads may share storage, but do not replace the
two memberships with one OR-upgraded edge. Updating H must not delete U.
The flag is part of logical edge identity for deduplication, queues,
publication, replay, loop observations, persistence and restore. A geometry interner may
ignore it; a retained-edge key or freshness test must not.

Do not derive U as `all edges minus H`: the same geometry can occur in both.
Apply this rule to exact scalar memberships before packing, including mixed
mark packets. A shared packed carrier must retain both independent class
memberships at an overlapping coordinate. Temporary result unions and loop
observation keys must retain the class too; do not OR it away in a query
helper before storage or delivery.

```text
offer(edge):
    view = H if edge.protected else U
    fresh = canonicalInsert(view, edge.geometry)  // same-flag subsumption only
    if view changed: invalidate coverage-dependent caches
    for geometry in fresh:
        publish(geometry, protected=edge.protected)

retainedEdges(U,H):
    return [(g,false) for g in U] + [(g,true) for g in H]
```

Geometry includes every ordinary coverage header, not only the field path.
Let A be a MAY root and B its MAY child, with other headers fixed:

```text
A plain; B plain; A protected -> U={A}, H={A}; expose A/plain and A/protected
A protected; A plain; B plain -> U={A}, H={A}; expose A/plain and A/protected
A protected; B plain          -> U={B}, H={A}; expose B/plain and A/protected
```

Plain A removes plain B in both of the first two orders. Protected A alone
cannot remove plain B. A new plain A after protected A is a fresh plain
membership and must be delivered. A repeat of that plain A is not fresh.
The symmetric rule applies when protected A arrives second. Subscribers
union the received membership into its own class; receiving plain A never
clears protected A.

A pass transports each class independently. It does not merge the classes
when their output geometry is equal. Save and restore both canonical
classes with their owner. Use the final admitted classes in direct and
opposite saved views and in handoff. No hidden plain certificate or raw
offer history is needed. The old render-only counterexample records the
superseded OR contract.

Within each class, MAY covers its descendants; MUST covers its admitted
descendant regions; same-head MUST exclusions merge by intersection.
A complete immediate child can fill one excluded field. A deeper child or
a child with a remaining hole cannot. None of these laws crosses classes.
Retaining two classes can add work relative to OR collapse. Do not claim
unchanged callback counts or a measured speedup.

## 3. Relation subsumption

### 3.1 General correlated FLOW rule

Consider two admitted NORMAL FLOW relations at the same complete interface:
method/context, direction, block scope and physical entry/exit ports. Their
premise paths need not be equal; those paths are compared by the rule.

```text
S: a.u.* / EiS  -> b.v.* / EoS
L: a.u.r.* / EiL -> b.v.r.* / EoL
```

The **same r** extends both endpoints. Let `ES=EiS union EoS` and
`EL=EiL union EoL`. S covers L when:

- Both compared coverage witnesses have the same protection flag. Never
  use a protected-only row to back an unprotected row, or the reverse.
- The input bases agree and the output bases agree. They can be legal named
  statics. Do not remove a static class/field anchor while factoring r.
- Every mark admitted by L is admitted by S. For FLOW mark exclusions this
  is `mxS subset mxL`; equality is a fast case, not a necessity. FLOW
  initials have empty mx, so this compares the conclusion mark exclusions.
- If r is empty, `ES subset EL`.
- If r is nonempty, its first field is not in ES. L's exclusions after r
  can then be arbitrary: S already admits that whole descendant region.

For any suffix tau of L, the executable witness in S is `r + tau`.
Exclusions at either endpoint restrict that same suffix. Thus both endpoints
must be checked. For packed output trees, test each candidate output path
against a retained path with this same correlated shift. Do not enumerate
a Cartesian product of input and output paths.

Example: `S: p.* -> q.* {f}` covers `L: p.g.* -> q.g.* E2` when g differs
from f. There is no reason to require Empty E here. Named static versions
of these same relations obey the same rule.

### 3.2 Matching the retained relation

Subsumption must preserve application, not only a set of abstract pairs.
For a same-head STAR summary endpoint and an actual STAR or MUST fact,
select the overlapping slice with `E = actual.E union endpoint.E`.
Keep the actual tail, mark, mx, supplied H and layer. Apply the relation to
that slice. The result also obeys the relation's output exclusion and the
usual layer join. Do not mutate or replace the original submitted fact.

For example, A is `p.* {f} -> q.*` and B is `p.g.* -> q.g.*`, with f, g and z
distinct. On actual `p.MUST/T {z},N`, the old same-head matcher can reject A
because `{f}` and `{z}` are incomparable while accepting B. The revised
matcher selects `p.MUST/T {f,z},N` for A and obtains a NORMAL q region which
still contains q.g. This closes the application gap before B is removed.

The old reverse example with `ret.* -> p.* {f}` was not such a gap: generic
STAR/STAR inversion clears its read-side E and carries the combined E on the
result. Keep that existing inverse construction.

Strict-ancestor matching of an incoming STAR fact remains allowed only for
opposite-direction saved records. This includes concrete STAR/DEMAND.
Same-head overlap does not enable CURRENT inside matching. MAY matching and
the existing trusted reverse-MUST lane retain their separate rules.

### 3.3 Concrete rows, protection and arrival order

The existing FLOW-backed rule also removes plain diagonal T-to-T rows when
T is not excluded and the FLOW has sufficient support. NORMAL FLOW can cover
NORMAL or DEMAND T; DEMAND FLOW cannot replace NORMAL T. Compare the same
initial geometry after a valid common-suffix specialization. STAR requires
the same correlated output coordinate and compatible E. ANY allows a covering
output prefix. EXACT, MUST and mark-changing rows keep their existing separate rules.
Every backing test also requires equal protection flags. A plain FLOW
companion cannot remove a protected T relation.

If A covers B and B covers C, test C directly against A's computed correlated
view. B need not have been stored. Do not publish a fabricated B. This must
work for A-then-C, C-then-A and one packet. Publication and handoff read the
final admitted basis. A stale queued row cannot remain a provider.

Keep FLOW-first processing. Local concrete memberships still reach CM,
cleaners and source hooks even when their summary is FLOW-backed.

### 3.4 Why the remaining guards exist

| Guard or limit | Example and reason |
| --- | --- |
| Same shift at both endpoints | `p.* -> q.*` does not cover `p.g.* -> q.*`: input p.g.$ maps to q.g.$ through the first row, but q.$ through the second. |
| Same-head exclusion inclusion | `p.* {f} -> q.*` cannot cover `p.* -> q.*`: exact p.f/T is excluded only by the first relation. |
| Admitted suffix at BOTH endpoints | `p.* -> q.* {g}` cannot cover `p.g.* -> q.g.*`. Its output excludes the very g branch which the long row preserves. |
| Mark admission | FLOW excluding T cannot replace a row carrying T. Replaying actual T would lose that result. Equal mx is not required if subset coverage holds. |
| Preserve support | A DEMAND-only route cannot replace a NORMAL route: the next call would lose its NORMAL result/report. |
| Same complete interface | A loop-header record at ports 10→4 cannot replace repeat4→4. It does not deliver to the repeat port. The same applies to different methods or contexts. |
| Real admitted provider | A guessed `p.* -> ret.*` for a method which clears p is not a provider. Removing its marked row on that assumption loses the actual transfer. |
| Equal protection flags | A plain FLOW relation does not replace the protected left-side dependency in §2.1. A protected-only parent also cannot remove a plain child. |
| Full ND matching | `{p/T,q/U} -> ret/V` cannot execute when only p/T is supplied. A one-member admission ticket never removes q/U from P. The aligned rule above is unary; it does not invent ND entailment. |
| Correlated STAR versus ANY | STAR maps a shared suffix tau. An ANY conclusion can independently choose another suffix. The common-suffix proof cannot replace that independent relation by STAR. |
| Opposite-only STAR inside | This is the selected workload policy, not a claim that every inside approximation is unsound. Applying `p.f.* -> q.f.f.*` to ancestor p.* can introduce q.f.f.ANY/DEMAND without a concrete f suffix. The selected CURRENT lane avoids that extra work. |

Nonstatic-only, Empty-E-only and exact-mx-equality were limits of the old
optimization/proof scope. They are not general mathematical necessities.
The broader E rule depends on the explicit overlap-matching change above.

## 4. Initial emission: primary and FLOW companions

This section is C2 for run-2 and later. First require legal bounded shapes,
equal bases and directed mark compatibility: FLOW excluding X accepts full T
when T is not in X, and FLOW excluding Y when X is a subset of Y. A concrete
T demand accepts T, not U or unknown FLOW. Bind a group to its accepted actual
full mark by the existing catalog rule. A FLOW initial has empty mx.

ZERO or Target control guidance admits only the canonical ZERO initial; it
does not create a DATA initial. Keep the existing CFG-reached backward ZERO
port correction. A raw EXACT/FLOW actual with nonempty E can use an Empty-E
view for C2 calculation only. The real actual and its E remain unchanged.

A legal stored FLOW demand entry has STAR or ANY tail. EXACT/FLOW is not a
legal demand-store entry. EXACT/FLOW actuals and raw initials are different
and remain legal. This is why rejecting an EXACT/FLOW demand against ANY
cannot lose a query under the pinned demand grammar; it is not a proof that
such hypothetical admission would always be unsafe.

Normalize abstract FLOW/STAR demand E as before: ignore that selector's E.
Keep actual E/mx/support for later application. Concrete EXACT and ANY have
Empty E. Every proper descent must pass the ancestor's tail/E test. EXACT
cannot descend; ANY can; STAR/MUST can unless the first new field is excluded.
Incomparable paths reject. MUST initials are forward-only.

The primary uses this complete table. p is the demand head and q the actual
head. Its mark is the accepted demand mark.

| Relation | Demand | Actual | Primary |
| --- | --- | --- | --- |
| p=q | ANY | EXACT | p.EXACT |
| p=q | ANY | STAR or ANY | p.STAR, Empty E |
| p=q | ANY | MUST | p.MUST, actual E |
| p=q | STAR or concrete EXACT | Any legal actual | p.EXACT |
| q extends p | ANY | Any legal actual | First new field r: r.STAR; use r.EXACT for concrete T if actual is EXACT exactly at r |
| q extends p | STAR, run-2 | Admitted descendant | Requested p.STAR with normalized demand E |
| q extends p | STAR, later runs; or EXACT | Any | Reject |
| p extends q | ANY | ANY | p.STAR, Empty E |
| p extends q | ANY | MUST | p.MUST, normalized demand E |
| p extends q | ANY | Ordinary STAR or EXACT | Reject |
| p extends q | STAR or concrete EXACT | MUST | p.EXACT |
| p extends q | Any | Ordinary STAR | Reject |
| p extends q | STAR or concrete EXACT | ANY | p.EXACT |
| p extends q | Any | EXACT | Reject |

Each emitted key starts as an identity. FLOW and ZERO starts are NORMAL.
Concrete STAR starts are DEMAND. Concrete EXACT/MUST starts are NORMAL only
when the actual support is NORMAL; an EXACT selected from ANY stays DEMAND.
A concrete DEMAND actual never becomes NORMAL through initial emission.

**Concrete-STAR companion:** whenever the primary is `x.STAR/T,DEMAND`, also emit
`x.STAR/FLOW,NORMAL` with the same base, path and field E. Both are identity
edges. Replace only its mark by FLOW with empty mx. Do not emit this companion
for a rejected primary, a concrete EXACT/MUST primary, ZERO or a FLOW primary.
Deduplicate equal commands using existing entry admission.

**EXACT/FLOW prefix companion:** when the demand is `a.x.ANY` and a
strictly deeper submitted fact `a.x.f...` passes primary admission, also emit
`a.x.EXACT/FLOW -> a.x.EXACT/FLOW,NORMAL`. Use Empty E/mx and no new H.
This applies to both FLOW and concrete-mark ANY demands, in either direction
on restricted runs. Keep the primary and any concrete-STAR companion.

```text
emitInitials(demand, submitted):
    primary = existingPrimary(demand, existingQueryView(submitted))
    if primary is absent: return []
    result = [primary]
    if primary is concrete STAR:
        result += same-geometry STAR/FLOW identity, NORMAL
    if demand.tail == ANY and submitted.path strictly extends demand.path:
        result += identity(demand.base, demand.path, EXACT, FLOW,
                           E={}, mx={}, NORMAL)
    return deduplicateRawInitials(result)
```

Run this same emitter for caller admission, block admission and loop C2
observations. Keep the original submitted fact in its binding, including E,
mark, H and support. The existing query view may clear raw EXACT/FLOW E only
for C2 calculation; it does not mutate that actual. Failed mark/base/shape
admission emits no prefix companion. Same-head or ancestor actuals and
non-ANY demands do not activate this rule. Existing static anchors remain
mandatory; add no class-wide or root-static query.

Keep the added initial and its live facts EXACT during execution. Apply the
existing whole-FLOW-pair EXACT-to-STAR normalization at the summary boundary,
before C5/storage. Preserve paths, E, mx and result layers. Concrete exact
facts, genuine ANY/DEMAND residuals and control results are unchanged.

| Demand | Submitted actual | Additional prefix command |
| --- | --- | --- |
| `a.x.ANY/FLOW` | `a.x.f.$/T,N` | `a.x.$/FLOW,N`; primary stays `a.x.f.*/FLOW,N` |
| `a.x.ANY/T` | `a.x.f.$/T,N` | `a.x.$/FLOW,N`; primary stays `a.x.f.$/T,N` |
| `a.x.ANY/T` | `a.x.f.g.$/T,N` | `a.x.$/FLOW,N`; keep child STAR/T,D and child STAR/FLOW,N |
| `a.x.ANY/T` | `a.x.f.ANY/T,D` | `a.x.$/FLOW,N`; actual support remains D during application |
| `a.x.ANY/U` | `a.x.f.$/T,N`, U!=T | None; primary admission rejects |
| `a.x.ANY/FLOW` | `a.x.ANY/T,D` | None; same-head behavior is unchanged |

These are conditional FLOW analyses, not assertions that the real actual
is NORMAL or has a mark at the shorter exact position. FLOW does not satisfy
CM(T). A direct return can normalize an exact identity to a STAR relation;
an exact prefix cannot read a strict child. The descendant primary remains
necessary for those reads.

This reuses existing field behavior. A strong write below the exact head
adds the required exclusion before normalization. A whole-position RemoveAll
kills it. A selected cleaner keeps its mark exclusion. Nested writes can
still yield ANY/DEMAND residuals; do not promote those results to NORMAL.

```text
Demand: (p.ANY/T, ret.ANY/T); actual: p.ANY/T,DEMAND
Primary:   p.STAR/T    -> p.STAR/T,DEMAND
Companion: p.STAR/FLOW -> p.STAR/FLOW,NORMAL
id(p){ return p; } infers p.STAR/FLOW -> ret.STAR/FLOW,NORMAL
Applying that summary to real p.ANY/T,DEMAND still returns ret.ANY/T,DEMAND.
Later actual p.g.EXACT/T,N has two applicable relations:
  FLOW relation -> ret.g.EXACT/T,N
  T relation    -> ret.g.EXACT/T,D
The admitted NORMAL FLOW can subsume the unprotected diagonal T relation.
```

FLOW is not evidence for CM(T). Rule conditions keep their existing compiler
semantics. In particular, the baseline compiles a residual mark-dependent
pass without that guard and emits a diagnostic; E27 is not a native guarded
pass example. A cleaner which excludes T yields FLOW mx
containing T; the original T exit demand rejects that result in §5.

**Do not guess a deeper point from STAR.** Demand `p.f.EXACT/T` with
submitted `p.STAR/T,DEMAND` emits nothing. It also emits no companion.
The previous demand was propagated to the caller. If that route exists,
wait for `p.f.STAR/T` or a more precise fact, or for an actual `p.ANY/T`
which admits that refinement. A MUST ancestor remains different: it already
proves membership at admitted children. Same-head STAR handling is unchanged.
The finite structural C2 image can remain the same: the removed ancestor
STAR case emitted an EXACT at the demand head, for which a legal same-head
EXACT witness already exists. The actual admission decision does change.

## 5. Intersection after splitting field chains

A previous-run edge is `Dp -> Dc`. Dp is one field chain; Dc can contain
many. A current candidate is `P -> C`. P is one field chain; C can contain
many. Split Dc and C first. Each inner operation then sees exactly four
scalar chains: `(dp -> dc)` and `(p -> c)`. Keep the original pair's owner,
ports, mark/exclusion headers and Dp budget. Never flatten different demand
edges into one unrelated pool of entry and exit chains.

The split is a reference presentation. A native trie implementation can
perform the same operation without materializing every scalar combination.

**FLOW companion handling is an entry check, not mark synthesis.** A
concrete dc can admit a FLOW p only if that p is an authorized companion:
replace its FLOW mark by dc's concrete T, check the concrete STAR primary's
C2 image and raw containment, then restore FLOW. Do not reject it afterward
with `markSub(T,FLOW)`. The paired dp stays unchanged. In particular, a T
exit rejects a FLOW result whose mx excludes T.

`primaryImage(dc)` below is the existing normalized C2 primary image, with
the existing raw EXACT/FLOW preimage of stored STAR/FLOW. The ancestor-STAR
rejection changes actual admission, but not that finite structural image:
EXACT-at-head results still have a legal same-head EXACT witness. The
concrete-STAR companion is the existing additional normalized-image branch.
The exact prefix companion adds a raw EXACT/FLOW preimage, but its public
STAR/FLOW key is already permitted: a FLOW ANY selector has that root-STAR
image, and a concrete ANY selector has it through its existing concrete-STAR
FLOW companion. No new paired-exit rule is needed.

```text
intersectEdge(previous=(dp -> Dc), current=(p -> C), run, L):
    require matching owner/context/direction/scope/physical ports
    require p and dp are single legal DATA chains
    (p,C) = existing whole-FLOW-pair normalization(p,C)
    entries = splitFieldChains(Dc)      // each dc keeps its original headers
    outputs = splitFieldChains(C)      // each c keeps mark/mx, E, layer and H
    result = empty exact union
    for dc in entries:
        entryKind = NONE
        if p belongs to primaryImage(dc):
            entryKind = PRIMARY
        else if p is STAR/FLOW and dc requires concrete T:
            twin = p with mark=T
            if twin is a legal concrete STAR primary in primaryImage(dc):
                entryKind = FLOW_COMPANION   // explicit second C2 output
        if entryKind == NONE: continue
        for c in outputs:
            selected = intersectChain(c,dp)
            if selected is empty: continue
            k = min(L, fieldDepth(dp)+1)     // this original pair's dp only
            if fieldDepth(selected) > k:
                selected.path = prefixThroughKFieldsKeepingStaticAnchor
                selected.tail = ANY
                selected.E = empty
                selected.layer = DEMAND
            if selected is EXACT/FLOW: selected.tail = STAR
            result += (unchanged p -> selected)
    return packExactUnion(result)

intersectChain(c,d):                    // one conclusion and one dp chain
    d = d with E cleared only for FLOW/STAR
    if bases differ or mark slots have no overlap: return empty
    // Keep c's mark/mx, support and supplied H. Never create a concrete mark.
    if c.path == d.path:
        if c.tail in {EXACT,STAR}: return c
        if c.tail == ANY:
            return c with tail=(EXACT if d.tail==EXACT else ANY), E=empty
        if c.tail == MUST:
            if d.tail == EXACT:
                return c with tail=EXACT, E=(c.E if c is FLOW else empty)
            if d.tail == STAR: return c with E=(c.E union d.E)
            return c                           // d.tail == ANY
    if c.path extends d.path by nonempty suffix:
        return c if d.tail/E admits suffix else empty
    if d.path extends c.path by nonempty suffix:
        if c.tail == EXACT or c.tail/E excludes suffix: return empty
        if c.tail == STAR: return c             // retain correlation
        if d.tail == EXACT: return c with path=d.path, tail=EXACT, E=empty
        return c with path=d.path,
            E=(d.E if c.tail==MUST and d.tail==STAR else empty)
    return empty                               // incomparable field chains
```

Here EXACT admits only an empty suffix, ANY admits every suffix, and
STAR/MUST admit a nonempty suffix when its first field is not excluded.
Full marks T and U overlap only if equal. T overlaps FLOW only if T is not
excluded. Keep native catalog-aware mx/GROUP overlap operations.

The reviewed alternative rebases ANY/MUST as above, but rejects STAR when
d.path strictly extends c.path. This is a semantic change, not a simpler
form of the same intersection. [E30's two-read trace](descendant-intersection-and-flow-completion-review-20261107.md)
shows a required NORMAL `p.f.f.* -> ret.*` relation in run-3. Rejecting it
loses the return route under current C2 unless another mechanism supplies it.
The same review checks an alternative coarse `ret.*/FLOW` start in run-2:
it produces a root-ret output demand, so the proposed STAR rejection passes
the run-3 relation without completion. Current C2 does not emit that extra
start; adding it is a separate admission-policy change.
The selected rule above remains unchanged during this review.

### 5.1 Scalar examples

Except where shown, E and mx are empty, H=false and marks are T. These are
conclusion intersections after the independent entry check has passed.

| c from current summary | dp from previous demand | Scalar result | Reason |
| --- | --- | --- | --- |
| `x.$/T,N` | `x.ANY/T` | `x.$/T,N` | Exact result is already inside the selector. |
| `x.ANY/T,D` | `x.$/T` | `x.$/T,D` | Provisional exact result stays DEMAND. |
| `x.*/T,D` | `x.$/T` | `x.*/T,D` | Do not break the premise/conclusion suffix correlation. |
| `x.MUST/T {f},N` | `x.*/T {g}` | `x.MUST/T {f,g},N` | Both exclusion sets apply. |
| `x.f.g.$/T,N` | `x.f.ANY/T` | `x.f.g.$/T,N` | One extra field fits the paired budget. |
| `x.f.g.h.$/T,N` | `x.f.ANY/T`, L>=2 | `x.f.g.ANY/T,D` | The pair's budget is 2; cut the third field. |
| `x.f.g.$/T,N` | `x.f.$/T` | empty | An exact parent does not select a descendant. |
| `x.MUST/T,N` | `x.f.ANY/T` | `x.f.MUST/T,N` | Uniform taint includes f. |
| `x.ANY/T,D` | `x.f.$/T` | `x.f.$/T,D` | The unknown suffix can contain f; support stays D. |
| `x.*/T,D` | `x.f.$/T` | `x.*/T,D` | C5 conclusion selection keeps the correlation; this is not C2 admission from a STAR actual. |
| `x.$/T,N` | `x.f.ANY/T` | empty | Exact x does not taint x.f. |
| `x.MUST/T {f},N` | `x.f.ANY/T` | empty | The actual excludes f. |
| `x.f.$/T,N` | `x.g.ANY/T` | empty | Different branches. |
| `x.$/U,N` | `x.ANY/T`, U!=T | empty | Different concrete marks. |
| `x.*/FLOW,N`, mx={} | `x.ANY/T` | `x.*/FLOW,N` | Keep FLOW, not T; the original T exit can accept it. |
| `x.*/FLOW,N`, mx={T} | `x.ANY/T` | empty | FLOW excludes the requested T. |

All selected outputs retain the supplied H. Subsumption after packing uses
the same-protection coverage views from §2.1. A real field cut sets DEMAND;
no operation upgrades an actual DEMAND witness to NORMAL.

### 5.2 Controls and the current implementation

The scalar DATA kernel does not turn ZERO or Target into field chains.
Keep these typed cases: Dc ZERO/Target admits only canonical ZERO P; a DATA
Dc rejects ZERO P; Dp ZERO accepts only Reach or DemandTarget. NormalTarget
keeps its NORMAL-forward, NORMAL-composition, persisted-dedup protocol.
Run-1 has no previous demand snapshot and uses its existing global limit.

P is unary in the kernel. An existing ND adapter can check a member while
retaining the complete ND original. It still requires all ND arms during
application; do not enumerate premise combinations or replace ND by one arm.

Compared with the current implementation:

- The normalized C2-image check, paired output selection, paired FL+1 cut and
  FLOW stored-form normalization already exist.
- The new entry branch is the explicit FLOW companion. Strict-ancestor STAR
  rejection changes which submitted facts can start analysis.
- Splitting Dc/C here makes the reference algorithm readable. It does not
  require native unpacking or alter existing scalar-chain output geometry.
- All matching complete demand rows still contribute. One can keep NORMAL
  output while another cuts the same candidate to DEMAND. Do not borrow a
  different row's dp or stop after the first DATA match.
- Strong-write exclusions and whole-position RemoveAll residuals keep their
  existing normalization. Rejected raw candidates are not stored providers.

## 6. Selected cleaner survivors and loop delivery

### 6.1 Partial selected-mark STAR survivors

First execute the existing cleaner base, selected-mark, exclusion and
spatial tests. This change applies only when that operation produces a
surviving concrete STAR/T result from its PART case, and T is selected by
the cleaner. Replace only that result's conclusion:

```text
Before cleaner: P -> x.p.*/T, input layer
Old PART result: P -> x.p.*/T, DEMAND, protected, E
New PART result: P -> x.p.[any]/T, DEMAND, protected, E={}
```

Keep the complete P, owner, paths, full mark and existing protection.
Do not retain the old STAR survivor as a second output. The broader ANY
conclusion remains DEMAND. ANY never becomes an initial or owned premise.
This rule applies in run-1 and later runs, forward and backward. The
existing field-action lowering and reversal remain unchanged.

```text
selectedCleaner(input, cleaner):
    result = existingSpatialAndMarkCleaning(input, cleaner)
    for each scalar result r:
        if cleaner selects r.fullMark
           and r is the PART branch's remaining STAR result:
            emit r with tail=ANY, E={}, layer=DEMAND
        else:
            emit r unchanged
```

The branch is known during cleaner evaluation. It needs no stored provenance
flag, new mark or grounding state. Apply the same rule to individual selected
marks and the selected memberships of a bulk FULL-mask cleanup. Keep all
unselected marks and separate exact siblings in their original classes.
Existing GROUP selected-mark no-kill behavior remains unchanged.

Use the old E-admission test before clearing E. A cleaner under an excluded
field is disjoint and must not trigger widening. Keep these cases:

| Existing cleaner result | Selected behavior |
| --- | --- |
| Partial selected STAR/T survivor | ANY/T, DEMAND, protected, Empty E |
| Same-head BELOW returns EXACT/T | Keep that EXACT result and its existing layer/protection |
| Disjoint STAR/T, including an excluded field | Keep STAR and its E/layer |
| Fully cleaned membership | No result |
| Other concrete mark | Keep its existing result |
| Existing EXACT, ANY or MUST result | Keep its existing result |
| FLOW selected cleaning | Keep mx exclusion and request behavior |
| RemoveAll | Keep its existing full-position semantics; no new STAR-to-ANY rule |

The change loses suffix correlation only on an already provisional result.
Every old STAR pair is in its ANY replacement. NORMAL cleaner results are
unchanged. Existing real field writes and cleaner kills are not weakened.

The principal example is:

```java
// Source: exact T at p.g. Sink: exact T at r.g.
// Run-1 initial: p.*/T,D; parallel FLOW initial stays NORMAL.
Box m(Box p) {
    cleanRootT(p);   // EXACT selected T at p only.
    return p;
}
// Run-1: p.*/T -> ret.[any]/T,D,protected.
// FLOW still excludes T. No NORMAL T provider is guessed.

// Run-2 demand: ret.[any]/T -> p.*/T.
// Submitted: ret.g.$/T,N.
// Initials: ret.g.$/T,N; ret.$/FLOW,N.
// Backward cleaner is disjoint from p.g.$/T.
// Retained: ret.g.$/T -> p.g.$/T,N,protected.

// Run-3: replay its saved opposite relation on real p.g.$/T,N.
// Result: ret.g.$/T,N,protected -> ordinary NormalTarget.
```

The [complete cleaner trace](subsumption-loop-and-gap-audit-20261108.md#34-selected-change-a-partial-start-survivor-to-anyt)
checks source permission and both argument/return rows through run-3.

### 6.2 Saved-first delivery

Replay saved NORMAL records on the original actual first. Then obtain C2
commands, analyze new commands through ordinary transfer and intersect each
candidate by section 5. Store and publish only admitted results. The actual
layer joins each applied summary layer. A NORMAL FLOW hypothesis is not a
NORMAL T input. Keep existing subscriptions, source permissions and static
writer ownership. Process plain/protected memberships independently as in
section 2.1.

### 6.3 ZERO-premise loop output bypass

An applied loop summary with its own effective ZERO premise bypasses only
the extra loop output restriction. For DATA-premise summaries, keep the
existing stored-shape growth test and complete loop observer.

```text
// Before publication, every current candidate still passes normalization
// and paired C5. Saved NORMAL rows keep their existing replay path.

onAppliedLoopSummary(row, parentOriginal, appliedValue):
    F = applyGlobalFieldLimit(appliedValue)
    if row.effectivePremise == ZERO:
        values = [F]
    else if existingStoredShapeTestSaysGrowing(row):
        values = restrictLoopOutput(F)  // same full observer and safe-prefix rule
    else:
        values = [F]
    for value in values:
        deliverFreshAtExistingBoundary(parentOriginal, value)
```

This applies to NORMAL and DEMAND ZERO-owned results in both directions.
Keep their actual layers, marks and flags. A proper global cut is still
ANY/DEMAND. Keep liveness, canonical ZERO admission, actual source permission,
output deduplication and Target handling.

Use the applied row's own premise, never the enclosing parent original.
A source-derived DATA fact can have parent ZERO while an applied DATA row
still grows it. That DATA row is not exempt. For opposite-direction saved
records, use the effective premise after reversal. A genuine ND premise is
DATA and keeps the existing arm-based growth test. FL(ZERO) remains zero;
only the decision to enter the extra gate changes. Run-1 already bypasses
that gate and retains its existing behavior.

A fixed ZERO row carries no incoming field suffix. Its repeated application
produces the same bounded output geometry, which the existing boundary store
deduplicates. DATA summaries can add a prefix to an incoming suffix, so their
growth restriction remains active. Finite field limits do not prove a small
workload or convergence across analysis runs.

For E21 at run-5, the admitted local row is `ZERO -> x.f.f.f.$/T,N`.
The new bypass delivers it to the repeat input. The already saved NORMAL
`x.f.*/FLOW -> x.*/FLOW` relation then gives `x.f.f.$/T,N`, followed by
`x.f.$/T,N`. Existing exact admission and the real body sink yield
`ZERO -> NormalTarget(id),N` at the enclosing owner. No new demand is needed.
Read the [root-cause trace](subsumption-loop-saved-replay-root-cause-20261108.md)
and [selected rule dossier](zero-premise-loop-output-bypass-candidate.md).

Native routing uses the Boolean gate overload. Both `onData` (current and
same-direction saved rows) and `applySavedView` (effective reversed premise)
must pass the correct decision to `onApplied`. Changing only a convenience
PremiseKey overload is insufficient.

### 6.4 Excluded completion and validation boundaries

Do not add the earlier FLOW endpoint self-pairs or paired-head erasure.
E21 is handled by the ZERO bypass, and the cleaner example is handled by
its concrete ANY survivor. E28's ordinary identity already has its NORMAL
provider from run-1. Historical completion models remain comparison evidence;
they are not part of this selected contract.

The ZERO change is not a general theorem for every growing DATA-premise
loop result. That proof and full native port/driver correspondence remain
validation obligations. No further complete FN-producing program has been
established for that DATA-premise case under the final rules. Keep the existing
empty-outgoing-refinement-demand stop rule. Do not use stable demand counts,
a desired iteration number, or a new zero/control seed as a substitute.

## 7. Principal cases and proof boundary

E01-E31 remain required, including wrong-mark/field, protected, ND, static,
loop, selected-cleaner and natural-stop controls. **E29 adds the real Conductor regression:**
proper-prefix DATA canonicalization can delete a finer demand head, although
that head selects a stronger initial. Spatial set inclusion alone does not
prove that removal is harmless for the next iteration.

The captured Conductor query has actual `arg0.workflowDefinition.MUST/Graal,N`.
A root ANY/FLOW guide emits `workflowDefinition.STAR/FLOW,N`; the removed
same-head ANY/FLOW guide would also emit `workflowDefinition.MUST/FLOW,N`.
The new concrete-STAR companion duplicates the existing STAR/FLOW command;
it does not itself restore the lost MUST command. Prefix completion of a
retained root selector also does not invent that child coordinate. A real
saved NORMAL transfer may provide another route, but it must be derived
through the actual method body and ports. Do not assume it exists.

The [Conductor example and fact trace](conductor-must-admission-fact-trace-20261108.md)
show the captured query and a small source/mapper/sink program. They distinguish
the latest C2 calculation from historical project measurements.

The small example now has a checked late route: run-4 exact analysis
produces both a saved NORMAL read and a child ANY/DEMAND output. Run-5
therefore has saved NORMAL replay and a same-head MUST initial. This shows
refinement delay, not permanent loss, in that example. Its bad branch can
still emit DEMAND, so do not infer natural completion from the finding.
The two historical Conductor identities remain mandatory implementation
regression checks. Their new full-project outcome is not yet measured.

The catalog states the exact two missing identities, paired demand row and
rollback evidence. It distinguishes that confirmed mechanism from the
uncompleted fact-by-fact causal chain to each sink. Conductor recovery is an
explicit implementation acceptance gate, not a demonstrated unresolved FN
counterexample against this final spec.

The original 684-law package checks the preceding revision's scoped models.
Its primary-only C2 laws are not laws about the expanded emitter; its
literal-H laws do not prove the revised same-flag compaction. The review
supplements check the expanded image, strict-ancestor STAR rejection, scalar
intersection examples, common-suffix exclusions, overlap projection and the
plain/protected coverage rules in their stated domains. The selected update
keeps both exact classes instead of the earlier OR view. Native adapter equality,
all principal program routes, GROUP and whole-driver convergence remain
explicit validation obligations. No new project run or speedup is claimed.

Implement this finalized contract from the pinned baseline. Satisfy the
listed native and project regression checks before accepting the
implementation. Preserve the existing dirty prototype as evidence, and
carry no SOA/new-tail branch into the implementation. If another semantic change is
needed, state its counterexample and obtain the intended behavior first.


Read the [selected-resolution proof dossier](selected-gap-resolutions-proof-dossier-20261108.md)
for constructive arguments, checked domains and the explicit native adapter
limits of all three updates. Historical OR/candidate results are evidence
for their old definitions, not the current selected contract.
