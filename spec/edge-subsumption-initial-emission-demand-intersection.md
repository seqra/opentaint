# Subsumption, initial emission and demand intersection

7 November 2026. Revised design; no analyzer implementation change.
Use the pre-implementation core at `52829d5890ec3b3145cc996a1d8162d85cb8ceda`,
which equals the reviewed `52f32dd4` core. The
[frozen baseline](subsumption-redesign-baseline-20261107.md) defines the exact
versions. Follow [proof-guide.md](proof-guide.md).

This document defines the rules. The [principal catalog](subsumption-principal-examples-20261107.md)
contains programs and historical traces, including the two missed Conductor
findings in E29. The [proof package](lean/proposals/subsumption-initial-demand-20261107/README.md)
states what is checked and what still needs native validation. A local proof
is not a proof that the new analyzer recovers every project finding.

## 1. Changes and fixed behavior

| Part | Before this review | Revised rule |
| --- | --- | --- |
| NORMAL relation subsumption | Nonstatic endpoints, Empty E and equal mx | Legal static endpoints are allowed. Compare both endpoint exclusions and the admitted marks. Use the common-suffix rule in §3. |
| Same-head summary matching | Some incomparable field exclusions reject | Match the overlap of STAR/MUST actuals with a STAR endpoint. Union their exclusions; retain the actual support. This is a matching change. |
| Protection classes | Literal protected coordinates could not be removed | Subsumption compares equal protection classes. Keep exact OR-upgrade in the visible row and retain its canonical plain coverage. |
| Ancestor STAR admission | A STAR actual could sample a deeper exact/STAR demand | Reject an ordinary STAR actual strictly above the demand. Wait for a matching-head/deeper fact or an ANY/MUST actual. |
| Restricted initial emission | One primary initial | If the primary is concrete STAR/DEMAND, also emit its same-geometry FLOW/STAR/NORMAL identity. |
| C5 entry check | Existing normalized C2-image test | Keep that mechanism and include the new companion in its image. |
| FLOW demand completion | Earlier draft proposed endpoint-prefix self-pairs and a paired-head permission | Keep this as a candidate pending the complete E21 trace. E28's identity is already handled in run-1. Do not assume completion is necessary. |

Keep ordinary field transfer, cleaners, aliases, complete ND conditions,
source permissions, Target IDs, liveness, loop gates and stopping rules.
Run-1 keeps its existing abstraction and static layers. The new companion
rule applies to restricted runs, from run-2. It does not make run-1 statics
NORMAL. The FULL schedule remains `1,1,2,3,4,...`; directions alternate.
The optional GROUP mode retains its stated known issues.

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

### 2.1 What an H coordinate means

**H is the existing non-subsumable flag on a concrete membership.** A
"coordinate" means the exact edge and conclusion to which that flag belongs:
owner/ports, complete P, conclusion base/path/tail/mark/E and support layer.
It is not another access-path component or a new analysis mechanism.

```text
same edge offered without H, then with H -> one visible edge with H (OR)
parent ANY without H, child ANY with H  -> neither subsumes the other
parent ANY with H, child ANY without H  -> neither subsumes the other
parent ANY with H, child ANY with H     -> ordinary same-flag coverage applies
pass an unprotected edge               -> still unprotected
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

The ordinary FLOW comes from `p.right`. T can instead come from the rule on
`p.left`. At a coarse limit their images can overlap. A rule triggered by a
T-marked conclusion and assigning T marks that concrete result protected.
Removing it merely because the coarse FLOW image covers it can lose the
left-to-result dependency needed by the next backward run. The existing
assignment, cleaner-survivor and mark-cycle producers keep their rules.
A pass carries an existing flag and never creates one.

Apply subsumption separately to the H=false and H=true coverage views.
An H=true edge never subsumes an H=false edge, or the reverse. Protected
edges can cover protected edges when all ordinary coverage tests pass.
This replaces the older rule which retained every literal protected child.

Keep one OR-upgraded visible row for exact duplicates. Its flag is not the
coverage authority. Retain canonical plain coverage U and canonical protected
coverage H separately; render their exact duplicates with OR. Updating H must
not delete U. A plain parent in U can still cover a later plain child after
its visible row becomes protected. A protected-only parent cannot do so.
These are current coverage views, not discarded-edge history or extra emitted
facts. Caches, restore and freshness must use the views, not reconstruct U
from the OR-rendered flag. If a protected child is covered by a protected
parent, a separately retained plain child can render plain: the protected
region remains represented by the parent, rather than by a sticky child flag.

```text
offer(edge):
    view = H if edge.protected else U
    canonicalInsert(view, edge.geometry)  // same-flag subsumption only
    if view changed: invalidate coverage-dependent caches
    publish changes to render(U,H)         // one exact row; flag = OR

render(U,H):
    return one row per exact geometry in union(U,H),
           protected = exact geometry is in H
```

`geometry` here includes all ordinary coverage headers, not only its field
path. In the following fixed-premise MAY example, A is the root and B its
child. Both offer orders must leave U={A}, H={A}, visible={A protected}:

```text
A plain; B plain; A protected
A protected; A plain; B plain
```

The plain A certificate removes plain B in both cases. If only protected A
was ever offered, it cannot remove plain B. A hidden new U certificate can
change coverage even when the visible rows do not change. Restoring only the
visible rows would therefore be incorrect. Save the current coverage views
with their owner; do not save an offer log. Native delivery still publishes
the OR-upgraded row, and a pass never creates protection.

Within each protection class, ordinary compatible facts keep the existing
laws: MAY covers its descendants;
MUST covers admitted descendant regions; same-head MUST exclusion sets merge
by intersection. A complete immediate child can fill one excluded field;
a deeper child or a child with a remaining hole cannot. These laws do not cross protection classes. Exact visible duplicates merge
by OR without deleting their plain coverage. A new H-only upgrade must be
delivered; a repeated identical flag need not be delivered again.

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

## 4. Initial emission: primary and FLOW companion

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

**New companion:** whenever the primary is `x.STAR/T,DEMAND`, also emit
`x.STAR/FLOW,NORMAL` with the same base, path and field E. Both are identity
edges. Replace only its mark by FLOW with empty mx. Do not emit this companion
for a rejected primary, a concrete EXACT/MUST primary, ZERO or a FLOW primary.
Deduplicate equal commands using existing entry admission.

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

FLOW is not evidence for CM(T). A conditional pass cannot become a NORMAL
transfer through this companion. A cleaner which excludes T yields FLOW mx
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
companion is the additional image branch.

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

## 6. Delivery and the open completion candidate

Replay saved NORMAL records on the original actual first. Then obtain C2
commands, analyze new commands through ordinary transfer and intersect each
candidate by §5. Store and publish only admitted results. The actual's layer
joins each applied summary's layer. A NORMAL FLOW hypothesis is not a NORMAL
T input. Existing current subscriptions, source permissions and static writer
registration keep their owners.

The earlier draft proposed this extra view over final admitted handoff rows:

```text
complete(row):
    keep row
    for each DATA endpoint q and each legal counted prefix p of q:
        add complete pair (p.ANY/FLOW, p.ANY/FLOW) at row's exact interface
    if both endpoints are DATA with legal structural heads:
        add complete pair (entry.ANY/FLOW, exit.ANY/FLOW) at that interface
```

These would be selector pairs, with Empty E/mx, not facts or inferred summaries.
Use legal register heads or complete named-static anchors. Add no broad
static root/class query. Keep the same complete pair in C2 and C5. Deduplicate
across marks and do not recursively complete generated rows. The offered
row count is linear in the source endpoint depths; use shared paths.
The run-2 shared static carry candidate exposes this view only for encountered
named fields. Later transitions retain local demand ownership.

**Its whole-program necessity and sufficiency remain open.** E28's ordinary
`id` already infers NORMAL `p.* / FLOW -> ret.* / FLOW` in run-1. Saved-first
application handles its later marked descendant. The earlier artificial
"no saved provider" premise is not a trace of that program.

E21's FLOW families can also infer its NORMAL shrinking record without this
completion. A DATA endpoint paired with ZERO still cannot publish a DATA
result, even when a companion initial exists. To prove completion necessary,
check all other final paired DATA rows, not only that control row. The
[per-run block ledger](subsumption-e21-block-ledger-20261107.md) records the
known families and the exact remaining proof boundary.

There is a separate delivery question: the present growing-output gate runs
before repeat delivery. Saved-first application inside the next input handler
does not move saved shrinking replay before that gate. The choice between
repairing demand guidance and moving saved non-growing replay before this
gate is pending. This spec does not silently change loop order or add another
observer. Do not implement completion as a proved repair on these examples.

If selected, generated selectors do not count as outgoing summaries. Newly inferred
DEMAND summaries do count. Keep the existing empty-outgoing-demand stop rule.
Do not use stable demand counts or a fixed desired iteration number.

## 7. Principal cases and proof boundary

E01–E28 remain required, including wrong-mark/field, protected, ND, static,
loop and natural-stop controls. **E29 adds the real Conductor regression:**
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

The catalog states the exact two missing identities, paired demand row and
rollback evidence. It distinguishes that confirmed mechanism from the
uncompleted fact-by-fact causal chain to each sink. Conductor recovery is an
explicit acceptance gate; this review does not claim it is proved fixed.

The original 684-law package checks the preceding revision's scoped models.
Its primary-only C2 laws are not laws about the new two-result emitter; its
literal-H laws do not prove the revised same-flag compaction. The review
supplements check the expanded image, strict-ancestor STAR rejection, scalar
intersection examples, common-suffix exclusions, overlap projection and the
plain/protected coverage repair in their stated domains. Native adapter equality,
all principal program routes, GROUP and whole-driver convergence remain
explicit validation obligations. No new project run or speedup is claimed.

Implement only after those obligations are satisfied. Start from the pinned
baseline, preserve the existing dirty prototype as evidence, and carry no
SOA/new-tail branch into the implementation. If another semantic change is
needed, state its counterexample and obtain the intended behavior first.
