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
| Restricted initial emission | One primary initial | If the primary is concrete STAR/DEMAND, also emit its same-geometry FLOW/STAR/NORMAL identity. |
| C5 entry check | Existing normalized C2-image test | Keep that mechanism and include the new companion in its image. |
| FLOW demand completion | Endpoint-prefix self-pairs and one paired-head permission | Keep both. A companion does not cover a rejected primary or a DATA endpoint paired with control. |

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
same edge offered without H, then with H -> one edge with H
parent ANY without H, child ANY with H  -> retain the child's H
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

Ordinary compatible facts keep the existing laws: MAY covers its descendants;
MUST covers admitted descendant regions; same-head MUST exclusion sets merge
by intersection. A complete immediate child can fill one excluded field;
a deeper child or a child with a remaining hole cannot. These laws never
remove H. Exact duplicate flags merge by OR. A new H-only upgrade must be
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
output prefix. EXACT, MUST, mark-changing and protected rows keep their
existing separate rules.

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
| H remains literal | In §2.1, right-side FLOW does not replace the protected left-side rule dependency. |
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
| p extends q | STAR or concrete EXACT | STAR or MUST | p.EXACT |
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

**Why accept a deeper demand from STAR?** For demand p.f.EXACT/T and actual
p.STAR/T,DEMAND, the suffix could be f. The emitted p.f.EXACT/T is therefore a
DEMAND hypothesis, not definite taint at every child. With FLOW the hypothesis
is a conditional NORMAL relation; actual support is still joined on replay.
This is the existing C2 selection policy. CURRENT summary application can
still reject a strict inside use. We have not established that rejecting this
whole C2 cell preserves refinement, so this review does not change it or
claim that a necessity counterexample has been demonstrated.

## 5. One demand-edge intersection

Let the previous-run edge be `Dp -> Dc`. In the current direction it gives
one demand pair `(Dc,Dp)`: entry permission Dc and paired output permission
Dp. Intersect it with the current summary candidate `P -> C`. Keep that pair's owner, scope, ports and field budget.

The C5 entry test already exists in `canEmitInitial`/`canStoreInitial`.
It asks whether a member of P can be a normalized output of C2 for Dc.
It does not ask whether feeding that member back into C2 emits itself.
The new part is the companion branch. Check its valid primary T/STAR witness,
then replace the mark. Do not repeat `markSub(T,FLOW)` on the companion.
Raw geometric containment and legality still apply. Keep the existing raw
EXACT/FLOW preimage of stored STAR/FLOW. No runtime witness object, actual
history or enumeration of hypothetical facts is required.

The following is the complete operation for ONE demand pair. `image(Dc)`
means that constructive normalized image of §4. `admits(t,E,s)` accepts an
empty suffix; for a nonempty suffix EXACT rejects, ANY accepts, and STAR/MUST
check its first field against E.

```text
intersect(demand=(Dc,Dp), candidate=(P,C), run, direction, L):
    if owner/context/direction/scope/entryPort/exitPort differ: return {}
    if shapes, marks, exclusions or static anchors are invalid: return {}
    if C is NormalTarget:
        keep (P,C) only for the existing NORMAL forward witness,
        with NORMAL composition and no identical persisted owned row
        return that result
    if run == 1: return existing first-run/global-limit admission(P,C)

    (P,C) = normalizeWholeFlowPair(P,C)
    // Unary FLOW DATA pair only: EXACT -> STAR at either endpoint.
    // Preserve each endpoint's own path/E/mx; preserve C's layer/H.
    if Dc is DATA:
        if P is ZERO or no member of complete P belongs to image(Dc): return {}
    else if Dc is ZERO or Target:
        if P is not canonical ZERO: return {}
    else: return {}
    // Keep complete P. ND still requires all members during application.

    if Dp is ZERO:
        return {(P,C)} if C is Reach or DemandTarget else {}
    if Dp is not legal DATA or C is not DATA: return {}
    d = Dp with E cleared only for FLOW/STAR
    results = empty exact union
    for each scalar membership c in C:
        if c.base != d.base or their mark slots have no overlap: continue
        // T/U must agree. T meets FLOW only if T is not excluded.
        // Native mx/GROUP overlap applies. Keep c's mark/mx, layer and H.
        p=d.path; q=c.path; Ed=d.E; Ec=c.E; selected=none
        if p == q:
            if c.tail is EXACT or STAR: selected=c
            if c.tail == ANY:
                selected=c with tail=(EXACT if d.tail==EXACT else ANY), E=empty
            if c.tail == MUST:
                if d.tail == EXACT:
                    selected=c with tail=EXACT, E=(Ec if c is FLOW else empty)
                if d.tail == STAR: selected=c with E=(Ec union Ed)
                if d.tail == ANY:  selected=c
        else if q == p + nonempty suffix:
            if admits(d.tail,Ed,suffix): selected=c
        else if p == q + nonempty suffix:
            if c.tail != EXACT and admits(c.tail,Ec,suffix):
                if c.tail == STAR: selected=c
                else if d.tail == EXACT:
                    selected=c with path=p, tail=EXACT, E=empty
                else:
                    selected=c with path=p,
                        E=(Ed if c.tail==MUST and d.tail==STAR else empty)
        if selected is none: continue
        k=min(L, countedDepth(d.path)+1)
        if countedDepth(selected.path) > k:
            selected=selected with path=prefixThroughKFieldsKeepingStaticAnchor,
                tail=ANY, E=empty, layer=DEMAND
        if selected is EXACT/FLOW: selected.tail=STAR
        results += selected
    return {(complete P, packExactUnion(results))} if results is nonempty else {}
```

This operation preserves candidate marks; it does not turn FLOW into T.
An entry ticket can admit an ND member without dropping the rest of P.
The selected output keeps its actual support and supplied H. Only a real
field cut changes support to DEMAND. ZERO is not an unlimited-field exception.

The caller unions results over ALL matching complete pairs, then applies
summary subsumption. One pair can retain a NORMAL leaf while another cuts it
to DEMAND. Never combine one pair's entry with another pair's exit or stop
at the first DATA match. Rejected raw candidates are not stored providers.

Whole-FLOW normalization retains strong-write exclusions and legal whole-
position RemoveAll residuals. It does not normalize concrete EXACT endpoints
or exact Target originals. The existing source compiler, SourceHit callback
and NormalTarget reporting protocol remain unchanged.

## 6. Demand completion and delivery

The companion is not the only FLOW permission. Keep the existing completion
view built once from final admitted handoff rows:

```text
complete(row):
    keep row
    for each DATA endpoint q and each legal counted prefix p of q:
        add complete pair (p.ANY/FLOW, p.ANY/FLOW) at row's exact interface
    if both endpoints are DATA with legal structural heads:
        add complete pair (entry.ANY/FLOW, exit.ANY/FLOW) at that interface
```

These are selector pairs, with Empty E/mx, not facts or inferred summaries.
Use legal register heads or complete named-static anchors. Add no broad
static root/class query. Keep the same complete pair in C2 and C5. Deduplicate
across marks and do not recursively complete generated rows. The offered
row count is linear in the source endpoint depths; use shared paths.
The run-2 shared static carry exposes this view for encountered named fields.
Later transitions retain local demand ownership.

Two examples show why the companion alone is insufficient:

- **E21:** `(ZERO, DATA(x.f.f.STAR/T))` cannot start a DATA initial. Its
  DATA endpoint still needs a FLOW/ANY self permission at the repeat port.
- **E28:** a later `(p.STAR/T, ret.STAR/T)` demand rejects `p.g.EXACT/T` before
  emitting a primary. A p-to-p self permission cannot publish p-to-ret.
  The complete paired FLOW permission is needed for that actual return.

Delivery remains: replay saved NORMAL records on the original actual first;
then obtain C2 commands; analyze new commands through ordinary transfer;
intersect candidates by §5; store and publish only admitted results. The
actual's layer joins each applied summary's layer. A NORMAL FLOW hypothesis
is not a NORMAL T input. Existing current subscriptions, loop ports, source
permissions and static writer registration keep their owners.

Generated selectors do not count as outgoing summaries. Newly inferred
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
Its primary-only C2 laws are not laws about the new two-result emitter.
The review supplements check the expanded image, common-suffix exclusions
and overlap projection in their stated domains. Native adapter equality,
all principal program routes, GROUP and whole-driver convergence remain
explicit validation obligations. No new project run or speedup is claimed.

Implement only after those obligations are satisfied. Start from the pinned
baseline, preserve the existing dirty prototype as evidence, and carry no
SOA/new-tail branch into the implementation. If another semantic change is
needed, state its counterexample and obtain the intended behavior first.
