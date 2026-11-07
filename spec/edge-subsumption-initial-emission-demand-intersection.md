# Edge subsumption, initial emission and demand intersection

7 November 2026. Status: **specification and scoped proof package**.
This file defines the combined design. The linked catalog supplies its
principal programs. The Lean package checks the declared component domains
and the stated program routes. It does not prove the Kotlin implementation,
all Java programs, or the optional GROUP mode. No new analyzer or project
run is reported. The current SOA worktree is evidence. It is not the selected
implementation. Keep the existing `ap.md` implementation contract until the
new design has passed its native implementation checks.

Read the [principal examples E01–E28](subsumption-principal-examples-20261107.md)
with the [proof obligations P01–P23](subsumption-initial-demand-proof-obligations.md).
This draft states the common operators and the required results; the catalog
contains the longer programs and captured traces. Follow [proof-guide.md](proof-guide.md).

## 1. Baseline and semantic ledger

The starting contract is the [frozen original proposal](baselines/subsumption-20261105/original-implementation-proposal.md),
not the accumulated current implementation. Its exact pre-implementation state
is `52829d5890ec3b3145cc996a1d8162d85cb8ceda`; its analyzer is
`52f32dd437d438aec4a700a02c18d94c31d58093`. Their entire `core` trees are equal.
The [baseline summary](subsumption-redesign-baseline-20261107.md) and
[byte-exact archive manifest](baselines/subsumption-20261105/manifest.json)
pin all five original documents. First implementation `8331bf9e` is outside
that baseline. No source rollback or implementation change is made here.

| Area | Original proposal at 528 | Selected combined contract |
| --- | --- | --- |
| Ordinary facts | Canonical MAY/MUST basis; C2 sees canonical actuals, not discarded leaves | Retain that architecture; prove required admission effects, not equal old initial lists |
| NORMAL relations | Admitted aligned FLOW STAR relation covers its correlated specialization under equal canonical mx | Retain that guard and the selected transitive/no-intermediate requirement; proper cross-mx widening is unselected |
| Protection H | Protected coverage could remove a protected descendant | Later user decision overrides this: retain literal typed H coordinates; exact duplicates merge, flag wins |
| Pass effects | Existing producer behavior | Later user decision: a pass transports H and cannot create H |
| Initial tails | Later ANY initials were legal | No ANY initial or premise; four ordinary tails only; old ANY outputs become STAR |
| FLOW seed layer in those replaced cells | FLOW/ANY started on DEMAND | FLOW/STAR starts on NORMAL as a conditional identity; the submitted actual keeps its own layer, and application still joins support |
| Same-head ANY demand | Actual ANY produced ANY; ordinary STAR was rejected | Either actual ANY or STAR produces the same plain STAR, Empty E |
| STAR start | Correlated extension starts STAR with STAR | Required identity start: FLOW/NORMAL, concrete/DEMAND; no independent MAY start |
| Other admission cells | Existing exact, MUST, first-field and run-2 requested STAR rules | Retain the complete table in section 5, including later STAR descendant rejection |
| C5 entry | Separate handwritten image checks | One constructive normalized image of this exact C2 operation |
| Handoff | Role-selected paired projection, including MUST to ANY | Retain STAR precision; no blanket STAR-to-ANY rewrite or invented identity provider |
| FLOW demand selection | A concrete selector admits only its concrete mark; a later precise STAR selector can leave no FLOW analysis | Keep that selector rule. Propose explicit FLOW demand rows from final retained DATA guidance, including provisional FLOW rows, as described in §8.1. Ordinary analysis must infer every provider. |

The later FLOW/concrete DEMAND-head retention implementations supply important
counterexamples and evidence. They are not silently imported as a separate
raw-guide history architecture. This draft must establish their required
effects through its canonical basis and real admitted relations. If that
cannot be done, the combined design remains incomplete; a discarded leaf
cannot be used as a hidden proof witness.

The selected FULL emission strategy replaces old ANY initials for both FLOW
and concrete marks. This name is separate from the existing run-1
`markMode=FULL/GROUP` option. That option is not removed or changed here.

## 2. Domain and ownership

Write a pattern as `(base, path, tail, mark, E)`. E excludes first fields of a
tail region; FLOW mark exclusion `mx` is a different coordinate. H annotates
an actual mark/position membership. A conclusion also has NORMAL or DEMAND
support. `P` means the complete original premise, including all ND members.

| Tail | Meaning | Permitted use in the redesign |
| --- | --- | --- |
| EXACT, `$` | Exact position | Actual, initial, premise, conclusion, selector |
| STAR, `*` | One correlated suffix shared by both endpoints | Actual, identity initial, premise, conclusion, selector |
| ANY, MAY | Independent unknown suffix | Actual, conclusion or demand selector; **never an initial or premise** |
| MUST, `ANY_TAINT` | Uniform definite taint over the admitted region | Existing forward actual/initial/premise/conclusion; not a demand entry |

No SOA, new tail, origin bit, raw-input archive, grounding state or new manager
is part of this contract. Existing data-class equality and interner identity
must not gain hidden metadata. ANY remains a real data approximation and a
selector; banning an ANY premise does not ban ANY conclusions.
Here an emitted premise means the owned original P and its InitialAp
members. An opposite-direction saved lookup can read an old ANY conclusion
as its matching pattern. A rule condition can also use ANY. Neither is an
emitted original or permission to construct an ANY initial.

All comparisons retain method/context, analysis direction, scope, physical
entry and output ports, full P, base, tail, layer and typed E/mx headers.
ND is a conjunction during application. A Target is a typed endpoint, not a
data pattern with a conveniently chosen path. ZERO has its unique empty EXACT
shape and Empty E. Static class anchors do not count as fields; the named
static field anchor is indivisible. Concrete class markers remain EXACT.

Keep native field/cleaner transfer, mark and group compatibility, aliases,
source identities, stopping rule and loop limits. A group selector binds an
accepted actual full mark by the existing catalog relation; it does not
enumerate marks. A concrete T selector cannot obtain T from FLOW or U.
The ordinary FULL schedule stays `[1,1,2,3,4,...]`: run-1 is forward,
run-2 is backward, and directions then alternate. In particular, run-4 has
global limit 3 and run-5 has global limit 4. A smaller pair-relative C5 cap
is not a different global run limit. GROUP compatibility keeps its existing
known limitations; scalar FULL proofs do not certify that optional mode.
Keep `trackFactsReachAnalysisEnd` empty in every run, as at the baseline.

## 3. Canonical facts, literal protection and freshness

Ordinary compatible data obey the original spatial laws, per mark and native
header cell. They do not turn correlated STAR into uniform MUST:

```text
MAY:  x.u.ANY covers x.u.r.ANY.
MUST: same head covers when covering E is a subset of covered E.
      union(MUST/E1, MUST/E2) = MUST/(E1 intersect E2).
      x.u.MUST/E covers x.u.f.r.MUST/E2 when f is not in E.
Fill: x.u.MUST/(E union {f}) + x.u.f.MUST/{} -> x.u.MUST/E.
```

Fill requires the whole immediate f child, with compatible marks/mx. A deeper
child, a child with a remaining hole, or T coverage for a U hole does not fill
it. Use catalog-aware native mx operations, not mark enumeration. Keep existing
cross-tail/layer rules; these formulas add no new one. Same-coordinate native
mx joins must retain their cofinite compatibility checks.

The selected later H law is literal, across all tails and layers:

```text
Hafter = typedUnion(Hbefore, Hoffered)
Hafter is a subset of the represented payload.
No ancestor, E coverage, ordinary join or protected ancestor removes an H atom.
Exact typed duplicates merge; an already supplied flag wins.
```

An EXACT H coordinate has no effective tail-wrapper/E distinction. A span H
coordinate retains its supplied tail and E. Do not move H to a broader joined
E header, infer H at a covered child, or create H at a filled parent. Ordinary
payload can still canonicalize under protected coverage; retain any plain
carrier needed to represent the ordinary DATA result.

An implementation may reuse the existing incremental DATA admission operator:

```text
U(S,t):
    temp = restoreCurrent(eraseProtection(S))
    (dataAfter, legacyDeltas) = oldDataAdmit(temp, eraseProtection(t))
    after = embed(dataAfter, typedUnion(H(S), H(t)))
    deltas = attachCurrentFlagsAtExactTypedCoordinates(legacyDeltas, after)
             plus literalNewProtection(after, S)
```

This is an incremental reference, not a theorem that arbitrary DATA histories
have one global confluent fold. `oldDataAdmit` includes the old whole group
law: equal-content STAR/T4 E intersection, whole mixed-packet carrier deltas
and existing FLOW replacement. It is not simply `canonicalTaintState` renamed.
Do not derive all deltas by subtracting final denotations: that can lose legacy
whole-packet replay. Coalescing equal typed packet headers does not authorize
prefix pruning of H.

Required basis results for the selected MAY/MUST and relation cells, and
literal H results, must hold cold, in one packet, parent
then child, child then parent, and on repetition. A new exact H bit is fresh;
a repeated exact H bit is not. Newly supported ordinary headers must be
delivered. Detached batches are filtered against the owner's final admitted
authority. Already queued work may finish once; no retraction or discarded
provider history is added. A pass, whether identified by rule role or PASS
kind, transports supplied H only. Existing authorized assignment/cleaner/cycle
protection rules are separate producers.

## 4. Relation subsumption and native application

The aligned NORMAL law is:

```text
admitted S: p.u.STAR/FLOW -> q.v.STAR/FLOW, NORMAL
candidate L: p.u.r.STAR/FLOW -> q.v.r.STAR/FLOW, NORMAL
S covers L by choosing S's suffix r ++ tau for each L suffix tau.
```

Require singleton nonzero nonstatic endpoints, Empty E, the same complete
interface and **equal canonical mx** on the compared aligned FLOW headers,
as in the original proposal. The later implementation's proper cross-mx
FLOW-to-FLOW widening is an unselected extension, not part of this draft.
Adding/removing r on only one endpoint, nonempty E, a missing/rejected S, or
a provider from another owner does not satisfy this law. Do not manufacture
S from L or from a factored empty suffix.

Existing FLOW-backed compaction can remove an unprotected diagonal T-to-T
specialization when marks, shape, output geometry and support permit it:
ANY uses covering prefixes; STAR uses its same-output-coordinate correlation
and E law. FLOW/N can cover T/N or T/D; FLOW/D cannot replace T/N. A provider
excluding T cannot cover T. Protected memberships remain literal.
This native FLOW-to-T mark test does not require an identical concrete mx
header and does not authorize proper cross-mx FLOW-to-FLOW removal.
Equal STAR endpoints and H=false do not establish NORMAL support. A
conditional pass can produce a provisional, unprotected identity; promoting
it by shape can give a false report when its concrete guard is false (E27).

If A covers B and B could cover C, A must cover C even when B was never stored.
Use A's transient correlated specialization as the witness; do not publish,
persist or hand off a fabricated B. Check one packet and both arrival orders.
Publication, direct/reverse indexes and later handoff use the final admitted
basis. An index cannot keep a removed row alive as a provider.

Native matching retains its selected roles. Strict-ancestor STAR inside use
is allowed only for an opposite-direction saved record, for FLOW and concrete
STAR/D alike. CURRENT and SAVED_DIRECT remain restricted. Keep applicable
same-head/descendant use and the existing trusted reverse-MUST overlap lane;
same-head incomparable E overlaps use E union with its real typed capability.
An old MUST premise alone does not create that capability.

Summary application selects from the original actual, retaining its tail,
E and support under native projection rules. It does not replace the caller
actual with the symbolic start fact. For STAR/EmptyE premise and STAR/E actual,
native applicable matching checks premise E subset actual E; the correlated
application transports the actual E. Opposite permission is not a C2 permission.

Keep the existing FLOW-first work policy: process pending FLOW deltas before
pending concrete deltas at the same owner. This is not a new whole-program
barrier. A FLOW provider can still arrive after concrete work has run.
In either order the final admitted basis must remove an eligible plain
specialization and retain a protected coordinate. Before detached summary
delivery, read the current admitted authority; do not publish a removed row
from a stale queue entry. Already performed work needs no retraction.

Summary subsumption does not authorize loss of local concrete rule work.
FLOW is an unknown mark, not proof that T is present. If point storage uses
a FLOW-backed representation for an actual T membership, it must retain the
existing membership and local delivery needed by `CM(T)`, source hits and
cleaners. Do not replace an offered T by unknown FLOW before those operations.
This reuses the baseline backed-store contract; it is not a raw candidate
archive or permission to propagate the removed T summary again.

## 5. Complete C2 operator and identity start

This C2 table is for restricted runs, starting at run-2. Run-1 keeps its
base-only abstraction protocol: nonstatic abstract inputs use the base with
an empty concrete field chain and STAR/FLOW; static field read origins use
the fixed class-plus-field anchor and STAR/FLOW under the existing writer
activation gate. Mark requests use the corresponding canonical STAR slot
with their concrete mark. Existing exact global class markers keep their
special handling. There is no S-root input seed or ANY initial in run-1.
Source GEN output is a point fact, not an initial; a real source/field cut
can still give that output an ANY conclusion.

Let `Dc=(base,p,dt,required,E_d)` and submitted `A=(base,q,at,actual,E_a)`.
First require equal bases, directed mark compatibility, valid typed shapes
and both counted depths within the current limit L. Use C2's directed
`markSub(required, actual)`, not C5's symmetric mark-overlap test:

```text
required FLOW excluding X, actual FLOW excluding Y: require X subset Y
required FLOW excluding X, actual full T:          require T not in X
required full T, actual full U:                    require T = U
required full T, actual FLOW:                      reject
required group g, actual full T:                   require existing belongs(T,g)
required concrete/group, actual unknown FLOW:      reject
```

Keep the existing catalog operations for native mx/group forms. A successful
concrete binding keeps that actual full mark. Normalize abstract demand E by
the existing rule. ANY and concrete EXACT have Empty E; emitted EXACT has Empty E.
Keep the native FLOW EXACT actual/output E exception in section 7. STAR/MUST
retain legal E. Demand MUST is invalid; backward MUST actuals/initials are invalid. Keep ZERO, static
grammar and existing mark-output checks. Every descent must pass the
ancestor's tail/E reachability test. Incomparable paths reject.

Emit at most one initial, using the bound required mark. No concrete initial
creates a companion FLOW query. All results below pass the existing initial
legality checks, with ANY and new tails forbidden.
Keep the baseline mark-header rule too: a FLOW initial has empty mx. If
rendering an original FLOW selector would require a nonempty initial mx,
that row emits no initial. Do not erase that selector or the actual's mx
implicitly. The separately derived §8.1 FLOW query has empty mx by its
explicit definition. GROUP guidance still uses its existing full-mark binding.

### Same head: p=q

| Demand tail | Actual tail | Result tail and E |
| --- | --- | --- |
| ANY | EXACT | EXACT, Empty E |
| ANY | STAR or ANY | **STAR, Empty E** |
| ANY | MUST | MUST, actual E; forward only |
| STAR | Any legal actual | EXACT, Empty E |
| EXACT, concrete | Any legal actual | EXACT, Empty E |
| EXACT, FLOW | ANY | Reject |
| EXACT, FLOW | Other legal actual | EXACT, Empty E |

The FLOW/EXACT row does not make an otherwise illegal abstract EXACT demand
entry legal in a native store. Concrete EXACT from ANY remains provisional.

### Actual is deeper: q=p+suffix, suffix nonempty

| Demand tail | Result |
| --- | --- |
| ANY | Stop after the first new counted field at r; STAR/EmptyE. For a bound concrete mark, actual EXACT and r=q, use EXACT/EmptyE instead. |
| STAR, run 2 | Requested STAR at p with normalized demand E |
| STAR, later runs | Reject |
| EXACT | Reject |

The first-field rule keeps a static anchor intact. It does not preserve a
deeper MUST merely because that actual is uniform. Requested run-2 STAR
requires a real admitted descendant within L.

### Demand is deeper: p=q+suffix, suffix nonempty

| Demand tail | Actual tail | Result at p |
| --- | --- | --- |
| ANY | ANY | STAR, Empty E |
| ANY | MUST | MUST, normalized demand E; forward only |
| ANY | Ordinary STAR | Reject |
| STAR or EXACT | STAR or MUST | EXACT, Empty E |
| STAR | ANY | EXACT, Empty E |
| EXACT, concrete | ANY | EXACT, Empty E; DEMAND support |
| EXACT, FLOW | ANY | Reject |
| Any | EXACT | Reject: exact ancestor cannot reach p |

These tables replace both former ANY outputs by STAR and add the selected
same-head ordinary-STAR admission. They do not add a virtual-MAY view for a
STAR ancestor or admit a deeper exact actual under a later STAR demand.

For emitted J, `start(J)=J`: in particular a STAR initial has a STAR identity
start. The rejected alternative `STAR key -> independent ANY start` is not
available. With DEMAND winning over NORMAL:

```text
intrinsic(ZERO or FLOW) = NORMAL
intrinsic(concrete STAR) = DEMAND
intrinsic(concrete EXACT or forward MUST) = NORMAL
seedLayer(FLOW or ZERO) = intrinsic(J)
seedLayer(concrete) = intrinsic(J) OR suppliedDEMAND
                     OR (J is EXACT and actual is ANY)
```

Thus the two selected same-head inputs give the same starting edge:
`a.STAR/FLOW -> a.STAR/FLOW,N` or `a.STAR/T -> a.STAR/T,D`.
The caller's actual E, source support and mark remain unchanged. Empty E on
the conditional query is distinct from actual E during application.

Reuse the existing source compiler and mark gates. A surviving positive
`CM(p,T)` source guard needs concrete T evidence; a restricted FLOW packet
cannot generate U from that guard, even with a NORMAL FLOW seed. The
baseline compiler approximates surviving negative source/sink mark literals
to TRUE after Boolean simplification. A resulting TRUE source uses ZERO;
FLOW cannot satisfy that ZERO premise. Do not add a runtime negative-CM
evaluator, grounding label, new GEN origin or source permission here. The
[source audit](lean/proposals/subsumption-initial-demand-20261107/SourceTransferAudit.md)
pins these unchanged seams and their proof limits.

## 6. C5 entry: constructive normalized C2 image

C2 and C5 share one image contract. A requested member is legal exactly when
it has a legal C2 witness, not when it emits itself:

```text
RawWitness(Dc,I) = (bounded legal actual A, supplied layer s)
                  with emit(Dc,A,s) = (I, seedLayer)
StoredWitness(Dc,Pmember) = RawWitness(Dc,I)
    with normalizeInitial(I)=Pmember and existing insideDemand(I,Dc)
canEmitInitial(Dc,I) = a RawWitness exists
canStoreInitial(Dc,Pmember) = a StoredWitness exists
```

Normalization is the existing complete FLOW EXACT-to-STAR P/C operation.
It preserves each endpoint's path, required E and suffix behavior. Concrete
EXACT is not normalized to STAR. ND retains its complete concrete premise.
No raw/stored premise has ANY. No witness is retained engine history.

The referenced `insideDemand(I,Dc)` is directed containment, not symmetric
overlap. After demand-side normalization it requires equal base, the existing
required-to-rendered mark relation and `I.path` extending `Dc.path`. A proper
extension must pass `admits(Dc.tail,Dc.E,suffix)`. At equal heads its tail test
is: ANY contains every tail; EXACT contains only EXACT; STAR contains EXACT,
contains ANY only with Empty E, and contains STAR/MUST when its E is a subset
of I.E. This test is on the raw witness I, before FLOW normalization; an
otherwise invalid demand/initial cannot become legal through containment.

The image classifier must implement a proved finite structural witness scheme
relative to the supplied paths, marks and headers:

| Candidate | Witness obligation |
| --- | --- |
| Same-head EXACT | Legal same-head EXACT actual with a compatible mark |
| Same-head STAR under ANY | Same-head ANY/D or STAR/EmptyE actual |
| MUST under ANY | Forward MUST actual with the required head/E |
| First-field STAR/EXACT | Legal actual at the first new counted field, with the tail/mark required by section 5 |
| Run-2 requested STAR | A legal one-new-field descendant admitted by demand E, within L |
| Stored STAR/FLOW | Either a raw STAR witness or an existing legal raw EXACT/FLOW preimage |

This is not a fixed universe of example fields. Requested STAR at the field
cap has no descendant witness. If a witness needs a fresh field outside finite
E, construct a typed admitted accessor or reject; do not assume its existence.
Include the ancestor-ANY branch through a valid same-head witness where
equivalent, and prove completeness for arbitrary relative input paths.

An existing legal class-only STAR/FLOW result must not be rejected by a
handwritten image ban: a run-2 class STAR/FLOW demand can have a legal named
static-field descendant witness. Concrete class-only STAR remains illegal by
its own grammar. The shared image, not a new class restriction, resolves this
classifier corner. ZERO is checked as its separate typed singleton.

Native EXACT/FLOW actuals can have nonempty E after a strong write. Keep
them legal. For C2's calculation only, an EXACT/FLOW actual can use an
Empty-E query view: an exact ancestor cannot descend, and the same-head and
deeper-actual cells never read that actual's E. All other actuals keep E.
The original actual is kept for binding, replay and propagation. This is the
existing C2 behavior, not a new field-write rule or global E erasure. The
30-law EXACT/FLOW input bridge extends the scalar model's smaller Empty-E
EXACT domain and proves the same constructive C5 image for this native cell.

## 7. Paired output intersection, normalization and controls

This section carries forward
[demand-relative summary restriction §§5.1–5.4 and 8](demand-relative-summary-restriction.md)
at 528. The new entry witness in section 6 replaces the old C2 image predicate;
the exit operation below does not change. Apply it to every newly inferred AP
candidate, NORMAL or DEMAND. Run-1 has no prior demand snapshot and retains
its existing first-run/global-limit admission policy; there is no run-1
Dp-relative budget. NormalTarget keeps the separate lane below.

### 7.1 Typed entry and exit permissions

Let `members(P)` be the singleton original or all members of a complete ND
original. `PZero` is the canonical ZERO original, not an arbitrary empty
premise. `DataMember(m)` means a nonzero initial member. For one complete row:

```text
EntryOK(DATA(Dc), P) = exists m in members(P):
                          DataMember(m) and StoredWitness(Dc,m)
EntryOK(ZERO, P) = P is PZero
EntryOK(Target, P) = P is PZero

ExitOK(ZERO, C) = C is Reach or DemandTarget
ExitOK(DATA(Dp), C) = C is DATA and ExitData(Dp,C) is nonempty
```

DemandTarget is the typed DEMAND terminal/Reach slot for this operation, not
an AP DATA leaf. ZERO exit rejects DATA. DATA exit rejects Reach/Target and
supplies the budget for DATA. Target is an entry kind; no new Target exit
selector is introduced. A `(ZERO or Target, DATA)` row can accept PZero and a
real DATA candidate, which is still intersected and capped. ZERO is not an
unlimited-output exemption. C2 control entries likewise start only ZERO.

Entry admission is existential over ND members, but the **complete P is kept**
on every admitted output. This ticket is not permission to execute with one
arm: complete ND matching remains AND. One row need not admit every member.
Never combine row 1's entry permission with row 2's exit or budget.

### 7.2 DATA exit operation

First normalize selector Dp only: abstract FLOW STAR ignores its field E by
the existing demand-side rule. Actual/record E is not erased. Require equal
DATA bases and intersecting mark slots. In FULL mode two full concrete marks
must be equal. For concrete versus FLOW, the concrete mark must not be in the
FLOW exclusion mx. Two FLOW slots pass the existing mark-meet test. GROUP mode
keeps the existing catalog-aware meet. Keep **C's mark slot**: a concrete Dp
does not turn a FLOW candidate into concrete taint.

Let `p=Dp.path`, `q=C.path`, `Ec=C.E`, `Ed=normalized Dp.E`.
`admits(t,E,s)` accepts an empty s; EXACT rejects a nonempty s; ANY accepts
it; STAR/MUST reject it exactly when s's first accessor is excluded. Demand
MUST is not a legal selector. Candidate C can have any of the four tails.

At the same head p=q, use this complete table; all cells retain C's layer:

| C tail | Dp EXACT | Dp STAR | Dp ANY |
| --- | --- | --- | --- |
| EXACT | Keep C whole | Keep C whole | Keep C whole |
| STAR | Keep C whole | Keep C whole | Keep C whole |
| ANY | EXACT/EmptyE | Keep ANY/EmptyE | Keep ANY/EmptyE |
| MUST | EXACT; keep Ec for FLOW, EmptyE for concrete | MUST/(Ec union Ed) | Keep MUST/Ec |

The FLOW MUST-to-EXACT Ec cell is the existing native exception, not a new
general concrete EXACT/E header. Correlated STAR stays whole even under an
EXACT selector; replacing it by an independently exact result would change
the original suffix relation.

For proper prefixes and incomparable paths:

```text
q = p ++ nonempty s:                  // candidate below selector
    if admits(Dp.tail, Ed, s): keep C whole
    else reject

p = q ++ nonempty s:                  // candidate above selector
    if C.tail == EXACT: reject
    require admits(C.tail, Ec, s)
    if C.tail == STAR: keep C whole, including path q and Ec
    if C.tail == ANY or MUST:
        move head to p
        if Dp.tail == EXACT: tail = EXACT; E = EmptyE
        else if C.tail == MUST and Dp.tail == STAR:
            tail = MUST; E = Ed
        else: retain C.tail; E = EmptyE

incomparable p,q: reject
```

These cases define `ExitData`. Selection transports the selected leaf's
supplied H through the stated projection; no unprotected leaf gains H.
Keep C's actual mark/mx and support. The seed layer is not the output layer.
There is no T/D-to-T/N upgrade and no layer test equating C to its seed.

### 7.3 Field cut and complete-row union

For each selected DATA leaf from that same row, let `k=min(L,FL(Dp)+1)`.
FL counts named fields/array elements, not class anchors, tails or marks.
The existing positive limits make k positive:

```text
if FL(selected) <= k: keep it unchanged
else:
    keep its prefix through k counted fields, preserving the static anchor
    replace lost suffix/tail by ANY; set support = DEMAND; set E = EmptyE
    retain base, mark/mx and transported H
```

Do not cut a NORMAL STAR to a shorter NORMAL STAR. Packed in-budget pieces
stay unchanged; overflow pieces join at their cut prefixes on DEMAND. A
DEMAND input stays DEMAND. H remains supplied H after projection, not a new
producer flag. Typed ZERO exits have no FL or field cut.

The reference C5 result is the union over **all** matching complete rows:

```text
results = empty exact result union
for each complete row with this owner/scope/outputPort:
    if not EntryOK(row.entry,P): continue
    if row.exit == ZERO and ExitOK(ZERO,C): add C
    if row.exit == DATA(Dp) and C is DATA:
        for selected in ExitData(Dp,C): add fieldCut(selected,min(L,FL(Dp)+1))
return results paired with unchanged complete P
```

Before packing this selected union into public summaries, use the existing
FLOW-conclusion normalization again: a selected EXACT/FLOW endpoint becomes
STAR/FLOW with the same base, path, E/mx, H and layer. C5 can create this
EXACT result from an ANY or MUST candidate, even after the input pair was
normalized. The premise is already normalized; C5 does not change it. This
is the baseline `packRestrictedSelections` step, not a new NORMAL exception
or second query. Field depth is unchanged. The annotated C5 component models
the pre-pack output; the whole-normalization bridge must include this step.

Apply ordinary admitted-summary replacement after that per-row union. Keep
independent N/D memberships and exact H upgrades under the stated laws; add
no cross-layer dominance rule. For example, raw `ret.a.b.c.EXACT/T,N` can
produce both an unchanged NORMAL leaf under `Dp=ret.a.b.c.EXACT/T` and
`ret.a.b.ANY/T,D` under `Dp=ret.a.ANY/T`. Matching only the first row is not
saturation. DATA cannot stop on raw coverage, an arbitrary maximum budget or
the first result. Early termination needs proof that every remaining row's
final capped output, including support and H, is already represented. Typed
Reach's single possible result keeps its existing narrow saturation rule.
Rejected unrestricted candidates have no semantic state or provider.

### 7.4 Complete FLOW normalization and terminal/static protocols

Whole-pair FLOW EXACT normalization must preserve strong overwrite and
RemoveAll residuals. It must not turn `p.$ -> ret.$` with killed f into an
unconditional `p.* -> ret.*`. A below-only cleaner leaving just the root does
not acquire a root-plus-descendants NORMAL identity.

For a complete FLOW P/C pair, independently replace an EXACT FLOW premise
tail and an EXACT FLOW conclusion tail by STAR. Keep each endpoint's own
base/path/E, layer, mark/mx and flags; do not copy premise fields or exclusions
to the conclusion. This is the existing pair normalization, including the
FLOW field-E policy above. It does not rewrite a concrete EXACT chain, a
concrete ND member, or an exact-origin Target premise. In particular, it adds
no concrete field transfer or cleaner rule.

DemandTarget uses EntryOK plus its paired ZERO exit, has no accessor chain
and retains provisional support. NormalTarget keeps its separate protocol:
produce only a complete NORMAL witness, compose only with NORMAL forward
support, ignore it backward and skip an already persisted identical owned
relation. Persisted ZERO-to-NormalTarget needs no replay; report IDs come from
the configured-root ZERO-to-NormalTarget rows. Neither an AP cut nor entry
admission/handoff creates a report or SourceHit. Source permission still
requires the accepted real backward source action. No rejected terminal
membership is retained solely for deduplication.

Static carry uses its existing implicit paired families. Try the direct
same-slot row first. If it cannot admit stored STAR, the existing same-slot
ANY family can supply the raw preimage only when this shared image proves it.
Choose the row/fallback; invent no writer, FLOW companion, source permission
or unrelated field. A nonzero writer is not a ZERO writer.

## 8. Integrated ownership, publication and handoff

### 8.1 Proposed FLOW demand completion

The user requires changes to initial emission and demand emission to obtain
the required FLOW summaries. An independent unchanged-region summary model
is not selected. This subsection is the proposed demand-emission repair.
This is a selected change to demand emission, not a consequence of the old
demand policy. The proof package checks its construction and the principal
recovery routes. The implementation must still pass the native adapter and
program checks in section 11.

The change is explicit: retained DATA demand can now cause separate FLOW
demand permissions at the same interface. A concrete selector itself still
admits only its concrete mark. C2, STAR identity starts, strong field writes
and the later precise-STAR descendant rejection stay unchanged.

Start with the final admitted handoff rows, after subsumption. Do not use
removed concrete leaves, rejected candidates, queued stale deltas or a raw
summary archive. Let `flowAny(q)` preserve q's base and concrete field head,
use the FLOW mark with empty mark exclusion, use the ANY selector tail and
use Empty field E. This is a demand pattern, not an initial or a fact.

A permitted structural head is a normal register head, or a named static
field head with its fixed class anchor. For static prefixes, keep the
class-plus-named-field anchor whole. Do not add S-root, class-wide or broad
class-marker FLOW queries. Existing exact global class marks keep their
separate existing handling. Every counted prefix must satisfy the native
grammar and current field limit.
Bind this limit to the input snapshot: each original endpoint is bounded by
the prior limit, and the current limit is at least that limit. Prefix depth
does not exceed endpoint depth. The completion model proves the prefix
inequality; the native adapter must supply this snapshot invariant or filter
an invalid source row. A generated permission does not bypass C2's limit.

For each retained complete row with a legal structural DATA endpoint:

```text
completeFlowDemand(row):
    result = {row}                         // keep original guidance
    for q in the DATA endpoints of row:
        for p in legalCountedPrefixes(q):
            result += ownedPair(flowAny(p), flowAny(p), row.interface)
    if both endpoints are DATA and both heads are structural heads:
        result += ownedPair(flowAny(row.entry), flowAny(row.exit),
                            row.interface)
    return result
```

`row.interface` includes the owner, direction, exact entry scope and physical
entry/output ports. Each added item is one complete pair. Never take an
entry from one derived pair and an exit or field budget from another.
The paired DATA/DATA row keeps both original heads; it is not a product of
their prefixes. Deduplicate identical FLOW pairs across marks and original
selector tails. This also applies to provisional FLOW-only guidance. The
baseline permits FLOW/DEMAND to cover unprotected T/DEMAND; completing only
rows that still mention T would therefore depend on arrival and subsumption.
The number of offered derived rows is linear in the sum of endpoint depths
plus the number of original rows, before deduplication.
This is a row-count bound. Copying every prefix's full field array can still
use quadratic bytes in one path depth. Use the existing immutable path
sharing or a demand-trie prefix view; this contract needs no new fact key.

Build this view once from the immutable original rows. Do not recursively
complete rows created by the view. An index may identify a derived complete
pair by its source row, endpoint/prefix or paired-head operation. That ID is
demand-index metadata; it must not change fact equality, mark identity or
deduplication. C2 and C5 read the same indexed row view. Saved records and
outgoing-frontier enumeration still read real admitted results.

Only the derived selector's E/mx is reset. Do not erase the submitted actual's
E/mx, flags or support. Ordinary application transports the actual under the
inferred relation. For example, a later strong write can produce NORMAL FLOW
with exclusion `{f}`; the new permission does not remove that exclusion or
turn this relation into an unconditional identity.

The paired row is necessary. For `id(p) { return p; }`, separate p-to-p and
ret-to-ret permissions cannot admit the inferred p-to-ret FLOW summary in
C5. The original p/T-to-ret/T pair cannot admit its FLOW premise either.
The new complete FLOW pair permits that real transfer; it does not assert
that the transfer exists. See E28.

The prefix self-pairs also cover DATA endpoints paired with ZERO or Target.
For example, an incoming `(Target, x.f.f.STAR/T)` pair can give a separate
`(x.f.f.ANY/FLOW, x.f.f.ANY/FLOW)` permission at the same physical ports.
It does not turn Target into DATA, start the block, or create a source hit.
Only a fact that actually reaches that port can use the new DATA permission.

The run-2 query-local shared static carry view must expose the same explicit
FLOW permission for its encountered named field. This is a change to that
demand view. It is not a default NORMAL S-to-S edge and does not enumerate
every method, static field and mark. The field's concrete carry pair remains
present. Later transitions retain their existing local-demand ownership.

An added selector row is not an inferred DEMAND summary and does not itself
enter the outgoing refinement frontier. A new DEMAND summary inferred under
that selector still follows the ordinary handoff and stopping rules. Thus
excluding selector copies from the frontier is not a convergence proof.
In particular, E22 must show that these additional analyses do not sustain
the OWASP cycle. No rule assumes that a provisional FLOW row already has a
NORMAL provider.

Every NORMAL FLOW provider must still be inferred by ordinary field/rule
transfer, normalization and complete-pair C5. A write to C.f can preserve
C.g, where f differs from g. In the straight-line negative `C.g = null`,
ordinary strong overwrite kills the incoming g fact; no unchanged g identity
is inferred from that killed fact. A real no-write branch, a real copy back
from an alias, or an existing weak-write model has its own ordinary transfer.
The synthetic E20 fixture has an untouched-static frame; do not describe it
as a strong-kill test. No result is promoted from DEMAND to NORMAL by its
shape, by H=false, or by the existence of a demand permission.

### 8.2 Propagation pipeline

```text
owner's canonical bounded actual
  -> saved NORMAL replay at the existing entry stage
  -> C2(initial, identity start, admitted support)
  -> unchanged local/native rules and complete ND joins
  -> complete P/C normalization -> paired C5 -> admitted summary authority
     (C5 output packing also restores the existing FLOW stored form)
  -> detached delivery / persistent NORMAL records / typed Targets
  -> existing selectedForHandoff(P, layer, sourceDirection)
  -> reversed complete demand pair for its real scope and ports
  -> proposed explicit FLOW demand view at those same interfaces (§8.1)
```

Owner/source direction is not a matched callee's P. The handoff role includes
its existing DEMAND, backward ZERO/NORMAL and normal-ND selections. Keep its
normal mark projection and MUST-to-ANY selector with Empty E. STAR stays STAR;
EXACT stays EXACT. Stored summary/record geometry is not replaced by a widened
guide. No universal static identity, cross-scope provider or new default seed
is introduced. Run-1 static composition uses genuine ZERO writers/readers at
the existing barrier; later static application requires actual matching data.

Loop restrictions retain the labelled adjacent, repeat, enclosing and scoped
control families whenever the existing decision needs them. Compare complete
P, scopes, entry/output ports, layers, H/E/mx and ND labels. An observer's
nonempty command is not proof of a real future delivered path. Do not replay
every saved repeat before all growing-output gates or add identity observers
as a hidden repair: either can preserve every growing raw path, despite finite
global field depth. Aliases, liveness and saved-first delivery keep their
existing owner and point scope.

## 9. Principal recovery paths

The catalog preserves the old failures and their exact revisions. The traces
below are deductions under this specification. They are not new native runs.

### 9.1 E19: a disjoint static write

```java
// Rule: assign T exactly at C.g.h. f != g.
void main() { sourceT(C.g.h); clearF(); sinkT(C.g.h); }
void clearF() { C.f = null; }
```

```text
F1, limit 1: actual source output C.g.ANY/T,D.
B2, limit 1: keep the concrete carry row; add the explicit named-field
    (C.g.ANY/FLOW, C.g.ANY/FLOW) query pair.
C2 FLOW query: C.g.STAR/FLOW -> C.g.STAR/FLOW,N.
Ordinary reverse write to f: the g hypothesis survives.
C5: the same FLOW pair admits the inferred g identity, within cap 1.
Persist: C.g.STAR/FLOW -> C.g.STAR/FLOW,N.
Apply the inferred relation to actual C.g.ANY/T,D: support remains D.
The real reverse source action grants the existing source permission.
F3, limit 2: the source emits C.g.h.EXACT/T,N.
Saved opposite NORMAL g relation transports that actual to the sink.
The precise current C.g.STAR/T demand can still reject the descendant.
The exact sink has a NORMAL T witness and produces NormalTarget.
```

`StaticFlowCompletion` derives the provider through C2, the disjoint write
and paired C5. It also proves that a strong write to g kills the incoming g
hypothesis, and that exact T at g does not taint g.h. A permission is not a
NORMAL record. `StaticCarryGap` remains a valid negative model of the old
interface with no FLOW route; completion supplies the missing route without
changing its precise STAR rejection.

### 9.2 E20: two static loops and distinct physical ports

```java
void main() {
    while (again1()) { a = sourceAtG(); Box.shared = a; }
    while (again2()) { b = get(); sinkExactT(b.g); }
}
Object get() { return Box.shared; }
```

The checked synthetic CFG has a no-write header route at backward ports
10→4. The existing query-local static carry exposes its named-field FLOW
pair. C2 and ordinary header transfer infer a NORMAL FLOW frame at those
ports. Its opposite saved replay is **4→10**, toward the adjacent block.
It is not the distinct repeat relation 4→4.

The actual fixture also models its static write as untouched by its touched
base set. Its repeat FLOW frame follows that existing weak transfer. The
separate strong-write control has no such static repeat frame. This design
changes neither transfer.

The real reverse write/source path grants source permission. In F3, the
source action and write produce `shared.g.EXACT/T,N`. Saved header replay
transports it to the next block. The actual getter's inferred FLOW summary
transports it to the physical sink. The precise current T/STAR rejection
still holds. ZERO replay follows the existing CFG; it is not the repair.
`TwoLoopHeaderFlow` checks these labelled routes and the mark/layer controls.
The old native capture completed run-3 without a finding. No new native
recovery or performance result is claimed.

### 9.3 E21: deep source, no loop leave and Target guidance

```java
// Source rule: exact T at x.f.f.f.f.
void deep(Node x) {
    while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
}
```

Keep the actual schedule F1/L1, B2/L1, F3/L2, B4/L3 and F5/L4. Keep physical
repeat port 5, discovery entry -1 and logical exit 11. The previous native
capture completed run-5 without its required finding.

The ordinary source, read, mark request, source hit, scoped ZERO/Target
publication and handoff produce these F5 rows:

```text
repeat5 -> exit11:    (DATA(x.f.EXACT/T), ZERO)
repeat5 -> repeat5:   (ZERO, DATA(x.f.f.STAR/T))
discovery -> repeat5: (Target, DATA(x.f.f.STAR/T))
```

`DeepGuidanceArrival` derives these rows under the actual global schedule.
It does not take them or a source permission as initial assumptions. The
DATA endpoint of the repeat pair now supplies a separate FLOW/ANY self
permission at that same repeat interface. The producing B4 rows end in
Reach or DemandTarget. The selected FLOW-backed T-to-T DATA law cannot
remove a typed control result, and the aligned NORMAL law cannot remove a
DEMAND control result. Thus this route does not depend on retaining a
subsumed DATA leaf. Its root and prefix queries let
ordinary analysis infer the NORMAL shrinking read frame
`x.f.STAR/FLOW -> x.STAR/FLOW`.

F5's actual source plus its first read produces `ZERO -> x.f.f.f.EXACT/T,N`.
The repeat FLOW query at head x.f.f emits the fine key x.f.f.f.STAR/FLOW.
A proper cut at depth 2 cannot reproduce that key. This is a distinction in
the complete labelled observation, not only a comparison with the exact T
selector. The loop gate therefore keeps the required precision. Saved
NORMAL read frames shrink the actual chain. When the fact reaches x.f.EXACT/T,
the concrete exact selector admits a NORMAL actor; the read reaches root T
and the real sink produces NormalTarget with the actual ZERO source origin.

`GeneralLoopAdmissionBound` proves the distinction for **all** additional
query families whose relevant heads and cut actuals have depth at most 2.
`GeneralLoopAdmissionOneStep` proves that every C2 initial has depth at most
its demand depth plus 1, even when B4's submitted actual has depth 3. The
producer/head-bound supplement establishes the needed bound in the actual
read/source operation grammar: F3 boundary facts and original heads have
depth≤1; B4 originals and independently capped DATA outputs have depth≤2.
Completion preserves both bounds. A recorded three-row list alone is not
assumed exhaustive. The native adapter must cover that complete producer
grammar and its saved read records.
The finite consumer and producer proofs do not establish native loop-store
or dispatcher equivalence. These are explicit implementation checks.

### 9.4 E16: the loop and mapper finding

The first feasible loop iteration writes the actual source through g then f.
At F1 its result is `s.f.ANY/T,D`; at F3 it is `s.f.g.EXACT/T,N`. The real
B2 getter relation yields the adjacent F3 demand `s.f.ANY/FLOW`.

That demand admits a depth2 STAR/FLOW key from the fine F3 result. Every
proper scalar cut has depth at most 1. Every other relevant B2-derived query
head is also bounded by B2's global limit 1. The ALL-family C2 bound proves
that no such cut, through any added family, can reproduce the fine key.
The growth gate therefore cannot replace the required fine observation.
The ordinary getter/mapper path and reverse source permission then give the
NORMAL sink finding. The other mapper branch does not remove that witness.

`LoopMapperRecovery` composes this labelled gate witness with the real
source/read/write/wrapper pipeline for arbitrary finite ordinary getter
wrappers. It models the feasible source-to-sink loop path, not arbitrary
native alias or dispatcher behavior. The historical native failure ended
at run-5; no new native run is claimed.

### 9.5 E07, E17–E18, E22 and E28

- **E07:** root MUST covers the supplied child MUST in either order. C2 uses
  only the canonical root, starts its definite MUST identity, and preserves
  an arbitrary full-mark field finding. No discarded child history or
  invented STAR provider is needed.
- **E17:** real run-1 reads produce the backward guides. At B2 a nested
  same-head STAR input is admitted under ANY. Each ordinary wrapper binds
  the same STAR hypothesis. The F getter can still be DEMAND at limit 1;
  F3 infers its precise NORMAL relation at limit 2. The source permission and
  sink finding follow for any finite wrapper count. `WrapperRecovery`
  proves this loop-free route.
- **E18:** F1's real guarded T→U source action yields `p.STAR/T ->
  ret.f.ANY/U,D`. B2 admits `ret.f.STAR/U,D`; the real reversed source
  action reaches `p.ANY/T,D` and the accepted source occurrences. F3's real
  exact T input starts `p.EXACT/T,N`. The source then produces
  `ret.f.g.EXACT/U,N`; its same paired exit has cap 2 and keeps it. Ordinary
  wrappers preserve this route. `ConcreteConverterWrapper` checks the raw
  action/summary kernels, C2, C5, finite wrappers and wrong-mark controls.
  It creates no FLOW converter or NORMAL input provider. The existing
  accepted-source occurrence callback is an explicit native adapter check.
- **E22:** the uniform source supplies the retained MUST hypothesis. The
  canonical getBytes/newString packet maps H-depth n to max(n-1,0). Every
  B2 DATA output has depth at most its global limit 1. After reversal, each
  F3 pair therefore has entry depth n≤1≤s+1, where s is its paired exit
  depth. Prefix self-pairs have n=s; paired erasure keeps the original n,s.
  The actual C5 selection thus stays within budget and stays NORMAL. Eligible plain T/D H arms are removed by
  the inferred NORMAL FLOW provider before demand completion. The checked
  uniform family thus creates no new DATA refinement demand. This is a
  scoped no-cycle result, not a termination theorem for arbitrary programs.
- **E28:** self-pairs at p and ret do not permit publication of p→ret. The
  additional complete erased pair does. Ordinary `return p` then infers the
  NORMAL p-to-ret FLOW relation. The overwrite/clean-object control cannot
  infer that relation. The permission never asserts a result by itself.

## 10. Proof map

The [proof ledger](subsumption-initial-demand-proof-obligations.md) defines
P01–P23. The [portable package](lean/proposals/subsumption-initial-demand-20261107/README.md)
contains the checked sources, source hashes, receipts and axiom audits. The
principal catalog records all E01–E28 programs and negative controls.

| Required property | Constructive argument and checked component | Scope |
| --- | --- | --- |
| P01: MAY/MUST and fill | Prefix/region witnesses in original `Canonical`; actual compatible E laws, complete immediate-child fill | Per compatible header cell; literal H uses P02 |
| P02: H and pass | Typed union, exact flag freshness and transport in `LiteralProtection` | Unchanged ordinary DATA operation is a parameter |
| P03–P04: NORMAL and transitive coverage | Choose common suffix r++tau; compute transient B; `Relations`, `Reachability`, `SelectedTransitiveSubsumption` | Admitted aligned nonstatic Empty-E equal-mx cell; both arrival orders, no stored B |
| P05: native match roles | Explicit opposite-role filter and overlap witness in `Matching`, `Canonical` | Native eligibility and reverse capability remain typed adapter inputs |
| P06–P08: C2 and normalized C5 image | Case split on relative prefixes; executable templates at the head or first new field in `RelativeAdmission`; `ExactFlowInputBridge` for legal FLOW EXACT/E | Arbitrary scalar fields/full marks, finite field E; native static/group adapters separate |
| P09–P11: paired C5 | Keep full P, choose one complete row, project its exit, apply its own counted cap; `AnnotatedC5Exit` | Typed Accessor/mx model; final native packing is required |
| P12: FLOW normalization | Each endpoint keeps its path/E; overwrite residual stays excluded; below-only whole-position cleaning is prohibited | Existing baseline transfer/normalization contract; native regression required |
| P13–P14: canonical input and replay | `GeneralLoopAdmissionBound`, `WrapperRecovery`, `ConcreteConverterWrapper`, `LoopMapperRecovery`, `StaticFlowCompletion`, `TwoLoopHeaderFlow` | Listed actual routes, no alias/ND/global Java theorem |
| P15–P18: loop/Target/handoff | Labelled row provenance, actual source/Target chain and fine-versus-cut queries in `DeepGuidanceArrival`, `DeepFlowCompletion`, `DeepExtraFrontier` and one-step bound | Stated producer/head bounds; exact physical ports |
| P19–P20: principal programs and stop | Compose the actual routes above; uniform E22 no-D cut theorem and existing no-outgoing-demand stop rule | Principal scalar programs; whole-native equivalence remains an implementation gate |
| P21–P23: explicit FLOW permissions | `FlowDemandCompletion` provenance and row bound; real provider proofs; uniform and Deep route proofs | Completion grants permission only; no blanket convergence claim |

The source audit also checks that the NORMAL FLOW identity start does not
change the baseline source compiler, positive mark gate, negative-condition
projection or GEN origin. The original 162 laws are reused only within their
stated domains. The later SOA proof package is not proof of this design.
A theorem count includes negative and local laws; it is not a count of
whole-analyzer correctness results.

## 11. Implementation and validation boundary

Implement from pinned source 528, whose core is the reviewed 52f32 source.
Do not port the withdrawn SOA prototype as the starting implementation. No
runtime change is authorized by this spec-writing task.

The implementation must connect the checked operators to both native stores:

1. C2 and the prepared C5 entry plan must use the same normalized image.
   Cover class anchors, static grammar, real mx/group catalogs, exclusions,
   exact FLOW/E and all legal support layers. No independent image table.
2. Apply C5 to every candidate before summary storage. Pack its complete-row
   result, normalize selected FLOW EXACT outputs and retain literal H.
   Do not keep rejected raw providers in an index or a guide archive.
3. Add the demand-completion view once per immutable snapshot, after final
   admitted subsumption. C2 and C5 must see the same complete rows and ports.
   Keep generated selectors out of inferred frontier enumeration.
4. Validate cold/warm/one-packet and both arrival orders in scalar and packed
   stores. Include A→B→C with no stored B, a late H-only upgrade, unequal mx,
   excluded T, current/direct/opposite STAR roles and reverse-MUST overlap.
5. Run all E01–E28 native regressions and their negative controls. Keep their
   strict finding checks and natural COMPLETE/NO_DEMAND_EDGE stopping. Do
   not hard-code a run count or use stable demand counts as a stop rule.
6. Only then repeat the configured OWASP and selected project campaign.
   Report the latest reached and completed run labels, times, demand frontier,
   quality and workload shape. These proof checks supply no speedup claim.

The pinned source has no SOA. If code is ported from the dirty prototype,
remove its enum/helper/equality/interner/start branches, AP operations,
point/packed deltas, native matching, ND/Target publication, records/demand/
static adapters, prepared C5 programs, replay and loop certificates. Each
initial-start path must enforce no ANY premise. Preserve ordinary ANY DATA
and selectors. Add no marker branch or global actual-to-STAR conversion.

Proof limits remain explicit: GROUP's known issues, native Kotlin/store
correspondence, arbitrary alias/ND programs and whole-driver convergence are
not proved by these scalar modules. Their existing semantics are preserved;
the native implementation must verify the adapter obligations above. If it
requires another semantic change, stop that dependent implementation and
obtain the intended behavior under the proof guide.
