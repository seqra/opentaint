# Plain STAR initial emission and demand intersection

Status: **superseded working candidate; not normative or ready to land**.
Date: 7 November 2026. The user requested examples first, then one combined
redesign based on the [original subsumption contract](subsumption-redesign-baseline-20261107.md).
Preserve this standalone candidate as design history; do not implement or
advertise it as the current specification. This draft defines C2 and C5 together. Global loop progress and complete
program acceptance remain unproved. The current SOA worktree still loses the
two-loop finding at complete run 3 and the DeepNoLeave finding at complete
run 5. Neither failure is waived. SOA removal is planned, not completed.

This draft follows [the proof guide](proof-guide.md). It does not update the
precedence in `ap.md` while the implementation and acceptance gates are open.

## 1. Selected change and retained behavior

Use only the existing four tails: EXACT, STAR, ANY and MUST (`ANY_TAINT`).
ANY remains legal on submitted facts, conclusions and demand selectors. It
must not occur on an emitted `InitialAp` or an analysis original/premise,
including a member of an ND premise or a public Target premise. Add no tail
kind, origin flag, rejected-fact history or new universal summary provider.

| Area | Current SOA worktree | Selected contract |
| --- | --- | --- |
| Old C2 cells which emitted ANY | Emit live SOA | Emit ordinary STAR |
| Same head: ANY demand, ordinary STAR input | Reject | Emit ordinary STAR with Empty E |
| Same head: ANY demand, ANY input | Emit SOA | Emit ordinary STAR with Empty E |
| Other four-tail C2 cells | Existing selector | Keep the table in section 3 |
| Concrete T demand | Concrete T query | Keep concrete-only admission; no companion FLOW query |
| Later STAR demand with a deeper actual | Reject | Keep rejection |
| Stored summary/record | Erase SOA to STAR | No SOA exists; keep complete FLOW EXACT normalization |
| Demand handoff | Existing role projection | Keep STAR and EXACT; keep existing MUST-to-ANY projection |

Do not reinterpret a precise STAR identity as a request for deeper fields.
There is no blanket STAR-to-ANY handoff rewrite. Do not promote a concrete
identity or a packed mark mask to a universal FLOW identity. Existing field
transfer, cleaners, literal protection, NORMAL relation coverage, matching
roles, static writer validation, source identities and Target IDs stay in
force. A later local extension needs a stated decision and proof.

## 2. Domain, guards and layers

Write demand entry `Dc=(base,p,tail,mark,E)` and submitted scalar
`A=(base,q,tail,mark,E)`. `T` is a concrete full mark; FLOW is the abstract
mark. A group demand can bind its accepted actual full mark through the
existing mark catalog. Emission keeps the required mark in all other cases.

Before table selection, keep these existing checks:

- Equal bases and compatible marks. A T demand cannot take T from FLOW or U.
- Both paths fit the current counted-field budget L. Class anchors do not
  count as fields. A requested static field keeps its class/field anchor.
- EXACT and ANY carry Empty E. STAR and forward MUST can carry legal E.
  Normalize abstract demand E as now; do not clear actual E or mark exclusions.
- Demand entries have no MUST tail. Backward actuals and initials have no MUST.
- ZERO has only the canonical empty path, EXACT tail, Empty E and ZERO mark.
- Keep concrete static named-field grammar and exact class markers. Abstract
  FLOW roots/classes remain legal where existing C2 permits them.

Every table result must pass the existing initial legality checks, with the
additional ban on ANY initials. Unrelated or incomparable paths give no result.
A proper descent must pass the ancestor tail/E reachability check.

Let `intrinsic(J)` be NORMAL for ZERO, FLOW STAR/EXACT/MUST and concrete
EXACT/MUST; it is DEMAND for concrete STAR. Admission uses the existing rule:

```text
FLOW or ZERO: seedLayer = intrinsic(J)
concrete:     seedLayer = intrinsic(J) OR supplied-is-DEMAND OR exact-loss
exact-loss:   J is EXACT and the actual tail is ANY
```

OR here means that DEMAND wins. A concrete STAR query stays DEMAND even when
the supplied actual is NORMAL. FLOW starts a symbolic query in NORMAL; this
does not confirm the actual concrete data. Starting a query and applying its
summary are separate operations. Do not replace the caller actual by the
started STAR packet. C5 does not require seedLayer to equal outputLayer.

## 3. Complete C2 table

All table entries include the guards in section 2. `result(r,t,E)` uses the
bound mark and the demand base. A rejected result has no initial or start.
The two new STAR cells use canonical Empty E for either submitted tail.

### 3.1 Same head, p=q

| Demand | Submitted tail | Emitted tail and E |
| --- | --- | --- |
| ANY | EXACT | EXACT, Empty E |
| ANY | ANY | STAR, Empty E |
| ANY | STAR | STAR, Empty E |
| ANY | MUST | MUST, actual E; forward only |
| STAR | Any legal submitted tail | EXACT, Empty E |
| EXACT, concrete required mark | Any legal submitted tail | EXACT, Empty E |
| EXACT, FLOW | ANY | Reject |
| EXACT, FLOW | Other legal submitted tail | EXACT, Empty E |

The generic FLOW/EXACT cell is not permission to store an abstract EXACT
demand entry where the existing typed demand grammar forbids it. A concrete
EXACT result from ANY input retains DEMAND support. It is not changed to ANY
or STAR merely because its support is provisional.

For actual STAR/E, the emitted STAR/EmptyE is a broader conditional query.
Native `applicablePart` tests premise E as a subset of actual E, selects the
actual leaf and retains the actual packet's tail/E/layer. A correlated STAR
summary transports that actual E. Explicit EXACT/ANY outputs keep the existing
projection rules; they need not retain an irrelevant suffix exclusion.

### 3.2 Submitted head is deeper, p is a proper prefix of q

First require the demand tail/E to admit `q-p`.

| Demand | Result |
| --- | --- |
| ANY | Let r end just after the first new counted field. Emit STAR at r, Empty E. If the bound mark is concrete, A is EXACT and r=q, emit EXACT instead. |
| STAR, run 2 | Emit requested STAR at p, with normalized demand E. |
| STAR, run 3 or later | Reject. |
| EXACT | Reject. |

A first-new-field result has at most one new counted field. It keeps the
indivisible static anchor. This rule is unchanged for submitted MUST too:
a deeper MUST actual is not automatically a same-head MUST initial.

### 3.3 Demand head is deeper, q is a proper prefix of p

First require A's tail/E to admit `p-q`.

| Demand | Submitted tail | Result at p |
| --- | --- | --- |
| ANY | ANY | STAR, Empty E |
| ANY | MUST | MUST, normalized demand E; forward only |
| ANY | Ordinary STAR | Reject, unchanged |
| STAR or EXACT | STAR or MUST | EXACT, Empty E |
| STAR | ANY | EXACT, Empty E |
| EXACT, concrete required mark | ANY | EXACT, Empty E; DEMAND support |
| EXACT, FLOW | ANY | Reject |
| Any demand | EXACT | Reject: an exact ancestor does not reach p |

Do not silently copy the former SOA virtual-MAY rule onto an ordinary STAR
ancestor. For example, `x.STAR` cannot start `x.f.STAR` under the new same-head
cell. Current direct summary matching also rejects the strict-ancestor STAR
inside case; opposite native records retain their separate existing policy.

## 4. Joint raw image and normalized stored image

C2 is the authority for its image. For one legal demand entry Dc, define:

```text
RawWitness(Dc,I) = a legal bounded actual A and supplied layer s
                  for which C2(Dc,A,s) returns initial I and its seed layer
NormalizePair(I,C) = the existing complete FLOW EXACT-to-STAR normalization
StoredWitness(Dc,P) = a RawWitness(Dc,I) with NormalizeInitial(I)=P
                      and existing insideDemand(I,Dc)
```

Every witness is executable in the stated AP domain. It is not a fact retained
from a previous query. Native image checks must not intern hypothetical APs,
walk all paths or enumerate marks. Use proved structural cases equivalent to
this witness relation. No self-emission test substitutes for an image proof:
requested run-2 STAR emits EXACT when offered to its own STAR demand.

A finite witness scheme for candidate raw I is sufficient:

| Candidate initial | Constructive actual witness |
| --- | --- |
| Same-head EXACT | Same-head legal EXACT, compatible mark, Empty E |
| Same-head STAR under ANY demand | Same-head ANY/D or STAR with Empty E |
| Same-head MUST under ANY demand | Same-head forward MUST with I's E |
| First-new-field STAR/EXACT under ANY | Actual at that first-new-field path with the tail/mark required by section 3.2 |
| Requested run-2 STAR at demand head | A legal admitted one-new-field EXACT descendant; its depth must fit L |
| Stored STAR/FLOW through existing normalization | A raw FLOW EXACT witness at the same head, when that raw image is legal |

Choose the actual mark from the candidate/bound full mark or FLOW as the
mark relation requires. Supply a legal layer; an ANY actual is DEMAND. A
fresh-field witness requires a constructive admitted typed accessor outside
finite E and a legal static anchor. Do not assume one exists in a restricted
finite model without supplying it. No such witness exists at the field cap.

The complete stored image has no ANY or SOA premise. Concrete EXACT is not
normalized to STAR. FLOW EXACT normalization applies to the complete FLOW
P/C pair; ND concrete members retain their own tails and complete conjunction.
A normalized key alone is not the raw C2 witness.

The current handwritten `requestedStarImage` excludes class-only STAR/FLOW
although the legal selector can emit it from a named-field descendant. The
single witness contract resolves this image classifier defect: an existing
legal C2 witness must be accepted by C5. Add no new class ban. Concrete
class-only marked STAR remains forbidden by its separate existing grammar.
The abstract static-root/class native case needs an explicit regression test.

## 5. C5: one complete paired demand and the existing output law

For a summary original P, candidate conclusion C and one pair `(Dc,Dp)`:

```text
for each member selected by the existing P/ND entry policy:
    ticket = StoredWitness(Dc, normalized member)
    if ticket exists:
        selected = existing restrictConclusionOnly(C,Dp)
        retain existing protection transport
        output = existing limit(selected, min(L, FL(Dp)+1))
        retain full original P, scope and actual output port
```

This pseudocode does not replace complete ND execution by OR. It keeps the
existing per-member C5 tickets and retains the full caller `PremiseSet`.
All required arms still join through the real AND application. It adds no
new requirement that one Dc admit every ND member. Each ticket and its exit
come from the same complete pair; never mix two rows' permissions.

C5 uses C's actual output layer, mark, E and literal H. A witness permits the
query; it does not turn a concrete provisional output into NORMAL. Keep the
existing native MUST lanes, pending loss/demotion and paired-exit mark gates.
A successful output match cannot create a missing entry witness.

Typed Target/Zero entries keep their current control policy. They admit only
ZERO through C2. A paired DATA exit can constrain a ZERO-origin output at C5;
it does not create a nonzero DATA initial. Concrete EXACT/D Target originals
stay EXACT at publication and handoff. No new Target-to-ANY conversion follows
from this draft.

The selected C5 shared-static-carry repair remains: keep the direct same-slot
pair first; if it rejects stored STAR, try the already present same-slot ANY
family only when this joint image admits P. It changes no C2 field/mark
permission, source identity or nonstatic query family.

## 6. Storage, publication and handoff

The pipeline is:

```text
bounded actual -> selected C2 command -> existing initial/start layer
    -> native rules/field transfer -> completed candidate P/C
    -> complete FLOW-pair normalization -> joint paired C5
    -> current admitted summary store -> detached publication/native record
    -> existing selectedForHandoff view -> reversed complete demand pair
```

Keep owner method/context, direction, scope, entry and output ports at every
step. A stored NORMAL record is an actual provider. A demand selector is not
a record or an inferred summary. Keep saved replay before C2 at an entered
body, and keep the selected growing-output gate before onward routing. This
draft does not add a consumer family or move replay across that gate.

Demand projection keeps STAR and EXACT. MUST becomes ANY with Empty E as in
the existing role projection. Keep mark normalization and static/Target
adapters. A precise STAR/T identity is not widened. No global S-to-S identity,
companion FLOW admission or new scope equivalence is introduced.

Within one exact interface, an actually admitted FLOW counterpart can cover
an unprotected diagonal T row under the existing layer/E/mark tests. It must
exist. A concrete T query alone does not prove the FLOW relation; a packed
FLOW-shaped encoding of its mark mask does not create one. Generic static
root specialization is not added to the NORMAL relation index.

## 7. Required examples and known acceptance gap

A same-head wrapper now works at the local command boundary:

```text
caller supplies ret.STAR/FLOW,N; callee demand ret.ANY/FLOW
C2 -> ret.STAR/FLOW,N
// Concrete T version starts DEMAND. Actual summary application keeps support.
```

This predicts local wrapper admission, not complete program recovery. Keep
the original four-method loop/mapper and nested positive finding assertions.

In the two-loop capture, B2 L1 has only concrete
`F.STAR/T -> F.STAR/T,D` rows at the relevant scopes/ports. No FLOW provider
is present there. Concrete-only admission is intentional. A getter FLOW row
from another method, or an `a -> a` record, cannot cover this static F row.

The later native control trace contains all 59 events with no drops/errors.
ZERO saved replay reaches L1 leave10, AL1 entry10 and ROOT_EXIT. Root C5 admits
ZERO identity. Thus absent current L2/getter actors do not show a ZERO delivery
gap. Saved replay can cover the whole adjacent composition.

The precise DATA path is different. Events44–50 apply `F.g.EXACT/T,N`, retain
it through growth restriction and freshly offer it to L1 repeat4. Its native
observer has a precise adjacent initial but no repeat initial. The actual
C2 returned list is not separately logged; the current empty-admission return
is source-derived. The tree's ANY_TAINT wrapper contains an exact leaf; it is
not a MUST fact. See the [worked trace](../docs/reports/bidirectional-star-or-any-worked-fact-traces-20261107.md).

The new same-head rule does not itself change that later STAR-demand rejection.
The current two-loop and DeepNoLeave findings remain landing blockers. Deep's
F3 concrete EXACT/D initial produces an exact-origin Target; a later STAR
Target exit is also captured. Neither is a former marker image which may be
silently changed to ANY. A new complete path or a further behavior decision
is required if the redesigned native programs still fail. Do not force them
to pass with broad guidance widening, an identity exemption or extra sources.

## 8. SOA removal and native validation plan

Removal must cover the full source inventory, not only the enum:

- Tail helpers, initial interning/start checks and C2 image classifiers.
- Point/groups/packed canonicalization and delta freshness.
- Transfer, cleaner, filter, mark, reverse-read and summary-application arms.
- Complete summary/ND/Target normalization, publication and native records.
- Demand/static/carry adapters, prepared C5 plans and loop query/certificate
  views. Keep strict matching roles and exact scope/port labels.
- Scoped contributor replay and all direct initial-start paths. No ANY original
  may enter these paths. Submitted MAY data and selectors remain legal.

Update tests and oracles against this table. Preserve literal H and pass
protection laws. Cover cold/warm insertion, one packet and both arrival
orders. Keep ordinary NORMAL/MUST data canonicalization unchanged.

Required native controls include all table cells in both directions; field
cap/E/mark/static/ZERO negatives; requested run-2 STAR witnesses; the abstract
class/root image corner; no-ANY ND/Target storage; direct/opposite matching;
MUST lanes; static carry; nested wrappers; the OWASP storage cycle; the two
loop finding assertions; and default module gates. Follow with the fixed
project campaign only after native acceptance. Report reached, completed and
accepted iteration labels; no convergence, quality or speed claim is made now.

## 9. Plain-STAR joint admission proof dossier

**Prepared; root verification and native refinement pending.** The external
[Plain-STAR joint admission model](/drive-testcomp/opentaint-go-rules/canonical-relations-directional-inside-20261105/analysis-tools/may-initial-to-star-audit-20261107/plain-star-joint-demand-redesign-20261107/formal/PlainStarJointAdmission.lean)
is preparation, not a completed proof of this full contract. Its selected
EmptyE mode and legal static grammar must agree with this draft. This document
claims no new checked law count or PASS receipt.

Prove constructive raw witnesses, complete normalized image in both
directions, raw/stored inside-demand agreement, actual support/E/H transport,
complete paired C5 with its output cap, and the declared static/ND/Target
adapters. Finite model scope must be explicit. Then validate native refinement
against unchanged positive programs. A local image theorem, equal denotations
or a full native unit pass does not prove global source/sink preservation or
loop progress. Those acceptance obligations remain open.
