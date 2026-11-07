# Proof obligations for the combined redesign

7 November 2026. Status: proof map for the combined specification.
The checked domains and remaining implementation obligations are stated below.
Follow [proof-guide.md](proof-guide.md). Use the
[frozen pre-implementation baseline](subsumption-redesign-baseline-20261107.md)
and [principal examples](subsumption-principal-examples-20261107.md).

The target is one specification for edge subsumption, initial emission and
paired demand intersection. A local inclusion theorem is not sufficient.
The combined rules must preserve the required source-to-sink routes in every
principal example. No runtime implementation is changed by this proof work.

## 1. Proof authority and scope

The original proposal has four constructive modules and 162 checked laws:
63 Canonical, 49 Relations, 41 Matching and 9 Reachability. These are the
original archived results at `52829d589`; they are not results for this
redesign. The later five-module, 175-law implementation package is a
different artifact. Do not merge the two counts or their scopes.

The original results cover spatial union, correlated relation inclusion,
matching restrictions and fixed concrete path witnesses. They do not prove
the changed C2 policy, normalized C5 image, complete loop observations or
iteration progress. Later literal protection and pass-role decisions also
need explicit correspondence; they are not original theorem assumptions.

The withdrawn STAR_OR_ANY proofs concern another contract. The fixed-domain
plain-STAR working model has not been accepted as the new complete model.
Neither is a replacement for the obligations below.

Use constructive witnesses. A proof of existence must give the relevant
actual fact, relation, demand row or program path. Use no `sorry`, custom
axiom, classical choice or assumed native-equivalence theorem.

## 2. Required results

| ID | Required statement | Principal cases |
| --- | --- | --- |
| P01 | Canonical MAY/MUST union preserves represented positions and marks under the selected E laws. A partial child cannot fill a whole excluded field. | E04–E06 |
| P02 | Protected coordinates cannot be subsumed. Protection is joined at the exact selected coordinate; a pass rule never creates protection. | E10–E11 |
| P03 | An admitted aligned NORMAL relation covers its specialization by an executable common-suffix witness. An absent or rejected provider cannot cover anything. | E01–E02 |
| P04 | Coverage is transitive, including NORMAL FLOW followed by FLOW-backed concrete coverage. Final coverage works in one packet and both arrival orders without retaining an intermediate row. | E03, E06 |
| P05 | Current, saved-direct and opposite matching have exactly their selected roles. All incoming STAR facts obey the strict-ancestor restriction; MAY/MUST keep their own rules. | E08–E09 |
| P06 | C2 emits no ANY initial or premise, creates no full mark from FLOW or a different full mark, and respects base, E reachability, direction and field limits. | E12–E13 |
| P07 | Both selected same-head ANY/STAR inputs under ANY demand yield the same ordinary STAR identity start. FLOW starts NORMAL; concrete STAR starts DEMAND. No MAY start or new tail is used. | E12, E17–E18, E25 |
| P08 | C5's normalized entry predicate is exactly the constructive image of the same C2 operation. Its witness works for arbitrary paths and full marks in the declared domain, including FLOW EXACT normalization and run-2 requested STAR at the cap. | E12–E15, E19 |
| P09 | Entry acceptance uses one complete paired row. A seed's layer is not a constraint on the later output layer. Complete ND premises remain complete during publication and application. | E14, E23 |
| P10 | Exit selection preserves the candidate mark, actual E, layer and H under its stated representability rules. A concrete selector does not synthesize concrete taint on a FLOW result. | E14–E15, E23 |
| P11 | The extra field cut uses that row's paired output depth: `min(currentLimit, FL(Dp)+1)`. Cuts are DEMAND; in-budget NORMAL pieces can persist; rejected raw candidates have no semantic summary state. | E14 |
| P12 | Whole-pair FLOW EXACT normalization preserves suffix behavior, including field-overwrite exclusions and permitted RemoveAll actions. | E15 |
| P13 | Canonical input and canonical relation selection preserve required admission effects. If an initial disappears, give another executable route through a retained normal record or valid new demand. Literal input denotation alone is insufficient. | E07, E16–E18, E22 |
| P14 | Saved replay precedes current admission. It preserves the original actual and support layer; an empty current demand does not erase an applicable saved effect. | E17–E24 |
| P15 | A loop observation which keeps or cuts a fact has a real continuation at the same scope and physical ports. Repeated shrinking saved steps, changed growth classifications and current admission must be checked together. | E16, E20–E22, E24 |
| P16 | Static carry selects its genuine paired family without inventing a NORMAL provider, implicit FLOW companion, root seed or unrelated field. The proposed explicit FLOW demand view follows P21. Real strong writes still kill overwritten fields and keep disjoint fields. | E13, E19–E20 |
| P17 | Typed ZERO/Target pairing preserves source permissions and reports. Provisional EXACT witnesses remain DEMAND. NormalTarget composes only with NORMAL support and is ignored backward. | E21, E23–E24 |
| P18 | Handoff retains precise STAR relations without inventing MAY refinement. Any additional guidance route must have a separate selected derivation. | E19–E21, E25 |
| P19 | Each complete principal program retains its required positive finding and negative controls under the combined rules, not only under an isolated shape calculation. | E01–E28 |
| P20 | The finite convergence examples finish naturally with the required report. No stable-count or arbitrary iteration cap replaces the outgoing-demand stop rule. | E16–E23 |
| P21 | Explicit FLOW demand completion uses only final retained DATA endpoints and legal counted prefixes, preserves exact owner/ports and complete paired heads, and creates no fact, provider, mark, source permission or frontier root. It also completes provisional FLOW rows which can cover T/DEMAND. | E19–E21, E28 |
| P22 | Ordinary analysis under the completed FLOW permission actually infers the required NORMAL transfer. A disjoint write preserves g; a write to g kills it. Cross-base p-to-ret transfer uses a single complete paired row. | E13, E19–E20, E28 |
| P23 | New demand permissions preserve the whole loop-observation continuation and do not sustain a new outgoing DEMAND frontier. Excluding selector copies from the frontier is not enough to prove this result. | E16, E20–E22 |

Source/store lifetime, immutable run snapshots, exact owner boundaries and
existing aliases are assumptions only where the baseline contract already
provides them. List each assumption at its use. Do not add grounding state,
raw input history or a new output flag as an unlisted proof helper.

## 3. Reference functions and implementation checks

The reference model must define these operations together:

```text
canonicalFacts(current, offered)
subsumes(admittedProvider, candidate)
emitInitial(run, demandEntry, submittedFact)
start(initial, admittedLayer)
normalizeSummary(completePremise, candidate)
entryWitness(run, demandEntry, normalizedPremiseMember)
restrictExit(candidate, pairedOutput)
restrictSummary(owner, completePremise, candidate, completeDemandRow)
applyCurrent(actual, admittedSummary)
applySaved(actual, normalRecord, matchingRole)
handoff(admittedSummaryOrTarget)
```

The C2/C5 image proof must not enumerate only a fixed list of example fields,
paths or marks and then claim completeness for arbitrary native inputs.
A finite relative witness algorithm can use the supplied demand/initial and
a constructive fresh admitted field. Check static class/field anchors and
typed ZERO separately from ordinary counted-field paths.

Keep publication, persistence and future demand based on admitted results.
An index is a view of those results. It cannot retain an old provider or
rejected candidate to make an existence proof succeed.

## 4. Historical evidence and the repaired route

The later static no-loop and two-loop captures show a concrete STAR identity
without a matching NORMAL FLOW provider. Concrete-only admission is selected.
The implicit static carry is demand, not an executable NORMAL summary.
No proof can assume the missing FLOW row exists.

The two-loop native diagnostic completes run-3 with no finding. Its 59
pipeline records show saved ZERO replay reaching the method exit, while
the marked exact fact is kept at the loop boundary and offered to repeat.
This is not proof of a missing ZERO path. The initial-admission return at
that final offer remains source-derived.

The separate deep-loop capture completes run-5 without its required
finding. It includes an EXACT-origin DemandTarget, accepted later STAR
Target guidance, an exact DATA repeat selector and a saved NORMAL shrinking
relation. Removing a tail marker alone does not prove its recovery.

These are evidence about their pinned later runtimes. They are not new
baseline runs or proofs that the redesigned operators fail or pass. The
new model must trace them under its actual selected rules. If the fixed
rules leave no route, show the concrete counterexample and request the
intended behavior before adding another semantic mechanism.

The new positive components below address the old missing transfer routes.
The old failures remain evidence about their pinned runtimes. Native adapter
and whole-driver equivalence are separate implementation obligations. Do not
infer them from a component receipt or a matching demand count.

## 5. Checked negative result: the static carry interface

The [portable static model](lean/proposals/subsumption-initial-demand-20261107/README.md)
has 22 root-kernel-checked local theorems. All declared theorems were audited;
their only printed axiom dependency is `propext`. The check returns a concrete
finding and no finding for the modeled selected interface.

This result exposes a missing bridge, not a successful redesign. In the
finite E19 instance, C2 has a real MAY/MAY carry-pair witness in run-2 and
starts the selected STAR identity. C5 retains it. Its precise STAR handoff,
the absence of a saved DATA provider, and the selected later descendant
rejection leave no DATA at the call output in run-3. ZERO replay is available
and source permission is true. A generic theorem gives the same result for
any complete C2 implementation which preserves that rejection.

The model states its no-other-DATA-route and retained-carry assumptions. It
does not prove the complete native engine has only those routes. The pinned
no-loop capture and the separate actual ZERO-replay trace supply interface
evidence. Neither a new native redesign run nor a repair is claimed.

The same model gives a concrete conditional-pass counterexample to blanket
DEMAND-to-NORMAL promotion. A false guard cannot become a valid unconditional
transfer merely because a hypothetical row has STAR geometry and no H flag.
Its compiled native adapter remains to be checked.

## 6. Checked component map

The [portable package](lean/proposals/subsumption-initial-demand-20261107/README.md)
contains the sources, exact hash manifest, root receipts and complete axiom
audits. The receipt is scoped: `nativeAnalyzerProved=false` and
`allPrincipalProgramsProved=false`. The latter means that there is no single
formal theorem for all native Java programs in the catalog. Local proofs and
scoped producer/consumer program models must not be relabelled as that theorem.

| Component | Laws | Obligations and exact boundary |
| --- | ---: | --- |
| Original Canonical/Relations/Matching/Reachability | 162 | P01/P03/P05 and relation-path witnesses; byte-identical to 528; native eligibility is an input; original protected-prefix law is superseded by literal H |
| Relative C2/image | 47 | P06–P08 for arbitrary Nat fields, full marks, finite E and restricted FULL runs; 24 executable cells; no static/group adapter theorem |
| Annotated C5 exits | 57 | P09–P11: typed controls, complete ND originals, paired rows, selection, layers/H and counted cuts; entry image is a callback |
| Native FLOW EXACT/E input bridge | 30 | P06/P08: legal nonempty-E exact FLOW uses only a query-local Empty-E view; original actual unchanged |
| Literal H/pass | 19 | P02: exact typed union, freshness, both arrival orders and no pass-created flag; ordinary DATA is an unchanged parameter |
| Selected transitive subsumption | 38 | P03/P04: equal-mx aligned FLOW, transient B, T/H negatives, local T work, both arrival orders, no stored B |
| FLOW demand completion | 50 | P21: final-row provenance, both DATA endpoints, legal prefixes, one complete paired erasure, exact ports and row-count bounds |
| Wrapper pipeline | 34 | P13/P14: real loop-free 1,1,2 source/read/call/permission/finding route for arbitrary finite ordinary wrappers |
| Concrete converter wrapper | 17 | P13/P14/P19: E18 actual T→U source/summary kernels, C2/C5, finite wrappers, accepted-source preconditions and wrong-mark negatives |
| Static/cross-base provider | 20 | P16/P22: actual C2/body/C5 derives E19/E28 NORMAL provider; same-field kill and exact-parent controls |
| Two-loop header flow | 27 | P14/P16: E20 actual header versus repeat ports, weak fixture versus strong negative, real source permission and marked sink path |
| Uniform OWASP/C5 | 24 | P20/P23: arbitrary H depth, actual uniform body/C5 and no-D cut under the paired depth bound; no arbitrary driver theorem |
| Finite Deep consumer union | 35 | P15/P18: complete supplied family, fine-key versus all proper cuts, real inferred shrinker and finite NORMAL shrinking chain |
| Deep producer arrival | 35 | P15/P17/P18: F1/B2/F3/B4 rows derived under global limits 1,1,2,3; exact source/Target/control ports retained |
| General loop bound and E07 | 19 | P13/P15: ALL labelled query families, depth bound and fine-key distinction; canonical root MUST identity retains an arbitrary full-mark field observation |
| Deep extra-frontier bound | 27 | P15/P18: source/cap/read and nonexpanding replay grammar, independent B4 initial/output bounds, ALL additional F5 family/cut distinction at global limit4 |
| Loop/mapper gate and pipeline | 13 | P13/P15/P19: E16 actual field writes, B2-derived adjacent query, ALL extra-family cut distinction and the feasible NORMAL source-to-sink path |
| One-step C2 bound | 8 | P08/P15: every C2/public key depth≤demand depth+1, independent of actual depth; B4 actual depth3 may produce only a depth2 key |
| Static negative interface | 22 | Old E19 no-provider counterexample and E27 anti-promotion control; not positive soundness laws |

The final portable root audit passes **684 declared laws**. Its receipt and
complete axiom list are in the package README. Counts include reused original,
negative, representation and local laws. They do not measure proof strength.

## 7. Constructive proof arguments

### Canonical data and literal H: P01–P02

For MAY, map each covered descendant location to the retained prefix. For
MUST, test the first suffix field against E. At the same head, a location is
in the union exactly when its first field is absent from E1 or absent from E2,
which is absence from their intersection. A whole immediate child fills its
one excluded branch; a deeper or partial child does not. Apply these arguments
per compatible ordinary mark/header cell.

H is a separate finite set of typed coordinates. Its update is set union.
Every supplied coordinate remains present, an exact duplicate adds nothing,
and a pass maps only existing coordinates. This proof does not apply the old
ordinary prefix-pruning operation to H. The packet delta must preserve the
old ordinary carrier deliveries and the new exact H upgrades.

### Correlated relations and native roles: P03–P05

Given a long suffix tau, use r++tau in the short NORMAL provider. Equality
of the compared mx cells and Empty E establish the same suffix admission.
For A→B→C, compute B's correlated view from A and apply the existing FLOW/T
membership test at C. This view is a witness, not an admitted or persisted
row. Protected C is retained. Testing C against the same admitted A in either
arrival order gives the same final visible basis. Stale queues consult that
basis before delivery.

The matching filter keeps native same-head/descendant/MAY/MUST eligibility.
It removes strict-ancestor STAR inside use exactly when the role is not
opposite saved. The reverse-MUST overlap witness is separately typed; this
proof does not make every MUST record a trusted reverse view.

### Initial/image equivalence: P06–P08

Split the two paths into equal heads, a proper actual extension, a proper
demand extension, or incomparable heads. Each accepted table case constructs
one of five templates: root EXACT, root STAR, root MUST/E, first-child STAR,
or first-child EXACT. Test marks, direction, E and limit before rendering.
Every rendered path is the demand head or its first new field. Thus no ANY
initial exists and its depth is at most demand depth+1. The max-demand/actual
depth bound also follows.

Conversely, each legal template constructs a relative actual witness for its
image cell. Run-2 requested STAR constructs an admitted new-field witness;
at the field cap there is none. Normalize the complete FLOW pair only after
this raw witness check. The FLOW EXACT/E query bridge preserves the relevant
path/mark tests while the real actual keeps E. This proves both directions
of the C2/C5 entry image within the declared scalar domain.

### Paired C5 and whole-pair normalization: P09–P12

An entry witness selects one complete row. It retains all of P even when the
witness belongs to only one ND member. Apply that row's exit operation and
budget; no argument obtains a budget from another row. Each projection keeps
the candidate mark, actual support and supplied H. Any lost field suffix is
covered by the clipped ANY result on DEMAND. The per-row result union retains
all such outputs. Public FLOW EXACT normalization is performed after packing
and preserves each endpoint's own fields/exclusions.

The existing exact-FLOW transfer invariant is essential: a write that removes
f updates its exclusion before EXACT-to-STAR summary normalization. The
normalized relation therefore does not restore f. RemoveAll cleans the whole
selected position, including permitted child positions. A below-only cleaner
that leaves an unexcluded root is not legal under the selected baseline.
Concrete exact endpoints and Target origins are not normalized by this law.

### Operational progress and controls: P13–P20

A canonical input need not produce the old redundant initial list. E07 gives
a constructive retained-MUST identity route. E17 gives real wrapper bootstrap,
backward source permission and later NORMAL application. E19/E20 give actual
FLOW provider derivations and saved-first marked application. The actual
binding joins support, so a NORMAL symbolic FLOW provider cannot upgrade a
DEMAND actual into a NORMAL sink witness.

In E21, derive source and Target rows at their real ports, complete their
DATA endpoints, and distinguish the fine query key from every proper cut.
The ordinary inferred saved read then decreases chain length until a concrete
NORMAL actor can reach the sink. Target DATA output is not treated as a DATA
entry. The B4 Reach/Target producers are typed controls, outside diagonal
FLOW-backed T-to-T DATA replacement; they cannot be removed to hide the
needed endpoint. The completed query emits STAR keys, so ordinary MAY/MUST
leaf canonicalization does not prune those keys. A real backward source
action, not a FLOW permission, grants the source permission. NormalTarget composes with NORMAL only and is ignored backward.

For E22's uniform producer family at limits 1,1,2, canonical body depth is
max(n-1,0). Every B2 DATA output has depth≤1 by the global limit, so every
reversed F3 entry has n≤1≤s+1. Self-prefix completion has equal endpoint
depths; paired erasure retains the original n,s. Actual C5 therefore produces
only in-budget NORMAL output. This does not assert the false general bound
that an output always has depth≤its own stored premise depth+1. Remove eligible T/D arms with the real NORMAL provider first. A forward
frontier containing no DEMAND record then stops by the existing empty-demand
criterion. This is an induction for the stated producer family; it does not
prove termination for arbitrary Java programs.

### Explicit FLOW demand completion: P21–P23

Each added pair carries a source row and either one endpoint prefix or both
original DATA heads. Prefix depth cannot exceed source depth. The interface
is copied exactly. No Cartesian product or recursively generated row is
needed. The witness therefore proves provenance, legality and the linear
row-count bound.

A derived pair grants only analysis permission. Its identity query is a
conditional relation; ordinary transfer and C5 must produce the provider.
Actual support still controls application. Strong same-field kill, negative
mark controls and provisional concrete STAR/D starts remain unchanged.
The static and loop models demonstrate the required progress routes. No
selector itself creates an outgoing frontier item or a SourceHit. Newly
inferred DEMAND results still count normally. Thus this argument does not
replace the principal no-cycle proof with an indexing convention.

## 8. Implementation obligations

The native implementation must validate static anchors, real mx/group
catalogs, scalar/packed equality, complete ND and alias application, stored
FLOW normalization, SourceHit/report adapters, and exact loop-port lookup.
For Deep, the producer grammar must cover every relevant native current and
saved row before an all-family bound is used. These are explicit proof/model
to code obligations. They are not permission to change field transfer,
cleaners, Target/ZERO admission, layers or the selected stopping rule.

Run every principal native program with its original strict assertion after
implementation. A historical run-3/run-5 failure and a new Lean model are
different evidence. Record the latest reached/completed run labels in every
new runtime report. No real-project result is added by this proof package.
