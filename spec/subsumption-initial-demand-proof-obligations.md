# Proof obligations for the combined redesign

7 November 2026. Finalization status updated 8 November 2026. This is the
proof and implementation-validation map for the finalized specification.
The checked domains and remaining implementation obligations are stated below.
Review update: companion emission, overlap matching, strict-ancestor STAR
rejection and same-flag coverage are explicit revised rules. The selected
8 November update keeps both exact protection classes, widens partial
selected STAR cleaner survivors to ANY/DEMAND, and exempts ZERO-premise
loop summaries from only the extra loop gate.
Earlier receipts describe their stated operators. The scalar E21 family and
gate comparison is now checked. Native correspondence, its stopping proof
and E29's Conductor recovery remain open.
The [8 November audit](subsumption-loop-and-gap-audit-20261108.md) adds E31:
a legal direct selected cleaner exposed a separate run-3 continuation gap;
the selected survivor rule repairs its checked local route.
It also corrects E27: the abstract guarded pass is not implemented as a
guarded native pass at the selected baseline.
Follow [proof-guide.md](proof-guide.md). Use the
[frozen pre-implementation baseline](subsumption-redesign-baseline-20261107.md)
and [principal examples](subsumption-principal-examples-20261107.md).

The target is one specification for edge subsumption, initial emission and
paired demand intersection. A local inclusion theorem is not sufficient.
The combined rules must preserve the required source-to-sink routes in every
principal example. No runtime implementation is changed by this proof work.

**Known-gap status:** no further unresolved FN-producing counterexample
is currently known in the reviewed FULL-mode cases. The selected three
repairs and the late run-5 uniform route cover the identified examples.
An open proof/adapter/project check below is a validation obligation; it
is not, by itself, evidence of another FN. The status is not a universal
soundness or convergence theorem. Historical models keep their original
scope and do not override the finalized rules.

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

The withdrawn STAR_OR_ANY proofs concern another contract. The plain-STAR components below check the selected finalized contract
within their stated domains. None is a universal model of the native driver.
The withdrawn SOA contract is not a replacement for these obligations.

Use constructive witnesses. A proof of existence must give the relevant
actual fact, relation, demand row or program path. Use no `sorry`, custom
axiom, classical choice or assumed native-equivalence theorem.

## 2. Required results

| ID | Required statement | Principal cases |
| --- | --- | --- |
| P01 | Canonical MAY/MUST union preserves represented positions and marks under the selected E laws. A partial child cannot fill a whole excluded field. | E04–E06 |
| P02 | Subsumption compares equal protection flags. Exact plain/protected duplicates remain two memberships and are published independently. Neither flag class covers the other; a pass never creates protection. | E06, E10–E11 |
| P03 | An admitted aligned NORMAL relation covers its specialization by an executable common-suffix witness. Include both endpoint E, legal static bases and admitted-mark inclusion. An absent or rejected provider cannot cover anything. | E01–E02 |
| P04 | Coverage is transitive, including NORMAL FLOW followed by FLOW-backed concrete coverage. Final coverage works in one packet and both arrival orders without retaining an intermediate row. | E03, E06 |
| P05 | Current, saved-direct and opposite matching have exactly their selected roles. All incoming STAR facts obey the strict-ancestor restriction; MAY/MUST keep their own rules. | E08–E09 |
| P06 | Primary C2 emits no ANY initial or premise, creates no full mark from FLOW or another full mark, and respects base, E, direction and limits. An ordinary STAR strict ancestor of the demand rejects, with no companion. | E12–E13 |
| P07 | Both selected same-head ANY/STAR inputs under ANY demand yield the same ordinary STAR identity start. FLOW starts NORMAL; concrete STAR starts DEMAND. No MAY start or new tail is used. | E12, E17–E18, E25 |
| P08 | C5's normalized entry predicate is exactly the constructive image of the same C2 operation. Its witness works for arbitrary paths and full marks in the declared domain, including FLOW EXACT normalization and run-2 requested STAR at the cap. | E12–E15, E19 |
| P09 | Entry acceptance uses one complete paired row. A seed's layer is not a constraint on the later output layer. Complete ND premises remain complete during publication and application. | E14, E23 |
| P10 | Exit selection preserves the candidate mark, actual E, layer and H under its stated representability rules. A concrete selector does not synthesize concrete taint on a FLOW result. | E14–E15, E23 |
| P11 | The extra field cut uses that row's paired output depth: `min(currentLimit, FL(Dp)+1)`. Cuts are DEMAND; in-budget NORMAL pieces can persist; rejected raw candidates have no semantic summary state. | E14 |
| P12 | Whole-pair FLOW EXACT normalization preserves suffix behavior, including field-overwrite exclusions and permitted RemoveAll actions. | E15 |
| P13 | Canonical input and canonical relation selection preserve required admission effects. If an initial disappears, give another executable route through a retained normal record or valid new demand. Literal input denotation alone is insufficient. | E07, E16–E18, E22 |
| P14 | Saved replay precedes current admission. It preserves the original actual and support layer; an empty current demand does not erase an applicable saved effect. | E17–E24 |
| P15 | A loop observation which keeps or cuts a fact has a real continuation at the same scope and physical ports. Repeated shrinking saved steps, changed growth classifications and current admission must be checked together. | E16, E20–E22, E24 |
| P16 | Static carry selects its genuine paired family without inventing a NORMAL provider, root seed or unrelated field. Only the explicit authorized companion can add FLOW. Do not add the historical completion candidate from P21. Real strong writes kill overwritten fields and keep disjoint fields. | E13, E19–E20 |
| P17 | Typed ZERO/Target pairing preserves source permissions and reports. Provisional EXACT witnesses remain DEMAND. NormalTarget composes only with NORMAL support and is ignored backward. | E21, E23–E24 |
| P18 | Handoff retains precise STAR relations without inventing MAY refinement. Any additional guidance route must have a separate selected derivation. | E19–E21, E25 |
| P19 | Each complete principal program retains its required positive finding and negative controls under the combined rules, not only under an isolated shape calculation. | E01-E31 |
| P20 | The finite convergence examples finish naturally with the required report. No stable-count or arbitrary iteration cap replaces the outgoing-demand stop rule. | E16–E23 |
| P21 | Historical, unselected FLOW completion uses only final retained DATA endpoints and legal counted prefixes, preserves exact owner/ports and complete paired heads, and creates no fact, provider, mark, source permission or frontier root. Prove its necessity separately. | E19–E21; historical comparison, not an implementation requirement |
| P22 | Under an explicitly supplied completed FLOW permission, ordinary analysis infers the stated transfer. A disjoint write preserves g; a write to g kills it. E28's actual id already has its provider from run-1. | E13, E19–E20, E28 |
| P23 | New demand permissions preserve the whole loop-observation continuation and do not sustain a new outgoing DEMAND frontier. Excluding selector copies from the frontier is not enough to prove this result. | E16, E20–E22 |
| P24 | STAR/STAR summary overlap selects actual STAR/MUST with Eactual union Eread, preserves original actual/mark/H/layer, and retains direct and opposite application effects required by generalized E subsumption. Do not enable CURRENT strict-ancestor STAR matching. | E02, E08–E09 |
| P25 | Expanded C2 keeps the primary and authorized concrete-STAR FLOW companion. A successful ANY-demand strict descendant also emits the exact FLOW prefix identity. The raw image grows for concrete demands; the complete normalized C5 image is unchanged by this extra seed. | E12, E19, E25, E28; ExactFlowPrefixCompanion |
| P26 | The E29 canonical basis preserves a real route to both Conductor Graal identities. Show retained finer demand or derive actual saved NORMAL transfer; a duplicate STAR/FLOW command is insufficient. | E29; real-project implementation acceptance check; small late route checked through run-5 |
| P27 | Canonical plain/protected views preserve each class's current region under insertion, duplicates and arbitrary offer permutations. The two exact classes are both retained; neither is reconstructed from the other. Native cache, restore and delivery preserve those views. | E06, E11; local region proof, native bridge open |
| P28 | Under current C2, a deeper output selector can still select a required correlated STAR relation. Compare STAR rejection, completion and an explicitly added coarse run-2 FLOW start, including source permissions and finding route. | E30; GetFFC5Policy, GetFFCoarseFlowRun2 |
| P29 | Derive E21's reference families rather than supplying three rows. Check pre-canonical bounds/subsets, local-vs-parent origins, all run-5 DATA selectors, both admitted source images and the kept gate with completion off/on. | E21ClosedFamilies, E21AllSourceImages; scalar contract only |
| P30 | Execute the new raw exact prefix through existing transfer before normalization. Derive E30 recovery with the actual emitter and recompute E21 rather than reusing old phase equalities. Preserve write E, cleaner mx, support, source permissions and complete C5 exits. | GetFFExactFlowPrefix, E21PrefixExactCompanion; field-kernel source audit |
| P31 | Preserve the marked-child continuation through direct empty-path EXACT selected cleaning. Include the real run-1 request answer, unchanged FLOW mx, the new protected ANY survivor, paired C5, saved NORMAL rows and source permission. | E31; CleanerMaySurvivorCandidate checks recovery through run-3; SelectedCleanerStarSurvivor checks the selected generic transformation |
| P32 | Retain, publish and transport plain/protected memberships independently. A second exact class is fresh; a repeated same class is not. Both arrival orders and ordinary passes preserve both classes without OR collapse. | PlainCoverageDelivery replaces the render-only contract; native key/packing/restore integration remains required |
| P33 | Close saved-first repeat delivery together with global limiting, loop cuts, completion freshness, C2 and current publication. Distinguish raw pre-gate candidates, parent completions and local summary originals. A transaction universe is not a reached fixed point. | E21Run4SavedReplayClosure checks the run-4 repeat component; all ports/enclosing publication remain open |
| P34 | Close run-2/run-3 publication-to-standing-input replay and saved replay before handoff. Include late concrete STAR admission, native ANY-ancestor matching, source permission, typed controls and valid NORMAL persistence. Compare final paired rows, not only input facts or one-body candidates. | E21Run2Run3WorklistClosure checks unchanged seven/three paired sets and arbitrary further rounds in the declared component; native adapters remain open |
| P35 | ZERO-premise summaries bypass only the extra loop gate; inspect the effective local premise after reversal. Keep global cuts, paired C5, liveness, layers and DATA-premise growth checks. Recover the existing NORMAL source/read/sink route without completion. | ZeroPremiseLoopBypassCandidate checks unchanged run-2/run-3 component fixed points and run-5 recovery; eight native component tests; general DATA-row and whole-driver obligations remain open |
| P36 | Widen only the old selected PART STAR/T residual to ANY/T,DEMAND,Empty E; keep P and H. Prove inclusion and unchanged NORMAL, exact, other-mark, disjoint, MUST/MAY and RemoveAll behavior. Clear E after the existing spatial test. | SelectedCleanerStarSurvivor plus E31 phase model; no change to initial grammar or field-action lowering |

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

The same model gives an abstract conditional-pass counterexample to blanket
DEMAND-to-NORMAL promotion. The native compiler audit now establishes that
it removes this residual pass guard with a diagnostic. Thus the abstract
example is not native evidence. Keep the real-provider obligation and use
the actual source/cleaner kernels for native controls.

## 6. Checked component map

The [portable package](lean/proposals/subsumption-initial-demand-20261107/README.md)
contains the sources, exact hash manifest, root receipts and complete axiom
audits. The receipt is scoped: `nativeAnalyzerProved=false` and
`allPrincipalProgramsProved=false`. The latter means that there is no single
formal theorem for all native Java programs in the catalog. Local proofs and
scoped producer/consumer program models must not be relabelled as that theorem.

| Component | Laws | Obligations and exact boundary |
| --- | ---: | --- |
| Original Canonical/Relations/Matching/Reachability | 162 | P01/P03/P05 and relation-path witnesses; byte-identical to 528; protection policy is historical, not the revised same-flag rule |
| Relative C2/image | 47 | P06–P08 for arbitrary Nat fields, full marks, finite E and restricted FULL runs; 24 executable cells; no static/group adapter theorem |
| Annotated C5 exits | 57 | P09–P11: typed controls, complete ND originals, paired rows, selection, layers/H and counted cuts; entry image is a callback |
| Native FLOW EXACT/E input bridge | 30 | P06/P08: legal nonempty-E exact FLOW uses only a query-local Empty-E view; original actual unchanged |
| Literal H/pass | 19 | P02: exact typed union, freshness, both arrival orders and no pass-created flag; ordinary DATA is an unchanged parameter |
| Selected transitive subsumption | 38 | P03/P04: equal-mx aligned FLOW, transient B, T/H negatives, local T work, both arrival orders, no stored B |
| FLOW demand completion | 50 | P21: final-row provenance, both DATA endpoints, legal prefixes, one complete paired erasure, exact ports and row-count bounds |
| Wrapper pipeline | 34 | P13/P14: real loop-free 1,1,2 source/read/call/permission/finding route for arbitrary finite ordinary wrappers |
| Concrete converter wrapper | 17 | P13/P14/P19: E18 actual T→U source/summary kernels, C2/C5, finite wrappers, accepted-source preconditions and wrong-mark negatives |
| Static/cross-base provider | 20 | P16/P22: conditional provider derivations; its artificial E28 no-saved-provider premise is not reachable evidence for ordinary id |
| Two-loop header flow | 27 | P14/P16: E20 actual header versus repeat ports, weak fixture versus strong negative, real source permission and marked sink path |
| Uniform OWASP/C5 | 24 | P20/P23: arbitrary H depth, actual uniform body/C5 and no-D cut under the paired depth bound; no arbitrary driver theorem |
| Finite Deep consumer union | 35 | P15/P18: complete supplied family, fine-key versus all proper cuts, real inferred shrinker and finite NORMAL shrinking chain |
| Deep producer arrival | 35 | P15/P17/P18: F1/B2/F3/B4 rows derived under global limits 1,1,2,3; exact source/Target/control ports retained |
| General loop bound and E07 | 19 | P13/P15: ALL labelled query families, depth bound and fine-key distinction; canonical root MUST identity retains an arbitrary full-mark field observation |
| Deep extra-frontier bound | 27 | P15/P18: source/cap/read and nonexpanding replay grammar, independent B4 initial/output bounds, ALL additional F5 family/cut distinction at global limit4 |
| Loop/mapper gate and pipeline | 13 | P13/P15/P19: E16 actual field writes, B2-derived adjacent query, ALL extra-family cut distinction and the feasible NORMAL source-to-sink path |
| One-step C2 bound | 8 | P08/P15: every C2/public key depth≤demand depth+1, independent of actual depth; B4 actual depth3 may produce only a depth2 key |
| Static negative interface | 22 | Old E19 no-provider counterexample and E27 anti-promotion control; not positive soundness laws |

The earlier portable audits passed 684 and then 776 declared laws. The latest
checked component set and complete axiom list are in the package README.
P15/P19's native E21 correspondence, P23's stopping result and P26 remain open. Counts include reused original,
negative, representation and local laws. They do not measure proof strength.

## 7. Constructive proof arguments

### Canonical data and the two coverage views: P01–P02, P27

For MAY, map each covered descendant location to the retained prefix. For
MUST, test the first suffix field against E. At the same head, a location is
in the union exactly when its first field is absent from E1 or absent from E2,
which is absence from their intersection. A whole immediate child fills its
one excluded branch; a deeper or partial child does not. Apply these arguments
per compatible ordinary mark/header cell.

The old LiteralProtection model preserves every historical H coordinate.
It is no longer the current compaction rule. Apply current canonicalization
independently to U and H. For any candidate region, insertion preserves the
previous region or adds the offered region in that flag class. Transitivity
gives a retained witness when insertion removes a covered child. Folding this
law makes coverage depend on the offered set, not its order. That input list
is a proof witness, not a stored offer history.

The old OR draft rendered exact duplicates once and lost plain membership.
The selected rule renders both classes. PlainCoverageDelivery proves that
fresh own-class publication keeps producer and subscriber canonical states
equal for arbitrary offer lists in its scalar domain. A repeated exact
class publishes nothing. Same-geometry opposite classes both publish.
Native E/mx/packed storage, fresh deliveries and restore remain bridge checks.
A pass still carries its supplied flag and creates none.

### Correlated relations and native roles: P03–P05

Given a long suffix tau, use r++tau in the short NORMAL provider. Equality
of the compatible field/mark regions establishes the same suffix admission.
For A→B→C, compute B's correlated view from A and apply the existing FLOW/T
membership test at C. This view is a witness, not an admitted or persisted
row. A and C must have the same flag in their coverage view. Testing C against the same admitted A in either
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

The review rejects ordinary STAR actuals strictly above the demand before
emission. MUST/ANY and every unblocked cell keep the old operation. Every
old structural image template has an executable unblocked witness: its
EXACT-at-head witness is sufficient where the ancestor STAR was removed.
Thus actual admission changes while the finite raw/normalized image stays
the same. The companion still requires a successful concrete STAR primary.

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

E21's existing models derive necessary source/Target routes and distinguish
a supplied fine query from a cut. They do not enumerate every final retained
DATA pair. The reviewed operator checks include omitted B2 FLOW rows which
can already produce the F3 shrinker without completion. They also show that
a B4 ZERO exit rejects all DATA outputs, including a companion. Neither fact
alone proves that the complete final authority has no other route.

The new `E21ClosedFamilies` computes all finite scalar families and checks
these classification laws before canonicalization as well as afterward.
The subset law avoids assuming monotonicity of canonical admission. Actual
source/read witnesses separately construct the required positive rows.
`E21AllSourceImages` checks the shorter C5 DEMAND image as well as the NORMAL
source image. Without completion both fail the kept gate. With completion
NormalTarget is restored, but DemandTarget can remain. Do not infer stopping.

The [review](descendant-intersection-and-flow-completion-review-20261107.md)
states the ownership/grammar/port boundary. Do not assume the raw source reaches
saved shrinking replay when an earlier growing-output gate can drop it.
Real backward SourceHit remains necessary; FLOW alone grants no source
permission. NormalTarget composes with NORMAL only and is ignored backward.

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
The static models demonstrate conditional routes under their supplied views.
E21 supplies a scoped kept-gate counterexample, but its existing saved NORMAL
repeat continuation is omitted by that gate. The no-completion diagnostic
route reaches the existing exact demand and a NORMAL Target. Thus E21 does
not establish a need for endpoint self-guidance. Necessity of any completion
addition, native correspondence and convergence
remain open. No
selector itself creates an outgoing frontier item or a SourceHit. Newly
inferred DEMAND results still count normally. Thus this argument does not
replace the principal no-cycle proof with an indexing convention.

## 8. Implementation obligations

The native implementation must validate static anchors, real mx/group
catalogs, scalar/packed equality, complete ND and alias application, stored
FLOW normalization, SourceHit/report adapters, and exact loop-port lookup.
It must also preserve both current protection coverage views across freshness,
cache invalidation, publication and restore. The selected update exposes
both exact classes; PlainCoverageDelivery replaces the old OR rendering.
For Deep, the producer grammar must cover every relevant native current and
saved row before an all-family bound is used. These are explicit proof/model
to code obligations. They are not permission to change field transfer, other cleaner cases,
Target/ZERO admission, layers or the stopping rule. Only the selected
PART STAR survivor change and own-ZERO extra-gate bypass are authorized.

Run every principal native program with its original strict assertion after
implementation. A historical run-3/run-5 failure and a new Lean model are
different evidence. Record the latest reached/completed run labels in every
new runtime report. No real-project result is added by this proof package.

## 9. Review delta and the Conductor gate

The reviewed spec retains the existing normalized-image architecture. The
concrete-STAR companion has
a concrete STAR primary witness, identical path/E, FLOW with empty mx and
NORMAL identity support. Check raw containment on that primary. Do not apply
the primary's concrete-to-FLOW mark test a second time. The original paired
exit remains unchanged and rejects FLOW which excludes the requested T.
The companion has the primary's depth, so the old max-depth and first-new-
field bounds lift to that expanded stream.

The selected exact prefix companion additionally applies after successful
ANY-demand descendant admission. It is raw EXACT/FLOW/NORMAL at the demand
head. Its depth is no greater than the primary's; the actual stays unchanged.
The raw image extends for concrete demands, but its public STAR/FLOW key
already has a constructive old root-STAR or concrete-STAR-companion witness.
`ExactFlowPrefixCompanion` proves the complete normalized-image equivalence.
No new C5 exit permission or mark synthesis follows from this addition.

The generalized E pair proof uses both endpoint exclusions. The selected
matching bridge projects the same-head STAR/MUST actual to the overlap,
with union E and unchanged layer. This bridge is a semantic matching change;
the former nonstatic/Empty-E/equal-mx limits are not mathematical necessities.
Strict-ancestor CURRENT STAR matching is still disabled.

E29 is not just the root/child identity example E07. It has the same complete
uniform actual and one paired root-to-listener demand, but the lost child
entry changes C2 from MUST/FLOW to STAR/FLOW. The historical one-expression
rollback recovers both native report projections; a later strict report also
recovers both identities. The exact end-to-end necessity of the captured
child row for each sink remains unproved. The current completion function
cannot reconstruct that child from the retained root row alone. The new
companion duplicates Current's existing STAR/FLOW command. P26 therefore
remains an explicit acceptance gate. No normal frame or discarded history
may be assumed to close it.

## 10. Descendant intersection review

The [review](descendant-intersection-and-flow-completion-review-20261107.md)
compares a proposed policy; it does not select a runtime change.
`DescendantExitReview` proves that non-STAR cells are unchanged and gives an
executable requested-suffix witness for the rejected NORMAL FLOW row.

`GetFFC5Policy` derives the two-read helper's full finite argument/return
catalogs. Run-1's NORMAL unchanged-argument row exists, while its return row
is DEMAND. Run-3 infers the needed NORMAL correlated return under current C5.
STAR rejection without completion removes that return and the modeled sink
Target route. Completion supplies a different DEMAND bridge and restores a
NORMAL return route in run-5. Real source and sink AP actions, saved opposite
orientation and actual source acceptance are computed, not assumed.

This is not a full Kotlin root-driver theorem. The caller source rule,
ZERO/Target scheduling and root dead-local projection remain adapters.
Completion's extra argument-output demands are retained in the model; its
return finding proof is not a proof of natural stopping with those demands.

`GetFFCoarseFlowRun2` checks a second repair. Current C2 emits only the
field-specific run-2 initial. Adding a coarse `ret.*/FLOW` identity passes
the existing C5 image check and infers a DEMAND relation whose reversed
output selector is root ret. Proposed STAR rejection then admits the
run-3 NORMAL getter without completion. This is an explicitly added
counterfactual start, not a theorem that current C2 emits it or a general
prefix-admission design.

`E19CompanionControl` rechecks the earlier static interface with the expanded
emitter under its original concrete T demand pair. The ordinary disjoint
write preserves the FLOW companion, and C5 admits it. A same-field write
kills both seeds. Thus this particular interface is no longer evidence that
completion is necessary. Static prescan/carry correspondence remains separate.

`E21ClosedFamilies` and `E21AllSourceImages` cover P29. Their kept-gate
counterexample needs an endpoint self-permission, not the paired-head FLOW
erasure. Additional ZERO/Target entries cannot mint DATA commands. The model
uses one compatible effective repeat interface; native physical ports must
not be merged to manufacture its positive source/read witness.

## 11. Selected exact FLOW prefix companion

P30 separates the new C2 policy from existing field behavior. The raw seed
is an identity with Empty E/mx and H=false. It remains EXACT during execution;
only complete FLOW pairs normalize exact endpoints to STAR before C5/storage.
The field-specific primary remains required for reads below that exact head.
The source-only field audit pins the exact baseline rules for writes,
whole-position RemoveAll, selected-cleaner mx and nested ANY/DEMAND residuals.

`GetFFExactFlowPrefix` uses the generic new emitter, derives both run-2
summaries, computes the actual backward source permission and recovers the
run-5 NORMAL finding without completion. It checks all argument/return
candidates and retains actual DEMAND support during summary application.

`E21PrefixExactCompanion` delegates to that same generic emitter. It adds
one saved NORMAL grower in run-2; this does not enter demand handoff. It
recomputes run-3/run-4 and proves the complete run-5 demand view unchanged.
Every new run-4 prefix DATA candidate fails its complete paired C5. Every
admitted run-5 source image still fails the kept gate without completion,
even for an arbitrary saved continuation after that gate. Completion's
positive reference route remains, with no natural-stop claim.

`E21SavedRepeatGateDiagnosis` isolates why that kept-gate comparison is
not a proof that completion is required. The gate drops the three-field
NORMAL source before repeat input, where the existing NORMAL read would
run before C2. Two saved reads reach the exact-f admission; the ordinary
body then emits the NORMAL sink Target. This bounded route uses no extra
demand and preserves ZERO parent and actual support. Five native baseline
component tests validate its AP, C5, gate and real sink/Target operations.
They do not execute the complete redesigned iteration driver. A general
loop repair, including identities, cycles, late rows and physical ports,
remains a separate design obligation.

## 11. Selected resolutions on 8 November

The authoritative rules are sections 2.1 and 6 of the combined spec. The
OR-view and candidate models remain historical evidence for their original
definitions. They are not the current delivery or cleaner contract.

- Protection: keep both class memberships and send each fresh class through
  existing dependencies. No hidden-plain update protocol is required.
- Cleaner: change only the selected PART STAR result to ANY/DEMAND/Empty E.
  The E31 source/helper/sink route recovers in run-3 without completion.
- Loop: exempt only the applied row's own ZERO premise from the extra gate.
  The E21 source/read/sink route recovers in run-5 without completion.

The separate [Conductor fact trace](conductor-must-admission-fact-trace-20261108.md)
explains the remaining MUST-guidance issue. It does not select a C2 policy
change or establish recovery of the two real Conductor findings. Full native
integration, the general DATA-premise loop continuation proof and complete
project convergence remain open.

The selected [proof dossier](selected-gap-resolutions-proof-dossier-20261108.md)
and [latest checked receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1209.json)
map the three rules to their executable constructive witnesses. The generic
cleaner includes an explicit four-tail adapter, so unchanged MUST behavior
is checked rather than inferred from the older three-kind codec.

## 12. Conductor late refinement: run-4 and run-5

[ConductorLateIterations](lean/proposals/subsumption-initial-demand-20261107/ConductorLateIterations.lean)
adds a checked continuation of the small uniform-prefix example. It keeps
the live F3 root prefix EXACT, derives both return rows from real branches,
and derives two B4 outputs from separate complete C5 pairs. The NORMAL
row persists; the DEMAND row regenerates the child admission head. F5 has
a saved NORMAL return route and a current MUST probe, plus a separate
DEMAND output from the deep copy. Three native component tests confirm
mapper publication, inverse MUST read and typed source-shaped discharge.

This closes the stated late mapper/C5 route. It does not prove the whole
root/callee driver, a natural run-5 stop, or recovery of the two real
Conductor identities. P26 remains a real-project implementation acceptance check. No additional
current-spec permanent-FN example is established by this local admission
difference.
