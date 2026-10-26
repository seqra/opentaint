# Implementation proofs for correlated concrete initials

Date: 26 October 2026. Status: **local constructive proofs and implementation correspondence tests checked**.
The analyzer implementation passes the local gates recorded in the
[validation report](../docs/reports/bidirectional-correlated-concrete-validation-20261026.md). Read the
[implementation proposal](../docs/design/bidirectional-correlated-concrete-implementation-20261026.md)
and the [semantic specification](run1-correlated-concrete-initials.md).
The latest referenced Thingsboard result is **run-2 OOM; run-1 COMPLETE**.
This work contains no new project run or performance claim.

## 1. Proof boundary

The new [implementation model](lean/ApSpec/CorrelatedConcreteImplementation.lean)
imports the existing AP denotation, geometry and mark operations. It also
imports the [general concrete model](lean/ApSpec/Run1CorrelatedConcreteInitials.lean)
and existing protection/store models. It does not replace their historical
claims or alter their definitions.

The local laws use arbitrary finite field paths, exclusions and runtime
mark atoms. They have no run/FULL gate. A group is one current atom; no full
member enumeration is needed. All proofs are constructive. The executable
raw operator supplies the result list and requests. Each cover proof gives
the suffix or membership used by that operator. There is no `sorry`, new
axiom or classical witness selection.

These models are not a translation of the Kotlin analyzer or the IR.
They do not prove the baseline Java alias analysis, source-rule adapter,
whole-engine termination or all real-project observations. The selected record and alias contracts are stated in sections 8 and 9.
Their reference operations and invariants are proved below; Kotlin/IR
correspondence is a required implementation gate, not a new axiom.

## 2. Generic STAR start and transfer

The existing general module proves:

| Law | Checked result |
| --- | --- |
| `start_keeps_star_exclusion`, `excluded_seed_identity` | Concrete STAR/E starts as a DEMAND identity on every admitted suffix |
| `selected_seed_inside_old`, cross-suffix controls | New seed is contained in the old seed and removes unrelated-suffix pairs |
| `star_exclusion_cover` | Equal-output-path STAR coverage with sufficient FLOW suffix admission |
| `any_prefix_cover_general` | ANY coverage at an equal or shorter FLOW output prefix |
| `general_specialization`, `general_summary_application` | Mark specialization and equal-shape application use the same geometry |
| `star_reverse`, `layer_composition` | STAR reversal and sufficient layer strength are direction-independent |
| `handoff_exclusion_cover` | Forward STAR/E -> backward ANY is a cover, retaining marked locations |

The new `raw_apply_sound` proof covers **all cases of the shared non-must AP
geometry/mark kernel**, before the historical W2 erasure. Given an incoming
represented pair and one micro/summary-edge pair, it constructs either:

1. a member of the actual `rawApply` result with the composed pair, or
2. the actual request needed by a nonconcrete input mark.

The proof uses `CoreAux.geo_sound`, `gate_cases` and `den_result` with their
existing mark-exclusion/pass conditions. It returns the raw result rather
than applying the old `AFact.norm` concrete-STAR erasure. It therefore closes
the previous gap between isolated copy examples and the general kernel.
It does not redefine the unchanged must-taint rows.

`concrete_cannot_request` proves that a concrete input cannot take the
request branch. `raw_summary_sound` lifts composition through the summary
layer OR. `raw_keeps_demand` and `summary_keeps_demand` prove that ordinary
transport cannot promote a DEMAND input. Thus a same-original derivation
started by a concrete STAR/D seed cannot become a normal native record
merely because it retained STAR.

The request alternative is not authority to emit requests after run-1.
`abstract_premise_cannot_request` proves that the removed pure-transport
recipes and alias edges need none. Concrete dependency barriers retain their
marked demands and use ordinary later emission/restriction. No StrongQueries
or new later-run request mechanism is used.

Kotlin must implement that same case table in `EdgeApplication`, selectors,
summary compilation and reconstruction. In particular, STAR output E is
shared STAR E, not the must-only target exclusion. A constructor which
preserves STAR does not authorize a producer to invent a suffix binder.

## 3. Field and cleaner residuals

`empty_exclusion_cover_sound` keeps each represented pair while removing
STAR output E and setting DEMAND. It changes no path, tail or mark. This law
supports the existing run-1 exclusion-needing residual. It does not authorize
an E-free cover at every field write, removal of complete kills, or use of
that cover in a later strong run.

`cleaner_root_survivor` constructs the EXACT root pair from a STAR row whose
concrete output is the root. This proves the required same-root BELOW
residual without relying on the old ANY seed. Selected-mark protection must
remain on that residual. Full kills have no surviving witness; disjoint
rows keep the incoming pair; other partial rows retain the existing cover
or later exclusion policy.

The existing `limitF_sound` theorem applies to arbitrary concrete STAR too;
it never required a concrete-STAR ban. The kept path preserves its tail.
A cut produces an independent suffix and DEMAND. Source/GEN/ND fixed targets
and their old must-taint semantics remain separate operations. No new STAR
target is generated by those rules.

## 4. Typed packet correspondence

A packet has one complete `FlowBackedStore.Geometry`, selected atoms and
protected atoms. The geometry includes input and output kinds, including
STAR exclusions, paths, bases and output layer. It is not a FLOW premise
which is interpreted as every marked input/output combination.

`packet_decode_exact` proves that every decoded object is precisely one
selected atom's scalar relation and flag. `packet_decode_diagonal` proves
that this atom is its own premise/output mark. `packet_preserves_tail` and
`packet_preserves_input_geometry` prove that decode cannot change STAR to
ANY, lose E, or change the original input shape.

`projected_protection_subset` proves that atom projection retains protection
inside projected ordinary membership, even when different full atoms map to
one group. Production mark sets canonicalize duplicate images. A projection
must not drop the flag mask when it creates a new typed tree.

The Kotlin decoder still needs correspondence tests. The new diagonal header
and `DiagonalDelta` fields must be passed through `NeutralRelationBatch`.
A geometry lacking the required uniform mark/protection shape must use the
existing scalar fallback before mutation. No Cartesian expansion is needed.

## 5. Current residuals, late flags and duplicate work

The `Residual` model stores only current FLOW coverage, explicit marked
membership and its current protection. `project` maps the existing
`FlowBackedStore.Cell` specification history into that runtime state.
The historical `marked` bit is a proof ghost, not a runtime archive.

`residual_simulation` proves that runtime update equals projection of the
historical admission operation. `projected_transport` reuses its constructive
covered-relation theorem. Current residuals therefore retain the same pair
union and protected obligations as the concept model, without storing each
removed plain marked row.

`covered_plain_needs_no_archive` checks that an already-covered plain offer
creates no explicit stored row. `late_flag_is_retained` and `late_flag_is_work`
prove that a later flagged offer is restored even if FLOW already exists.
The incoming flagged offer supplies the data needed to restore it; no old
plain row is borrowed from an archive.

`residual_idempotent` and `residual_commutes` prove duplicate elimination and
arrival-order independence of the final state. `repeated_event_has_no_delta`
proves that an unchanged protected repeat produces no new work. These laws
must hold for the new STAR typed cell, not just for ANY.

This is a material implementation condition: the old `TaintGroup.subtract`
expression would not subtract STAR nonexact memberships. With the new type
admitted but no new subtraction case, repeated protected STAR offers can
keep producing an annotation delta. Constructor support alone is insufficient.

For a finite set of complete relation/flag keys, the existing per-key ghost
credit proof bounds novel FLOW/mark/flag changes. It does not prove a bound
on the number of method/query/ND keys in the full analyzer. It is not a
claim that Thingsboard run-2 will complete within a specified heap.

## 6. General replacement, without an alias guard

`remove_covered_relation` proves union preservation under pair inclusion,
without an identity/alias-class premise. `remove_covered_star` and
`remove_covered_any` instantiate it for the two selected geometry cells.
The protection rules remain mandatory; the alias classifier is not a
subsumption gate. Remove both the scalar identity residual branch and the
packed identity restoration branch.

All runtime admission owners must compare the exact complete initial shape
and current scope described by spec section 5.1. A trie branch without an
output annotation is not a covering output. STAR requires equal output
paths and admitted suffixes; ANY permits the current prefix cover.
EXACT/must/ND/cross-atom cells retain their explicit representation.

Raw and selected summary owners and publications normalize independently.
A late FLOW arrival can compact current marked residuals. Already delivered
work is not retracted. A late protected membership must still be emitted and
replayed. Callback/delta counts can vary with arrival order; the normalized
relation and protection state have the stated invariant.

## 7. Protection and record obligations

The existing `FlowBackedProtection` laws are not tied to a run number. They
retain triggering-conclusion assignment protection, restored-atom cycles,
selected-cleaner survival and sticky composition. Kotlin currently gates
some producers to FULL run-1; implementation must remove those gates while
keeping request and field policies scoped as before.

Ordinary later ND inputs also need metadata upgrades. Join-key equality must
not change a repeated literal binding into a new premise combination because
its flag changed. The implementation proposal requires an annotation upgrade
of the existing current binding and replay of its already-owned combinations.
No new ND origin products or facts history is selected.

Native records already carry a flagged `Facts` conclusion. Reversed scalar
views need the same bit passed to their consumer. The view's ordinary
semantic equality does not include this invocation metadata. The adapter
must attach the flag to the actual transported result and run the same cycle
check with the caller's original premise.

These are required Kotlin correspondence gates. The existing pure flag laws,
packet correspondence and repeated-upgrade proof do not establish that the
current code already transports those annotations; it currently does not.

## 8. Normal FLOW export with nonempty E

The user selected persistence of valid NORMAL summaries with nonempty E.
`nonempty_flow_export_gap`, `export_gap_has_a_pair` and
`covered_pair_can_lack_export` retain the old-validator counterexample.
It is a regression witness, not the proposed behavior.

`selectedNativeFlowInitial` removes the Empty-E restriction for the selected
abstract STAR initial. `nonempty_flow_is_persistable` proves eligibility for
arbitrary E. Normal-layer, singleton, positive-bound and direction checks
remain separate, unchanged gates. Ordinary concrete STAR seeds remain D.

`native_star_view_exact` proves exact pair reversal for a normal STAR FLOW
record with arbitrary Ei, Eo and mark exclusion X. The stored record retains
Ei and Eo. Its generic reverse view places their union on its STAR result,
with an unrestricted STAR read premise. Both sides admit exactly the same
suffix and mark; no exclusion is lost. The unchanged above-prefix read
can still take its ordinary DEMAND approximation.

`LayerTrace` models C0: every ordinary same-original step ORs in an
approximation bit and never promotes D. `demand_trace_stays_demand` proves
this invariant. `normal_covered_flow_has_record` gives the complete export
case split for selected STAR/ANY FLOW initials: a NORMAL trace cannot have
an ANY initial, whose start is D. It must have a STAR initial, and the
selected native validator admits its legal E.

Therefore a removed D marked row has either a retained FLOW demand or a
persisted NORMAL FLOW record. `IterationDriver` already calls persistence
before handoff. Original emission/restriction certificates then select and
retain each required represented pair. No new demand fallback or actual-input
query permission is introduced. The same argument applies in both directions,
with their current handoff projections and native/reversed views.

## 9. Input alias closure and identity redundancy

The user selected input alias closure as the reason identity-only alias
candidates can be omitted. The subsumption guard remains absent. No runtime
closure index, extra barrier, alias compatibility flag or FLOW replay is added.

`AliasState` is semantic proof data: an address map for named mark locations,
a predicate for actual T, and a predicate for represented input coverage.
It is not an analyzer data structure. `covered` can be supplied by FLOW or
TAINT and can include harmless over-approximation. False may-alias candidates
need not be present in the actual address relation.

`empty_inputs_covered` establishes the initial empty state. The reference
steps establish and preserve positive input coverage:

| Reference operation | Existing producer contract | Theorem |
| --- | --- | --- |
| `defineAlias` | A copy, field definition or binding supplies the new name from its source | `define_alias_preserves`, `transport_aliases_preserves` |
| `produceMark` | A mark/source/write arrival supplies existing genuine aliases | `produce_mark_preserves` |
| `cleanCell` | Cleaning removes actual positive marks; surviving required positives remain covered | `clean_preserves_positive_coverage` |
| Identity | No new positive mark location is created | `alias_step_covered` |

`alias_trace_covered` constructs the invariant over every finite sequence of
these events, including general pointwise binding/field transfer. Initial
actual inputs are mark-arrival events on the initial address map. The
executable controls check alias-before-mark and mark-before-alias orders.
Per-field-suffix copies use the same law; field-limit approximation is covered
by the existing AP transfer/cut theorems. A strong rebind uses the new address
map and does not require stale aliases to remain true.

`input_alias_closure` proves that a real T at p and a genuine alias p=q imply
that q/T is already represented. `identity_alias_is_redundant` proves that an
identity-only arm creates no uncovered concrete alias consequence. This closes
the required consequence proof for the later NORMAL-FLOW/DEMAND-T identity
case. `covered_alias_step` proves coverage through a shared enabled alias
edge for every represented pair. For run-1, ANY FLOW remains alias-enabled
and STAR equal-path raw identity shapes agree. Backward stages retain their
alias transfer. In later forward runs the N identity/D marked distinction
uses the closure result; other enabled edges use composition.
`direct_arm_retained` separately proves direct output retention; it is not
the closure argument.

`alias_work_is_not_equal` remains a negative control: old auxiliary candidate
lists can differ. The selected correctness claim is coverage of required
concrete facts and demands, not equality of false may-alias work.

The correspondence with Kotlin is explicit: copies/bindings must supply
the new alias name, and real mark/source/write producers must perform their
current alias transfer. This is the existing producer/alias contract, now
made an induction invariant. The proof is a fixed-point invariant, not a
claim that a method queue has already processed every alias when a call is
first visited. Fair pending producer/request/demand work supplies the witness.
Implementation tests must check this correspondence on the actual call forms.
A method may also have other effects: those use their retained effect
summaries/producers. An identity arm is not a statement that the whole
method is side-effect-free. The local proof is not a proof of the full Java
alias analysis.

## 10. Validation and status

The [audit](lean/correlated-concrete-implementation-audit.lean) checks every
owned declaration in the general and implementation modules. It permits
only the existing `propext` and `Quot.sound` axioms. Finite controls check
packet/admission/export/alias cases; theorems quantify over arbitrary paths
and atoms where stated. The [receipt](lean/correlated-concrete-implementation-checks.json)
records commands, source hashes and the selected decisions.

The local feature obligations, including the selected export and alias
contracts, are now proved relative to the existing AP/producer correspondence
contracts. The proposed implementation must pass its
adapter tests and the selected project checks after coding. No Kotlin change,
benchmark, report comparison or memory-profile cleanup was performed for this
specification-only task.
