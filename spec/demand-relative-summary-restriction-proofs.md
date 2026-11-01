# Demand-relative restriction: proofs and limits

Date: 1 November 2026. This dossier supports the
[specification](demand-relative-summary-restriction.md).
The implementation is unchanged. Follow [proof-guide.md](proof-guide.md).

## 1. Checked claim

The selected gate is exact paired restriction, followed by the existing
field cut at `min(runLimit, FL(Dp)+1)`. A local sound abstraction of every
selected candidate survives. All new semantic summary state comes from
that gate, including NORMAL state. No raw NORMAL persistence exemption is
used in the model.

The local cut can lose correlation and definite information. Thus this
is not an equality proof for the old publication stream. Overflow moves
to DEMAND; it cannot prove a NORMAL report. The specification marks this
as a major semantic change.

The [checker](lean/proposals/demand-relative-summary-restriction-20261101/check.py)
builds all eight modules in Lean 4.33.1. It audits every explicit public
theorem, definition, and abbreviation. It rejects unproved declarations,
classical choice, and noncomputable implementations. The generated
[receipt](lean/proposals/demand-relative-summary-restriction-20261101/checks.json)
contains source hashes, the exact inventory, and command results. The
current check passes 162 theorems and 274 audited declarations.

## 2. Model map

| Module | Constructive result | Limit |
|---|---|---|
| [Geometry](lean/proposals/demand-relative-summary-restriction-20261101/Geometry.lean) | Executable counted-prefix cut; positive paired budget; prefix coverage, bounds, unchanged in-budget result, retained mark/protection, no D-to-N | Scalar candidate locations; MUST is not interpreted as universal evidence |
| [Restriction](lean/proposals/demand-relative-summary-restriction-20261101/Restriction.lean) | Executable concrete empty-E C2 image and C5 table; one row supplies entry, exit, and budget; output depth; executable selected witness | Nonzero FULL scalar DATA; JVM initial-shape adapter remains separate |
| [Annotations](lean/proposals/demand-relative-summary-restriction-20261101/Annotations.lean) | FLOW/concrete slot meaning, preserved mark exclusions, field-exclusion widening, finite packed-leaf candidate coverage | Does not replace correlated FLOW application, MUST, or subsumption proofs |
| [Admission](lean/proposals/demand-relative-summary-restriction-20261101/Admission.lean) | Operational restrict-before-insert store; provenance, rejection identity, output deduplication, pending/native/index/provider views | Exact annotated membership reference; no optimized tree merge or provider-geometry proof |
| [Controls](lean/proposals/demand-relative-summary-restriction-20261101/Controls.lean) | Typed ZERO/Target, complete control pairs, NORMAL Target policy, full AP handoff selector, early-stop counterexample | AP meet is a parameter in this control model |
| [Integration](lean/proposals/demand-relative-summary-restriction-20261101/Integration.lean) | Actual scalar C5/cut feeds the admission store; NORMAL-to-DEMAND publication/frontier, rejected NORMAL, admitted NORMAL persistence | Connects the scalar core; does not verify Kotlin or arbitrary whole-program findings |
| [Progress](lean/proposals/demand-relative-summary-restriction-20261101/Progress.lean) | Finite depth recurrence, two-field wrap boundary witness, 16-to-1 output compression | Needs available compatible derivations; not a driver-termination proof |
| [SourceProgress](lean/proposals/demand-relative-summary-restriction-20261101/SourceProgress.lean) | Real matching reverse source action restores permission; next precise admitted source result can report/persist without raw cache | Finite source boundary trace with supplied ZERO route and first source permission |

These modules share the concrete geometry where needed. In particular,
Integration uses the executable restriction operation from Restriction,
not a separately assumed list of desired results. Demand-row IDs are
removed before semantic summary equality.

## 3. Cut proof

For each finite path, `clip` keeps uncounted class accessors and consumes
one budget unit for each named field or array element. It stops at the
first counted accessor that does not fit. Structural induction constructs
a suffix witness that the result is a prefix of the original path.

`clip_depth_le` proves the bound. `clip_identity` proves no change if the
path already fits. `limit_possible_coverage` then constructs a containing
MAY prefix for every selected location. The base and mark are unchanged.
The overflow branch is DEMAND. Therefore, any NORMAL result of this cut
is the unchanged selected result.

The annotations model supplies the additional mark and exclusion laws:

```text
cut_keeps_every_selected_location_and_mark
excluded_mark_is_still_excluded_after_cut
different_concrete_mark_is_not_invented
packed_cut_preserves_all_candidate_memberships
normal_admitted_annotated_result_was_not_cut
```

A FLOW slot denotes all full marks except its `mx` set. The slot remains
identical through a cut. Empty field exclusion on overflow admits all
previously admitted suffixes; it cannot remove a selected location.
Packed candidate coverage has an executable leaf witness, then a mapped
cut-leaf witness. Tree sharing and exact protection-union representation
are runtime adapter obligations; the reference does not enumerate mark
members to implement a FLOW slot.

These are possible-location results. They do not turn a MUST assertion
into a universal MAY assertion on NORMAL. Loss of that stronger meaning
is on DEMAND. Uncut correlated FLOW keeps its existing meaning.

## 4. C2 and complete paired C5

`entry_image_depth_step` proves that a scalar initial accepted by the
modeled C2 image has at most one counted field beyond Dc. The same-prefix
cells have equal depth. The first-new-field cell has exactly one new
counted accessor; preceding class accessors cost zero.

The concrete empty-E exit table models equal, descendant, ancestor, and
disjoint chains. EXACT rejects a strict descendant. An ancestor STAR is
kept whole; ancestor MAY/MUST can rebase under the existing table. No C5
branch changes the selected layer.

`selectedWitness` inspects the actual Option result. It returns an
executable witness for the exact C5 result and the limit that produced
the admitted result. No existence proof uses choice.

```text
existing_c5_requires_this_entry
existing_c5_uses_this_exit
exact_restrict_then_cap
restriction_global_depth
restriction_exit_depth_step
restriction_never_promotes_demand
restriction_covers_selected_locations
every_output_has_one_complete_row
```

The crossed-row negative control gives one row a compatible entry only
and another a compatible exit only. The result is empty. This tests the
error that independent entry and exit selection would introduce.

For normalized FLOW initials, use the existing C2 preimage rule. Containment
is checked on that preimage. The scalar model does not assert that a
stored normalized STAR key itself passes an EXACT-preimage containment
test. The
[exact-DEMAND package](lean/proposals/demand-layer-exact-initials-20261031/README.md)
retains its own selected C2 scope; no C2 behavior is changed here.

## 5. Union and early stopping

The reference visits every complete matching row and unions its final
result. The control model proves both directions of per-row membership:
each result has a complete row witness, and each accepted row result is
in the union.

An executable counterexample retains a deep exact NORMAL leaf from the
first row and adds a shorter MAY/DEMAND prefix from the second row. Thus
raw coverage after the first row is insufficient. Integration checks
both row orders against actual C5/cut and storage. Exact list order is
not a semantic observation; the membership set is the same.

The reference removes the unsafe shortcut. A future optimized search
must prove saturation of final capped results, including layer and
protection. No new normal-over-demand dominance rule is assumed.

## 6. Admission, persistence, and replacement order

The executable store has only admitted rows and pending publications.
`offer` computes restriction before it calls insertion. A rejected offer
returns the same state. Equal final annotated memberships do not add
another publication. A finite operational trace gives every retained
membership a restriction witness.

```text
rejected_changes_no_state
reachable_rows_have_gate_provenance
reachable_pending_has_gate_witness
reachable_native_has_gate_witness
reachable_index_has_gate_witness
reachable_row_has_executable_receipt
```

`source?` searches the finite external proof trace and returns the actual
candidate that admitted the row. This trace is proof evidence. It is not
an analyzer raw-candidate storage requirement.

Integration removes the generic-gap risk. It calls `admitRows` from the
actual scalar restriction model and stores its semantic results:

```text
every_stored_row_has_concrete_gate_witness
native_row_has_concrete_gate_witness
normal_provider_has_concrete_gate_witness
Controls.actual_cut_store_and_publication_contain_only_admitted_result
Controls.actual_cut_enters_frontier_and_has_no_normal_native
Controls.rejected_normal_leaves_all_semantic_state_unchanged
Controls.within_normal_is_persisted_from_actual_gate
```

Admission's `providers` view models **NORMAL providers only**. A raw NORMAL
FLOW rejected by the gate cannot act as a provider. One cut to DEMAND
cannot act as a NORMAL provider. This does not ban the existing admitted
DEMAND-FLOW-to-DEMAND-concrete replacement cell. Its coverage and
protection laws stay unchanged. Ordinary method-point storage does not
destructively remove concrete memberships before this gate.

The store reference treats semantic annotations as part of its exact
membership. Existing packed equality can omit protection only with its
existing monotone annotation merge. This proof does not authorize a new
data-class field, equality change, or loss of a protection upgrade.

## 7. Handoff and typed controls

Admission's `frontier` and Integration's frontier controls prove the
ordinary final-DEMAND case. They are not the entire handoff selector.
Controls separately preserves the existing NORMAL ND and NORMAL
backward-ZERO AP guidance cases. Each case is evaluated on admitted
results. There is no raw-layer classification step and no new per-edge
save operation.

The typed model assigns no AP budget to ZERO or Target. A ZERO original
with a DATA exit still receives that exit's cap. ZERO exit accepts Reach,
not DATA. DemandTarget requires one complete paired permission. It does
not manufacture a ZERO propagation event.

NormalTarget uses its existing forward report lane. It requires NORMAL
support, preserves its ID, is ignored backward, and is not re-emitted if
the owned relation is already retained. The changed AP gate does not
silently introduce a new terminal C5 policy. A cut AP result is DEMAND
and cannot supply NORMAL terminal composition.

## 8. Progress and work witnesses

The finite arithmetic recurrence advances one counted field until it
reaches a supplied finite target. It constructs that endpoint after a
finite number of steps. This is conditional on compatible derivations
remaining available. It does not prove that every real alternating run
supplies the required inputs.

The wrap witness uses a root current premise, a two-field body result,
and a preceding opposite initial with one field. A fixed current-premise
cap loses the second field again. The new Dp-relative cap retains both
fields on NORMAL. No uncut native record supplies them.

SourceProgress gives a separate finite permission trace. Its inputs
include an admitted ZERO control route and permission for the first
source action. The declared source output is `ret.a.b.c.$/T`, and the
first restricted result is `ret.a.[any]/T`, DEMAND, with no native record.
The exact sink offer makes unchanged C2 expose `ret.a.b.*/T`, DEMAND. A
matching actual reverse source action records ID 42. Its new forward
exit guide has depth 2; the new budget 3 retains the precise NORMAL
source result. Wrong mark and unrelated-field controls cannot create
the hit. Permission alone cannot bypass a mismatching DATA exit.

This is not a proof that all source rules or all call contexts recover
every future source permission. In particular, the model does not derive
the whole ZERO/Target route or the scheduler from the Java snippet. Those
contracts and their runtime integration must be checked together.

The finite output family contains 16 distinct depth-3 leaves under one
field. The cut yields one protected, marked DEMAND prefix. This proves a
practical output-membership reduction, not a measured speedup. A separate
counter-control retains the exponential inverse-loop body family. A
publication gate cannot remove work performed before publication.

## 9. Reused contracts and remaining validation

The new theory does not redefine or prove all instruction transfers,
alias closure, FLOW-backed replacement, native reversal, static
completion, rule specialization, or Target reporting. These are explicit
reused contracts. The reviewed source hashes bind the correspondence
review, not a proof of Kotlin implementation correctness.

Implementation must show that packed operations refine this reference,
especially for mixed kept/cut leaves, mark sets, nonempty field and mark
exclusions, static anchors, all ND members, and protection upgrades.
It must connect the actual gate to persistence, final-layer demand
selection, source callbacks, saved replay, and the completed barrier.
The acceptance cases are listed in section 11 of the specification.

The old raw-NORMAL persistence control describes the old runtime. It is
not evidence for this selected design. Do not use a raw cache to make a
new test pass. No new source-permission route is selected by these proofs.

No project was run with this mechanism. The unchanged campaign's latest
reached/completed/accepted iterations remain: Stirling-PDF **run-8/7/7**,
conductor **run-4/3/3**, thingsboard **run-2/1/1**, and OWASP **run-5/5/5**.
General convergence, whole-analyzer finding equivalence, and project
performance improvement are **not established** by this design package.
