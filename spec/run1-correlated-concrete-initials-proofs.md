# Proofs for correlated concrete initials and general FLOW subsumption

Date: 26 October 2026. Status: local constructive model checked; runtime is unchanged.
Read the [spec](run1-correlated-concrete-initials.md) first.

## 1. Model and scope

The [model](lean/ApSpec/Run1CorrelatedConcreteInitials.lean) retains its file
and namespace names for existing links. Its general operations have no run,
direction or mark-mode parameter. A numeric mark denotes the current runtime
atom, FULL or GROUP. The proofs do not enumerate a group's full members.

The model imports the existing AP pair denotation, geometry, mark gates,
emitter and FLOW-backed handoff certificates. Historical operations and
claims are unchanged. `selectedStart` is the general concrete STAR start.
`rawApply` exposes the current geometry/mark result before historical W2
erasure. The producer must still establish the bound-suffix invariant.
No proof turns an independent ANY value into a correlated STAR value.

Paths, marks, exclusions and summary layers are parameters. Witnesses contain
explicit suffixes. There is no classical choice, `sorry` or new axiom. The
audit permits only `propext` and `Quot.sound`, as in the existing AP project.
Availability in all runs does not imply that every initial/output shape has
a well-formed FLOW counterpart or that every runtime adapter is proved.

## 2. General seed and precision

`start_keeps_star_exclusion` checks that the selected concrete STAR initial
starts with exactly that STAR and E, in DEMAND. `excluded_seed_identity`
constructs the identity pair for every suffix admitted by E. No run or FULL
condition is needed. The mark is supplied by the input; the seed is not a
source or proof of must-taint.

`selected_seed_inside_old` proves inclusion in the old seed with arbitrary E.

The earlier `seed` is the Empty-E specialization. `seed_identity` and
`seed_is_demand` check its identity and layer. `new_seed_inside_old` proves
inclusion in the old ANY seed. `old_seed_cross_suffix` admits input suffix
[f] and output suffix [g]; `new_seed_rejects_cross_suffix` rejects that pair.
The seed change is a strict precision change, not equality of coarse results.
The controls also check that ANY and EXACT start rows stay unchanged.

Ordinary validation still restricts which initials a run can select. Run-1
requires Empty E and its bounded path grammar. Later runs retain their
ordinary paths and exclusions. A theorem about arbitrary E does not authorize
an initial forbidden by that grammar.

## 3. Transfer coverage

`correlated_copy` and `copy_composes` construct the same suffix at each copy
endpoint. `trace` gives executable locations for a finite copy sequence.
`raw_copy_keeps_star` checks the existing dispatch without W2 erasure.

`descent_any_cover` constructs independent suffixes for a read below the
tracked prefix. `descent_geometry` and `raw_descent_widens` check the current
above-prefix result. `explicit_may_geometry` keeps an explicit may target.
`cut_any_cover` constructs the output suffix lost by a field cut. These
laws justify retaining the necessary ANY sites in either direction.

For a below-only cleaner at the tracked root, `cleaner_root_cover` constructs
an EXACT root residual. The current selected-cleaner protection must remain.
This is a local residual cover, not a proof of every typed cleaner branch.

The remaining witness argument preserves the current transfer contracts:

- Full overwrite/clean: a killed location is not a surviving witness.
- Disjoint transfer/filter: retain the current row and witness.
- Run-1 partial overwrite: its existing E-free D residual contains each
  surviving suffix. Keep the suffix; do not create an exclusion.
- Later strong field transfer: preserve the existing admitted/excluded
  suffix test. Do not import the run-1 E-free cover into that run.
- Source/GEN/ND fixed target: use its existing target witness. Do not bind
  a generated output suffix to the input suffix.
- Partial cleaner: use the current spatial residual and E policy; retain
  protection on a selected-mark survivor.
- Finite join: retain the contributing row's tail and OR its protection.
  Do not merge unlike tail headers into a common STAR header.

These cases give the design's induction over surviving concrete witnesses.
The Lean module checks the stated local laws. It does **not** prove all
Kotlin/IR transfers, typed cleaners, rule/ND closure, or general solver
termination. The implementation gates in spec section 9 remain required.
Historical W2 and backward no-concrete-STAR proofs do not prove the new grammar.

## 4. General summary replacement

`general_specialization` proves pair equality after mark specialization for
arbitrary equal initial/output kinds and paths, if FLOW admits T. It includes
nonempty STAR exclusions and an ANY initial. Runtime eligibility separately
requires representable, well-formed FLOW shapes. The conceptual theorem does
not permit abstract-mark EXACT or must facts.

`star_exclusion_cover` proves STAR coverage when the FLOW output excludes no
more suffixes than the TAINT output. It uses the executable `Excl.subB` test
and the existing `CoreAux.Excl.subB_sound` theorem. Initial geometry, including
E, is equal. The output paths are equal. The input and output suffix witnesses
are unchanged.

`any_prefix_cover_general` proves ANY prefix coverage for arbitrary equal
initial geometry. The constructed FLOW output suffix is `extra ++ suffix`.
No run-1, Empty-E or FULL premise is used.

`general_summary_application` proves equal computed outputs, requests and
layers for equal-shaped summaries on an actual T input, with arbitrary
initial/output kinds. It uses the existing geometry and mark operations
before W2 erasure. Prefix-only or weaker-exclusion coverage is inclusion,
not equality of every computed output; original restriction still applies.

`star_reverse` constructs the reversed same-suffix pair and swaps the initial
and output exclusions. Thus correlation and specialization are not
forward-only properties. The store still compares one direction/view at a
time. Correct construction of the typed reverse view is an adapter obligation.

`layer_composition` proves that sufficient layer strength survives the ordinary
OR with an incoming layer. A marked NORMAL row requires NORMAL FLOW. A marked
DEMAND row can use NORMAL or DEMAND FLOW. No proof promotes a marked layer.
The concrete seed continues to use its current DEMAND policy.

`star_alias_class` records equal raw identity/effect classification for
STAR FLOW and same-mark STAR TAINT. It is a diagnostic law, not a premise
of subsumption. `sameAliasEffectClass` is removed from admission.
`longer_star_output` and `prefix_star_does_not_cover` reject the ANY prefix
rule for STAR. Input suffix [] ends at different output locations.

`protection_blocks` and `exclusion_blocks` check mandatory negative gates.
The existing assignment, cleaner, local/call-cycle and sticky-merge contracts
must now hold in every enabled run and mark domain. The original protection
model is independent of run number. Enabling its corresponding runtime hooks
and preserving masks through native/reversed record views are new explicit
implementation obligations. Missing metadata is not proof of an unprotected
row. Unsupported cells keep the marked residual.

`remove_covered_relation` proves that removing E from the union of F and E
preserves every represented pair when E is covered by F. It has no identity
or alias-class premise. `remove_covered_star` and `remove_covered_any` apply
that theorem to the selected STAR/E and ANY-prefix cells.

The explicit owner/initial test in spec section 5.1 states the scope in which
these relations are compared. It is not a new producer, key or caller store.
The concrete initial and unrestricted FLOW initial have equal base, path,
tail and E; collection ownership establishes the method/run/view boundary.

The old alias-class guard and the same-base ANY identity exception no longer
limit those theorems. The original counterexample to classification equality
remains valid, but classification equality is no longer a contract of relation
replacement. This selects a change in auxiliary alias work.

`later_alias_layer_distinction` checks the existing later-run DEMAND bypass:
a normal identity skips aliases, while a demand identity enables them.
Thus the pair-union proof does not imply identical alias callback/candidate
sets. The JVM plan has separate direct BIND_BACK and alias arms; the direct arm
remains. The [implementation proof module](lean/ApSpec/CorrelatedConcreteImplementation.lean)
now establishes positive input alias closure under the existing definition,
mark-producer and cleaning contracts. It proves that identity-only alias
consequences are already covered, and that other enabled alias steps retain
coverage. This does not assume equality of false may-alias candidates.
Kotlin/IR correspondence with the producer contracts remains an implementation
gate. No replacement guard is inferred from that proof boundary.

## 5. Statics

During run-1, ZERO can activate a reader while the procedure retains or
selects a conditional static original. A same-suffix reader is then the
ordinary copy case. Later runs require the actual static premise. General
subsumption does not change this distinction.

Pool membership proves mark availability, not equality of independent
writer/reader suffixes. `independent_supply_any` supplies the independent
pair. The cross-suffix counterexample rejects STAR when the binder is lost.
A raw pool materializer must select ANY explicitly. A typed encoder no
longer performs that semantic erasure from mark kind alone. Once the current
procedure selects its canonical STAR initial, the general identity seed applies.

The three-set protocol, read/write activation, S-S erasure and static demand
fallback are unchanged. Their existing arguments require the new adapters
to preserve those memberships and the selected original. No new global static
algorithm is proved or selected here.

## 6. Handoff, records and demand replacement

`marked_handoff` retains T while converting the Empty-E STAR conclusion to
an ANY backward entry pattern. `handoff_covers` proves equal pattern sets
for Empty E. `handoff_exclusion_cover` proves inclusion for arbitrary E;
there is no equality claim when forward-to-backward handoff drops nonempty E.
`flow_handoff` checks the corresponding abstract entry. The original endpoint
keeps its normal handoff shape and exclusion. Backward-to-forward keeps its
existing construction; no extra STAR erasure is selected for that direction.

For a retained marked row, the direction's ordinary handoff keeps its
witness demand. For a replaced row:

1. `general_specialization`, `star_exclusion_cover`, or
   `any_prefix_cover_general` supplies the covered pair in retained FLOW.
2. `flow_guide_start` checks the original emitter on an actual T input;
   the existing `prefix_guide_start` handles a descendant input.
3. `general_summary_application` supplies equal equal-shape instantiation;
   inclusion cells retain the requested pair by ordinary restriction.
4. Existing `FlowBackedHandoff.startFromFlowGuide` and
   `publishFromFlowGuide` certificates use original emission and whole-premise
   restriction. Their coverage and whole-premise gates still apply.
5. Protection keeps concrete guides at dependency barriers. It must be
   computed and transported on the actual current derivation in every run.

A removed NORMAL marked row needs a retained NORMAL FLOW row, eligible for
persistence under the same native record rules. A D row can use retained
FLOW demand or a normal record. Native and reversed views must retain their
actual direction, tails, exclusions, layers and protection. Do not treat a
record with an unverified/missing annotation adapter as a removable barrier.
No persistence eligibility is granted by the new STAR tail.

The user selected persistence of NORMAL FLOW records with nonempty E.
The implementation model's `normal_covered_flow_has_record` uses C0 and the
STAR/ANY start table to prove that every NORMAL covering FLOW is eligible
under the revised abstract STAR/E record rule. `native_star_view_exact`
proves reversal while retaining Ei union Eo. The old native-validator
counterexample remains a regression control, not the selected behavior.
The driver persists before handoff, so D FLOW demand or a native/reversed
NORMAL FLOW record supplies the export witness in both directions.

This is a relative original-AP replay argument. It does not prove arbitrary
multi-run Kotlin closure, a new query permission, or equality of old coarse
candidate counts. StrongQueries is not used. Each query still needs its
ordinary demand and whole-premise restriction.

## 7. Audit and implementation boundary

Run the commands in the [receipt](lean/run1-correlated-concrete-initials-checks.json).
The [audit](lean/run1-correlated-concrete-initials-audit.lean) checks every
owned declaration and executes finite controls. Historical modules remain
unchanged. The general laws extend their stated local cells; they do not
retroactively expand their old closure claims.

The source inventory separates executable facts, reconstruction, patterns
and read views. The revised spec also identifies phase-gated summary and
protection owners which implementation must update. No analyzer source is
changed. No whole-engine termination, memory bound or speedup is claimed.
