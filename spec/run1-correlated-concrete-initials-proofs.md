# Proofs for correlated concrete initials

Date: 26 October 2026. Status: local constructive model checked; runtime is unchanged.
Read the [spec](run1-correlated-concrete-initials.md) first.

## 1. Model and scope

The [model](lean/ApSpec/Run1CorrelatedConcreteInitials.lean) imports the existing
AP `den`, geometry, mark gates, emitter and FLOW-backed handoff certificates.
It does not modify their historical definitions. `seed` is the new FULL run-1
start. `rawApply` exposes the existing geometry/mark result before the old W2
erasure. Production may use that result only in the selected owner cells.
It is not a replacement for the general AP normalizer.

Paths and marks in the theorems are arbitrary lists and natural numbers.
Witnesses contain explicit suffixes. No classical choice, `sorry` or new axiom
is used. The audit permits only `propext` and `Quot.sound`, as in the existing
AP proof project.

## 2. Seed and precision

For each admitted concrete input `x.p.s/T`, `seed_identity` constructs the
pair from that input to itself. Thus the new seed does not lose an input.
`seed_is_demand` keeps its layer. This is a conditional identity; it does not
assert that T exists on every descendant.

`new_seed_inside_old` proves inclusion in the old ANY seed. The old seed
permits an input suffix `[f]` to produce suffix `[g]`. Theorems
`old_seed_cross_suffix` and `new_seed_rejects_cross_suffix` check this pair.
The two seeds are not abstractly equivalent. The selected semantic change
removes a false suffix association.

## 3. Transfer coverage

`correlated_copy` and `copy_composes` construct the same suffix at each copy
endpoint. `trace` gives executable locations for a finite list of copy points.
`raw_copy_keeps_star` checks the actual existing geometry/mark dispatch without
the W2 erasure. No input/field/mark matcher has to change for this dispatch.
Typed readers do need to admit the new tail.

`descent_any_cover` supplies independent input/output suffixes for a read below
the tracked prefix. `descent_geometry` and `raw_descent_widens` check the
existing above-prefix result. `explicit_may_geometry` keeps an explicit may
target. `cut_any_cover` constructs the output suffix lost by a field cut.
These results justify keeping these ANY sites. They do not justify general
STAR recovery after widening.

For a below-only cleaner, a surviving root is an EXACT output.
`cleaner_root_cover` constructs that root result. The concrete cleaner must
still set the existing protection flag. The theorem is a local residual
cover, not a proof of every current typed cleaner branch.

For the remaining operations, the required witness argument is as follows:

- Full overwrite/clean: a killed location is not a surviving witness.
- Disjoint transfer/filter: the existing row and witness stay valid.
- Partial field overwrite: the existing E-free DEMAND residual contains each
  surviving suffix. Keep that suffix; do not create an exclusion.
- Fixed source/GEN target: use the existing target witness. Do not bind its
  new suffix to the input suffix.
- Selected cleaner residual: keep its existing mark and protection. Use
  EXACT for a root residual and the E-free cover for other partials.
- Finite joins: retain the row from the contributing branch, with its own
  tail and flag. Do not force a common ANY/STAR header on unlike branches.

An induction over concrete program derivations uses the identity at entry
and these local surviving-witness cases. This gives the design argument for
sound coverage. The Lean module checks the listed seed, geometry and suffix
laws. It does **not** establish the Kotlin/IR correspondence, general source/ND
closure, or all typed cleaner and field-write cases. The implementation tests
in spec section 9 are required gates. A proof of an old W2 closure is not a
proof of the extended closure.

## 4. Summary replacement

`star_specialization` proves exact pair equality for a concrete T input and
the equal-geometry FLOW instance, if FLOW admits T. Both use the same suffix.
`star_summary_application` checks equality of computed results, layers and
requests using the existing geometry and mark operations before W2 erasure.
It is stronger than output-path overlap. It does not authorize a new call
binding or a different scope.

`star_alias_class` proves equal raw identity/alias-effect classification for
these STAR FLOW and same-mark STAR TAINT shapes, for arbitrary bases and paths.

`longer_star_output` and `prefix_star_does_not_cover` give a counterexample
to the ANY prefix rule in the STAR cell. The input suffix is empty. FLOW ends
at `return.f`; the marked edge ends at `return.f.g`. Keep path equality for
STAR. The existing ANY prefix theorem remains valid in its old scope.

`protection_blocks` and `exclusion_blocks` check mandatory negative admission
gates. Existing assignment, selected-cleaner, cycle and sticky-union proofs in
`FlowBackedProtection` still apply: changing the tail does not remove a
dependency barrier. Scope, identity/effect and producer-hook checks remain
separate implementation obligations. Pair inclusion alone cannot erase them.

## 5. Statics

A static read can retain a conditional `C.f.*` original even when ZERO
activates the summary during run-1. A same-suffix reader is then the ordinary
copy case. Current call code already keeps that original or selects the
canonical marked static original. The proposal preserves this ownership.

A pool membership proves only mark availability at a region. It does not
bind two independently derived suffixes. `independent_supply_any` constructs
the general independent pair. The cross-suffix counterexample shows why a
STAR result is invalid if an adapter discards its binder. Keep ANY there.

The three-set protocol, read/write activation and universal static demand
fallback are unchanged. Their existing completeness arguments remain
applicable provided the new typed adapter preserves these memberships and
the static original. This file does not prove a new global static algorithm.

## 6. Handoff and marked demand replacement

`marked_handoff` retains T while changing the backward entry STAR to ANY.
`handoff_covers` proves equal pattern location/mark sets. `flow_handoff`
checks the corresponding abstract guide. The original initial remains the
other endpoint; the stored forward result is not rewritten during run-1.

For an unreplaced marked row, handoff therefore keeps every represented
marked location and its demand. A concrete STAR row remains DEMAND; it does
not become a normal record.

For a replaced row:

1. `star_specialization` supplies the same pair under the retained FLOW guide.
2. `flow_guide_start` checks the original emitter on an actual T input.
   The existing `prefix_guide_start` covers an input below that guide prefix.
3. `star_summary_application` supplies equal instantiated geometry and layers.
4. The existing `FlowBackedHandoff.startFromFlowGuide` and
   `publishFromFlowGuide` certificates use original emission and whole-premise
   restriction. The actual demand coverage and whole-premise gates still apply.
5. The existing protected transport replay keeps separate concrete guides at
   assignments, surviving cleaners and mark cycles. A plain removed diagonal
   row has no such barrier.

This is a relative original-AP replay argument for the selected replacement
cell. It does not assert that arbitrary FLOW geometry can replace a marked
dependency, or that an input can start a query without a demand. It does not
use StrongQueries. The prior FLOW-backed dossier retains its closure and
runtime-correspondence limits.

## 7. Audit and implementation boundary

Run the commands recorded in the [check receipt](lean/run1-correlated-concrete-initials-checks.json).
The [audit](lean/run1-correlated-concrete-initials-audit.lean) checks every
owned declaration and executes the finite controls. Historical modules are
imported; their definitions and claims are not rewritten.

The source inventory was checked against direct `Tail.ANY` sites and implicit
DEMAND defaults. It separates executable facts, transport reconstruction,
patterns and views. Implementation must also audit consumers of a new STAR
header. The local model does not prove that the listed Kotlin sites implement
the extension. No whole-engine termination, observational equivalence of the
old coarse result, memory bound or speedup is claimed.
