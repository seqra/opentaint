import Restriction

namespace NonEmptyCoverage
open NonEmptyPolicy NonEmptyRestriction

-- The common complete premise, scope, flags and support are fixed. This
-- is language inclusion for independent MAY/NE postconditions only.
def post (head : Path) (t : NonEmptyMay.Tail) (location : Path) : Prop :=
  NonEmptyMay.rooted head t location
def coversPost (a : Path) (ta : NonEmptyMay.Tail)
    (b : Path) (tb : NonEmptyMay.Tail) : Prop :=
  ∀ location, post b tb location → post a ta location

theorem selected_may_covers_nonempty (head : Path) :
    coversPost head .may head .nonEmpty := by
  intro location inside
  exact NonEmptyMay.may_covers_nonempty head location inside

theorem coverage_is_transitive (a b c : Path)
    (ta tb tc : NonEmptyMay.Tail)
    (ab : coversPost a ta b tb) (bc : coversPost b tb c tc) :
    coversPost a ta c tc := by
  intro location inside
  exact ab location (bc location inside)

theorem may_prefix_covers_nonempty_descendant (head rest : Path) :
    coversPost head .may (head ++ rest) .nonEmpty := by
  rintro location ⟨suffix,shape,_⟩
  refine ⟨rest ++ suffix,?_,True.intro⟩
  rw [shape,List.append_assoc]

theorem same_head_c2_nonempty_service_is_in_may (d : Ap) (a : Offered)
    (s : Seed) (h : s ∈ atHead {d with tail := .ne} a) :
    s ∈ atHead {d with tail := .may} a := by
  cases ht : a.ap.tail <;> simp_all [atHead,seed]

theorem star_exact_point_entry_table_is_still_equivalent (d : Ap) (a : Offered) :
    atHead {d with tail := .star} a = atHead {d with tail := .exact} a := by
  cases ht : a.ap.tail <;> simp_all [atHead,seed]

theorem old_empty_exclusion_output_keys_agree_for_new_ne_too (t : Tail) :
    intersectExit (v t) (out .star) = intersectExit (v t) (out .must) := by
  cases t <;> decide

-- Counterexample is retained: correlated STAR cannot replace the
-- independent loss of suffix correlation merely because their heads agree.
def correlated (inputSuffix outputSuffix : Path) : Prop := inputSuffix = outputSuffix
theorem correlated_star_does_not_cover_independent_may :
    NonEmptyMay.denotes .may [] ∧ ¬ correlated [1] [] := by
  exact ⟨True.intro,by simp [correlated]⟩
theorem correlated_star_does_not_cover_independent_nonempty :
    NonEmptyMay.denotes .nonEmpty [2] ∧ ¬ correlated [1] [2] := by
  exact ⟨by simp [NonEmptyMay.denotes],by simp [correlated]⟩

-- Same-coordinate retained basis is a join followed by one canonical
-- projection. Arrival order cannot change its logical memberships.
abbrev Basis := Bool × Bool
def offerMay (state : Basis) : Basis := (true,false)
def offerNe (state : Basis) : Basis := (state.1,!state.1)

theorem both_arrival_orders_keep_only_may :
    offerMay (offerNe (false,false)) = offerNe (offerMay (false,false)) ∧
    offerMay (offerNe (false,false)) = (true,false) := by decide

theorem repeated_offer_is_idempotent (state : Basis) :
    offerMay (offerMay state) = offerMay state ∧
    offerNe (offerNe state) = offerNe state := by
  rcases state with ⟨a,b⟩
  cases a <;> cases b <;> decide

-- H=false and H=true have independent bases. Offering the protected
-- provider is not a reason to remove an unprotected non-empty member.
abbrev FlagBases := Basis × Basis
def protectedMay (state : FlagBases) : FlagBases := (state.1,offerMay state.2)
theorem no_cross_protection_compaction (plain : Basis) (protectedBasis : Basis) :
    (protectedMay (plain,protectedBasis)).1 = plain := rfl

-- Per-row C2/C5 service cover is compositional. This rule requires actual
-- service inclusion, not equal diagnostic counts or a finite run cap.
def serviceCovers (provider candidate : List Ap) : Prop :=
  ∀ key ∈ candidate, key ∈ provider
theorem service_cover_is_transitive (a b c : List Ap)
    (ab : serviceCovers a b) (bc : serviceCovers b c) : serviceCovers a c := by
  intro key member
  exact ab key (bc key member)

-- ND outgoing projection preserves each member; it does not execute a
-- unary approximation. If each projected member has a retained witness,
-- the joint ledger retains all projected services of the AND origin.
def project (premises : List Ap) (conclusion : Ap) : List (Ap × Ap) :=
  premises.map fun p => (conclusion,p)
theorem nd_projection_has_a_real_member (premises : List Ap) (c : Ap)
    (entry exit : Ap) (h : (entry,exit) ∈ project premises c) :
    entry = c ∧ exit ∈ premises := by
  rcases List.mem_map.mp h with ⟨p,member,same⟩
  cases same
  exact ⟨rfl,member⟩

#print axioms selected_may_covers_nonempty
#print axioms coverage_is_transitive
#print axioms may_prefix_covers_nonempty_descendant
#print axioms same_head_c2_nonempty_service_is_in_may
#print axioms star_exact_point_entry_table_is_still_equivalent
#print axioms old_empty_exclusion_output_keys_agree_for_new_ne_too
#print axioms correlated_star_does_not_cover_independent_may
#print axioms correlated_star_does_not_cover_independent_nonempty
#print axioms both_arrival_orders_keep_only_may
#print axioms repeated_offer_is_idempotent
#print axioms no_cross_protection_compaction
#print axioms service_cover_is_transitive
#print axioms nd_projection_has_a_real_member

end NonEmptyCoverage
