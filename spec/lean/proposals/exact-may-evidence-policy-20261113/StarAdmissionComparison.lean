import Std

namespace StarAdmissionComparison

abbrev Path := List Nat
inductive Tail where | exact | star | may
  deriving DecidableEq, Repr

-- The current scalar code already changes a same-head MAY admission to
-- STAR. The selected change additionally gives STAR the MAY admission
-- capabilities at a deeper demand head (subject to native E guards).
def currentDeeperMayAdmission (actual : Tail) : Option Tail :=
  match actual with | .may => some .star | _ => none
def proposedDeeperMayAdmission (actual : Tail) : Option Tail :=
  match actual with | .star | .may => some .star | _ => none

theorem new_nested_star_admission :
    currentDeeperMayAdmission .star = none ∧
    proposedDeeperMayAdmission .star = some .star := by decide

theorem existing_may_admission_unchanged :
    currentDeeperMayAdmission .may = proposedDeeperMayAdmission .may := rfl

-- Isolate the native loss event in `return x.f.g` with input x.f.*.
-- The missing read suffix g destroys correlation. Renaming a START is
-- not a change to this ordinary transfer rule.
def readDeeper (tail : Tail) : Option (Tail × Bool) :=
  match tail with
  | .exact => none
  | .star | .may => some (.may,true)

theorem a_star_start_still_can_lose_correlation :
    readDeeper .star = some (.may,true) := rfl

-- The user's subsumption keeps the conclusion tail distinction. The
-- STAR -> MAY row above is therefore not a candidate for deletion by
-- STAR -> STAR, so its existence is not a gap in that selected rule.
def sameOutputTail (provider candidate : Tail) : Bool := provider == candidate
theorem genuine_may_loss_is_not_selected_for_star_subsumption :
    sameOutputTail .star .may = false := by decide

-- The empty-binding certificate filters a singleton EXACT payload.
-- A broad STAR can still bind a nonempty suffix. Without another
-- certificate, rejecting its whole region would discard those bindings.
def emptyBindingGate (mayEmpty : Bool) (actual : Tail) : Bool :=
  mayEmpty || actual != .exact
theorem nonempty_cut_does_not_remove_broad_star :
    emptyBindingGate false .exact = false ∧
    emptyBindingGate false .star = true ∧
    emptyBindingGate false .may = true := by decide

theorem extra_star_admission_survives_empty_only_evidence :
    proposedDeeperMayAdmission .star = some .star ∧
    emptyBindingGate false .star = true := by decide

-- For S: x.f.* -> ret.*, a concrete input x.f.<suffix> must keep
-- that suffix. For R: x.f.* -> ret.[any], it can be forgotten.
-- Model the output languages directly; paths are relative to ret.
def normalOutput (suffix output : Path) : Prop := output = suffix
def demandOutput (_suffix _output : Path) : Prop := True

theorem star_premises_do_not_prove_relation_inclusion :
    demandOutput [2] [] ∧ ¬ normalOutput [2] [] := by
  exact ⟨True.intro, by change ([] : Path) ≠ [2]; decide⟩

-- Actual ordinary code: if (b) return x.f; else return x.f.g.
-- On marked x.f.g, the first result is ret.g, the second is ret.
def codeOnFG : List Path := [[2],[]]
theorem the_other_branch_is_an_actual_transfer :
    [] ∈ codeOnFG ∧ ¬ normalOutput [2] [] := by
  change ([] : Path) ∈ [[2],[]] ∧ ([] : Path) ≠ [2]
  decide

-- Applying S on an admitted same-head STAR instead of the original
-- precise input is a different application service. A free suffix can
-- cover every output at ret, but this lemma proves only that local fact
-- language coverage, not a correlated caller summary or future handoff.
def admittedStarOutput (output : Path) : Prop := ∃ suffix : Path, output = suffix
theorem admitted_view_covers_local_output (output : Path) : admittedStarOutput output :=
  ⟨output,rfl⟩
theorem admitted_view_is_not_original_precise_application :
    admittedStarOutput [] ∧ ¬ normalOutput [2] [] :=
  ⟨admitted_view_covers_local_output [],by change ([] : Path) ≠ [2]; decide⟩

#print axioms new_nested_star_admission
#print axioms existing_may_admission_unchanged
#print axioms a_star_start_still_can_lose_correlation
#print axioms genuine_may_loss_is_not_selected_for_star_subsumption
#print axioms nonempty_cut_does_not_remove_broad_star
#print axioms extra_star_admission_survives_empty_only_evidence
#print axioms star_premises_do_not_prove_relation_inclusion
#print axioms the_other_branch_is_an_actual_transfer
#print axioms admitted_view_covers_local_output
#print axioms admitted_view_is_not_original_precise_application

end StarAdmissionComparison
