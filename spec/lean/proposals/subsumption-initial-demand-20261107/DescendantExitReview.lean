import AnnotatedC5Exit

/- Review model only. This defines the proposed strict-descendant selector
delta without editing the selected C5 operator. It keeps all non-STAR cells.
The program-level need for STAR is a separate obligation. -/
namespace DescendantExitReview
open AnnotatedC5Exit

def rejectsCorrelatedAncestor (raw selector : Pattern) : Bool :=
  decide (raw.tail = .star ∧ raw.path.IsPrefix selector.path ∧
    raw.path ≠ selector.path)

def proposedMeet (forward : Bool) (raw : Fact) (selector : Pattern) : Option Fact :=
  if rejectsCorrelatedAncestor raw.toPattern selector then none
  else meetExit forward raw selector

def proposedRestrict (forward : Bool) (global : Nat) (raw : Fact)
    (selector : Pattern) : Option Fact :=
  (proposedMeet forward raw selector).map (cut (pairBudget global selector))

theorem non_STAR_cells_are_unchanged (forward : Bool) (raw : Fact) (selector : Pattern)
    (notStar : raw.tail ≠ .star) :
    proposedMeet forward raw selector = meetExit forward raw selector := by
  simp [proposedMeet,rejectsCorrelatedAncestor,notStar]

theorem MAY_cells_are_unchanged (forward : Bool) (raw : Fact) (selector : Pattern)
    (may : raw.tail = .may) :
    proposedRestrict forward 5 raw selector = restrictData forward 5 raw selector := by
  have notStar : raw.tail ≠ .star := by simp [may]
  simp [proposedRestrict,restrictData,non_STAR_cells_are_unchanged _ _ _ notStar]

theorem MUST_cells_are_unchanged (forward : Bool) (raw : Fact) (selector : Pattern)
    (must : raw.tail = .must) :
    proposedMeet forward raw selector = meetExit forward raw selector := by
  apply non_STAR_cells_are_unchanged
  simp [must]

theorem same_head_cells_are_unchanged (forward : Bool) (raw : Fact) (selector : Pattern)
    (same : raw.path = selector.path) :
    proposedMeet forward raw selector = meetExit forward raw selector := by
  simp [proposedMeet,rejectsCorrelatedAncestor,same]

theorem proposed_success_is_an_original_success (forward : Bool) (raw kept : Fact)
    (selector : Pattern) (accepted : proposedMeet forward raw selector = some kept) :
    meetExit forward raw selector = some kept := by
  unfold proposedMeet at accepted
  split at accepted
  next => cases accepted
  next => exact accepted

theorem proposed_keeps_supplied_mark_layer_H (forward : Bool) (raw kept : Fact)
    (selector : Pattern) (accepted : proposedMeet forward raw selector = some kept) :
    kept.base = raw.base ∧ kept.slot = raw.slot ∧ kept.layer = raw.layer ∧ kept.h = raw.h :=
  meet_preserves_layer_slot_H forward raw kept selector
    (proposed_success_is_an_original_success forward raw kept selector accepted)

def f : RelativeRestriction.Accessor := .field 0
def g : RelativeRestriction.Accessor := .field 1
def p (path : Path) (tail : Tail) (E : List Accessor := []) : Pattern :=
  ⟨1,path,tail,.full 7,E⟩
def a (path : Path) (tail : Tail) (layer : Layer) (E : List Accessor := []) : Fact :=
  ⟨p path tail E,layer,false⟩

theorem MAY_rebases_then_meets_EXACT :
    proposedMeet true (a [] .may .demand) (p [f] .exact) =
      some (a [f] .exact .demand) := by decide

theorem MAY_rebases_then_meets_STAR :
    proposedMeet true (a [] .may .demand) (p [f] .star) =
      some (a [f] .may .demand) := by decide

theorem MUST_rebases_then_meets_EXACT :
    proposedMeet true (a [] .must .normal) (p [f] .exact) =
      some (a [f] .exact .normal) := by decide

theorem MUST_rebases_then_meets_STAR_with_E :
    proposedMeet true (a [] .must .normal) (p [f] .star [g]) =
      some (a [f] .must .normal [g]) := by decide

theorem excluded_MUST_branch_still_rejects :
    proposedMeet true (a [] .must .normal [f]) (p [f] .may) = none := by decide

theorem EXACT_ancestor_already_rejected :
    meetExit true (a [] .exact .normal) (p [f] .may) = none ∧
    proposedMeet true (a [] .exact .normal) (p [f] .may) = none := by decide

theorem STAR_ancestor_is_the_changed_cell :
    meetExit true (a [] .star .normal) (p [f] .star) =
      some (a [] .star .normal) ∧
    proposedMeet true (a [] .star .normal) (p [f] .star) = none := by decide

def flowOutput : Fact := ⟨⟨1,[],.star,.flow [],[]⟩,.normal,false⟩
def deeperFlowSelector : Pattern := ⟨1,[f],.star,.flow [],[]⟩

theorem NORMAL_FLOW_has_a_requested_descendant_witness :
    represents flowOutput.toPattern 1 7 [f] ∧
    represents deeperFlowSelector 1 7 [f] := by
  constructor
  · refine ⟨rfl,?_,[f],rfl,?_⟩
    · simp [flowOutput,slotAdmits]
    · simp [flowOutput,geometry,allows,admits]
  · refine ⟨rfl,?_,[],rfl,?_⟩
    · simp [deeperFlowSelector,slotAdmits]
    · simp [deeperFlowSelector,geometry,allows,admits]

theorem NORMAL_FLOW_descendant_is_rejected_only_by_proposal :
    restrictData true 2 flowOutput deeperFlowSelector = some flowOutput ∧
    proposedRestrict true 2 flowOutput deeperFlowSelector = none := by decide

end DescendantExitReview
