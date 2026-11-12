import Std

/-! A negative eligibility component only. It does not prove C5 admission,
publication, demand ancestry, or future permission preservation. Native FLOW
geometry coverage is the arbitrary Boolean parameter `geometryCovered`.
All original owner/port/path/header/layer coordinates are opaque and retained.
No rule, storage, protection or handoff behavior is changed. -/
namespace MarkedRuleGuidance

inductive Origin where
  | zero
  | flow
  | single (mark : Nat)
  | nd (marks : List Nat)
  deriving DecidableEq, Repr

structure Coordinate where
  mark : Nat
  isProtected : Bool
  anyMask : Bool
  eligibleHeader : Bool
  fullOtherCoordinates : Nat
  deriving DecidableEq, Repr

def diagonal (origin : Origin) (c : Coordinate) : Bool :=
  match origin with
  | .single mark => c.mark == mark
  | _ => false

def removeByFlow (origin : Origin) (c : Coordinate)
    (eligiblePremise geometryCovered : Bool) : Option Coordinate :=
  if eligiblePremise && c.eligibleHeader && c.anyMask &&
      !c.isProtected && diagonal origin c && geometryCovered then none else some c

theorem cross_mark_retained (input : Nat) (c : Coordinate)
    (different : c.mark ≠ input) (premise geometry : Bool) :
    removeByFlow (.single input) c premise geometry = some c := by
  simp [removeByFlow, diagonal, different]

theorem protected_retained (origin : Origin) (c : Coordinate)
    (h : c.isProtected = true) (premise geometry : Bool) :
    removeByFlow origin c premise geometry = some c := by
  simp [removeByFlow, h]

theorem exact_mask_retained (origin : Origin) (c : Coordinate)
    (h : c.anyMask = false) (premise geometry : Bool) :
    removeByFlow origin c premise geometry = some c := by
  simp [removeByFlow, h]

theorem unsupported_header_retained (origin : Origin) (c : Coordinate)
    (h : c.eligibleHeader = false) (premise geometry : Bool) :
    removeByFlow origin c premise geometry = some c := by
  simp [removeByFlow, h]

theorem zero_original_retained (c : Coordinate) (premise geometry : Bool) :
    removeByFlow .zero c premise geometry = some c := by
  simp [removeByFlow, diagonal]

theorem flow_original_not_a_concrete_diagonal (c : Coordinate) (premise geometry : Bool) :
    removeByFlow .flow c premise geometry = some c := by
  simp [removeByFlow, diagonal]

theorem nd_original_retained (marks : List Nat) (c : Coordinate) (premise geometry : Bool) :
    removeByFlow (.nd marks) c premise geometry = some c := by
  simp [removeByFlow, diagonal]

theorem failed_premise_gate_retained (origin : Origin) (c : Coordinate) (geometry : Bool) :
    removeByFlow origin c false geometry = some c := by
  simp [removeByFlow]

theorem failed_geometry_gate_retained (origin : Origin) (c : Coordinate) (premise : Bool) :
    removeByFlow origin c premise false = some c := by
  simp [removeByFlow]

theorem retained_coordinate_is_literal (origin : Origin) (c result : Coordinate)
    (premise geometry : Bool)
    (h : removeByFlow origin c premise geometry = some result) : result = c := by
  unfold removeByFlow at h
  split at h
  · contradiction
  · exact (Option.some.inj h).symm

/- Unary selected assignment uses the triggering conclusion mark. Its second
   branch restores the original mark after a different current mark. This is
   the native same-mark/cycle formula, not a new protection label. -/
def assignmentProtection (original triggering assigned : Nat) : Bool :=
  Nat.beq triggering assigned || (Nat.beq original assigned && !(Nat.beq triggering assigned))

theorem assignment_back_to_original_is_protected (original triggering : Nat) :
    assignmentProtection original triggering original = true := by
  cases h : (Nat.beq triggering original) <;>
    simp only [assignmentProtection, Nat.beq_refl, h, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_or, Bool.true_or]

theorem same_trigger_assignment_is_protected (original triggering : Nat) :
    assignmentProtection original triggering triggering = true := by
  simp only [assignmentProtection, Nat.beq_refl, Bool.true_or]

def assignedCoordinate (original triggering assigned : Nat)
    (inherited anyMask header : Bool) (fullCoordinates : Nat) : Coordinate :=
  ⟨assigned, inherited || assignmentProtection original triggering assigned,
    anyMask, header, fullCoordinates⟩

theorem every_unary_assignment_survives_flow_replacement
    (original triggering assigned : Nat) (inherited anyMask header premise geometry : Bool)
    (fullCoordinates : Nat) :
    removeByFlow (.single original)
      (assignedCoordinate original triggering assigned inherited anyMask header fullCoordinates)
      premise geometry =
    some (assignedCoordinate original triggering assigned inherited anyMask header fullCoordinates) := by
  by_cases same : assigned = original
  · subst assigned
    apply protected_retained
    simp [assignedCoordinate, assignment_back_to_original_is_protected]
  · apply cross_mark_retained
    exact same

theorem selected_survivor_survives_flow_replacement (original mark : Nat)
    (anyMask header premise geometry : Bool) (fullCoordinates : Nat) :
    removeByFlow (.single original) ⟨mark, true, anyMask, header, fullCoordinates⟩
      premise geometry = some ⟨mark, true, anyMask, header, fullCoordinates⟩ := by
  exact protected_retained _ _ rfl _ _

/- A plain pass preserves its mark and existing flag. This model does not
   authorize a pass to create a protection membership. -/
def pass (c : Coordinate) (nextCoordinates : Nat) : Coordinate :=
  { c with fullOtherCoordinates := nextCoordinates }

theorem pass_preserves_mark_and_flag (c : Coordinate) (nextCoordinates : Nat) :
    (pass c nextCoordinates).mark = c.mark ∧
      (pass c nextCoordinates).isProtected = c.isProtected := by exact ⟨rfl, rfl⟩

theorem pass_does_not_protect_plain (c : Coordinate) (h : c.isProtected = false)
    (nextCoordinates : Nat) : (pass c nextCoordinates).isProtected = false := h

theorem cycle_restoration_protected (original other : Nat) :
    assignmentProtection original other original = true :=
  assignment_back_to_original_is_protected original other

/- Recompaction may test several providers in any order. Negative eligibility
   remains valid for every provider, not only the first arrival. -/
def compact (origin : Origin) (premise : Bool) (c : Coordinate) : List Bool → Option Coordinate
  | [] => some c
  | covered :: rest =>
      match removeByFlow origin c premise covered with
      | none => none
      | some kept => compact origin premise kept rest

theorem cross_mark_survives_every_provider (input : Nat) (c : Coordinate)
    (different : c.mark ≠ input) (premise : Bool) (providers : List Bool) :
    compact (.single input) premise c providers = some c := by
  induction providers with
  | nil => rfl
  | cons head tail ih =>
      simp only [compact, cross_mark_retained input c different premise head]
      exact ih

theorem protected_survives_every_provider (origin : Origin) (c : Coordinate)
    (h : c.isProtected = true) (premise : Bool) (providers : List Bool) :
    compact origin premise c providers = some c := by
  induction providers with
  | nil => rfl
  | cons head tail ih =>
      simp only [compact, protected_retained origin c h premise head]
      exact ih

theorem a_plain_same_mark_can_be_removed :
    removeByFlow (.single 7) ⟨7, false, true, true, 19⟩ true true = none := by decide

theorem cross_mark_negative_control :
    removeByFlow (.single 7) ⟨8, false, true, true, 19⟩ true true =
      some ⟨8, false, true, true, 19⟩ := by decide

#print axioms cross_mark_retained
#print axioms protected_retained
#print axioms exact_mask_retained
#print axioms unsupported_header_retained
#print axioms zero_original_retained
#print axioms flow_original_not_a_concrete_diagonal
#print axioms nd_original_retained
#print axioms failed_premise_gate_retained
#print axioms failed_geometry_gate_retained
#print axioms retained_coordinate_is_literal
#print axioms assignment_back_to_original_is_protected
#print axioms same_trigger_assignment_is_protected
#print axioms every_unary_assignment_survives_flow_replacement
#print axioms selected_survivor_survives_flow_replacement
#print axioms pass_preserves_mark_and_flag
#print axioms pass_does_not_protect_plain
#print axioms cycle_restoration_protected
#print axioms cross_mark_survives_every_provider
#print axioms protected_survives_every_provider
#print axioms a_plain_same_mark_can_be_removed
#print axioms cross_mark_negative_control

end MarkedRuleGuidance
