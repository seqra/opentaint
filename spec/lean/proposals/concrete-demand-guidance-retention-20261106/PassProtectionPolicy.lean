/-
SELECTED PASS LAW, PROPOSAL ADAPTER ONLY. Pass edges transport existing H but
cannot introduce it. This model does not claim that generic summary composition
cannot add cycle protection. Native assignment/cleaner policies remain explicit.
No production implementation or whole-engine equivalence is proved here.
-/
import Std

namespace PassProtectionPolicy

inductive ActionRole where | passThrough | other
deriving DecidableEq, Repr
inductive OccurrenceKind where | passThrough | other
deriving DecidableEq, Repr
structure ActionMetadata where
  role : ActionRole
  occurrenceKind : OccurrenceKind
deriving DecidableEq, Repr
structure ForwardMetadata where
  isSource : Bool
  action : Option ActionMetadata
deriving DecidableEq, Repr

def passTagged (edgeMetadata : ForwardMetadata) : Bool :=
  match edgeMetadata.action with
  | none => false
  | some action => decide (action.role = .passThrough) ||
      decide (action.occurrenceKind = .passThrough)

/-- Current EngineAlgebra expression; not a claim that native JIR passes have
an action ID. The observed ordinary JIR pass has neither source nor action ID. -/
def oldRuleAssignment (edgeMetadata : ForwardMetadata) : Bool :=
  edgeMetadata.isSource || edgeMetadata.action.isSome

/-- Exact proposed defensive predicate: reject either typed pass tag before
using the unchanged old expression for every other micro edge. -/
def proposedRuleAssignment (edgeMetadata : ForwardMetadata) : Bool :=
  !(passTagged edgeMetadata) && oldRuleAssignment edgeMetadata

inductive Direction where | direct | reversed
deriving DecidableEq, Repr
def flip : Direction → Direction | .direct => .reversed | .reversed => .direct
inductive Slot where | x | y | other
deriving DecidableEq, Repr
structure Transfer where
  sourceSlot : Slot
  targetSlot : Slot
deriving DecidableEq, Repr
structure MicroEdge where
  forward : Transfer
  metadata : ForwardMetadata
  direction : Direction
deriving DecidableEq, Repr

def reverse (edge : MicroEdge) : MicroEdge := { edge with direction := flip edge.direction }
def source (edge : Transfer) : Direction → Slot | .direct => edge.sourceSlot | .reversed => edge.targetSlot
def target (edge : Transfer) : Direction → Slot | .direct => edge.targetSlot | .reversed => edge.sourceSlot

abbrev Mask := Slot → Bool
def zeroMask : Mask := fun _ => false
def singleton (slot : Slot) : Mask := fun out => decide (out = slot)

/-- The same directed transfer is applied to payload and incoming H. It is a
finite coordinate map, not a proof of every native AP operation. -/
def transport (edge : Transfer) (direction : Direction) (mask : Mask) : Mask :=
  fun out => if out = target edge direction then mask (source edge direction) else false

structure Packet where
  payload : Mask
  h : Mask
def plain (payload : Mask) : Packet := ⟨payload,zeroMask⟩

inductive Policy where | transportOnly | ruleAssignment | cleanerSelected | rawSummaryComposition
deriving DecidableEq, Repr
def microPolicy (edge : MicroEdge) : Policy :=
  if proposedRuleAssignment edge.metadata then .ruleAssignment else .transportOnly

inductive Operation where
  | micro (edge : MicroEdge)
  | cleaner
  | rawSummary
def operationPolicy : Operation → Policy
  | .micro edge => microPolicy edge
  | .cleaner => .cleanerSelected
  | .rawSummary => .rawSummaryComposition

structure Candidates where
  assignmentCondition : Bool
  assigned : Mask
  cleanerCondition : Bool
  cleaned : Mask
  summaryFlags : Mask
  summaryCycle : Mask

def introduced (policy : Policy) (c : Candidates) (out : Slot) : Bool :=
  match policy with
  | .transportOnly => false
  | .ruleAssignment => c.assignmentCondition && c.assigned out
  | .cleanerSelected => c.cleanerCondition && c.cleaned out
  | .rawSummaryComposition => c.summaryFlags out || c.summaryCycle out

def applyPolicy (policy : Policy) (edge : Transfer) (direction : Direction)
    (input : Packet) (c : Candidates) : Packet :=
  let output := transport edge direction input.payload
  ⟨output,fun out => transport edge direction input.h out ||
    (introduced policy c out && output out)⟩
def runMicro (edge : MicroEdge) (input : Packet) (c : Candidates) : Packet :=
  applyPolicy (microPolicy edge) edge.forward edge.direction input c

theorem either_typed_pass_tag_blocks_rule_assignment (sourceFlag : Bool) :
    proposedRuleAssignment ⟨sourceFlag,some ⟨.passThrough,.other⟩⟩ = false ∧
    proposedRuleAssignment ⟨sourceFlag,some ⟨.other,.passThrough⟩⟩ = false ∧
    proposedRuleAssignment ⟨sourceFlag,some ⟨.passThrough,.passThrough⟩⟩ = false := by
  cases sourceFlag <;> decide

theorem untagged_micro_preserves_old_expression (edgeMetadata : ForwardMetadata)
    (notPass : passTagged edgeMetadata = false) :
    proposedRuleAssignment edgeMetadata = oldRuleAssignment edgeMetadata := by
  simp [proposedRuleAssignment,notPass]

theorem valid_SOURCE_or_other_nontagged_action_retains_assignment (sourceFlag : Bool) :
    proposedRuleAssignment ⟨sourceFlag,some ⟨.other,.other⟩⟩ = true := by
  cases sourceFlag <;> decide

theorem tagged_micro_uses_transport_policy (edge : MicroEdge)
    (isPass : passTagged edge.metadata = true) : microPolicy edge = .transportOnly := by
  simp [microPolicy,proposedRuleAssignment,isPass]

theorem reversal_retains_forward_metadata (edge : MicroEdge) :
    (reverse edge).metadata = edge.metadata ∧ (reverse edge).forward = edge.forward := ⟨rfl,rfl⟩

theorem direct_reversed_dispatch_use_identical_policy (edge : MicroEdge) :
    microPolicy (reverse edge) = microPolicy edge := rfl

theorem reverse_twice_restores_micro (edge : MicroEdge) : reverse (reverse edge) = edge := by
  cases edge with
  | mk transfer metadata direction => cases direction <;> rfl

theorem transport_plain_mask_is_plain (edge : Transfer) (direction : Direction) (out : Slot) :
    transport edge direction zeroMask out = false := by simp [transport,zeroMask]

theorem transport_only_never_uses_introduction_candidates (c : Candidates) (out : Slot) :
    introduced .transportOnly c out = false := rfl

theorem pass_H_follows_exactly_the_existing_transfer
    (edge : Transfer) (direction : Direction) (input : Packet) (c : Candidates) (out : Slot) :
    (applyPolicy .transportOnly edge direction input c).h out =
      transport edge direction input.h out := by simp [applyPolicy,introduced]

theorem pass_plain_input_remains_plain (edge : Transfer) (direction : Direction)
    (payload : Mask) (c : Candidates) (out : Slot) :
    (applyPolicy .transportOnly edge direction (plain payload) c).h out = false := by
  simp [applyPolicy,introduced,plain,transport,zeroMask]

theorem tagged_pass_plain_input_remains_plain (edge : MicroEdge)
    (isPass : passTagged edge.metadata = true) (payload : Mask) (c : Candidates) (out : Slot) :
    (runMicro edge (plain payload) c).h out = false := by
  rw [runMicro,tagged_micro_uses_transport_policy edge isPass]
  exact pass_plain_input_remains_plain _ _ _ _ _

theorem tagged_reversed_pass_plain_input_remains_plain (edge : MicroEdge)
    (isPass : passTagged edge.metadata = true) (payload : Mask) (c : Candidates) (out : Slot) :
    (runMicro (reverse edge) (plain payload) c).h out = false := by
  exact tagged_pass_plain_input_remains_plain (reverse edge) isPass payload c out

theorem pass_existing_H_reaches_the_mapped_target
    (edge : Transfer) (direction : Direction) (input : Packet) (c : Candidates) :
    (applyPolicy .transportOnly edge direction input c).h (target edge direction) =
      input.h (source edge direction) := by simp [applyPolicy,introduced,transport]

theorem pass_does_not_create_H_at_unmapped_output (edge : Transfer) (direction : Direction)
    (input : Packet) (c : Candidates) (out : Slot) (unmapped : out ≠ target edge direction) :
    (applyPolicy .transportOnly edge direction input c).h out = false := by
  simp [applyPolicy,introduced,transport,unmapped]

theorem assignment_and_cleaner_introduction_policies_are_explicit :
    operationPolicy .cleaner = .cleanerSelected ∧
    operationPolicy .rawSummary = .rawSummaryComposition := ⟨rfl,rfl⟩

theorem assignment_gate_is_not_a_pass_gate (c : Candidates) (out : Slot) :
    introduced .ruleAssignment c out = (c.assignmentCondition && c.assigned out) ∧
    introduced .cleanerSelected c out = (c.cleanerCondition && c.cleaned out) := ⟨rfl,rfl⟩

def xy : Transfer := ⟨.x,.y⟩
def taggedByRole : ForwardMetadata := ⟨false,some ⟨.passThrough,.other⟩⟩
def taggedByKind : ForwardMetadata := ⟨false,some ⟨.other,.passThrough⟩⟩
def ordinaryJirPass : ForwardMetadata := ⟨false,none⟩
def allCandidates : Candidates := ⟨true,singleton .y,true,singleton .y,singleton .y,singleton .y⟩
def cycleOnly : Candidates := ⟨false,zeroMask,false,zeroMask,zeroMask,singleton .y⟩
def markedX : Packet := ⟨singleton .x,singleton .x⟩
def markedY : Packet := ⟨singleton .y,singleton .y⟩

theorem actual_untagged_JIR_pass_was_already_nonassignment :
    oldRuleAssignment ordinaryJirPass = false ∧ proposedRuleAssignment ordinaryJirPass = false := by decide

theorem defensive_tagged_case_is_not_an_observed_JIR_bug :
    oldRuleAssignment taggedByRole = true ∧ proposedRuleAssignment taggedByRole = false ∧
    oldRuleAssignment taggedByKind = true ∧ proposedRuleAssignment taggedByKind = false := by decide

theorem finite_direct_pass_transports_H_without_new_flags :
    (runMicro ⟨xy,taggedByRole,.direct⟩ markedX allCandidates).h .y = true ∧
    (runMicro ⟨xy,taggedByRole,.direct⟩ markedX allCandidates).h .x = false ∧
    (runMicro ⟨xy,taggedByRole,.direct⟩ (plain (singleton .x)) allCandidates).h .y = false := by decide

theorem finite_reversed_pass_transports_H_without_new_flags :
    (runMicro ⟨xy,taggedByKind,.reversed⟩ markedY allCandidates).h .x = true ∧
    (runMicro ⟨xy,taggedByKind,.reversed⟩ markedY allCandidates).h .y = false ∧
    (runMicro ⟨xy,taggedByKind,.reversed⟩ (plain (singleton .y)) allCandidates).h .x = false := by decide

/-- This deliberate positive case prevents a false global non-introduction
claim about generic summary application, which has no raw pass provenance. -/
theorem generic_summary_cycle_can_introduce_protection :
    (applyPolicy .rawSummaryComposition xy .direct (plain (singleton .x)) cycleOnly).h .y = true ∧
    (applyPolicy .transportOnly xy .direct (plain (singleton .x)) cycleOnly).h .y = false := by decide

theorem assignment_cleaner_and_summary_cases_are_separate :
    (applyPolicy .ruleAssignment xy .direct (plain (singleton .x)) allCandidates).h .y = true ∧
    (applyPolicy .cleanerSelected xy .direct (plain (singleton .x)) allCandidates).h .y = true ∧
    (applyPolicy .ruleAssignment xy .direct (plain (singleton .x)) cycleOnly).h .y = false ∧
    (applyPolicy .cleanerSelected xy .direct (plain (singleton .x)) cycleOnly).h .y = false := by decide

def witness : Bool :=
  decide ((runMicro ⟨xy,taggedByRole,.direct⟩ (plain (singleton .x)) allCandidates).h .y = false) &&
  decide ((runMicro ⟨xy,taggedByKind,.reversed⟩ markedY allCandidates).h .x = true) &&
  decide ((applyPolicy .rawSummaryComposition xy .direct (plain (singleton .x)) cycleOnly).h .y = true)

theorem executable_pass_policy_witness : witness = true := by decide

#eval (if witness then "PASS_PROTECTION_POLICY=true" else "PASS_PROTECTION_POLICY=false")

-- One audit command per theorem.
#print axioms either_typed_pass_tag_blocks_rule_assignment
#print axioms untagged_micro_preserves_old_expression
#print axioms valid_SOURCE_or_other_nontagged_action_retains_assignment
#print axioms tagged_micro_uses_transport_policy
#print axioms reversal_retains_forward_metadata
#print axioms direct_reversed_dispatch_use_identical_policy
#print axioms reverse_twice_restores_micro
#print axioms transport_plain_mask_is_plain
#print axioms transport_only_never_uses_introduction_candidates
#print axioms pass_H_follows_exactly_the_existing_transfer
#print axioms pass_plain_input_remains_plain
#print axioms tagged_pass_plain_input_remains_plain
#print axioms tagged_reversed_pass_plain_input_remains_plain
#print axioms pass_existing_H_reaches_the_mapped_target
#print axioms pass_does_not_create_H_at_unmapped_output
#print axioms assignment_and_cleaner_introduction_policies_are_explicit
#print axioms assignment_gate_is_not_a_pass_gate
#print axioms actual_untagged_JIR_pass_was_already_nonassignment
#print axioms defensive_tagged_case_is_not_an_observed_JIR_bug
#print axioms finite_direct_pass_transports_H_without_new_flags
#print axioms finite_reversed_pass_transports_H_without_new_flags
#print axioms generic_summary_cycle_can_introduce_protection
#print axioms assignment_cleaner_and_summary_cases_are_separate
#print axioms executable_pass_policy_witness

end PassProtectionPolicy
