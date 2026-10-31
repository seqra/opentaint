import FullComputedLayer

/-!
User-authorized backward source-summary completion, 2026-10-31.

This boundary runs after an existing summary/record matcher accepts a result.
A concrete nonzero callee premise and a ZERO result identify source completion
in backward execution. Emit an anonymous terminal under the complete caller
original. Balanced ZERO -> ZERO stays ordinary control. No matcher, C2, C5,
field operation, source/action occurrence, or fresh GEN callback is added.
-/
namespace SourceSummaryCompletion
open SelectedCore
open FullZeroSourceReplay
set_option autoImplicit false

inductive CalleePremise where | zero | concrete | flow deriving DecidableEq, Repr
inductive Completion where
  | ap (effect : NativeEffect)
  | terminal (row : Summary)
  deriving DecidableEq, Repr

def complete (direction : Direction) (premise : CalleePremise) (owner : Nat)
    (original : Premise) (effect : NativeEffect) : Completion :=
  match direction, premise, effect with
  | .backward, .concrete, .zero _ => .terminal (targetSummary owner original)
  | _, _, _ => .ap effect

theorem accepted_backward_source_is_terminal (owner : Nat) (original : Premise) (layer : Layer) :
    complete .backward .concrete owner original (.zero layer) =
      .terminal (targetSummary owner original) := rfl

theorem complete_caller_original_is_preserved (owner : Nat) (original : Premise) (layer : Layer) :
    complete .backward .concrete owner original (.zero layer) =
      .terminal ⟨owner, original, .target .demandTarget, .demand⟩ := rfl

theorem source_completion_never_creates_normal_report (owner : Nat) (original : Premise)
    (layer : Layer) (id : Nat) :
    complete .backward .concrete owner original (.zero layer) ≠
      .terminal (layeredTargetSummary owner original .normal id) := by
  simp [complete, targetSummary, layeredTargetSummary, Target.fromLayer]

theorem balanced_zero_is_ordinary (direction : Direction) (owner : Nat)
    (original : Premise) (layer : Layer) :
    complete direction .zero owner original (.zero layer) = .ap (.zero layer) := by
  cases direction <;> rfl

theorem forward_application_unchanged (premise : CalleePremise) (owner : Nat)
    (original : Premise) (effect : NativeEffect) :
    complete .forward premise owner original effect = .ap effect := by
  cases premise <;> cases effect <;> rfl

theorem nonzero_result_unchanged (direction : Direction) (premise : CalleePremise)
    (owner : Nat) (original : Premise) (key : SourceKey) (layer : Layer) :
    complete direction premise owner original (.marked key layer) = .ap (.marked key layer) := by
  cases direction <;> cases premise <;> rfl

theorem flow_premise_does_not_create_target (direction : Direction) (owner : Nat)
    (original : Premise) (effect : NativeEffect) :
    complete direction .flow owner original effect = .ap effect := by
  cases direction <;> cases effect <;> rfl

/-- Source-summary completion is after matching, not an alternative matcher. -/
def accepted (direction : Direction) (premise : CalleePremise) (owner : Nat)
    (original : Premise) (result : Option NativeEffect) : List Completion :=
  result.toList.map (complete direction premise owner original)

theorem rejected_application_emits_nothing (direction : Direction) (premise : CalleePremise)
    (owner : Nat) (original : Premise) : accepted direction premise owner original none = [] := rfl

theorem current_and_native_source_completion_equal (owner : Nat) (original : Premise)
    (layer : Layer) :
    accepted .backward .concrete owner original (some (.zero layer)) =
      [.terminal (targetSummary owner original)] := rfl

def nativePremise : Direction → CalleePremise
  | .forward => .zero | .backward => .concrete

/-- The existing native read still decides all geometry and layer matching. -/
def replay (direction : Direction) (owner : Nat) (original : Premise)
    (saved : List SourceKey) (input : Input) : List Completion :=
  saved.flatMap fun row => accepted direction (nativePremise direction) owner original
    (readNative direction row input)

structure CallResult where
  effects : List Completion
  initials : List SourceKey
  sourceHits : List SourceKey
  startCurrent : Bool
  deriving DecidableEq, Repr

/-- Record reads do not execute an actual source action. The hit list stays empty. -/
def call (direction : Direction) (owner : Nat) (original : Premise)
    (saved : List SourceKey) (guide : Option SourceKey) (input : Input) : CallResult :=
  let effects := replay direction owner original saved input
  let initials := admitExact guide input
  ⟨effects, initials, [], !initials.isEmpty⟩

theorem native_may_replay_emits_target_before_empty_gate (owner : Nat) (original : Premise)
    (key : SourceKey) (layer : Layer) (guide : Option SourceKey) :
    call .backward owner original [key] guide (.may key layer) =
      ⟨[.terminal (targetSummary owner original)], [], [], false⟩ := by
  cases guide <;> simp [call, replay, accepted, nativePremise, readNative, admitExact, complete]

theorem forward_saved_source_stays_ordinary_before_empty_gate (owner : Nat) (original : Premise)
    (key : SourceKey) :
    call .forward owner original [key] none (.zero .normal) =
      ⟨[.ap (.marked key .normal)], [], [], false⟩ := by
  simp [call, replay, accepted, nativePremise, readNative, admitExact, complete]

theorem no_fresh_source_hit_from_summary_replay (direction : Direction) (owner : Nat)
    (original : Premise) (saved : List SourceKey) (guide : Option SourceKey) (input : Input) :
    (call direction owner original saved guide input).sourceHits = [] := rfl

theorem c2_may_rejection_unchanged (owner : Nat) (original : Premise) (key guide : SourceKey)
    (saved : List SourceKey) (layer : Layer) :
    (call .backward owner original saved (some guide) (.may key layer)).initials = [] := rfl

theorem replay_independent_of_current_demand (direction : Direction) (owner : Nat)
    (original : Premise) (saved : List SourceKey) (left right : Option SourceKey) (input : Input) :
    (call direction owner original saved left input).effects =
      (call direction owner original saved right input).effects := rfl

theorem completed_source_handoff_keeps_full_original (owner : Nat) (original : Premise) :
    selectedTargetHandoff (targetSummary owner original) =
      (premiseMembers original).map (fun member => ⟨owner, .target, member⟩) := rfl

/-- Publication remains subject to the selected same-pair C5 rule. -/
theorem completion_does_not_bypass_c5 (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat) (original : Premise) :
    c5Accept entryAP exitAP d (targetSummary owner original) = true ↔
      (d.owner == owner) = true ∧ entryIntersects entryAP d.entry original = true ∧ d.exit = .zero :=
  c5_accept_target_iff _ _ _ _ _ _ _

/-- Admission still has no fallback when no matching native record exists.
This bounded cell applies when no matching NORMAL producer exists.
It is not a claim that every FULL nonzero producer has DEMAND layer. -/
theorem no_native_and_may_exact_guide_has_no_route (owner : Nat) (original : Premise)
    (guide actual : SourceKey) (layer : Layer) :
    call .backward owner original [] (some guide) (.may actual layer) =
      ⟨[], [], [], false⟩ := rfl

namespace Controls

def key : SourceKey := ⟨7, 2, [], 11⟩

theorem nonzero_origin_is_not_replaced_by_zero :
    complete .backward .concrete 3 (.ap .b) (.zero .normal) =
      .terminal (targetSummary 3 (.ap .b)) := rfl

theorem balanced_zero_never_becomes_terminal :
    complete .backward .zero 3 .zero (.zero .normal) = .ap (.zero .normal) := rfl

/-- Atom a represents the static descriptor in the separate runtime trace.
Completion dispatch alone cannot combine permissions from different rows. -/
def staticWriterGuide : Demand := ⟨3, .ap .a, .zero⟩
def staticReaderGuide : Demand := ⟨3, .target, .ap .a⟩

theorem source_completion_does_not_close_static_pair_gap :
    complete .backward .concrete 3 .zero (.zero .demand) =
      .terminal (targetSummary 3 .zero) ∧
    c5Accept exactEntry exactExit staticWriterGuide (targetSummary 3 .zero) = false ∧
    c5Accept exactEntry exactExit staticReaderGuide (targetSummary 3 .zero) = false := by decide

/-- A source result whose ordinary transfer already computed DEMAND. -/
def nonzeroFullSource : Packet := ⟨key, .exact, .fullTaint, .ordinary, false, .demand⟩
def nonzeroFullNativeCandidates : List SourceKey :=
  (normalLayerCandidate (FullComputedLayer.force true nonzeroFullSource)).toList

theorem computed_demand_producer_has_no_native_admission_fallback :
    (FullComputedLayer.force true nonzeroFullSource).layer = .demand ∧
      nonzeroFullNativeCandidates = [] ∧
      call .backward 3 .zero nonzeroFullNativeCandidates (some key) (.may key .demand) =
        ⟨[], [], [], false⟩ := ⟨rfl, rfl, rfl⟩

def checks : Bool :=
  decide (call .backward 3 (.both .a .b) [key] none (.may key .demand) =
    ⟨[.terminal (targetSummary 3 (.both .a .b))], [], [], false⟩) &&
  decide (complete .backward .zero 3 .zero (.zero .normal) = .ap (.zero .normal)) &&
  decide (call .forward 3 .zero [key] none (.zero .normal) =
    ⟨[.ap (.marked key .normal)], [], [], false⟩) &&
  decide (c5Accept exactEntry exactExit staticWriterGuide (targetSummary 3 .zero) = false) &&
  decide (c5Accept exactEntry exactExit staticReaderGuide (targetSummary 3 .zero) = false) &&
  decide (call .backward 3 .zero nonzeroFullNativeCandidates (some key) (.may key .demand) =
    ⟨[], [], [], false⟩)

theorem checks_pass : checks = true := rfl
end Controls

#print axioms accepted_backward_source_is_terminal
#print axioms native_may_replay_emits_target_before_empty_gate
#print axioms completion_does_not_bypass_c5
#print axioms Controls.source_completion_does_not_close_static_pair_gap
#print axioms Controls.computed_demand_producer_has_no_native_admission_fallback
#print axioms Controls.checks_pass
#eval Controls.checks

end SourceSummaryCompletion
