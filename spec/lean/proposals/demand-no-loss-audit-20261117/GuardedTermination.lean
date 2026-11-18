import ServiceSimulation
import UniformStickyColdAlternating
import BoundBodyCold
import BoundUniformCold
import PriorReplay
import StrictExact
import StrictUniform
import StrictDifferent
import LaneProof

namespace GuardedTermination

open ServiceSimulation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000000

def retireTarget (closedOrigin : Bool) (enabled plan : List Action)
    (retained otherUses : List Need) : Bool :=
  closedOrigin && check enabled plan retained otherUses

theorem a_retired_target_keeps_each_listed_control_use
    (retired : retireTarget closedOrigin enabled plan retained otherUses = true)
    (wanted : need ∈ otherUses) :
    AuditKernel.Derives (nativeRules enabled) (· ∈ retained) need :=
  checked_service_supplies_each_obligation (Bool.and_eq_true_iff.mp retired).2 wanted

-- These pure writer/reader reference programs have one source and one
-- observer. Their interface has no additional required use of the root key.
-- This adapter does not infer that property for arbitrary source programs.
def fieldCone (closedOrigin : Bool) (otherUses : List Need) : Nat → RegularRepair.Frame
  | 0 => ⟨closedOrigin,true,true,true,false⟩
  | n+1 =>
    let prev := fieldCone closedOrigin otherUses n
    let allowed := prev.target
    ⟨closedOrigin,allowed && !retireTarget prev.closedGoal [] [] [] otherUses,
      allowed,allowed,false⟩

theorem all_later_pairs_of_the_isolated_disjoint_slice_are_quiet
    (closedOrigin : Bool) (closed : closedOrigin = true) (n : Nat) :
    fieldCone closedOrigin [] (n+2) = ⟨true,false,false,false,false⟩ := by
  subst closedOrigin
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.succ_add,fieldCone,ih]; rfl

theorem the_disjoint_regular_and_nested_models_keep_the_run5_stop :
    fieldCone (RegularCertificate.certifiesEmpty RegularCertificate.writer
      RegularCertificate.reader) [] 2 = ⟨true,false,false,false,false⟩ ∧
    fieldCone (PairedContext.check PairedContext.reader 1 PairedContext.writer) [] 2 =
      ⟨true,false,false,false,false⟩ := by decide

-- The same word certificate cannot serve a second seed or a later
-- permission. A key for the wrong scope does not fulfill that obligation.
theorem disjointness_cannot_retire_a_key_with_an_unserved_control_use (need : Need) :
    retireTarget true [] [] [] [need] = false := by simp [retireTarget,check,replay,ready]

theorem the_unserved_control_preserves_the_root_key_in_every_pair (need : Need) (n : Nat) :
    fieldCone true [need] n = ⟨true,true,true,true,false⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fieldCone,ih,disjointness_cannot_retire_a_key_with_an_unserved_control_use]
    rfl

theorem a_required_control_can_be_discharged_by_retained_service (need : Need) :
    retireTarget true [] [] [need] [need] = true := by simp [retireTarget,check,replay,ready]

theorem a_shallow_observer_cannot_remove_the_only_late_track :
    let suppress := !(retainReply true true false)
    CoveredOrigin.cold suppress 1 = ⟨true,false,true⟩ ∧
    CoveredOrigin.cold suppress 2 = ⟨true,true,false⟩ := by decide

-- Use the same accumulating Target calculation as UniformSticky, with
-- all value-only omissions disabled to measure conservative retention.
def retainedForwardDemand (run : Nat) (old : UniformAlternating.State) : Bool :=
  UniformSticky.seenDemand (fun data => data.offers.getLast!.any (·.demand))
    (UniformAlternating.round false run (UniformAlternating.limit run) old.rows old.saved) 12
    (UniformAlternating.initialData false)

def retainedStep (run : Nat) (old : UniformAlternating.State) : UniformAlternating.State :=
  let next := UniformAlternating.step false run old
  if run % 2 == 1 && old.sourceAllowed then
    {next with observationActive := retainedForwardDemand run old}
  else next

def retainedHistory : Nat → UniformAlternating.State
  | 0 => UniformAlternating.initial
  | n+1 => retainedStep (n+1) (retainedHistory n)

def alternatingControl (run : Nat) : Nat × Bool × Nat × Bool × Bool × Nat × Bool :=
  let earlier := UniformSticky.newHistory run
  let retained := retainedHistory run
  (run,earlier.report,earlier.rows.length,earlier.observationActive,
    retained.report,retained.rows.length,retained.observationActive)

#eval [1,3,5,7,9,11].map alternatingControl

def boundControl (run : Nat) : Nat × Bool × Nat × Bool × Bool × Nat × Bool :=
  let exact := BoundBody.history false run
  let uniform := BoundUniform.history false run
  (run,exact.report,exact.rows.length,exact.observationActive,
    uniform.report,uniform.rows.length,uniform.observationActive)

#eval [1,3,5,7,9,11].map boundControl

section AlternatingOrigins
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition

def alternatives : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (alternatives n).flatMap fun rest => [false::rest,true::rest]

theorem every_three_call_generator_choice_is_enumerated
    (choices : List Bool) (size : choices.length = n) : choices ∈ alternatives n := by
  induction choices generalizing n with
  | nil =>
    subst n
    simp [alternatives]
  | cons choice rest ih =>
    rw [List.length_cons] at size
    subst n
    apply List.mem_flatMap.mpr
    refine ⟨rest,ih rfl,?_⟩
    cases choice <;> simp

-- The two generator sites for a given input mark are uniquely identified
-- by their different result heads (root and f). Use an admitted paired
-- C2/body/C5 result and its own binding for each chosen site.
def nextOffer (atField : Bool) (m : Color) : Offered :=
  ⟨fact p (if atField then [f] else []) .must m.flip,false⟩

def generatorWitness (state : UniformAlternating.State) (offer : Offered)
    (m : Color) (atField : Bool) : Bool :=
  let out := value p (nextOffer atField m).ap.path .must m.flip false
  (UniformAlternating.candidates 3 2 false state.rows state.saved [offer]).any fun edge =>
    UniformAlternating.read edge offer == some out

def generatorTrack (state : UniformAlternating.State) : List Bool → Offered → Color → Bool
  | [], _, _ => true
  | atField::rest, offer, m =>
    generatorWitness state offer m atField &&
    generatorTrack state rest (nextOffer atField m) m.flip

theorem all_eight_generator_routes_have_a_paired_NORMAL_witness_at_run3 :
    (alternatives 3).all (fun choices => generatorTrack UniformStickyColdAlternating.state2
      choices source .t) = true := by decide +kernel

theorem each_three_call_route_has_its_own_witness (choices : List Bool)
    (size : choices.length = 3) :
    generatorTrack UniformStickyColdAlternating.state2 choices source .t = true :=
  List.all_eq_true.mp all_eight_generator_routes_have_a_paired_NORMAL_witness_at_run3
    choices (every_three_call_generator_choice_is_enumerated choices size)

end AlternatingOrigins

-- These independent cold reference results keep their own assumptions.
-- In particular, Strict* enables R15 without modelling the affected-use
-- catalogue. This conjunction is not a certificate for that catalogue.
theorem the_definite_replay_reference_cases_keep_both_observations :
    (StrictExact.history 5).reports = [0,1] ∧
    (StrictUniform.history 5).reports = [0,1] ∧
    (StrictDifferent.history 5).reports = [0,1] :=
  ⟨StrictExact.reports_and_normal_records_preserved.1,
    StrictUniform.reports_and_normal_records_preserved.1,
    StrictDifferent.reports_and_normal_records_preserved.1⟩

end GuardedTermination
