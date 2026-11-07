/-
Second Deep case only. A supplied ZERO-origin growing output is x.f^3.$/T,N.
All three existing observation families are empty at this critical offer.
One supplied saved NORMAL FLOW repeat row x.f.* -> x.* maps the actual to
x.f^2.$/T,N and can replay a finite nongrowing chain to x.$/T,N.
This is an explicit conditional finite countermodel, not a native adapter,
eligibility, ownership, whole-program or global-progress theorem. No repair.
-/
import RestrictedInitialPolicy

namespace SavedRepeatObserverCountermodel
open ApSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def x : Base := 1
def f : Acc := 7
def g : Acc := 8
def taint : ApSpec.Mark := 11
def fields : Nat → List Acc | 0 => [] | n+1 => f :: fields n
def exactAt (n : Nat) : AFact := ⟨⟨x,fields n,.exact,.conc taint⟩,false⟩
def savedInput : PFact := ⟨x,[f],.star .empty,.star⟩
def savedOutput : AFact := ⟨⟨x,[],.star .empty,.star⟩,false⟩
def savedApply (actual : AFact) : Res := applySummary actual savedInput savedOutput

theorem saved_NORMAL_FLOW_repeat_maps_every_exact_successor_to_its_predecessor (n : Nat) :
    (savedApply (exactAt (n+1))).facts = [exactAt n] ∧
    (savedApply (exactAt (n+1))).reqs = [] := by
  cases n <;> constructor <;> rfl

theorem root_and_wrong_field_do_not_gain_an_extra_saved_repeat_output :
    (savedApply (exactAt 0)).facts = [] ∧
    (savedApply ⟨⟨x,[g,g,g],.exact,.conc taint⟩,false⟩).facts = [] := by decide

inductive Origin where | zero | data (initial : Nat)
deriving DecidableEq, Repr
structure GrowingOffer where
  origin : Origin
  actual : AFact
deriving DecidableEq, Repr

def growingZero : GrowingOffer := ⟨.zero,exactAt 3⟩
structure ThreeFamilies where
  adjacent : List Nat
  enclosingCurrentB : List AFact
  repeatDATA : List Nat
deriving DecidableEq, Repr
structure WithSavedRepeat where
  ordinary : ThreeFamilies
  repeatSavedNORMAL : List AFact
deriving DecidableEq, Repr

def emptyThree : ThreeFamilies := ⟨[],[],[]⟩
/-- These are the scenario's recorded/assumed empty responses AT THIS OFFER,
not claims about every value, run or method. The saved row is a separate input. -/
def atCriticalOffer : ThreeFamilies := ⟨[],[],[]⟩
def fullAtCriticalOffer : WithSavedRepeat := ⟨atCriticalOffer,(savedApply growingZero.actual).facts⟩
def fullAtBaseline : WithSavedRepeat := ⟨emptyThree,[]⟩
def retainByThree : List AFact := if atCriticalOffer = emptyThree then [] else [growingZero.actual]

theorem ZERO_origin_and_NORMAL_exact_layer_are_explicit_and_not_a_DATA_initial :
    growingZero.origin = .zero ∧ growingZero.actual = exactAt 3 ∧
    growingZero.actual.demand = false ∧ savedOutput.demand = false ∧
    savedInput.mark = .star ∧ savedOutput.fact.mark = .star := by decide

theorem three_empty_families_equal_the_baseline_and_drop_the_growing_offer :
    atCriticalOffer = emptyThree ∧ retainByThree = [] ∧
    fullAtCriticalOffer.ordinary = fullAtBaseline.ordinary := by decide

def nongrowing (actual : AFact) : Bool := decide (actual.fact.path.length ≤ 2)
def savedStep (actual : AFact) : List AFact := (savedApply actual).facts.filter nongrowing
def replay : Nat → List AFact → List AFact
  | 0,inputs => inputs
  | fuel+1,inputs => replay fuel (inputs.flatMap savedStep)
def normalSink (values : List AFact) : Bool := decide (exactAt 0 ∈ values)

theorem omitted_saved_repeat_has_a_NORMAL_nongrowing_output_and_a_different_signature :
    fullAtCriticalOffer.repeatSavedNORMAL = [exactAt 2] ∧
    nongrowing (exactAt 2) = true ∧ (exactAt 2).demand = false ∧
    fullAtCriticalOffer ≠ fullAtBaseline := by decide

theorem saved_replay_computes_the_three_step_NORMAL_chain_without_new_seeds :
    savedStep (exactAt 3) = [exactAt 2] ∧
    savedStep (exactAt 2) = [exactAt 1] ∧
    savedStep (exactAt 1) = [exactAt 0] ∧
    replay 3 [growingZero.actual] = [exactAt 0] ∧
    normalSink (replay 3 [growingZero.actual]) = true := by decide

theorem empty_baseline_drop_loses_this_finite_saved_replay_observation :
    replay 3 retainByThree = [] ∧
    normalSink (replay 3 retainByThree) = false ∧
    normalSink (replay 3 retainByThree) ≠ normalSink (replay 3 [growingZero.actual]) := by decide

theorem counterexample_has_executable_offer_and_saved_relation_witnesses :
    ∃ offer : GrowingOffer, ∃ entry : PFact, ∃ result : AFact,
      offer = growingZero ∧ entry = savedInput ∧ result = savedOutput ∧
      (applySummary offer.actual entry result).facts = [exactAt 2] ∧
      atCriticalOffer = emptyThree ∧ normalSink (replay 3 [offer.actual]) = true := by
  exact ⟨growingZero,savedInput,savedOutput,rfl,rfl,rfl,by decide,rfl,by decide⟩

def check : Bool :=
  decide (retainByThree = []) &&
  decide (fullAtCriticalOffer ≠ fullAtBaseline) &&
  normalSink (replay 3 [growingZero.actual]) &&
  !normalSink (replay 3 retainByThree)

theorem executable_second_Deep_countermodel : check = true := by decide
#eval (if check then "SECOND_DEEP_SAVED_REPEAT_COUNTERMODEL=true" else "SECOND_DEEP_SAVED_REPEAT_COUNTERMODEL=false")

#print axioms saved_NORMAL_FLOW_repeat_maps_every_exact_successor_to_its_predecessor
#print axioms root_and_wrong_field_do_not_gain_an_extra_saved_repeat_output
#print axioms ZERO_origin_and_NORMAL_exact_layer_are_explicit_and_not_a_DATA_initial
#print axioms three_empty_families_equal_the_baseline_and_drop_the_growing_offer
#print axioms omitted_saved_repeat_has_a_NORMAL_nongrowing_output_and_a_different_signature
#print axioms saved_replay_computes_the_three_step_NORMAL_chain_without_new_seeds
#print axioms empty_baseline_drop_loses_this_finite_saved_replay_observation
#print axioms counterexample_has_executable_offer_and_saved_relation_witnesses
#print axioms executable_second_Deep_countermodel

end SavedRepeatObserverCountermodel
