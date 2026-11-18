import RootCleanerPolicy
import DisjointCleaner
import DirectPossibleReplay

/- The current selected EXACT cleaner policy, including the same-head
   MUST exception. The candidate uses a strict descendant, so the exception
   is present but inactive. No source or summary is assumed as a demand. -/
namespace DescendantCleanerCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open UniformRootCleanerCycle
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

def cleaned : Path := [f]

def sameHeadMUST (c : Value) : Bool :=
  c.ap.base==x && c.ap.mark==some t && c.ap.path==cleaned && c.ap.tail==.must

def exactClean (c : Value) : Option Value :=
  if c.ap.base != x || c.ap.mark != some t then some c else
  if sameHeadMUST c then some {c with h:=true} else
  match dropHead cleaned c.ap.path with
  | some []=>if c.ap.tail==.exact then none else
      some {c with demand:=true,h:=true,ap:={c.ap with tail:=if c.ap.tail==.star then .may else c.ap.tail}}
  | some (_::_)=>some {c with h:=true}
  | none=>match dropHead c.ap.path cleaned with
    | some (first::_)=>
      if c.ap.tail==.exact || c.ap.e.contains first then some {c with h:=true}
      else some {c with demand:=true,h:=true,ap:={c.ap with tail:=if c.ap.tail==.star then .may else c.ap.tail}}
    | _=>some {c with h:=true}

def forwardRun (run : Nat) (rows : List ControlRow) (permission : Bool) : Capture :=
  if (run==1 || admitted rows) && (run==1 || permission) then
    let hit:=(exactClean sourceValue).bind sinkForward
    let pubs:=if run==1 then hit.toList else hit.toList.filterMap (controlC5 guidance)
    ⟨completion::pubs,false,hit.isSome⟩
  else ⟨[],false,false⟩

def backwardRun (rows : List ControlRow) (permission : Bool) : Capture :=
  if admitted rows && permission then
    let offered:=exactClean sinkRequirement
    let pubs:=(offered.bind sourceBackward).toList.filterMap (controlC5 guidance)
    ⟨completion::pubs,offered.any sourceMatches,false⟩
  else ⟨[],false,false⟩

def forwards : Nat → Capture
  | 0=>forwardRun 1 [] false
  | n+1=>
    let previous:=forwards n
    let b:=backwardRun (handoff previous.summaries) previous.sinkPermission
    forwardRun (2*n+3) (handoff b.summaries) b.sourcePermission

theorem the_selected_same_head_exception_is_active_only_at_its_own_head :
    sameHeadMUST sourceValue=false ∧
    exactClean ⟨ap x cleaned .must (some t),false,false⟩=
      some ⟨ap x cleaned .must (some t),false,true⟩ := by decide

theorem a_proper_descendant_cleaner_demotes_uniform_input_without_a_cut :
    exactClean sourceValue=some cleanedSource ∧ cleanedSource.demand=true ∧
    cleanedSource.ap.tail=.must ∧ cleanedSource.ap.path=[] := by decide

theorem backward_requirement_remains_the_same_protected_MAY :
    exactClean sinkRequirement=some cleanedRequirement := by decide

theorem the_object_root_and_a_sibling_are_real_surviving_points :
    exactClean (val (ap x [] .exact (some t)))=some ⟨ap x [] .exact (some t),false,true⟩ ∧
    exactClean (val (ap x [f+1] .exact (some t)))=some ⟨ap x [f+1] .exact (some t),false,true⟩ := by decide

theorem the_selected_point_really_is_removed :
    exactClean (val (ap x cleaned .exact (some t)))=none := by decide

theorem no_field_limit_changes_any_fact_on_this_path (k : Nat) :
    cut k sourceValue=sourceValue ∧ cut k cleanedSource=cleanedSource ∧
    cut k sinkRequirement=sinkRequirement ∧ cut k cleanedRequirement=cleanedRequirement := by
  simp only [cut,sourceValue,cleanedSource,sinkRequirement,cleanedRequirement,val,ap,List.length_nil,Nat.not_lt_zero,ite_false]
  repeat constructor

theorem the_two_directions_really_compute_their_targets :
    (exactClean sourceValue).bind sinkForward=some target ∧
    (exactClean sinkRequirement).bind sourceBackward=some target := by decide

theorem the_cold_forward_and_backward_steps_are_the_old_fixed_control_states :
    forwardRun 1 [] false=forwardFixed ∧
    backwardRun (handoff forwardFixed.summaries) forwardFixed.sinkPermission=backwardFixed := by decide

theorem no_source_or_observation_permission_is_fabricated :
    forwardRun 3 [guidance] false=⟨[],false,false⟩ ∧
    backwardRun [guidance] false=⟨[],false,false⟩ ∧ backwardRun [] true=⟨[],false,false⟩ := by decide

theorem later_forward_recomputes_the_target (n : Nat) :
    forwardRun (n+3) (handoff backwardFixed.summaries) backwardFixed.sourcePermission=forwardFixed := by
  have not1 : (n+3==1)=false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    have same:=of_decide_eq_true hit
    omega
  unfold forwardRun
  rw [not1]
  rfl

theorem every_forward_handoff_repeats (n : Nat) : forwards n=forwardFixed := by
  induction n with
  | zero=>exact the_cold_forward_and_backward_steps_are_the_old_fixed_control_states.1
  | succ n ih=>
    simp only [forwards,ih,the_cold_forward_and_backward_steps_are_the_old_fixed_control_states.2]
    exact later_forward_recomputes_the_target (2*n)

theorem every_backward_handoff_repeats (n : Nat) :
    backwardRun (handoff (forwards n).summaries) (forwards n).sinkPermission=backwardFixed := by
  rw [every_forward_handoff_repeats]
  exact the_cold_forward_and_backward_steps_are_the_old_fixed_control_states.2

theorem no_uncapped_forward_or_backward_frontier_is_empty (n : Nat) :
    handoff (forwards n).summaries=[guidance] ∧
    handoff (backwardRun (handoff (forwards n).summaries) (forwards n).sinkPermission).summaries=[guidance] := by
  rw [every_forward_handoff_repeats,the_cold_forward_and_backward_steps_are_the_old_fixed_control_states.2]
  decide

theorem run3_and_run5_have_the_same_literal_outgoing_demand :
    handoff (forwards 1).summaries=handoff (forwards 2).summaries ∧
    handoff (forwards 2).summaries=[guidance] := by decide

theorem no_NORMAL_target_or_new_path_can_emerge (n : Nat) :
    (forwards n).summaries=[completion,target] ∧
    ((forwards n).summaries.filter fun e=>e.conclusion==.target && !e.demand)=[] := by
  rw [every_forward_handoff_repeats]
  decide

theorem R31_is_not_a_concrete_cleaner_change (old : Value → Value) :
    DisjointCleaner.corrected old cleaned .exact sourceValue=old sourceValue :=
  DisjointCleaner.concrete_cleaner_rows_are_unchanged old cleaned .exact sourceValue (by decide)

theorem NORMAL_FLOW_complement_still_cannot_carry_T :
    marksMeet {ap x [] .star with mx:=[t]} (ap x [] .may (some t))=false := by decide

-- The ordinary empty body derives its own identity; this is not a supplied
-- summary model. Binding into/out of it preserves the input annotations.
def emptyBody (q : Seed) : Value:=⟨q.ap,q.demand,false⟩
def emptySummary : Edge:=normalize (ap p [] .star) (emptyBody ⟨ap p [] .star,false⟩)
theorem the_analyzed_empty_body_computes_its_NORMAL_identity :
    emptySummary=(ap p [] .star,⟨ap p [] .star,false,false⟩) := by decide

def emptyReplay (c : Value) : Value:=c
theorem empty_body_service_cannot_change_the_cleaner_layer_or_shape (c : Value) :
    emptyReplay c=c := rfl

theorem R34_adds_nothing_for_either_actual_uniform_or_MAY_input :
    DirectPossibleReplay.possible emptySummary false ⟨ap p [] .must (some t),true⟩=false ∧
    DirectPossibleReplay.possible emptySummary true ⟨ap p [] .may (some t),true⟩=false := by decide

end DescendantCleanerCycle
