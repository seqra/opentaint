import UniformCleanerSpine
namespace NestedCleanerProtocol
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open UniformRootCleanerCycle UniformRootCleanerPolicy
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

def cleaned : Path:=[f,g]

/-- Current concrete ancestor PART row, on the root facts in this trace.
    For two fields, the existing one-field MUST special case is false.
    It is the same row for selected ALL/BELOW and RemoveAll/ALL. -/
def oldDeep (c : Value) : Option Value :=
  if c.ap.base != x || c.ap.mark != some t then some c
  else if c.ap.path.isEmpty && c.ap.tail != .exact then
    some {c with demand:=true,h:=true,ap:={c.ap with tail:=if c.ap.tail==.star then .may else c.ap.tail}}
  else some {c with h:=true}

def oldForward (run : Nat) (rows : List ControlRow) (permission : Bool) : Capture :=
  if (run==1 || admitted rows) && (run==1 || permission) then
    let hit:=(oldDeep sourceValue).bind sinkForward
    let pubs:=if run==1 then hit.toList else hit.toList.filterMap (controlC5 guidance)
    ⟨completion::pubs,false,hit.isSome⟩ else ⟨[],false,false⟩
def oldBackward (rows : List ControlRow) (permission : Bool) : Capture :=
  if admitted rows && permission then
    let offered:=oldDeep sinkRequirement
    let pubs:=(offered.bind sourceBackward).toList.filterMap (controlC5 guidance)
    ⟨completion::pubs,offered.any sourceMatches,false⟩ else ⟨[],false,false⟩

theorem the_one_field_special_case_is_not_applicable :
    cleaned.length=2 ∧ sourceValue.ap.path.length=0 ∧
    cleaned.length≠sourceValue.ap.path.length+1 ∧
    dropHead sourceValue.ap.path cleaned=some [f,g] := by decide

theorem current_rows_really_equal_the_proved_recurrent_PART_rows :
    oldDeep sourceValue=some cleanedSource ∧ oldDeep sinkRequirement=some cleanedRequirement := by decide

theorem the_full_control_transfer_is_the_same_as_the_first_counterexample
    (run : Nat) (rows : List ControlRow) (permission : Bool) :
    oldForward run rows permission=DescendantCleanerCycle.forwardRun run rows permission ∧
    oldBackward rows permission=DescendantCleanerCycle.backwardRun rows permission := by
  constructor <;> rfl

def oldForwards : Nat → Capture
 | 0=>oldForward 1 [] false
 | n+1=>
   let previous:=oldForwards n
   let back:=oldBackward (handoff previous.summaries) previous.sinkPermission
   oldForward (2*n+3) (handoff back.summaries) back.sourcePermission

theorem old_handoffs_equal_the_first_counterexample_for_every_uncapped_pair (n : Nat) :
    oldForwards n=DescendantCleanerCycle.forwards n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [oldForwards,DescendantCleanerCycle.forwards,ih]
    rfl

theorem the_nested_cleaner_has_nonempty_demand_forever (n : Nat) :
    handoff (oldForwards n).summaries=[guidance] := by
  rw [old_handoffs_equal_the_first_counterexample_for_every_uncapped_pair]
  exact (DescendantCleanerCycle.no_uncapped_forward_or_backward_frontier_is_empty n).1

-- Runtime instantiation of the precise spatial proof. P and all headers
-- stay fixed except the ordinary result path, E and existing H producer.
def valueOf (input : Value) (r : UniformCleanerSpine.Region) : Value :=
  let output : Ap:={input.ap with path:=input.ap.path++r.path,tail:=(if r.exact then .exact else .must),e:=r.holes}
  {input with ap:=output,h:=true}

def repairedValues (run k : Nat) (reach : UniformCleanerSpine.Reach) : List Value :=
  if run==1 then (oldDeep sourceValue).toList
  else ((UniformCleanerSpine.regions reach cleaned sourceValue.ap.e).map (valueOf sourceValue)).map (cut k)

def observe (c : Value) : Option SinkTarget :=
  if c.ap.base==x && c.ap.mark==some t then
    some (if c.demand then .demand else .normal sinkId) else none

def targets (run k : Nat) (reach : UniformCleanerSpine.Reach) : List SinkTarget :=
  ((repairedValues run k reach).filterMap observe).eraseDups

theorem the_repair_keeps_run1_unchanged :
    repairedValues 1 1 .all=[cleanedSource] ∧ targets 1 1 .all=[.demand] := by decide

theorem run2_keeps_the_same_real_backward_source_permission :
    oldBackward (nextDemand (targets 1 1 .all)) true=backwardFixed := by decide

theorem whole_subtree_run3_has_only_NORMAL_precise_residuals :
    repairedValues 3 2 .all=
      [⟨{ap x [] .must (some t) with e:=[f]},false,true⟩,
       ⟨{ap x [f] .must (some t) with e:=[g]},false,true⟩] := by decide

theorem below_run3_keeps_its_additional_NORMAL_point :
    (repairedValues 3 2 .below).all (fun c=> !c.demand)=true ∧
    (repairedValues 3 2 .below).any (fun c=>decide (c.ap.path=cleaned ∧ c.ap.tail=.exact))=true := by decide

theorem both_repaired_modes_have_NORMAL_targets_and_empty_handoff_at_run3 :
    targets 3 2 .all=[.normal sinkId] ∧ nextDemand (targets 3 2 .all)=[] ∧
    targets 3 2 .below=[.normal sinkId] ∧ nextDemand (targets 3 2 .below)=[] := by decide

theorem both_repaired_modes_respect_global_limit_two :
    (repairedValues 3 2 .all ++ repairedValues 3 2 .below).all
      (fun c=>decide (c.ap.path.length≤2))=true := by decide

theorem a_real_later_cut_still_becomes_uncertain_instead_of_NORMAL :
    (repairedValues 3 1 .below).any (fun c=>c.demand && c.ap.tail==.ne)=true := by decide

def later (reach : UniformCleanerSpine.Reach) : Nat → List SinkTarget
 | 0=>targets 3 2 reach
 | n+1=>later reach n

theorem neither_repaired_case_can_restart_after_natural_completion
    (reach : UniformCleanerSpine.Reach) (n : Nat) :
    later reach n=[.normal sinkId] ∧ nextDemand (later reach n)=[] := by
  induction n with
  | zero=>cases reach <;> decide
  | succ _ ih=>exact ih
end NestedCleanerProtocol
