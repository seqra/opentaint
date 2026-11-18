import RecursiveWrapperCycle
import TargetSupport
namespace LostMarkOrigin
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- Labels belong only to the proof/test relation. They are not extra AP
-- marks or source identities on production facts.
inductive MarkPoint where | shallow | deep
  deriving DecidableEq, BEq, Repr

def observerId : Nat:=9
def sourceB : Value:=val (ap p [f,f,f,f] .exact (some t))
def readOne (c : Value) : Option Value:=
  (OverwriteReplay.move [f] [] c.ap).map fun next=>{next with demand:=next.demand || c.demand,h:=c.h}
def readThree (c : Value) : Option Value:=((some c).bind readOne).bind readOne |>.bind readOne
def resultB (k : Nat) : Option Value:=readThree (cut k sourceB)
def normalB (k : Nat) : Bool:=(resultB k).any fun c=>
  !c.demand && c.ap.path==[f] && c.ap.tail==.exact && c.ap.mark==some t
def demandB (k : Nat) : Bool:=(resultB k).any (·.demand)

theorem run1_deep_path_is_only_a_candidate :
    resultB 1=some (val (ap p [] .may (some t)) true) ∧ normalB 1=false ∧ demandB 1=true := by decide
theorem run3_deep_path_is_still_only_a_candidate :
    resultB 2=some (val (ap p [] .may (some t)) true) ∧ normalB 2=false ∧ demandB 2=true := by decide
theorem run5_can_track_the_deep_mark_to_the_distinct_observed_field :
    resultB 4=some (val (ap p [f] .exact (some t))) ∧ normalB 4=true ∧ demandB 4=false := by decide

-- The other branch assigns T at r.g.$. It is precise from run-1 and
-- satisfies the same CM(r.MAY,T), but not the deep point's r.f relation.
def shallowResult : Value:=val (ap p [g] .exact (some t))
theorem the_shallow_NORMAL_fact_is_not_the_deep_fact :
    shallowResult.ap.path=[g] ∧ shallowResult.ap.path≠[f] ∧ shallowResult.demand=false := by decide

-- Backward CM(r.MAY,T) crosses the same three ordinary field transfers.
-- Its result includes the full declared deep source at every cold limit.
def pushOne (k : Nat) (c : Value) : Value:=cut k {c with ap:={c.ap with path:=f::c.ap.path}}
def backThree (k : Nat) : Value:=
  let request:=val (ap p [] .may (some t)) true
  pushOne k (pushOne k (pushOne k request))
theorem both_required_backward_source_permissions_are_real :
    (backThree 1).ap=ap p [f] .ne (some t) ∧
    (backThree 3).ap=ap p [f,f,f] .may (some t) ∧
    admits (backThree 1).ap.tail [] [f,f,f]=true ∧
    admits (backThree 3).ap.tail [] [f]=true := by decide

structure Frame where
  knownReport : Bool
  rootDemand : Bool
  deepReached : Bool
  shallowReached : Bool
  active : Bool
  deriving DecidableEq, BEq, Repr

def forward (useR37 : Bool) (run : Nat) (known active : Bool) : Frame:=
  if !active then ⟨known,false,false,false,false⟩ else
  let k:=max 1 (run-1)
  let rawDemand:=demandB k
  -- Both witness kinds have report id 9. R37 tests only that id.
  let needs:= !known
  let omitted:=useR37 && RecursiveTargetSupport.retire true true true true needs
  ⟨true,rawDemand && !omitted,normalB k,true,true⟩

def history (useR37 : Bool) : Nat → Frame
 | 0=>forward useR37 1 false true
 | n+1=>
   let previous:=history useR37 n
   -- In this void root, local facts produce no DATA summaries.
   -- Without the root Target, ordinary admission supplies no next seed.
   forward useR37 (2*n+3) previous.knownReport previous.rootDemand

theorem baseline_cold_run1_keeps_both_marking_routes_live :
    history false 0=⟨true,true,false,true,true⟩ := by decide
theorem baseline_run3_keeps_the_deep_refinement_permission :
    history false 1=⟨true,true,false,true,true⟩ := by decide
theorem baseline_run5_completes_with_both_distinct_marking_relations :
    history false 2=⟨true,false,true,true,true⟩ := by decide
theorem R37_run3_completes_without_the_deep_relation :
    history true 1=⟨true,false,false,true,true⟩ := by decide

theorem every_later_R37_run_has_no_recovery_without_an_iteration_limit (n : Nat) :
    history true (n+2)=⟨true,false,false,false,false⟩ := by
  induction n with
  | zero=>decide
  | succ n ih=>rw [Nat.succ_add,history,ih]; rfl

theorem report_count_equivalence_does_not_imply_reachability_equivalence :
    (history false 2).knownReport=(history true 1).knownReport ∧
    (history false 2).deepReached=true ∧ (history true 1).deepReached=false := by decide

theorem the_old_one_bit_certificate_really_covers_both_report_origins :
    RecursiveTargetSupport.fullOriginNeeds (fun id=>decide (id=observerId))
      [.report observerId,.report observerId]=false := by decide

end LostMarkOrigin
