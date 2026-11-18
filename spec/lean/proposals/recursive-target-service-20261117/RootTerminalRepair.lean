import RecursiveWrapperCycle
import TargetSupport
namespace RootTerminalRepair
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open RecursiveTargetSupport
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

structure Frame where
  known : Bool
  target : Bool
  dataDemand : Bool
  rootActive : Bool
  deriving DecidableEq, BEq, Repr

def hasGuide (rows : List UniformRootCleanerCycle.Terminal) : Bool :=
  !(UniformRootCleanerCycle.handoff rows).isEmpty

-- The marking source is rooted at ZERO. It is not a fresh free input when
-- backward control failed to grant permission. All saved records remain.
def forward (n : Nat) (known allowed : Bool) : Frame :=
  if !allowed then ⟨known,false,false,false⟩ else
  let normal:=(RecursiveWrapperCycle.rootSource n).demand==false
  let oldTarget:=hasGuide (RecursiveWrapperCycle.forward n)
  let needs:= !known -- this one observation is the only concrete origin
  let outgoing:=oldTarget && !(retire true true true true needs)
  ⟨known || normal,outgoing,true,true⟩

def backwardPermission (n : Nat) (f : Frame) : Bool :=
  f.target && hasGuide (RecursiveWrapperCycle.backward n)

def history : Nat → Frame
  | 0=>forward 0 false true
  | n+1=>let previous:=history n
         forward (n+1) previous.known (backwardPermission n previous)

theorem cold_run1_is_unchanged : history 0=⟨false,true,true,true⟩ := by decide
theorem run3_retains_its_new_NORMAL_observation_but_does_not_use_it_early :
    history 1=⟨true,true,true,true⟩ := by decide
theorem run5_retires_only_the_covered_root_target_and_keeps_DATA_demand :
    history 2=⟨true,false,true,true⟩ := by decide
theorem run6_has_no_root_Target_entry_permission :
    backwardPermission 2 (history 2)=false := by decide
theorem run7_has_no_outgoing_demand_and_keeps_the_confirmed_observation :
    history 3=⟨true,false,false,false⟩ := by decide

theorem every_later_forward_stays_quiet_without_any_iteration_limit (n : Nat) :
    history (n+3)=⟨true,false,false,false⟩ := by
  induction n with
  | zero=>exact run7_has_no_outgoing_demand_and_keeps_the_confirmed_observation
  | succ n ih=>
    rw [Nat.succ_add,history,ih]
    rfl

-- The native caller policy cannot replay a saved DATA summary without a
-- root offer. Saved-first is kept; the original offered set is simply empty.
theorem saved_replay_on_an_unreached_root_offer_set_has_no_new_effect
    (saved : List α) (apply : α → β → List γ) :
    ([] : List β).flatMap (fun a=>saved.flatMap (fun s=>apply s a))=[] := rfl

theorem an_anonymous_row_with_another_unconfirmed_origin_is_not_retired :
    retire true true true true (false || true)=false := rfl

theorem a_local_NORMAL_hypothesis_does_not_count_as_a_confirmed_root_report :
    confirmed (fun _=>false) (.report 9)=false ∧
    retire true true true true true=false := by decide

end RootTerminalRepair
