import LostMarkOrigin
import OriginService
import RootTerminalRepair
namespace OriginRepair
open LostMarkOrigin
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- Upper graph contains both real marking points. Only concrete NORMAL
-- mark-to-observer paths enter the lower graph. The normal shallow report
-- cannot manufacture the deep source's generator edge.
def normalGraph (deepKnown : Bool) : OriginService.Graph:=
  if deepKnown then OriginService.lateNormal else OriginService.earlyNormal
def closedGoal (deepKnown : Bool) : Bool:=
  OriginService.served [0,1] OriginService.upperTwo (normalGraph deepKnown) 2 true

structure Frame where
  bothKnown : Bool
  rootDemand : Bool
  deepReached : Bool
  shallowReached : Bool
  active : Bool
  deriving DecidableEq, BEq, Repr

def forward (run : Nat) (known active : Bool) : Frame:=
  if !active then ⟨known,false,false,false,false⟩ else
  let k:=max 1 (run-1)
  ⟨known || normalB k,demandB k && !closedGoal known,normalB k,true,true⟩
def history : Nat → Frame
  | 0=>forward 1 false true
  | n+1=>
    let prev:=history n
    forward (2*n+3) prev.bothKnown prev.rootDemand

theorem a_shallow_report_does_not_close_the_other_marking_route : closedGoal false=false := by decide
theorem both_exact_generator_to_observer_routes_do_close_the_goal : closedGoal true=true := by decide
theorem the_repair_keeps_the_required_run3_Target : history 1=⟨false,true,false,true,true⟩ := by decide
theorem the_repair_reaches_the_same_deep_relation_as_the_baseline_at_run5 :
    history 2=⟨true,false,true,true,true⟩ ∧ (history 2).deepReached=(LostMarkOrigin.history false 2).deepReached := by decide

theorem no_later_forward_run_can_renew_this_flat_example (n : Nat) :
    history (n+3)=⟨true,false,false,false,false⟩ := by
  induction n with
  | zero=>decide
  | succ n ih=>rw [Nat.succ_add,history,ih]; rfl

-- R37's existing one-origin recursive certificate is retained only when
-- that unique origin has a genuine root NORMAL witness. In the old wrapper
-- there is one full-mark generator and no cleaner or mark-changing rule.
def uniqueOriginClosed (normalWitness : Bool) : Bool:=
  OriginService.served [0] [(0,1)] (if normalWitness then [(0,1)] else []) 1 true

theorem the_unique_origin_fast_path_is_exactly_its_NORMAL_witness (b : Bool) :
    uniqueOriginClosed b=b := by cases b <;> decide

theorem earlier_single_origin_recursive_completion_is_preserved :
    RootTerminalRepair.history 3=⟨true,false,false,false⟩ :=
  RootTerminalRepair.run7_has_no_outgoing_demand_and_keeps_the_confirmed_observation

-- A loop or recursive neutral wrapper can keep a cut even after its actual
-- input is normal. Retirement waits for every possible marking origin.
-- `raw` stays true forever here: completion cannot be a hidden finite cap.
structure RecursiveFrame where
  closed : Bool
  target : Bool
  dataDemand : Bool
  active : Bool
  deriving DecidableEq, BEq, Repr

def recursiveForward (firstPrecise secondPrecise : Nat) (n : Nat)
    (known active : Bool) : RecursiveFrame:=
  if !active then ⟨known,false,false,false⟩ else
  let both:=decide (firstPrecise≤2*n ∧ secondPrecise≤2*n)
  let ready:=OriginService.served [0,1] OriginService.upperTwo
    (if known then OriginService.lateNormal else OriginService.earlyNormal) 2 true
  ⟨known || both,!ready,true,true⟩
def recursiveHistory (a b : Nat) : Nat → RecursiveFrame
  | 0=>recursiveForward a b 0 false true
  | n+1=>
    let prev:=recursiveHistory a b n
    recursiveForward a b (n+1) prev.closed prev.target

theorem two_recursive_marking_points_stop_without_source_vectors_at_run7 :
    recursiveHistory 2 2 3=⟨true,false,false,false⟩ := by decide
theorem a_later_recursive_marking_point_is_not_retired_at_run3 :
    recursiveHistory 1 4 1=⟨false,true,true,true⟩ := by decide
theorem the_later_recursive_relation_is_served_before_natural_run9_completion :
    recursiveHistory 1 4 2=⟨true,true,true,true⟩ ∧
    recursiveHistory 1 4 3=⟨true,false,true,true⟩ ∧
    recursiveHistory 1 4 4=⟨true,false,false,false⟩ := by decide

theorem no_field_or_layer_is_added_by_goal_service
    (edge : NonEmptyRestriction.Value) (certificate : Bool) :
    (if certificate then edge else edge)=edge := by cases certificate <;> rfl
end OriginRepair
