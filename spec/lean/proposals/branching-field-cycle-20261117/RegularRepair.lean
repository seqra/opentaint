import CycleRules
namespace RegularRepair
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 800000000

-- NoRoute is available only after a completed finite structural check.
-- The frozen next-forward goal set can use it without a NORMAL report.
structure Frame where
  closedGoal : Bool
  target : Bool
  data : Bool
  sourcePermission : Bool
  normalReport : Bool
  deriving BEq, DecidableEq, Repr

def forward (_n : Nat) (known permitted : Bool) : Frame:=
  if !permitted then ⟨known,false,false,false,false⟩
  else ⟨RegularCertificate.certifiesEmpty RegularCertificate.writer RegularCertificate.reader,
    !known,true,true,false⟩
def history : Nat → Frame
 | 0=>forward 0 false true
 | n+1=>let prev:=history n
        forward (n+1) prev.closedGoal prev.target

theorem run1_keeps_its_full_closure_and_normal_stop_policy :
    history 0=⟨true,true,true,true,false⟩ := by decide
theorem run3_removes_only_the_certified_impossible_root_Target :
    history 1=⟨true,false,true,true,false⟩ := by decide
theorem run5_has_no_root_offer_or_renewed_DATA_demand :
    history 2=⟨true,false,false,false,false⟩ := by decide
theorem every_later_forward_run_stays_quiet_without_a_hard_limit (n : Nat) :
    history (n+2)=⟨true,false,false,false,false⟩ := by
  induction n with
  | zero=>exact run5_has_no_root_offer_or_renewed_DATA_demand
  | succ n ih=>rw [Nat.succ_add,history,ih]; rfl

-- Both alternatives are certificates about the SAME source/mark/observer
-- pair. Every possible source needs one of them; another NORMAL ID is not
-- a replacement for the all-source test.
def allServed (pairs : List (Bool × Bool)) : Bool:=pairs.all fun (normal,noRoute)=>normal || noRoute
theorem one_unserved_source_keeps_the_goal : allServed [(false,true),(false,false)]=false := by decide
theorem two_different_kinds_of_valid_service_can_close_one_goal :
    allServed [(false,true),(true,false)]=true := by decide

-- Comparative soundness is independent of how long the witness word is.
-- The grammar compiler and complete-slice map are explicit obligations.
theorem a_valid_mark_to_observer_relation_cannot_be_pruned
    (validW : gw.all (RegularCertificate.validatesClause w)=true)
    (validR : gr.all (RegularCertificate.validatesClause r)=true)
    (left : RegularCertificate.Derives gw w.start word)
    (right : RegularCertificate.Derives gr r.start word)
    (empty : RegularCertificate.certifiesEmpty w r=true) : False :=
  RegularCertificate.all_true_ordinary_routes_survive_certified_pruning validW validR left right empty

-- Full current owner-model replay, including source permission and Target.
-- This supplies finite cold validation separately from the generic proof.
def scan (branch positive : Bool) : Nat × Bool × Bool:=Id.run do
  let mut prev : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
  let mut allowed:=true
  let mut known:=false
  let mut normalSeen:=false
  let mut fixed:=true
  for index in List.range 17 do
    let run:=index+1
    let (next,ready,_):=PairedReference.step run prev branch positive allowed
    fixed:=fixed && ready
    let values:=next.data.offers[2]!
    if run%2==1 then
      let normal:=values.any fun a=> !a.demand && PairedReference.observed a
      let raw:=values.any fun a=>a.demand && PairedReference.observed a
      let target:=raw && !known
      let noRoute:=RegularCertificate.certifiesEmpty RegularCertificate.writer
        (if positive then RegularCertificate.overlapReader else RegularCertificate.reader)
      known:=known || noRoute || normal
      normalSeen:=normalSeen || normal
      if next.rows.all List.isEmpty && !target then return (run,normalSeen,fixed)
      allowed:=target
    else
      allowed:=allowed && values.any (fun a=>PairedReference.observed a)
    prev:=next
  return (0,normalSeen,fixed)

def main : IO Unit:=do
  for branch in [false,true] do
    for positive in [false,true] do
      IO.println s!"REGULAR_REPAIR branch={branch} positive={positive} result={scan branch positive}"
end RegularRepair
