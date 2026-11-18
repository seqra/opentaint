import NestedWriteStable
import NestedWriteConcrete
import TargetZeroKernel

namespace NestedWriteControl
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE
open NestedSavedReplayCycle NestedColdMachine OverwriteReplay NestedWriteStable NestedWriteCold
open TargetZeroKernel
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def current (backward : Bool) : List Edge := if backward then state6.current[0]! else state5.current[0]!
def reply (run limit : Nat) (backward : Bool) : List Offered :=
  OverwriteReplay.offer run limit (frontier backward) saved (current backward) (actual backward)

theorem actual_forward_base : reply 5 4 false = [need] := by decide
theorem actual_backward_base : reply 6 5 true = [need] := by decide

theorem all_plans_stable (k : Nat) (backward : Bool) :
    (frontier backward).map (fun row => plan (2*k+(if backward then 6 else 5))
      (2*k+(if backward then 5 else 4)) backward (frontier backward)
      (OverwriteReplay.views backward saved) row (actual backward)) =
    (frontier backward).map (fun row => plan (if backward then 6 else 5)
      (if backward then 5 else 4) backward (frontier backward)
      (OverwriteReplay.views backward saved) row (actual backward)) :=
  List.map_congr_left (fun row hr => plan_stable k backward row hr)

theorem actual_reply_stable (k : Nat) (backward : Bool) :
    reply (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward = [need] := by
  have pf : (2*k+5)%2 = 1 := by omega
  have pb : (2*k+6)%2 = 0 := by omega
  have r5 : 2*k+5 ≠ 1 := by omega
  have r6 : 2*k+6 ≠ 1 := by omega
  have l0 : ¬2*k+4<0 := by omega
  have l1 : ¬2*k+4<1 := by omega
  have m0 : ¬2*k+5<0 := by omega
  have m1 : ¬2*k+5<1 := by omega
  have plansF := all_plans_stable k false
  have plansB := all_plans_stable k true
  simp only [Bool.false_eq_true,ite_false,ite_true] at plansF plansB
  unfold reply OverwriteReplay.offer
  cases backward <;> simp only [Bool.false_eq_true,ite_false,ite_true,pf,pb,
    show ((1 : Nat)==0) = false from rfl,show ((0 : Nat)==0) = true from rfl]
  all_goals first | rw [plansF] | rw [plansB]
  all_goals simp [frontier,rowsF,rowsB,saved,current,actual,NestedWriteCold.source,
    state5,state6,OverwriteReplay.views,OverwriteReplay.apply,OverwriteReplay.reverseEdge,OverwriteReplay.union,
    plan,baseFamily,fields,compatibleChild,emit,emitBase,completeFamily,primary,atHead,selector,marksOK,admits,seed,probe,legalSeed,
    OverwriteReplay.values,OverwriteReplay.valueCovered,OverwriteReplay.valueKey,OverwriteReplay.apKey,executable,normalAp,point,ap,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,NestedColdMachine.edgeKey,pairKey,
    p,ret,f,g,t,need,cutOffer,cut,val,List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,
    List.getElem!_eq_getElem?_getD,r5,r6,l0,l1,m0,m1,
    NonEmptyPolicy.instBEqOffered.beq,NonEmptyPolicy.instBEqAp.beq,NonEmptyPolicy.instBEqTail.beq,NonEmptyPolicy.instBEqSeed.beq,
    NonEmptyPolicy.Tail.ctorIdx,Option.instBEq.beq,List.beq,BEq.beq]

def observation (a : Offered) : Summary := forwardSinkTarget 0 .zero
  (if a.demand then .demand else .normal) 0
def rootDemand := handoffTarget 0 .zero
def producerPermission : Bool := admits need.ap.tail need.ap.e [g] && need.ap.mark == some t
def producerHit : Option Summary := backwardGenEventTarget .actualReverseTransfer
  ⟨.zero,.ap .a⟩ producerPermission true 0 .zero

theorem the_actual_marked_packet_is_repeated_at_every_boundary (k : Nat) :
    reply (2*k+5) (2*k+4) false = [need] ∧
    reply (2*k+6) (2*k+5) true = [need] := by
  exact ⟨actual_reply_stable k false,actual_reply_stable k true⟩

theorem every_forward_run_has_anonymous_target (k : Nat) :
    (reply (2*k+5) (2*k+4) false).map observation = [targetSummary 0 .zero] := by
  have h := actual_reply_stable k false
  change reply (2*k+5) (2*k+4) false = [need] at h
  rw [h]
  decide

theorem every_backward_run_reaches_the_real_mark_producer :
    producerPermission = true ∧ producerHit = some (targetSummary 0 .zero) := by decide

theorem paired_control_c5_and_handoff_stay_live :
    c5Restrict exactEntry exactExit rootDemand (targetSummary 0 .zero) = some (targetSummary 0 .zero) ∧
    producerHit.bind (c5Restrict exactEntry exactExit rootDemand) = some (targetSummary 0 .zero) ∧
    emittedZero .restricted [rootDemand] 0 .zero = [.zero] ∧
    selectedTargetHandoff (targetSummary 0 .zero) = some rootDemand ∧
    continuationRelevant (targetSummary 0 .zero) = true := by decide

theorem no_confirmed_observation_is_manufactured (k : Nat) :
    collectReports [0] ((reply (2*k+5) (2*k+4) false).map observation) = [] := by
  rw [every_forward_run_has_anonymous_target]
  decide

theorem nontermination_without_any_iteration_limit (k : Nat) :
    (afterForwardPairs k).length = 4 ∧
    (advance (2*k+5) (2*k+4) false (afterForwardPairs k)).length = 2 ∧
    (reply (2*k+5) (2*k+4) false).map observation = [targetSummary 0 .zero] ∧
    producerHit = some (targetSummary 0 .zero) ∧
    selectedTargetHandoff (targetSummary 0 .zero) = some rootDemand ∧
    continuationRelevant (targetSummary 0 .zero) = true := by
  exact ⟨(no_later_forward_pair_has_empty_demand k).1,
    (no_later_forward_pair_has_empty_demand k).2,
    every_forward_run_has_anonymous_target k,
    every_backward_run_reaches_the_real_mark_producer.2,
    paired_control_c5_and_handoff_stay_live.2.2.2.1,
    paired_control_c5_and_handoff_stay_live.2.2.2.2⟩

end NestedWriteControl
#print axioms NestedWriteControl.actual_forward_base
#print axioms NestedWriteControl.actual_backward_base
#print axioms NestedWriteControl.all_plans_stable
#print axioms NestedWriteControl.actual_reply_stable
#print axioms NestedWriteControl.the_actual_marked_packet_is_repeated_at_every_boundary
#print axioms NestedWriteControl.every_forward_run_has_anonymous_target
#print axioms NestedWriteControl.every_backward_run_reaches_the_real_mark_producer
#print axioms NestedWriteControl.paired_control_c5_and_handoff_stay_live
#print axioms NestedWriteControl.no_confirmed_observation_is_manufactured
#print axioms NestedWriteControl.nontermination_without_any_iteration_limit
