import OverwriteWitnesses

namespace OverwriteStable
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay OverwriteWitnesses
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def stableRows : List Row := [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩]
def stableSaved : List Saved := [⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]
def domainF := [need,NestedSavedReplayCycle.source 0,NestedSavedReplayCycle.source 1,NestedSavedReplayCycle.source 2]
def domainB := [need]
def publications := state9.current[0]!

/-- Every child current-demand set is empty. Thus the complete wrapper
    result comes from original saved replay. Its real E disables delegation. -/
def cell (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Edge :=
  let norms := OverwriteReplay.views backward stableSaved
  let pl := plan run limit backward stableRows norms row a
  pl.flatMap fun (q,_) => norms.filterMap fun (e,inside) => do
    let c ← OverwriteReplay.apply inside e ⟨q.ap,false⟩
    let v := cutOffer limit c
    OverwriteReplay.pub run limit norms row (pl.map (·.1)) q (val {v.ap with base := ret} v.demand)

def packet (run limit : Nat) (backward : Bool) (domain : List Offered) : List Edge :=
  unique OverwriteReplay.edgeKey
    (stableRows.flatMap fun row => domain.flatMap fun a => cell run limit backward row a)

theorem mature_forward_base : packet 9 8 false domainF = publications := by decide
theorem mature_backward_base : packet 10 9 true domainB = publications := by decide

theorem full_handoff_is_the_same_four_rows :
    OverwriteReplay.outputRows ⟨[[],[]],[publications,[]],[[],[],[],[]]⟩ = rows9 := by decide

theorem child_has_no_current_data_demand : rows9[1]! = [] := by decide

theorem ordinary_writes_disable_replay_pruning (q : Ap) (mask : List Nat)
    (a : Offered) (e : Edge × Bool) (he : e ∈ OverwriteReplay.views false stableSaved) :
    PreparedChildReplay.delegated q mask e.1 e.2 a = false := by
  have all : (OverwriteReplay.views false stableSaved).all
      (fun x => decide (x.1.2.ap.e = [g])) = true := by decide
  have ex : e.1.2.ap.e = [g] := of_decide_eq_true (List.all_eq_true.mp all e he)
  simp [PreparedChildReplay.delegated,ex]


theorem plan_stable (n : Nat) (backward : Bool) (row : Row) (a : Offered)
    (hr : row ∈ stableRows) (ha : a ∈ (if backward then domainB else domainF)) :
    plan (n+9) (n+8) backward stableRows (OverwriteReplay.views backward stableSaved) row a =
      plan 9 8 backward stableRows (OverwriteReplay.views backward stableSaved) row a := by
  have l0 : ¬n+8<0 := by omega
  have l1 : ¬n+8<1 := by omega
  have l2 : ¬n+8<2 := by omega
  have l3 : ¬n+8<3 := by omega
  have l4 : ¬n+8<4 := by omega
  have l5 : ¬n+8<5 := by omega
  have l6 : ¬n+8<6 := by omega
  have l7 : ¬n+8<7 := by omega
  have l8 : ¬n+8<8 := by omega
  have b1 : 1 ≤ n+8 := by omega
  have b2 : 2 ≤ n+8 := by omega
  have b3 : 3 ≤ n+8 := by omega
  have b4 : 4 ≤ n+8 := by omega
  have b5 : 5 ≤ n+8 := by omega
  have b6 : 6 ≤ n+8 := by omega
  have b7 : 7 ≤ n+8 := by omega
  have b8 : 8 ≤ n+8 := by omega
  have nz : n+8 ≠ 0 := by omega
  have r1 : n+9 ≠ 1 := by omega
  have r2 : n+9 ≠ 2 := by omega
  have hr' : row ∈ [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩] := by
    have same : stableRows = [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩] := by decide
    rw [same] at hr; exact hr
  have ha' : a ∈ (if backward then [need] else
      [need,NestedSavedReplayCycle.source 0,NestedSavedReplayCycle.source 1,NestedSavedReplayCycle.source 2]) := by
    cases backward <;> simpa [domainF,domainB,state9,state10,NestedSavedReplayCycle.source,need,List.replicate_succ,List.replicate_zero] using ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
  rcases hr' with h | h | h | h <;> subst row
  all_goals cases backward <;> simp only [Bool.false_eq_true,ite_false,ite_true,
      List.mem_cons,List.not_mem_nil,or_false] at ha'
  all_goals (try (rcases ha' with h | h | h | h <;> subst a))
  all_goals (try subst a)
  all_goals simp [plan,baseFamily,fields,stableRows,rows9,stableSaved,saved9,
    OverwriteReplay.views,OverwriteReplay.apply,OverwriteReplay.reverseEdge,OverwriteReplay.union,
    OverwriteReplay.pub,OverwriteReplay.normalsCover,normalAp,
    NestedSavedReplayCycle.source,need,point,emit,emitBase,completeFamily,primary,atHead,selector,
    marksOK,admits,seed,probe,legalSeed,ap,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,
    List.replicate_succ,List.replicate_zero,p,ret,f,g,cutOffer,restricted,normalize,
    intersectExit,marksMeet,exactAt,cut,val,List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.getElem!_eq_getElem?_getD,
    nz,r1,r2,l0,l1,l2,l3,l4,l5,l6,l7,l8,b1,b2,b3,b4,b5,b6,b7,b8]


























theorem basePlanF0_0 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF0_1 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [] .star⟩) (⟨point p [f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF0_2 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [] .star⟩) (⟨point p [f,f,f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF0_3 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [] .star⟩) (⟨point p [f,f,f,f,f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF1_0 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[f]),(⟨point p [f,f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanF1_1 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [] .star⟩) (⟨point p [f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,g] .star,false⟩,[])] := by decide

theorem basePlanF1_2 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [] .star⟩) (⟨point p [f,f,f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanF1_3 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [] .star⟩) (⟨point p [f,f,f,f,f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanF2_0 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [f] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF2_1 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [f] .star⟩) (⟨point p [f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF2_2 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [f] .star⟩) (⟨point p [f,f,f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF2_3 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [] .may,point ret [f] .star⟩) (⟨point p [f,f,f,f,f,g] .must (some t),false⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanF3_0 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [f] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[f]),(⟨point p [f,f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanF3_1 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [f] .star⟩) (⟨point p [f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,g] .star,false⟩,[])] := by decide

theorem basePlanF3_2 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [f] .star⟩) (⟨point p [f,f,f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanF3_3 : plan 9 8 false stableRows (OverwriteReplay.views false stableSaved) (⟨point p [f] .may,point ret [f] .star⟩) (⟨point p [f,f,f,f,f,g] .must (some t),false⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanB0_0 : plan 9 8 true stableRows (OverwriteReplay.views true stableSaved) (⟨point p [] .may,point ret [] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanB1_0 : plan 9 8 true stableRows (OverwriteReplay.views true stableSaved) (⟨point p [f] .may,point ret [] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[f]),(⟨point p [f,f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem basePlanB2_0 : plan 9 8 true stableRows (OverwriteReplay.views true stableSaved) (⟨point p [] .may,point ret [f] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanB3_0 : plan 9 8 true stableRows (OverwriteReplay.views true stableSaved) (⟨point p [f] .may,point ret [f] .star⟩) (⟨point p [] .may (some t),true⟩) = [(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[f]),(⟨point p [f,f] .exact,false⟩,[]),(⟨point p [f,f] .star,false⟩,[])] := by decide

theorem cell_stable (n : Nat) (backward : Bool) (row : Row) (a : Offered)
    (hr : row ∈ stableRows) (ha : a ∈ (if backward then domainB else domainF)) :
    cell (n+9) (n+8) backward row a = cell 9 8 backward row a := by
  simp only [cell,plan_stable n backward row a hr ha]
  have l0 : ¬n+8<0 := by omega
  have l1 : ¬n+8<1 := by omega
  have l2 : ¬n+8<2 := by omega
  have l3 : ¬n+8<3 := by omega
  have l4 : ¬n+8<4 := by omega
  have l5 : ¬n+8<5 := by omega
  have l6 : ¬n+8<6 := by omega
  have l7 : ¬n+8<7 := by omega
  have l8 : ¬n+8<8 := by omega
  have b1 : 1 ≤ n+8 := by omega
  have b2 : 2 ≤ n+8 := by omega
  have b3 : 3 ≤ n+8 := by omega
  have b4 : 4 ≤ n+8 := by omega
  have b5 : 5 ≤ n+8 := by omega
  have b6 : 6 ≤ n+8 := by omega
  have b7 : 7 ≤ n+8 := by omega
  have b8 : 8 ≤ n+8 := by omega
  have nz : n+8 ≠ 0 := by omega
  have r1 : n+9 ≠ 1 := by omega
  have r2 : n+9 ≠ 2 := by omega
  have hr' : row ∈ [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩] := by
    have same : stableRows = [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩] := by decide
    rw [same] at hr; exact hr
  have ha' : a ∈ (if backward then [need] else
      [need,NestedSavedReplayCycle.source 0,NestedSavedReplayCycle.source 1,NestedSavedReplayCycle.source 2]) := by
    cases backward <;> simpa [domainF,domainB,state9,state10,NestedSavedReplayCycle.source,need,List.replicate_succ,List.replicate_zero] using ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
  rcases hr' with h | h | h | h <;> subst row
  all_goals cases backward <;> simp only [Bool.false_eq_true,ite_false,ite_true,
      List.mem_cons,List.not_mem_nil,or_false] at ha'
  all_goals (try (rcases ha' with h | h | h | h <;> subst a))
  all_goals (try subst a)
  all_goals simp only [show need = (⟨point p [] .may (some t),true⟩ : Offered) from rfl,
    show NestedSavedReplayCycle.source 0 = (⟨point p [f,g] .must (some t),false⟩ : Offered) from rfl,
    show NestedSavedReplayCycle.source 1 = (⟨point p [f,f,f,g] .must (some t),false⟩ : Offered) from rfl,
    show NestedSavedReplayCycle.source 2 = (⟨point p [f,f,f,f,f,g] .must (some t),false⟩ : Offered) from rfl]
  all_goals simp only [basePlanF0_0,basePlanF0_1,basePlanF0_2,basePlanF0_3,basePlanF1_0,basePlanF1_1,basePlanF1_2,basePlanF1_3,basePlanF2_0,basePlanF2_1,basePlanF2_2,basePlanF2_3,basePlanF3_0,basePlanF3_1,basePlanF3_2,basePlanF3_3,basePlanB0_0,basePlanB1_0,basePlanB2_0,basePlanB3_0]
  all_goals simp [plan,baseFamily,fields,stableRows,rows9,stableSaved,saved9,
    OverwriteReplay.views,OverwriteReplay.apply,OverwriteReplay.reverseEdge,OverwriteReplay.union,
    OverwriteReplay.pub,OverwriteReplay.normalsCover,normalAp,
    NestedSavedReplayCycle.source,need,point,emit,emitBase,completeFamily,primary,atHead,selector,
    marksOK,admits,seed,probe,legalSeed,ap,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,
    List.replicate_succ,List.replicate_zero,p,ret,f,g,cutOffer,restricted,normalize,
    intersectExit,marksMeet,exactAt,cut,val,List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.getElem!_eq_getElem?_getD,
    nz,r1,r2,l0,l1,l2,l3,l4,l5,l6,l7,l8,b1,b2,b3,b4,b5,b6,b7,b8]


theorem complete_packet_stable (n : Nat) (backward : Bool) :
    packet (n+9) (n+8) backward (if backward then domainB else domainF) = publications := by
  have same := flatMap_equal_on_members stableRows
    (fun row => (if backward then domainB else domainF).flatMap fun a => cell (n+9) (n+8) backward row a)
    (fun row => (if backward then domainB else domainF).flatMap fun a => cell 9 8 backward row a) (by
      intro row hr
      apply flatMap_equal_on_members
      intro a ha
      exact cell_stable n backward row a hr ha)
  have equal : packet (n+9) (n+8) backward (if backward then domainB else domainF) =
      packet 9 8 backward (if backward then domainB else domainF) := congrArg
      (unique OverwriteReplay.edgeKey) same
  rw [equal]
  cases backward
  · exact mature_forward_base
  · decide

def advance (run limit : Nat) (rows : List Row) : List Row :=
  let backward := run % 2 == 0
  let edges := unique OverwriteReplay.edgeKey
    (rows.flatMap fun row => (if backward then domainB else domainF).flatMap
      fun a => cell run limit backward row a)
  (OverwriteReplay.outputRows ⟨[[],[]],[edges,[]],[[],[],[],[]]⟩)[0]!

theorem every_later_handoff_repeats (n : Nat) :
    advance (n+9) (n+8) stableRows = stableRows := by
  unfold advance
  change (OverwriteReplay.outputRows
    ⟨[[],[]],[packet (n+9) (n+8) ((n+9)%2==0)
      (if (n+9)%2==0 then domainB else domainF),[]],[[],[],[],[]]⟩)[0]! = stableRows
  rw [complete_packet_stable]
  decide

def repeatFromRun9 : Nat → List Row
  | 0 => stableRows
  | n+1 => advance (n+9) (n+8) (repeatFromRun9 n)

theorem uncapped_recurrence (n : Nat) : repeatFromRun9 n = stableRows := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [repeatFromRun9,ih,every_later_handoff_repeats]

theorem no_later_handoff_has_empty_demand (n : Nat) : (repeatFromRun9 n).length = 4 := by
  rw [uncapped_recurrence]
  decide

theorem every_refinement_frontier_has_the_same_root_may (n : Nat) :
    (⟨point p [] .may,point ret [] .star⟩ : Row) ∈ repeatFromRun9 n := by
  rw [uncapped_recurrence]
  simp [stableRows]

theorem cold_states_reach_this_stationary_saved_basis :
    rows9 = [stableRows,[]] ∧ rows10 = rows9 ∧ rows11 = rows9 ∧
    saved9 = [stableSaved,stableSaved] ∧ saved10 = saved9 ∧ saved11 = saved9 := by decide


end OverwriteStable
#print axioms OverwriteStable.mature_forward_base
#print axioms OverwriteStable.mature_backward_base
#print axioms OverwriteStable.full_handoff_is_the_same_four_rows
#print axioms OverwriteStable.child_has_no_current_data_demand
#print axioms OverwriteStable.ordinary_writes_disable_replay_pruning

#print axioms OverwriteStable.plan_stable

#print axioms OverwriteStable.cell_stable


#print axioms OverwriteStable.complete_packet_stable
#print axioms OverwriteStable.every_later_handoff_repeats
#print axioms OverwriteStable.uncapped_recurrence
#print axioms OverwriteStable.no_later_handoff_has_empty_demand
#print axioms OverwriteStable.every_refinement_frontier_has_the_same_root_may
#print axioms OverwriteStable.cold_states_reach_this_stationary_saved_basis

#print axioms OverwriteStable.basePlanF0_0
#print axioms OverwriteStable.basePlanF0_1
#print axioms OverwriteStable.basePlanF0_2
#print axioms OverwriteStable.basePlanF0_3
#print axioms OverwriteStable.basePlanF1_0
#print axioms OverwriteStable.basePlanF1_1
#print axioms OverwriteStable.basePlanF1_2
#print axioms OverwriteStable.basePlanF1_3
#print axioms OverwriteStable.basePlanF2_0
#print axioms OverwriteStable.basePlanF2_1
#print axioms OverwriteStable.basePlanF2_2
#print axioms OverwriteStable.basePlanF2_3
#print axioms OverwriteStable.basePlanF3_0
#print axioms OverwriteStable.basePlanF3_1
#print axioms OverwriteStable.basePlanF3_2
#print axioms OverwriteStable.basePlanF3_3
#print axioms OverwriteStable.basePlanB0_0
#print axioms OverwriteStable.basePlanB1_0
#print axioms OverwriteStable.basePlanB2_0
#print axioms OverwriteStable.basePlanB3_0
