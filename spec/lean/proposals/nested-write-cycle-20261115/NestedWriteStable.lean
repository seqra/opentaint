import NestedWriteBodies

namespace NestedWriteStable
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay NestedWriteReplay NestedWriteCold NestedWriteBodies
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def rowsF : List Row := [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]
def rowsB : List Row := [⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]
def saved : List Saved := [⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]
def actual (backward : Bool) : Offered := if backward then need else NestedWriteCold.source
def domain (backward : Bool) : List Offered := [actual backward]
def frontier (backward : Bool) : List Row := if backward then rowsB else rowsF

def workWith (run limit : Nat) (backward : Bool) (rows : List Row) : List Cell :=
  cells run limit backward rows (OverwriteReplay.views backward saved) (domain backward)
def work (run limit : Nat) (backward : Bool) : List Cell := workWith run limit backward (frontier backward)

def cellWith (run limit : Nat) (backward : Bool) (rows : List Row) (row : Row) : List Edge :=
  let norms := OverwriteReplay.views backward saved
  let pl := plan run limit backward rows norms row (actual backward)
  pl.flatMap fun (q,_) =>
    let mask := commonMask (workWith run limit backward rows) q
    NestedWriteCold.methods[0]!.flatMap fun branch =>
      let outputs := (NestedWriteReplay.body run limit [] [] branch q mask [] ⟨[],[],[]⟩).2
      outputs.filterMap fun c => OverwriteReplay.pub run limit norms row (pl.map (·.1)) q c

def cell (run limit : Nat) (backward : Bool) (row : Row) : List Edge :=
  cellWith run limit backward (frontier backward) row
def packetFrom (run limit : Nat) (backward : Bool) (rows : List Row) : List Edge :=
  unique OverwriteReplay.edgeKey (rows.flatMap (cellWith run limit backward rows))
def packet (run limit : Nat) (backward : Bool) : List Edge :=
  packetFrom run limit backward (frontier backward)

theorem cold_matches_stable_frontiers :
    rows2 = [rowsF] ∧ rows3 = [rowsB] ∧ rows4 = [rowsF] ∧ saved4 = [saved] := by decide

theorem stable_forward_base : packet 5 4 false = state5.current[0]! := by decide
theorem stable_backward_base : packet 6 5 true = state6.current[0]! := by decide

theorem plan_stable (k : Nat) (backward : Bool) (row : Row)
    (hr : row ∈ frontier backward) :
    plan (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward
      (frontier backward) (OverwriteReplay.views backward saved) row (actual backward) =
    plan (if backward then 6 else 5) (if backward then 5 else 4) backward
      (frontier backward) (OverwriteReplay.views backward saved) row (actual backward) := by
  have l0 : ¬2*k+4<0 := by omega
  have l1 : ¬2*k+4<1 := by omega
  have l2 : ¬2*k+4<2 := by omega
  have l3 : ¬2*k+4<3 := by omega
  have l4 : ¬2*k+4<4 := by omega
  have m0 : ¬2*k+5<0 := by omega
  have m1 : ¬2*k+5<1 := by omega
  have m2 : ¬2*k+5<2 := by omega
  have m3 : ¬2*k+5<3 := by omega
  have m4 : ¬2*k+5<4 := by omega
  have b1 : 1 ≤ 2*k+4 := by omega
  have b2 : 2 ≤ 2*k+4 := by omega
  have b3 : 1 ≤ 2*k+5 := by omega
  have b4 : 2 ≤ 2*k+5 := by omega
  have z4 : 2*k+4 ≠ 0 := by omega
  have z5 : 2*k+5 ≠ 0 := by omega
  have r51 : 2*k+5 ≠ 1 := by omega
  have r52 : 2*k+5 ≠ 2 := by omega
  have r61 : 2*k+6 ≠ 1 := by omega
  have r62 : 2*k+6 ≠ 2 := by omega
  cases backward <;> simp only [frontier,Bool.false_eq_true,ite_false,ite_true,rowsF,rowsB,
    List.mem_cons,List.not_mem_nil,or_false] at hr
  all_goals first | (rcases hr with h | h | h | h <;> subst row) | (rcases hr with h | h <;> subst row)
  all_goals simp [plan,baseFamily,fields,frontier,rowsF,rowsB,saved,domain,actual,
    OverwriteReplay.views,OverwriteReplay.reverseEdge,OverwriteReplay.union,
    NestedWriteCold.source,need,point,emit,emitBase,completeFamily,primary,atHead,selector,
    marksOK,admits,seed,probe,legalSeed,ap,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,
    List.replicate_succ,List.replicate_zero,p,ret,f,g,
    List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.getElem!_eq_getElem?_getD,
    l0,l1,l2,l3,l4,m0,m1,m2,m3,m4,b1,b2,b3,b4,z4,z5,r51,r52,r61,r62]

theorem work_stable (k : Nat) (backward : Bool) :
    work (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward =
    work (if backward then 6 else 5) (if backward then 5 else 4) backward := by
  have nr : 2*k+(if backward then 6 else 5) ≠ 1 := by cases backward <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  have nb : (if backward then 6 else 5) ≠ (1 : Nat) := by cases backward <;> decide
  simp only [work,workWith,cells,beq_iff_eq,ite_eq_right nr,ite_eq_right nb]
  apply flatMap_equal_on_members
  intro row hr
  simp only [domain,List.map_cons,List.map_nil]
  rw [plan_stable k backward row hr]


theorem workWith_stable (k : Nat) (backward : Bool) :
    workWith (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward (frontier backward) =
    workWith (if backward then 6 else 5) (if backward then 5 else 4) backward (frontier backward) :=
  work_stable k backward


theorem basePlanF0 : plan 5 4 false (frontier false) (OverwriteReplay.views false saved) (⟨point p [] .may,point ret [] .star⟩) (actual false) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [g] .star,false⟩,[])] := by decide

theorem basePlanF1 : plan 5 4 false (frontier false) (OverwriteReplay.views false saved) (⟨point p [f] .ne,point ret [] .star⟩) (actual false) = [] := by decide

theorem basePlanF2 : plan 5 4 false (frontier false) (OverwriteReplay.views false saved) (⟨point p [f] .may,point ret [f] .star⟩) (actual false) = [] := by decide

theorem basePlanF3 : plan 5 4 false (frontier false) (OverwriteReplay.views false saved) (⟨point p [f] .ne,point ret [f] .star⟩) (actual false) = [] := by decide

theorem baseWorkF : work 5 4 false = [(⟨point p [] .may,point ret [] .star⟩,[(⟨point p [] .exact,false⟩,[]),(⟨point p [g] .star,false⟩,[])]),(⟨point p [f] .ne,point ret [] .star⟩,[]),(⟨point p [f] .may,point ret [f] .star⟩,[]),(⟨point p [f] .ne,point ret [f] .star⟩,[])] := by decide

theorem basePlanB0 : plan 6 5 true (frontier true) (OverwriteReplay.views true saved) (⟨point p [] .may,point ret [] .star⟩) (actual true) = [(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])] := by decide

theorem basePlanB1 : plan 6 5 true (frontier true) (OverwriteReplay.views true saved) (⟨point p [f] .ne,point ret [] .star⟩) (actual true) = [(⟨point p [f] .star,false⟩,[])] := by decide

theorem baseWorkB : work 6 5 true = [(⟨point p [] .may,point ret [] .star⟩,[(⟨point p [] .exact,false⟩,[]),(⟨point p [] .star,false⟩,[f]),(⟨point p [f] .exact,false⟩,[]),(⟨point p [f] .star,false⟩,[])]),(⟨point p [f] .ne,point ret [] .star⟩,[(⟨point p [f] .star,false⟩,[])])] := by decide


theorem baseMaskF0 : commonMask (workWith 5 4 false (frontier false)) ⟨point p [] .exact,false⟩ = [] := by decide

theorem baseMaskFG : commonMask (workWith 5 4 false (frontier false)) ⟨point p [g] .star,false⟩ = [] := by decide

theorem baseMaskB0 : commonMask (workWith 6 5 true (frontier true)) ⟨point p [] .exact,false⟩ = [] := by decide

theorem baseMaskBS : commonMask (workWith 6 5 true (frontier true)) ⟨point p [] .star,false⟩ = [f] := by decide

theorem baseMaskBFE : commonMask (workWith 6 5 true (frontier true)) ⟨point p [f] .exact,false⟩ = [] := by decide

theorem baseMaskBFS : commonMask (workWith 6 5 true (frontier true)) ⟨point p [f] .star,false⟩ = [] := by decide
theorem cell_stable (k : Nat) (backward : Bool) (row : Row)
    (hr : row ∈ frontier backward) :
    cell (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward row =
    cell (if backward then 6 else 5) (if backward then 5 else 4) backward row := by
  simp only [cell,cellWith,plan_stable k backward row hr,workWith_stable]
  have l0 : ¬2*k+4<0 := by omega
  have l1 : ¬2*k+4<1 := by omega
  have l2 : ¬2*k+4<2 := by omega
  have l3 : ¬2*k+4<3 := by omega
  have l4 : ¬2*k+4<4 := by omega
  have m0 : ¬2*k+5<0 := by omega
  have m1 : ¬2*k+5<1 := by omega
  have m2 : ¬2*k+5<2 := by omega
  have m3 : ¬2*k+5<3 := by omega
  have m4 : ¬2*k+5<4 := by omega
  have b1 : 1 ≤ 2*k+4 := by omega
  have b2 : 2 ≤ 2*k+4 := by omega
  have b3 : 1 ≤ 2*k+5 := by omega
  have b4 : 2 ≤ 2*k+5 := by omega
  have r51 : 2*k+5 ≠ 1 := by omega
  have r61 : 2*k+6 ≠ 1 := by omega
  have pf : (2*k+5)%2 = 1 := by omega
  have pb : (2*k+6)%2 = 0 := by omega
  cases backward <;> simp only [frontier,Bool.false_eq_true,ite_false,ite_true,rowsF,rowsB,
    List.mem_cons,List.not_mem_nil,or_false] at hr
  all_goals first | (rcases hr with h | h | h | h <;> subst row) | (rcases hr with h | h <;> subst row)
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,basePlanF0,basePlanF1,basePlanF2,
    basePlanF3,basePlanB0,basePlanB1,List.flatMap_cons,List.flatMap_nil,List.nil_append,List.append_nil]
  all_goals try simp only [baseMaskF0,baseMaskFG,baseMaskB0,baseMaskBS,baseMaskBFE,baseMaskBFS]
  all_goals dsimp only [NestedWriteCold.methods]
  all_goals try simp only [List.flatMap_cons,List.flatMap_nil,List.nil_append,List.append_nil,
    bodyFE0,bodyFE1,bodyFG0,bodyFG1,bodyBE0,bodyBE1,bodyBS0,bodyBS1,bodyBFE0,bodyBFE1,bodyBFS0,bodyBFS1]
  all_goals simp [NestedWriteCold.methods,NestedWriteReplay.body,NestedWriteReplay.reversed,NestedWriteReplay.through,NestedWriteReplay.step,
    NestedWriteReplay.nestedWrite,NestedWriteReplay.keep,commonMask,
    OverwriteReplay.values,OverwriteReplay.valueCovered,OverwriteReplay.valueKey,OverwriteReplay.apKey,
    OverwriteReplay.move,OverwriteReplay.pub,OverwriteReplay.normalsCover,
    OverwriteReplay.views,OverwriteReplay.apply,OverwriteReplay.reverseEdge,OverwriteReplay.union,saved,
    normalAp,point,ap,admits,dropHead,sortBy,insertBy,unique,
    NestedColdMachine.apKey,NestedColdMachine.pathKey,NestedColdMachine.tailKey,
    p,ret,f,g,cutOffer,restricted,normalize,intersectExit,marksMeet,exactAt,cut,val,selector,
    List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop,List.getElem!_eq_getElem?_getD,
    l0,l1,l2,l3,l4,m0,m1,m2,m3,m4,b1,b2,b3,b4,r51,r61,pf,pb,
    NonEmptyPolicy.instBEqOffered.beq,NonEmptyPolicy.instBEqAp.beq,NonEmptyPolicy.instBEqTail.beq,
    NonEmptyPolicy.Tail.ctorIdx,Option.instBEq.beq,List.beq,BEq.beq]


theorem complete_packet_stable (k : Nat) (backward : Bool) :
    packet (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward =
      (if backward then state6.current[0]! else state5.current[0]!) := by
  have same := flatMap_equal_on_members (frontier backward)
    (cell (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward)
    (cell (if backward then 6 else 5) (if backward then 5 else 4) backward)
    (fun row hr => cell_stable k backward row hr)
  have eq : packet (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward =
      packet (if backward then 6 else 5) (if backward then 5 else 4) backward :=
    congrArg (unique OverwriteReplay.edgeKey) same
  rw [eq]
  cases backward
  · exact stable_forward_base
  · exact stable_backward_base

/-- Same C2/raw-transfer/C5 pipeline for an arbitrary incoming row set.
    This operation is not defined by the claimed cyclic frontiers. -/
def advance (run limit : Nat) (backward : Bool) (rows : List Row) : List Row :=
  (OverwriteReplay.outputRows ⟨[[]],[packetFrom run limit backward rows],[[],[]]⟩)[0]!

theorem every_later_handoff (k : Nat) (backward : Bool) :
    advance (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward
      (frontier backward) = frontier (!backward) := by
  change (OverwriteReplay.outputRows
    ⟨[[]],[packet (2*k+(if backward then 6 else 5)) (2*k+(if backward then 5 else 4)) backward],[[],[]]⟩)[0]! = _
  rw [complete_packet_stable]
  cases backward <;> decide

def afterForwardPairs : Nat → List Row
  | 0 => rowsF
  | k+1 => advance (2*k+6) (2*k+5) true
      (advance (2*k+5) (2*k+4) false (afterForwardPairs k))

theorem uncapped_two_run_recurrence (k : Nat) : afterForwardPairs k = rowsF := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [afterForwardPairs,ih]
    have fwd := every_later_handoff k false
    have bwd := every_later_handoff k true
    change advance (2*k+5) (2*k+4) false rowsF = rowsB at fwd
    change advance (2*k+6) (2*k+5) true rowsB = rowsF at bwd
    rw [fwd,bwd]

theorem intermediate_handoff_has_the_same_two_rows (k : Nat) :
    advance (2*k+5) (2*k+4) false (afterForwardPairs k) = rowsB := by
  rw [uncapped_two_run_recurrence]
  exact every_later_handoff k false

theorem no_later_forward_pair_has_empty_demand (k : Nat) :
    (afterForwardPairs k).length = 4 ∧
    (advance (2*k+5) (2*k+4) false (afterForwardPairs k)).length = 2 := by
  rw [intermediate_handoff_has_the_same_two_rows,uncapped_two_run_recurrence]
  decide

theorem the_root_may_demand_is_renewed_forever (k : Nat) :
    (point p [] .star,val (point ret [] .may) true) ∈ packet (2*k+5) (2*k+4) false := by
  have h := complete_packet_stable k false
  change packet (2*k+5) (2*k+4) false = state5.current[0]! at h
  rw [h]
  simp [state5]

theorem stationary_saved_records_have_real_code_producers :
    saved = saved2[0]! ∧ saved = saved3[0]! ∧ saved = saved4[0]! := by decide

end NestedWriteStable
#print axioms NestedWriteStable.cold_matches_stable_frontiers
#print axioms NestedWriteStable.stable_forward_base
#print axioms NestedWriteStable.stable_backward_base
#print axioms NestedWriteStable.plan_stable
#print axioms NestedWriteStable.work_stable

#print axioms NestedWriteStable.basePlanF0
#print axioms NestedWriteStable.basePlanF1
#print axioms NestedWriteStable.basePlanF2
#print axioms NestedWriteStable.basePlanF3
#print axioms NestedWriteStable.baseWorkF
#print axioms NestedWriteStable.basePlanB0
#print axioms NestedWriteStable.basePlanB1
#print axioms NestedWriteStable.baseWorkB

#print axioms NestedWriteStable.cell_stable

#print axioms NestedWriteStable.baseMaskF0

#print axioms NestedWriteStable.baseMaskFG

#print axioms NestedWriteStable.baseMaskB0

#print axioms NestedWriteStable.baseMaskBS

#print axioms NestedWriteStable.baseMaskBFE

#print axioms NestedWriteStable.baseMaskBFS

#print axioms NestedWriteStable.complete_packet_stable
#print axioms NestedWriteStable.every_later_handoff
#print axioms NestedWriteStable.uncapped_two_run_recurrence
#print axioms NestedWriteStable.intermediate_handoff_has_the_same_two_rows
#print axioms NestedWriteStable.no_later_forward_pair_has_empty_demand
#print axioms NestedWriteStable.the_root_may_demand_is_renewed_forever
#print axioms NestedWriteStable.stationary_saved_records_have_real_code_producers

#print axioms NestedWriteStable.workWith_stable
