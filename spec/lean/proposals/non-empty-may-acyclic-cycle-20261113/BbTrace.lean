import Cycle

/- BB-local refinement of the same example. This uses the proposed common
   local-block pipeline: saved NORMAL replay first, C2 for current work,
   local C5, and enclosing method C5. No extra loop-growth gate is added
   to an acyclic BB. Witness projection; additional paired rows are allowed. -/
namespace AcyclicMayBbTrace
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h
local instance : BEq Ap := ⟨fun a b => decide (a = b)⟩
local instance : ReflBEq Ap where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Ap where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
set_option linter.unusedSimpArgs false

def readForward3 : Row := ⟨ap p [f] .ne,ap ret [] .star⟩
def readBackward4 : Row := ⟨ap ret [] .may,ap p [f] .star⟩
def methodForward5 : Row := ⟨ap p [f] .may,ap ret [] .star⟩
def methodBackward6 : Row := ⟨ap ret [] .may,ap p [f] .star⟩
def firstMethodQuery : Ap := ap p [f] .must
def secondMethodOffer : Offered := ⟨ap p [f] .ne (some t),true⟩
def laterForwardLoss : Ap × Value := (ap p [f] .star,val (ap ret [] .may) true)
def laterBackwardLoss : Ap × Value := (ap ret [] .star,val (ap p [f] .may) true)

theorem run2_read_bb_keeps_the_cut_separately :
    restrictOne 2 1 true [sinkNeed] (ap ret [] .star)
      (cut 1 (val (ap p [f,g] .star))) backwardRow =
        some (ap ret [] .star,val (ap p [f] .ne) true) := by decide

theorem run3_read_bb_accepts_the_partial_query :
    emit 3 2 false readForward3.entry ⟨ap p [f] .star,false⟩ =
      [⟨ap p [f] .star,false⟩] := by decide

theorem run3_read_bb_rejects_the_root_star_query :
    emit 3 2 false readForward3.entry ⟨ap p [] .star,false⟩ = [] := by decide

theorem run3_read_bb_publishes_only_the_selected_partial_loss :
    restrictOne 3 2 false [⟨ap p [f] .star,false⟩] (ap p [f] .star)
      (val (ap ret [] .may) true) readForward3 = some laterForwardLoss := by decide

theorem run4_read_bb_finishes_its_precise_relation :
    restrictOne 4 3 true [sinkNeed] (ap ret [] .star)
      (val (ap p [f,g] .star)) readBackward4 =
        some (ap ret [] .star,val (ap p [f,g] .star)) := by decide

theorem run4_write_replay_still_leaves_method_demand :
    restrictOne 4 3 true [sinkNeed] (ap ret [] .star)
      (val (ap p [] .may) true) readBackward4 = some laterBackwardLoss := by decide

theorem later_first_method_query (run k : Nat) :
    emit (run+5) (k+2) false methodForward5.entry source =
      [⟨firstMethodQuery,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,methodForward5,source,
    selector,marksOK,seed,firstMethodQuery,ap,legalSeed,f,p,ret,dropHead] <;>
      try dsimp at *
  all_goals simp [dropHead]

theorem saved_read_preserves_uniform_taint_for_the_first_query :
    move p ret [f,g] [] firstMethodQuery = some (val (ap ret [] .must)) := by decide

theorem saved_write_result_is_precise_before_method_c5 :
    move p ret [] [f] firstMethodQuery = some (val (ap ret [f,f] .must)) := by decide

theorem method_cut_repeats_at_every_later_limit (run k : Nat) :
    restrictOne (run+5) (k+2) false [source] firstMethodQuery
      (val (ap ret [f,f] .must)) methodForward5 =
        some (firstMethodQuery,val (ap ret [f] .ne) true) := by
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,later_first_method_query]
  simp [firstMethodQuery,methodForward5,normalize,normalAp,intersectExit,
    selector,marksMeet,cut,ap,val,f,p,ret,dropHead,admits]

theorem method_retains_the_separate_normal_uniform_result (run k : Nat) :
    restrictOne (run+5) (k+2) false [source] firstMethodQuery
      (val (ap ret [] .must)) methodForward5 =
        some (firstMethodQuery,val (ap ret [] .must)) := by
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,later_first_method_query]
  simp [firstMethodQuery,methodForward5,normalize,normalAp,intersectExit,
    selector,marksMeet,cut,ap,val,f,p,ret,dropHead,admits]

/-- Current MUST premise has a definite same-head original MUST binding.
    The independent NE result is DEMAND and keeps the actual full mark. -/
def applyFirstCut (stored : Ap × Value) : Offered :=
  ⟨{stored.2.ap with base := p,mark := source.ap.mark},stored.2.demand⟩

theorem first_cut_supplies_the_actual_second_offer :
    applyFirstCut (firstMethodQuery,val (ap ret [f] .ne) true) = secondMethodOffer := by decide

theorem later_second_method_query (run k : Nat) :
    emit (run+5) (k+2) false methodForward5.entry secondMethodOffer =
      [⟨ap p [f] .star,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,methodForward5,secondMethodOffer,
    selector,marksOK,seed,ap,legalSeed,f,p,ret,dropHead] <;> try dsimp at *
  all_goals simp [dropHead]

/-- The record was produced BACKWARD at run4. Its forward opposite view
    admits STAR-inside and reads the unknown g suffix of p.f.STAR. -/
theorem saved_opposite_read_recreates_may_without_current_bb_analysis :
    move p ret [f,g] [] (ap p [f] .star) = some (val (ap ret [] .may) true) := by decide

theorem method_may_row_repeats_after_replay (run k : Nat) :
    restrictOne (run+5) (k+2) false [secondMethodOffer] (ap p [f] .star)
      (val (ap ret [] .may) true) methodForward5 = some laterForwardLoss := by
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,later_second_method_query]
  simp [laterForwardLoss,methodForward5,normalize,normalAp,intersectExit,
    selector,marksMeet,cut,ap,val,f,p,ret,dropHead,admits]

theorem later_backward_queries (run k : Nat) :
    emit (run+6) (k+2) true methodBackward6.entry sinkNeed =
      [⟨ap ret [] .exact,false⟩,⟨ap ret [] .star,false⟩] := by
  simp [emit,emitBase,completeFamily,primary,atHead,methodBackward6,sinkNeed,
    selector,marksOK,seed,ap,legalSeed,f,p,ret,dropHead] <;> try dsimp at *
  all_goals simp [dropHead]

theorem saved_opposite_write_recreates_root_may :
    move ret p [f] [] (ap ret [] .star) = some (val (ap p [] .may) true) := by decide

theorem enclosing_backward_c5_restores_the_same_entry (run k : Nat) :
    restrictOne (run+6) (k+2) true [sinkNeed] (ap ret [] .star)
      (val (ap p [] .may) true) methodBackward6 = some laterBackwardLoss := by
  unfold restrictOne
  simp only [rawImage,List.flatMap_cons,List.flatMap_nil,later_backward_queries]
  simp [laterBackwardLoss,methodBackward6,normalize,normalAp,intersectExit,
    selector,marksMeet,cut,ap,val,f,p,ret,dropHead,admits]

theorem later_method_rows_reverse_to_the_same_pairs :
    (⟨laterForwardLoss.2.ap,laterForwardLoss.1⟩ : Row) = methodBackward6 ∧
    (⟨laterBackwardLoss.2.ap,laterBackwardLoss.1⟩ : Row) = methodForward5 := by decide

theorem later_may_can_trigger_the_same_sink :
    applyLoss laterForwardLoss secondMethodOffer = some sinkNeed := by decide

def backwardFirstOffer : Offered := ⟨ap ret [f] .may (some t),true⟩
theorem reverse_second_call_supplies_the_first_at_f :
    (applyLoss laterBackwardLoss sinkNeed).map bindReturn = some backwardFirstOffer := by decide

theorem reverse_first_call_reaches_the_named_source_region :
    applyLoss laterBackwardLoss backwardFirstOffer =
      some ⟨ap p [f] .may (some t),true⟩ := by decide

/-- A compact executable certificate, not a hard-coded frontier transition. -/
def nextForward (run limit : Nat) : Bool :=
  match restrictOne run limit false [source] firstMethodQuery
      (val (ap ret [f,f] .must)) methodForward5 with
  | none => false
  | some stored =>
    let actual := applyFirstCut stored
    let commands := emit run limit false methodForward5.entry actual
    commands.any fun command =>
      match move p ret [f,g] [] command.ap with
      | none => false
      | some value =>
        restrictOne run limit false [actual] command.ap value methodForward5 == some laterForwardLoss

theorem next_forward_never_settles (run k : Nat) : nextForward (run+5) (k+2) = true := by
  unfold nextForward
  rw [method_cut_repeats_at_every_later_limit]
  change _ = true
  simp only [first_cut_supplies_the_actual_second_offer,later_second_method_query]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [saved_opposite_read_recreates_may_without_current_bb_analysis]
  dsimp only
  rw [method_may_row_repeats_after_replay]
  decide

def nextBackward (run limit : Nat) : Bool :=
  let commands := emit run limit true methodBackward6.entry sinkNeed
  commands.any fun command =>
    match move ret p [f] [] command.ap with
    | none => false
    | some value =>
      restrictOne run limit true [sinkNeed] command.ap value methodBackward6 == some laterBackwardLoss

theorem next_backward_never_settles (run k : Nat) : nextBackward (run+6) (k+2) = true := by
  unfold nextBackward
  rw [later_backward_queries]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [saved_opposite_write_recreates_root_may]
  dsimp only
  rw [enclosing_backward_c5_restores_the_same_entry]
  simp
  exact Or.inr (by decide)

def laterHandoffs : Nat → Bool
  | 0 => nextForward 5 4
  | n+1 => laterHandoffs n && nextBackward (2*n+6) (2*n+5) &&
      nextForward (2*n+7) (2*n+6)

theorem arbitrarily_many_later_forward_handoffs_have_demand (n : Nat) :
    laterHandoffs n = true := by
  induction n with
  | zero => exact next_forward_never_settles 0 2
  | succ n ih =>
    rw [laterHandoffs,ih,next_backward_never_settles (2*n) (2*n+3),
      next_forward_never_settles (2*n+2) (2*n+4)]
    rfl

end AcyclicMayBbTrace

#print axioms AcyclicMayBbTrace.run2_read_bb_keeps_the_cut_separately
#print axioms AcyclicMayBbTrace.run3_read_bb_accepts_the_partial_query
#print axioms AcyclicMayBbTrace.run3_read_bb_rejects_the_root_star_query
#print axioms AcyclicMayBbTrace.run3_read_bb_publishes_only_the_selected_partial_loss
#print axioms AcyclicMayBbTrace.run4_read_bb_finishes_its_precise_relation
#print axioms AcyclicMayBbTrace.run4_write_replay_still_leaves_method_demand
#print axioms AcyclicMayBbTrace.later_first_method_query
#print axioms AcyclicMayBbTrace.saved_read_preserves_uniform_taint_for_the_first_query
#print axioms AcyclicMayBbTrace.saved_write_result_is_precise_before_method_c5
#print axioms AcyclicMayBbTrace.method_cut_repeats_at_every_later_limit
#print axioms AcyclicMayBbTrace.method_retains_the_separate_normal_uniform_result
#print axioms AcyclicMayBbTrace.first_cut_supplies_the_actual_second_offer
#print axioms AcyclicMayBbTrace.later_second_method_query
#print axioms AcyclicMayBbTrace.saved_opposite_read_recreates_may_without_current_bb_analysis
#print axioms AcyclicMayBbTrace.method_may_row_repeats_after_replay
#print axioms AcyclicMayBbTrace.later_backward_queries
#print axioms AcyclicMayBbTrace.saved_opposite_write_recreates_root_may
#print axioms AcyclicMayBbTrace.enclosing_backward_c5_restores_the_same_entry
#print axioms AcyclicMayBbTrace.later_method_rows_reverse_to_the_same_pairs
#print axioms AcyclicMayBbTrace.later_may_can_trigger_the_same_sink
#print axioms AcyclicMayBbTrace.reverse_second_call_supplies_the_first_at_f
#print axioms AcyclicMayBbTrace.reverse_first_call_reaches_the_named_source_region
#print axioms AcyclicMayBbTrace.next_forward_never_settles
#print axioms AcyclicMayBbTrace.next_backward_never_settles
#print axioms AcyclicMayBbTrace.arbitrarily_many_later_forward_handoffs_have_demand
