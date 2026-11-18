import ReturnFrozen
import ExactKernel
namespace ReturnKernel
open UnadmittedReturn ReturnFrozen AlternatingCondition NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def extra : Value := ⟨⟨ret,[kfield],.must,some extraMark,[],[]⟩,false,false⟩

theorem exact_query_has_two_NORMAL_return_effects :
    gen .t point=[value ret [h] .must .u false,extra] := by decide +kernel

theorem all_three_marks_are_assigned_and_checked :
    ([1,2,extraMark].filter (fun m => [1,2,extraMark].contains m))=[1,2,extraMark] := by decide +kernel

theorem V_effect_is_not_a_real_field_cut : cut 1 extra=extra := by decide +kernel

theorem the_disjoint_V_consumer_does_not_accept_the_returned_k_region :
    gen .u ⟨⟨p,[kfield],.must,some extraMark,[],[]⟩,false⟩=[] := by decide +kernel

theorem normal_V_return_is_rejected_by_U_output :
    intersectExit extra (fact ret [] .star .u)=none := by decide +kernel

theorem V_demand_at_s_does_not_accept_the_k_region :
    intersectExit extra ⟨ret,[sfield],.may,some extraMark,[],[]⟩=none := by decide +kernel

theorem original_admission_still_includes_coarse_T_and_the_fine_point :
    (HeadPolicy.emit 5 8 false (fact p [] .may .t) ⟨point.ap,false⟩).contains (star p [f] .t)=true ∧
    HeadPolicy.emit 5 8 false (fact p [f] .ne .t) ⟨point.ap,false⟩=[point] := by decide +kernel

theorem critical_point_keeps_both_input_caps :
    point.ap.path.length≤2 ∧ point.ap.path.length≤(fact p [f] .ne .t).path.length+1 := by decide +kernel

theorem no_normal_V_return_service_is_admitted_in_either_steady_state :
    s9.data.raw.all (fun e => e.2.ap.mark != some extraMark)=true ∧
    s10.data.raw.all (fun e => e.2.ap.mark != some extraMark)=true ∧
    s9.saved.all (fun e => e.edge.2.ap.mark != some extraMark)=true := by decide +kernel

theorem missing_V_service_prevents_completeness (current : List UnadmittedReturn.Edge)
    (missing : ∀ e ∈ current, e.2.ap.mark ≠ some extraMark) : completePoint current point=false := by
  cases answer : completePoint current point
  · rfl
  · have all := answer
    simp only [completePoint,Bool.and_eq_true] at all
    have member : extra ∈ colors.flatMap (fun m => gen m point) := by
      apply List.mem_flatMap.mpr
      refine ⟨.t,by simp [colors],?_⟩
      rw [exact_query_has_two_NORMAL_return_effects]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    have found := List.all_eq_true.mp all.2 extra member
    simp only [Bool.and_eq_true] at found
    rcases List.any_eq_true.mp found.2 with ⟨e,inside,equal⟩
    have eq := of_decide_eq_true equal
    have bad := missing e inside
    rw [eq.2] at bad
    exact False.elim (bad rfl)

theorem the_T_point_is_never_complete_at_the_steady_states :
    completePoint s9.data.raw point=false ∧ completePoint s10.data.raw point=false := by decide +kernel

theorem completion_is_enabled_and_a_different_query_really_completes :
    s9.complete=[fact p [h] .exact .u] ∧
    s10.complete=s9.complete ∧
    s9.data.complete=s9.complete := by decide +kernel

theorem the_critical_coarse_delivery_is_not_suppressed :
    suppress 9 s9.complete ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [] .may .u)=false := by decide +kernel

theorem the_coarse_reply_is_applicable_to_the_exact_actual :
    read (fact p [f] .star .t,value ret [] .may .u) ⟨point.ap,false⟩=some (rootMay .u) := by decide +kernel

theorem h_NORMAL_is_not_whole_region_root_MAY_coverage :
    UniformActual.foldValues false [] [rootMay .u,value p [h] .must .u false]=
      [rootMay .u,value p [h] .must .u false] := by decide +kernel

end ReturnKernel
