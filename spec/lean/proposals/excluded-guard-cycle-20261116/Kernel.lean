import Excluded
namespace ExcludedKernel
open ExcludedGuardCycle AlternatingCondition NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def hole (m : Color) : Offered := ⟨{fact p [f] .must m with e := [g]},false⟩

theorem ordinary_write_run1_is_demand_without_an_exclusion :
    afterWrite 1 1 = [value p [f] .must .t] := by decide

theorem ordinary_write_later_creates_the_real_hole :
    afterWrite 3 2 = [⟨(hole .t).ap,false,false⟩] := by decide

theorem coarse_first_field_still_starts (run k : Nat) (positive : 1 ≤ k) :
    star p [f] .t ∈ emit run k false (fact p [] .may .t) (hole .t) := by
  simp [emit,emitBase,selector,marksOK,completeFamily,primary,dropHead,admits,
    seed,probe,legalSeed,hole,star,fact,p,f,g,Color.id,positive] <;>
    exact Nat.ne_of_gt positive

theorem coarse_source_rule_recreates_root_may (m : Color) :
    gen m (star p [f] m) = [value ret [] .may m.flip,value ret [h] .must m.flip] := by
  cases m <;> decide

theorem same_head_fine_query_preserves_the_hole (m : Color) :
    emit 3 2 false (fact p [f] .ne m) (hole m) =
      [⟨(hole m).ap,false⟩] := by cases m <;> decide

theorem fine_source_rule_cannot_supply_a_normal_root (m : Color) :
    gen m ⟨(hole m).ap,false⟩ = [value ret [h] .must m.flip false] := by
  cases m <;> decide

theorem ordinary_h_child_cannot_supply_a_normal_root (m : Color) :
    gen m ⟨fact p [h] .must m,false⟩ = [value ret [h] .must m.flip false] := by
  cases m <;> decide

theorem exact_f_and_h_queries_only_supply_the_h_child (m : Color) :
    gen m ⟨fact p [f] .exact m,false⟩ = [value ret [h] .must m.flip false] ∧
    gen m ⟨fact p [h] .exact m,false⟩ = [value ret [h] .must m.flip false] := by
  cases m <;> decide

theorem native_coarse_binding_reaches_the_actual_caller (m : Color) :
    ExcludedGuardCycle.read (fact p [f] .star m,value ret [] .may m.flip) (hole m) =
      some (rootMay m.flip) := by cases m <;> decide

theorem ready_normal_h_does_not_cover_root_may (m : Color) :
    UniformActual.foldValues false [] [rootMay m,value p [h] .must m false] =
      [rootMay m,value p [h] .must m false] := by cases m <;> decide

theorem reverse_star_generates_the_broad_request (k : Nat) (m : Color) :
    value p [] .may m ∈ reverseGen k m (star ret [] m.flip) := by
  cases m <;> simp [reverseGen,star,fact,Color.id,Color.flip,p,ret,f,g,h,value,dropHead]

theorem root_may_survives_the_actual_replacement :
    beforeWrite 4 3 ⟨[],[],[[],[],[],[rootMay .t]]⟩ =
      [rootMay .t,value p [f] .may .t] := by decide

theorem no_diagonal_flow_can_cover_the_critical_cross_mark_edges (m : Color) :
    (forwardEdge [] m).1.mark ≠ (forwardEdge [] m).2.ap.mark ∧
    (backwardEdge m).1.mark ≠ (backwardEdge m).2.ap.mark := by cases m <;> decide

theorem zero_target_control_does_not_cancel_a_demand_for_a_normal_report :
    TargetZeroKernel.continuationRelevant (terminal (rootMay .u)) = true ∧
    TargetZeroKernel.c5Restrict TargetZeroKernel.exactEntry TargetZeroKernel.exactExit
      targetDemand (terminal (rootMay .u)) = some (terminal (rootMay .u)) ∧
    TargetZeroKernel.emittedZero .restricted [targetDemand] 0 .zero = [.zero] := by decide
end ExcludedKernel
