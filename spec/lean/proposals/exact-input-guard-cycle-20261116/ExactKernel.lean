import ExactGuard
import HeadSafety
namespace ExactKernel
open ExactGuard AlternatingCondition NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def actual (m : Color) : Offered := ⟨fact p [f,g] .exact m,false⟩

theorem entry_run1_is_a_real_nonempty_cut :
    entryValues 1 1=[value p [f] .ne .t] := by decide +kernel

theorem later_entry_is_the_unchanged_normal_exact_point :
    entryValues 3 2=[value p [f,g] .exact .t false] := by decide +kernel

theorem latest_policy_still_emits_the_coarse_first_field (m : Color) :
    (HeadPolicy.emit 5 8 false (fact p [] .may m) (actual m)).contains (star p [f] m)=true := by
  cases m <;> decide +kernel

theorem a_qualified_NE_can_emit_the_precise_point (m : Color) :
    HeadPolicy.emit 5 8 false (fact p [f] .ne m) (actual m)=
      [⟨fact p [f,g] .exact m,false⟩] := by cases m <;> decide +kernel

theorem coarse_guard_generates_root_MAY (m : Color) :
    gen m (star p [f] m)=[value ret [] .may m.flip,value ret [h] .must m.flip] := by
  cases m <;> decide +kernel

theorem fine_point_cannot_satisfy_the_deeper_guard (m : Color) :
    gen m ⟨(actual m).ap,false⟩=[value ret [h] .must m.flip false] := by
  cases m <;> decide +kernel

theorem normal_h_input_also_cannot_satisfy_the_deep_guard (m : Color) :
    gen m ⟨fact p [h] .must m,false⟩=[value ret [h] .must m.flip false] := by
  cases m <;> decide +kernel

theorem the_coarse_conditional_result_applies_to_the_real_point (m : Color) :
    read (fact p [f] .star m,value ret [] .may m.flip) (actual m)=some (rootMay m.flip) := by
  cases m <;> decide +kernel

theorem normal_child_cannot_cover_the_root_MAY (m : Color) :
    UniformActual.foldValues false [] [rootMay m,value p [h] .must m false]=
      [rootMay m,value p [h] .must m false] := by cases m <;> decide +kernel

theorem reverse_star_recreates_the_broad_request (k : Nat) (m : Color) :
    value p [] .may m ∈ reverseGen k m (star ret [] m.flip) := by
  cases m <;> simp [reverseGen,star,fact,Color.id,Color.flip,p,ret,f,g,h,value,dropHead]

theorem exact_actuals_never_qualify_for_the_new_exception
    (run : Nat) (back : Bool) (d : Ap) (m : Color) (q : Seed) :
    HeadPolicy.capException run back d (actual m) q=false := by
  simp [HeadPolicy.capException,actual,fact]

theorem all_Empty_E_offers_keep_the_original_entry_cap
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (empty : a.ap.e=[]) (inside : q ∈ HeadPolicy.emit run k back d a) :
    q.ap.path.length≤k ∧ q.ap.path.length≤d.path.length+1 := by
  rw [HeadPolicy.empty_actual_E_is_exactly_the_old_policy run k back d a empty] at inside
  have legal := NonEmptyPolicy.emitted_legal run k back d a q inside
  exact ⟨legal.1,by simpa only [selector_path] using legal.2.1⟩

theorem no_correlated_FLOW_covers_the_critical_mark_change (m : Color) :
    (forwardEdge [] m).1.mark≠(forwardEdge [] m).2.ap.mark ∧
    (backwardEdge m).1.mark≠(backwardEdge m).2.ap.mark := by cases m <;> decide +kernel

theorem Target_routing_still_requires_a_next_run :
    TargetZeroKernel.continuationRelevant (terminal (rootMay .u))=true ∧
    TargetZeroKernel.c5Restrict TargetZeroKernel.exactEntry TargetZeroKernel.exactExit
      targetDemand (terminal (rootMay .u))=some (terminal (rootMay .u)) := by decide +kernel
end ExactKernel
