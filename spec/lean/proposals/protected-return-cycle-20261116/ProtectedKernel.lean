import ProtectedFrozen
import KernelEval
namespace ProtectedKernel
open ProtectedReturn ProtectedFrozen NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def protectedReply (m : Color) (q : Seed) : Value :=
  {(value ret [kfield] .must m q.demand) with h:=true}

theorem same_mark_action_has_an_independent_protected_return (m : Color) (q : Seed)
    (base : q.ap.base=p) (mark : q.ap.mark=some m.id) :
    protectedReply m q∈colors.flatMap (fun n => gen n q) := by
  apply List.mem_flatMap.mpr
  refine ⟨m,?_,?_⟩
  · cases m <;> simp [colors]
  · simp [gen,base,mark,protectedReply]

theorem protection_is_not_a_DEMAND_layer (m : Color) (q : Seed) :
    (protectedReply m q).demand=q.demand ∧ (protectedReply m q).h=true := by constructor <;> rfl

theorem a_protected_member_fails_the_selected_plain_NORMAL_scan
    (raw : List Value) (c : Value) (member : c∈raw) (flag : c.h=true) :
    raw.all ScopedCore.normal=false := by
  cases ok : raw.all ScopedCore.normal
  · rfl
  · have yes := List.all_eq_true.mp ok c member
    simp [ScopedCore.normal,flag] at yes

theorem body_closed_rejects_every_supported_input_at_every_limit
    (m : Color) (q : Seed) (k : Nat) (base : q.ap.base=p) (mark : q.ap.mark=some m.id) :
    bodyClosed k q=false := by
  have no := a_protected_member_fails_the_selected_plain_NORMAL_scan _ _
    (same_mark_action_has_an_independent_protected_return m q base mark) rfl
  unfold bodyClosed
  cases ok : (colors.flatMap fun n => gen n q).all
      (fun c => ScopedCore.normal c && decide (c.ap.path.length≤k))
  · simp
  · have all := List.all_eq_true.mp ok _
        (same_mark_action_has_an_independent_protected_return m q base mark)
    simp [ScopedCore.normal,protectedReply] at all

theorem reply_region_eligibility_also_rejects_the_protected_other_return
    (m : Color) (q : Seed) (basis : List ReplyCore.Edge) (region : Ap)
    (base : q.ap.base=p) (mark : q.ap.mark=some m.id) :
    ReplyCore.completeFor basis q (colors.flatMap fun n => gen n q) region=false := by
  have no := a_protected_member_fails_the_selected_plain_NORMAL_scan _ _
    (same_mark_action_has_an_independent_protected_return m q base mark) rfl
  simp [ReplyCore.completeFor,no]

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := value ret [h,h] .must .u false
def bad : Value := protectedReply .t point
def region : Ap := fact ret [h] .may .u
def basis : List ReplyCore.Edge := [(point.ap,good)]
def native : List Value := [{good with ap:={good.ap with base:=p}}]

theorem exact_body_returns_ONE_plain_and_ONE_protected_NORMAL_value :
    colors.flatMap (fun m => gen m point)=[good,bad] ∧
    good.demand=false ∧ good.h=false ∧ bad.demand=false ∧ bad.h=true := by decide +kernel

theorem geometry_and_all_relevant_NORMAL_service_are_already_satisfied :
    ReplyCore.focus [good,bad] region=[good] ∧
    (ReplyCore.focus [good,bad] region).all (ScopedCore.covered basis point)=true ∧
    ReplyCore.received native [good,bad] region=true := by decide +kernel

theorem the_region_scan_fails_BEFORE_its_terminal_projection :
    ReplyCore.completeFor basis point [good,bad] region=false ∧
    bodyClosed 8 point=false ∧
    suppressReply 5 [point.ap] basis native ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=false := by decide +kernel

theorem the_protected_return_is_not_a_field_truncation (k : Nat) (positive : 1≤k) :
    cut k bad=bad := by
  apply no_cut_preserves_intrinsic_may
  simpa [bad,protectedReply,value,fact] using positive

theorem both_marks_are_assigned_and_checked :
    colors.map Color.id=[1,2] ∧ colors.map (fun m => m.flip.id)=[2,1] := by decide +kernel

theorem C5_discards_the_protected_return_and_preserves_the_plain_service :
    intersectExit bad (fact ret [h] .star .u)=none ∧
    intersectExit good (fact ret [h] .star .u)=some good := by decide +kernel

theorem protected_values_do_not_have_to_reach_the_steady_summary_store :
    s11.data.raw.all (fun e => !e.2.h)=true ∧
    s12.data.raw.all (fun e => !e.2.h)=true ∧
    s11.saved.all (fun e => !e.edge.2.h && e.edge.2.ap.path != [kfield])=true := by decide +kernel

theorem all_completion_mechanisms_are_enabled_but_their_checks_fail :
    s11.complete=[] ∧ s11.services=[] ∧ s11.data.closed=[] ∧
    s12.complete=[] ∧ s12.services=[] ∧ s12.data.closed=[] := by decide +kernel

theorem the_true_body_needs_no_unknown_deep_guard :
    CompletePoint.gen .t point=[value ret [h] .must .u false] := by decide +kernel

end ProtectedKernel
