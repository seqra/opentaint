import OriginalReturn
import FlagProof
import KernelEval
namespace OriginalKernel
open OriginalReturn NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := {(value ret [h,f,g] .exact .t false) with h:=true}
def region : Ap := fact ret [h] .may .t
def coarse : OriginalReturn.Edge := (fact p [f] .star .t,{(value ret [h] .may .t) with h:=true})
def basis : List OriginalReturn.Edge := [(point.ap,good)]
def native : List Value := [{good with ap:={good.ap with base:=p}}]

theorem same_flag_NORMAL_body_and_native_service_are_ready :
    colors.flatMap (fun m => gen m point)=[good] ∧
    FlagCore.completeFor basis point [good] region true=true ∧
    FlagCore.received native [good] region true=true := by decide +kernel

theorem body_closure_is_ready_at_every_sufficient_limit (n : Nat) :
    bodyClosed (n+3) point=true := by kernel_decide_open

theorem plain_original_is_selected_but_protected_original_is_not :
    suppressFlaggedReply 5 [point.ap] basis native ⟨point.ap,false⟩ false coarse=true ∧
    suppressFlaggedReply 5 [point.ap] basis native ⟨point.ap,false⟩ true coarse=false := by decide +kernel

theorem protected_original_always_falls_back_at_any_later_run
    (run : Nat) (closed : List Ap) (service : List OriginalReturn.Edge)
    (native : List Value) (actual : Offered) (e : OriginalReturn.Edge) :
    suppressFlaggedReply run closed service native actual true e=false := by simp [suppressFlaggedReply]

theorem true_h_read_returns_a_protected_exact_value_for_the_next_call :
    consumeH good=some {(value ret [f,g] .exact .t false) with h:=true} := by decide +kernel

theorem old_whole_mark_and_plain_reply_checks_do_not_bypass_the_guard :
    suppress 5 [point.ap] ⟨point.ap,false⟩ coarse=false ∧
    suppressMark 5 [(point.ap,1)] ⟨point.ap,false⟩ coarse=false ∧
    suppressReply 5 [point.ap] basis native ⟨point.ap,false⟩ coarse=false := by decide +kernel

end OriginalKernel
