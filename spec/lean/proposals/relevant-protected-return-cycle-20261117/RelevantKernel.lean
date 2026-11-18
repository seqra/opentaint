import RelevantReturn
import LayerProof
import KernelEval
namespace RelevantKernel
open RelevantReturn NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

local instance : BEq Value where beq a b := decide (a=b)
local instance : LawfulBEq Value where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := {(value ret [h,h] .must .t false) with h:=true}
def region : Ap := fact ret [h] .may .t
def coarse : RelevantReturn.Edge := (fact p [f] .star .t,{(value ret [h] .may .t) with h:=true})
def basis : List RelevantReturn.Edge := [(point.ap,good)]
def native : List Value := [{good with ap:={good.ap with base:=p}}]

theorem all_generated_return_memberships_are_protected (m : Color) (q : Seed)
    (c : Value) (hc : c∈gen m q) : c.h=true := by
  obtain ⟨v,_,hv⟩ := List.mem_map.mp hc
  subst c
  rfl

theorem the_precise_query_has_a_NORMAL_protected_return :
    colors.flatMap (fun m => gen m point)=[good] ∧ good.demand=false ∧ good.h=true := by decide +kernel

theorem full_NORMAL_layer_closure_IS_ready (n : Nat) :
    bodyClosed (n+2) point=true := by kernel_decide_open

theorem actual_NORMAL_service_can_apply_without_authorizing_plain_pruning :
    LayerCore.received native [good] region=true ∧
    ScopedCore.covered basis point good=true ∧
    LayerCore.completeFor basis point [good] region=false := by decide +kernel

theorem terminal_protection_veto_is_independent_of_field_limit
    (_k : Nat) (service : List RelevantReturn.Edge) :
    LayerCore.completeFor service point (colors.flatMap (fun m => gen m point)) region=false := by
  apply LayerCore.a_relevant_protected_return_still_blocks_selection service point _ region good
  · decide +kernel
  · decide +kernel
  · rfl

theorem protected_current_replies_bypass_all_three_plain_selection_paths
    (run : Nat) (whole : List Ap) (services : List (Ap × Nat)) (closed : List Ap)
    (service : List RelevantReturn.Edge) (native : List Value) (a : Offered) (e : RelevantReturn.Edge)
    (flag : e.2.h=true) :
    suppress run whole a e=false ∧ suppressMark run services a e=false ∧
    suppressReply run closed service native a e=false := by
  constructor
  · simp [suppress,flag]
  constructor
  · unfold suppressMark
    split <;> simp [suppress,flag]
  · simp [suppressReply,suppress,flag]

theorem the_native_current_coarse_reply_remains_DEMAND_and_protected :
    read coarse ⟨point.ap,false⟩=some {(value p [h] .may .t) with h:=true} := by decide +kernel

theorem the_ordinary_h_read_renews_root_MAY_without_a_cut :
    consumeH {(value p [h] .may .t) with h:=true}=
      some {(rootMay .t) with h:=true} := by decide +kernel

theorem actual_uniform_coverage_cannot_cover_the_root_MAY :
    UniformActual.foldValues false []
      [{(value p [h] .must .t false) with h:=true},{(rootMay .t) with h:=true}]
    =[{(value p [h] .must .t false) with h:=true},{(rootMay .t) with h:=true}] := by decide +kernel

theorem first_field_STAR_still_satisfies_the_deep_check_conservatively :
    {(value ret [h] .may .t) with h:=true}∈gen .t (star p [f] .t) := by decide +kernel

theorem the_NORMAL_point_cannot_satisfy_the_deep_check :
    {(value ret [h] .must .t false) with h:=true}∉gen .t point := by decide +kernel

end RelevantKernel
