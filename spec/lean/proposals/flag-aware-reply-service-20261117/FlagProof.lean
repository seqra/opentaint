import FlagBody
import FlagCold
import RelevantKernel
import LayerRegression
namespace FlagProof
open FlagBody NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := {(value ret [h,h] .must .t false) with h:=true}
def region : Ap := fact ret [h] .may .t
def coarse : FlagBody.Edge := (fact p [f] .star .t,{(value ret [h] .may .t) with h:=true})
def basis : List FlagBody.Edge := [(point.ap,good)]
def native : List Value := [{good with ap:={good.ap with base:=p}}]

theorem same_flag_NORMAL_service_answers_the_current_protected_reply :
    FlagCore.completeFor basis point [good] region true=true ∧
    FlagCore.received native [good] region true=true ∧
    suppressFlaggedReply 5 [point.ap] basis native ⟨point.ap,false⟩ false coarse=true := by decide +kernel

theorem a_plain_provider_cannot_answer_a_protected_return :
    FlagCore.completeFor [(point.ap,{good with h:=false})] point [good] region true=false := by decide +kernel

theorem the_other_flag_does_not_create_cross_flag_service :
    FlagCore.completeFor [] point [{good with h:=false}] region true=true ∧
    FlagCore.completeFor [] point [good,{good with h:=false}] region true=false := by decide +kernel

theorem both_literal_memberships_are_retained_in_the_same_query :
    [good,{good with h:=false}].eraseDups.length=2 ∧ good.h=true := by decide +kernel

theorem NORMAL_protected_outputs_are_not_selected (run : Nat) (closed : List Ap)
    (service : List FlagBody.Edge) (native : List Value) (a : Offered) (originalH : Bool) (e : FlagBody.Edge)
    (normal : e.2.demand=false) :
    suppressFlaggedReply run closed service native a originalH e=false := by
  simp [suppressFlaggedReply,suppress,normal]

theorem a_rejected_existing_shape_guard_rejects_both_flags
    (run : Nat) (closed : List Ap) (service : List FlagBody.Edge)
    (native : List Value) (a : Offered) (originalH : Bool) (e : FlagBody.Edge)
    (no : suppress run closed a (e.1,{e.2 with h:=false})=false) :
    suppressFlaggedReply run closed service native a originalH e=false := by
  simp [suppressFlaggedReply,no]

theorem a_protected_original_still_falls_back (run : Nat) (closed : List Ap)
    (service : List FlagBody.Edge) (native : List Value) (a : Offered) (e : FlagBody.Edge) :
    suppressFlaggedReply run closed service native a true e=false := by simp [suppressFlaggedReply]

theorem missing_closure_service_or_receipt_still_blocks :
    suppressFlaggedReply 5 [] basis native ⟨point.ap,false⟩ false coarse=false ∧
    suppressFlaggedReply 5 [point.ap] [] native ⟨point.ap,false⟩ false coarse=false ∧
    suppressFlaggedReply 5 [point.ap] basis [] ⟨point.ap,false⟩ false coarse=false := by decide +kernel

theorem full_closure_still_rejects_DEMAND_even_outside_the_selected_flag :
    FlagCore.completeFor basis point [good,{good with h:=false,demand:=true}] region true=false := by decide +kernel

theorem wrong_flag_receipts_are_not_accepted :
    FlagCore.received [{good with ap:={good.ap with base:=p},h:=false}] [good] region true=false := by decide +kernel

theorem NORMAL_actual_shape_layer_direction_and_run_guards_remain :
    suppressFlaggedReply 5 [point.ap] basis native ⟨point.ap,true⟩ false coarse=false ∧
    suppressFlaggedReply 4 [point.ap] basis native ⟨point.ap,false⟩ false coarse=false ∧
    suppressFlaggedReply 1 [point.ap] basis native ⟨point.ap,false⟩ false coarse=false ∧
    suppressFlaggedReply 5 [point.ap] basis native ⟨{point.ap with tail:=.must},false⟩ false coarse=false := by decide +kernel

inductive Node where | entry (q : Seed) | result (v : Value)
  deriving DecidableEq

def next : Node → List Node
  | .entry q => (colors.flatMap fun m => gen m q).map Node.result
  | .result _ => []
def owned (q : Seed) := Node.entry q :: next (.entry q)
def selected (region : Ap) (flag : Bool) : Node → Bool
  | .entry _ => false
  | .result c => c.h==flag && ReplyCore.overlaps c.ap region
def service (current : List FlagBody.Edge) (q : Seed) : Node → Bool
  | .entry _ => true
  | .result c => ScopedCore.covered current q c

theorem full_internal_closure_and_same_flag_terminal_service
    (current : List FlagBody.Edge) (q : Seed) (region : Ap) (flag : Bool)
    (ok : FlagCore.completeFor current q (colors.flatMap fun m => gen m q) region flag=true) :
    CompleteClosure.check next [.entry q] (owned q) (selected region flag) (service current q)=true := by
  simp only [CompleteClosure.check,Bool.and_eq_true]
  constructor
  · constructor
    · simp [owned]
    · apply List.all_eq_true.mpr
      intro n hn
      simp only [owned,List.mem_cons] at hn
      rcases hn with seed | exit
      · subst n
        apply List.all_eq_true.mpr
        intro t ht
        exact decide_eq_true (List.mem_cons_of_mem _ ht)
      · rcases List.mem_map.mp exit with ⟨c,_,eq⟩
        subst n
        simp [next]
  · apply List.all_eq_true.mpr
    intro n hn
    simp only [owned,List.mem_cons] at hn
    rcases hn with seed | exit
    · subst n; rfl
    · rcases List.mem_map.mp exit with ⟨c,hc,eq⟩
      subst n
      cases chosen : c.h==flag && ReplyCore.overlaps c.ap region
      · simp [selected,chosen]
      · have chosenParts := chosen
        simp only [Bool.and_eq_true] at chosenParts
        have same : c.h=flag := by simpa using chosenParts.1
        have hit := FlagCore.selected_return_has_the_same_flag_and_whole_NORMAL_service current q _ region flag ok c hc same chosenParts.2
        simpa [selected,chosen,service] using hit.2

end FlagProof
