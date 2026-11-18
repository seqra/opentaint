import BoundCoreProof
import BoundBodyCold
namespace BoundProof
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition BoundBody
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := {(value ret [h,f,g] .exact .t false) with h:=true}
def coarse : BoundBody.Edge := (point.ap,{(value ret [h,f] .ne .t) with h:=true})
def native : List Value := [BoundCore.bind ⟨true,[]⟩ good]

theorem protected_original_uses_bound_NORMAL_service :
    suppressNativeReply 5 [point.ap] native ⟨point.ap,false⟩ true coarse=true := by decide +kernel

theorem exact_or_same_head_premise_does_not_block_the_certificate :
    coarse.1.tail=.exact ∧ coarse.1.path=point.ap.path ∧
    suppressNativeReply 5 [point.ap] native ⟨point.ap,false⟩ true coarse=true := by decide +kernel

theorem no_storage_flag_is_changed_to_make_service_fit :
    good.h=true ∧ (BoundCore.bind ⟨true,[]⟩ good).h=true ∧ coarse.2.h=true := by decide +kernel

theorem missing_native_receipt_or_full_closure_still_blocks :
    suppressNativeReply 5 [] native ⟨point.ap,false⟩ true coarse=false ∧
    suppressNativeReply 5 [point.ap] [] ⟨point.ap,false⟩ true coarse=false := by decide +kernel

theorem DEMAND_actuals_backward_runs_and_run1_fall_back :
    suppressNativeReply 5 [point.ap] native ⟨point.ap,true⟩ true coarse=false ∧
    suppressNativeReply 4 [point.ap] native ⟨point.ap,false⟩ true coarse=false ∧
    suppressNativeReply 1 [point.ap] native ⟨point.ap,false⟩ true coarse=false := by decide +kernel

theorem NORMAL_replies_are_always_retained (run : Nat) (closed : List Ap)
    (actual : Offered) (inputH : Bool) (images : List Value) (e : BoundBody.Edge)
    (normal : e.2.demand=false) :
    suppressNativeReply run closed images actual inputH e=false := by
  simp [suppressNativeReply,normal]

theorem NORMAL_MUST_actual_can_close_the_existing_body :
    bodyClosed 8 ⟨fact p [f,g] .must .t,false⟩=true := by decide +kernel

theorem current_cut_or_unknown_query_never_becomes_full_closure :
    bodyClosed 2 ⟨point.ap,false⟩=false ∧
    BoundCore.eligible ⟨{point.ap with tail:=.may},false⟩=false ∧
    BoundCore.eligible ⟨{point.ap with tail:=.ne},false⟩=false ∧
    BoundCore.eligible ⟨{point.ap with tail:=.star},false⟩=false := by decide +kernel

inductive Node where | entry (q : Seed) | result (v : Value)
  deriving DecidableEq

def next : Node → List Node
  | .entry q => (colors.flatMap fun m => gen m q).map Node.result
  | .result _ => []
def owned (q : Seed) := Node.entry q :: next (.entry q)
def selected (region : Ap) (ctx : BoundCore.Context) (flag : Bool) : Node → Bool
  | .entry _ => false
  | .result c => BoundCore.flag ctx c==flag && ReplyCore.overlaps c.ap region
def service (images : List Value) (ctx : BoundCore.Context) : Node → Bool
  | .entry _ => true
  | .result c => images.any (fun n => BoundCore.covers n (BoundCore.bind ctx c))

theorem native_service_has_complete_internal_closure_and_terminal_witnesses
    (images : List Value) (q : Seed) (region : Ap) (ctx : BoundCore.Context) (flag : Bool)
    (ok : BoundCore.completeFor images q (colors.flatMap fun m => gen m q) region ctx flag=true) :
    CompleteClosure.check next [.entry q] (owned q) (selected region ctx flag) (service images ctx)=true := by
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
      cases chosen : BoundCore.flag ctx c==flag && ReplyCore.overlaps c.ap region
      · simp [selected,chosen]
      · have parts := chosen
        simp only [Bool.and_eq_true] at parts
        have same : BoundCore.flag ctx c=flag := by simpa using parts.1
        obtain ⟨n,hn,covered,_,_⟩ := BoundCoreProof.completed_query_constructs_a_real_native_witness
          images q _ region ctx flag ok c hc same parts.2
        have yes : images.any (fun n => BoundCore.covers n (BoundCore.bind ctx c))=true :=
          List.any_eq_true.mpr ⟨n,hn,covered⟩
        simpa [selected,chosen,service] using yes

-- Query ownership, revision, physical ports, original premise and native packet
-- identity are bound by the caller before this pure selection function is used.
-- The executable witness is already delivered NORMAL data, never a new query.
theorem pass_binding_does_not_create_protection (c : Value)
    (plain : c.h=false) : (BoundCore.bind ⟨false,[]⟩ c).h=false := by
  cases mark : c.ap.mark <;> simp [BoundCore.bind,BoundCore.flag,plain,mark]

end BoundProof
