import LayerBody
namespace LayerProof
open LayerBody NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

inductive Node where
  | entry (q : Seed)
  | result (c : Value)
  deriving DecidableEq

def next : Node → List Node
  | .entry q => (colors.flatMap fun m => gen m q).map Node.result
  | .result _ => []
def owned (q : Seed) := Node.entry q :: next (.entry q)
def relevant (region : Ap) : Node → Bool
  | .entry _ => false
  | .result c => ReplyCore.overlaps c.ap region

def service (current : List LayerCore.Edge) (q : Seed) : Node → Bool
  | .entry _ => true
  | .result c => LayerCore.plainService c && ScopedCore.covered current q c

theorem full_internal_closure_preserves_protected_states
    (current : List LayerCore.Edge) (q : Seed) (region : Ap)
    (ok : LayerCore.completeFor current q (colors.flatMap fun m => gen m q) region=true) :
    CompleteClosure.check next [.entry q] (owned q) (relevant region) (service current q)=true := by
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
      cases chosen : ReplyCore.overlaps c.ap region
      · simp [relevant,chosen]
      · have hit := LayerCore.selected_returns_require_plain_service current q _ region ok c hc chosen
        simp only [relevant,chosen,service,LayerCore.plainService,LayerCore.normalLayer,
          Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true']
        exact ⟨⟨hit.1,hit.2.1⟩,hit.2.2⟩

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def good : Value := value ret [h,h] .must .u false
def protectedK : Value := {(value ret [kfield] .must .t false) with h:=true}
def region : Ap := fact ret [h] .may .u
def basis : List LayerCore.Edge := [(point.ap,good)]
def native : List Value := [{good with ap:={good.ap with base:=p}}]

theorem the_analyzed_program_and_its_protection_are_unchanged :
    colors.flatMap (fun m => gen m point)=[good,protectedK] ∧
    protectedK.demand=false ∧ protectedK.h=true := by decide +kernel

theorem new_body_status_accepts_both_NORMAL_members :
    ProtectedReturn.bodyClosed 8 point=false ∧ bodyClosed 8 point=true := by decide +kernel

theorem new_reply_uses_only_relevant_plain_NORMAL_service :
    LayerCore.completeFor basis point [good,protectedK] region=true ∧
    LayerCore.received native [good,protectedK] region=true ∧
    suppressReply 5 [point.ap] basis native ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=true := by decide +kernel

theorem old_whole_and_mark_fast_paths_keep_their_stricter_checks :
    completePoint basis point=false ∧
    ScopedCore.completeFor basis point [good,protectedK] 2=false := by decide +kernel

theorem relevant_protected_return_is_a_veto_even_with_protected_NORMAL_service :
    let protectedH := {good with h:=true}
    LayerCore.completeFor [(point.ap,protectedH)] point [protectedH] region=false := by decide +kernel

theorem protected_provider_cannot_cover_a_plain_return :
    LayerCore.completeFor [(point.ap,{good with h:=true})] point [good] region=false := by decide +kernel

theorem both_literal_H_memberships_remain_distinct :
    good≠{good with h:=true} ∧ [good,{good with h:=true}].eraseDups.length=2 := by decide +kernel

theorem a_protected_return_can_be_disjoint_even_with_the_same_output_mark :
    LayerCore.completeFor basis point [good,{protectedK with ap:={protectedK.ap with mark:=some 2}}] region=true := by decide +kernel

theorem incomplete_DEMAND_and_missing_receipts_still_block :
    bodyClosed 1 point=false ∧
    LayerCore.completeFor basis point [good,{protectedK with demand:=true}] region=false ∧
    suppressReply 5 [point.ap] basis [] ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=false := by decide +kernel

theorem no_closed_status_still_means_no_selection :
    suppressReply 5 [] basis native ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=false := by decide +kernel

theorem NORMAL_results_are_retained (run : Nat) (closed : List Ap)
    (normal : List LayerCore.Edge) (native : List Value) (a : Offered) (e : LayerCore.Edge)
    (n : e.2.demand=false) : suppressReply run closed normal native a e=false := by
  simp [suppressReply,suppress,n]

theorem protected_results_are_retained (run : Nat) (closed : List Ap)
    (normal : List LayerCore.Edge) (native : List Value) (a : Offered) (e : LayerCore.Edge)
    (h : e.2.h=true) : suppressReply run closed normal native a e=false := by
  simp [suppressReply,suppress,h]

theorem receipts_keep_the_literal_protection_coordinate (c : Value) :
    ({c with ap:={c.ap with base:=p}}).h=c.h := rfl

theorem rejected_old_input_guard_rejects_every_region
    (run : Nat) (closed : List Ap) (normal : List LayerCore.Edge)
    (native : List Value) (a : Offered) (e : LayerCore.Edge)
    (no : CompletePoint.suppress run [a.ap] a e=false) :
    suppressReply run closed normal native a e=false := by
  have h : suppress run [a.ap] a e=false := no
  have absent : suppress run closed a e=false := by
    cases hit : closed.any (fun q => decide (q=a.ap))
    · simp [suppress,hit]
    · simpa [suppress,hit] using h
  simp [suppressReply,absent]

end LayerProof
