import ReplyBody
namespace ReplyProof
open ReplyBody NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
set_option linter.unusedSimpArgs false

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

def service (current : List ReplyCore.Edge) (q : Seed) : Node → Bool
  | .entry _ => true
  | .result c => ScopedCore.normal c && ScopedCore.covered current q c

theorem region_certificate_retains_the_full_leaf_closure
    (current : List ReplyCore.Edge) (q : Seed) (region : Ap)
    (ok : ReplyCore.completeFor current q (colors.flatMap fun m => gen m q) region=true) :
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
      · have hit := ReplyCore.completion_covers_every_selected_return current q _ region ok c hc chosen
        simpa only [relevant,chosen,service,Bool.not_true,Bool.false_or,Bool.and_eq_true] using hit

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def hh : Value := value ret [h,h] .must .u false
def kk : Value := value ret [kfield] .must .u false
def basis : List ReplyCore.Edge := [(point.ap,hh)]
def region : Ap := fact ret [h] .may .u

theorem old_whole_and_mark_certificates_still_fail :
    completePoint basis point=false ∧
    ScopedCore.completeFor basis point [hh,kk] 2=false := by decide +kernel

theorem the_h_reply_has_complete_NORMAL_service :
    ReplyCore.completeFor basis point [hh,kk] region=true := by decide +kernel

theorem broad_or_k_reply_is_not_certified :
    ReplyCore.completeFor basis point [hh,kk] (fact ret [] .may .u)=false ∧
    ReplyCore.completeFor basis point [hh,kk] (fact ret [kfield] .may .u)=false := by decide +kernel

theorem a_missing_relevant_return_still_blocks_completion :
    ReplyCore.completeFor basis point [hh,value ret [h,f] .must .u false,kk] region=false := by decide +kernel

theorem ancestor_uniform_return_is_relevant_to_h :
    ReplyCore.overlaps (fact ret [] .must .u) region=true := by decide +kernel

theorem same_head_exact_and_NE_are_disjoint :
    ReplyCore.overlaps (fact ret [h] .exact .u) (fact ret [h] .ne .u)=false ∧
    ReplyCore.overlaps (fact ret [h] .exact .u) (fact ret [h] .may .u)=true := by decide +kernel

theorem exclusion_stays_at_its_original_head :
    ReplyCore.overlaps ⟨ret,[],.must,some 2,[h],[]⟩ region=false ∧
    ReplyCore.overlaps ⟨ret,[h],.must,some 2,[h],[]⟩ region=true := by decide +kernel

theorem unfinished_or_DEMAND_internal_work_does_not_complete :
    bodyClosed 1 point=false ∧ bodyClosed 8 point=true ∧
    ReplyCore.completeFor basis point [hh,{kk with demand:=true}] region=false := by decide +kernel

theorem no_region_return_needs_no_native_service_but_still_needs_closure :
    ReplyCore.completeFor [] point [kk] region=true ∧
    ReplyCore.received [] [kk] region=true ∧
    suppressReply 5 [] [] [] ⟨point.ap,false⟩ (fact p [f] .star .t,value ret [h] .may .u)=false := by decide +kernel

theorem no_new_region_cache_or_summary_is_required :
    suppressReply 5 [point.ap] basis [{hh with ap:={hh.ap with base:=p}}] ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=true := by decide +kernel

theorem all_supporting_NORMAL_rows_must_actually_apply :
    suppressReply 5 [point.ap] basis [] ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [h] .may .u)=false := by decide +kernel

theorem NORMAL_and_protected_results_are_never_selected (run : Nat) (closed : List Ap)
    (normal : List ReplyCore.Edge) (native : List Value) (a : Offered) (e : ReplyCore.Edge) :
    e.2.demand=false → suppressReply run closed normal native a e=false := by
  intro n
  simp [suppressReply,suppress,n]

theorem protection_is_not_a_region_optimization (run : Nat) (closed : List Ap)
    (normal : List ReplyCore.Edge) (native : List Value) (a : Offered) (e : ReplyCore.Edge) :
    e.2.h=true → suppressReply run closed normal native a e=false := by
  intro n
  simp [suppressReply,suppress,n]

theorem rejected_old_input_guard_rejects_every_region
    (run : Nat) (closed : List Ap) (normal : List ReplyCore.Edge)
    (native : List Value) (a : Offered) (e : ReplyCore.Edge)
    (no : CompletePoint.suppress run [a.ap] a e=false) :
    suppressReply run closed normal native a e=false := by
  have h : suppress run [a.ap] a e=false := no
  have absent : suppress run closed a e=false := by
    cases hit : closed.any (fun q => decide (q=a.ap))
    · simp [suppress,hit]
    · simpa [suppress,hit] using h
  simp [suppressReply,absent]

end ReplyProof
