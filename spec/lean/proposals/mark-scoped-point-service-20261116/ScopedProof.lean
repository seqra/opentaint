import ScopedBody
import ScopedCore
namespace ScopedProof
open ScopedBody NonEmptyPolicy NonEmptyRestriction AlternatingCondition
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def u : Value := value ret [h] .must .u false
def v : Value := ⟨⟨ret,[kfield],.must,some extraMark,[],[]⟩,false,false⟩
def admittedU : List ScopedCore.Edge := [(point.ap,u)]

inductive Node where
  | entry (q : Seed)
  | result (c : Value)
  deriving DecidableEq

def next : Node → List Node
  | .entry q => (colors.flatMap fun m => gen m q).map Node.result
  | .result _ => []
def owned (q : Seed) : List Node := .entry q :: next (.entry q)
def selectedReturn (mark : Nat) : Node → Bool
  | .entry _ => false
  | .result c => c.ap.mark==some mark

def service (current : List ScopedCore.Edge) (q : Seed) : Node → Bool
  | .entry _ => true
  | .result c => ScopedCore.normal c && ScopedCore.covered current q c

theorem projected_leaf_certificate_is_a_complete_NORMAL_closure
    (current : List ScopedCore.Edge) (q : Seed) (mark : Nat)
    (ok : ScopedCore.completeFor current q (colors.flatMap fun m => gen m q) mark=true) :
    CompleteClosure.check next [.entry q] (owned q) (selectedReturn mark) (service current q)=true := by
  have h := ok
  simp only [ScopedCore.completeFor,Bool.and_eq_true] at h
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
      cases isSelected : c.ap.mark==some mark
      · simp [selectedReturn,isSelected]
      · have same : c.ap.mark=some mark := by simpa using isSelected
        have yes := ScopedCore.completeFor_has_full_same_mark_coverage current q _ mark ok c hc same
        simpa only [selectedReturn,isSelected,service,Bool.not_true,Bool.false_or,Bool.and_eq_true] using yes

theorem every_true_return_with_the_selected_mark_has_an_admitted_NORMAL_row
    (current : List ScopedCore.Edge) (q : Seed) (mark : Nat)
    (ok : ScopedCore.completeFor current q (colors.flatMap fun m => gen m q) mark=true)
    (c : Value) (reachable : CompleteClosure.Reach next [.entry q] (.result c))
    (same : c.ap.mark=some mark) :
    c.demand=false ∧ c.h=false ∧ ∃ e ∈ current,e.1=q.ap ∧ e.2=c := by
  have all := CompleteClosure.every_reachable_return_is_covered next [.entry q] (owned q)
    (selectedReturn mark) (service current q)
    (projected_leaf_certificate_is_a_complete_NORMAL_closure current q mark ok) (.result c) reachable
    (by simp [selectedReturn,same])
  simp only [service,ScopedCore.normal,ScopedCore.covered,Bool.and_eq_true,
    Bool.not_eq_true',List.any_eq_true,decide_eq_true_eq] at all
  exact ⟨all.1.1,all.1.2,all.2⟩

theorem the_old_whole_certificate_still_rejects_the_missing_V_row :
    completePoint admittedU point=false := by decide +kernel

theorem U_service_completes_and_V_service_does_not :
    ScopedCore.completeFor admittedU point [u,v] 2=true ∧
    ScopedCore.completeFor admittedU point [u,v] extraMark=false ∧
    ScopedCore.extra admittedU point [u,v]=[2] := by decide +kernel

theorem one_U_child_cannot_hide_another_missing_U_return :
    ScopedCore.completeFor admittedU point
      [u,value ret [kfield] .must .u false] 2=false := by decide +kernel

theorem a_point_U_row_cannot_replace_the_full_uniform_U_return :
    ScopedCore.completeFor [(point.ap,value ret [h] .exact .u false)] point [u,v] 2=false := by decide +kernel

theorem wrong_initial_and_DEMAND_service_rows_do_not_certify_U :
    ScopedCore.completeFor [(fact p [f] .exact .t,u)] point [u,v] 2=false ∧
    ScopedCore.completeFor [(point.ap,value ret [h] .must .u)] point [u,v] 2=false := by decide +kernel

theorem the_U_certificate_does_not_suppress_a_V_reply :
    suppressMark 3 [(point.ap,2)] ⟨point.ap,false⟩
      (fact p [f] .star .t,⟨⟨ret,[],.may,some extraMark,[],[]⟩,true,false⟩)=false := by decide +kernel

theorem the_ready_U_certificate_suppresses_only_the_coarse_U_reply :
    suppressMark 3 [(point.ap,2)] ⟨point.ap,false⟩
      (fact p [f] .star .t,value ret [] .may .u)=true := by decide +kernel

theorem all_selected_U_service_must_have_passed_native_application
    (native : List Value) (key : Ap × Nat) (ok : deliveredMark native key=true)
    (c : Value) (member : c ∈ colors.flatMap (fun m => gen m ⟨key.1,false⟩))
    (same : c.ap.mark=some key.2) : c.demand=false ∧ c.h=false ∧
      ∃ n ∈ native,n={c with ap := {c.ap with base := p}} := by
  have inside : c ∈ ScopedCore.focus (colors.flatMap fun m => gen m ⟨key.1,false⟩) key.2 :=
    List.mem_filter.mpr ⟨member,by simp [same]⟩
  have h := List.all_eq_true.mp ok c inside
  simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2,h.2⟩

theorem all_normal_current_rows_are_retained (run : Nat) (ready : List (Ap × Nat))
    (a : Offered) (e : ScopedCore.Edge) (normal : e.2.demand=false) :
    suppressMark run ready a e=false := by
  unfold suppressMark
  split
  · rfl
  · simp [suppress,normal]

theorem protected_current_rows_are_retained (run : Nat) (ready : List (Ap × Nat))
    (a : Offered) (e : ScopedCore.Edge) (flag : e.2.h=true) : suppressMark run ready a e=false := by
  unfold suppressMark
  split
  · rfl
  · simp [suppress,flag]

theorem abstract_FLOW_replies_get_no_new_suppression (run : Nat) (ready : List (Ap × Nat))
    (a : Offered) (e : ScopedCore.Edge) (flow : e.2.ap.mark=none) :
    suppressMark run ready a e=false := by simp [suppressMark,flow]

end ScopedProof
