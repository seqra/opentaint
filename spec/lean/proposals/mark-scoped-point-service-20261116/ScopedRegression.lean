import ScopedProof
import ScopedHomogeneous
import CompleteRegression
namespace ScopedRegression
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem empty_extension_preserves_every_native_reply (run : Nat) (a : Offered) (e : ScopedCore.Edge) :
    ScopedBody.suppressMark run [] a e=false := by
  unfold ScopedBody.suppressMark
  split
  · rfl
  · simp [ScopedBody.suppress]

theorem applying_no_extra_cells_is_the_identity (run : Nat) (a : Offered) (xs : List ScopedCore.Edge) :
    xs.filter (fun e => !ScopedBody.suppressMark run [] a e)=xs := by
  simp only [empty_extension_preserves_every_native_reply,Bool.not_false]
  exact List.filter_eq_self.mpr (fun _ _ => rfl)

theorem flatMap_empty {α β : Type} (f : α → List β) (empty : ∀ x,f x=[])
    (xs : List α) : xs.flatMap f=[] := by
  induction xs with
  | nil => rfl
  | cons x rest ih => rw [List.flatMap_cons,empty x,ih]; rfl

theorem old_exact_owner_never_creates_extension_memberships
    (current : List ScopedCore.Edge) (qs : List Seed) :
    qs.flatMap (fun q => ScopedCore.extra current q
      (CompletePoint.colors.flatMap fun m => CompletePoint.gen m q))=[] := by
  exact flatMap_empty _ (fun q => ScopedHomogeneous.old_exact_case_gets_no_new_scoped_cells current q) qs

theorem old_deep_real_E_owner_never_creates_extension_memberships
    (current : List ScopedCore.Edge) (qs : List Seed) :
    qs.flatMap (fun q => ScopedCore.extra current q
      (HeadDeep.colors.flatMap fun m => HeadDeep.gen m q))=[] := by
  simp only [ScopedHomogeneous.deep_real_E_body_is_the_same_generator]
  exact old_exact_owner_never_creates_extension_memberships current qs

theorem old_shallow_owner_never_creates_extension_memberships
    (current : List ScopedCore.Edge) (qs : List Seed) :
    qs.flatMap (fun q => ScopedCore.extra current q
      ([.t,.u].flatMap fun m => HeadShallow.gen m q))=[] := by
  exact flatMap_empty _ (fun q => ScopedHomogeneous.old_shallow_case_gets_no_new_scoped_cells current q) qs

theorem old_alternating_owner_never_creates_extension_memberships
    (current : List ScopedCore.Edge) (qs : List Seed) :
    qs.flatMap (fun q => ScopedCore.extra current q
      ([.t,.u].flatMap fun m => AlternatingCondition.generate m q))=[] := by
  exact flatMap_empty _ (fun q => ScopedHomogeneous.old_alternating_case_gets_no_new_scoped_cells current q) qs

theorem all_old_FLOW_owned_queries_are_ineligible (current : List ScopedCore.Edge)
    (q : Seed) (raw : List Value) (flow : q.ap.mark=none) : ScopedCore.extra current q raw=[] :=
  ScopedHomogeneous.abstract_queries_get_no_new_scoped_cells current q raw flow

theorem strict_MUST_actuals_remain_ineligible (run : Nat) (ready : List (Ap × Nat))
    (a : Offered) (e : ScopedCore.Edge) (tail : a.ap.tail=.must) :
    ScopedBody.suppressMark run ready a e=false := by
  unfold ScopedBody.suppressMark
  split
  · rfl
  · simp [ScopedBody.suppress,tail]

end ScopedRegression
