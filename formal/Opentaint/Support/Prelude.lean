import Opentaint.Support.Constructive

/-!
# List lemmas

`formal/` has no mathlib, so the handful of list facts the models need are proved here
rather than imported.  Nothing in this file is about OpenTaint.
-/

namespace Opentaint

theorem all_append {α} (f : α → Bool) :
    ∀ l₁ l₂ : List α, (l₁ ++ l₂).all f = (l₁.all f && l₂.all f)
  | [], _ => by simp
  | a :: as, l₂ => by
      simp [List.cons_append, List.all_cons, all_append f as l₂, Bool.and_assoc]

theorem any_append {α} (f : α → Bool) :
    ∀ l₁ l₂ : List α, (l₁ ++ l₂).any f = (l₁.any f || l₂.any f)
  | [], _ => by simp
  | a :: as, l₂ => by
      simp [List.cons_append, List.any_cons, any_append f as l₂, Bool.or_assoc]

/-- Weakening the predicate under a `List.all`. -/
theorem all_mono {α} {f g : α → Bool} (h : ∀ x, f x = true → g x = true) :
    ∀ l : List α, l.all f = true → l.all g = true
  | [], _ => rfl
  | a :: as, ha => by
      simp only [List.all_cons, Bool.and_eq_true] at ha ⊢
      exact ⟨h a ha.1, all_mono h as ha.2⟩

#constructive all_append any_append all_mono

end Opentaint
