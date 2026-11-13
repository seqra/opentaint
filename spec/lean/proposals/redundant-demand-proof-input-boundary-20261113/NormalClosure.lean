import Std

namespace NormalEnvelopeClosure

-- NORMAL STAR/FLOW replay on an EXACT point is a prefix replacement.
-- Ignore matching/base/port guards to obtain a larger closure. The actual
-- native point images form a subset. No MUST or concrete GEN is modelled.
structure Rule where
  read : List Nat
  write : List Nat
  deriving DecidableEq, Repr

def image (r : Rule) (input : List Nat) := r.write ++ input.drop r.read.length

def fields (basis : List Rule) := basis.flatMap (fun r => r.read ++ r.write)

def ceiling : List Nat → Nat
 | [] => 0
 | x::xs => max x (ceiling xs)

theorem member_bounded (xs : List Nat) (x : Nat) (h : x ∈ xs) : x ≤ ceiling xs := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
      rcases List.mem_cons.mp h with same | tail
      · subst x; exact Nat.le_max_left a (ceiling xs)
      · exact Nat.le_trans (ih tail) (Nat.le_max_right a (ceiling xs))

def fresh (basis : List Rule) (input : List Nat) : Nat := ceiling (input ++ fields basis) + 1

theorem fresh_not_fields (basis : List Rule) (input : List Nat) :
    fresh basis input ∉ input ++ fields basis := by
  intro member
  have impossible := member_bounded (input ++ fields basis) (fresh basis input) member
  exact Nat.not_succ_le_self _ impossible

theorem fresh_not_input (basis : List Rule) (input : List Nat) :
    fresh basis input ∉ input := by
  intro member
  exact fresh_not_fields basis input (List.mem_append.mpr (Or.inl member))

theorem fresh_not_output (basis : List Rule) (input : List Nat) (r : Rule) (hr : r ∈ basis) :
    fresh basis input ∉ r.write := by
  intro member
  have inFields : fresh basis input ∈ fields basis := by
    exact List.mem_flatMap.mpr ⟨r,hr,List.mem_append.mpr (Or.inr member)⟩
  exact fresh_not_fields basis input (List.mem_append.mpr (Or.inr inFields))

-- This relation is the UNION of every finite sequence of basis rules.
-- Its branching and path length are unbounded.
inductive Closure (basis : List Rule) (input : List Nat) : List Nat → Prop where
 | start : Closure basis input input
 | next {before : List Nat} (h : Closure basis input before) (r : Rule) (hr : r ∈ basis) :
     Closure basis input (image r before)

theorem closure_preserves_absence (basis : List Rule) (input : List Nat)
    (field : Nat) (hin : field ∉ input) (hout : ∀ r ∈ basis, field ∉ r.write)
    (output : List Nat) (h : Closure basis input output) : field ∉ output := by
  induction h with
  | start => exact hin
  | next before r hr ih =>
      intro member
      rcases List.mem_append.mp member with old | kept
      · exact hout r hr old
      · exact ih (List.mem_of_mem_drop kept)

theorem no_composition_with_given_fresh_field
    (basis : List Rule) (input targetPrefix : List Nat) (field : Nat)
    (hin : field ∉ input) (hout : ∀ r ∈ basis, field ∉ r.write) :
    ¬ Closure basis input (targetPrefix ++ [field]) := by
  intro reached
  exact closure_preserves_absence basis input field hin hout _ reached
    (List.mem_append.mpr (Or.inr (by simp)))

theorem closure_preserves_fresh_absence (basis : List Rule) (input : List Nat)
    (output : List Nat) (h : Closure basis input output) : fresh basis input ∉ output := by
  induction h with
  | start => exact fresh_not_input basis input
  | next before r hr ih =>
      intro member
      rcases List.mem_append.mp member with old | kept
      · exact fresh_not_output basis input r hr old
      · exact ih (List.mem_of_mem_drop kept)

theorem no_union_of_compositions_covers_fresh_point
    (basis : List Rule) (input targetPrefix : List Nat) :
    ¬ Closure basis input (targetPrefix ++ [fresh basis input]) := by
  intro reached
  exact closure_preserves_fresh_absence basis input _ reached
    (List.mem_append.mpr (Or.inr (by simp)))

-- Computed concrete witness, not an existential future-edge assumption.
theorem executable_witness (basis : List Rule) (input targetPrefix : List Nat) :
    ∃ field, field = fresh basis input ∧ ¬ Closure basis input (targetPrefix ++ [field]) := by
  exact ⟨fresh basis input,rfl,no_union_of_compositions_covers_fresh_point basis input targetPrefix⟩

#print axioms closure_preserves_absence
#print axioms no_composition_with_given_fresh_field
#print axioms member_bounded
#print axioms fresh_not_fields
#print axioms fresh_not_input
#print axioms fresh_not_output
#print axioms closure_preserves_fresh_absence
#print axioms no_union_of_compositions_covers_fresh_point
#print axioms executable_witness
end NormalEnvelopeClosure
