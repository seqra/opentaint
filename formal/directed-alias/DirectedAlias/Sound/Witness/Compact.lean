import DirectedAlias.Sound.Witness.Rename

/-!
# Compaction of indices

A list `U` of `n` indices uses at most `n` different values. So swaps can move all of them
into the range `[0, n)` (`compact`). The proof is constructive: each step finds a bad index
(`n ≤ i`) and a free index (`j < n`, `j ∉ U`) with `List.find?`, and swaps them.
The number of bad entries goes down at each step.
-/

namespace DirectedAlias.Sound.Witness

open DirectedAlias

/-- Remove the first entry `a` of a list. (The library `List.erase` lemmas use
`Classical.choice`, so this file uses its own function.) -/
def rm (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: l => if b = a then l else b :: rm a l

/-- Removing an entry of the list makes the list one shorter. -/
theorem rm_length (a : Nat) : ∀ (l : List Nat), a ∈ l → (rm a l).length + 1 = l.length
  | [], h => by cases h
  | b :: l, h => by
    unfold rm
    by_cases hb : b = a
    · rw [ite_eq_left hb]; rfl
    · rw [ite_eq_right hb]
      have hl : a ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hb
        · exact h
      simp only [List.length_cons, rm_length a l hl]

/-- Removing `a` keeps the other entries. -/
theorem mem_rm {a j : Nat} (hj : j ≠ a) : ∀ (l : List Nat), j ∈ l → j ∈ rm a l
  | [], h => by cases h
  | b :: l, h => by
    unfold rm
    by_cases hb : b = a
    · rw [ite_eq_left hb]
      rcases List.mem_cons.mp h with h | h
      · exact absurd (h.trans hb) hj
      · exact h
    · rw [ite_eq_right hb]
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_rm hj l h)

/-- If all indices below `n` and one more index `i ≥ n` are in `U`, then `U` is longer than `n`. -/
theorem cover_lt : ∀ (n : Nat) (U : List Nat) (i : Nat), (∀ j, j < n → j ∈ U) → i ∈ U → n ≤ i →
    n < U.length
  | 0, U, i, _, hi, _ => by
    cases U with
    | nil => cases hi
    | cons _ _ => exact Nat.succ_pos _
  | n + 1, U, i, hall, hi, hn => by
    have hm : n ∈ U := hall n (Nat.lt_succ_self n)
    have hne : i ≠ n := by omega
    have h1 : ∀ j, j < n → j ∈ rm n U := fun j hj => mem_rm (by omega) U (hall j (by omega))
    have h2 : i ∈ rm n U := mem_rm hne U hi
    have := cover_lt n (rm n U) i h1 h2 (by omega)
    have := rm_length n U hm
    omega

/-- A list with an entry `i ≥ n`, where `n` is the length, misses some index below `n`. -/
theorem free_index (U : List Nat) (i : Nat) (hi : i ∈ U) (hn : U.length ≤ i) :
    ∃ j, j < U.length ∧ j ∉ U := by
  cases hf : (List.range U.length).find? (fun j => !(U.contains j)) with
  | some j =>
    have h1 := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    have h2 := List.find?_some hf
    refine ⟨j, h1, fun hj => ?_⟩
    have : U.contains j = true := List.contains_iff_mem.mpr hj
    rw [this] at h2
    cases h2
  | none =>
    have hall : ∀ j, j < U.length → j ∈ U := by
      intro j hj
      have := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
      cases hc : U.contains j with
      | true => exact List.contains_iff_mem.mp hc
      | false => rw [hc] at this; exact absurd rfl this
    have := cover_lt U.length U i hall hi hn
    omega

/-- The bad entries of `U` for the bound `n`. -/
def badN (n : Nat) (U : List Nat) : Nat := U.countP (fun i => decide (n ≤ i))

/-- No bad entry: each entry is below the bound. -/
theorem badN_zero {n : Nat} : ∀ (U : List Nat), badN n U = 0 → ∀ i ∈ U, i < n
  | [], _, i, hi => by cases hi
  | e :: U, h, i, hi => by
    simp only [badN, List.countP_cons] at h
    cases hd : decide (n ≤ e) with
    | true =>
      rw [hd] at h
      have e1 : (if true = true then 1 else 0) = 1 := rfl
      rw [e1] at h
      omega
    | false =>
      rw [hd] at h
      have e0 : (if false = true then 1 else 0) = 0 := rfl
      rw [e0, Nat.add_zero] at h
      rcases List.mem_cons.mp hi with h' | h'
      · rw [h']; exact Nat.lt_of_not_le (of_decide_eq_false hd)
      · exact badN_zero U h i h'

/-- A swap of a bad index `i` with a free index `j` does not add bad entries, and it removes
the entries of `i`. -/
theorem badN_swap {n i j : Nat} (hj : j < n) (hi : n ≤ i) :
    ∀ (U : List Nat), j ∉ U →
      badN n (U.map (swp i j)) ≤ badN n U ∧ (i ∈ U → badN n (U.map (swp i j)) < badN n U)
  | [], _ => ⟨Nat.le_refl _, fun h => by cases h⟩
  | e :: U, hjU => by
    have hj' : j ∉ U := fun h => hjU (List.mem_cons_of_mem _ h)
    have hej : e ≠ j := fun h => hjU (h ▸ List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := badN_swap hj hi U hj'
    simp only [badN, List.map_cons, List.countP_cons] at ih1 ih2 ⊢
    by_cases hei : e = i
    · subst hei
      rw [swp_left]
      have h1 : decide (n ≤ j) = false := decide_eq_false (by omega)
      have h2 : decide (n ≤ e) = true := decide_eq_true hi
      rw [h1, h2]
      have e1 : (if false = true then 1 else 0) = 0 := rfl
      have e2 : (if true = true then 1 else 0) = 1 := rfl
      rw [e1, e2]
      refine ⟨by omega, fun _ => by omega⟩
    · rw [swp_other hei hej]
      refine ⟨by omega, fun hm => ?_⟩
      rcases List.mem_cons.mp hm with h | h
      · exact absurd h.symm hei
      · have := ih2 h; omega

/-- Compaction: if a property is kept by each swap, then a witness of it has a renamed
witness whose indices are all below the length of the index list. -/
theorem compact {α : Type} (U : α → List Nat) (R : Nat → Nat → α → α)
    (hU : ∀ a b d, U (R a b d) = (U d).map (swp a b)) (P : α → Prop)
    (hP : ∀ a b d, P d → P (R a b d)) :
    ∀ (m : Nat) (d : α), badN (U d).length (U d) ≤ m → P d →
      ∃ d', P d' ∧ (U d').length = (U d).length ∧ ∀ i ∈ U d', i < (U d).length := by
  intro m
  induction m with
  | zero =>
    intro d hb hd
    refine ⟨d, hd, rfl, fun i hi => ?_⟩
    have h0 : badN (U d).length (U d) = 0 := by omega
    exact badN_zero _ h0 i hi
  | succ m ih =>
    intro d hb hd
    cases hz : badN (U d).length (U d) with
    | zero => exact ih d (by omega) hd
    | succ k =>
      have hpos : 0 < (U d).countP (fun i => decide ((U d).length ≤ i)) := by
        show 0 < badN _ _; omega
      obtain ⟨i, hi, hbad⟩ := List.countP_pos_iff.mp hpos
      have hbad' : (U d).length ≤ i := of_decide_eq_true hbad
      obtain ⟨j, hj, hjU⟩ := free_index (U d) i hi hbad'
      have hlen : (U (R i j d)).length = (U d).length := by rw [hU, List.length_map]
      have hlt := (badN_swap hj hbad' (U d) hjU).2 hi
      obtain ⟨d', h1, h2, h3⟩ := ih (R i j d) (by rw [hlen, hU]; omega) (hP i j d hd)
      exact ⟨d', h1, h2.trans hlen, fun i hi => hlen ▸ h3 i hi⟩

end DirectedAlias.Sound.Witness
