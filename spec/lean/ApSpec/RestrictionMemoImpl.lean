/-
  ApSpec.RestrictionMemoImpl — the implementation of rule P2' (spec/next-iteration-p3-p2m-implementation.md
  §4): the production form of the per-run restriction memo (engine/LoopRestrictionMemo.kt,
  engine/MethodBlockRuntime.kt `onApplied`).

  It extends `ApSpec.RestrictionMemo` (the rule) with the production facts:
    1. The restriction is a function `r` of the whole call input `i`. The memo key `key i` is a
       projection of the input. The code reading of the rule is `KeyDetermines`: two inputs with the
       same key have the same restriction. The model needs no function on keys and no choice of a
       representative input.
    2. A bypass input (run 1, a REACH value, no gate: `LoopOutputRestriction.bypasses`) does not use the
       memo. It runs the native restriction.
    3. The memo is not always there (`SoftReferenceManager.createRef` returns null while the memory
       guard is active): the call runs the native restriction and stores nothing.
    4. The memo has a cap. A miss on a full memo clears it before it stores the new entry.
    5. The memo can be cleared at any time (the memory guard, the end of the run).

  Theorems.
    * `lookup_det`: a sound memo returns the restriction of the input.
    * `step_sound`: a call keeps the memo sound.
    * `runImpl_eq`: for every sequence of calls, unavailable calls and clears, the results are the native
       restriction of each input.

  Constructive: no classical axioms beyond `propext` (simp).
-/
import ApSpec.RestrictionMemo

namespace ApSpec.RestrictionMemoImpl

open ApSpec.RestrictionMemo (lookup)

set_option linter.unusedSectionVars false

variable {I K V : Type} [DecidableEq K]
variable (r : I → V) (key : I → K) (bypass : I → Bool) (cap : Nat)

/-- The code reading (spec §3.6): the restriction is a function of the key in one run. -/
def KeyDetermines : Prop := ∀ i j, key i = key j → r i = r j

/-- Every stored pair comes from a real call. -/
def Sound (memo : List (K × V)) : Prop := ∀ p ∈ memo, ∃ i, key i = p.1 ∧ p.2 = r i

theorem lookup_mem (memo : List (K × V)) (k : K) (v : V) (hl : lookup memo k = some v) :
    (k, v) ∈ memo := by
  induction memo with
  | nil => cases hl
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [lookup] at hl
    by_cases hk : k' = k
    · rw [if_pos hk] at hl
      cases hl
      rw [hk]
      exact List.mem_cons_self ..
    · rw [if_neg hk] at hl
      exact List.mem_cons_of_mem _ (ih hl)

theorem lookup_det (hdet : KeyDetermines r key) (memo : List (K × V)) (h : Sound r key memo)
    (j : I) (v : V) (hl : lookup memo (key j) = some v) : v = r j := by
  obtain ⟨i, hki, hvi⟩ := h _ (lookup_mem memo (key j) v hl)
  simp only at hki hvi
  rw [hvi]
  exact hdet i j hki

/-- One call of the restriction in `onApplied` with the memo. -/
def step (memo : List (K × V)) (i : I) : V × List (K × V) :=
  if bypass i then (r i, memo)
  else match lookup memo (key i) with
    | some v => (v, memo)
    | none => (r i, (key i, r i) :: (if cap ≤ memo.length then [] else memo))

theorem step_eq (hdet : KeyDetermines r key) (memo : List (K × V)) (h : Sound r key memo) (i : I) :
    (step r key bypass cap memo i).1 = r i := by
  unfold step
  split
  · rfl
  · cases hl : lookup memo (key i) with
    | none => rfl
    | some v => exact lookup_det r key hdet memo h i v hl

theorem step_sound (memo : List (K × V)) (h : Sound r key memo) (i : I) :
    Sound r key (step r key bypass cap memo i).2 := by
  unfold step
  split
  · exact h
  · cases lookup memo (key i) with
    | some v => exact h
    | none =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨i, rfl, rfl⟩
      · split at hp
        · cases hp
        · exact h p hp

/-- The events of one method runtime in one run. -/
inductive Op (I : Type) where
  /-- A restriction call while the memo map is there. -/
  | call (i : I)
  /-- A restriction call while the memo map is not there (`createRef` returned null). -/
  | unavailable (i : I)
  /-- The memory guard or the end of the run clears the soft reference. -/
  | clear

def runImpl : List (Op I) → List (K × V) → List V
  | [], _ => []
  | .call i :: ops, memo => (step r key bypass cap memo i).1 :: runImpl ops (step r key bypass cap memo i).2
  | .unavailable i :: ops, _ => r i :: runImpl ops []
  | .clear :: ops, _ => runImpl ops []

/-- The native runtime: every call runs the restriction. -/
def runNative : List (Op I) → List V
  | [] => []
  | .call i :: ops => r i :: runNative ops
  | .unavailable i :: ops => r i :: runNative ops
  | .clear :: ops => runNative ops

theorem empty_sound : Sound r key ([] : List (K × V)) := by
  intro p hp; cases hp

/-- P2' as implemented is exact: from an empty memo (the start of the runtime), every call returns
    the native restriction, whatever the bypasses, the cap, the unavailable calls and the clears. -/
theorem runImpl_eq (hdet : KeyDetermines r key) (ops : List (Op I)) (memo : List (K × V))
    (h : Sound r key memo) : runImpl r key bypass cap ops memo = runNative r ops := by
  induction ops generalizing memo with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | call i =>
      simp only [runImpl, runNative]
      rw [step_eq r key bypass cap hdet memo h i, ih _ (step_sound r key bypass cap memo h i)]
    | unavailable i =>
      simp only [runImpl, runNative]
      rw [ih [] (empty_sound r key)]
    | clear =>
      simp only [runImpl, runNative]
      exact ih [] (empty_sound r key)

/-- A key that drops an input component that the restriction reads breaks the rule: two inputs with
    one key and two restrictions. `KeyDetermines` is therefore a real obligation of the key choice
    (spec §3.6: `link` is the only component that the key leaves out, and only the trace reads it). -/
theorem key_must_determine :
    ¬ KeyDetermines (fun i : Bool × Bool => i.2) (fun i : Bool × Bool => i.1) := by
  intro h
  have := h (true, true) (true, false) rfl
  cases this

end ApSpec.RestrictionMemoImpl
