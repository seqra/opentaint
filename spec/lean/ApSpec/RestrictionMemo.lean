/-
  ApSpec.RestrictionMemo — rule P2' of spec/next-iteration-p1-p3.md: a per-run memo of the loop-output
  restriction (engine/MethodBlockRuntime.kt `onApplied`).

  Model. `f : K → V` is the restriction as a function of its key (parent scope, loop, exit, original,
  bounded value, gate). In production it reads only frozen run inputs and pure caches, so it is a
  function of the key in one run. The memo is a list of (key, value) pairs. A call looks the key up;
  on a miss it computes `f k` and stores it. The memo may also be cleared at any time (production: a
  soft reference or a full map).

  Theorems.
    * `call_eq`: a call returns `f k` whenever every stored pair is (k, f k) (`Sound`).
    * `call_sound`, `clear_sound`: a call and a clear keep `Sound`.
    * `runMemo_eq`: for every sequence of calls and clears, the results are `f` of the keys.

  Constructive: no classical axioms.
-/

namespace ApSpec.RestrictionMemo

set_option linter.unusedSectionVars false

variable {K V : Type} [DecidableEq K] (f : K → V)

/-- Every stored value is the function value of its key. -/
def Sound (memo : List (K × V)) : Prop := ∀ p ∈ memo, p.2 = f p.1

def lookup : List (K × V) → K → Option V
  | [], _ => none
  | (k', v) :: rest, k => if k' = k then some v else lookup rest k

theorem lookup_sound (memo : List (K × V)) (h : Sound f memo) (k : K) (v : V)
    (hl : lookup memo k = some v) : v = f k := by
  induction memo with
  | nil => cases hl
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [lookup] at hl
    by_cases hk : k' = k
    · rw [if_pos hk] at hl
      cases hl
      have := h (k', v) (List.mem_cons_self ..)
      simp only at this
      rw [this, hk]
    · rw [if_neg hk] at hl
      exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp)) hl

/-- One call: the result and the new memo. -/
def call (memo : List (K × V)) (k : K) : V × List (K × V) :=
  match lookup memo k with
  | some v => (v, memo)
  | none => (f k, (k, f k) :: memo)

theorem call_eq (memo : List (K × V)) (h : Sound f memo) (k : K) : (call f memo k).1 = f k := by
  unfold call
  cases hl : lookup memo k with
  | none => rfl
  | some v => exact lookup_sound f memo h k v hl

theorem call_sound (memo : List (K × V)) (h : Sound f memo) (k : K) : Sound f (call f memo k).2 := by
  unfold call
  cases lookup memo k with
  | some v => exact h
  | none =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact h p hp

theorem clear_sound : Sound f ([] : List (K × V)) := by
  intro p hp; cases hp

/-- An operation: a call with a key, or a clear (soft reference cleared, or the map is full). -/
inductive Op (K : Type) where
  | call (k : K)
  | clear

/-- Run the operations; collect the results of the calls. -/
def runMemo : List (Op K) → List (K × V) → List V
  | [], _ => []
  | .clear :: ops, _ => runMemo ops []
  | .call k :: ops, memo => (call f memo k).1 :: runMemo ops (call f memo k).2

/-- The calls of the native runtime (no memo). -/
def runNative : List (Op K) → List V
  | [] => []
  | .clear :: ops => runNative ops
  | .call k :: ops => f k :: runNative ops

/-- P2' is exact: with a sound memo (for example the empty memo at the start of a run), the memo
    returns the native result for every call, whatever the clears. -/
theorem runMemo_eq (ops : List (Op K)) (memo : List (K × V)) (h : Sound f memo) :
    runMemo f ops memo = runNative f ops := by
  induction ops generalizing memo with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | clear => simp only [runMemo, runNative]; exact ih [] (clear_sound f)
    | call k =>
      simp only [runMemo, runNative]
      rw [call_eq f memo h k, ih _ (call_sound f memo h k)]

end ApSpec.RestrictionMemo
