import Std

namespace ObservationPlan
set_option autoImplicit false

/- The native binding maps complete scoped/layered descriptors injectively to Nat.
   Canonical lists represent exact observation sets. This model does not assert
   that two different native query keys are equivalent. -/
structure Observation where
  c2 : List Nat
  enclosing : List Nat
  deriving DecidableEq, Repr

def extra (base trial : List Nat) : Option Nat :=
  trial.find? (fun x => !(decide (x ∈ base)))

theorem extra_sound (base trial : List Nat) (w : Nat)
    (h : extra base trial = some w) : w ∈ trial ∧ w ∉ base := by
  induction trial with
  | nil => simp [extra] at h
  | cons x xs ih =>
    by_cases hx : x ∈ base
    · have rest : extra base xs = some w := by simpa [extra, List.find?, hx] using h
      obtain ⟨mem, absent⟩ := ih rest
      exact ⟨List.mem_cons_of_mem x mem, absent⟩
    · have eq : x = w := by simpa [extra, List.find?, hx] using h
      subst w
      exact ⟨List.mem_cons_self, hx⟩

theorem extra_rejects (base trial : Observation) (w : Nat)
    (h : extra base.c2 trial.c2 = some w) : trial ≠ base := by
  obtain ⟨mem, absent⟩ := extra_sound _ _ _ h
  intro eq
  subst trial
  exact absent mem

structure Trial where
  budget : Nat
  result : Observation
  deriving DecidableEq, Repr

def choose (base : Observation) : List Trial → Option Nat
  | [] => none
  | t :: ts => if t.result = base then some t.budget else choose base ts

def viable (base : Observation) (t : Trial) : Bool :=
  (extra base.c2 t.result.c2).isNone

theorem not_viable_rejects (base : Observation) (t : Trial)
    (h : viable base t = false) : t.result ≠ base := by
  unfold viable at h
  generalize eq : extra base.c2 t.result.c2 = found at h
  cases found with
  | none => simp at h
  | some w => exact extra_rejects _ _ _ eq

theorem prune_preserves_first (base : Observation) (ts : List Trial) :
    choose base (ts.filter (viable base)) = choose base ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases h : viable base t with
    | false =>
      have no := not_viable_rejects base t h
      simpa [List.filter_cons, h, choose, no] using ih
    | true =>
      simp only [List.filter_cons, h, ↓reduceIte, choose]
      split
      · rfl
      · exact ih

theorem all_bad_has_no_cut (base : Observation) (ts : List Trial)
    (h : ts.all (fun t => !(viable base t)) = true) : choose base ts = none := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have pair : viable base t = false ∧ ts.all (fun t => !(viable base t)) = true := by
      simpa [List.all_cons, Bool.and_eq_true] using h
    have ht := pair.1
    have rest := pair.2
    have no := not_viable_rejects base t ht
    simpa [choose, no] using ih rest

def decideResult (base : Observation) (ts : List Trial) : String :=
  if base.c2.isEmpty && base.enclosing.isEmpty then "DROP"
  else if (choose base ts).isSome then "CUT" else "RAW"

theorem nonempty_c2_all_bad_returns_raw (base : Observation) (ts : List Trial)
    (nonempty : base.c2.isEmpty = false)
    (bad : ts.all (fun t => !(viable base t)) = true) :
    decideResult base ts = "RAW" := by
  simp [decideResult, nonempty, all_bad_has_no_cut base ts bad]

/- Exact query cells may be shared only under equality of the complete key. -/
theorem equal_key_query_equal (query : Nat → Observation) (a b : Nat) (h : a = b) :
    query a = query b := congrArg query h

#print axioms extra_sound
#print axioms extra_rejects
#print axioms not_viable_rejects
#print axioms prune_preserves_first
#print axioms all_bad_has_no_cut
#print axioms nonempty_c2_all_bad_returns_raw
#print axioms equal_key_query_equal
end ObservationPlan
