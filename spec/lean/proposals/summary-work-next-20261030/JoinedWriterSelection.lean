import Std

/-! Match/query sharing over a fixed joined input snapshot. Selection is arbitrary
but depends only on the complete query and input. AP image application remains
per writer/input. No whole-analyzer closure or mutable input claim is made. -/
namespace JoinedWriterSelection

structure Query where
  method : Nat
  methodContext : List Nat
  initial : Nat
  run1 : Bool
  direction : Nat
  fieldLimit : Nat
  markMode : Nat
  apManager : Nat
  deriving DecidableEq, Repr

structure Writer where
  query : Query
  destination : Nat
  deriving DecidableEq, Repr

abbrev Select := Query → Nat → Bool
abbrev Apply := Writer → Nat → List Nat

def selected (q : Query) (inputs : List Nat) (select : Select) : List Nat :=
  inputs.filter (select q)

def oldResults (q : Query) (writers : List Writer) (inputs : List Nat)
    (select : Select) (apply : Apply) : List Nat :=
  writers.flatMap fun w => (selected q inputs select).flatMap (apply w)

def sharedResults (q : Query) (writers : List Writer) (inputs : List Nat)
    (select : Select) (apply : Apply) : List Nat :=
  (selected q inputs select).flatMap fun i => writers.flatMap fun w => apply w i

theorem query_selection_is_destination_independent (q : Query) (a b : Writer)
    (_ha : a.query = q) (_hb : b.query = q) (inputs : List Nat) (select : Select) :
    selected a.query inputs select = selected b.query inputs select := by
  simp [_ha, _hb]

theorem shared_selection_preserves_all_result_memberships (q : Query)
    (writers : List Writer) (inputs : List Nat) (select : Select) (apply : Apply) (output : Nat) :
    output ∈ oldResults q writers inputs select apply ↔
      output ∈ sharedResults q writers inputs select apply := by
  simp only [oldResults, sharedResults, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, i, hi, effect⟩
    exact ⟨i, hi, w, hw, effect⟩
  · rintro ⟨i, hi, w, hw, effect⟩
    exact ⟨w, hw, i, hi, effect⟩

theorem late_writer_memberships_are_not_lost (q : Query) (before after : List Writer)
    (inputs : List Nat) (select : Select) (apply : Apply) (output : Nat) :
    output ∈ sharedResults q (before ++ after) inputs select apply ↔
      output ∈ sharedResults q before inputs select apply ∨
      output ∈ sharedResults q after inputs select apply := by
  simp only [sharedResults, List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨i, hi, w, hw, effect⟩
    rcases hw with hb | ha
    · exact Or.inl ⟨i, hi, w, hb, effect⟩
    · exact Or.inr ⟨i, hi, w, ha, effect⟩
  · intro h
    rcases h with ⟨i, hi, w, hw, effect⟩ | ⟨i, hi, w, hw, effect⟩
    · exact ⟨i, hi, w, Or.inl hw, effect⟩
    · exact ⟨i, hi, w, Or.inr hw, effect⟩

def oldMatchCalls (writers : List Writer) (inputs : List Nat) : Nat := writers.length * inputs.length
def sharedMatchCalls (inputs : List Nat) : Nat := inputs.length

theorem one_nonempty_batch_never_increases_match_calls (writers : List Writer) (inputs : List Nat)
    (h : 1 ≤ writers.length) : sharedMatchCalls inputs ≤ oldMatchCalls writers inputs := by
  simpa [sharedMatchCalls, oldMatchCalls] using Nat.mul_le_mul_right inputs.length h

theorem two_writers_halve_match_calls (a b : Writer) (inputs : List Nat) :
    oldMatchCalls [a,b] inputs = 2 * sharedMatchCalls inputs := by
  simp [oldMatchCalls, sharedMatchCalls]

/-- Rejected selected atoms cannot appear in a surviving image when marking
    only filters the geometric subpart. This is a negative prefilter law. -/
def markPresent (root : List Nat) (trigger : Nat) : Bool := root.contains trigger
def filterMark (geometry : List Nat) (trigger : Nat) : List Nat := geometry.filter (· == trigger)

theorem absent_mark_rejects_every_geometric_subpart (root geometry : List Nat) (trigger : Nat)
    (part : ∀ m, m ∈ geometry → m ∈ root) (absent : markPresent root trigger = false) :
    filterMark geometry trigger = [] := by
  induction geometry with
  | nil => rfl
  | cons head tail ih =>
      have different : head ≠ trigger := by
        intro equal
        have hit := List.contains_iff_mem.mpr (part head (List.mem_cons_self))
        subst head
        unfold markPresent at absent
        rw [hit] at absent
        cases absent
      have rest := ih (fun m hm => part m (List.mem_cons_of_mem head hm))
      have flag : (head == trigger) = false := by
        cases h : (head == trigger) with
        | false => rfl
        | true => exact False.elim (different (eq_of_beq h))
      simpa only [filterMark, List.filter_cons, flag, Bool.false_eq_true, ↓reduceIte] using rest


end JoinedWriterSelection
