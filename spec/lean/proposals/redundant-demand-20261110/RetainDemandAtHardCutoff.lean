import Std

namespace RetainDemandAtHardCutoff

inductive Next where
  | abnormal
  | noDemand
  | runLimit
  | run (demand : List Nat)
  deriving DecidableEq, Repr

structure Barrier where
  complete : Bool
  forward : Bool
  index : Nat
  hardLimit : Nat
  deriving DecidableEq, Repr

/- IncreasingLimits with its production HardRunLimitPolicy wrapper. The
   demand parameter is the list of successful outgoing projection rows. -/
def next (barrier : Barrier) (demand : List Nat) : Next :=
  if !barrier.complete then .abnormal
  else if barrier.forward && demand.isEmpty then .noDemand
  else if barrier.forward && barrier.index ≥ barrier.hardLimit then .runLimit
  else .run demand

structure ReportState where
  confirmed : List Nat
  latestForward : List Nat
  deriving DecidableEq, Repr

def report (state : ReportState) : Next → List (Nat × Bool)
  | .runLimit => state.confirmed.map (·, false) ++
      (state.latestForward.filter (fun id => !state.confirmed.contains id)).map (·, true)
  | _ => state.confirmed.map (·, false)

def retained (rows : List Nat) (retire : Nat → Bool) : List Nat :=
  rows.filter fun id => !retire id

def candidate (barrier : Barrier) (rows : List Nat) (retire : Nat → Bool) (anchor : Nat) : Bool :=
  barrier.complete && barrier.forward && barrier.index == barrier.hardLimit &&
    rows.contains anchor && !retire anchor

theorem retained_anchor (rows : List Nat) (retire : Nat → Bool) (anchor : Nat)
    (member : anchor ∈ rows) (keep : retire anchor = false) : anchor ∈ retained rows retire := by
  exact List.mem_filter.mpr ⟨member, by simp [keep]⟩

theorem native_cutoff (barrier : Barrier) (rows : List Nat)
    (complete : barrier.complete = true) (forward : barrier.forward = true)
    (index : barrier.index = barrier.hardLimit) (nonempty : rows ≠ []) : next barrier rows = .runLimit := by
  cases rows with
  | nil => contradiction
  | cons head tail => simp [next, complete, forward, index]

theorem candidate_preserves_cutoff (barrier : Barrier) (rows : List Nat) (retire : Nat → Bool) (anchor : Nat)
    (ok : candidate barrier rows retire anchor = true) :
    next barrier rows = .runLimit ∧ next barrier (retained rows retire) = .runLimit := by
  simp only [candidate, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at ok
  obtain ⟨⟨⟨⟨complete, forward⟩, index⟩, member⟩, keep⟩ := ok
  refine ⟨native_cutoff barrier rows complete forward index ?_,
    native_cutoff barrier (retained rows retire) complete forward index ?_⟩
  · intro empty
    rw [empty] at member
    simp at member
  · intro empty
    have notRemoved : retire anchor = false := by cases h : retire anchor <;> simp_all
    have kept := retained_anchor rows retire anchor member notRemoved
    rw [empty] at kept
    simp at kept

theorem same_terminal_behavior (barrier : Barrier) (rows : List Nat) (retire : Nat → Bool) (anchor : Nat)
    (state : ReportState) (ok : candidate barrier rows retire anchor = true) :
    (next barrier rows, report state (next barrier rows)) =
    (next barrier (retained rows retire), report state (next barrier (retained rows retire))) := by
  obtain ⟨before, after⟩ := candidate_preserves_cutoff barrier rows retire anchor ok
  rw [before, after]

def finalBarrier : Barrier := ⟨true, true, 11, 11⟩

example : candidate finalBarrier [4, 5, 6] (· != 5) 5 = true := rfl
example : retained [4, 5, 6] (· != 5) = [5] := rfl
example : report ⟨[7], [7, 8]⟩ (next finalBarrier [5]) = [(7, false), (8, true)] := rfl
example : next finalBarrier [] = .noDemand := rfl
example : report ⟨[7], [7, 8]⟩ (next finalBarrier []) = [(7, false)] := rfl
example : next ⟨true, true, 9, 11⟩ [4, 5] ≠ next ⟨true, true, 9, 11⟩ [5] := by decide
example : candidate ⟨false, true, 11, 11⟩ [5] (fun _ => false) 5 = false := rfl
example : candidate ⟨true, false, 11, 11⟩ [5] (fun _ => false) 5 = false := rfl

end RetainDemandAtHardCutoff

#print axioms RetainDemandAtHardCutoff.retained_anchor
#print axioms RetainDemandAtHardCutoff.native_cutoff
#print axioms RetainDemandAtHardCutoff.candidate_preserves_cutoff
#print axioms RetainDemandAtHardCutoff.same_terminal_behavior
