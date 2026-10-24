/- FLOW priority within the existing nonzero phase. ZERO is chosen outside
   this kernel. Remaining-credit is a finite-domain proof measure only. -/
import Std

namespace ApSpec.FlowBackedPriority

structure Ready (α : Type) where
  flowUnchanged : List α := []
  flowChanged : List α := []
  taintUnchanged : List α := []
  taintChanged : List α := []
deriving Repr

def Ready.linear {α} (q : Ready α) : List α :=
  q.flowUnchanged ++ q.flowChanged ++ q.taintUnchanged ++ q.taintChanged

def pop {α} (q : Ready α) : Option (α × Ready α) :=
  match q.flowUnchanged with
  | x :: xs => some (x, { q with flowUnchanged := xs })
  | [] => match q.flowChanged with
    | x :: xs => some (x, { q with flowChanged := xs })
    | [] => match q.taintUnchanged with
      | x :: xs => some (x, { q with taintUnchanged := xs })
      | [] => match q.taintChanged with
        | x :: xs => some (x, { q with taintChanged := xs })
        | [] => none

theorem pop_exact {α} (q : Ready α) :
    (pop q).map (fun r => (r.1, r.2.linear)) =
      q.linear.head?.map (fun x => (x, q.linear.tail)) := by
  cases q with | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem flow_changed_precedes_taint_unchanged {α} (x : α) (xs ts ds : List α) :
    pop ⟨[], x :: xs, ts, ds⟩ = some (x, ⟨[], xs, ts, ds⟩) := rfl

theorem pop_decreases {α} (q q' : Ready α) (x : α) (h : pop q = some (x, q')) :
    q'.linear.length + 1 = q.linear.length := by
  have he := pop_exact q
  rw [h] at he
  cases hl : q.linear with
  | nil => simp [hl] at he
  | cons a rest =>
    simp only [hl, List.head?_cons, List.tail_cons, Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at he
    simp [he.2]

theorem empty_iff_drained {α} (q : Ready α) : pop q = none ↔ q.linear = [] := by
  cases q with | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> simp [pop, Ready.linear]

/-- A process step consumes one ready atom and charges fresh queued atoms
    against finite remaining admission credit. No old atom is re-admitted. -/
theorem finite_measure_decreases (pending credit fresh : Nat)
    (nonempty : 0 < pending) (withinCredit : fresh ≤ credit) :
    (pending - 1 + fresh) + (credit - fresh) < pending + credit := by omega

/-- Deciding a barrier must include every deferred continuation/flag lane. -/
def barrierReady (main continuations protectionUpdates : Nat) : Bool :=
  main == 0 && continuations == 0 && protectionUpdates == 0

theorem barrier_drained (a b c : Nat) : barrierReady a b c = true ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  simp [barrierReady, Bool.and_eq_true, and_assoc]

def controls : List Bool := [
  decide ((pop (⟨[], [1], [2], [3]⟩ : Ready Nat)).map Prod.fst = some 1),
  decide ((pop (⟨[4], [1], [2], [3]⟩ : Ready Nat)).map Prod.fst = some 4),
  decide ((pop (⟨[], [], [2], [3]⟩ : Ready Nat)).map Prod.fst = some 2),
  decide ((pop (⟨[], [], [], [3]⟩ : Ready Nat)).map Prod.fst = some 3),
  decide ((pop (⟨[], [], [], []⟩ : Ready Nat)).isNone),
  decide (barrierReady 0 0 1 = false),
  decide (barrierReady 0 1 0 = false),
  decide (barrierReady 0 0 0 = true)
]

#print axioms pop_exact
#print axioms flow_changed_precedes_taint_unchanged
#print axioms pop_decreases
#print axioms empty_iff_drained
#print axioms finite_measure_decreases
#print axioms barrier_drained
end ApSpec.FlowBackedPriority
