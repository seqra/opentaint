import Std

namespace ExactMayPriority

inductive Lane where | exact | may
  deriving DecidableEq, Repr
structure Job where
  id : Nat
  lane : Lane
  deriving DecidableEq, Repr

-- This is ONE method/block owner, not the run. Exact includes its local
-- generated deliveries/publications. A reservation remains live until
-- local children are queued or reserved. It does not await a remote actor.
structure Ready where
  exact : List Nat
  may : List Nat
  busyExact : Nat
  deriving DecidableEq, Repr

def take (s : Ready) : Option (Job × Ready) :=
  match s.exact with
  | j :: rest => some (⟨j,.exact⟩,{s with exact := rest,busyExact := s.busyExact + 1})
  | [] => match s.busyExact with
    | _ + 1 => none
    | 0 => match s.may with
      | [] => none
      | j :: rest => some (⟨j,.may⟩,{s with may := rest})

theorem ready_exact_runs_first (j : Nat) (rest low : List Nat) (busy : Nat) :
    take ⟨j :: rest,low,busy⟩ = some (⟨j,.exact⟩,⟨rest,low,busy+1⟩) := rfl

theorem busy_exact_prevents_may (low : List Nat) (busy : Nat) :
    take ⟨[],low,busy+1⟩ = none := rfl

theorem may_dispatch_has_exact_quiescence (s after : Ready) (j : Nat)
    (selected : take s = some (⟨j,.may⟩,after)) :
    s.exact = [] ∧ s.busyExact = 0 := by
  cases s with
  | mk high low busy =>
    cases high with
    | cons n rest => cases selected
    | nil =>
      cases busy with
      | succ n => cases selected
      | zero => exact ⟨rfl,rfl⟩

def queued (s : Ready) : Nat := s.exact.length + s.may.length

theorem dispatch_removes_exactly_one_pending_job
    (s after : Ready) (j : Job) (selected : take s = some (j,after)) :
    queued after + 1 = queued s := by
  cases s with
  | mk high low busy =>
    cases high with
    | cons n rest =>
      cases selected
      simp only [queued,List.length_cons]
      omega
    | nil =>
      cases busy with
      | succ n => cases selected
      | zero =>
        cases low with
        | nil => cases selected
        | cons n rest => cases selected; rfl

-- A late exact arrival preempts the remaining MAY queue at the next
-- dispatch. This does not assert that exact work created by a MAY step
-- could have executed before its own cause.
theorem late_exact_preempts (high : Nat) (low : List Nat) :
    take ⟨[high],low,0⟩ = some (⟨high,.exact⟩,⟨[],low,1⟩) := rfl

-- Losing a reservation before its child publication is visible permits
-- a MAY dispatch. This is the explicit transport/barrier obligation.
theorem dropping_reservation_too_early_is_observable :
    take ⟨[],[2],1⟩ = none ∧
    take ⟨[],[2],0⟩ = some (⟨2,.may⟩,⟨[],[],0⟩) := by decide

theorem another_owner_need_not_wait :
    take ⟨[1],[],0⟩ = some (⟨1,.exact⟩,⟨[],[],1⟩) ∧
    take ⟨[],[2],0⟩ = some (⟨2,.may⟩,⟨[],[],0⟩) := by decide

#print axioms ready_exact_runs_first
#print axioms busy_exact_prevents_may
#print axioms may_dispatch_has_exact_quiescence
#print axioms dispatch_removes_exactly_one_pending_job
#print axioms late_exact_preempts
#print axioms dropping_reservation_too_early_is_observable
#print axioms another_owner_need_not_wait
end ExactMayPriority
