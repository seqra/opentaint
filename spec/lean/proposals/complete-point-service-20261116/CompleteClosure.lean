import Std
/- Executable finite certificates for a COMPLETE NORMAL return service.
   A queue-empty observation or a single positive row is not a certificate. -/
namespace CompleteClosure
set_option autoImplicit false
set_option linter.unusedSimpArgs false

inductive Reach {α : Type} (next : α → List α) (seeds : List α) : α → Prop
  | seed (s : α) : s ∈ seeds → Reach next seeds s
  | step (s t : α) : Reach next seeds s → t ∈ next s → Reach next seeds t

variable {α : Type} [DecidableEq α]

def check (next : α → List α) (seeds owned : List α)
    (returned covered : α → Bool) : Bool :=
  seeds.all (fun s => decide (s ∈ owned)) &&
  owned.all (fun s => (next s).all (fun t => decide (t ∈ owned))) &&
  owned.all (fun s => !returned s || covered s)

theorem complete_closure (next : α → List α) (seeds owned : List α)
    (returned covered : α → Bool) (ok : check next seeds owned returned covered = true)
    (s : α) (reached : Reach next seeds s) : s ∈ owned := by
  have h := ok
  simp only [check,Bool.and_eq_true] at h
  have seed := List.all_eq_true.mp h.1.1
  have closed := List.all_eq_true.mp h.1.2
  induction reached with
  | seed s hs => exact of_decide_eq_true (seed s hs)
  | step s t _ ht ih => exact of_decide_eq_true (List.all_eq_true.mp (closed s ih) t ht)

theorem every_reachable_return_is_covered (next : α → List α) (seeds owned : List α)
    (returned covered : α → Bool) (ok : check next seeds owned returned covered = true)
    (s : α) (reached : Reach next seeds s) (exit : returned s = true) : covered s = true := by
  have hs := complete_closure next seeds owned returned covered ok s reached
  have h := List.all_eq_true.mp (by simpa only [check,Bool.and_eq_true] using ok :
      (seeds.all (fun s => decide (s ∈ owned)) = true ∧
       owned.all (fun s => (next s).all (fun t => decide (t ∈ owned))) = true) ∧
       owned.all (fun s => !returned s || covered s) = true).2 s hs
  simpa [exit] using h

/-- A whole-row service witness, not overlap with one convenient child. -/
def hasWitness (service : List α) (covers : α → α → Bool) (s : α) : Bool :=
  service.any (fun n => covers n s)

theorem a_concrete_normal_service_witness (next : α → List α) (seeds owned service : List α)
    (returned : α → Bool) (covers : α → α → Bool)
    (ok : check next seeds owned returned (hasWitness service covers) = true)
    (s : α) (reached : Reach next seeds s) (exit : returned s = true) :
    ∃ n ∈ service, covers n s = true := by
  exact List.any_eq_true.mp
    (every_reachable_return_is_covered next seeds owned returned _ ok s reached exit)

/-- Abstract proof of caller preservation for ANY continuation observation.
    The NORMAL witness is actually applied before coarse current replies are omitted. -/
theorem caller_observation_is_preserved (next : α → List α) (seeds owned service : List α)
    (returned : α → Bool) (covers : α → α → Bool) (observe : α → Prop)
    (ok : check next seeds owned returned (hasWitness service covers) = true)
    (native : ∀ n ∈ service, ∀ s, covers n s = true → observe s → observe n)
    (s : α) (reached : Reach next seeds s) (exit : returned s = true) (seen : observe s) :
    ∃ n ∈ service, observe n := by
  rcases a_concrete_normal_service_witness next seeds owned service returned covers ok s reached exit
    with ⟨n,hn,cover⟩
  exact ⟨n,hn,native n hn s cover seen⟩

/-- Certificates compose bottom up. The caller uses the real closed normal
    child relation as its step; it does not guess completion from demand silence. -/
theorem compose_complete_services (callerNext : α → List α) (seeds owned : List α)
    (returned covered : α → Bool)
    (ok : check callerNext seeds owned returned covered = true)
    (childNext : α → List α)
    (childCover : ∀ s ∈ owned, ∀ t ∈ childNext s, t ∈ callerNext s)
    (s : α) (reached : Reach childNext seeds s) : s ∈ owned := by
  induction reached with
  | seed s hs =>
      exact complete_closure callerNext seeds owned returned covered ok s (.seed s hs)
  | step s t _ ht ih =>
      have h := ok
      simp only [check,Bool.and_eq_true] at h
      exact of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp h.1.2 s ih) t (childCover s ih t ht))

-- Small rejection tests: the missing branch is precisely the unsafe case.
def next (n : Nat) : List Nat := if n == 0 then [1,2] else []
def returned (n : Nat) := n != 0

theorem one_positive_row_is_insufficient :
    check next [0] [0,1] returned (fun _ => true) = false := by decide

theorem c5_discarded_return_invalidates_completion :
    check next [0] [0,1,2] returned (fun n => n == 1) = false := by decide

theorem complete_closed_service_is_accepted :
    check next [0] [0,1,2] returned (fun n => n == 1 || n == 2) = true := by decide

theorem absent_seed_is_rejected :
    check next [0] [1,2] returned (fun _ => true) = false := by decide

theorem empty_service_requires_a_complete_no_return_analysis :
    check (fun (_ : Nat) => []) [0] [0] (fun _ => false) (fun _ => false) = true := by decide

end CompleteClosure
