import Std

/-!
One counted resource at one completed handoff. "Saved" is the audited
lower bound for a native operation already bypassed, with the replacement
and accounting work charged first. A skipped future run earns no credits.
For several work counters the implementation reserves their bounds jointly.
-/
namespace HandoffBudget
set_option autoImplicit false

structure Account where
  saved : Nat
  reserved : Nat
  deriving DecidableEq, Repr

def empty : Account := ⟨0, 0⟩

def Account.credit (a : Account) (netSaved : Nat) : Account :=
  { a with saved := a.saved + netSaved }

def Account.reserve (a : Account) (upperBound : Nat) : Option Account :=
  if a.reserved + upperBound ≤ a.saved then
    some { a with reserved := a.reserved + upperBound }
  else none

theorem Account.reserve_spec (a b : Account) (upperBound : Nat)
    (ready : a.reserve upperBound = some b) :
    b.saved = a.saved ∧ b.reserved = a.reserved + upperBound ∧ b.reserved ≤ b.saved := by
  unfold Account.reserve at ready
  split at ready
  · rename_i fits
    cases ready
    exact ⟨rfl, rfl, fits⟩
  · cases ready

theorem Account.refusal (a : Account) (upperBound : Nat)
    (insufficient : a.saved < a.reserved + upperBound) :
    a.reserve upperBound = none := by
  simp [Account.reserve, Nat.not_le_of_lt insufficient]

theorem Account.credit_preserves (a : Account) (netSaved : Nat)
    (balanced : a.reserved ≤ a.saved) :
    (a.credit netSaved).reserved ≤ (a.credit netSaved).saved :=
  Nat.le_trans balanced (Nat.le_add_right _ _)

inductive Verdict where
  | covered
  | unknown
  deriving DecidableEq

structure Result where
  account : Account
  keepRow : Bool

/-- Failure consumes the reservation. The verifier runs after a successful
reservation. A covered verdict requires the separate service proof. -/
def check (a : Account) (upperBound : Nat) (verify : Unit → Verdict) : Result :=
  match a.reserve upperBound with
  | none => ⟨a, true⟩
  | some b => ⟨b, verify () == .unknown⟩

theorem check_without_credit_keeps_row (a : Account) (n : Nat)
    (verify : Unit → Verdict) (insufficient : a.saved < a.reserved + n) :
    (check a n verify).keepRow = true := by
  simp [check, Account.refusal a n insufficient]

theorem failed_check_charges_reservation (a b : Account) (n : Nat)
    (ready : a.reserve n = some b) :
    (check a n (fun _ => .unknown)).account.reserved = a.reserved + n ∧
    (check a n (fun _ => .unknown)).keepRow = true := by
  have reserved := (Account.reserve_spec a b n ready).2.1
  simp [check, ready, reserved]

theorem check_preserves_budget (a : Account) (n : Nat)
    (verify : Unit → Verdict) (balanced : a.reserved ≤ a.saved) :
    (check a n verify).account.reserved ≤ (check a n verify).account.saved := by
  unfold check
  split
  · exact balanced
  · rename_i b ready
    exact (Account.reserve_spec a b n ready).2.2

theorem modeled_work_is_no_greater (native saved reserved : Nat)
    (bounded : saved ≤ native) (paid : reserved ≤ saved) :
    native - saved + reserved ≤ native := by omega

example : (check empty 1 (fun _ => .covered)).keepRow = true := by decide

-- A failure uses both units. A later proof cannot spend the same savings.
example :
    (check (check (empty.credit 2) 2 (fun _ => .unknown)).account 1
      (fun _ => .covered)).keepRow = true := by decide

#print axioms Account.reserve_spec
#print axioms Account.refusal
#print axioms Account.credit_preserves
#print axioms check_without_credit_keeps_row
#print axioms failed_check_charges_reservation
#print axioms check_preserves_budget
#print axioms modeled_work_is_no_greater

end HandoffBudget
