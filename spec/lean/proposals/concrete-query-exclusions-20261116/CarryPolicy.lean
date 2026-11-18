import Recurrence

/- Restricted FULL concrete demand families only. Keep the old family and
   its cardinality. If a STAR initial keeps the actual head, retain the
   actual's real E there, including on its same-geometry FLOW companion.
   FLOW demand families, empty E, every different head, and run-1 are old. -/
namespace CarryPolicy
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def eligible (a : Offered) (q : Seed) : Bool :=
  q.ap.tail == .star && q.ap.base == a.ap.base && q.ap.path == a.ap.path &&
    q.ap.e.isEmpty && (a.ap.tail == .star || a.ap.tail == .must)

def carry (a : Offered) (q : Seed) : Seed :=
  if eligible a q then
    {q with ap := {q.ap with e := a.ap.e}}
  else q

def emit (run k : Nat) (back : Bool) (d : Ap) (a : Offered) : List Seed :=
  let old := NonEmptyPolicy.emit run k back d a
  if run < 2 || d.mark.isNone || a.ap.e.isEmpty then old else old.map (carry a)

def rawImage (run k : Nat) (back : Bool) (d : Ap) (as : List Offered) : List Ap :=
  as.flatMap fun a => (emit run k back d a).map Seed.ap

def restrictOne (run limit : Nat) (back : Bool) (as : List Offered)
    (raw : Ap) (c : Value) (row : Row) : Option (Ap × Value) := do
  if (rawImage run limit back row.entry as).any (fun k => decide (k = raw)) then
    let normalized := normalize raw c
    let selected ← intersectExit normalized.2 row.exit
    return normalize normalized.1 (cut (min limit (row.exit.path.length+1)) selected)
  else none

theorem abstract_demands_are_exactly_the_old_policy (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (abstract : d.mark = none) :
    emit run k back d a = NonEmptyPolicy.emit run k back d a := by simp [emit,abstract]

theorem empty_actual_E_is_exactly_the_old_policy (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (empty : a.ap.e = []) :
    emit run k back d a = NonEmptyPolicy.emit run k back d a := by simp [emit,empty]

theorem run1_is_exactly_the_old_policy (k : Nat) (back : Bool) (d : Ap) (a : Offered) :
    emit 1 k back d a = NonEmptyPolicy.emit 1 k back d a := by simp [emit]

end CarryPolicy
