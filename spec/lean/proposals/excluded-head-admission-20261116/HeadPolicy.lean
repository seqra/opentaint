import DeeperRecurrence
namespace HeadPolicy
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def eligible (a : Offered) (q : Seed) : Bool :=
  q.ap.tail == .star && q.ap.e.isEmpty && q.ap.base == a.ap.base &&
    a.ap.tail == .must && !a.demand &&
    match dropHead q.ap.path a.ap.path with
    | some (_ :: _) => true
    | _ => false

def retain (a : Offered) (q : Seed) : Seed :=
  if eligible a q then {q with ap := {q.ap with path := a.ap.path,e := a.ap.e}} else q

def capException (run : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed) : Bool :=
  !(run < 2 || back || d.mark.isNone || a.ap.e.isEmpty ||
      !(d.tail == .may || d.tail == .ne)) && eligible a q

def emit (run k : Nat) (back : Bool) (d : Ap) (a : Offered) : List Seed :=
  let old := CarryPolicy.emit run k back d a
  if run < 2 || back || d.mark.isNone || a.ap.e.isEmpty ||
      !(d.tail == .may || d.tail == .ne) then old else old.map (retain a)

def rawImage (run k : Nat) (back : Bool) (d : Ap) (as : List Offered) : List Ap :=
  as.flatMap fun a => (emit run k back d a).map Seed.ap

def restrictOne (run k : Nat) (back : Bool) (as : List Offered)
    (raw : Ap) (c : Value) (row : Row) : Option (Ap × Value) := do
  if (rawImage run k back row.entry as).any (fun p => decide (p=raw)) then
    let normalized := normalize raw c
    let selected ← intersectExit normalized.2 row.exit
    return normalize normalized.1 (cut (min k (row.exit.path.length+1)) selected)
  else none

theorem abstract_unchanged (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (abstract : d.mark=none) : emit run k back d a=CarryPolicy.emit run k back d a := by
  simp [emit,abstract]

theorem empty_E_unchanged (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (empty : a.ap.e=[]) : emit run k back d a=CarryPolicy.emit run k back d a := by
  simp [emit,empty]

theorem run1_unchanged (k : Nat) (back : Bool) (d : Ap) (a : Offered) :
    emit 1 k back d a=CarryPolicy.emit 1 k back d a := by simp [emit]

theorem backward_unchanged (run k : Nat) (d : Ap) (a : Offered) :
    emit run k true d a=CarryPolicy.emit run k true d a := by simp [emit]

theorem non_uniform_actual_unchanged (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (notMust : a.ap.tail≠.must) : emit run k back d a=CarryPolicy.emit run k back d a := by
  have same : retain a = id := by
    funext q
    simp [retain,eligible,notMust]
  unfold emit
  split
  · rfl
  · rw [same]; simp

theorem demand_actual_unchanged (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (demand : a.demand=true) : emit run k back d a=CarryPolicy.emit run k back d a := by
  have same : retain a = id := by
    funext q
    simp [retain,eligible,demand]
  unfold emit
  split
  · rfl
  · rw [same]; simp
theorem abstract_demands_are_exactly_the_old_policy (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (abstract : d.mark=none) :
    emit run k back d a=NonEmptyPolicy.emit run k back d a := by
  rw [abstract_unchanged run k back d a abstract]
  exact CarryPolicy.abstract_demands_are_exactly_the_old_policy run k back d a abstract

theorem empty_actual_E_is_exactly_the_old_policy (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (empty : a.ap.e=[]) :
    emit run k back d a=NonEmptyPolicy.emit run k back d a := by
  rw [empty_E_unchanged run k back d a empty]
  exact CarryPolicy.empty_actual_E_is_exactly_the_old_policy run k back d a empty
end HeadPolicy
