import Std

/-!
Prepared scalar MAY/T/DEMAND reference. Owner fixes complete P, direction,
scope, ports, mark, layer and E. Only conclusion path and H vary. This models
the proposed same-H rule and exposes its interaction with exact flag-OR.
It is not a native store implementation or a selected resolution.
-/
namespace FlagMatchedSubsumption
set_option autoImplicit false

structure Row where
  owner : Nat
  path : List Nat
  h : Bool
  deriving DecidableEq

def prefixB : List Nat → List Nat → Bool
  | [],_ => true
  | _ :: _,[] => false
  | first :: rest,head :: tail => decide (first = head) && prefixB rest tail

def samePoint (left right : Row) : Bool :=
  decide (left.owner = right.owner ∧ left.path = right.path)

def subsumes (left right : Row) : Bool :=
  decide (left.owner = right.owner ∧ left.h = right.h) && prefixB left.path right.path

/-- Candidate eager canonical-only update: exact duplicates OR flags first,
then remove only same-H covered rows. It deliberately keeps no raw history. -/
def offer (current : List Row) (incoming : Row) : List Row :=
  let joined : Row := ⟨incoming.owner,incoming.path,
    incoming.h || (current.any (fun old => samePoint old incoming && old.h))⟩
  let other := current.filter (fun old => !samePoint old joined)
  if other.any (fun old => subsumes old joined) then other
  else joined :: other.filter (fun old => !subsumes joined old)

def run (offered : List Row) : List Row := offered.foldl offer []
def present (row : Row) (rows : List Row) : Bool := decide (row ∈ rows)
def pass (row : Row) : Row := row

theorem subsumption_requires_same_flag (left right : Row)
    (accepted : subsumes left right = true) : left.h = right.h := by
  have guards : decide (left.owner = right.owner ∧ left.h = right.h) = true :=
    ((Bool.and_eq_true _ _).mp accepted).1
  exact (of_decide_eq_true guards).2

theorem opposite_flags_never_subsume (left right : Row) (different : left.h ≠ right.h) :
    subsumes left right = false := by simp [subsumes,different]

theorem changing_both_flags_together_keeps_geometry_test (left right : Row) (flag : Bool) :
    subsumes {left with h := flag} {right with h := flag} =
      (decide (left.owner = right.owner) && prefixB left.path right.path) := by
  by_cases sameOwner : left.owner = right.owner <;> simp [subsumes,sameOwner]

theorem pass_keeps_the_input_flag (row : Row) : (pass row).h = row.h := rfl
theorem pass_cannot_introduce_H (row : Row) (plain : row.h = false) : (pass row).h = false := plain

def parent (flag : Bool) : Row := ⟨42,[],flag⟩
def child (flag : Bool) : Row := ⟨42,[7],flag⟩

theorem same_plain_parent_child_both_orders :
    run [parent false,child false] = [parent false] ∧
    run [child false,parent false] = [parent false] := by decide

theorem same_protected_parent_child_both_orders :
    run [parent true,child true] = [parent true] ∧
    run [child true,parent true] = [parent true] := by decide

theorem cross_flag_coverage_is_rejected_both_ways :
    subsumes (parent false) (child true) = false ∧
    subsumes (parent true) (child false) = false := by decide

theorem mixed_flag_rows_are_kept_in_both_orders :
    present (parent false) (run [parent false,child true]) = true ∧
    present (child true) (run [parent false,child true]) = true ∧
    present (parent false) (run [child true,parent false]) = true ∧
    present (child true) (run [child true,parent false]) = true := by decide

theorem exact_duplicate_flag_OR_still_wins :
    run [parent false,parent true] = [parent true] ∧
    run [parent true,parent false] = [parent true] := by decide

theorem repeated_identical_flag_is_not_new_state :
    run [parent true,parent true] = [parent true] ∧
    run [parent false,parent false] = [parent false] := by decide

def childBeforeUpgrade : List Row := run [parent false,child false,parent true]
def childAfterUpgrade : List Row := run [parent true,parent false,child false]

theorem pruned_plain_child_is_missing_after_late_parent_flag_upgrade :
    childBeforeUpgrade = [parent true] ∧
    present (child false) childBeforeUpgrade = false := by decide

theorem same_plain_child_is_retained_if_offered_after_parent_upgrade :
    childAfterUpgrade = [child false,parent true] ∧
    present (child false) childAfterUpgrade = true := by decide

theorem exact_OR_plus_strict_flag_partition_is_not_arrival_invariant :
    childBeforeUpgrade ≠ childAfterUpgrade := by decide

theorem both_histories_still_keep_the_exact_protected_parent :
    present (parent true) childBeforeUpgrade = true ∧
    present (parent true) childAfterUpgrade = true := by decide

theorem wrong_owner_never_supplies_coverage :
    subsumes (parent false) ⟨43,[7],false⟩ = false := by decide

end FlagMatchedSubsumption
