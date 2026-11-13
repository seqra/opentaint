import Policy

namespace NonEmptyRestriction
open NonEmptyPolicy

structure Value where
  ap : Ap
  demand : Bool := false
  h : Bool := false
  deriving DecidableEq, BEq, Repr
structure Row where
  entry : Ap
  exit : Ap
  deriving DecidableEq, BEq, Repr

def marksMeet (a d : Ap) : Bool :=
  match a.mark,d.mark with
  | some t,some u => t == u
  | some t,none => !d.mx.contains t
  | none,some t => !a.mx.contains t
  | none,none => true

def exactAt (c : Value) (p : Path) : Value :=
  {c with ap := {c.ap with path := p,tail := .exact,e := (if c.ap.mark.isNone && c.ap.tail == .must && p == c.ap.path then c.ap.e else [])}}

def intersectExit (c : Value) (inputExit : Ap) : Option Value :=
  let d := selector inputExit
  -- NE cannot be an owned initial, hence cannot be a projected Dp.
  if d.tail == .ne || c.ap.base != d.base || !marksMeet c.ap d then none
  else if c.ap.path == d.path then
    match c.ap.tail with
    | .exact | .star => some c
    | .ne => if d.tail == .exact then none else some c
    | .may => some (if d.tail == .exact then exactAt c d.path else c)
    | .must => some (if d.tail == .exact then exactAt c d.path
        else if d.tail == .star then {c with ap := {c.ap with e := c.ap.e ++ d.e}}
        else c)
  else match dropHead d.path c.ap.path with
  | some (f :: rest) => if admits d.tail d.e (f :: rest) then some c else none
  | _ => match dropHead c.ap.path d.path with
      | some (f :: rest) =>
        if !admits c.ap.tail c.ap.e (f :: rest) then none
        else match c.ap.tail with
          | .exact => none
          | .star => some c
          | .may | .ne =>
            if d.tail == .exact then some (exactAt c d.path)
            else some {c with ap := {c.ap with path := d.path,tail := .may,e := []}}
          | .must =>
            if d.tail == .exact then some (exactAt c d.path)
            else some {c with ap := {c.ap with path := d.path,e := (if d.tail == .star then d.e else [])}}
      | _ => none

def cut (budget : Nat) (c : Value) : Value :=
  if c.ap.path.length > budget then
    {c with ap := {c.ap with path := c.ap.path.take budget,tail := .ne,e := []},demand := true}
  else c

def normalize (p : Ap) (c : Value) : Ap × Value :=
  if p.mark.isNone && c.ap.mark.isNone then
    (normalAp p,{c with ap := normalAp c.ap})
  else (p,c)

def restrictOne (run limit : Nat) (backward : Bool) (domain : List Offered)
    (raw : Ap) (candidate : Value) (row : Row) : Option (Ap × Value) := do
  if (rawImage run limit backward row.entry domain).any (fun key => decide (key = raw)) then
    let normalized := normalize raw candidate
    let selected ← intersectExit normalized.2 row.exit
    let bounded := cut (min limit (row.exit.path.length + 1)) selected
    return normalize normalized.1 bounded
  else none

theorem real_cut_has_ne_demand_and_keeps_mark_protection
    (budget : Nat) (c : Value) (h : c.ap.path.length > budget) :
    (cut budget c).ap.tail = .ne ∧ (cut budget c).demand = true ∧
    (cut budget c).ap.mark = c.ap.mark ∧
    (cut budget c).h = c.h := by
  simp [cut,h]

theorem no_cut_preserves_intrinsic_may (budget : Nat) (c : Value)
    (h : c.ap.path.length ≤ budget) : cut budget c = c := by
  simp [cut,Nat.not_lt.mpr h]

theorem cut_respects_depth (budget : Nat) (c : Value) :
    (cut budget c).ap.path.length ≤ budget := by
  unfold cut
  split
  · simp only [List.length_take]
    exact Nat.min_le_left _ _
  · rename_i h
    exact Nat.le_of_not_lt h

theorem cut_never_upgrades_demand (budget : Nat) (c : Value)
    (h : c.demand = true) : (cut budget c).demand = true := by
  unfold cut; split <;> simp_all

theorem normalize_preserves_paths_marks_layers_protection (p : Ap) (c : Value) :
    (normalize p c).1.path = p.path ∧
    (normalize p c).2.ap.path = c.ap.path ∧
    (normalize p c).2.ap.mark = c.ap.mark ∧
    (normalize p c).2.demand = c.demand ∧
    (normalize p c).2.h = c.h := by
  simp only [normalize]
  split
  · simp only [normalAp]; split <;> split <;> simp
  · simp

theorem normalize_does_not_erase_ne (p : Ap) (c : Value) (h : c.ap.tail = .ne) :
    (normalize p c).2.ap.tail = .ne := by
  unfold normalize
  split
  · change (normalAp c.ap).tail = .ne
    unfold normalAp
    have no : ¬ (c.ap.tail == .exact) = true := by rw [h]; decide
    rw [if_neg no]
    exact h
  · exact h

theorem every_admitted_summary_has_the_actual_raw_witness
    (run limit : Nat) (backward : Bool) (domain : List Offered)
    (raw : Ap) (c : Value) (row : Row) (result : Ap × Value)
    (h : restrictOne run limit backward domain raw c row = some result) :
    ∃ a ∈ domain, ∃ command ∈ emit run limit backward row.entry a, command.ap = raw := by
  unfold restrictOne at h
  split at h
  · rename_i accepted
    rcases List.any_eq_true.mp accepted with ⟨key,member,same⟩
    have eq : key = raw := of_decide_eq_true same
    rw [eq] at member
    exact raw_image_has_constructive_offer run limit backward row.entry domain raw member
  · simp at h

theorem final_summary_keeps_its_own_row_bound
    (run limit : Nat) (backward : Bool) (domain : List Offered)
    (raw : Ap) (c : Value) (row : Row) (result : Ap × Value)
    (h : restrictOne run limit backward domain raw c row = some result) :
    result.2.ap.path.length ≤ min limit (row.exit.path.length + 1) := by
  unfold restrictOne at h
  split at h
  · dsimp only at h
    cases selected : intersectExit (normalize raw c).2 row.exit with
    | none => simp [selected] at h
    | some value =>
      simp only [selected] at h
      change some (normalize (normalize raw c).1
        (cut (min limit (row.exit.path.length+1)) value)) = some result at h
      have same := Option.some.inj h
      rw [← same]
      rw [(normalize_preserves_paths_marks_layers_protection
        (normalize raw c).1 (cut (min limit (row.exit.path.length+1)) value)).2.1]
      exact cut_respects_depth _ _
  · simp at h

def v (tail : Tail) (path : Path := []) (mark : Option Nat := some 7)
    (demand : Bool := true) : Value := ⟨⟨0,path,tail,mark,[],[]⟩,demand,false⟩
def out (tail : Tail) (path : Path := []) : Ap := ⟨0,path,tail,some 7,[],[]⟩

theorem ne_does_not_supply_exact_same_head_exit :
    intersectExit (v .ne) (out .exact) = none := by decide
theorem ne_can_supply_a_deeper_exact_exit :
    intersectExit (v .ne) (out .exact [1]) = some (v .exact [1]) := by decide
theorem nonempty_descent_resets_the_residual_to_may :
    intersectExit (v .ne) (out .star [1]) = some (v .may [1]) := by decide
theorem same_head_star_exit_keeps_ne :
    intersectExit (v .ne) (out .star) = some (v .ne) := by decide
theorem intrinsic_may_still_supplies_exact_exit_without_confirmation :
    intersectExit (v .may) (out .exact) = some (v .exact) := by decide
theorem actual_field_cut_produces_ne_not_may :
    cut 1 (v .exact [1,2,3] (some 7) false) = v .ne [1] := by decide
theorem correlated_star_is_kept_whole_during_exit_selection :
    intersectExit (v .star [] none false) (out .star [1]) =
      some (v .star [] none false) := by decide
theorem raw_exact_cannot_borrow_the_normalized_star_witness :
    restrictOne 3 2 false [⟨flow .may,true⟩] (flow .exact)
      (v .exact [] none false) ⟨flow .ne,out .star⟩ = none := by decide
theorem two_rows_keep_their_own_exit_budget :
    cut (min 4 (0+1)) (v .exact [1,2,3] (some 7) false) = v .ne [1] ∧
    cut (min 4 (2+1)) (v .exact [1,2,3] (some 7) false) =
      v .exact [1,2,3] (some 7) false := by decide

#print axioms real_cut_has_ne_demand_and_keeps_mark_protection
#print axioms no_cut_preserves_intrinsic_may
#print axioms cut_respects_depth
#print axioms cut_never_upgrades_demand
#print axioms normalize_preserves_paths_marks_layers_protection
#print axioms normalize_does_not_erase_ne
#print axioms every_admitted_summary_has_the_actual_raw_witness
#print axioms final_summary_keeps_its_own_row_bound
#print axioms ne_does_not_supply_exact_same_head_exit
#print axioms ne_can_supply_a_deeper_exact_exit
#print axioms nonempty_descent_resets_the_residual_to_may
#print axioms same_head_star_exit_keeps_ne
#print axioms intrinsic_may_still_supplies_exact_exit_without_confirmation
#print axioms actual_field_cut_produces_ne_not_may
#print axioms correlated_star_is_kept_whole_during_exit_selection
#print axioms raw_exact_cannot_borrow_the_normalized_star_witness
#print axioms two_rows_keep_their_own_exit_budget

end NonEmptyRestriction
