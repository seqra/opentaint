import Geometry

/-!
Executable empty-E, concrete-FULL scalar C5 followed by the proposed cut.

The old relation is dp -> dc. The current initial is tested against dc;
its produced conclusion is restricted against dp. One Row supplies both
tests and the cut budget. No cross-row entry/exit product is formed.

The entry-image table models nonzero concrete data initials. JVM static
anchor validity remains an adapter obligation. The exit table is the
current scalar tail/path table, including the correlated STAR ancestor
keep. Exclusions are empty in this module. FLOW mark exclusions, packed
forests, ND support, typed controls, caches and report observations require
separate adapters. These theorems establish local restriction/cut laws;
they do not assert whole-analyzer completeness or cross-run termination.
-/
namespace RelativeRestriction
set_option autoImplicit false

structure Context where
  global : Nat
  run2 : Bool := false
  forward : Bool := true
  deriving DecidableEq, Repr

structure Row where
  id : Nat
  dc : Pattern
  dp : Pattern
  deriving DecidableEq, Repr

/-- The frozen-demand/global-budget adapter supplies these well-formedness
    facts. The local algebra below is also defined on a wider test domain. -/
def rowWellFormed (context : Context) (row : Row) : Prop :=
  0 < context.global ∧ depth row.dc.path ≤ context.global ∧
    depth row.dp.path ≤ context.global ∧ row.dc.tail ≠ .must

/-- A suffix ends immediately after its first counted accessor. -/
def oneNewField : Path → Bool
  | [] => false
  | .classId _ :: rest => oneNewField rest
  | .field _ :: [] => true
  | .element :: [] => true
  | _ => false

def entryShape (context : Context) (dc initial : Pattern) : Bool :=
  if initial.path = dc.path then
    match initial.tail with
    | .exact => decide (dc.tail ≠ .must)
    | .may => decide (dc.tail = .may)
    | .must => decide (dc.tail = .may) && context.forward
    | .star => context.run2 && decide (dc.tail = .star) && decide (depth dc.path < context.global)
  else if dc.tail = .may ∧ dc.path.IsPrefix initial.path ∧
      oneNewField (initial.path.drop dc.path.length) = true then
    decide (initial.tail = .exact ∨ initial.tail = .star)
  else false

/-- Concrete, empty-E C2 image used by the existing paired C5 entry gate. -/
def entryImage (context : Context) (dc initial : Pattern) : Bool :=
  decide (dc.base = initial.base ∧ dc.mark = initial.mark ∧
    depth dc.path ≤ context.global ∧ depth initial.path ≤ context.global ∧
    (initial.tail ≠ .must ∨ context.forward = true)) && entryShape context dc initial

def meetTail (raw selected : Tail) : Tail :=
  match raw, selected with
  | .may, .exact | .must, .exact => .exact
  | _, _ => raw

def tailDescends : Tail → Bool
  | .exact => false
  | .star | .may | .must => true

/-- The current C5 exit table. It may keep a longer descendant unchanged. -/
def exitGeometry (dp raw : Pattern) : Option (Path × Tail) :=
  if dp.base ≠ raw.base ∨ dp.mark ≠ raw.mark then none
  else if raw.path = dp.path then some (raw.path,meetTail raw.tail dp.tail)
  else if dp.path.IsPrefix raw.path then
    if tailDescends dp.tail then some (raw.path,raw.tail) else none
  else if raw.path.IsPrefix dp.path then
    match raw.tail with
    | .may | .must => some (dp.path,if dp.tail = .exact then .exact else raw.tail)
    | .star => some (raw.path,raw.tail)
    | .exact => none
  else none

def restrictExit (raw : Scalar) (dp : Pattern) : Option Scalar :=
  (exitGeometry dp raw.toPattern).map fun geometry =>
    {raw with path := geometry.1,tail := geometry.2}

/-- This is restriction before abstraction. Its layer is exactly the raw layer. -/
def existingC5 (context : Context) (row : Row) (initial : Pattern) (raw : Scalar) : Option Scalar :=
  if entryImage context row.dc initial then restrictExit raw row.dp else none

/-- The per-pair operation; every candidate is processed, NORMAL and DEMAND alike. -/
def restrictRow (context : Context) (row : Row) (initial : Pattern) (raw : Scalar) : Option Scalar :=
  (existingC5 context row initial raw).map (limit (pairBudget context.global row.dp))

structure Admitted where
  row : Row
  initial : Pattern
  result : Scalar
  deriving DecidableEq, Repr

/-- Only the accepted result and its complete row are returned, never a raw cache. -/
def admitRow (context : Context) (row : Row) (initial : Pattern) (raw : Scalar) : Option Admitted :=
  (restrictRow context row initial raw).map fun result => ⟨row,initial,result⟩

def admitRows (context : Context) (rows : List Row) (initial : Pattern) (raw : Scalar) : List Admitted :=
  rows.filterMap fun row => admitRow context row initial raw

theorem one_new_field_has_depth_one (suffix : Path) (fresh : oneNewField suffix = true) :
    depth suffix = 1 := by
  induction suffix with
  | nil => cases fresh
  | cons accessor rest ih =>
    cases accessor with
    | classId value => exact ih fresh
    | field value =>
      cases rest with
      | nil => rfl
      | cons next later => cases fresh
    | element =>
      cases rest with
      | nil => rfl
      | cons next later => cases fresh

theorem entry_shape_depth_step (context : Context) (dc initial : Pattern)
    (accepted : entryShape context dc initial = true) : depth initial.path ≤ depth dc.path + 1 := by
  unfold entryShape at accepted
  split at accepted
  next same =>
    rw [same]
    exact Nat.le_succ _
  next different =>
    split at accepted
    next extension =>
      obtain ⟨_,prefixProof,fresh⟩ := extension
      obtain ⟨suffix,same⟩ := prefixProof
      have suffixFresh : oneNewField suffix = true := by
        rw [← same,List.drop_append_length] at fresh
        exact fresh
      have suffixDepth := one_new_field_has_depth_one suffix suffixFresh
      rw [← same,depth_append,suffixDepth]
      exact Nat.le_refl _
    next => cases accepted

theorem entry_image_depth_step (context : Context) (dc initial : Pattern)
    (accepted : entryImage context dc initial = true) : depth initial.path ≤ depth dc.path + 1 :=
  entry_shape_depth_step context dc initial (Bool.and_eq_true_iff.mp accepted).2

theorem entry_image_base_and_mark (context : Context) (dc initial : Pattern)
    (accepted : entryImage context dc initial = true) : dc.base = initial.base ∧ dc.mark = initial.mark := by
  have guards := of_decide_eq_true (Bool.and_eq_true_iff.mp accepted).1
  exact ⟨guards.1,guards.2.1⟩

theorem existing_c5_requires_this_entry (context : Context) (row : Row) (initial : Pattern)
    (raw selected : Scalar) (accepted : existingC5 context row initial raw = some selected) :
    entryImage context row.dc initial = true := by
  unfold existingC5 at accepted
  split at accepted
  next yes => exact yes
  next => cases accepted

theorem existing_c5_uses_this_exit (context : Context) (row : Row) (initial : Pattern)
    (raw selected : Scalar) (accepted : existingC5 context row initial raw = some selected) :
    restrictExit raw row.dp = some selected := by
  unfold existingC5 at accepted
  split at accepted
  next => exact accepted
  next => cases accepted

theorem exit_restriction_preserves_metadata (raw selected : Scalar) (dp : Pattern)
    (accepted : restrictExit raw dp = some selected) :
    selected.base = raw.base ∧ selected.mark = raw.mark ∧
    selected.protection = raw.protection ∧ selected.layer = raw.layer := by
  unfold restrictExit at accepted
  cases geometry : exitGeometry dp raw.toPattern with
  | none => simp only [geometry,Option.map_none] at accepted; cases accepted
  | some pair =>
    simp only [geometry,Option.map_some,Option.some.injEq] at accepted
    cases accepted
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem existing_c5_preserves_metadata (context : Context) (row : Row) (initial : Pattern)
    (raw selected : Scalar) (accepted : existingC5 context row initial raw = some selected) :
    selected.base = raw.base ∧ selected.mark = raw.mark ∧
    selected.protection = raw.protection ∧ selected.layer = raw.layer :=
  exit_restriction_preserves_metadata raw selected row.dp
    (existing_c5_uses_this_exit context row initial raw selected accepted)

/-- An executable restriction witness, obtained by inspecting this same Option. -/
def selectedWitness (context : Context) (row : Row) (initial : Pattern) (raw output : Scalar)
    (accepted : restrictRow context row initial raw = some output) :
    {selected : Scalar // existingC5 context row initial raw = some selected ∧
      output = limit (pairBudget context.global row.dp) selected} := by
  unfold restrictRow at accepted
  cases selected : existingC5 context row initial raw with
  | none => simp only [selected,Option.map_none] at accepted; cases accepted
  | some value =>
    simp only [selected,Option.map_some,Option.some.injEq] at accepted
    exact ⟨value,rfl,accepted.symm⟩

theorem exact_restrict_then_cap (context : Context) (row : Row) (initial : Pattern)
    (raw selected : Scalar) (old : existingC5 context row initial raw = some selected) :
    restrictRow context row initial raw = some (limit (pairBudget context.global row.dp) selected) := by
  simp only [restrictRow,old,Option.map_some]

theorem restriction_output_depth (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output) :
    depth output.path ≤ pairBudget context.global row.dp := by
  let witness := selectedWitness context row initial raw output accepted
  rw [witness.property.2]
  exact limit_depth_bound _ _

theorem restriction_global_depth (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output) :
    depth output.path ≤ context.global :=
  Nat.le_trans (restriction_output_depth context row initial raw output accepted)
    (pair_budget_le_global context.global row.dp)

theorem restriction_exit_depth_step (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output) :
    depth output.path ≤ depth row.dp.path + 1 :=
  Nat.le_trans (restriction_output_depth context row initial raw output accepted)
    (pair_budget_le_exit_step context.global row.dp)

theorem restriction_preserves_metadata (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output) :
    output.base = raw.base ∧ output.mark = raw.mark ∧ output.protection = raw.protection := by
  let witness := selectedWitness context row initial raw output accepted
  have prior := existing_c5_preserves_metadata context row initial raw witness.val witness.property.1
  rw [witness.property.2]
  exact ⟨(limit_base_retained _ _).trans prior.1,
    (limit_mark_retained _ _).trans prior.2.1,
    (limit_protection_retained _ _).trans prior.2.2.1⟩

theorem restriction_never_promotes_demand (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output)
    (demand : raw.layer = .demand) : output.layer = .demand := by
  let witness := selectedWitness context row initial raw output accepted
  have prior := existing_c5_preserves_metadata context row initial raw witness.val witness.property.1
  rw [witness.property.2]
  exact limit_demand_stays_demand _ _ (prior.2.2.2.trans demand)

theorem restriction_normal_is_an_uncut_existing_result (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output)
    (normal : output.layer = .normal) :
    ∃ selected, existingC5 context row initial raw = some selected ∧
      output = selected ∧ raw.layer = .normal := by
  let witness := selectedWitness context row initial raw output accepted
  have normalLimit : (limit (pairBudget context.global row.dp) witness.val).layer = .normal := by
    rw [← witness.property.2]
    exact normal
  have unchanged := limit_normal_is_unchanged _ _ normalLimit
  have same : output = witness.val := witness.property.2.trans unchanged
  have prior := existing_c5_preserves_metadata context row initial raw witness.val witness.property.1
  refine ⟨witness.val,witness.property.1,same,?_⟩
  rw [← prior.2.2.2,← same]
  exact normal

theorem restriction_also_bounds_the_initial (context : Context) (row : Row) (initial : Pattern)
    (raw output : Scalar) (accepted : restrictRow context row initial raw = some output) :
    depth initial.path ≤ depth row.dc.path + 1 := by
  let witness := selectedWitness context row initial raw output accepted
  exact entry_image_depth_step context row.dc initial
    (existing_c5_requires_this_entry context row initial raw witness.val witness.property.1)

theorem restriction_covers_selected_locations (context : Context) (row : Row) (initial : Pattern)
    (raw selected output : Scalar) (old : existingC5 context row initial raw = some selected)
    (accepted : restrictRow context row initial raw = some output)
    (base mark : Nat) (location : Path) (present : possible selected base mark location) :
    possible output base mark location := by
  have unique := exact_restrict_then_cap context row initial raw selected old
  have same : output = limit (pairBudget context.global row.dp) selected :=
    Option.some.inj (accepted.symm.trans unique)
  rw [same]
  exact limit_possible_coverage _ _ _ _ _ present

theorem within_budget_existing_result_is_identical (context : Context) (row : Row) (initial : Pattern)
    (raw selected : Scalar) (old : existingC5 context row initial raw = some selected)
    (within : depth selected.path ≤ pairBudget context.global row.dp) :
    restrictRow context row initial raw = some selected := by
  rw [exact_restrict_then_cap context row initial raw selected old,
    limit_within_identity _ _ within]

theorem admitted_row_provenance (context : Context) (row : Row) (initial : Pattern)
    (raw : Scalar) (output : Admitted) (accepted : admitRow context row initial raw = some output) :
    output.row = row ∧ output.initial = initial ∧
    restrictRow context row initial raw = some output.result := by
  unfold admitRow at accepted
  cases selected : restrictRow context row initial raw with
  | none => simp only [selected,Option.map_none] at accepted; cases accepted
  | some value =>
    simp only [selected,Option.map_some,Option.some.injEq] at accepted
    cases accepted
    exact ⟨rfl,rfl,rfl⟩

theorem every_output_has_one_complete_row (context : Context) (rows : List Row) (initial : Pattern)
    (raw : Scalar) (output : Admitted) (member : output ∈ admitRows context rows initial raw) :
    ∃ row, row ∈ rows ∧ output.row = row ∧ output.initial = initial ∧
      entryImage context row.dc initial = true ∧
      ∃ selected, restrictExit raw row.dp = some selected ∧
        output.result = limit (pairBudget context.global row.dp) selected := by
  obtain ⟨row,inRows,accepted⟩ := List.mem_filterMap.mp member
  have provenance := admitted_row_provenance context row initial raw output accepted
  let witness := selectedWitness context row initial raw output.result provenance.2.2
  exact ⟨row,inRows,provenance.1,provenance.2.1,
    existing_c5_requires_this_entry context row initial raw witness.val witness.property.1,
    witness.val,existing_c5_uses_this_exit context row initial raw witness.val witness.property.1,
    witness.property.2⟩

theorem independent_rows_append_without_cross_products (context : Context) (left right : List Row)
    (initial : Pattern) (raw : Scalar) :
    admitRows context (left ++ right) initial raw =
      admitRows context left initial raw ++ admitRows context right initial raw := by
  exact List.filterMap_append

theorem existing_rejection_stays_rejected (context : Context) (row : Row) (initial : Pattern)
    (raw : Scalar) (rejected : existingC5 context row initial raw = none) :
    restrictRow context row initial raw = none := by simp only [restrictRow,rejected,Option.map_none]

theorem exact_exit_rejects_a_strict_descendant (dp raw : Pattern)
    (exactTail : dp.tail = .exact) (descendant : dp.path.IsPrefix raw.path)
    (different : raw.path ≠ dp.path) : exitGeometry dp raw = none := by
  simp only [exitGeometry]
  split
  · rfl
  · simp only [↓reduceIte,exactTail,tailDescends,Bool.false_eq_true]

namespace Controls

def context : Context := ⟨4,false,false⟩
def dc : Pattern := ⟨1,[],.may,7⟩
def dp : Pattern := ⟨2,[],.may,7⟩
def row : Row := ⟨10,dc,dp⟩
def initial : Pattern := ⟨1,[.field 11],.exact,7⟩
def raw : Scalar := ⟨⟨2,[.field 21,.field 22,.element],.exact,7⟩,.normal,true⟩

theorem current_c5_keeps_three_counted_fields : existingC5 context row initial raw = some raw := by decide

theorem new_result_keeps_one_counted_field_and_protection :
    restrictRow context row initial raw =
      some ⟨⟨2,[.field 21],.may,7⟩,.demand,true⟩ := by decide

def exactRow : Row := {row with dp := {dp with tail := .exact}}

theorem exact_exit_already_rejects_deeper_conclusion : existingC5 context exactRow initial raw = none := by decide

/-- Entry accepts only row 1, exit accepts only row 2. Neither row is complete. -/
def crossedRows : List Row := [
  {row with dp := {dp with base := 9}},
  {row with id := 11,dc := {dc with base := 9}}]

theorem crossed_partial_rows_never_form_a_result : admitRows context crossedRows initial raw = [] := by decide

def preciseRow : Row :=
  {row with id := 12,dp := {dp with path := [.field 21,.field 22,.element]}}

/-- Existing raw-coverage success for the first row cannot justify omitting
    the second capped DEMAND value under literal independent-row union. -/
theorem a_precise_normal_row_does_not_erase_another_rows_demand :
    admitRows context [preciseRow,row] initial raw = [
      ⟨preciseRow,initial,raw⟩,
      ⟨row,initial,⟨⟨2,[.field 21],.may,7⟩,.demand,true⟩⟩] := by decide

theorem same_overflow_rule_also_accepts_a_demand_candidate :
    restrictRow context row initial {raw with layer := .demand} =
      some ⟨⟨2,[.field 21],.may,7⟩,.demand,true⟩ := by decide

end Controls
end RelativeRestriction
