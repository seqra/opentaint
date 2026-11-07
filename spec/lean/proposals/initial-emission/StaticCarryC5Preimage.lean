/-
C5-only shared-static-carry adapter model. A static class+field anchor is an
indivisible Slot; its one counted field is the budget coordinate. This is not
a complete static ownership or packed Facts adapter. Ordinary C2 is unchanged.
The source-projected same-position image keeps old FLOW EXACT normalization.
The helper selects an existing ANY->ANY virtual pair only after canStore permits
it. Actual Facts, their E, layer and literal H are never edited by that choice.
-/
import StarOrAnyDesignProofFixed

namespace StaticCarryC5Preimage
open ApSpec StarOrAnyDesign
abbrev Mark := StarOrAnyDesign.Mark
abbrev Layer := StarOrAnyDesign.Layer
abbrev Head := StarOrAnyDesign.Head
abbrev PlainHead := StarOrAnyDesign.PlainHead

structure Slot where
  owner : Nat
  field : Acc
deriving DecidableEq, Repr
structure Endpoint where
  slot : Slot
  head : Head
  mark : Mark
  exclusion : List Acc := []
deriving DecidableEq, Repr
structure Pair where
  entry : Endpoint
  exit : Endpoint
deriving DecidableEq, Repr

def isSTAR (p : Endpoint) : Bool := decide (p.head = .plain .star)
def isMAY (p : Endpoint) : Bool := decide (p.head = .plain .may)
def isFLOW (p : Endpoint) : Bool := match p.mark with | .flow => true | _ => false
def sameSlotMark (a b : Endpoint) : Bool := decide (a.slot = b.slot ∧ a.mark = b.mark)
def queryMAY (p : Endpoint) : Endpoint := {p with head := .plain .may,exclusion := []}
def samePair (p : Endpoint) : Pair := ⟨p,p⟩

/-- Same-coordinate part of current structural canEmitInitial: only STAR stored
keys are classified below. The static anchor includes a field, so class-only
initial exceptions do not apply. Its counted depth is exactly one. -/
def requestedSTAR (run limit : Nat) (d raw : Endpoint) : Bool :=
  decide (run = 2 ∧ 1 < limit) && isSTAR d && decide (raw.exclusion = d.exclusion)
def rawSameImage (run limit : Nat) (d raw : Endpoint) : Bool :=
  sameSlotMark d raw && decide (1 ≤ limit) &&
  match raw.head with
  | .plain .exact => decide (raw.exclusion = [])
  | .plain .star => requestedSTAR run limit d raw
  | .starOrAny => (isMAY d && decide (raw.exclusion = [])) || requestedSTAR run limit d raw
  | _ => false
/-- At one identical slot: MAY covers the raw STAR-like preimage; STAR demands
must have no more field exclusions than that preimage. EXACT is at the head. -/
def insideSame (raw d : Endpoint) : Bool :=
  if isMAY d then true
  else if isSTAR d then
    match raw.head with
    | .plain .exact => true
    | .plain .star | .starOrAny => d.exclusion.all (fun a => decide (a ∈ raw.exclusion))
    | _ => false
  else false

def canStoreSTAR (run limit : Nat) (d stored : Endpoint) : Bool :=
  if !isSTAR stored then false else
    let fits := fun raw => rawSameImage run limit d raw && insideSame raw d
    fits stored || fits {stored with head := .starOrAny} ||
      (isFLOW stored && decide (stored.exclusion = []) &&
        fits {stored with head := .plain .exact})

/-- Pure query selection. `legacy` is the existing same-slot family row. No row
is inserted, emitted, interned or delivered to C2 by this function. -/
def selectCarry (canStore : Endpoint → Endpoint → Bool) (stored : Endpoint) (legacy : Pair) : Pair :=
  if !canStore legacy.entry stored && isSTAR stored then
    let virtual := queryMAY stored
    if canStore virtual stored then samePair virtual else legacy
  else legacy

def p : Endpoint := ⟨⟨17,7⟩,.plain .star,.full 11,[]⟩
def legacy : Pair := samePair p
def capPolicy : Endpoint → Endpoint → Bool := canStoreSTAR 2 1
/-- Counted projection only: the native STATIC class anchor stays in Slot.
The ordinary scalar lemma supplies this exact one-field image witness. -/
def asPattern (e : Endpoint) : StarOrAnyDesign.Pattern :=
  ⟨e.slot.owner+1,[e.slot.field],e.head,e.mark,e.exclusion⟩

theorem capped_MAY_actual_has_a_concrete_SOA_initial_and_stored_STAR_preimage :
    c2 .starThenMayForAny 2 ⟨.backward,1⟩
      ⟨18,[7],.any,.full 11⟩
      ⟨⟨18,[7],.plain .may,.full 11,[]⟩,.demand,false⟩ =
        [⟨⟨18,[7],.starOrAny,.full 11,[]⟩,.demand⟩] ∧
    eraseSeed ⟨⟨18,[7],.starOrAny,.full 11,[]⟩,.demand⟩ =
      ⟨asPattern p,.demand⟩ := by decide

theorem capped_concrete_STAR_family_rejects_but_existing_MAY_family_accepts :
    capPolicy p p = false ∧ capPolicy (queryMAY p) p = true ∧
    selectCarry capPolicy p legacy = samePair (queryMAY p) := by decide

theorem accepted_legacy_pair_is_kept_without_any_new_query_pair
    (canStore : Endpoint → Endpoint → Bool) (stored : Endpoint) (old : Pair)
    (accepted : canStore old.entry stored = true) :
    selectCarry canStore stored old = old := by simp [selectCarry,accepted]

theorem rejected_MAY_candidate_keeps_the_legacy_row
    (canStore : Endpoint → Endpoint → Bool) (stored : Endpoint) (old : Pair)
    (refused : canStore (queryMAY stored) stored = false) :
    selectCarry canStore stored old = old := by
  unfold selectCarry
  split <;> simp [refused]

theorem nonSTAR_stored_key_keeps_the_existing_legacy_pair
    (canStore : Endpoint → Endpoint → Bool) (stored : Endpoint) (old : Pair)
    (notSTAR : isSTAR stored = false) :
    selectCarry canStore stored old = old := by simp [selectCarry,notSTAR]

theorem any_selected_virtual_pair_requires_the_unchanged_entry_permission
    (canStore : Endpoint → Endpoint → Bool) (stored : Endpoint) (old : Pair)
    (changed : selectCarry canStore stored old ≠ old) :
    isSTAR stored = true ∧ canStore old.entry stored = false ∧
      canStore (queryMAY stored) stored = true ∧
      selectCarry canStore stored old = samePair (queryMAY stored) := by
  unfold selectCarry at changed ⊢
  cases oldGate : canStore old.entry stored <;> cases starGate : isSTAR stored <;>
    cases newGate : canStore (queryMAY stored) stored <;>
    simp_all

theorem virtual_pair_keeps_owner_field_and_mark_on_both_paired_endpoints (stored : Endpoint) :
    (samePair (queryMAY stored)).entry.slot = stored.slot ∧
    (samePair (queryMAY stored)).exit.slot = stored.slot ∧
    (samePair (queryMAY stored)).entry.mark = stored.mark ∧
    (samePair (queryMAY stored)).exit.mark = stored.mark ∧
    (samePair (queryMAY stored)).entry = (samePair (queryMAY stored)).exit := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem nonempty_stored_E_is_not_cleared_and_old_FLOW_preimage_stays_accepted :
    let excluded := {p with exclusion := [9]}
    capPolicy (queryMAY excluded) excluded = false ∧
    selectCarry capPolicy excluded (samePair excluded) = samePair excluded ∧
    excluded.exclusion = [9] ∧
    capPolicy {p with mark := .flow} {p with mark := .flow} = true := by decide

/- Pointwise scalar output restriction, projected from restrictConclusionOnly.
Exit is STAR/EmptyE or ANY at the SAME position. All candidate E stays input;
only the ordinary restricted RESULT may relocate as the source rule specifies. -/
inductive Position where | at | below (first : Acc) (rest : List Acc) | above (first : Acc) (rest : List Acc) | apart
deriving DecidableEq, Repr
inductive ExitKind where | starEmpty | may
deriving DecidableEq, Repr
structure Geometry where
  position : Position
  head : PlainHead
  exclusion : List Acc
deriving DecidableEq, Repr
structure Candidate where
  geometry : Geometry
  layer : Layer
  protection : Bool
  mark : Mark
deriving DecidableEq, Repr

def admits (excluded : List Acc) (first : Acc) : Bool := !decide (first ∈ excluded)
def restrictGeometry (exit : ExitKind) (g : Geometry) : Option Geometry :=
  match g.position with
  | .at =>
    match g.head,exit with
    | .must,.starEmpty => some {g with exclusion := g.exclusion ++ []}
    | _,_ => some g
  | .below _ _ => some g
  | .above first _ =>
    match g.head with
    | .may | .must => if admits g.exclusion first then some {g with position := .at,exclusion := []} else none
    | .star => if admits g.exclusion first then some g else none
    | .exact => none
  | .apart => none

def restrictCandidate (exit : ExitKind) (c : Candidate) : Option Candidate :=
  (restrictGeometry exit c.geometry).map (fun g => {c with geometry := g})
def gatedRestriction (sameField markMatches : Bool) (exit : ExitKind) (c : Candidate) : Option Candidate :=
  if sameField && markMatches then restrictCandidate exit c else none

theorem STAR_EmptyE_and_MAY_same_position_have_equal_scalar_output_restriction (g : Geometry) :
    restrictGeometry .starEmpty g = restrictGeometry .may g := by
  cases g with
  | mk position head excluded =>
    cases position <;> cases head <;> simp [restrictGeometry]

theorem identical_field_and_mark_gates_preserve_the_restriction_equality
    (sameField markMatches : Bool) (c : Candidate) :
    gatedRestriction sameField markMatches .starEmpty c =
      gatedRestriction sameField markMatches .may c := by
  simp [gatedRestriction,restrictCandidate,
    STAR_EmptyE_and_MAY_same_position_have_equal_scalar_output_restriction]

theorem output_restriction_preserves_every_supplied_layer_mark_and_literal_H
    (exit : ExitKind) (c result : Candidate)
    (selected : restrictCandidate exit c = some result) :
    result.layer = c.layer ∧ result.mark = c.mark ∧ result.protection = c.protection := by
  cases observed : restrictGeometry exit c.geometry with
  | none => simp only [restrictCandidate,observed,Option.map_none] at selected; cases selected
  | some geometry =>
    have same : {c with geometry := geometry} = result := by
      simpa only [restrictCandidate,observed,Option.map_some,Option.some.injEq] using selected
    rw [← same]
    exact ⟨rfl,rfl,rfl⟩

def restrictCarry (pair : Pair) (stored : Endpoint) (c : Candidate) : Option Candidate :=
  if capPolicy pair.entry stored && sameSlotMark pair.entry pair.exit && sameSlotMark pair.entry stored then
    match pair.exit.head with
    | .plain .star => if pair.exit.exclusion = [] then restrictCandidate .starEmpty c else none
    | .plain .may => restrictCandidate .may c
    | _ => none
  else none

def candidate : Candidate := ⟨⟨.at,.star,[]⟩,.demand,true,.full 11⟩

theorem capped_C5_recovery_keeps_the_candidate_and_does_not_cross_a_different_field :
    restrictCarry legacy p candidate = none ∧
    restrictCarry (selectCarry capPolicy p legacy) p candidate = some candidate ∧
    restrictCarry (selectCarry capPolicy p legacy)
      {p with slot := ⟨17,8⟩} candidate = none := by decide

def check : Bool :=
  !capPolicy p p && capPolicy (queryMAY p) p &&
  decide (selectCarry capPolicy p legacy = samePair (queryMAY p)) &&
  decide (restrictCarry (selectCarry capPolicy p legacy) p candidate = some candidate) &&
  decide (p.exclusion = [])

theorem executable_C5_only_adapter_cells : check = true := by decide
#eval (if check then "STATIC_CARRY_C5_PREIMAGE=true" else "STATIC_CARRY_C5_PREIMAGE=false")

#print axioms capped_MAY_actual_has_a_concrete_SOA_initial_and_stored_STAR_preimage
#print axioms capped_concrete_STAR_family_rejects_but_existing_MAY_family_accepts
#print axioms accepted_legacy_pair_is_kept_without_any_new_query_pair
#print axioms rejected_MAY_candidate_keeps_the_legacy_row
#print axioms nonSTAR_stored_key_keeps_the_existing_legacy_pair
#print axioms any_selected_virtual_pair_requires_the_unchanged_entry_permission
#print axioms virtual_pair_keeps_owner_field_and_mark_on_both_paired_endpoints
#print axioms nonempty_stored_E_is_not_cleared_and_old_FLOW_preimage_stays_accepted
#print axioms STAR_EmptyE_and_MAY_same_position_have_equal_scalar_output_restriction
#print axioms identical_field_and_mark_gates_preserve_the_restriction_equality
#print axioms output_restriction_preserves_every_supplied_layer_mark_and_literal_H
#print axioms capped_C5_recovery_keeps_the_candidate_and_does_not_cross_a_different_field
#print axioms executable_C5_only_adapter_cells

end StaticCarryC5Preimage
