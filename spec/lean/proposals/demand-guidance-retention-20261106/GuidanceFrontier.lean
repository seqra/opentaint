/-
Selected design: keep STAR; retain operational guidance separately from data
coverage. C2 below is the existing imported scalar policy, without overrides.

Scope: finite FULL scalar lists, ordinary nonstatic bases, counted fields,
Empty E, no ZERO data transfer, GROUP/mx, aliases, ND transfer or field budget.
ZERO/ND appear only in the existing source-handoff selector truth table.
Exit labels are opaque complete coordinates: no exit component is recomputed.

This proves local union and image facts once exact paired rows are available.
It does NOT prove rows arrive from point/summary producers or survive their
normalization. Producer-transition, ownership, 39-adapter and global effect
obligations remain OPEN. No assumed arrival invariant closes those gaps.
-/
import RestrictedInitialPolicy

namespace GuidanceFrontier
open ApSpec

abbrev Demand := RestrictedInitialPolicy.Demand
abbrev Input := RestrictedInitialPolicy.Input
abbrev Mark := RestrictedInitialPolicy.Mark

structure Row where
  query : Demand
  exitLabel : Nat
deriving DecidableEq, Repr

/-- Exact paired-row union. Lists implement finite set membership; duplicates
and order have no meaning in the image predicates below. This is the guide
algebra, not a data-coverage antichain and not a callback-count theorem. -/
def guideUnion (left right : List Row) : List Row := left ++ right

def containsBy (accept : Row → Bool) : List Row → Bool
  | [] => false
  | row :: rest => accept row || containsBy accept rest

/-- Apply unchanged C2 to each retained query coordinate. -/
def c2Image (rows : List Row) (actual initial : Input) : Bool :=
  containsBy (fun row => decide (RestrictedInitialPolicy.emit row.query actual = some initial)) rows

/-- Paired admission image: C2 emits an initial and keeps that same row's
complete opaque exit label. Production C5 restriction, canStoreInitial and
budget are not modeled. containsBy can later accept an actual C5-row predicate. -/
def pairedAdmissionImage (rows : List Row) (actual initial : Input) (exitLabel : Nat) : Bool :=
  containsBy (fun row =>
    decide (RestrictedInitialPolicy.emit row.query actual = some initial) &&
      Nat.beq row.exitLabel exitLabel) rows

theorem contains_guide_union (accept : Row → Bool) (left right : List Row) :
    containsBy accept (guideUnion left right) =
      (containsBy accept left || containsBy accept right) := by
  induction left with
  | nil => rfl
  | cons row rest ih =>
    simpa only [guideUnion, List.cons_append, containsBy, Bool.or_assoc] using
      congrArg (fun value => accept row || value) ih

theorem guide_union_both_orders (accept : Row → Bool) (left right : List Row) :
    containsBy accept (guideUnion left right) =
      containsBy accept (guideUnion right left) := by
  rw [contains_guide_union, contains_guide_union]
  exact Bool.or_comm _ _

theorem c2_image_union (left right : List Row) (actual initial : Input) :
    c2Image (guideUnion left right) actual initial =
      (c2Image left actual initial || c2Image right actual initial) :=
  contains_guide_union _ left right

theorem paired_admission_image_union (left right : List Row) (actual initial : Input)
    (label : Nat) :
    pairedAdmissionImage (guideUnion left right) actual initial label =
      (pairedAdmissionImage left actual initial label || pairedAdmissionImage right actual initial label) :=
  contains_guide_union _ left right

theorem paired_admission_image_both_orders (left right : List Row) (actual initial : Input)
    (label : Nat) :
    pairedAdmissionImage (guideUnion left right) actual initial label =
      pairedAdmissionImage (guideUnion right left) actual initial label :=
  guide_union_both_orders _ left right

/-- Separate DATA algebra. This local ANY-prefix coverage recognizer is used
only to exhibit loss; it does not claim to model all native canonicalization. -/
def queryCovers (broad narrow : Demand) : Bool :=
  decide (broad.base = narrow.base) && decide (broad.mark = narrow.mark) &&
    RestrictedInitialPolicy.shapeEq broad.shape .any &&
    (dropPrefix broad.path narrow.path).isSome

def dataCovers (broad narrow : Row) : Bool :=
  Nat.beq broad.exitLabel narrow.exitLabel && queryCovers broad.query narrow.query

def dataInsert (row : Row) (rows : List Row) : List Row :=
  if rows.any (fun old => dataCovers old row) then rows
  else row :: rows.filter (fun old => !(dataCovers row old))

def p : Nat := 1
def f : Acc := 7
def T : Mark := .full 11
def d0 : Demand := ⟨p, [], .any, .flow⟩
def d1 : Demand := ⟨p, [f], .any, .flow⟩
def rootRow : Row := ⟨d0, 17⟩
def childRow : Row := ⟨d1, 17⟩
def actualChildMust : Input := ⟨p, [f], .any, T, true⟩
def childStarFlow : Input := ⟨p, [f], .star, .flow, false⟩
def childMustFlow : Input := ⟨p, [f], .any, .flow, true⟩

def anyQuerySupports (query : Demand) (location : List Acc) : Bool :=
  RestrictedInitialPolicy.shapeEq query.shape .any &&
    (dropPrefix query.path location).isSome

theorem denotational_root_ANY_covers_child_ANY (location : List Acc) :
    anyQuerySupports d1 location = true → anyQuerySupports d0 location = true := by
  intro _
  rfl

theorem unchanged_C2_has_distinct_root_child_images :
    RestrictedInitialPolicy.emit d0 actualChildMust = some childStarFlow ∧
    RestrictedInitialPolicy.emit d1 actualChildMust = some childMustFlow ∧
    childStarFlow ≠ childMustFlow := by decide

theorem guide_pair_keeps_both_images_in_both_orders :
    pairedAdmissionImage (guideUnion [rootRow] [childRow]) actualChildMust childStarFlow 17 = true ∧
    pairedAdmissionImage (guideUnion [rootRow] [childRow]) actualChildMust childMustFlow 17 = true ∧
    pairedAdmissionImage (guideUnion [childRow] [rootRow]) actualChildMust childStarFlow 17 = true ∧
    pairedAdmissionImage (guideUnion [childRow] [rootRow]) actualChildMust childMustFlow 17 = true := by decide

theorem DATA_prefix_removal_discards_child_in_both_orders :
    dataInsert childRow (dataInsert rootRow []) = [rootRow] ∧
    dataInsert rootRow (dataInsert childRow []) = [rootRow] := by decide

theorem DATA_coverage_is_not_C2_image_equivalence :
    queryCovers d0 d1 = true ∧
    c2Image [rootRow] actualChildMust childMustFlow = false ∧
    c2Image (guideUnion [rootRow] [childRow]) actualChildMust childMustFlow = true := by decide

/-- A later exact-union store can retain what it receives, but cannot recover
this missing coordinate from a producer that already emitted only rootRow.
This is a countermodel, not a claim about which native producer owns the loss. -/
theorem late_store_retention_cannot_recover_discarded_child :
    guideUnion (dataInsert childRow (dataInsert rootRow [])) [] = [rootRow] ∧
    pairedAdmissionImage (guideUnion (dataInsert childRow (dataInsert rootRow [])) [])
      actualChildMust childMustFlow 17 = false := by decide

theorem exact_pairing_does_not_cross_exit_labels :
    pairedAdmissionImage [⟨d0, 41⟩, ⟨d1, 42⟩] actualChildMust childStarFlow 41 = true ∧
    pairedAdmissionImage [⟨d0, 41⟩, ⟨d1, 42⟩] actualChildMust childMustFlow 42 = true ∧
    pairedAdmissionImage [⟨d0, 41⟩, ⟨d1, 42⟩] actualChildMust childStarFlow 42 = false ∧
    pairedAdmissionImage [⟨d0, 41⟩, ⟨d1, 42⟩] actualChildMust childMustFlow 41 = false := by decide

inductive Layer where | normal | demand
deriving DecidableEq, Repr
inductive Direction where | forward | backward
deriving DecidableEq, Repr
inductive Origin where | initial (isZero : Bool) | nd
deriving DecidableEq, Repr

/-- Existing source-handoff selection, not a new all-NORMAL export rule. -/
def selectedForHandoff : Layer → Direction → Origin → Bool
  | .demand, _, _ => true
  | .normal, _, .nd => true
  | .normal, .backward, .initial true => true
  | _, _, _ => false

theorem source_handoff_selector_table :
    selectedForHandoff .demand .forward (.initial false) = true ∧
    selectedForHandoff .demand .backward (.initial false) = true ∧
    selectedForHandoff .normal .forward .nd = true ∧
    selectedForHandoff .normal .backward .nd = true ∧
    selectedForHandoff .normal .backward (.initial true) = true ∧
    selectedForHandoff .normal .forward (.initial true) = false ∧
    selectedForHandoff .normal .forward (.initial false) = false ∧
    selectedForHandoff .normal .backward (.initial false) = false := by decide

/-- Empty-E scalar part of guidancePattern: MUST loses its must flag, keeps
its ANY geometry, and other heads stay themselves. No emitter is changed. -/
def guidanceHead (actual : Input) : Demand :=
  ⟨actual.base, actual.path, actual.shape, actual.mark⟩

theorem guidance_MUST_ANY_and_other_heads :
    guidanceHead actualChildMust = ⟨p, [f], .any, T⟩ ∧
    guidanceHead ⟨p, [f], .star, T, false⟩ = ⟨p, [f], .star, T⟩ ∧
    guidanceHead ⟨p, [f], .exact, T, false⟩ = ⟨p, [f], .exact, T⟩ := by decide

/-- Same point, concrete MAY versus EXACT guidance. ANY geometry may cover
EXACT geometry while selecting a different current C2 initial. This shows why
guide retention must inspect all heads, not just proper-prefix ANY pairs. -/
def mayQuery : Demand := ⟨p, [], .any, T⟩
def exactQuery : Demand := ⟨p, [], .exact, T⟩
def actualRootMay : Input := ⟨p, [], .any, T, false⟩
def rootExact : Input := ⟨p, [], .exact, T, false⟩

theorem same_point_MAY_EXACT_guide_countercell :
    queryCovers mayQuery exactQuery = true ∧
    RestrictedInitialPolicy.emit mayQuery actualRootMay = some actualRootMay ∧
    RestrictedInitialPolicy.emit exactQuery actualRootMay = some rootExact ∧
    pairedAdmissionImage [⟨mayQuery, 17⟩] actualRootMay rootExact 17 = false ∧
    pairedAdmissionImage [⟨mayQuery, 17⟩, ⟨exactQuery, 17⟩] actualRootMay rootExact 17 = true := by decide

/-- A concrete row-union witness that root can evaluate without choice. -/
def retainedRows : List Row := guideUnion [rootRow] [childRow]

theorem retained_rows_are_an_executable_witness :
    retainedRows = [rootRow, childRow] ∧
    pairedAdmissionImage retainedRows actualChildMust childMustFlow 17 = true := by decide

#eval retainedRows
#eval (pairedAdmissionImage retainedRows actualChildMust childMustFlow 17)
#print axioms contains_guide_union
#print axioms guide_union_both_orders
#print axioms c2_image_union
#print axioms paired_admission_image_union
#print axioms paired_admission_image_both_orders
#print axioms denotational_root_ANY_covers_child_ANY
#print axioms unchanged_C2_has_distinct_root_child_images
#print axioms guide_pair_keeps_both_images_in_both_orders
#print axioms DATA_prefix_removal_discards_child_in_both_orders
#print axioms DATA_coverage_is_not_C2_image_equivalence
#print axioms late_store_retention_cannot_recover_discarded_child
#print axioms exact_pairing_does_not_cross_exit_labels
#print axioms source_handoff_selector_table
#print axioms guidance_MUST_ANY_and_other_heads
#print axioms same_point_MAY_EXACT_guide_countercell
#print axioms retained_rows_are_an_executable_witness

end GuidanceFrontier
