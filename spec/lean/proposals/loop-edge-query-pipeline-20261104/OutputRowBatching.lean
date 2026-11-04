import Std

namespace OutputRowBatching

/-- The payload is the WHOLE paired row; its raw ordinal is never quotiented. -/
structure PairedRow (Payload : Type) where
  ordinal : Nat
  payload : Payload
deriving DecidableEq, Repr

variable {Row Scalar Part Result : Type}

/-- Native selection is opaque. A part can retain all geometry and annotations. -/
def selectedParts (select : Row → Scalar → Option Part) (row : Row)
    (scalars : List Scalar) : List Part := scalars.filterMap (select row)

/-- Candidate lookup is permitted to omit only a native None cell. -/
def CandidateComplete (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) : Prop :=
  ∀ row scalar, candidate row scalar = false → select row scalar = none

def maskedSelect (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (row : Row) (scalar : Scalar) : Option Part :=
  if candidate row scalar then select row scalar else none

theorem conservative_candidate_cell (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (complete : CandidateComplete select candidate)
    (row : Row) (scalar : Scalar) : maskedSelect select candidate row scalar = select row scalar := by
  cases h : candidate row scalar with
  | false => simp [maskedSelect, h, complete row scalar h]
  | true => simp [maskedSelect, h]

theorem conservative_candidate_parts (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (complete : CandidateComplete select candidate)
    (row : Row) (scalars : List Scalar) :
    selectedParts (maskedSelect select candidate) row scalars = selectedParts select row scalars := by
  have same : maskedSelect select candidate row = select row := by
    funext scalar
    exact conservative_candidate_cell select candidate complete row scalar
  simp only [selectedParts, same]

/-- Append one scalar column to positionally distinct row buckets. -/
def prependColumn (select : Row → Scalar → Option Part) (scalar : Scalar)
    (rows : List Row) (buckets : List (List Part)) : List (List Part) :=
  List.zipWith (fun row parts => match select row scalar with
    | none => parts
    | some part => part :: parts) rows buckets

/-- Leaf-major reference assembly. Each column visits scalar postings; buckets are
    positional row slots. Input scalar order is restored by the right fold. -/
def leafMajor (select : Row → Scalar → Option Part) (rows : List Row) :
    List Scalar → List (List Part)
  | [] => rows.map (fun _ => [])
  | scalar :: tail => prependColumn select scalar rows (leafMajor select rows tail)

theorem zipWith_map_same (f : Row → Part → Result) (g : Row → Part) (rows : List Row) :
    List.zipWith f rows (rows.map g) = rows.map (fun row => f row (g row)) := by
  induction rows with
  | nil => rfl
  | cons row tail ih => simp [ih]

theorem leaf_major_buckets_equal_native (select : Row → Scalar → Option Part)
    (rows : List Row) (scalars : List Scalar) :
    leafMajor select rows scalars = rows.map (fun row => selectedParts select row scalars) := by
  induction scalars with
  | nil => rfl
  | cons scalar tail ih =>
    simp only [leafMajor, prependColumn, ih, zipWith_map_same]
    apply List.map_congr_left
    intro row _
    cases h : select row scalar <;> simp [selectedParts, h]

theorem conservative_leaf_major_buckets (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (complete : CandidateComplete select candidate)
    (rows : List Row) (scalars : List Scalar) :
    leafMajor (maskedSelect select candidate) rows scalars =
      rows.map (fun row => selectedParts select row scalars) := by
  rw [leaf_major_buckets_equal_native]
  apply List.map_congr_left
  intro row _
  exact conservative_candidate_parts select candidate complete row scalars

/-- Entry checks use the exact paired row. Rejected rows do not call pack/cut. -/
def nativeRows (accepted : Row → Bool) (select : Row → Scalar → Option Part)
    (packCut : Row → List Part → List Result) (rows : List Row) (scalars : List Scalar) : List Result :=
  rows.flatMap (fun row => if accepted row then packCut row (selectedParts select row scalars) else [])

/-- Packing/cutting stays opaque and is performed once on the complete row bucket. -/
def emitBuckets (packCut : Row → List Part → List Result) (rows : List Row)
    (buckets : List (List Part)) : List Result := (List.zipWith packCut rows buckets).flatten

def preparedRows (accepted : Row → Bool) (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (packCut : Row → List Part → List Result)
    (rows : List Row) (scalars : List Scalar) : List Result :=
  let plan := rows.filter accepted
  emitBuckets packCut plan (leafMajor (maskedSelect select candidate) plan scalars)

theorem entry_mask_elimination (accepted : Row → Bool) (f : Row → List Result) (rows : List Row) :
    rows.flatMap (fun row => if accepted row then f row else []) = (rows.filter accepted).flatMap f := by
  induction rows with
  | nil => rfl
  | cons row tail ih => cases h : accepted row <;> simp [h, ih]

theorem emit_complete_buckets (packCut : Row → List Part → List Result)
    (parts : Row → List Part) (rows : List Row) :
    emitBuckets packCut rows (rows.map parts) = rows.flatMap (fun row => packCut row (parts row)) := by
  simp [emitBuckets, zipWith_map_same, List.flatMap]

theorem full_ordered_factorization (accepted : Row → Bool) (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (complete : CandidateComplete select candidate)
    (packCut : Row → List Part → List Result) (rows : List Row) (scalars : List Scalar) :
    preparedRows accepted select candidate packCut rows scalars =
      nativeRows accepted select packCut rows scalars := by
  change emitBuckets packCut (rows.filter accepted)
    (leafMajor (maskedSelect select candidate) (rows.filter accepted) scalars) = _
  rw [conservative_leaf_major_buckets select candidate complete]
  rw [emit_complete_buckets]
  exact (entry_mask_elimination accepted
    (fun row => packCut row (selectedParts select row scalars)) rows).symm

/-- Any identical downstream ordered union sees identical inputs. No distributivity assumed. -/
theorem same_ordered_union (accepted : Row → Bool) (select : Row → Scalar → Option Part)
    (candidate : Row → Scalar → Bool) (complete : CandidateComplete select candidate)
    (packCut : Row → List Part → List Result) (rows : List Row) (scalars : List Scalar)
    (orderedUnion : List Result → Part) :
    orderedUnion (preparedRows accepted select candidate packCut rows scalars) =
      orderedUnion (nativeRows accepted select packCut rows scalars) := by
  rw [full_ordered_factorization accepted select candidate complete]

/-- A plan output posting is an eligible owner output posting, in the same order. -/
def planPostings (accepted : Row → Bool) (ownerPostings : List Row) : List Row :=
  ownerPostings.filter accepted

theorem plan_postings_sublist (accepted : Row → Bool) (postings : List Row) :
    (planPostings accepted postings).Sublist postings := List.filter_sublist

theorem output_posting_work_bound (accepted : Row → Bool) (postings : List Row) :
    (planPostings accepted postings).length ≤ postings.length :=
  (plan_postings_sublist accepted postings).length_le

def currentPostingWork (lookup : Scalar → List Row) : List Scalar → Nat
  | [] => 0
  | scalar :: tail => (lookup scalar).length + currentPostingWork lookup tail

def planPostingWork (accepted : Row → Bool) (lookup : Scalar → List Row) : List Scalar → Nat
  | [] => 0
  | scalar :: tail => (planPostings accepted (lookup scalar)).length + planPostingWork accepted lookup tail

theorem batched_posting_work_bound (accepted : Row → Bool) (lookup : Scalar → List Row)
    (scalars : List Scalar) : planPostingWork accepted lookup scalars ≤ currentPostingWork lookup scalars := by
  induction scalars with
  | nil => exact Nat.le_refl 0
  | cons scalar tail ih =>
    exact Nat.add_le_add (output_posting_work_bound accepted (lookup scalar)) ih

theorem no_saving_when_all_eligible (postings : List Row) :
    planPostings (fun _ => true) postings = postings := by simp [planPostings]

theorem all_unrelated_postings_removed (postings : List Row) :
    (planPostings (fun _ => false) postings).length = 0 := by
  induction postings with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Finite counterexample controls: ordinal-distinct rows must not be merged. -/
def exampleRows : List (PairedRow Nat) := [⟨7, 4⟩, ⟨8, 4⟩]

theorem distinct_nd_ordinals_retained :
    nativeRows (fun _ => true) (fun (_ : PairedRow Nat) (s : Nat) => some s)
      (fun row parts => [(row.ordinal, parts)]) exampleRows [3, 5] =
      [(7, [3, 5]), (8, [3, 5])] := rfl

theorem scalar_input_order_retained :
    leafMajor (fun (_ : Nat) (s : Nat) => if s = 4 then none else some s) [9] [3, 4, 5] =
      [[3, 5]] := rfl

theorem pack_cut_need_not_distribute :
    ([([3, 5] : List Nat).length] : List Nat) ≠ [([3] : List Nat).length] ++ [([5] : List Nat).length] := by
  decide

theorem rejected_row_does_not_pack_empty :
    nativeRows (fun (_ : Nat) => false) (fun (_ : Nat) (_ : Nat) => (none : Option Nat))
      (fun _ _ => [99]) [1] [3] = [] := rfl

theorem dropping_live_candidate_changes_answer :
    selectedParts (fun (_ : Nat) (s : Nat) => some s) 0 [3] ≠
      selectedParts (maskedSelect (fun (_ : Nat) (s : Nat) => some s) (fun _ _ => false)) 0 [3] := by
  decide

theorem strict_work_improvement_witness :
    (planPostings (fun (row : Nat) => row == 1) [0, 1, 2, 3]).length < ([0, 1, 2, 3] : List Nat).length := by
  decide

end OutputRowBatching
