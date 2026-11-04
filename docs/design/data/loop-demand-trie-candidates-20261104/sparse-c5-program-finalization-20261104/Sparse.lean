import Std

namespace SparseC5Finalization

-- Each scalar/header/mark/exclusion identity is opaque and exact, never geometry-only.
structure Bucket where
  protectedSelections : List Nat
  ordinarySelections : List Nat
  deriving DecidableEq, Repr

structure Output where
  payload : Nat
  annotation : Nat
  deriving DecidableEq, Repr

abbrev Rows := Nat → Option Bucket
abbrev Emit := Nat → Bucket → List Output

def emitAt (rows : Rows) (emit : Emit) (ordinal : Nat) : List Output :=
  match rows ordinal with
  | none => []
  | some bucket => emit ordinal bucket

def activeKeys (programs : List Nat) (rows : Rows) : List Nat :=
  programs.filter fun ordinal => (rows ordinal).isSome

def dense (programs : List Nat) (rows : Rows) (emit : Emit) : List Output :=
  programs.flatMap (emitAt rows emit)

def ascending (a b : Nat) : Bool := decide (a ≤ b)

def sparse (encountered : List Nat) (rows : Rows) (emit : Emit) : List Output :=
  (encountered.mergeSort ascending).flatMap (emitAt rows emit)

theorem empty_cell_is_silent (rows : Rows) (emit : Emit) (ordinal : Nat)
    (empty : rows ordinal = none) : emitAt rows emit ordinal = [] := by
  simp [emitAt, empty]

theorem discard_empty_cells (programs : List Nat) (rows : Rows) (emit : Emit) :
    dense programs rows emit = dense (activeKeys programs rows) rows emit := by
  induction programs with
  | nil => rfl
  | cons ordinal rest ih =>
    cases found : rows ordinal with
    | none => simpa [dense, activeKeys, emitAt, found] using ih
    | some bucket => simpa [dense, activeKeys, emitAt, found] using congrArg (List.append (emit ordinal bucket)) ih

theorem ascending_transitive (a b c : Nat) (ab : ascending a b) (bc : ascending b c) : ascending a c := by
  simp only [ascending, decide_eq_true_eq] at *
  exact Nat.le_trans ab bc

theorem ascending_total (a b : Nat) : ascending a b || ascending b a := by
  simp only [ascending, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total a b

theorem sorted_encountered (keys : List Nat) :
    (keys.mergeSort ascending).Pairwise (fun a b => a ≤ b) := by
  have sorted := List.pairwise_mergeSort ascending_transitive ascending_total keys
  simpa [ascending] using sorted

theorem native_ordinals_sorted (count : Nat) : (List.range count).Pairwise (fun a b => a ≤ b) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ]
    apply List.pairwise_append.mpr
    refine ⟨ih, ?_, ?_⟩
    · simp
    · intro a member b last
      have equal : b = count := List.mem_singleton.mp last
      subst b
      exact Nat.le_of_lt (List.mem_range.mp member)

theorem active_keys_sorted (count : Nat) (rows : Rows) :
    (activeKeys (List.range count) rows).Pairwise (fun a b => a ≤ b) := by
  exact (native_ordinals_sorted count).filter _

theorem sort_restores_native_ordinals (count : Nat) (rows : Rows) (keys : List Nat)
    (complete : keys.Perm (activeKeys (List.range count) rows)) :
    keys.mergeSort ascending = activeKeys (List.range count) rows := by
  apply List.Perm.eq_of_pairwise
    (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
    (sorted_encountered keys) (active_keys_sorted count rows)
  exact (List.mergeSort_perm keys ascending).trans complete

theorem exact_ordered_output_stream (count : Nat) (rows : Rows) (emit : Emit) (keys : List Nat)
    (complete : keys.Perm (activeKeys (List.range count) rows)) :
    sparse keys rows emit = dense (List.range count) rows emit := by
  unfold sparse
  rw [sort_restores_native_ordinals count rows keys complete]
  exact (discard_empty_cells (List.range count) rows emit).symm

-- Equality is of the full ordered annotated stream, so any unchanged exact native union sees identical input.
theorem exact_final_annotation_union {Result : Type} (finish : List Output → Result)
    (count : Nat) (rows : Rows) (emit : Emit) (keys : List Nat)
    (complete : keys.Perm (activeKeys (List.range count) rows)) :
    finish (sparse keys rows emit) = finish (dense (List.range count) rows emit) := by
  rw [exact_ordered_output_stream count rows emit keys complete]

-- Executable reference certificate for native tests; it is not proposed for the hot path.
def certify (count : Nat) (rows : Rows) (keys : List Nat) : Bool :=
  decide (keys.mergeSort ascending = activeKeys (List.range count) rows)

theorem certificate_ordered_output (count : Nat) (rows : Rows) (emit : Emit) (keys : List Nat)
    (accepted : certify count rows keys = true) :
    sparse keys rows emit = dense (List.range count) rows emit := by
  have ordered : keys.mergeSort ascending = activeKeys (List.range count) rows := of_decide_eq_true accepted
  unfold sparse
  rw [ordered]
  exact (discard_empty_cells (List.range count) rows emit).symm

theorem sparse_sort_preserves_work_size (keys : List Nat) : (keys.mergeSort ascending).length = keys.length := by
  exact List.length_mergeSort keys

theorem selected_finalizers_at_most_plan (count : Nat) (rows : Rows) (keys : List Nat)
    (complete : keys.Perm (activeKeys (List.range count) rows)) : keys.length ≤ count := by
  rw [complete.length_eq]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem selected_finalizers_at_most_reference_cap (keys : List Nat) (references : Nat)
    (each_key_has_reference : keys.length ≤ references) (within_cap : references ≤ 2048) : keys.length ≤ 2048 :=
  Nat.le_trans each_key_has_reference within_cap

inductive QueryResult where
  | fallback
  | admitted (outputs : List Output)
  deriving DecidableEq, Repr

def finishQuery (references : Nat) (outputs : List Output) : QueryResult :=
  if references ≤ 2048 then .admitted outputs else .fallback

theorem exact_bounded_query_result (count : Nat) (rows : Rows) (emit : Emit) (keys : List Nat) (references : Nat)
    (complete : keys.Perm (activeKeys (List.range count) rows)) :
    finishQuery references (sparse keys rows emit) = finishQuery references (dense (List.range count) rows emit) := by
  rw [exact_ordered_output_stream count rows emit keys complete]

theorem overflow_returns_no_partial_outputs (references : Nat) (outputs : List Output) (overflow : 2048 < references) :
    finishQuery references outputs = .fallback := by
  simp [finishQuery, Nat.not_le_of_lt overflow]

-- Input scalar order can discover a later output program before an earlier one.
def exampleBucket : Bucket := ⟨[11], [11, 13]⟩
def exampleRows (ordinal : Nat) : Option Bucket := if ordinal = 0 ∨ ordinal = 2 then some exampleBucket else none
def exampleEmit (ordinal : Nat) (_ : Bucket) : List Output := [⟨ordinal + 10, ordinal + 100⟩]

theorem unsorted_encounter_is_not_native_order :
    ([2, 0].flatMap (emitAt exampleRows exampleEmit)) ≠ dense (List.range 3) exampleRows exampleEmit := by decide

theorem sorted_sparse_example :
    sparse [2, 0] exampleRows exampleEmit = dense (List.range 3) exampleRows exampleEmit := by
  apply exact_ordered_output_stream
  change [2, 0].Perm [0, 2]
  exact .swap ..

theorem example_active_keys : activeKeys (List.range 3) exampleRows = [0, 2] := by decide

theorem duplicate_ordinal_certificate_is_rejected : certify 3 exampleRows [2, 0, 2] = false := by
  unfold certify
  apply decide_eq_false_iff_not.mpr
  intro equal
  have sizes := congrArg List.length equal
  have impossible : (3 : Nat) = 2 := by simpa [example_active_keys] using sizes
  exact (by decide : (3 : Nat) ≠ 2) impossible

theorem missing_ordinal_certificate_is_rejected : certify 3 exampleRows [2] = false := by
  unfold certify
  apply decide_eq_false_iff_not.mpr
  intro equal
  have sizes := congrArg List.length equal
  have impossible : (1 : Nat) = 2 := by simpa [example_active_keys] using sizes
  exact (by decide : (1 : Nat) ≠ 2) impossible

theorem empty_query_allocates_no_selected_cells : activeKeys (List.range 100) (fun _ => none) = [] := by decide

theorem selected_bucket_can_emit_nothing : sparse [2, 0] exampleRows (fun _ _ => []) = [] := by
  have complete : [2, 0].Perm (activeKeys (List.range 3) exampleRows) := by
    change [2, 0].Perm [0, 2]
    exact .swap ..
  rw [exact_ordered_output_stream 3 exampleRows (fun _ _ => []) [2, 0] complete]
  decide

end SparseC5Finalization
