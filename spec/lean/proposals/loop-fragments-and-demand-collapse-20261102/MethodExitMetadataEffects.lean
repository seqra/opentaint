import Std

/-!
FULL/valid-TAINT projection model for the existing method-exit DATA adjustment.

Both selectors use the same immutable input and ordered positive literal index.
The old selector also updates an arbitrary join/report state. A Holds part is
appended independently of whether that state can complete an ND rule. Equality
of the complete ordered part list gives equality of the existing without fold.

The concrete finite records below model one mark at one node, including mixed
EXACT/ANY membership, layer, exclusions, ANY header and protection. They are
not a proof of full AP checkMark, aliases, Kotlin callback order or all trees.
-/
namespace MethodExitMetadataEffects
set_option autoImplicit false

inductive Base where
  | static | argument | zero
  deriving DecidableEq, Repr
inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr
inductive AnyTail where
  | may | must
  deriving DecidableEq, Repr
inductive Original where
  | zero | local | argument
  deriving DecidableEq, Repr

structure Tree where
  base : Base
  exact : Bool
  any : Bool
  layer : Layer
  exclusion : List Nat
  anyTail : AnyTail
  protectedExact : Bool
  protectedAny : Bool
  deriving DecidableEq, Repr
structure Literal where
  occurrence : Nat
  ordinal : Nat
  base : Base
  mark : Nat
  projected : Option Tree
  deriving DecidableEq, Repr
structure Predicate where
  isTrue : Bool
  indexedLeaves : List Literal
  deriving DecidableEq, Repr
structure Sink where
  predicate : Option Predicate
  patterns : List Literal
  deriving DecidableEq, Repr
structure Input where
  value : Tree
  markOrder : List Nat
  deriving DecidableEq, Repr

/-- This is the existing exact base/mark index in its existing leaf order.
No complete NNF truth or unary/multi classification is evaluated here. -/
def matchingLeaves (input : Input) (predicate : Predicate) (mark : Nat) : List Literal :=
  predicate.indexedLeaves.filter (fun literal =>
    decide (literal.base = input.value.base ∧ literal.mark = mark))

def selectedLiterals (input : Input) (sink : Sink) : List Literal :=
  match sink.predicate with
  | some predicate => if predicate.isTrue then sink.patterns
      else input.markOrder.flatMap (matchingLeaves input predicate)
  | none => sink.patterns

def literalOrder (input : Input) (sinks : List Sink) : List Literal :=
  sinks.flatMap (selectedLiterals input)

/-- Valid FULL TAINT checkMark projection: None or Holds of a fully annotated
part, always selected from this original immutable input. No FLOW request. -/
def checkMark (input : Input) (literal : Literal) : Option Tree :=
  if literal.base = input.value.base ∧ input.markOrder.contains literal.mark then literal.projected
  else none

def orderedScan {State Literal Part : Type} (check : Literal → Option Part)
    (update : State → Literal → Part → State) : List Literal → State → List Part × State
  | [], state => ([], state)
  | literal :: rest, state =>
      match check literal with
      | none => orderedScan check update rest state
      | some part =>
          let remaining := orderedScan check update rest (update state literal part)
          (part :: remaining.1, remaining.2)

def oldScan {State : Type} (input : Input) (update : State → Literal → Tree → State)
    (literals : List Literal) (state : State) : List Tree × State :=
  orderedScan (checkMark input) update literals state

def pureParts (input : Input) (literals : List Literal) : List Tree :=
  literals.filterMap (checkMark input)

theorem an_arbitrary_immutable_check_has_the_same_ordered_parts_despite_state_updates
    {State Literal Part : Type} (check : Literal → Option Part)
    (update : State → Literal → Part → State) (literals : List Literal) (state : State) :
    (orderedScan check update literals state).1 = literals.filterMap check := by
  induction literals generalizing state with
  | nil => rfl
  | cons literal rest preserved =>
      cases checked : check literal with
      | none => simp [orderedScan, checked, preserved]
      | some part => simp [orderedScan, checked, preserved]

theorem old_parts_equal_the_pure_ordered_parts_for_every_join_state
    {State : Type} (input : Input) (update : State → Literal → Tree → State)
    (literals : List Literal) (state : State) :
    (oldScan input update literals state).1 = pureParts input literals :=
  an_arbitrary_immutable_check_has_the_same_ordered_parts_despite_state_updates
    (checkMark input) update literals state

theorem different_old_join_or_report_states_do_not_change_the_parts
    {State : Type} (input : Input) (update : State → Literal → Tree → State)
    (literals : List Literal) (first second : State) :
    (oldScan input update literals first).1 = (oldScan input update literals second).1 := by
  rw [old_parts_equal_the_pure_ordered_parts_for_every_join_state,
    old_parts_equal_the_pure_ordered_parts_for_every_join_state]

def orderedWithout {Value Part : Type} (without : Value → Part → Option Value)
    (input : Value) (parts : List Part) : Option Value :=
  parts.foldl (fun current part => current.bind (fun value => without value part)) (some input)

theorem identical_ordered_parts_give_identical_existing_fold
    {Value Part : Type} (without : Value → Part → Option Value)
    (input : Value) (oldParts newParts : List Part) (same : oldParts = newParts) :
    orderedWithout without input oldParts = orderedWithout without input newParts := by rw [same]

/-- Existing exact-only header normalization. Empty trees disappear. -/
def withMembership (input : Tree) (exact any : Bool) : Option Tree :=
  if exact || any then some { input with
    exact := exact
    any := any
    exclusion := if any then input.exclusion else []
    anyTail := if any then input.anyTail else .must
    protectedExact := input.protectedExact && exact
    protectedAny := input.protectedAny && any }
  else none

/-- A finite cell of the existing withoutPart contract. ANY masks require
matching layer/header; exact-only masks do not require an ANY header match. -/
def without (input part : Tree) : Option Tree :=
  if input.layer ≠ part.layer ∨
      (part.any = true ∧ (input.exclusion ≠ part.exclusion ∨ input.anyTail ≠ part.anyTail)) then
    some input
  else withMembership input (input.exact && !part.exact) (input.any && !part.any)

def withoutEntryMark (input : Tree) (remove : Bool) : Option Tree :=
  if remove then none else some input

structure Mode where
  direction : Direction
  run1 : Bool
  deriving DecidableEq, Repr
structure Metadata where
  globalDrop : Bool
  removeEntryMark : Bool
  deriving DecidableEq, Repr

def finishWithParts (mode : Mode) (original : Original) (metadata : Metadata)
    (input : Input) (parts : List Tree) : Option Tree :=
  let global := if mode.direction = .forward ∧ metadata.globalDrop = true ∧
      original = .zero ∧ input.value.base = .static then orderedWithout without input.value parts
    else some input.value
  if mode.run1 = false ∧ original = .zero then global.bind
      (fun value => withoutEntryMark value metadata.removeEntryMark)
  else global

def oldFinish {State : Type} (mode : Mode) (original : Original) (metadata : Metadata)
    (input : Input) (sinks : List Sink) (update : State → Literal → Tree → State) (state : State) : Option Tree :=
  let parts := if mode.direction = .forward then
      (oldScan input update (literalOrder input sinks) state).1 else []
  finishWithParts mode original metadata input parts

def pureFinish (mode : Mode) (original : Original) (metadata : Metadata)
    (input : Input) (sinks : List Sink) : Option Tree :=
  let parts := if mode.direction = .forward then pureParts input (literalOrder input sinks) else []
  finishWithParts mode original metadata input parts

theorem the_restored_complete_method_original_preserves_the_entire_finalizer
    {State : Type} (mode : Mode) (original : Original) (metadata : Metadata)
    (input : Input) (sinks : List Sink) (update : State → Literal → Tree → State) (state : State) :
    oldFinish mode original metadata input sinks update state = pureFinish mode original metadata input sinks := by
  unfold oldFinish pureFinish
  rw [old_parts_equal_the_pure_ordered_parts_for_every_join_state]

theorem backward_global_drop_has_no_forward_sink_mask_effect
    (run1 : Bool) (original : Original) (remove : Bool) (input : Input) (sinks : List Sink) :
    pureFinish ⟨.backward, run1⟩ original ⟨true, remove⟩ input sinks =
      pureFinish ⟨.backward, run1⟩ original ⟨false, remove⟩ input sinks := by
  simp [pureFinish, finishWithParts]

def mixed : Tree := {
  base := .static, exact := true, any := true, layer := .demand,
  exclusion := [], anyTail := .may, protectedExact := true, protectedAny := true }
def onlyAny : Tree := { mixed with exact := false, protectedExact := false }
def onlyExact : Tree := { mixed with any := false, anyTail := .must, protectedAny := false }
def childLiteral : Literal := {
  occurrence := 1, ordinal := 0, base := .static, mark := 10, projected := some onlyAny }
def rootLiteral : Literal := {
  occurrence := 2, ordinal := 2, base := .static, mark := 10, projected := some mixed }
def absentLiteral : Literal := {
  occurrence := 1, ordinal := 1, base := .static, mark := 20, projected := none }
def mixedInput : Input := { value := mixed, markOrder := [10] }
def ndSink : Sink := { predicate := some ⟨false, [childLiteral, absentLiteral]⟩, patterns := [] }

structure JoinState where
  first : Bool
  second : Bool
  fired : Bool
  deriving DecidableEq, Repr

def updateJoin (state : JoinState) (literal : Literal) (_part : Tree) : JoinState :=
  let first := state.first || decide (literal.ordinal = 0)
  let second := state.second || decide (literal.ordinal = 1)
  { first, second, fired := state.fired || first && second }

theorem an_incomplete_ND_guard_still_appends_its_positive_Holds_part :
    oldScan mixedInput updateJoin (literalOrder mixedInput [ndSink]) ⟨false, false, false⟩ =
      ([onlyAny], ⟨true, false, false⟩) := by decide

theorem a_prior_ND_binding_changes_firing_but_not_the_ordered_parts :
    oldScan mixedInput updateJoin (literalOrder mixedInput [ndSink]) ⟨false, true, false⟩ =
      ([onlyAny], ⟨true, true, true⟩) := by decide

theorem TRUE_predicates_use_the_legacy_pattern_branch :
    selectedLiterals mixedInput ⟨some ⟨true, []⟩, [rootLiteral, childLiteral]⟩ =
      [rootLiteral, childLiteral] := by decide

theorem indexed_predicates_keep_mark_then_leaf_order_instead_of_scanning_all_leaves :
    selectedLiterals { mixedInput with markOrder := [20, 10] }
      ⟨some ⟨false, [childLiteral, absentLiteral, rootLiteral]⟩, []⟩ =
      [absentLiteral, childLiteral, rootLiteral] := by decide

theorem repeated_legacy_patterns_keep_both_Holds_parts :
    pureParts mixedInput (literalOrder mixedInput [⟨none, [childLiteral, childLiteral]⟩]) =
      [onlyAny, onlyAny] := by decide

theorem all_masks_are_selected_from_the_original_mixed_input :
    pureParts mixedInput [childLiteral, rootLiteral] = [onlyAny, mixed] := by decide

theorem removing_the_last_ANY_normalizes_the_surviving_EXACT_header_and_protection :
    without mixed onlyAny = some onlyExact := by decide

theorem the_original_ordered_fold_keeps_the_EXACT_survivor :
    orderedWithout without mixed [onlyAny, mixed] = some onlyExact := by decide

theorem reversing_the_masks_changes_the_result :
    orderedWithout without mixed [mixed, onlyAny] = none := by decide

theorem replacing_masks_with_their_union_changes_the_result :
    orderedWithout without mixed [mixed] = none ∧
    orderedWithout without mixed [onlyAny, mixed] ≠ orderedWithout without mixed [mixed] := by decide

theorem a_mask_from_another_layer_is_not_reused :
    without { mixed with layer := .normal } onlyAny = some { mixed with layer := .normal } := by decide

def entryInput : Input := {
  value := { onlyExact with base := .argument, layer := .normal }, markOrder := [10] }
def entryMetadata : Metadata := ⟨false, true⟩

theorem using_a_nonzero_local_initial_instead_of_method_ZERO_changes_entry_removal :
    pureFinish ⟨.forward, false⟩ .zero entryMetadata entryInput [] = none ∧
    pureFinish ⟨.forward, false⟩ .local entryMetadata entryInput [] = some entryInput.value := by decide

theorem using_local_ZERO_instead_of_a_nonzero_method_original_changes_global_drop :
    pureFinish ⟨.forward, false⟩ .argument ⟨true, false⟩ mixedInput [⟨none, [rootLiteral]⟩] = some mixed ∧
    pureFinish ⟨.forward, false⟩ .zero ⟨true, false⟩ mixedInput [⟨none, [rootLiteral]⟩] = none := by decide

theorem the_existing_run1_entry_mark_removal_exception_is_unchanged :
    pureFinish ⟨.forward, true⟩ .zero entryMetadata entryInput [] = some entryInput.value := by decide

theorem backward_can_still_apply_the_existing_entry_mark_metadata :
    pureFinish ⟨.backward, false⟩ .zero entryMetadata entryInput [] = none := by decide

theorem a_ZERO_literal_does_not_select_a_static_global_drop_part :
    checkMark { mixedInput with markOrder := [0, 10] }
      { childLiteral with base := .zero, mark := 0 } = none := by decide

theorem an_empty_FALSE_index_does_not_fall_back_to_legacy_patterns :
    selectedLiterals mixedInput ⟨some ⟨false, []⟩, [rootLiteral]⟩ = [] := by decide

end MethodExitMetadataEffects

/- Per-module axiom audit; the package checker audits these declarations too. -/
#print axioms MethodExitMetadataEffects.matchingLeaves
#print axioms MethodExitMetadataEffects.selectedLiterals
#print axioms MethodExitMetadataEffects.literalOrder
#print axioms MethodExitMetadataEffects.checkMark
#print axioms MethodExitMetadataEffects.orderedScan
#print axioms MethodExitMetadataEffects.oldScan
#print axioms MethodExitMetadataEffects.pureParts
#print axioms MethodExitMetadataEffects.an_arbitrary_immutable_check_has_the_same_ordered_parts_despite_state_updates
#print axioms MethodExitMetadataEffects.old_parts_equal_the_pure_ordered_parts_for_every_join_state
#print axioms MethodExitMetadataEffects.different_old_join_or_report_states_do_not_change_the_parts
#print axioms MethodExitMetadataEffects.orderedWithout
#print axioms MethodExitMetadataEffects.identical_ordered_parts_give_identical_existing_fold
#print axioms MethodExitMetadataEffects.withMembership
#print axioms MethodExitMetadataEffects.without
#print axioms MethodExitMetadataEffects.withoutEntryMark
#print axioms MethodExitMetadataEffects.finishWithParts
#print axioms MethodExitMetadataEffects.oldFinish
#print axioms MethodExitMetadataEffects.pureFinish
#print axioms MethodExitMetadataEffects.the_restored_complete_method_original_preserves_the_entire_finalizer
#print axioms MethodExitMetadataEffects.backward_global_drop_has_no_forward_sink_mask_effect
#print axioms MethodExitMetadataEffects.mixed
#print axioms MethodExitMetadataEffects.onlyAny
#print axioms MethodExitMetadataEffects.onlyExact
#print axioms MethodExitMetadataEffects.childLiteral
#print axioms MethodExitMetadataEffects.rootLiteral
#print axioms MethodExitMetadataEffects.absentLiteral
#print axioms MethodExitMetadataEffects.mixedInput
#print axioms MethodExitMetadataEffects.ndSink
#print axioms MethodExitMetadataEffects.updateJoin
#print axioms MethodExitMetadataEffects.an_incomplete_ND_guard_still_appends_its_positive_Holds_part
#print axioms MethodExitMetadataEffects.a_prior_ND_binding_changes_firing_but_not_the_ordered_parts
#print axioms MethodExitMetadataEffects.TRUE_predicates_use_the_legacy_pattern_branch
#print axioms MethodExitMetadataEffects.indexed_predicates_keep_mark_then_leaf_order_instead_of_scanning_all_leaves
#print axioms MethodExitMetadataEffects.repeated_legacy_patterns_keep_both_Holds_parts
#print axioms MethodExitMetadataEffects.all_masks_are_selected_from_the_original_mixed_input
#print axioms MethodExitMetadataEffects.removing_the_last_ANY_normalizes_the_surviving_EXACT_header_and_protection
#print axioms MethodExitMetadataEffects.the_original_ordered_fold_keeps_the_EXACT_survivor
#print axioms MethodExitMetadataEffects.reversing_the_masks_changes_the_result
#print axioms MethodExitMetadataEffects.replacing_masks_with_their_union_changes_the_result
#print axioms MethodExitMetadataEffects.a_mask_from_another_layer_is_not_reused
#print axioms MethodExitMetadataEffects.entryInput
#print axioms MethodExitMetadataEffects.entryMetadata
#print axioms MethodExitMetadataEffects.using_a_nonzero_local_initial_instead_of_method_ZERO_changes_entry_removal
#print axioms MethodExitMetadataEffects.using_local_ZERO_instead_of_a_nonzero_method_original_changes_global_drop
#print axioms MethodExitMetadataEffects.the_existing_run1_entry_mark_removal_exception_is_unchanged
#print axioms MethodExitMetadataEffects.backward_can_still_apply_the_existing_entry_mark_metadata
#print axioms MethodExitMetadataEffects.a_ZERO_literal_does_not_select_a_static_global_drop_part
#print axioms MethodExitMetadataEffects.an_empty_FALSE_index_does_not_fall_back_to_legacy_patterns
