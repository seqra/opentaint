import Std

/-!
Selected contract: publish a reached Target or run-1 static output at its nearest
block boundary, then use ordinary complete summary application at every ancestor.

This constructive finite interface model checks ownership, paired scope labels,
complete bindings, typed Target restrictions, annotations and local handoff.
It does not verify AP matching, rule execution, the Kotlin adapter, physical CFG
construction or convergence. Binding input is the existing matched application
result, not permission to create an unmatched literal or a new ZERO seed.
-/
namespace NearestBoundaryTerminals
set_option autoImplicit false

structure Block where
  ordinal : Nat
  deriving DecidableEq, Repr
namespace Block
def leaf : Block := ⟨3⟩
def inner : Block := ⟨2⟩
def outer : Block := ⟨1⟩
def root : Block := ⟨0⟩
end Block
inductive Port where
  | leafIn | innerIn | outerIn | rootIn | normalOut | staticShortcut | other
  deriving DecidableEq, Repr
inductive Atom where
  | localT | argumentT | argumentU | rootT | rootU | staticF | staticG | unrelated
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr
inductive Terminal where
  | demandTarget
  | normalTarget (report : Nat)
  | run1Static (field : Nat) (path : List Nat) (mark : Nat)
  deriving DecidableEq, Repr

def parentOf (block : Block) : Option Block :=
  match block.ordinal with
  | 0 => none
  | n + 1 => some ⟨n⟩

structure Scope where
  block : Block
  entry : Port
  deriving DecidableEq, Repr
structure Annotations where
  protection : Bool
  reportSite : Nat
  deriving DecidableEq, Repr
structure Row where
  scope : Scope
  exit : Port
  premise : List Atom
  terminal : Terminal
  layer : Layer
  annotations : Annotations
  deriving DecidableEq, Repr
structure MemberBinding where
  member : Atom
  parentOriginal : List Atom
  layer : Layer
  deriving DecidableEq, Repr
structure Link where
  child : Scope
  parent : Scope
  childExit : Port
  parentExit : Port
  bindings : List MemberBinding
  reachedZero : Bool
  zeroParentOriginal : List Atom
  offeredLayer : Layer
  deriving DecidableEq, Repr

def unionOrigins (bindings : List MemberBinding) : List Atom :=
  (bindings.flatMap MemberBinding.parentOriginal).eraseDups

/-- Supplied members are already matched by the ordinary AP applicator. Every
required member must occur. ZERO requires the existing actual ZERO offer. -/
def complete (row : Row) (link : Link) : Bool :=
  if row.premise.isEmpty then link.reachedZero
  else decide (row.premise = row.premise.eraseDups) &&
    row.premise.all (fun member => link.bindings.any (fun bound => bound.member = member)) &&
    decide ((link.bindings.filter (fun bound => row.premise.contains bound.member)).length = row.premise.length)

def selectedBindings (row : Row) (link : Link) : List MemberBinding :=
  link.bindings.filter (fun bound => row.premise.contains bound.member)

def bindingLayer (row : Row) (link : Link) : Layer :=
  if row.layer = .demand ∨ link.offeredLayer = .demand ∨
      (selectedBindings row link).any (fun bound => bound.layer = .demand) then .demand
  else .normal

def validInterface (row : Row) (link : Link) : Bool :=
  decide (row.scope = link.child ∧ row.exit = link.childExit ∧
    parentOf link.child.block = some link.parent.block)

def terminalAllowed (terminal : Terminal) (layer : Layer) : Bool :=
  match terminal with
  | .normalTarget _ => decide (layer = .normal)
  | .demandTarget => true
  | .run1Static _ _ _ => true

def resultLayer (terminal : Terminal) (bound : Layer) : Layer :=
  match terminal with
  | .demandTarget | .run1Static _ _ _ => .demand
  | .normalTarget _ => bound

/-- One ordinary adjacent parent application. No ancestor can be skipped. -/
def compose (row : Row) (link : Link) : Option Row :=
  if validInterface row link && complete row link &&
      terminalAllowed row.terminal (bindingLayer row link) then
    some {
      scope := link.parent
      exit := link.parentExit
      premise := if row.premise.isEmpty then link.zeroParentOriginal
        else unionOrigins (selectedBindings row link)
      terminal := row.terminal
      layer := resultLayer row.terminal (bindingLayer row link)
      annotations := row.annotations }
  else none

/-- A genuine physical sink/write event has already occurred. This function
only records the supplied semantic result at its actual nearest scope. -/
def publishNearest (scope : Scope) (exit : Port) (premise : List Atom)
    (terminal : Terminal) (layer : Layer) (annotations : Annotations)
    (_eligible : terminalAllowed terminal layer = true) : Row :=
  { scope, exit, premise, terminal, layer := resultLayer terminal layer, annotations }

theorem every_composed_result_keeps_its_terminal_and_annotations
    (row : Row) (link : Link) (result : Row) (found : compose row link = some result) :
    result.terminal = row.terminal ∧ result.annotations = row.annotations ∧
    result.scope = link.parent ∧ result.exit = link.parentExit := by
  unfold compose at found
  split at found
  · have same := Option.some.inj found
    cases same
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

theorem every_composed_result_has_one_complete_adjacent_interface
    (row : Row) (link : Link) (result : Row) (found : compose row link = some result) :
    validInterface row link = true ∧ complete row link = true ∧
    terminalAllowed row.terminal (bindingLayer row link) = true := by
  unfold compose at found
  split at found
  · rename_i permitted
    simpa only [Bool.and_eq_true, and_assoc] using permitted
  · contradiction

def leafScope : Scope := { block := .leaf, entry := .leafIn }
def innerScope : Scope := { block := .inner, entry := .innerIn }
def outerScope : Scope := { block := .outer, entry := .outerIn }
def rootScope : Scope := { block := .root, entry := .rootIn }
def notes : Annotations := { protection := true, reportSite := 17 }
def demandLeaf : Row := publishNearest leafScope .normalOut [.localT]
  .demandTarget .demand notes (by decide)
def normalLeaf : Row := publishNearest leafScope .normalOut [.localT]
  (.normalTarget 42) .normal notes (by decide)
def staticLeaf : Row := publishNearest leafScope .normalOut [.localT]
  (.run1Static 7 [1, 2] 9) .demand notes (by decide)

def leafLink : Link := {
  child := leafScope, parent := innerScope, childExit := .normalOut, parentExit := .normalOut,
  bindings := [{ member := .localT, parentOriginal := [.argumentT], layer := .normal }],
  reachedZero := false, zeroParentOriginal := [], offeredLayer := .normal }
def innerLink : Link := {
  child := innerScope, parent := outerScope, childExit := .normalOut, parentExit := .normalOut,
  bindings := [{ member := .argumentT, parentOriginal := [.rootT], layer := .normal }],
  reachedZero := false, zeroParentOriginal := [], offeredLayer := .normal }
def outerLink : Link := {
  child := outerScope, parent := rootScope, childExit := .normalOut, parentExit := .normalOut,
  bindings := [{ member := .rootT, parentOriginal := [], layer := .normal }],
  reachedZero := false, zeroParentOriginal := [], offeredLayer := .normal }

def demandInner : Row := { demandLeaf with scope := innerScope, premise := [.argumentT] }
def demandOuter : Row := { demandLeaf with scope := outerScope, premise := [.rootT] }
def demandRoot : Row := { demandLeaf with scope := rootScope, premise := [] }

def propagate (row : Row) (links : List Link) : List Row :=
  match links with
  | [] => [row]
  | link :: rest => match compose row link with
    | none => [row]
    | some parent => row :: propagate parent rest

theorem nearest_publication_keeps_its_true_original_and_both_ports :
    demandLeaf.scope = leafScope ∧ demandLeaf.exit = .normalOut ∧
    demandLeaf.premise = [.localT] := by decide

theorem a_normal_Target_retains_its_report_identity :
    compose normalLeaf leafLink = some {
      normalLeaf with scope := innerScope, premise := [.argumentT] } := by decide

theorem a_demand_Target_has_an_ordinary_adjacent_parent_result :
    compose demandLeaf leafLink = some demandInner := by decide

theorem every_ancestor_keeps_a_scoped_demand_Target_row :
    propagate demandLeaf [leafLink, innerLink, outerLink] =
      [demandLeaf, demandInner, demandOuter, demandRoot] := by decide

theorem normal_ancestor_application_reaches_the_method_ZERO_report :
    (propagate normalLeaf [leafLink, innerLink, outerLink]).getLast? =
      some { normalLeaf with scope := rootScope, premise := [] } := by decide

theorem run1_static_application_keeps_the_complete_static_payload :
    (propagate staticLeaf [leafLink, innerLink, outerLink]).getLast? =
      some { staticLeaf with scope := rootScope, premise := [] } := by decide

theorem propagation_preserves_the_physical_report_site_and_protection :
    (propagate demandLeaf [leafLink, innerLink, outerLink]).map Row.annotations =
      [notes, notes, notes, notes] := by decide

theorem a_local_result_cannot_skip_its_actual_parent :
    compose demandLeaf { leafLink with parent := rootScope } = none := by decide

theorem another_child_entry_is_not_a_saved_summary_match :
    compose demandLeaf { leafLink with child := { leafScope with entry := .other } } = none := by decide

theorem another_child_exit_is_not_a_saved_summary_match :
    compose demandLeaf { leafLink with childExit := .other } = none := by decide

theorem an_unmatched_literal_does_not_emit_a_parent_Target :
    compose demandLeaf { leafLink with bindings := [] } = none := by decide

theorem a_demand_context_cannot_apply_a_NormalTarget :
    compose normalLeaf { leafLink with offeredLayer := .demand } = none := by decide

theorem a_demand_context_can_continue_a_DemandTarget :
    compose demandLeaf { leafLink with offeredLayer := .demand } = some demandInner := by decide

def ndLeaf : Row := { demandLeaf with premise := [.argumentT, .argumentU] }
def ndLink : Link := { leafLink with bindings := [
  { member := .argumentT, parentOriginal := [.rootT], layer := .normal },
  { member := .argumentU, parentOriginal := [.rootU], layer := .demand }] }

theorem complete_ND_application_preserves_every_contributing_original :
    compose ndLeaf ndLink = some {
      demandLeaf with scope := innerScope, premise := [.rootT, .rootU] } := by decide

theorem a_unary_restriction_arm_cannot_replace_complete_ND_execution :
    compose ndLeaf { ndLink with bindings := ndLink.bindings.take 1 } = none := by decide

theorem an_ND_demand_member_prevents_a_NormalTarget_result :
    compose { ndLeaf with terminal := .normalTarget 42, layer := .normal } ndLink = none := by decide

def zeroLeaf : Row := { demandLeaf with premise := [] }

theorem ZERO_publication_still_needs_the_existing_reached_ZERO_offer :
    compose zeroLeaf leafLink = none := by decide

theorem an_actual_ZERO_offer_uses_its_true_waiting_parent_original :
    compose zeroLeaf { leafLink with reachedZero := true, zeroParentOriginal := [.rootT] } =
      some { demandInner with premise := [.rootT] } := by decide

structure Guidance where
  scope : Scope
  exit : Port
  entryEndpoint : Terminal
  exitPremise : List Atom
  annotations : Annotations
  deriving DecidableEq, Repr

def reverseScope (row : Row) : Scope := { block := row.scope.block, entry := row.exit }

/-- Only selected terminal DEMAND rows enter this finite Target/static handoff
view. Native NORMAL data and the backward-ZERO exception are outside its scope. -/
def handoff (row : Row) : Option Guidance :=
  if row.layer = .demand then some {
    scope := reverseScope row
    exit := row.scope.entry
    entryEndpoint := row.terminal
    exitPremise := row.premise
    annotations := row.annotations }
  else none

def scopedGuidance (rows : List Row) (scope : Scope) : List Guidance :=
  (rows.filterMap handoff).filter (fun guide => guide.scope = scope)

theorem nearest_publication_supplies_its_local_complete_handoff :
    scopedGuidance (propagate demandLeaf [leafLink, innerLink, outerLink]) (reverseScope demandLeaf) = [
      { scope := reverseScope demandLeaf, exit := .leafIn,
        entryEndpoint := .demandTarget, exitPremise := [.localT], annotations := notes }] := by decide

theorem each_composed_parent_has_its_own_paired_guidance :
    (scopedGuidance (propagate demandLeaf [leafLink, innerLink, outerLink]) (reverseScope demandInner)).length = 1 ∧
    (scopedGuidance (propagate demandLeaf [leafLink, innerLink, outerLink]) (reverseScope demandOuter)).length = 1 ∧
    (scopedGuidance (propagate demandLeaf [leafLink, innerLink, outerLink]) (reverseScope demandRoot)).length = 1 := by decide

theorem root_only_terminal_ownership_does_not_supply_local_guidance :
    scopedGuidance [demandRoot] (reverseScope demandLeaf) = [] ∧
    scopedGuidance [demandRoot] (reverseScope demandInner) = [] := by decide

theorem a_NormalTarget_does_not_create_backward_refinement_guidance :
    handoff normalLeaf = none := by decide

theorem run1_static_handoff_keeps_its_field_path_mark_and_complete_original :
    handoff staticLeaf = some {
      scope := reverseScope staticLeaf, exit := .leafIn,
      entryEndpoint := .run1Static 7 [1, 2] 9,
      exitPremise := [.localT], annotations := notes } := by decide

theorem selected_terminal_handoff_reverses_both_genuine_ports
    (row : Row) (guide : Guidance) (found : handoff row = some guide) :
    guide.scope = reverseScope row ∧ guide.exit = row.scope.entry ∧
    guide.entryEndpoint = row.terminal ∧ guide.exitPremise = row.premise ∧
    guide.annotations = row.annotations := by
  unfold handoff at found
  split at found
  · have same := Option.some.inj found
    cases same
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · contradiction

def staticAtom : Atom → Bool
  | .staticF | .staticG => true
  | _ => false

/-- Existing run-1 static/static erasure belongs at the public method boundary.
Its complete relation remains a static completion seed there. -/
def publicAdmission (row : Row) : Option Row × Option Row :=
  match row.terminal with
  | .run1Static _ _ _ =>
      if row.scope.block = .root ∧ !row.premise.isEmpty ∧ row.premise.all staticAtom then
        (none, some row)
      else (some row, none)
  | _ => (some row, none)

def staticCopyLeaf : Row := { staticLeaf with premise := [.staticF] }
def staticCopyLink (link : Link) : Link := { link with bindings := [
  { member := .staticF, parentOriginal := [.staticF], layer := .normal }] }
def staticCopyInner : Row := { staticCopyLeaf with scope := innerScope }
def staticCopyOuter : Row := { staticCopyLeaf with scope := outerScope }
def staticCopyRoot : Row := { staticCopyLeaf with scope := rootScope }

theorem static_static_rows_are_composed_through_each_internal_ancestor :
    propagate staticCopyLeaf [staticCopyLink leafLink, staticCopyLink innerLink, staticCopyLink outerLink] =
      [staticCopyLeaf, staticCopyInner, staticCopyOuter, staticCopyRoot] := by decide

theorem internal_static_static_rows_are_not_erased :
    publicAdmission staticCopyLeaf = (some staticCopyLeaf, none) ∧
    publicAdmission staticCopyInner = (some staticCopyInner, none) ∧
    publicAdmission staticCopyOuter = (some staticCopyOuter, none) := by decide

theorem only_the_public_static_static_row_becomes_a_complete_static_seed :
    publicAdmission staticCopyRoot = (none, some staticCopyRoot) := by decide

theorem a_public_Target_is_not_erased_by_the_static_static_policy :
    publicAdmission demandRoot = (some demandRoot, none) := by decide

structure ScopedContribution where
  scope : Scope
  binding : MemberBinding
  deriving DecidableEq, Repr

def boundaryInputs (scope : Scope) (inputs : List ScopedContribution) : List MemberBinding :=
  (inputs.filter (fun contribution => contribution.scope = scope)).map ScopedContribution.binding

def boundaryJoin (scope : Scope) (row : Row) (link : Link)
    (inputs : List ScopedContribution) : Option Row :=
  if row.scope = scope then compose row { link with bindings := boundaryInputs scope inputs }
  else none

def secondEntry : Scope := { leafScope with entry := .other }
def firstBound : MemberBinding := { member := .argumentT, parentOriginal := [], layer := .normal }
def secondBound : MemberBinding := { member := .argumentU, parentOriginal := [], layer := .normal }
def conditionalNormalSink : Row := { normalLeaf with premise := [.argumentT, .argumentU] }
def splitEntryInputs : List ScopedContribution := [
  { scope := leafScope, binding := firstBound },
  { scope := secondEntry, binding := secondBound }]
def sameEntryInputs : List ScopedContribution := [
  { scope := leafScope, binding := firstBound },
  { scope := leafScope, binding := secondBound }]

theorem every_boundary_input_keeps_the_selected_exact_scope
    (scope : Scope) (inputs : List ScopedContribution) (contribution : ScopedContribution)
    (selected : contribution ∈ inputs.filter (fun input => input.scope = scope)) :
    contribution.scope = scope := by
  have same := (List.mem_filter.mp selected).2
  simpa only [decide_eq_true_eq] using same

theorem the_earlier_unscoped_boundary_join_can_combine_mutually_exclusive_entries :
    compose conditionalNormalSink { leafLink with bindings := splitEntryInputs.map ScopedContribution.binding } =
      some { normalLeaf with scope := innerScope, premise := [] } := by decide

theorem withdrawn_physical_entry_partition_would_remove_the_accepted_branch_union :
    boundaryJoin leafScope conditionalNormalSink leafLink splitEntryInputs = none ∧
    boundaryJoin secondEntry { conditionalNormalSink with scope := secondEntry }
      { leafLink with child := secondEntry } splitEntryInputs = none := by decide

theorem complete_ND_evidence_within_one_entry_still_emits_the_normal_Target :
    boundaryJoin leafScope conditionalNormalSink leafLink sameEntryInputs =
      some { normalLeaf with scope := innerScope, premise := [] } := by decide

theorem a_duplicate_literal_is_not_a_complete_ND_binding :
    compose conditionalNormalSink { leafLink with bindings := [firstBound, firstBound] } = none := by decide

inductive EntryRole where
  | normalLeave | feedback | exceptional | methodReturn | discovery
  deriving DecidableEq, Repr
structure RoutedContribution where
  actual : ScopedContribution
  role : EntryRole
  deriving DecidableEq, Repr
structure NormalizedContribution where
  actual : RoutedContribution
  joinScope : Scope
  deriving DecidableEq, Repr

/-- A finite shared normal interface. The full actual contribution is retained;
only its join owner is canonicalized. Non-normal roles keep their exact scope. -/
def normalizeContribution (input : RoutedContribution) : NormalizedContribution :=
  { actual := input, joinScope :=
      if input.role = .normalLeave ∧ input.actual.scope.block = leafScope.block
      then leafScope else input.actual.scope }

def commonNormalBindings (scope : Scope) (inputs : List RoutedContribution) : List MemberBinding :=
  ((inputs.map normalizeContribution).filter (fun input => input.joinScope = scope)).map
    (fun input => input.actual.actual.binding)

def commonNormalJoin (row : Row) (link : Link) (inputs : List RoutedContribution) : Option Row :=
  compose row { link with bindings := commonNormalBindings row.scope inputs }

def normalBranchInputs : List RoutedContribution :=
  splitEntryInputs.map (fun input => { actual := input, role := .normalLeave })
def secondActual : ScopedContribution := { scope := secondEntry, binding := secondBound }

theorem canonicalizing_the_normal_join_keeps_the_actual_contribution (input : RoutedContribution) :
    (normalizeContribution input).actual = input := rfl

theorem the_common_normal_exit_retains_the_accepted_branch_union_false_positive :
    commonNormalJoin conditionalNormalSink leafLink normalBranchInputs =
      some { normalLeaf with scope := innerScope, premise := [] } := by decide

theorem the_common_normal_exit_still_requires_the_complete_ND_binding :
    commonNormalJoin conditionalNormalSink leafLink (normalBranchInputs.take 1) = none := by decide

theorem exceptional_feedback_return_and_discovery_are_not_normal_aliases :
    (normalizeContribution { actual := secondActual, role := .exceptional }).joinScope = secondEntry ∧
    (normalizeContribution { actual := secondActual, role := .feedback }).joinScope = secondEntry ∧
    (normalizeContribution { actual := secondActual, role := .methodReturn }).joinScope = secondEntry ∧
    (normalizeContribution { actual := secondActual, role := .discovery }).joinScope = secondEntry := by decide

/- An arbitrary finite ancestor chain. Each constructor contains the actual
ordinary application proof; no constructor skips a missing application. -/
inductive Lift : Row → Row → Type where
  | stay (row : Row) : Lift row row
  | step (first next last : Row) (link : Link)
      (applied : compose first link = some next) (rest : Lift next last) : Lift first last

def Lift.rows {first last : Row} (proof : Lift first last) : List Row :=
  match proof with
  | .stay row => [row]
  | .step first _ _ _ _ rest => first :: rest.rows

theorem every_finite_ancestor_chain_keeps_the_same_terminal_and_annotations
    {first last : Row} (proof : Lift first last) :
    last.terminal = first.terminal ∧ last.annotations = first.annotations := by
  induction proof with
  | stay row => exact ⟨rfl, rfl⟩
  | step first next last link applied rest preserved =>
      have stepLaw := every_composed_result_keeps_its_terminal_and_annotations first link next applied
      exact ⟨preserved.1.trans stepLaw.1, preserved.2.trans stepLaw.2.1⟩

theorem every_finite_ancestor_chain_collects_the_nearest_row
    {first last : Row} (proof : Lift first last) : first ∈ proof.rows := by
  cases proof <;> simp [Lift.rows]

theorem every_finite_ancestor_chain_collects_its_final_row
    {first last : Row} (proof : Lift first last) : last ∈ proof.rows := by
  induction proof with
  | stay row => simp [Lift.rows]
  | step first next last link applied rest collected =>
      exact List.mem_cons_of_mem first collected

/-- A raw run-1 static write still requires the original method exit operation.
An ordinary normal-output row has already passed that operation. The transport
port, rather than AP shape or local entry, distinguishes those phases. -/
inductive RootExitAction where
  | runActualExit | metadataOnly
  deriving DecidableEq, Repr

def rootExitAction (exit : Port) : RootExitAction :=
  if exit = .staticShortcut then .runActualExit else .metadataOnly

/-- Parent application retains the raw shortcut's typed output until the actual
method handler is reached. Binding/original/layer payloads use ordinary compose. -/
def carryShortcut (row : Row) (link : Link) : Option Row :=
  compose row { link with parentExit := row.exit }

def carryShortcutPath (row : Row) (links : List Link) : Option Row :=
  match links with
  | [] => some row
  | link :: rest => match carryShortcut row link with
    | none => none
    | some parent => carryShortcutPath parent rest

def rawStaticLeaf : Row := { staticLeaf with exit := .staticShortcut }

/-- The actual existing exit operation produces ordinary normal-output rows.
The semantic result is supplied by that operation, not synthesized here. -/
def exitOperationCompleted (actualOutput : Row) : Row :=
  { actualOutput with exit := .normalOut }

theorem raw_shortcut_requires_the_real_exit_handler :
    rootExitAction .staticShortcut = .runActualExit := by decide

theorem ordinary_normal_output_requires_metadata_only :
    rootExitAction .normalOut = .metadataOnly := by decide

theorem changing_the_static_initial_does_not_change_the_completed_phase
    (row : Row) :
    rootExitAction ({ row with exit := .normalOut } : Row).exit = .metadataOnly := rfl

theorem carried_shortcut_keeps_its_typed_exit
    (row : Row) (link : Link) (parent : Row)
    (found : carryShortcut row link = some parent) : parent.exit = row.exit := by
  exact (every_composed_result_keeps_its_terminal_and_annotations row
    { link with parentExit := row.exit } parent found).2.2.2

theorem arbitrary_shortcut_ancestors_keep_the_typed_exit
    (row : Row) (links : List Link) (last : Row)
    (found : carryShortcutPath row links = some last) : last.exit = row.exit := by
  induction links generalizing row with
  | nil => exact (Option.some.inj found) ▸ rfl
  | cons link rest ih =>
      unfold carryShortcutPath at found
      split at found
      · contradiction
      · rename_i parent applied
        exact (ih parent found).trans (carried_shortcut_keeps_its_typed_exit row link parent applied)

theorem raw_static_reaches_root_without_running_an_intermediate_exit :
    carryShortcutPath rawStaticLeaf [
      { leafLink with childExit := .staticShortcut },
      { innerLink with childExit := .staticShortcut },
      { outerLink with childExit := .staticShortcut }] =
      some { rawStaticLeaf with scope := rootScope, premise := [] } := by decide

theorem a_normal_output_link_cannot_apply_a_raw_shortcut_row :
    carryShortcut rawStaticLeaf leafLink = none := by decide

theorem a_completed_static_result_never_reenters_the_actual_exit (actualOutput : Row) :
    rootExitAction (exitOperationCompleted actualOutput).exit = .metadataOnly := rfl

theorem completing_the_exit_keeps_the_actual_semantic_result (actualOutput : Row) :
    (exitOperationCompleted actualOutput).terminal = actualOutput.terminal ∧
    (exitOperationCompleted actualOutput).premise = actualOutput.premise ∧
    (exitOperationCompleted actualOutput).annotations = actualOutput.annotations ∧
    (exitOperationCompleted actualOutput).layer = actualOutput.layer := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem raw_and_completed_static_rows_have_distinct_reversed_entries :
    (reverseScope rawStaticLeaf).entry = .staticShortcut ∧
    (reverseScope (exitOperationCompleted rawStaticLeaf)).entry = .normalOut ∧
    (reverseScope rawStaticLeaf).entry ≠
      (reverseScope (exitOperationCompleted rawStaticLeaf)).entry := by decide

theorem raw_shortcut_handoff_keeps_its_complete_pair :
    handoff rawStaticLeaf = some {
      scope := { leafScope with entry := .staticShortcut }, exit := .leafIn,
      entryEndpoint := .run1Static 7 [1, 2] 9,
      exitPremise := [.localT], annotations := notes } := by decide

theorem the_shortcut_output_is_not_an_operation_input_port :
    Port.staticShortcut ≠ Port.normalOut := by decide

end NearestBoundaryTerminals

/- Per-module axiom audit; the package checker audits these declarations too. -/
#print axioms NearestBoundaryTerminals.Block.leaf
#print axioms NearestBoundaryTerminals.Block.inner
#print axioms NearestBoundaryTerminals.Block.outer
#print axioms NearestBoundaryTerminals.Block.root
#print axioms NearestBoundaryTerminals.parentOf
#print axioms NearestBoundaryTerminals.unionOrigins
#print axioms NearestBoundaryTerminals.complete
#print axioms NearestBoundaryTerminals.selectedBindings
#print axioms NearestBoundaryTerminals.bindingLayer
#print axioms NearestBoundaryTerminals.validInterface
#print axioms NearestBoundaryTerminals.terminalAllowed
#print axioms NearestBoundaryTerminals.resultLayer
#print axioms NearestBoundaryTerminals.compose
#print axioms NearestBoundaryTerminals.publishNearest
#print axioms NearestBoundaryTerminals.every_composed_result_keeps_its_terminal_and_annotations
#print axioms NearestBoundaryTerminals.every_composed_result_has_one_complete_adjacent_interface
#print axioms NearestBoundaryTerminals.leafScope
#print axioms NearestBoundaryTerminals.innerScope
#print axioms NearestBoundaryTerminals.outerScope
#print axioms NearestBoundaryTerminals.rootScope
#print axioms NearestBoundaryTerminals.notes
#print axioms NearestBoundaryTerminals.demandLeaf
#print axioms NearestBoundaryTerminals.normalLeaf
#print axioms NearestBoundaryTerminals.staticLeaf
#print axioms NearestBoundaryTerminals.leafLink
#print axioms NearestBoundaryTerminals.innerLink
#print axioms NearestBoundaryTerminals.outerLink
#print axioms NearestBoundaryTerminals.demandInner
#print axioms NearestBoundaryTerminals.demandOuter
#print axioms NearestBoundaryTerminals.demandRoot
#print axioms NearestBoundaryTerminals.propagate
#print axioms NearestBoundaryTerminals.nearest_publication_keeps_its_true_original_and_both_ports
#print axioms NearestBoundaryTerminals.a_normal_Target_retains_its_report_identity
#print axioms NearestBoundaryTerminals.a_demand_Target_has_an_ordinary_adjacent_parent_result
#print axioms NearestBoundaryTerminals.every_ancestor_keeps_a_scoped_demand_Target_row
#print axioms NearestBoundaryTerminals.normal_ancestor_application_reaches_the_method_ZERO_report
#print axioms NearestBoundaryTerminals.run1_static_application_keeps_the_complete_static_payload
#print axioms NearestBoundaryTerminals.propagation_preserves_the_physical_report_site_and_protection
#print axioms NearestBoundaryTerminals.a_local_result_cannot_skip_its_actual_parent
#print axioms NearestBoundaryTerminals.another_child_entry_is_not_a_saved_summary_match
#print axioms NearestBoundaryTerminals.another_child_exit_is_not_a_saved_summary_match
#print axioms NearestBoundaryTerminals.an_unmatched_literal_does_not_emit_a_parent_Target
#print axioms NearestBoundaryTerminals.a_demand_context_cannot_apply_a_NormalTarget
#print axioms NearestBoundaryTerminals.a_demand_context_can_continue_a_DemandTarget
#print axioms NearestBoundaryTerminals.ndLeaf
#print axioms NearestBoundaryTerminals.ndLink
#print axioms NearestBoundaryTerminals.complete_ND_application_preserves_every_contributing_original
#print axioms NearestBoundaryTerminals.a_unary_restriction_arm_cannot_replace_complete_ND_execution
#print axioms NearestBoundaryTerminals.an_ND_demand_member_prevents_a_NormalTarget_result
#print axioms NearestBoundaryTerminals.zeroLeaf
#print axioms NearestBoundaryTerminals.ZERO_publication_still_needs_the_existing_reached_ZERO_offer
#print axioms NearestBoundaryTerminals.an_actual_ZERO_offer_uses_its_true_waiting_parent_original
#print axioms NearestBoundaryTerminals.reverseScope
#print axioms NearestBoundaryTerminals.handoff
#print axioms NearestBoundaryTerminals.scopedGuidance
#print axioms NearestBoundaryTerminals.nearest_publication_supplies_its_local_complete_handoff
#print axioms NearestBoundaryTerminals.each_composed_parent_has_its_own_paired_guidance
#print axioms NearestBoundaryTerminals.root_only_terminal_ownership_does_not_supply_local_guidance
#print axioms NearestBoundaryTerminals.a_NormalTarget_does_not_create_backward_refinement_guidance
#print axioms NearestBoundaryTerminals.run1_static_handoff_keeps_its_field_path_mark_and_complete_original
#print axioms NearestBoundaryTerminals.selected_terminal_handoff_reverses_both_genuine_ports
#print axioms NearestBoundaryTerminals.staticAtom
#print axioms NearestBoundaryTerminals.publicAdmission
#print axioms NearestBoundaryTerminals.staticCopyLeaf
#print axioms NearestBoundaryTerminals.staticCopyLink
#print axioms NearestBoundaryTerminals.staticCopyInner
#print axioms NearestBoundaryTerminals.staticCopyOuter
#print axioms NearestBoundaryTerminals.staticCopyRoot
#print axioms NearestBoundaryTerminals.static_static_rows_are_composed_through_each_internal_ancestor
#print axioms NearestBoundaryTerminals.internal_static_static_rows_are_not_erased
#print axioms NearestBoundaryTerminals.only_the_public_static_static_row_becomes_a_complete_static_seed
#print axioms NearestBoundaryTerminals.a_public_Target_is_not_erased_by_the_static_static_policy
#print axioms NearestBoundaryTerminals.boundaryInputs
#print axioms NearestBoundaryTerminals.boundaryJoin
#print axioms NearestBoundaryTerminals.secondEntry
#print axioms NearestBoundaryTerminals.firstBound
#print axioms NearestBoundaryTerminals.secondBound
#print axioms NearestBoundaryTerminals.conditionalNormalSink
#print axioms NearestBoundaryTerminals.splitEntryInputs
#print axioms NearestBoundaryTerminals.sameEntryInputs
#print axioms NearestBoundaryTerminals.every_boundary_input_keeps_the_selected_exact_scope
#print axioms NearestBoundaryTerminals.the_earlier_unscoped_boundary_join_can_combine_mutually_exclusive_entries
#print axioms NearestBoundaryTerminals.withdrawn_physical_entry_partition_would_remove_the_accepted_branch_union
#print axioms NearestBoundaryTerminals.complete_ND_evidence_within_one_entry_still_emits_the_normal_Target
#print axioms NearestBoundaryTerminals.a_duplicate_literal_is_not_a_complete_ND_binding
#print axioms NearestBoundaryTerminals.normalizeContribution
#print axioms NearestBoundaryTerminals.commonNormalBindings
#print axioms NearestBoundaryTerminals.commonNormalJoin
#print axioms NearestBoundaryTerminals.normalBranchInputs
#print axioms NearestBoundaryTerminals.secondActual
#print axioms NearestBoundaryTerminals.canonicalizing_the_normal_join_keeps_the_actual_contribution
#print axioms NearestBoundaryTerminals.the_common_normal_exit_retains_the_accepted_branch_union_false_positive
#print axioms NearestBoundaryTerminals.the_common_normal_exit_still_requires_the_complete_ND_binding
#print axioms NearestBoundaryTerminals.exceptional_feedback_return_and_discovery_are_not_normal_aliases
#print axioms NearestBoundaryTerminals.Lift.rows
#print axioms NearestBoundaryTerminals.every_finite_ancestor_chain_keeps_the_same_terminal_and_annotations
#print axioms NearestBoundaryTerminals.every_finite_ancestor_chain_collects_the_nearest_row
#print axioms NearestBoundaryTerminals.every_finite_ancestor_chain_collects_its_final_row
#print axioms NearestBoundaryTerminals.rootExitAction
#print axioms NearestBoundaryTerminals.carryShortcut
#print axioms NearestBoundaryTerminals.carryShortcutPath
#print axioms NearestBoundaryTerminals.rawStaticLeaf
#print axioms NearestBoundaryTerminals.exitOperationCompleted
#print axioms NearestBoundaryTerminals.raw_shortcut_requires_the_real_exit_handler
#print axioms NearestBoundaryTerminals.ordinary_normal_output_requires_metadata_only
#print axioms NearestBoundaryTerminals.changing_the_static_initial_does_not_change_the_completed_phase
#print axioms NearestBoundaryTerminals.carried_shortcut_keeps_its_typed_exit
#print axioms NearestBoundaryTerminals.arbitrary_shortcut_ancestors_keep_the_typed_exit
#print axioms NearestBoundaryTerminals.raw_static_reaches_root_without_running_an_intermediate_exit
#print axioms NearestBoundaryTerminals.a_completed_static_result_never_reenters_the_actual_exit
#print axioms NearestBoundaryTerminals.completing_the_exit_keeps_the_actual_semantic_result
#print axioms NearestBoundaryTerminals.raw_and_completed_static_rows_have_distinct_reversed_entries
#print axioms NearestBoundaryTerminals.raw_shortcut_handoff_keeps_its_complete_pair
#print axioms NearestBoundaryTerminals.the_shortcut_output_is_not_an_operation_input_port
#print axioms NearestBoundaryTerminals.a_normal_output_link_cannot_apply_a_raw_shortcut_row
