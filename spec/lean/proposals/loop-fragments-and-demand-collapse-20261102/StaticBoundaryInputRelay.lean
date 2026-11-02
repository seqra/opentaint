import Std

/-!
Narrow operation-local ROOT_EXIT relay. Only a genuine FLOW mark-check request
starts it. It follows existing identity continuation links to the original
registered root input and delegates materialization to the existing input
request service. A reached C.g/T never proves C.f/T. A genuine reply enters
inner spans under canonical C.g/T and keeps C.f/T only at the waiting outer link.

This finite interface model does not verify AP matching/materialization, the
Kotlin traversal or source rules. No global static request/history store is
introduced. Actual point processing precedes ordinary output deduplication.
-/
namespace StaticBoundaryInputRelay
set_option autoImplicit false

structure Scope where
  depth : Nat
  rootExit : Bool
  deriving DecidableEq, Repr
structure Link where
  id : Nat
  child : Scope
  parent : Scope
  originalField : Nat
  imageField : Nat
  deriving DecidableEq, Repr
structure RegisteredLink where
  link : Link
  registered : Bool
  present : registered = true
  localExit : link.child.rootExit = true
  strictParent : link.parent.depth < link.child.depth

inductive IdentityPath where
  | root (input : RegisteredLink)
  | hop (input : RegisteredLink) (rest : IdentityPath)

def IdentityPath.scope : IdentityPath → Scope
  | .root input => input.link.child
  | .hop input _ => input.link.child
def IdentityPath.field : IdentityPath → Nat
  | .root input => input.link.imageField
  | .hop input _ => input.link.imageField
def validPath : IdentityPath → Bool
  | .root input => decide (input.link.parent.depth = 0)
  | .hop input rest =>
      decide (input.link.parent = rest.scope ∧ input.link.originalField = input.link.imageField ∧
        input.link.imageField = rest.field) && validPath rest

def IdentityPath.rootLink : IdentityPath → Link
  | .root input => input.link
  | .hop _ rest => rest.rootLink
def IdentityPath.replyScopes : IdentityPath → List Scope
  | .root input => [input.link.child]
  | .hop input rest => rest.replyScopes ++ [input.link.child]

inductive MarkCheck where
  | none | holds
  | request (mark : Nat)
  deriving DecidableEq, Repr
structure Point where
  scope : Scope
  field : Nat
  flow : Bool
  normalExitInput : Bool
  check : MarkCheck
  deriving DecidableEq, Repr
structure Interest where
  rootLink : Nat
  field : Nat
  mark : Nat
  deriving DecidableEq, Repr

def request (point : Point) (path : IdentityPath) : Option Interest :=
  match point.check with
  | .request mark =>
      if validPath path && point.flow && point.normalExitInput && point.scope.rootExit &&
          decide (point.scope = path.scope ∧ point.field = path.field) then
        some { rootLink := path.rootLink.id, field := path.rootLink.originalField, mark }
      else none
  | _ => none

def queries (point : Point) (paths : List IdentityPath) : List Interest :=
  (paths.filterMap (request point)).eraseDups

theorem every_successful_request_names_the_true_original_link
    (point : Point) (path : IdentityPath) (interest : Interest)
    (found : request point path = some interest) :
    interest.field = path.rootLink.originalField ∧ interest.rootLink = path.rootLink.id := by
  cases checked : point.check with
  | none => simp [request, checked] at found
  | holds => simp [request, checked] at found
  | request mark =>
      simp only [request, checked] at found
      split at found
      · have same := Option.some.inj found
        cases same
        exact ⟨rfl, rfl⟩
      · contradiction

theorem a_checked_identity_hop_strictly_decreases_scope_depth
    (input : RegisteredLink) (rest : IdentityPath)
    (checked : validPath (.hop input rest) = true) : rest.scope.depth < input.link.child.depth := by
  simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at checked
  have parent := checked.1.1
  rw [← parent]
  exact input.strictParent

theorem a_checked_identity_chain_preserves_its_actual_image_field
    (path : IdentityPath) (checked : validPath path = true) : path.rootLink.imageField = path.field := by
  induction path with
  | root input => rfl
  | hop input rest preserved =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact (preserved checked.2).trans checked.1.2.2.symm

structure Supply where
  field : Nat
  mark : Nat
  deriving DecidableEq, Repr

def existingPointInterest (point : Point) : Option Supply :=
  match point.check with
  | .request mark => if point.flow && point.normalExitInput && point.scope.rootExit then
      some { field := point.field, mark } else none
  | _ => none

structure Effects where
  originalPointInterest : Option Supply
  boundaryInputInterests : List Interest
  addedWriterRegistrations : Nat
  deriving DecidableEq, Repr

def collectEffects (point : Point) (paths : List IdentityPath) : Effects :=
  { originalPointInterest := existingPointInterest point,
    boundaryInputInterests := queries point paths, addedWriterRegistrations := 0 }

theorem the_existing_point_interest_and_writer_directory_are_unchanged
    (point : Point) (paths : List IdentityPath) :
    (collectEffects point paths).originalPointInterest = existingPointInterest point ∧
    (collectEffects point paths).addedWriterRegistrations = 0 := ⟨rfl, rfl⟩

structure Reply where
  outerOriginal : Supply
  innerInitial : Supply
  innerActual : Supply
  scopes : List Scope
  deriving DecidableEq, Repr

/-- The supply is an actual answer at the requested ORIGINAL field. The finite
image is the existing FLOW materializer's output; no supply is invented. -/
def answer (point : Point) (path : IdentityPath) (supply : Supply) : Option Reply :=
  match request point path with
  | none => none
  | some interest =>
      if supply.field = interest.field ∧ supply.mark = interest.mark then
        let actual : Supply := { field := path.field, mark := supply.mark }
        some {
          outerOriginal := supply
          innerInitial := actual
          innerActual := actual
          scopes := path.replyScopes }
      else none

theorem a_supply_at_another_field_never_answers_the_original
    (point : Point) (path : IdentityPath) (supply : Supply)
    (wrong : supply.field ≠ path.rootLink.originalField) : answer point path supply = none := by
  unfold answer
  cases found : request point path with
  | none => rfl
  | some interest =>
      have original := (every_successful_request_names_the_true_original_link point path interest found).1
      simp only [original, wrong, false_and, ↓reduceIte]

structure Effect where
  original : Supply
  resultMark : Nat
  deriving DecidableEq, Repr

/-- An existing leaf C.g/T -> ret/U row, applied after genuine local delivery. -/
def applyLeaf (reply : Reply) (field mark resultMark : Nat) : Option Effect :=
  if reply.innerInitial = { field, mark } ∧ reply.innerActual = reply.innerInitial then
    some { original := reply.outerOriginal, resultMark }
  else none

def rootScope : Scope := ⟨0, false⟩
def firstScope : Scope := ⟨1, true⟩
def middleScope : Scope := ⟨2, true⟩
def pointScope : Scope := ⟨3, true⟩
def outerLink : RegisteredLink := {
  link := { id := 1, child := firstScope, parent := rootScope, originalField := 1, imageField := 2 }
  registered := true, present := rfl, localExit := rfl, strictParent := by decide }
def middleLink : RegisteredLink := {
  link := { id := 2, child := middleScope, parent := firstScope, originalField := 2, imageField := 2 }
  registered := true, present := rfl, localExit := rfl, strictParent := by decide }
def innerLink : RegisteredLink := {
  link := { id := 3, child := pointScope, parent := middleScope, originalField := 2, imageField := 2 }
  registered := true, present := rfl, localExit := rfl, strictParent := by decide }
def path : IdentityPath := .hop innerLink (.hop middleLink (.root outerLink))
def point : Point := { scope := pointScope, field := 2, flow := true, normalExitInput := true, check := .request 10 }

theorem the_actual_point_requests_only_the_original_root_field :
    request point path = some { rootLink := 1, field := 1, mark := 10 } := by decide

theorem a_reached_image_group_does_not_answer_the_original_request :
    answer point path { field := 2, mark := 10 } = none := by decide

theorem a_genuine_original_supply_keeps_both_original_and_canonical_inner_basis :
    answer point path { field := 1, mark := 10 } = some {
      outerOriginal := { field := 1, mark := 10 }, innerInitial := { field := 2, mark := 10 },
      innerActual := { field := 2, mark := 10 }, scopes := [firstScope, middleScope, pointScope] } := by decide

theorem the_existing_leaf_relation_composes_back_to_the_true_root_original :
    ((answer point path { field := 1, mark := 10 }).bind (fun reply => applyLeaf reply 2 10 20)) =
      some { original := { field := 1, mark := 10 }, resultMark := 20 } := by decide

theorem the_outer_field_cannot_be_used_as_the_inner_canonical_initial :
    ((answer point path { field := 1, mark := 10 }).bind (fun reply => applyLeaf reply 1 10 20)) = none := by decide

theorem no_actual_mark_request_means_no_relay :
    request { point with check := .holds } path = none ∧ request { point with check := .none } path = none := by decide

theorem concrete_inputs_and_other_operation_sites_do_not_use_this_relay :
    request { point with flow := false } path = none ∧
    request { point with normalExitInput := false } path = none := by decide

theorem another_scope_or_static_field_is_not_a_matching_point_input :
    request { point with scope := middleScope } path = none ∧
    request { point with field := 3 } path = none := by decide

theorem another_mark_does_not_answer_the_request :
    answer point path { field := 1, mark := 11 } = none := by decide

theorem no_parent_links_preserves_the_original_Cg_interest_without_a_root_request :
    collectEffects point [] = {
      originalPointInterest := some { field := 2, mark := 10 },
      boundaryInputInterests := [], addedWriterRegistrations := 0 } := by decide

def secondOuter : RegisteredLink := { outerLink with
  link := { outerLink.link with id := 4, originalField := 3 } }
def secondPath : IdentityPath := .hop innerLink (.hop middleLink (.root secondOuter))

structure Snapshot where
  registeredPaths : List IdentityPath
  queuedPoints : List Point

/-- Input registration precedes actual operation enqueue. Initial-output dedup
does not suppress that point's mark-check request. No seen cache crosses calls. -/
def submitInput (snapshot : Snapshot) (newPath : IdentityPath) (point : Point)
    (_initialWasFresh : Bool) : Snapshot :=
  { registeredPaths := snapshot.registeredPaths ++ [newPath],
    queuedPoints := snapshot.queuedPoints ++ [point] }

def firstSnapshot : Snapshot := { registeredPaths := [path], queuedPoints := [] }

theorem a_late_input_is_registered_before_its_genuine_point_request :
    queries point (submitInput firstSnapshot secondPath point false).registeredPaths = [
      { rootLink := 1, field := 1, mark := 10 }, { rootLink := 4, field := 3, mark := 10 }] := by decide

theorem an_old_initial_does_not_suppress_the_new_point_processing :
    (submitInput firstSnapshot secondPath point false).queuedPoints = [point] := by decide

theorem repeated_paths_need_only_one_existing_original_interest_per_call :
    queries point [path, path] = [{ rootLink := 1, field := 1, mark := 10 }] := by decide

end StaticBoundaryInputRelay

/- Per-module axiom audit; the package checker audits these declarations too. -/
#print axioms StaticBoundaryInputRelay.IdentityPath.scope
#print axioms StaticBoundaryInputRelay.IdentityPath.field
#print axioms StaticBoundaryInputRelay.validPath
#print axioms StaticBoundaryInputRelay.IdentityPath.rootLink
#print axioms StaticBoundaryInputRelay.IdentityPath.replyScopes
#print axioms StaticBoundaryInputRelay.request
#print axioms StaticBoundaryInputRelay.queries
#print axioms StaticBoundaryInputRelay.every_successful_request_names_the_true_original_link
#print axioms StaticBoundaryInputRelay.a_checked_identity_hop_strictly_decreases_scope_depth
#print axioms StaticBoundaryInputRelay.a_checked_identity_chain_preserves_its_actual_image_field
#print axioms StaticBoundaryInputRelay.existingPointInterest
#print axioms StaticBoundaryInputRelay.collectEffects
#print axioms StaticBoundaryInputRelay.the_existing_point_interest_and_writer_directory_are_unchanged
#print axioms StaticBoundaryInputRelay.answer
#print axioms StaticBoundaryInputRelay.a_supply_at_another_field_never_answers_the_original
#print axioms StaticBoundaryInputRelay.applyLeaf
#print axioms StaticBoundaryInputRelay.rootScope
#print axioms StaticBoundaryInputRelay.firstScope
#print axioms StaticBoundaryInputRelay.middleScope
#print axioms StaticBoundaryInputRelay.pointScope
#print axioms StaticBoundaryInputRelay.outerLink
#print axioms StaticBoundaryInputRelay.middleLink
#print axioms StaticBoundaryInputRelay.innerLink
#print axioms StaticBoundaryInputRelay.path
#print axioms StaticBoundaryInputRelay.point
#print axioms StaticBoundaryInputRelay.the_actual_point_requests_only_the_original_root_field
#print axioms StaticBoundaryInputRelay.a_reached_image_group_does_not_answer_the_original_request
#print axioms StaticBoundaryInputRelay.a_genuine_original_supply_keeps_both_original_and_canonical_inner_basis
#print axioms StaticBoundaryInputRelay.the_existing_leaf_relation_composes_back_to_the_true_root_original
#print axioms StaticBoundaryInputRelay.the_outer_field_cannot_be_used_as_the_inner_canonical_initial
#print axioms StaticBoundaryInputRelay.no_actual_mark_request_means_no_relay
#print axioms StaticBoundaryInputRelay.concrete_inputs_and_other_operation_sites_do_not_use_this_relay
#print axioms StaticBoundaryInputRelay.another_scope_or_static_field_is_not_a_matching_point_input
#print axioms StaticBoundaryInputRelay.another_mark_does_not_answer_the_request
#print axioms StaticBoundaryInputRelay.no_parent_links_preserves_the_original_Cg_interest_without_a_root_request
#print axioms StaticBoundaryInputRelay.secondOuter
#print axioms StaticBoundaryInputRelay.secondPath
#print axioms StaticBoundaryInputRelay.submitInput
#print axioms StaticBoundaryInputRelay.firstSnapshot
#print axioms StaticBoundaryInputRelay.a_late_input_is_registered_before_its_genuine_point_request
#print axioms StaticBoundaryInputRelay.an_old_initial_does_not_suppress_the_new_point_processing
#print axioms StaticBoundaryInputRelay.repeated_paths_need_only_one_existing_original_interest_per_call
