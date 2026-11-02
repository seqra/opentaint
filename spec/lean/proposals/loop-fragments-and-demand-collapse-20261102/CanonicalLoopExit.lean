import Std

/-!
Selected single normal-loop-exit interface, with exact physical route labels.

This model separates the shared normal-exit/AL join identity from the actual
physical CFG edge. It proves labelled split/erasure and native/handoff route
refinement. It does not select a Kotlin representation or authorize routing
DATA along a different label. Shared boundary ND false positives are permitted
separately; feedback, exceptions, returns and discovery are not normal leaves.
-/
namespace CanonicalLoopExit
set_option autoImplicit false

inductive Kind where
  | normalLeave | feedback | exceptional | methodReturn | discovery
  deriving DecidableEq, Repr
inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr
inductive JoinKey where
  | normalExit (loop : Nat)
  | physical (port : Nat) (kind : Kind)
  deriving DecidableEq, Repr
structure Route where
  source : Nat
  target : Nat
  port : Nat
  loop : Nat
  kind : Kind
  deriving DecidableEq, Repr

def joinKey (route : Route) : JoinKey :=
  if route.kind = .normalLeave then .normalExit route.loop
  else .physical route.port route.kind

structure StoredRoute where
  join : JoinKey
  physical : Route
  deriving DecidableEq, Repr

def storeRoute (route : Route) : StoredRoute := { join := joinKey route, physical := route }

def directedEdge (direction : Direction) (route : Route) : Nat × Nat :=
  match direction with
  | .forward => (route.source, route.target)
  | .backward => (route.target, route.source)

def refineNative (direction : Direction) (stored : StoredRoute) : Nat × Nat :=
  directedEdge direction stored.physical

def reverseDirection : Direction → Direction
  | .forward => .backward
  | .backward => .forward

structure NativeRow where
  entry : StoredRoute
  exit : StoredRoute
  direction : Direction
  payload : Nat
  deriving DecidableEq, Repr

def reverseRow (row : NativeRow) : NativeRow :=
  { row with entry := row.exit, exit := row.entry, direction := reverseDirection row.direction }

/-- The shared intermediate node retains the exact normal-leave label.
The leave constructor cannot substitute a different physical route. -/
structure NormalSplit (graph : List Route) where
  actual : Route
  present : actual ∈ graph
  normal : actual.kind = .normalLeave

def enterPoint {graph : List Route} (split : NormalSplit graph) : Nat × JoinKey :=
  (split.actual.source, .normalExit split.actual.loop)
def leavePoint {graph : List Route} (split : NormalSplit graph) : JoinKey × Nat :=
  (.normalExit split.actual.loop, split.actual.target)
def eraseSplit {graph : List Route} (split : NormalSplit graph) : Route := split.actual

theorem shared_exit_has_the_original_source_and_target
    {graph : List Route} (split : NormalSplit graph) :
    (enterPoint split).1 = split.actual.source ∧
    (leavePoint split).2 = split.actual.target := ⟨rfl, rfl⟩

theorem split_erasure_constructs_an_existing_physical_edge
    {graph : List Route} (split : NormalSplit graph) : eraseSplit split ∈ graph := split.present

theorem shared_interface_does_not_erase_the_actual_route (route : Route) :
    (storeRoute route).physical = route := rfl

theorem native_refinement_keeps_the_same_forward_CFG_edge (route : Route) :
    refineNative .forward (storeRoute route) = (route.source, route.target) := rfl

theorem native_refinement_keeps_the_same_reverse_CFG_edge (route : Route) :
    refineNative .backward (storeRoute route) = (route.target, route.source) := rfl

theorem reversal_keeps_the_complete_row_payload (row : NativeRow) :
    (reverseRow row).payload = row.payload ∧
    (reverseRow row).entry.physical = row.exit.physical ∧
    (reverseRow row).exit.physical = row.entry.physical := ⟨rfl, rfl, rfl⟩

theorem double_native_or_demand_reversal_restores_the_exact_row (row : NativeRow) :
    reverseRow (reverseRow row) = row := by
  cases row with
  | mk entry exit direction payload => cases direction <;> rfl

def candidates (graph : List Route) (key : JoinKey) : List Route :=
  graph.filter (fun route => joinKey route = key)

/-- A reverse common-entry output can use all original predecessors of its
actual boundary node, not an unrelated destination of another normal leave. -/
def reverseAt (graph : List Route) (key : JoinKey) (actualBoundary : Nat) : List Route :=
  (candidates graph key).filter (fun route => route.target = actualBoundary)

theorem every_reverse_refinement_is_an_existing_edge
    (graph : List Route) (key : JoinKey) (boundary : Nat) (route : Route)
    (selected : route ∈ reverseAt graph key boundary) :
    route ∈ graph ∧ route.target = boundary := by
  have outer := List.mem_filter.mp selected
  have inner := List.mem_filter.mp outer.1
  exact ⟨inner.1, by simpa only [decide_eq_true_eq] using outer.2⟩

theorem every_actual_predecessor_with_the_same_key_is_retained
    (graph : List Route) (route : Route) (present : route ∈ graph) :
    route ∈ reverseAt graph (joinKey route) route.target := by
  apply List.mem_filter.mpr
  constructor
  · exact List.mem_filter.mpr ⟨present, by simp⟩
  · simp

def left : Route := { source := 2, target := 6, port := 20, loop := 1, kind := .normalLeave }
def right : Route := { source := 4, target := 6, port := 40, loop := 1, kind := .normalLeave }
def differentTarget : Route := { right with target := 9, port := 49 }
def feedback : Route := { source := 7, target := 1, port := 71, loop := 1, kind := .feedback }
def exceptional : Route := { source := 8, target := 6, port := 86, loop := 1, kind := .exceptional }
def returned : Route := { source := 9, target := 6, port := 96, loop := 1, kind := .methodReturn }
def discovery : Route := { source := 10, target := 6, port := 106, loop := 1, kind := .discovery }
def exampleGraph : List Route := [left, right, differentTarget, feedback, exceptional, returned, discovery]

theorem normal_leave_paths_have_one_shared_join_identity :
    joinKey left = joinKey right ∧ joinKey right = joinKey differentTarget := by decide

theorem actual_forward_destinations_remain_distinct_after_normalization :
    refineNative .forward (storeRoute left) = (2, 6) ∧
    refineNative .forward (storeRoute differentTarget) = (4, 9) := by decide

theorem the_reverse_shared_boundary_retains_both_real_normal_predecessors :
    reverseAt exampleGraph (.normalExit 1) 6 = [left, right] := by decide

theorem a_different_continuation_does_not_join_that_reverse_route :
    differentTarget ∉ reverseAt exampleGraph (.normalExit 1) 6 := by decide

theorem feedback_exception_return_and_discovery_remain_separate :
    joinKey feedback ≠ .normalExit 1 ∧ joinKey exceptional ≠ .normalExit 1 ∧
    joinKey returned ≠ .normalExit 1 ∧ joinKey discovery ≠ .normalExit 1 := by decide

theorem reversing_a_stored_normal_entry_keeps_its_physical_exit_refinement :
    let row : NativeRow := {
      entry := storeRoute right, exit := storeRoute left, direction := .forward, payload := 37 }
    refineNative (reverseRow row).direction (reverseRow row).exit = (6, 4) ∧
    (reverseRow row).payload = 37 := by decide

/-! Structural normal-leave-tail extension. The original SCC headers and
feedback edges stay fixed. A finite checker rejects an extension with another
normal exit or an additional cycle after the existing feedback cuts. -/

structure ExtensionPlan where
  graph : List Route
  core : List Nat
  tails : List Nat
  headers : List Nat
  normalExits : List Nat
  join : Nat
  rank : Nat → Nat

def body (plan : ExtensionPlan) : List Nat := (plan.core ++ plan.tails).eraseDups
def inside (plan : ExtensionPlan) (node : Nat) : Bool := (body plan).contains node
def normalOutlet (plan : ExtensionPlan) (route : Route) : Bool :=
  inside plan route.source && !(inside plan route.target) && decide (route.kind = .normalLeave)
def internalNonFeedback (plan : ExtensionPlan) (route : Route) : Bool :=
  inside plan route.source && inside plan route.target && decide (route.kind ≠ .feedback)
def outletCheck (plan : ExtensionPlan) : Bool :=
  (plan.graph.filter (normalOutlet plan)).all (fun route => decide (route.target = plan.join))
def rankCheck (plan : ExtensionPlan) : Bool :=
  (plan.graph.filter (internalNonFeedback plan)).all (fun route => decide (plan.rank route.source < plan.rank route.target))

def advanceBeforeJoin (graph : List Route) (join : Nat) (seen : List Nat) : List Nat :=
  (seen ++ (graph.filter (fun route => seen.contains route.source &&
    decide (route.kind = .normalLeave) && decide (route.target ≠ join))).map Route.target).eraseDups
def closeBeforeJoin (graph : List Route) (join : Nat) : Nat → List Nat → List Nat
  | 0, seen => seen
  | n + 1, seen => closeBeforeJoin graph join n (advanceBeforeJoin graph join seen)
def computedTails (plan : ExtensionPlan) : List Nat :=
  let vertices := (plan.graph.flatMap (fun route => [route.source, route.target]) ++ plan.core).eraseDups
  (closeBeforeJoin plan.graph plan.join (vertices.length + 1) plan.core).filter
    (fun node => !(plan.core.contains node))
def sameNodes (first second : List Nat) : Bool :=
  first.all second.contains && second.all first.contains

def validExtension (plan : ExtensionPlan) : Bool :=
  plan.tails.all (fun node => !(plan.core.contains node)) &&
  plan.headers.all plan.core.contains &&
  !(inside plan plan.join) &&
  (body plan).all (fun node => !(plan.normalExits.contains node)) &&
  sameNodes plan.tails (computedTails plan) && outletCheck plan && rankCheck plan &&
  decide (body plan).Nodup

structure CertifiedExtension where
  plan : ExtensionPlan
  checked : validExtension plan = true

def certify (plan : ExtensionPlan) : Option CertifiedExtension :=
  if checked : validExtension plan = true then some ⟨plan, checked⟩ else none

structure Expanded where
  graph : List Route
  loopInstructions : List Nat
  headers : List Nat
  feedback : List Route
  join : Nat
  deriving DecidableEq, Repr

def expand (certificate : CertifiedExtension) : Expanded := {
  graph := certificate.plan.graph
  loopInstructions := body certificate.plan
  headers := certificate.plan.headers
  feedback := certificate.plan.graph.filter (fun route => route.kind = .feedback)
  join := certificate.plan.join }

theorem extension_keeps_the_original_graph_headers_and_feedback
    (certificate : CertifiedExtension) :
    (expand certificate).graph = certificate.plan.graph ∧
    (expand certificate).headers = certificate.plan.headers ∧
    (expand certificate).feedback = certificate.plan.graph.filter (fun route => route.kind = .feedback) :=
  ⟨rfl, rfl, rfl⟩

theorem every_checked_normal_outlet_reaches_the_real_common_join
    (certificate : CertifiedExtension) (route : Route)
    (present : route ∈ certificate.plan.graph)
    (leaves : normalOutlet certificate.plan route = true) :
    route.target = certificate.plan.join := by
  have fields := certificate.checked
  simp only [validExtension, Bool.and_eq_true, and_assoc] at fields
  have outlets := fields.2.2.2.2.2.1
  have member : route ∈ certificate.plan.graph.filter (normalOutlet certificate.plan) :=
    List.mem_filter.mpr ⟨present, leaves⟩
  have target := List.all_eq_true.mp outlets route member
  simpa only [decide_eq_true_eq] using target

theorem every_checked_internal_nonfeedback_edge_increases_rank
    (certificate : CertifiedExtension) (route : Route)
    (present : route ∈ certificate.plan.graph)
    (internalEdge : internalNonFeedback certificate.plan route = true) :
    certificate.plan.rank route.source < certificate.plan.rank route.target := by
  have fields := certificate.checked
  simp only [validExtension, Bool.and_eq_true, and_assoc] at fields
  have ranks := fields.2.2.2.2.2.2.1
  have member : route ∈ certificate.plan.graph.filter (internalNonFeedback certificate.plan) :=
    List.mem_filter.mpr ⟨present, internalEdge⟩
  have increase := List.all_eq_true.mp ranks route member
  simpa only [decide_eq_true_eq] using increase

def oldFeedback (plan : ExtensionPlan) : List Route :=
  plan.graph.filter (fun route => route.kind = .feedback)

theorem a_typed_exception_return_or_discovery_route_keeps_its_exact_identity
    (certificate : CertifiedExtension) (route : Route)
    (present : route ∈ certificate.plan.graph) : route ∈ (expand certificate).graph := present

def edge (source target port : Nat) (kind : Kind := .normalLeave) : Route :=
  { source, target, port, loop := 1, kind }
def branchGraph : List Route := [
  edge 0 1 1, edge 1 2 12, edge 1 4 14, edge 1 7 17,
  edge 2 3 23, edge 3 6 36, edge 4 5 45, edge 5 6 56, edge 7 1 71 .feedback]
def branchRank : Nat → Nat
  | 1 => 0
  | 2 | 4 | 7 => 1
  | 3 | 5 => 2
  | _ => 3
def branchPlan (join : Nat := 6) : ExtensionPlan := {
  graph := branchGraph, core := [1, 7], tails := [2, 3, 4, 5], headers := [1],
  normalExits := [6], join, rank := branchRank }
def branchCertificate : CertifiedExtension := ⟨branchPlan, by decide⟩

theorem branch_tail_extension_is_executable_and_certified :
    validExtension branchPlan = true ∧ sameNodes (computedTails branchPlan) [2, 3, 4, 5] = true := by decide

theorem all_branch_operations_belong_to_L_and_the_join_belongs_to_AL :
    (expand branchCertificate).loopInstructions = [1, 7, 2, 3, 4, 5] ∧
    !(inside branchPlan 6) = true := by decide

theorem the_branch_extension_keeps_the_original_header_and_only_feedback_edge :
    (expand branchCertificate).headers = [1] ∧
    (expand branchCertificate).feedback = [edge 7 1 71 .feedback] := by decide

theorem extended_normal_outlets_have_one_actual_AL_target :
    branchGraph.filter (normalOutlet branchPlan) = [edge 3 6 36, edge 5 6 56] := by decide

theorem reverse_shared_exit_refines_to_both_exact_original_tail_edges :
    reverseAt (branchGraph.filter (normalOutlet branchPlan)) (.normalExit 1) 6 =
      [edge 3 6 36, edge 5 6 56] := by decide

theorem an_alternative_normal_exit_cannot_be_absorbed_as_an_acyclic_tail :
    validExtension { branchPlan with normalExits := [3, 6] } = false := by decide

theorem a_new_nonfeedback_cycle_cannot_pass_the_extension_certificate :
    validExtension { branchPlan with graph := branchGraph ++ [edge 5 4 54] } = false := by decide

theorem the_original_SCC_alone_does_not_yet_have_a_single_normal_exit :
    outletCheck { branchPlan with tails := [] } = false := by decide

theorem expanded_loop_instruction_membership_has_no_duplicates
    (certificate : CertifiedExtension) : (expand certificate).loopInstructions.Nodup := by
  have fields := certificate.checked
  simp only [validExtension, Bool.and_eq_true, and_assoc] at fields
  simpa only [expand, decide_eq_true_eq] using fields.2.2.2.2.2.2.2

inductive CutPath (certificate : CertifiedExtension) : Nat → Nat → Type where
  | edge (route : Route) (present : route ∈ certificate.plan.graph)
      (internalEdge : internalNonFeedback certificate.plan route = true) :
      CutPath certificate route.source route.target
  | cons (route : Route) (present : route ∈ certificate.plan.graph)
      (internalEdge : internalNonFeedback certificate.plan route = true)
      (finish : Nat) (rest : CutPath certificate route.target finish) :
      CutPath certificate route.source finish

theorem every_nonempty_cut_body_path_strictly_increases_rank
    {certificate : CertifiedExtension} {start finish : Nat}
    (path : CutPath certificate start finish) :
    certificate.plan.rank start < certificate.plan.rank finish := by
  induction path with
  | edge route present internalEdge =>
      exact every_checked_internal_nonfeedback_edge_increases_rank certificate route present internalEdge
  | cons route present internalEdge finish rest increase =>
      exact Nat.lt_trans
        (every_checked_internal_nonfeedback_edge_increases_rank certificate route present internalEdge) increase

theorem a_checked_extension_has_no_new_cycle_after_the_original_feedback_cuts
    {certificate : CertifiedExtension} {node : Nat} (cycle : CutPath certificate node node) : False :=
  Nat.lt_irrefl _ (every_nonempty_cut_body_path_strictly_increases_rank cycle)

def noLeavePlan : ExtensionPlan := {
  graph := [edge 1 7 17, edge 7 1 71 .feedback], core := [1, 7], tails := [],
  headers := [1], normalExits := [6], join := 6, rank := branchRank }

theorem a_nonreturning_loop_needs_no_new_normal_exit_edge :
    validExtension noLeavePlan = true ∧
    noLeavePlan.graph.filter (normalOutlet noLeavePlan) = [] := by decide

def twoExitGraph : List Route := [
  edge 1 2 12, edge 1 4 14, edge 1 7 17, edge 2 3 23,
  edge 3 6 36, edge 4 5 45, edge 5 9 59, edge 7 1 71 .feedback]

theorem two_unmerged_normal_exits_fail_the_common_join_certificate :
    validExtension { branchPlan with graph := twoExitGraph, tails := [2, 3, 4, 5, 9], normalExits := [6, 9] } = false ∧
    validExtension { branchPlan 9 with graph := twoExitGraph, tails := [2, 3, 4, 5, 6], normalExits := [6, 9] } = false := by decide

/-! A normal leave is relative to the current loop. An edge can leave the inner
loop normally and remain the original outer loop's feedback edge. The actual
route label must survive the inner interface and be restored at the outer one. -/

def relativeNormal (currentLoop : Nat) (route : Route) : Bool :=
  decide (route.kind = .normalLeave ∨ route.kind = .feedback ∧ route.loop ≠ currentLoop)

/-- Classification view only. Actual stored routes and the original graph are
never replaced by this temporary view. -/
def classifyFor (currentLoop : Nat) (route : Route) : Route :=
  if route.kind = .feedback ∧ route.loop ≠ currentLoop then { route with kind := .normalLeave }
  else route

def storeAtLoop (currentLoop : Nat) (route : Route) : StoredRoute :=
  { join := if relativeNormal currentLoop route then .normalExit currentLoop
      else .physical route.port route.kind,
    physical := route }

theorem relative_classification_keeps_both_endpoints_port_and_original_owner
    (currentLoop : Nat) (route : Route) :
    (classifyFor currentLoop route).source = route.source ∧
    (classifyFor currentLoop route).target = route.target ∧
    (classifyFor currentLoop route).port = route.port ∧
    (classifyFor currentLoop route).loop = route.loop := by
  unfold classifyFor
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem stored_inner_control_keeps_the_exact_original_physical_route
    (currentLoop : Nat) (route : Route) : (storeAtLoop currentLoop route).physical = route := rfl

structure ContextPlan where
  currentLoop : Nat
  region : List Nat
  original : ExtensionPlan

def contextView (plan : ContextPlan) : ExtensionPlan :=
  { plan.original with graph := plan.original.graph.map (classifyFor plan.currentLoop) }
def validContext (plan : ContextPlan) : Bool :=
  validExtension (contextView plan) && (body plan.original).all plan.region.contains
structure ContextCertificate where
  plan : ContextPlan
  checked : validContext plan = true
def checkedView (certificate : ContextCertificate) : CertifiedExtension :=
  { plan := contextView certificate.plan,
    checked := by
      have fields := certificate.checked
      simp only [validContext, Bool.and_eq_true] at fields
      exact fields.1 }

def contextAL (plan : ContextPlan) : List Nat :=
  plan.region.filter (fun node => !(inside plan.original node))
def physicalContextGraph (certificate : ContextCertificate) : List Route := certificate.plan.original.graph
def ownContextFeedback (certificate : ContextCertificate) : List Route :=
  certificate.plan.original.graph.filter (fun route =>
    decide (route.kind = .feedback ∧ route.loop = certificate.plan.currentLoop))

theorem a_context_extension_keeps_the_complete_original_graph
    (certificate : ContextCertificate) : physicalContextGraph certificate = certificate.plan.original.graph := rfl

theorem every_context_normal_outlet_reaches_its_real_join
    (certificate : ContextCertificate) (route : Route)
    (present : route ∈ (contextView certificate.plan).graph)
    (leaves : normalOutlet (contextView certificate.plan) route = true) :
    route.target = certificate.plan.original.join :=
  every_checked_normal_outlet_reaches_the_real_common_join (checkedView certificate) route present leaves

def outerContinue4 : Route := { source := 4, target := 1, port := 41, loop := 1, kind := .feedback }
def outerContinue5 : Route := { source := 5, target := 1, port := 51, loop := 1, kind := .feedback }
def outerContinue6 : Route := { source := 6, target := 1, port := 61, loop := 1, kind := .feedback }
def ownInnerRepeat : Route := { source := 3, target := 2, port := 32, loop := 2, kind := .feedback }
def innerEdge (source target port : Nat) : Route := { edge source target port with loop := 2 }
def outerContinueGraph : List Route := [
  innerEdge 2 3 23, ownInnerRepeat, innerEdge 2 4 24, innerEdge 2 5 25, innerEdge 2 6 26,
  outerContinue4, outerContinue5, outerContinue6]
def outerContinueRank : Nat → Nat
  | 2 => 0
  | 3 | 4 | 5 | 6 => 1
  | _ => 2
def outerContinuePlan : ContextPlan := {
  currentLoop := 2, region := [2, 3, 4, 5, 6], original := {
    graph := outerContinueGraph, core := [2, 3], tails := [4, 5, 6], headers := [2],
    normalExits := [10], join := 1, rank := outerContinueRank } }
def outerContinueCertificate : ContextCertificate := ⟨outerContinuePlan, by decide⟩

theorem a_real_enclosing_header_can_be_the_inner_normal_join_outside_its_region :
    validContext outerContinuePlan = true ∧
    !(outerContinuePlan.region.contains 1) = true ∧
    contextAL outerContinuePlan = [] := by decide

theorem inner_normal_tail_extension_preserves_the_inner_header_and_own_repeat :
    (expand (checkedView outerContinueCertificate)).headers = [2] ∧
    ownContextFeedback outerContinueCertificate = [ownInnerRepeat] := by decide

theorem the_same_actual_edge_is_inner_normal_and_outer_feedback :
    (storeAtLoop 2 outerContinue4).join = .normalExit 2 ∧
    (storeAtLoop 1 outerContinue4).join = .physical 41 .feedback ∧
    (storeAtLoop 2 outerContinue4).physical = outerContinue4 := by decide

theorem an_inner_native_reverse_still_refines_the_original_outer_feedback_edge :
    refineNative .backward (storeAtLoop 2 outerContinue5) = (1, 5) ∧
    (storeAtLoop 2 outerContinue5).physical.kind = .feedback ∧
    (storeAtLoop 2 outerContinue5).physical.loop = 1 := by decide

theorem own_feedback_exceptions_returns_and_discovery_are_not_inner_normal_leaves :
    relativeNormal 2 ownInnerRepeat = false ∧ relativeNormal 2 exceptional = false ∧
    relativeNormal 2 returned = false ∧ relativeNormal 2 discovery = false := by decide

end CanonicalLoopExit

/- Per-module axiom audit; the package checker audits these declarations too. -/
#print axioms CanonicalLoopExit.joinKey
#print axioms CanonicalLoopExit.storeRoute
#print axioms CanonicalLoopExit.directedEdge
#print axioms CanonicalLoopExit.refineNative
#print axioms CanonicalLoopExit.reverseDirection
#print axioms CanonicalLoopExit.reverseRow
#print axioms CanonicalLoopExit.enterPoint
#print axioms CanonicalLoopExit.leavePoint
#print axioms CanonicalLoopExit.eraseSplit
#print axioms CanonicalLoopExit.shared_exit_has_the_original_source_and_target
#print axioms CanonicalLoopExit.split_erasure_constructs_an_existing_physical_edge
#print axioms CanonicalLoopExit.shared_interface_does_not_erase_the_actual_route
#print axioms CanonicalLoopExit.native_refinement_keeps_the_same_forward_CFG_edge
#print axioms CanonicalLoopExit.native_refinement_keeps_the_same_reverse_CFG_edge
#print axioms CanonicalLoopExit.reversal_keeps_the_complete_row_payload
#print axioms CanonicalLoopExit.double_native_or_demand_reversal_restores_the_exact_row
#print axioms CanonicalLoopExit.candidates
#print axioms CanonicalLoopExit.reverseAt
#print axioms CanonicalLoopExit.every_reverse_refinement_is_an_existing_edge
#print axioms CanonicalLoopExit.every_actual_predecessor_with_the_same_key_is_retained
#print axioms CanonicalLoopExit.left
#print axioms CanonicalLoopExit.right
#print axioms CanonicalLoopExit.differentTarget
#print axioms CanonicalLoopExit.feedback
#print axioms CanonicalLoopExit.exceptional
#print axioms CanonicalLoopExit.returned
#print axioms CanonicalLoopExit.discovery
#print axioms CanonicalLoopExit.exampleGraph
#print axioms CanonicalLoopExit.normal_leave_paths_have_one_shared_join_identity
#print axioms CanonicalLoopExit.actual_forward_destinations_remain_distinct_after_normalization
#print axioms CanonicalLoopExit.the_reverse_shared_boundary_retains_both_real_normal_predecessors
#print axioms CanonicalLoopExit.a_different_continuation_does_not_join_that_reverse_route
#print axioms CanonicalLoopExit.feedback_exception_return_and_discovery_remain_separate
#print axioms CanonicalLoopExit.reversing_a_stored_normal_entry_keeps_its_physical_exit_refinement
#print axioms CanonicalLoopExit.body
#print axioms CanonicalLoopExit.inside
#print axioms CanonicalLoopExit.normalOutlet
#print axioms CanonicalLoopExit.internalNonFeedback
#print axioms CanonicalLoopExit.outletCheck
#print axioms CanonicalLoopExit.rankCheck
#print axioms CanonicalLoopExit.advanceBeforeJoin
#print axioms CanonicalLoopExit.closeBeforeJoin
#print axioms CanonicalLoopExit.computedTails
#print axioms CanonicalLoopExit.sameNodes
#print axioms CanonicalLoopExit.validExtension
#print axioms CanonicalLoopExit.certify
#print axioms CanonicalLoopExit.expand
#print axioms CanonicalLoopExit.extension_keeps_the_original_graph_headers_and_feedback
#print axioms CanonicalLoopExit.every_checked_normal_outlet_reaches_the_real_common_join
#print axioms CanonicalLoopExit.every_checked_internal_nonfeedback_edge_increases_rank
#print axioms CanonicalLoopExit.oldFeedback
#print axioms CanonicalLoopExit.a_typed_exception_return_or_discovery_route_keeps_its_exact_identity
#print axioms CanonicalLoopExit.edge
#print axioms CanonicalLoopExit.branchGraph
#print axioms CanonicalLoopExit.branchRank
#print axioms CanonicalLoopExit.branchPlan
#print axioms CanonicalLoopExit.branchCertificate
#print axioms CanonicalLoopExit.branch_tail_extension_is_executable_and_certified
#print axioms CanonicalLoopExit.all_branch_operations_belong_to_L_and_the_join_belongs_to_AL
#print axioms CanonicalLoopExit.the_branch_extension_keeps_the_original_header_and_only_feedback_edge
#print axioms CanonicalLoopExit.extended_normal_outlets_have_one_actual_AL_target
#print axioms CanonicalLoopExit.reverse_shared_exit_refines_to_both_exact_original_tail_edges
#print axioms CanonicalLoopExit.an_alternative_normal_exit_cannot_be_absorbed_as_an_acyclic_tail
#print axioms CanonicalLoopExit.a_new_nonfeedback_cycle_cannot_pass_the_extension_certificate
#print axioms CanonicalLoopExit.the_original_SCC_alone_does_not_yet_have_a_single_normal_exit
#print axioms CanonicalLoopExit.expanded_loop_instruction_membership_has_no_duplicates
#print axioms CanonicalLoopExit.every_nonempty_cut_body_path_strictly_increases_rank
#print axioms CanonicalLoopExit.a_checked_extension_has_no_new_cycle_after_the_original_feedback_cuts
#print axioms CanonicalLoopExit.noLeavePlan
#print axioms CanonicalLoopExit.a_nonreturning_loop_needs_no_new_normal_exit_edge
#print axioms CanonicalLoopExit.twoExitGraph
#print axioms CanonicalLoopExit.two_unmerged_normal_exits_fail_the_common_join_certificate
#print axioms CanonicalLoopExit.relativeNormal
#print axioms CanonicalLoopExit.classifyFor
#print axioms CanonicalLoopExit.storeAtLoop
#print axioms CanonicalLoopExit.relative_classification_keeps_both_endpoints_port_and_original_owner
#print axioms CanonicalLoopExit.stored_inner_control_keeps_the_exact_original_physical_route
#print axioms CanonicalLoopExit.contextView
#print axioms CanonicalLoopExit.validContext
#print axioms CanonicalLoopExit.checkedView
#print axioms CanonicalLoopExit.contextAL
#print axioms CanonicalLoopExit.physicalContextGraph
#print axioms CanonicalLoopExit.ownContextFeedback
#print axioms CanonicalLoopExit.a_context_extension_keeps_the_complete_original_graph
#print axioms CanonicalLoopExit.every_context_normal_outlet_reaches_its_real_join
#print axioms CanonicalLoopExit.outerContinue4
#print axioms CanonicalLoopExit.outerContinue5
#print axioms CanonicalLoopExit.outerContinue6
#print axioms CanonicalLoopExit.ownInnerRepeat
#print axioms CanonicalLoopExit.innerEdge
#print axioms CanonicalLoopExit.outerContinueGraph
#print axioms CanonicalLoopExit.outerContinueRank
#print axioms CanonicalLoopExit.outerContinuePlan
#print axioms CanonicalLoopExit.outerContinueCertificate
#print axioms CanonicalLoopExit.a_real_enclosing_header_can_be_the_inner_normal_join_outside_its_region
#print axioms CanonicalLoopExit.inner_normal_tail_extension_preserves_the_inner_header_and_own_repeat
#print axioms CanonicalLoopExit.the_same_actual_edge_is_inner_normal_and_outer_feedback
#print axioms CanonicalLoopExit.an_inner_native_reverse_still_refines_the_original_outer_feedback_edge
#print axioms CanonicalLoopExit.own_feedback_exceptions_returns_and_discovery_are_not_inner_normal_leaves
