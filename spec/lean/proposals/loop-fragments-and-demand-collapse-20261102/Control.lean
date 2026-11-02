import Std

/-!
Exact control factorization for a supplied finite CFG partition.

The source graph, node partition, feedback cuts and exit classification are
executable inputs. A boundary edge crosses owners or has an explicit feedback
cut, including a same-owner self-loop. It keeps its source, destination and exit
kind as its port key.
Synthetic routing emits no physical-operation ID. Each original operation keeps
the same ID and position in the trace. The reverse lane reverses these same
labelled transitions; it does not classify a return as ordinary fallthrough.

This file does not construct a JVM extraction pass. It does not prove alias,
fact-transfer, demand-cap, ND, rule-binding, or new summary-boundary semantics.
In particular, exact factorization alone does not cut a cyclic transfer fixed
point or establish a speedup. Those are separate obligations.
-/
namespace LoopFragments
set_option autoImplicit false

inductive ExitKind where
  | ordinary
  | nextIteration
  | breakLoop
  | methodReturn
  | handler
  | methodThrow
  deriving DecidableEq, Repr

structure ControlGraph (nodes regions : Nat) where
  edge : Fin nodes → Fin nodes → Bool
  owner : Fin nodes → Fin regions
  feedback : Fin nodes → Fin nodes → Bool
  exitKind : Fin nodes → Fin nodes → ExitKind

structure Port (nodes : Nat) where
  source : Fin nodes
  target : Fin nodes
  kind : ExitKind
  deriving DecidableEq, Repr

inductive ControlState (nodes : Nat) where
  | physical (node : Fin nodes)
  | leaving (port : Port nodes)
  | entering (port : Port nodes)
  deriving DecidableEq, Repr

variable {nodes regions : Nat}

def ControlGraph.port (graph : ControlGraph nodes regions)
    (source target : Fin nodes) : Port nodes :=
  ⟨source, target, graph.exitKind source target⟩

def ControlGraph.boundary (graph : ControlGraph nodes regions)
    (source target : Fin nodes) : Bool :=
  decide (graph.owner source ≠ graph.owner target) || graph.feedback source target

theorem boundary_iff_owner_change_or_feedback (graph : ControlGraph nodes regions)
    (source target : Fin nodes) :
    graph.boundary source target = true ↔
      graph.owner source ≠ graph.owner target ∨ graph.feedback source target = true := by
  simp [ControlGraph.boundary, Bool.or_eq_true]

theorem internal_iff_same_owner_without_feedback (graph : ControlGraph nodes regions)
    (source target : Fin nodes) :
    graph.boundary source target = false ↔
      graph.owner source = graph.owner target ∧ graph.feedback source target = false := by
  simp [ControlGraph.boundary, Bool.or_eq_false_iff]

def ValidPort (graph : ControlGraph nodes regions) (port : Port nodes) : Prop :=
  graph.edge port.source port.target = true ∧
  graph.boundary port.source port.target = true ∧
  port.kind = graph.exitKind port.source port.target

def emitSite (site : Option (Fin nodes)) : List (Fin nodes) := site.toList

/-- A transition executes at most one original physical operation. -/
inductive SourceStep (graph : ControlGraph nodes regions) :
    Fin nodes → Option (Fin nodes) → Fin nodes → Prop where
  | edge {source target : Fin nodes} (present : graph.edge source target = true) :
      SourceStep graph source (some source) target

inductive FragmentStep (graph : ControlGraph nodes regions) :
    ControlState nodes → Option (Fin nodes) → ControlState nodes → Prop where
  | internal {source target : Fin nodes}
      (present : graph.edge source target = true)
      (uncut : graph.boundary source target = false) :
      FragmentStep graph (.physical source) (some source) (.physical target)
  | leave {source target : Fin nodes}
      (present : graph.edge source target = true)
      (cut : graph.boundary source target = true) :
      FragmentStep graph (.physical source) (some source)
        (.leaving (graph.port source target))
  | dispatch {port : Port nodes} (valid : ValidPort graph port) :
      FragmentStep graph (.leaving port) none (.entering port)
  | enter {port : Port nodes} (valid : ValidPort graph port) :
      FragmentStep graph (.entering port) none (.physical port.target)

/-- Inductive path evidence contains its executable finite transition sequence. -/
inductive Walk {State Label : Type}
    (step : State → Option Label → State → Prop) :
    State → List Label → State → Prop where
  | nil (state : State) : Walk step state [] state
  | cons {source middle target : State} {site : Option Label} {rest : List Label}
      (first : step source site middle) (tail : Walk step middle rest target) :
      Walk step source (site.toList ++ rest) target

theorem walk_append {State Label : Type}
    {step : State → Option Label → State → Prop}
    {source middle target : State} {first second : List Label}
    (left : Walk step source first middle) (right : Walk step middle second target) :
    Walk step source (first ++ second) target := by
  induction left with
  | nil => simpa using right
  | cons head tail ih =>
      simpa only [List.append_assoc] using Walk.cons head (ih right)

theorem walk_single {State Label : Type}
    {step : State → Option Label → State → Prop}
    {source target : State} {site : Option Label} (edge : step source site target) :
    Walk step source site.toList target := by
  simpa using Walk.cons edge (Walk.nil target)

def backward {State Label : Type} (step : State → Option Label → State → Prop)
    (source : State) (site : Option Label) (target : State) : Prop :=
  step target site source

theorem walk_reverse {State Label : Type}
    {step : State → Option Label → State → Prop}
    {source target : State} {trace : List Label}
    (path : Walk step source trace target) :
    Walk (backward step) target trace.reverse source := by
  induction path with
  | nil state => exact Walk.nil state
  | @cons source middle target site rest head tail ih =>
      have one : Walk (backward step) middle site.toList source :=
        walk_single head
      have result := walk_append ih one
      cases site <;> simpa using result

/-- Only uncut edges inside one selected body belong to its local CFG. -/
inductive BodyInternalStep (graph : ControlGraph nodes regions) (body : Fin regions) :
    Fin nodes → Option (Fin nodes) → Fin nodes → Prop where
  | edge {source target : Fin nodes}
      (inBody : graph.owner source = body)
      (present : graph.edge source target = true)
      (uncut : graph.boundary source target = false) :
      BodyInternalStep graph body source (some source) target

/-- An extractor must provide this certificate for each helper body. -/
structure BodyAcyclicCertificate (graph : ControlGraph nodes regions) (body : Fin regions) where
  rank : Fin nodes → Nat
  increases : ∀ (source target : Fin nodes), graph.owner source = body →
    graph.edge source target = true → graph.boundary source target = false →
    rank source < rank target

theorem body_internal_path_rank_nondecreasing (graph : ControlGraph nodes regions)
    (body : Fin regions) (certificate : BodyAcyclicCertificate graph body)
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (BodyInternalStep graph body) source trace target) :
    certificate.rank source ≤ certificate.rank target := by
  induction path with
  | nil node => exact Nat.le_refl _
  | cons first tail ih =>
      cases first with
      | edge inBody present uncut =>
          exact Nat.le_trans (Nat.le_of_lt (certificate.increases _ _ inBody present uncut)) ih

theorem positive_body_internal_path_rank_increases (graph : ControlGraph nodes regions)
    (body : Fin regions) (certificate : BodyAcyclicCertificate graph body)
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (BodyInternalStep graph body) source trace target) (positive : trace ≠ []) :
    certificate.rank source < certificate.rank target := by
  cases path with
  | nil node => exact False.elim (positive rfl)
  | cons first tail =>
      cases first with
      | edge inBody present uncut =>
          exact Nat.lt_of_lt_of_le (certificate.increases _ _ inBody present uncut)
            (body_internal_path_rank_nondecreasing graph body certificate tail)

theorem no_positive_closed_internal_body_path (graph : ControlGraph nodes regions)
    (body : Fin regions) (certificate : BodyAcyclicCertificate graph body)
    (node : Fin nodes) (trace : List (Fin nodes))
    (positive : trace ≠ []) : ¬ Walk (BodyInternalStep graph body) node trace node := by
  intro path
  exact Nat.lt_irrefl _ (positive_body_internal_path_rank_increases
    graph body certificate path positive)

theorem internal_body_step_preserves_its_owner (graph : ControlGraph nodes regions)
    (body : Fin regions) {source target : Fin nodes} {site : Option (Fin nodes)}
    (step : BodyInternalStep graph body source site target) : graph.owner target = body := by
  cases step with
  | edge inBody present uncut =>
      exact ((internal_iff_same_owner_without_feedback graph _ _).mp uncut).1.symm.trans inBody

def sourceAnchor : ControlState nodes → Fin nodes
  | .physical node => node
  | .leaving port => port.target
  | .entering port => port.target

theorem canonical_port_valid (graph : ControlGraph nodes regions)
    (source target : Fin nodes)
    (edge : graph.edge source target = true)
    (cut : graph.boundary source target = true) :
    ValidPort graph (graph.port source target) :=
  ⟨edge, cut, rfl⟩

/-- Port enumeration is a pure, total function of an original edge and partition. -/
def routeVertices (graph : ControlGraph nodes regions)
    (source target : Fin nodes) : List (ControlState nodes) :=
  if graph.boundary source target then
    [.physical source, .leaving (graph.port source target),
     .entering (graph.port source target), .physical target]
  else [.physical source, .physical target]

theorem route_internal (graph : ControlGraph nodes regions) (source target : Fin nodes)
    (uncut : graph.boundary source target = false) :
    routeVertices graph source target = [.physical source, .physical target] := by
  simp [routeVertices, uncut]

theorem route_crossing (graph : ControlGraph nodes regions) (source target : Fin nodes)
    (cut : graph.boundary source target = true) :
    routeVertices graph source target =
      [.physical source, .leaving (graph.port source target),
       .entering (graph.port source target), .physical target] := by
  simp [routeVertices, cut]

theorem source_edge_lifts (graph : ControlGraph nodes regions) (source target : Fin nodes)
    (edge : graph.edge source target = true) :
    Walk (FragmentStep graph) (.physical source) [source] (.physical target) := by
  cases split : graph.boundary source target with
  | false => exact walk_single (FragmentStep.internal edge split)
  | true =>
    have valid := canonical_port_valid graph source target edge split
    exact Walk.cons (FragmentStep.leave edge split)
      (Walk.cons (FragmentStep.dispatch valid)
        (Walk.cons (FragmentStep.enter valid) (Walk.nil (ControlState.physical target))))

theorem source_path_lifts (graph : ControlGraph nodes regions)
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (SourceStep graph) source trace target) :
    Walk (FragmentStep graph) (.physical source) trace (.physical target) := by
  induction path with
  | nil node => exact Walk.nil (ControlState.physical node)
  | cons first tail ih =>
      cases first with
      | edge present => exact walk_append (source_edge_lifts graph _ _ present) ih

theorem fragment_path_erases (graph : ControlGraph nodes regions)
    {source target : ControlState nodes} {trace : List (Fin nodes)}
    (path : Walk (FragmentStep graph) source trace target) :
    Walk (SourceStep graph) (sourceAnchor source) trace (sourceAnchor target) := by
  induction path with
  | nil state => exact Walk.nil (sourceAnchor state)
  | cons first tail ih =>
      cases first with
      | internal present same => exact Walk.cons (SourceStep.edge present) ih
      | leave present different => exact Walk.cons (SourceStep.edge present) ih
      | dispatch valid => exact ih
      | enter valid => exact ih

theorem exact_forward_trace_correspondence (graph : ControlGraph nodes regions)
    (source target : Fin nodes) (trace : List (Fin nodes)) :
    Walk (SourceStep graph) source trace target ↔
      Walk (FragmentStep graph) (.physical source) trace (.physical target) :=
  ⟨source_path_lifts graph, fragment_path_erases graph⟩

theorem source_reverse_path_lifts (graph : ControlGraph nodes regions)
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (backward (SourceStep graph)) source trace target) :
    Walk (backward (FragmentStep graph)) (.physical source) trace (.physical target) := by
  have original := walk_reverse path
  have plain : Walk (SourceStep graph) target trace.reverse source := original
  have lifted := walk_reverse (source_path_lifts graph plain)
  simpa using lifted

theorem fragment_reverse_path_erases (graph : ControlGraph nodes regions)
    {source target : ControlState nodes} {trace : List (Fin nodes)}
    (path : Walk (backward (FragmentStep graph)) source trace target) :
    Walk (backward (SourceStep graph)) (sourceAnchor source) trace (sourceAnchor target) := by
  have original := walk_reverse path
  have plain : Walk (FragmentStep graph) target trace.reverse source := original
  have erased := walk_reverse (fragment_path_erases graph plain)
  simpa using erased

theorem exact_backward_trace_correspondence (graph : ControlGraph nodes regions)
    (source target : Fin nodes) (trace : List (Fin nodes)) :
    Walk (backward (SourceStep graph)) source trace target ↔
      Walk (backward (FragmentStep graph)) (.physical source) trace (.physical target) :=
  ⟨source_reverse_path_lifts graph, fragment_reverse_path_erases graph⟩

/-- Use this contract at every recursive extraction level; no extractor is assumed. -/
structure ExactFactorization {Original Routed Label : Type}
    (original : Original → Option Label → Original → Prop)
    (routed : Routed → Option Label → Routed → Prop) where
  embed : Original → Routed
  traceCorrespondence : ∀ (source target : Original) (trace : List Label),
    Walk original source trace target ↔ Walk routed (embed source) trace (embed target)

def fragmentFactorization (graph : ControlGraph nodes regions) :
    ExactFactorization (SourceStep graph) (FragmentStep graph) :=
  ⟨ControlState.physical, exact_forward_trace_correspondence graph⟩

def composeFactorizations {First Middle Last Label : Type}
    {first : First → Option Label → First → Prop}
    {middle : Middle → Option Label → Middle → Prop}
    {last : Last → Option Label → Last → Prop}
    (one : ExactFactorization first middle) (two : ExactFactorization middle last) :
    ExactFactorization first last where
  embed node := two.embed (one.embed node)
  traceCorrespondence source target trace :=
    (one.traceCorrespondence source target trace).trans
      (two.traceCorrespondence (one.embed source) (one.embed target) trace)

theorem recursive_factorization_preserves_trace {First Middle Last Label : Type}
    {first : First → Option Label → First → Prop}
    {middle : Middle → Option Label → Middle → Prop}
    {last : Last → Option Label → Last → Prop}
    (one : ExactFactorization first middle) (two : ExactFactorization middle last)
    (source target : First) (trace : List Label) :
    Walk first source trace target ↔
      Walk last (two.embed (one.embed source)) trace (two.embed (one.embed target)) :=
  (composeFactorizations one two).traceCorrespondence source target trace

theorem dispatch_keeps_the_complete_port (graph : ControlGraph nodes regions)
    (left right : Port nodes)
    (step : FragmentStep graph (.leaving left) none (.entering right)) : left = right := by
  cases step
  rfl

theorem reverse_dispatch_keeps_the_complete_port (graph : ControlGraph nodes regions)
    (left right : Port nodes)
    (step : backward (FragmentStep graph) (.entering left) none (.leaving right)) :
    left = right := by
  exact (dispatch_keeps_the_complete_port graph right left step).symm

theorem entering_keeps_the_exact_destination (graph : ControlGraph nodes regions)
    (port : Port nodes) (destination : Fin nodes)
    (step : FragmentStep graph (.entering port) none (.physical destination)) :
    destination = port.target := by
  cases step
  rfl

theorem physical_to_physical_never_crosses_a_feedback_cut (graph : ControlGraph nodes regions)
    {source target : Fin nodes} {site : Option (Fin nodes)}
    (step : FragmentStep graph (.physical source) site (.physical target)) :
    graph.feedback source target = false := by
  cases step with
  | internal present uncut =>
      exact ((internal_iff_same_owner_without_feedback graph _ _).mp uncut).2

theorem valid_port_keeps_exit_kind (graph : ControlGraph nodes regions) (port : Port nodes)
    (valid : ValidPort graph port) : port.kind = graph.exitKind port.source port.target :=
  valid.2.2

theorem different_status_ports_cannot_merge (left right : Port nodes)
    (different : left.kind ≠ right.kind) : left ≠ right := by
  intro equal
  exact different (congrArg Port.kind equal)

theorem different_exit_destinations_cannot_merge (left right : Port nodes)
    (different : left.target ≠ right.target) : left ≠ right := by
  intro equal
  exact different (congrArg Port.target equal)

theorem different_entry_edges_cannot_merge (left right : Port nodes)
    (different : left.source ≠ right.source) : left ≠ right := by
  intro equal
  exact different (congrArg Port.source equal)

theorem observable_step_is_the_original_physical_operation (graph : ControlGraph nodes regions)
    {source target : ControlState nodes} {site : Fin nodes}
    (step : FragmentStep graph source (some site) target) :
    source = .physical site := by
  cases step <;> rfl

theorem synthetic_source_step_is_silent (graph : ControlGraph nodes regions)
    {source target : ControlState nodes} {site : Option (Fin nodes)}
    (synthetic : ∀ node, source ≠ .physical node)
    (step : FragmentStep graph source site target) : site = none := by
  cases step with
  | internal present same => exact False.elim (synthetic _ rfl)
  | leave present different => exact False.elim (synthetic _ rfl)
  | dispatch valid => rfl
  | enter valid => rfl

/-- Original operation IDs may include several source/sink/rule observations. -/
def observedOperations {operationIds : Nat}
    (operations : Fin nodes → List (Fin operationIds)) (trace : List (Fin nodes)) :
    List (Fin operationIds) := trace.flatMap operations

theorem physical_operation_ids_preserved (graph : ControlGraph nodes regions)
    {operationIds : Nat} (operations : Fin nodes → List (Fin operationIds))
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (SourceStep graph) source trace target) :
    ∃ routedTrace, Walk (FragmentStep graph) (.physical source) routedTrace (.physical target) ∧
      observedOperations operations routedTrace = observedOperations operations trace :=
  ⟨trace, source_path_lifts graph path, rfl⟩

theorem no_new_physical_operation_ids (graph : ControlGraph nodes regions)
    {operationIds : Nat} (operations : Fin nodes → List (Fin operationIds))
    {source target : Fin nodes} {trace : List (Fin nodes)}
    (path : Walk (FragmentStep graph) (.physical source) trace (.physical target)) :
    ∃ originalTrace, Walk (SourceStep graph) source originalTrace target ∧
      observedOperations operations originalTrace = observedOperations operations trace :=
  ⟨trace, fragment_path_erases graph path, rfl⟩

theorem dispatch_has_no_synthetic_rule_observation {operationIds : Nat}
    (operations : Fin nodes → List (Fin operationIds)) :
    observedOperations operations (emitSite (none : Option (Fin nodes))) = [] := rfl

theorem enter_has_no_synthetic_rule_observation {operationIds : Nat}
    (operations : Fin nodes → List (Fin operationIds)) :
    observedOperations operations (emitSite (none : Option (Fin nodes))) = [] := rfl

/-- This is a control-overhead witness, not an analyzer-speedup claim. -/
def routeHopCount (graph : ControlGraph nodes regions) (source target : Fin nodes) : Nat :=
  if graph.boundary source target then 3 else 1

theorem local_edge_one_hop (graph : ControlGraph nodes regions) (source target : Fin nodes)
    (uncut : graph.boundary source target = false) : routeHopCount graph source target = 1 := by
  simp [routeHopCount, uncut]

theorem crossing_edge_three_hops (graph : ControlGraph nodes regions) (source target : Fin nodes)
    (cut : graph.boundary source target = true) :
    routeHopCount graph source target = 3 := by
  simp [routeHopCount, cut]

def controlFixture : ControlGraph 5 4 where
  edge source target :=
    (source == 0 && target == 1) || (source == 1 && target == 2) ||
    (source == 2 && target == 1) || (source == 1 && target == 3) ||
    (source == 3 && target == 4)
  owner node := if node == 0 then 0 else if node == 1 then 1 else if node == 2 then 2 else 3
  feedback source target := source == 2 && target == 1
  exitKind source target := if source == 2 && target == 1 then .nextIteration else .ordinary

def fixtureEdges : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 1), (1, 3), (3, 4)]

theorem finite_fixture_physical_steps : fixtureEdges.length = 5 := by decide

theorem finite_fixture_control_hops :
    (fixtureEdges.map (fun edge => routeHopCount controlFixture edge.1 edge.2)).sum = 13 := by decide

theorem finite_fixture_retains_the_back_edge :
    controlFixture.edge 2 1 = true ∧
    (controlFixture.port 2 1).kind = .nextIteration := by decide

theorem finite_fixture_trace_lifts :
    Walk (FragmentStep controlFixture) (.physical 0) [0, 1, 2, 1, 3] (.physical 4) := by
  apply source_path_lifts controlFixture
  exact Walk.cons (SourceStep.edge (by decide))
    (Walk.cons (SourceStep.edge (by decide))
      (Walk.cons (SourceStep.edge (by decide))
        (Walk.cons (SourceStep.edge (by decide))
          (Walk.cons (SourceStep.edge (by decide)) (Walk.nil 4)))))

def selfLoopFixture : ControlGraph 1 1 where
  edge _ _ := true
  owner _ := 0
  feedback _ _ := true
  exitKind _ _ := .nextIteration

theorem self_loop_cut_crosses_even_with_equal_owners :
    selfLoopFixture.owner 0 = selfLoopFixture.owner 0 ∧
    selfLoopFixture.boundary 0 0 = true ∧
    ValidPort selfLoopFixture (selfLoopFixture.port 0 0) := by
  simp [ValidPort, ControlGraph.boundary, ControlGraph.port, selfLoopFixture]

theorem self_loop_route_uses_exit_and_entry_ports :
    routeVertices selfLoopFixture 0 0 =
      [.physical 0, .leaving (selfLoopFixture.port 0 0),
       .entering (selfLoopFixture.port 0 0), .physical 0] := by decide

theorem self_loop_exact_trace_is_not_dropped :
    Walk (FragmentStep selfLoopFixture) (.physical 0) [0] (.physical 0) :=
  source_edge_lifts selfLoopFixture 0 0 (by decide)

def selfLoopBodyCertificate : BodyAcyclicCertificate selfLoopFixture 0 where
  rank _ := 0
  increases source target inBody present uncut := by
    simp [ControlGraph.boundary, selfLoopFixture] at uncut

theorem self_loop_has_no_positive_internal_cycle (trace : List (Fin 1)) (positive : trace ≠ []) :
    ¬ Walk (BodyInternalStep selfLoopFixture 0) 0 trace 0 :=
  no_positive_closed_internal_body_path selfLoopFixture 0 selfLoopBodyCertificate 0 trace positive

end LoopFragments
