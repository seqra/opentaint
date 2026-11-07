import Init

/-!
Preserve the existing exceptional-exit backward discovery overlay.

Forward uses the raw graph. Backward uses its reverse plus existing edges
from the exceptional exit to nodes that cannot reach either forward exit.
The normal exit gains no route: the exceptional exit has no incoming
backward edge, so a path starting elsewhere cannot use an overlay edge.

Paths and coverage certificates are Type-valued executable witnesses.
The dead-node predicate and its exiting-path certificate are supplied by
the existing graph adapter. This module does not verify that adapter's BFS,
scoped C2 implementation, source permissions or a Kotlin block dispatcher.
-/
namespace LoopFragments.Discovery
set_option autoImplicit false

variable {nodes : Nat}

abbrev Edges (nodes : Nat) := Fin nodes → Fin nodes → Bool

inductive Path (edge : Edges nodes) : Fin nodes → Fin nodes → Type where
  | refl (node : Fin nodes) : Path edge node node
  | cons {source middle target : Fin nodes} (present : edge source middle = true)
      (rest : Path edge middle target) : Path edge source target

def append {edge : Edges nodes} {source middle target : Fin nodes}
    (first : Path edge source middle) (last : Path edge middle target) : Path edge source target :=
  match first with
  | .refl _ => last
  | .cons present rest => .cons present (append rest last)

def reverse (edge : Edges nodes) : Edges nodes := fun source target => edge target source

def reversePath {edge : Edges nodes} {source target : Fin nodes}
    (path : Path edge source target) : Path (reverse edge) target source :=
  match path with
  | .refl node => .refl node
  | .cons present rest => append (reversePath rest) (.cons present (.refl _))

def mapPath {before after : Edges nodes}
    (inclusion : ∀ source target, before source target = true → after source target = true)
    {source target : Fin nodes} (path : Path before source target) : Path after source target :=
  match path with
  | .refl node => .refl node
  | .cons present rest => .cons (inclusion _ _ present) (mapPath inclusion rest)

structure Overlay (nodes : Nat) where
  raw : Edges nodes
  normal : Fin nodes
  exceptional : Fin nodes
  distinctExits : normal ≠ exceptional
  dead : Fin nodes → Bool
  exceptionalHasNoSuccessor : ∀ target, raw exceptional target = false
  exceptionalIsNotDead : dead exceptional = false

def forward (graph : Overlay nodes) : Edges nodes := graph.raw

def backward (graph : Overlay nodes) : Edges nodes := fun source target =>
  graph.raw target source || (decide (source = graph.exceptional) && graph.dead target)

theorem forward_graph_is_unchanged (graph : Overlay nodes) : forward graph = graph.raw := rfl

theorem raw_reverse_edge_is_preserved (graph : Overlay nodes) (source target : Fin nodes)
    (present : reverse graph.raw source target = true) : backward graph source target = true := by
  simp only [backward, reverse] at *
  simp only [present, Bool.true_or]

def liftReversePath (graph : Overlay nodes) {source target : Fin nodes}
    (path : Path graph.raw source target) : Path (backward graph) target source :=
  mapPath (raw_reverse_edge_is_preserved graph) (reversePath path)

theorem existing_discovery_edge (graph : Overlay nodes) (node : Fin nodes)
    (dead : graph.dead node = true) : backward graph graph.exceptional node = true := by
  simp [backward, dead]

def discoverDead (graph : Overlay nodes) (node : Fin nodes) (dead : graph.dead node = true) :
    Path (backward graph) graph.exceptional node :=
  .cons (existing_discovery_edge graph node dead) (.refl node)

theorem exceptional_has_no_backward_incoming (graph : Overlay nodes) (node : Fin nodes) :
    backward graph node graph.exceptional = false := by
  simp [backward, graph.exceptionalHasNoSuccessor node, graph.exceptionalIsNotDead]

theorem away_from_exceptional_only_raw_reverse (graph : Overlay nodes) (source target : Fin nodes)
    (different : source ≠ graph.exceptional) :
    backward graph source target = reverse graph.raw source target := by
  simp [backward, reverse, different]

def stripDiscovery (graph : Overlay nodes) {source target : Fin nodes}
    (path : Path (backward graph) source target) (different : source ≠ graph.exceptional) :
    Path (reverse graph.raw) source target :=
  match path with
  | .refl node => .refl node
  | @Path.cons _ _ first middle last present rest => by
      have middleDifferent : middle ≠ graph.exceptional := by
        intro same
        rw [same, exceptional_has_no_backward_incoming] at present
        cases present
      have rawPresent : reverse graph.raw first middle = true := by
        rw [away_from_exceptional_only_raw_reverse graph first middle different] at present
        exact present
      exact .cons rawPresent (stripDiscovery graph rest middleDifferent)

def normalPathWasAlreadyPresent (graph : Overlay nodes) {target : Fin nodes}
    (path : Path (backward graph) graph.normal target) :
    Path (reverse graph.raw) graph.normal target :=
  stripDiscovery graph path graph.distinctExits

inductive ExitPath (graph : Overlay nodes) (node : Fin nodes) where
  | normal (path : Path graph.raw node graph.normal)
  | exceptional (path : Path graph.raw node graph.exceptional)

inductive StartWitness (graph : Overlay nodes) (node : Fin nodes) where
  | normal (path : Path (backward graph) graph.normal node)
  | exceptional (path : Path (backward graph) graph.exceptional node)

structure ExitingCertificate (graph : Overlay nodes) where
  survivor : ∀ node, graph.dead node = false → ExitPath graph node

def discover (graph : Overlay nodes) (certificate : ExitingCertificate graph)
    (node : Fin nodes) : StartWitness graph node :=
  match dead : graph.dead node with
  | true => .exceptional (discoverDead graph node dead)
  | false => match certificate.survivor node dead with
    | .normal path => .normal (liftReversePath graph path)
    | .exceptional path => .exceptional (liftReversePath graph path)

def noLeave : Overlay 4 where
  raw := fun source target => (source == 0 && target == 1) || (source == 1 && target == 1)
  normal := 2
  exceptional := 3
  distinctExits := by decide
  dead := fun node => node == 0 || node == 1
  exceptionalHasNoSuccessor := by decide
  exceptionalIsNotDead := by decide

theorem no_leave_forward_has_no_added_exit : forward noLeave 1 2 = false := by decide

theorem no_leave_backward_has_exceptional_discovery : backward noLeave 3 1 = true := by decide

theorem no_leave_backward_normal_has_no_added_edge : backward noLeave 2 1 = false := by decide

def noLeaveWitness : Path (backward noLeave) 3 1 := discoverDead noLeave 1 (by decide)

end LoopFragments.Discovery
