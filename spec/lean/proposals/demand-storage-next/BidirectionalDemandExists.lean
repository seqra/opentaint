/-
  PROPOSAL ONLY. Directed proof graph for one C2 compatible-T existence query.
  Ports are logical proof coordinates, NOT proposed IR/heap objects.

  O(row) is an output geometry, I(row) an input geometry. A join is oriented
  O -> I and is supplied only by the current same-anchor/overlap adapter.
  Transfer I -> O exists only for an actual retained FLOW bridge. Eligible
  mapped outputs accepting actual T are sources; the FLOW reader input is the
  target. Visibility is fixed to the original querying method, not recomputed
  from whichever owner a frontier happens to visit. No all-mark inventory.

  The implementation can keep two typed geometry frontiers and test their
  oriented join; it need not materialize ports or join arcs. The finite lists
  below describe the reference adapter relation, not a storage requirement.

  Meeting proofs certify positives. Exhaustion requires complete adjacency,
  including newly enabled remote edges BETWEEN old local frontier states.
  The local/remote scheduler proof is in StagedDemandLookup.lean. This file
  does not prove AP adapter completeness, production BFS fairness or C5.
-/
import Init

namespace DemandStorageNext.BidirectionalDemandExists
set_option autoImplicit false

inductive Port where
  | output (id : Nat)
  | input (id : Nat)
  deriving DecidableEq, Repr

abbrev Arc := Nat × Nat

inductive DirectedEdge (joins flowBridges : List Arc) : Port → Port → Type where
  | join {out inp : Nat} (member : (out,inp) ∈ joins) :
      DirectedEdge joins flowBridges (.output out) (.input inp)
  | transfer {inp out : Nat} (member : (inp,out) ∈ flowBridges) :
      DirectedEdge joins flowBridges (.input inp) (.output out)

inductive Path (joins flowBridges : List Arc) : Port → Port → Type where
  | refl (atPort : Port) : Path joins flowBridges atPort atPort
  | cons {source middle target : Port} (edge : DirectedEdge joins flowBridges source middle)
      (rest : Path joins flowBridges middle target) : Path joins flowBridges source target

def append {joins flowBridges : List Arc} {source middle target : Port}
    (left : Path joins flowBridges source middle) (right : Path joins flowBridges middle target) :
    Path joins flowBridges source target :=
  match left with
  | .refl _ => right
  | .cons edge rest => .cons edge (append rest right)

structure Witness (joins flowBridges : List Arc) (sources : List Nat) (reader : Nat) where
  source : Nat
  eligible : source ∈ sources
  path : Path joins flowBridges (.output source) (.input reader)

structure SamePortMeeting (joins flowBridges : List Arc) (sources : List Nat) (reader : Nat) where
  source : Nat
  eligible : source ∈ sources
  meeting : Port
  forward : Path joins flowBridges (.output source) meeting
  backward : Path joins flowBridges meeting (.input reader)

structure OrientedJoinMeeting (joins flowBridges : List Arc) (sources : List Nat) (reader : Nat) where
  source : Nat
  eligible : source ∈ sources
  forwardOutput : Nat
  backwardInput : Nat
  forward : Path joins flowBridges (.output source) (.output forwardOutput)
  joinsHere : (forwardOutput,backwardInput) ∈ joins
  backward : Path joins flowBridges (.input backwardInput) (.input reader)

def samePortIsWitness {joins flowBridges : List Arc} {sources : List Nat} {reader : Nat}
    (meeting : SamePortMeeting joins flowBridges sources reader) : Witness joins flowBridges sources reader :=
  ⟨meeting.source,meeting.eligible,append meeting.forward meeting.backward⟩

def orientedJoinIsWitness {joins flowBridges : List Arc} {sources : List Nat} {reader : Nat}
    (meeting : OrientedJoinMeeting joins flowBridges sources reader) : Witness joins flowBridges sources reader :=
  ⟨meeting.source,meeting.eligible,
    append meeting.forward (.cons (.join meeting.joinsHere) meeting.backward)⟩

/-- Completeness of the meeting criterion as a relation; the search must
    separately establish that its finite frontiers/exhaustion implement it. -/
def witnessHasMeeting {joins flowBridges : List Arc} {sources : List Nat} {reader : Nat}
    (witness : Witness joins flowBridges sources reader) : SamePortMeeting joins flowBridges sources reader :=
  ⟨witness.source,witness.eligible,.output witness.source,.refl _,witness.path⟩

theorem meetingEquivalent (joins flowBridges : List Arc) (sources : List Nat) (reader : Nat) :
    Nonempty (Witness joins flowBridges sources reader) ↔
      Nonempty (SamePortMeeting joins flowBridges sources reader) :=
  ⟨fun ⟨witness⟩ => ⟨witnessHasMeeting witness⟩,fun ⟨meeting⟩ => ⟨samePortIsWitness meeting⟩⟩

structure ForwardExhausted (joins flowBridges : List Arc) (sources : List Nat) (seen : List Port) where
  roots : ∀ {source}, source ∈ sources → Port.output source ∈ seen
  complete : ∀ {source target}, source ∈ seen → DirectedEdge joins flowBridges source target → target ∈ seen

structure BackwardExhausted (joins flowBridges : List Arc) (reader : Nat) (seen : List Port) where
  root : Port.input reader ∈ seen
  complete : ∀ {source target}, target ∈ seen → DirectedEdge joins flowBridges source target → source ∈ seen

theorem forwardContainsPath {joins flowBridges : List Arc} {sources : List Nat} {seen : List Port}
    (closed : ForwardExhausted joins flowBridges sources seen) {source target : Port}
    (path : Path joins flowBridges source target) (atSource : source ∈ seen) : target ∈ seen :=
  match path with
  | .refl _ => atSource
  | .cons edge rest => forwardContainsPath closed rest (closed.complete atSource edge)

theorem backwardContainsPath {joins flowBridges : List Arc} {reader : Nat} {seen : List Port}
    (closed : BackwardExhausted joins flowBridges reader seen) {source target : Port}
    (path : Path joins flowBridges source target) (atTarget : target ∈ seen) : source ∈ seen :=
  match path with
  | .refl _ => atTarget
  | .cons edge rest => closed.complete (backwardContainsPath closed rest atTarget) edge

theorem forwardExhaustionCanReject {joins flowBridges : List Arc} {sources : List Nat} {reader : Nat}
    {forwardSeen backwardSeen : List Port}
    (closed : ForwardExhausted joins flowBridges sources forwardSeen)
    (readerSeen : Port.input reader ∈ backwardSeen)
    (noMeeting : ∀ {port}, port ∈ forwardSeen → port ∈ backwardSeen → False) :
    Witness joins flowBridges sources reader → False :=
  fun witness => noMeeting (forwardContainsPath closed witness.path (closed.roots witness.eligible)) readerSeen

theorem backwardExhaustionCanReject {joins flowBridges : List Arc} {sources : List Nat} {reader : Nat}
    {forwardSeen backwardSeen : List Port}
    (closed : BackwardExhausted joins flowBridges reader backwardSeen)
    (sourcesSeen : ∀ {source}, source ∈ sources → Port.output source ∈ forwardSeen)
    (noMeeting : ∀ {port}, port ∈ forwardSeen → port ∈ backwardSeen → False) :
    Witness joins flowBridges sources reader → False :=
  fun witness => noMeeting (sourcesSeen witness.eligible) (backwardContainsPath closed witness.path closed.root)

/-- Physical forward frontier contains OUTPUT geometries only. One step
    joins a real FLOW bridge input, then queues that bridge's output. -/
structure ForwardOutputsClosed (joins flowBridges : List Arc) (sources seen : List Nat) where
  roots : ∀ {source}, source ∈ sources → source ∈ seen
  complete : ∀ {out inp next}, out ∈ seen → (out,inp) ∈ joins → (inp,next) ∈ flowBridges → next ∈ seen

/-- Physical backward frontier contains INPUT geometries only. One step
    joins a real FLOW bridge output, then queues that bridge's input. -/
structure BackwardInputsClosed (joins flowBridges : List Arc) (reader : Nat) (seen : List Nat) where
  root : reader ∈ seen
  complete : ∀ {current out earlier}, current ∈ seen → (out,current) ∈ joins →
    (earlier,out) ∈ flowBridges → earlier ∈ seen

def ForwardCover (joins : List Arc) (seen : List Nat) : Port → Prop
  | .output out => out ∈ seen
  | .input inp => ∃ out, out ∈ seen ∧ (out,inp) ∈ joins

def BackwardCover (joins : List Arc) (seen : List Nat) : Port → Prop
  | .input inp => inp ∈ seen
  | .output out => ∃ inp, inp ∈ seen ∧ (out,inp) ∈ joins

theorem typedForwardEdge {joins flowBridges : List Arc} {sources seen : List Nat}
    (closed : ForwardOutputsClosed joins flowBridges sources seen) {source target : Port}
    (edge : DirectedEdge joins flowBridges source target) :
    ForwardCover joins seen source → ForwardCover joins seen target :=
  match edge with
  | .join joined => fun here => ⟨_,here,joined⟩
  | .transfer bridge => fun ⟨_,here,joined⟩ => closed.complete here joined bridge

theorem typedBackwardEdge {joins flowBridges : List Arc} {reader : Nat} {seen : List Nat}
    (closed : BackwardInputsClosed joins flowBridges reader seen) {source target : Port}
    (edge : DirectedEdge joins flowBridges source target) :
    BackwardCover joins seen target → BackwardCover joins seen source :=
  match edge with
  | .join joined => fun here => ⟨_,here,joined⟩
  | .transfer bridge => fun ⟨_,here,joined⟩ => closed.complete here joined bridge

theorem typedForwardCoverPath {joins flowBridges : List Arc} {sources seen : List Nat}
    (closed : ForwardOutputsClosed joins flowBridges sources seen) {source target : Port}
    (path : Path joins flowBridges source target) :
    ForwardCover joins seen source → ForwardCover joins seen target :=
  match path with
  | .refl _ => fun here => here
  | .cons edge rest => fun here => typedForwardCoverPath closed rest (typedForwardEdge closed edge here)

theorem typedBackwardCoverPath {joins flowBridges : List Arc} {reader : Nat} {seen : List Nat}
    (closed : BackwardInputsClosed joins flowBridges reader seen) {source target : Port}
    (path : Path joins flowBridges source target) :
    BackwardCover joins seen target → BackwardCover joins seen source :=
  match path with
  | .refl _ => fun here => here
  | .cons edge rest => fun here => typedBackwardEdge closed edge (typedBackwardCoverPath closed rest here)

theorem rejectTypedForwardPath {joins flowBridges : List Arc} {sources forwardSeen backwardSeen : List Nat}
    {reader out : Nat} (closed : ForwardOutputsClosed joins flowBridges sources forwardSeen)
    (readerSeen : reader ∈ backwardSeen)
    (noJoin : ∀ {left right}, left ∈ forwardSeen → right ∈ backwardSeen → (left,right) ∈ joins → False)
    (path : Path joins flowBridges (.output out) (.input reader)) (here : out ∈ forwardSeen) : False :=
  match typedForwardCoverPath closed path here with
  | ⟨_,reached,joined⟩ => noJoin reached readerSeen joined

theorem typedForwardExhaustionCanReject {joins flowBridges : List Arc} {sources forwardSeen backwardSeen : List Nat}
    {reader : Nat} (closed : ForwardOutputsClosed joins flowBridges sources forwardSeen)
    (readerSeen : reader ∈ backwardSeen)
    (noJoin : ∀ {left right}, left ∈ forwardSeen → right ∈ backwardSeen → (left,right) ∈ joins → False) :
    Witness joins flowBridges sources reader → False :=
  fun witness => rejectTypedForwardPath closed readerSeen noJoin witness.path (closed.roots witness.eligible)

theorem typedBackwardContainsInput {joins flowBridges : List Arc} {backwardSeen : List Nat}
    {reader input : Nat} (closed : BackwardInputsClosed joins flowBridges reader backwardSeen)
    (path : Path joins flowBridges (.input input) (.input reader)) : input ∈ backwardSeen :=
  typedBackwardCoverPath closed path closed.root

theorem typedBackwardExhaustionCanReject {joins flowBridges : List Arc} {sources forwardSeen backwardSeen : List Nat}
    {reader : Nat} (closed : BackwardInputsClosed joins flowBridges reader backwardSeen)
    (sourcesSeen : ∀ {source}, source ∈ sources → source ∈ forwardSeen)
    (noJoin : ∀ {left right}, left ∈ forwardSeen → right ∈ backwardSeen → (left,right) ∈ joins → False) :
    Witness joins flowBridges sources reader → False :=
  fun witness => match typedBackwardCoverPath closed witness.path closed.root with
  | ⟨_,reached,joined⟩ => noJoin (sourcesSeen witness.eligible) reached joined

theorem memberSingleton {α : Type} {row first : α} (member : row ∈ [first]) : row = first :=
  match member with | .head _ => rfl | .tail _ impossible => nomatch impossible

theorem inputStuckWithoutFlowBridge {joins : List Arc} {input : Nat} {target : Port}
    (path : Path joins [] (.input input) target) : target = .input input :=
  match path with
  | .refl _ => rfl
  | .cons (.transfer impossible) _ => nomatch impossible

theorem oneJoinWithoutTransfer {joins : List Arc} {out inp : Nat}
    (path : Path joins [] (.output out) (.input inp)) : (out,inp) ∈ joins := by
  cases path with
  | cons edge rest =>
      cases edge with
      | join member =>
          have endpoint := inputStuckWithoutFlowBridge rest
          cases endpoint
          exact member

/- Generic AP warning, not a claim that these nested geometries occur at the
   pinned run-1 field limit: left exact overlaps broad input; right output also
   overlaps broad input and the right reader. No actual FLOW bridge exists.
   An undirected overlap chain would invent left->right. The port graph cannot.
-/
def overlapOnlyJoins : List Arc := [(0,0),(1,0),(1,1)]

theorem broadOverlapIsNotATransfer :
    (0,0) ∈ overlapOnlyJoins ∧ (1,0) ∈ overlapOnlyJoins ∧ (1,1) ∈ overlapOnlyJoins ∧
    ¬ Nonempty (Path overlapOnlyJoins [] (.output 0) (.input 1)) := by
  refine ⟨.head _,.tail _ (.head _),.tail _ (.tail _ (.head _)),?_⟩
  intro ⟨path⟩
  have member := oneJoinWithoutTransfer path
  cases member with
  | tail _ rest =>
      cases rest with
      | tail _ last =>
          have impossible := memberSingleton last
          have source := congrArg Prod.fst impossible
          cases source

/-- Stage 3 reveals a join between two OLD local frontier ports. No newly
    allocated/discovered port is necessary for this first positive answer. -/
def remoteJoinAcrossOldFrontiers : OrientedJoinMeeting [(0,1)] [] [0] 1 :=
  ⟨0,.head _,0,1,.refl _,.head _,.refl _⟩

def newlyEnabledJoinIsPositive : Witness [(0,1)] [] [0] 1 :=
  orientedJoinIsWitness remoteJoinAcrossOldFrontiers

theorem oldFrontiersHaveNoIdenticalPort {port : Port}
    (left : port ∈ [Port.output 0]) (right : port ∈ [Port.input 1]) : False :=
  nomatch (memberSingleton left).symm.trans (memberSingleton right)

/-- Forward and backward steps both cross a real FLOW bridge. They do not
    use arbitrary output-output or input-input overlap as a transfer. -/
def realFlowBridgePath : Path [(0,0),(1,1)] [(0,1)] (.output 0) (.input 1) :=
  .cons (.join (.head _)) (.cons (.transfer (.head _)) (.cons (.join (.tail _ (.head _))) (.refl _)))

#print axioms append
#print axioms samePortIsWitness
#print axioms orientedJoinIsWitness
#print axioms witnessHasMeeting
#print axioms meetingEquivalent
#print axioms forwardContainsPath
#print axioms backwardContainsPath
#print axioms forwardExhaustionCanReject
#print axioms backwardExhaustionCanReject
#print axioms rejectTypedForwardPath
#print axioms typedForwardExhaustionCanReject
#print axioms typedBackwardContainsInput
#print axioms typedBackwardExhaustionCanReject
#print axioms inputStuckWithoutFlowBridge
#print axioms oneJoinWithoutTransfer
#print axioms broadOverlapIsNotATransfer
#print axioms remoteJoinAcrossOldFrontiers
#print axioms newlyEnabledJoinIsPositive
#print axioms oldFrontiersHaveNoIdenticalPort
#print axioms realFlowBridgePath

end DemandStorageNext.BidirectionalDemandExists
