/-
  PROPOSAL ONLY. Frozen local/remote query scheduling, not AP reassociation.

  A node is an opaque COMPLETE query state: fixed snapshot/method/direction,
  endpoint geometry and any symbolic selector coordinates required by that
  operation. Local and remote arcs are finite, immutable adapter outputs.
  Remote means all inherited rows visible to the ORIGINAL querying method,
  including transitive and sibling owners; it is not a call-chain relay.

  Constructive path conversion proves local closure followed by repeated
  remote-step/local-closure has exactly the full mixed reachability. Result
  equality uses the SAME read-only emitter. An exact output upper bound and
  accumulated result keys can justify an earlier stop. Keys must preserve all
  relevant AP geometry, tails, marks, layers and protection information.

  For C2's compatible-T existence question, the graph adapter admits only
  backward FLOW-prefix transitions and emits a witness at a composable mapped
  row whose output selector accepts actual T. A first positive witness is
  enough; a negative answer requires complete local AND remote exhaustion.
  C5 retains its separate paired-state emitter and does not use that stop rule.

  This file proves derivation/saturation contracts, not a concrete production
  BFS queue/fuel bound, AP adapter completeness, JVM results or measured savings.
-/
import Init

namespace DemandStorageNext.StagedDemandLookup
set_option autoImplicit false

abbrev Node := Nat
abbrev Key := Nat
abbrev Arc := Node × Node
abbrev Edge (arcs : List Arc) (source target : Node) := (source,target) ∈ arcs

inductive LocalPath (arcs : List Arc) : Node → Node → Type where
  | refl (atNode : Node) : LocalPath arcs atNode atNode
  | step {source middle target : Node} (before : LocalPath arcs source middle)
      (edge : Edge arcs middle target) : LocalPath arcs source target

inductive FullReach (roots : List Node) (localArcs remoteArcs : List Arc) : Node → Type where
  | root {node : Node} (member : node ∈ roots) : FullReach roots localArcs remoteArcs node
  | localStep {source target : Node} (before : FullReach roots localArcs remoteArcs source)
      (edge : Edge localArcs source target) : FullReach roots localArcs remoteArcs target
  | remoteStep {source target : Node} (before : FullReach roots localArcs remoteArcs source)
      (edge : Edge remoteArcs source target) : FullReach roots localArcs remoteArcs target

/-- Stage 1 is the first constructor. Stage 3 reopens EVERY previously local
    state for remote arcs, then locally closes EACH new remote image. -/
inductive StagedReach (roots : List Node) (localArcs remoteArcs : List Arc) : Node → Type where
  | localBase {source target : Node} (member : source ∈ roots)
      (closure : LocalPath localArcs source target) : StagedReach roots localArcs remoteArcs target
  | remoteThenLocal {source middle target : Node} (before : StagedReach roots localArcs remoteArcs source)
      (remote : Edge remoteArcs source middle) (closure : LocalPath localArcs middle target) :
      StagedReach roots localArcs remoteArcs target

def extendLocal {roots : List Node} {localArcs remoteArcs : List Arc} {source target : Node}
    (before : StagedReach roots localArcs remoteArcs source) (edge : Edge localArcs source target) :
    StagedReach roots localArcs remoteArcs target :=
  match before with
  | .localBase member path => .localBase member (.step path edge)
  | .remoteThenLocal earlier remote path => .remoteThenLocal earlier remote (.step path edge)

def fullToStaged {roots : List Node} {localArcs remoteArcs : List Arc} {target : Node}
    (path : FullReach roots localArcs remoteArcs target) : StagedReach roots localArcs remoteArcs target :=
  match path with
  | .root member => .localBase member (.refl _)
  | .localStep before edge => extendLocal (fullToStaged before) edge
  | .remoteStep before edge => .remoteThenLocal (fullToStaged before) edge (.refl _)

def finishLocal {roots : List Node} {localArcs remoteArcs : List Arc} {source target : Node}
    (before : FullReach roots localArcs remoteArcs source) (path : LocalPath localArcs source target) :
    FullReach roots localArcs remoteArcs target :=
  match path with
  | .refl _ => before
  | .step earlier edge => .localStep (finishLocal before earlier) edge

def stagedToFull {roots : List Node} {localArcs remoteArcs : List Arc} {target : Node}
    (path : StagedReach roots localArcs remoteArcs target) : FullReach roots localArcs remoteArcs target :=
  match path with
  | .localBase member closure => finishLocal (.root member) closure
  | .remoteThenLocal before edge closure => finishLocal (.remoteStep (stagedToFull before) edge) closure

theorem stagedReachEquivalent (roots : List Node) (localArcs remoteArcs : List Arc) (target : Node) :
    Nonempty (FullReach roots localArcs remoteArcs target) ↔
      Nonempty (StagedReach roots localArcs remoteArcs target) :=
  ⟨fun ⟨path⟩ => ⟨fullToStaged path⟩,fun ⟨path⟩ => ⟨stagedToFull path⟩⟩

/-- What a terminated mixed BFS must establish. Local membership alone does
    not imply a remote expansion has happened. No semantic store is mutated. -/
structure Saturated (roots : List Node) (localArcs remoteArcs : List Arc) (seen : List Node) where
  rootsSeen : ∀ {node}, node ∈ roots → node ∈ seen
  localClosed : ∀ {source target}, source ∈ seen → Edge localArcs source target → target ∈ seen
  remoteClosed : ∀ {source target}, source ∈ seen → Edge remoteArcs source target → target ∈ seen

theorem exhaustedContainsReachable {roots seen : List Node} {localArcs remoteArcs : List Arc}
    (closed : Saturated roots localArcs remoteArcs seen) {target : Node}
    (path : FullReach roots localArcs remoteArcs target) : target ∈ seen :=
  match path with
  | .root member => closed.rootsSeen member
  | .localStep before edge => closed.localClosed (exhaustedContainsReachable closed before) edge
  | .remoteStep before edge => closed.remoteClosed (exhaustedContainsReachable closed before) edge

theorem exhaustedSeenEquivalent {roots seen : List Node} {localArcs remoteArcs : List Arc}
    (closed : Saturated roots localArcs remoteArcs seen)
    (sound : ∀ {node}, node ∈ seen → FullReach roots localArcs remoteArcs node) (target : Node) :
    target ∈ seen ↔ Nonempty (FullReach roots localArcs remoteArcs target) :=
  ⟨fun member => ⟨sound member⟩,fun ⟨path⟩ => exhaustedContainsReachable closed path⟩

inductive QueryResult (roots : List Node) (localArcs remoteArcs : List Arc)
    (ordinary : List Key) (emit : Node → List Key) : Key → Type where
  | direct {key : Key} (member : key ∈ ordinary) : QueryResult roots localArcs remoteArcs ordinary emit key
  | reached {node : Node} {key : Key} (path : FullReach roots localArcs remoteArcs node)
      (member : key ∈ emit node) : QueryResult roots localArcs remoteArcs ordinary emit key

inductive StagedResult (roots : List Node) (localArcs remoteArcs : List Arc)
    (ordinary : List Key) (emit : Node → List Key) : Key → Type where
  | direct {key : Key} (member : key ∈ ordinary) : StagedResult roots localArcs remoteArcs ordinary emit key
  | reached {node : Node} {key : Key} (path : StagedReach roots localArcs remoteArcs node)
      (member : key ∈ emit node) : StagedResult roots localArcs remoteArcs ordinary emit key

def resultToStaged {roots ordinary : List Nat} {localArcs remoteArcs : List Arc} {emit : Node → List Key} {key : Key}
    (result : QueryResult roots localArcs remoteArcs ordinary emit key) :
    StagedResult roots localArcs remoteArcs ordinary emit key :=
  match result with
  | .direct member => .direct member
  | .reached path member => .reached (fullToStaged path) member

def resultToFull {roots ordinary : List Nat} {localArcs remoteArcs : List Arc} {emit : Node → List Key} {key : Key}
    (result : StagedResult roots localArcs remoteArcs ordinary emit key) :
    QueryResult roots localArcs remoteArcs ordinary emit key :=
  match result with
  | .direct member => .direct member
  | .reached path member => .reached (stagedToFull path) member

theorem stagedResultEquivalent (roots ordinary : List Nat) (localArcs remoteArcs : List Arc)
    (emit : Node → List Key) (key : Key) :
    Nonempty (QueryResult roots localArcs remoteArcs ordinary emit key) ↔
      Nonempty (StagedResult roots localArcs remoteArcs ordinary emit key) :=
  ⟨fun ⟨result⟩ => ⟨resultToStaged result⟩,fun ⟨result⟩ => ⟨resultToFull result⟩⟩

/-- For C2 these keys are the existing complete AP.emit results at the fixed
    terminal geometry. For C5 they must include full paired/reduced payloads
    and protection information. A spatially broader result is not equal-key
    coverage. The bound is independent of which search states were visited. -/
structure OutputUpperBound (ordinary possible : List Key) (emit : Node → List Key) where
  ordinaryBound : ∀ {key}, key ∈ ordinary → key ∈ possible
  emittedBound : ∀ {node key}, key ∈ emit node → key ∈ possible

theorem queryResultWithinBound {roots ordinary possible : List Nat} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} (bound : OutputUpperBound ordinary possible emit) {key : Key}
    (result : QueryResult roots localArcs remoteArcs ordinary emit key) : key ∈ possible :=
  match result with
  | .direct member => bound.ordinaryBound member
  | .reached _ member => bound.emittedBound member

theorem exactCoverageStop {roots ordinary possible accumulated : List Nat} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} (bound : OutputUpperBound ordinary possible emit)
    (covered : ∀ {key}, key ∈ possible → key ∈ accumulated)
    (sound : ∀ {key}, key ∈ accumulated → QueryResult roots localArcs remoteArcs ordinary emit key)
    (key : Key) : key ∈ accumulated ↔ Nonempty (QueryResult roots localArcs remoteArcs ordinary emit key) :=
  ⟨fun member => ⟨sound member⟩,fun ⟨result⟩ => covered (queryResultWithinBound bound result)⟩

/-- An existential C2 query returns one concrete witness or an exhaustion
    proof. It does not enumerate paths, original inputs or all output colors. -/
inductive Answer (Witness : Type) where
  | yes (witness : Witness)
  | no (exhausted : Witness → False)

def stagedAnswerToFull {roots ordinary : List Nat} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} {compatibleT : Key}
    (answer : Answer (StagedResult roots localArcs remoteArcs ordinary emit compatibleT)) :
    Answer (QueryResult roots localArcs remoteArcs ordinary emit compatibleT) :=
  match answer with
  | .yes witness => .yes (resultToFull witness)
  | .no exhausted => .no (fun result => exhausted (resultToStaged result))

theorem firstCompatibleWitnessIsEnough {roots ordinary : List Nat} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} {compatibleT : Key}
    (witness : StagedResult roots localArcs remoteArcs ordinary emit compatibleT) :
    Nonempty (QueryResult roots localArcs remoteArcs ordinary emit compatibleT) := ⟨resultToFull witness⟩

theorem negativeNeedsMixedExhaustion {roots ordinary : List Nat} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} {compatibleT : Key}
    (none : StagedResult roots localArcs remoteArcs ordinary emit compatibleT → False) :
    QueryResult roots localArcs remoteArcs ordinary emit compatibleT → False :=
  fun result => none (resultToStaged result)

theorem memberSingleton {α : Type} {row first : α} (member : row ∈ [first]) : row = first :=
  match member with | .head _ => rfl | .tail _ impossible => nomatch impossible

theorem memberPair {α : Type} {row first second : α} (member : row ∈ [first,second]) : row = first ∨ row = second :=
  match member with
  | .head _ => .inl rfl
  | .tail _ rest => .inr (memberSingleton rest)

/- A finite alternating route: initial local 0->1, inherited 1->2,
   then own local 2->3. Both scheduling mistakes lose the final key. -/
def localFixture : List Arc := [(0,1),(2,3)]
def remoteFixture : List Arc := [(1,2)]

def alternatingFull : FullReach [0] localFixture remoteFixture 3 :=
  .localStep (.remoteStep (.localStep (.root (.head _)) (.head _)) (.head _)) (.tail _ (.head _))

def alternatingStaged : StagedReach [0] localFixture remoteFixture 3 := fullToStaged alternatingFull

theorem localFixtureInvariant {source target : Node} (path : LocalPath localFixture source target)
    (initial : source = 0 ∨ source = 1) : target = 0 ∨ target = 1 := by
  cases path with
  | refl => exact initial
  | step before edge =>
      have prior := localFixtureInvariant before initial
      have choice := memberPair edge
      cases choice with
      | inl first =>
          have endpoint := congrArg Prod.snd first
          exact .inr endpoint
      | inr second =>
          have endpoint := congrArg Prod.fst second
          cases prior with
          | inl zero => cases endpoint.symm.trans zero
          | inr one =>
              have impossible : (1 : Nat) = 0 := congrArg Nat.pred (endpoint.symm.trans one)
              exact nomatch impossible

inductive RemoteOnlyAfterLocal : Node → Type where
  | base {source target : Node} (root : source ∈ [0]) (path : LocalPath localFixture source target) :
      RemoteOnlyAfterLocal target
  | remote {source target : Node} (before : RemoteOnlyAfterLocal source) (edge : Edge remoteFixture source target) :
      RemoteOnlyAfterLocal target

theorem remoteOnlyRange {target : Node} (bad : RemoteOnlyAfterLocal target) :
    target = 0 ∨ target = 1 ∨ target = 2 :=
  match bad with
  | .base root path =>
      match localFixtureInvariant path (.inl (memberSingleton root)) with
      | .inl zero => .inl zero
      | .inr one => .inr (.inl one)
  | .remote _ edge => .inr (.inr (congrArg Prod.snd (memberSingleton edge)))

theorem mustLocallyCloseRemoteImages :
    Nonempty (StagedReach [0] localFixture remoteFixture 3) ∧ ¬ Nonempty (RemoteOnlyAfterLocal 3) :=
  ⟨⟨alternatingStaged⟩,fun ⟨bad⟩ =>
    match remoteOnlyRange bad with
    | .inl impossible => nomatch impossible
    | .inr (.inl impossible) => nomatch congrArg Nat.pred impossible
    | .inr (.inr impossible) => nomatch congrArg Nat.pred (congrArg Nat.pred impossible)⟩

theorem remoteFromOriginalRootsIsInsufficient {source target : Node}
    (root : source ∈ [0]) (edge : Edge remoteFixture source target) : False := by
  have atZero := memberSingleton root
  have atOne := congrArg Prod.fst (memberSingleton edge)
  cases atZero.symm.trans atOne

def rightRemoteEligible (_localSeen : Bool) (remoteExpanded : Bool) : Bool := !remoteExpanded
def wrongRemoteEligible (localSeen remoteExpanded : Bool) : Bool := !localSeen && !remoteExpanded

theorem localVisitedDoesNotMeanRemoteExpanded :
    rightRemoteEligible true false = true ∧ wrongRemoteEligible true false = false := ⟨rfl,rfl⟩

/- Concrete reverse-query state names:
   0: C.g/FLOW -> ret/FLOW (local R)
   1: C.h/T -> ret/T      (prepend inherited C.h/T -> C.g/T)
   2: C.f/T -> ret/T      (prepend own FLOW C.f -> C.h)
   3: p/T -> ret/T        (prepend local W p/T -> C.f/T)
   The graph adapter preserves the fixed ret geometry and exact labels. -/
def reverseStaticTrace : StagedReach [0] [(1,2),(2,3)] [(0,1)] 3 :=
  .remoteThenLocal (.localBase (.head _) (.refl 0)) (.head _)
    (.step (.step (.refl 1) (.head _)) (.tail _ (.head _)))

/-- Per-terminal AP range is supplied independently. If FLOW and actual-T
    exact keys are already present, no transitive Boolean query is needed. -/
def twoKeys : List Key := [0,1]

theorem bothExactKeysPermitStop {roots : List Node} {localArcs remoteArcs : List Arc}
    {emit : Node → List Key} (bound : ∀ {node key}, key ∈ emit node → key ∈ twoKeys) (key : Key) :
    key ∈ twoKeys ↔ Nonempty (QueryResult roots localArcs remoteArcs twoKeys emit key) :=
  exactCoverageStop ⟨(fun member => member),bound⟩ (fun member => member) (fun member => .direct member) key

theorem oneKeyDoesNotCoverT : (0 : Key) ∈ [0] ∧ ¬ (1 : Key) ∈ [0] :=
  ⟨.head _,fun member => nomatch memberSingleton member⟩

#print axioms extendLocal
#print axioms fullToStaged
#print axioms finishLocal
#print axioms stagedToFull
#print axioms stagedReachEquivalent
#print axioms exhaustedContainsReachable
#print axioms exhaustedSeenEquivalent
#print axioms resultToStaged
#print axioms resultToFull
#print axioms stagedResultEquivalent
#print axioms queryResultWithinBound
#print axioms exactCoverageStop
#print axioms stagedAnswerToFull
#print axioms firstCompatibleWitnessIsEnough
#print axioms negativeNeedsMixedExhaustion
#print axioms alternatingFull
#print axioms alternatingStaged
#print axioms localFixtureInvariant
#print axioms remoteOnlyRange
#print axioms mustLocallyCloseRemoteImages
#print axioms remoteFromOriginalRootsIsInsufficient
#print axioms localVisitedDoesNotMeanRemoteExpanded
#print axioms reverseStaticTrace
#print axioms bothExactKeysPermitStop
#print axioms oneKeyDoesNotCoverT

end DemandStorageNext.StagedDemandLookup
