/-
  PROPOSAL ONLY. Tighter local-versus-shared demand lookup gates.

  Local coverage is an explicit production-adapter assumption: every visible
  primitive W/R and own B is directly indexed. An inherited row omitted from
  that local index must be B. Shared B stays shared; guards ignore its owners,
  labels and all AP tail/exclusion details. Actual lookup still checks them.

  This finite model reuses the existing symbolic relation and its targeted
  entry projection. It does not reassociate AP summary applications. Endpoint
  queries abstract conservative location indexes. Genuine ZERO/carry, packed
  leaves, ND, exact MethodKey construction, AP emission/restriction and result
  annotations remain production adapters. No runtime change or savings claim.
-/
import «proposals».«demand-storage-next».DemandQueries

namespace DemandStorageNext.LookupStrategies
open RestrictedDemandNext.EntryProjection
open DemandStorageNext.DemandQueries
set_option autoImplicit false

/-- The same bounded base/path candidate test used by the real query. A hit
    cannot cross the ordinary/static base distinction. Marks are ignored. -/
structure EndpointQuery where
  staticKind : Bool
  accepts : Vertex → Bool
  sameKind : ∀ {point}, accepts point = true → isStatic point = staticKind

inductive Placement (localRows : List Seed) (row : Seed) : Type where
  | direct (member : row ∈ localRows)
  | inherited (sourceStatic : isStatic row.source = true)
      (targetStatic : isStatic row.target = true)

/-- Finite primitive inventory already fixed at transition. The shared list
    may include invisible rows: guards can be positive unnecessarily. Local
    references do not copy B into every caller. ownB models reflexive ownership;
    actual B visibility is still required by every path constructor. -/
structure Coverage (seeds localRows bridges : List Seed) (method : Nat) where
  localSound : ∀ {row}, row ∈ localRows → row ∈ seeds
  placement : ∀ {row}, row ∈ seeds → method ∈ row.visibleTo → Placement localRows row
  shared : ∀ {row}, row ∈ seeds → method ∈ row.visibleTo →
    isStatic row.source = true → isStatic row.target = true → row ∈ bridges
  ownB : Seed → Bool
  ownLocal : ∀ {row}, row ∈ seeds → method ∈ row.visibleTo → ownB row = true → row ∈ localRows

def isFlow : Label → Bool
  | .flow => true
  | .mapped _ _ => false

def bridgeTarget (bridges : List Seed) (query : EndpointQuery) : Bool :=
  anyRow bridges (fun row => query.accepts row.target)

def bridgeSource (bridges : List Seed) (query : EndpointQuery) : Bool :=
  anyRow bridges (fun row => query.accepts row.source)

def readerTarget (localRows : List Seed) (query : EndpointQuery) (flowOnly : Bool) : Bool :=
  anyRow localRows (fun row => isStatic row.source && !isStatic row.target &&
    (!flowOnly || isFlow row.label) && query.accepts row.target)

def writerSource (localRows : List Seed) (query : EndpointQuery) : Bool :=
  anyRow localRows (fun row => !isStatic row.source && isStatic row.target && query.accepts row.source)

def entryGate (localRows bridges : List Seed) (query : EndpointQuery) : Bool :=
  if query.staticKind then bridgeTarget bridges query else readerTarget localRows query true

def pairedTargetGate (localRows bridges : List Seed) (query : EndpointQuery) : Bool :=
  if query.staticKind then bridgeTarget bridges query else readerTarget localRows query false

def pairedSourceGate (localRows bridges : List Seed) (query : EndpointQuery) : Bool :=
  if query.staticKind then bridgeSource bridges query else writerSource localRows query

def pairedGate (localRows bridges : List Seed) (entryGoal exitGoal : EndpointQuery) : Bool :=
  pairedTargetGate localRows bridges entryGoal && pairedSourceGate localRows bridges exitGoal

theorem boolConflict (same : (true : Bool) = false) : False := nomatch same

theorem nonstaticTargetLocal {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (ordinary : isStatic row.target = false) : row ∈ localRows :=
  match coverage.placement member seen with
  | .direct direct => direct
  | .inherited _ hs => False.elim (boolConflict (hs.symm.trans ordinary))

theorem nonstaticSourceLocal {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (ordinary : isStatic row.source = false) : row ∈ localRows :=
  match coverage.placement member seen with
  | .direct direct => direct
  | .inherited hs _ => False.elim (boolConflict (hs.symm.trans ordinary))

structure LastStatic (seeds : List Seed) (method : Nat) (target : Vertex) (label : Label) where
  found : LastSeed seeds method target label
  sourceStatic : isStatic found.seed.source = true

structure FirstStatic (seeds : List Seed) (method : Nat) (source : Vertex) (label : Label) where
  found : FirstSeed seeds method source label
  targetStatic : isStatic found.seed.target = true

/-- Preserve the actual primitive endpoint witness, without flattening or
    reassociating the supplied symbolic path. -/
def lastFromStatic {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) (hs : isStatic a = true) : LastStatic seeds method b label :=
  match path with
  | .flowSeed member seen => ⟨⟨_,member,seen,rfl,trivial⟩,hs⟩
  | .mappedSeed member seen => ⟨⟨_,member,seen,rfl,rfl⟩,hs⟩
  | .compose hm _ after joined =>
      let next := lastFromStatic after hm
      ⟨⟨next.found.seed,next.found.member,next.found.visible,next.found.endpoint,
          transferOutput joined next.found.outputBound⟩,next.sourceStatic⟩

def firstToStatic {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) (hs : isStatic b = true) : FirstStatic seeds method a label :=
  match path with
  | .flowSeed member seen => ⟨⟨_,member,seen,rfl,trivial⟩,hs⟩
  | .mappedSeed member seen => ⟨⟨_,member,seen,rfl,rfl⟩,hs⟩
  | .compose hm before _ joined =>
      let next := firstToStatic before hm
      ⟨⟨next.found.seed,next.found.member,next.found.visible,next.found.endpoint,
          transferInput joined next.found.inputBound⟩,next.targetStatic⟩

theorem pairedTargetHit {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (hs : isStatic row.source = true)
    (query : EndpointQuery) (hit : query.accepts row.target = true) :
    pairedTargetGate localRows bridges query = true := by
  have targetKind := query.sameKind hit
  cases hq : query.staticKind with
  | false =>
      have ht : isStatic row.target = false := targetKind.trans hq
      have direct := nonstaticTargetLocal coverage member seen ht
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member direct (by rw [hs,ht,hit]; rfl)
  | true =>
      have ht : isStatic row.target = true := targetKind.trans hq
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member (coverage.shared member seen hs ht) hit

theorem pairedSourceHit {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (ht : isStatic row.target = true)
    (query : EndpointQuery) (hit : query.accepts row.source = true) :
    pairedSourceGate localRows bridges query = true := by
  have sourceKind := query.sameKind hit
  cases hq : query.staticKind with
  | false =>
      have hs : isStatic row.source = false := sourceKind.trans hq
      have direct := nonstaticSourceLocal coverage member seen hs
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member direct (by rw [hs,ht,hit]; rfl)
  | true =>
      have hs : isStatic row.source = true := sourceKind.trans hq
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member (coverage.shared member seen hs ht) hit

structure PrimitivePair (localRows : List Seed) (method : Nat) (a b : Vertex) (label : Label) where
  seed : Seed
  member : seed ∈ localRows
  seen : method ∈ seed.visibleTo
  source : seed.source = a
  target : seed.target = b
  marks : seed.label = label

/-- Either a complete pair is already direct-local, or BOTH chosen C5
    endpoint gates are positive. A positive gate still proves no connection. -/
def classifyPair {seeds localRows bridges : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (coverage : Coverage seeds localRows bridges method) (path : Full seeds method a b label)
    (entryGoal exitGoal : EndpointQuery) (entryHit : entryGoal.accepts b = true)
    (exitHit : exitGoal.accepts a = true) :
    PSum (PrimitivePair localRows method a b label) (pairedGate localRows bridges entryGoal exitGoal = true) :=
  match path with
  | .flowSeed member seen =>
      match coverage.placement member seen with
      | .direct direct => .inl ⟨_,direct,seen,rfl,rfl,rfl⟩
      | .inherited hs ht => .inr (by
          have target := pairedTargetHit coverage member seen hs entryGoal entryHit
          have source := pairedSourceHit coverage member seen ht exitGoal exitHit
          unfold pairedGate; rw [target,source]; rfl)
  | .mappedSeed member seen =>
      match coverage.placement member seen with
      | .direct direct => .inl ⟨_,direct,seen,rfl,rfl,rfl⟩
      | .inherited hs ht => .inr (by
          have target := pairedTargetHit coverage member seen hs entryGoal entryHit
          have source := pairedSourceHit coverage member seen ht exitGoal exitHit
          unfold pairedGate; rw [target,source]; rfl)
  | .compose hm before after _ => .inr (by
      let terminal := lastFromStatic after hm
      let initial := firstToStatic before hm
      have target := pairedTargetHit coverage terminal.found.member terminal.found.visible
        terminal.sourceStatic entryGoal ((congrArg entryGoal.accepts terminal.found.endpoint).trans entryHit)
      have source := pairedSourceHit coverage initial.found.member initial.found.visible
        initial.targetStatic exitGoal ((congrArg exitGoal.accepts initial.found.endpoint).trans exitHit)
      unfold pairedGate; rw [target,source]; rfl)

def negativePairGateIsLocal {seeds localRows bridges : List Seed} {method : Nat}
    {a b : Vertex} {label : Label} (coverage : Coverage seeds localRows bridges method)
    (path : Full seeds method a b label) (entryGoal exitGoal : EndpointQuery)
    (entryHit : entryGoal.accepts b = true) (exitHit : exitGoal.accepts a = true)
    (negative : pairedGate localRows bridges entryGoal exitGoal = false) :
    PrimitivePair localRows method a b label :=
  match classifyPair coverage path entryGoal exitGoal entryHit exitHit with
  | .inl direct => direct
  | .inr positive => False.elim (boolConflict (positive.symm.trans negative))

structure DirectEntry (rows : List Seed) (method : Nat) (target : Vertex) (slot : EntrySlot) where
  seed : Seed
  member : seed ∈ rows
  seen : method ∈ seed.visibleTo
  endpoint : seed.target = target
  projection : output seed.label = slot

theorem flowReaderEntryHit {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (hs : isStatic row.source = true) (flow : row.label = .flow)
    (query : EndpointQuery) (hit : query.accepts row.target = true) :
    entryGate localRows bridges query = true := by
  have targetKind := query.sameKind hit
  cases hq : query.staticKind with
  | false =>
      have ht : isStatic row.target = false := targetKind.trans hq
      have direct := nonstaticTargetLocal coverage member seen ht
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member direct (by rw [hs,ht,flow,hit]; rfl)
  | true =>
      have ht : isStatic row.target = true := targetKind.trans hq
      change (if query.staticKind then _ else _) = true
      rw [hq]
      exact any_member (coverage.shared member seen hs ht) hit

theorem inheritedEntryHit {seeds localRows bridges : List Seed} {method : Nat} {row : Seed}
    (coverage : Coverage seeds localRows bridges method) (member : row ∈ seeds)
    (seen : method ∈ row.visibleTo) (hs : isStatic row.source = true) (ht : isStatic row.target = true)
    (query : EndpointQuery) (hit : query.accepts row.target = true) : entryGate localRows bridges query = true := by
  have kind : query.staticKind = true := (query.sameKind hit).symm.trans ht
  change (if query.staticKind then _ else _) = true
  rw [kind]
  exact any_member (coverage.shared member seen hs ht) hit

/-- The C2 proof operates on the previously proved targeted projection, not
    on a new composition scheduler. A terminal mapped local row is complete;
    a FLOW suffix may carry a color and therefore requires the chosen gate. -/
def classifyEntry {seeds localRows bridges : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (coverage : Coverage seeds localRows bridges method) (entry : BackEntry seeds method target slot)
    (query : EndpointQuery) (hit : query.accepts target = true) :
    PSum (DirectEntry localRows method target slot) (entryGate localRows bridges query = true) :=
  match entry with
  | .abstract member seen =>
      match coverage.placement member seen with
      | .direct direct => .inl ⟨_,direct,seen,rfl,rfl⟩
      | .inherited hs ht => .inr (inheritedEntryHit coverage member seen hs ht query hit)
  | .colored member seen =>
      match coverage.placement member seen with
      | .direct direct => .inl ⟨_,direct,seen,rfl,rfl⟩
      | .inherited hs ht => .inr (inheritedEntryHit coverage member seen hs ht query hit)
  | .flowPrefix member seen hs _ => .inr (flowReaderEntryHit coverage member seen hs rfl query hit)

def fullEntryChoice {seeds localRows bridges : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (coverage : Coverage seeds localRows bridges method) (entry : FullTarget seeds method target slot)
    (query : EndpointQuery) (hit : query.accepts target = true) :
    PSum (DirectEntry localRows method target slot) (entryGate localRows bridges query = true) :=
  classifyEntry coverage (entryToBack (targetToEntry entry)) query hit

def negativeEntryGateIsLocal {seeds localRows bridges : List Seed} {method : Nat}
    {target : Vertex} {slot : EntrySlot} (coverage : Coverage seeds localRows bridges method)
    (entry : FullTarget seeds method target slot) (query : EndpointQuery) (hit : query.accepts target = true)
    (negative : entryGate localRows bridges query = false) : DirectEntry localRows method target slot :=
  match fullEntryChoice coverage entry query hit with
  | .inl direct => direct
  | .inr positive => False.elim (boolConflict (positive.symm.trans negative))

theorem mappedTerminalOutput {left result : Label} {i o : Atom}
    (joined : Join left (.mapped i o) result) : output result = .colored o :=
  transferOutput joined (primitive := .mapped i o) rfl

/-- The exact target and output selector of a mapped local terminal already
    occur in the local C2 index. This does not make its paired C5 prefix local. -/
def mappedTerminalLocal {localRows : List Seed} {method : Nat} {a b : Vertex}
    {i o : Atom} {owners : List Nat} {left result : Label}
    (direct : (⟨a,b,.mapped i o,owners⟩ : Seed) ∈ localRows) (seen : method ∈ owners)
    (joined : Join left (.mapped i o) result) : DirectEntry localRows method b (output result) :=
  ⟨_,direct,seen,rfl,(mappedTerminalOutput joined).symm⟩

/-- Actual FLOW cannot produce a concrete/group initial. ZERO/Reach is not
    represented by this adapter, and must keep its separate existing route. -/
structure FlowEmitter (Initial : Type) where
  emit : Vertex → EntrySlot → List Initial
  rejectsColored : ∀ {target mark result}, result ∉ emit target (.colored mark)

/-- Every result that CAN emit from actual FLOW has a direct abstract
    primitive witness, local or a visible shared one-edge FLOW B. No color
    traversal is required. Includes own B without requiring it to be inherited. -/
def flowActualDirect {Initial : Type} {seeds localRows bridges : List Seed} {method : Nat}
    {target : Vertex} {slot : EntrySlot} {result : Initial}
    (coverage : Coverage seeds localRows bridges method) (emitter : FlowEmitter Initial)
    (entry : BackEntry seeds method target slot) (emitted : result ∈ emitter.emit target slot) :
    Sum (DirectEntry localRows method target .abstract) (DirectEntry bridges method target .abstract) :=
  match entry with
  | .abstract member seen =>
      match coverage.placement member seen with
      | .direct direct => .inl ⟨_,direct,seen,rfl,rfl⟩
      | .inherited hs ht => .inr ⟨_,coverage.shared member seen hs ht,seen,rfl,rfl⟩
  | .colored _ _ => False.elim (emitter.rejectsColored emitted)
  | .flowPrefix _ _ _ _ => False.elim (emitter.rejectsColored emitted)

def flowActualNonstaticLocal {Initial : Type} {seeds localRows bridges : List Seed} {method : Nat}
    {target : Vertex} {slot : EntrySlot} {result : Initial}
    (coverage : Coverage seeds localRows bridges method) (emitter : FlowEmitter Initial)
    (entry : BackEntry seeds method target slot) (emitted : result ∈ emitter.emit target slot)
    (ordinary : isStatic target = false) : DirectEntry localRows method target .abstract :=
  match entry with
  | .abstract member seen => ⟨_,nonstaticTargetLocal coverage member seen ordinary,seen,rfl,rfl⟩
  | .colored _ _ => False.elim (emitter.rejectsColored emitted)
  | .flowPrefix _ _ _ _ => False.elim (emitter.rejectsColored emitted)

/- Small finite witnesses. They are lookup/projection examples, not source
   programs executed by a JVM/AP model. All have the same fixed visible owner. -/
def p : Vertex := .ordinary 10
def ret : Vertex := .ordinary 11
def cf : Vertex := .static 12
def cg : Vertex := .static 13

def ordinaryQuery (point : Nat) : EndpointQuery :=
  ⟨false,(fun vertex => match vertex with | .ordinary n => natSame n point | .static _ => false),
    (by intro vertex hit; cases vertex with
        | ordinary _ => rfl
        | static _ => exact False.elim (false_not_true hit))⟩

def staticQuery (point : Nat) : EndpointQuery :=
  ⟨true,(fun vertex => match vertex with | .static n => natSame n point | .ordinary _ => false),
    (by intro vertex hit; cases vertex with
        | static _ => rfl
        | ordinary _ => exact False.elim (false_not_true hit))⟩

def w : Seed := ⟨p,cf,.mapped t u,[0]⟩
def flowR : Seed := ⟨cf,ret,.flow,[0]⟩
def mappedR : Seed := ⟨cf,ret,.mapped u v,[0]⟩

def flowReturnPath : Full [w,flowR] 0 p ret (.mapped t u) :=
  .compose rfl (.mappedSeed (.head _) (.head _))
    (.flowSeed (.tail _ (.head _)) (.head _)) (.flowRight _)

theorem writerReaderWithoutB :
    entryGate [w,flowR] [] (ordinaryQuery 11) = true ∧
    pairedGate [w,flowR] [] (ordinaryQuery 11) (ordinaryQuery 10) = true := ⟨rfl,rfl⟩

theorem coloredNonstaticReturn :
    Nonempty (FullTarget [w,flowR] 0 ret (.colored u)) :=
  ⟨⟨p,.mapped t u,flowReturnPath,rfl⟩⟩

theorem noPrimitiveColoredFlowReturn : ¬ Nonempty (PrimitiveEntries [w,flowR] 0 ret (.colored u)) := by
  intro ⟨proof⟩
  cases proof with
  | mapped member _ =>
      have either := member_pair member
      cases either with
      | inl same =>
          have endpoint := congrArg Seed.target same
          change ret = cf at endpoint
          cases endpoint
      | inr same =>
          have label := congrArg Seed.label same
          change Label.mapped _ u = Label.flow at label
          cases label

def mappedReturnPath : Full [w,mappedR] 0 p ret (.mapped t v) :=
  .compose rfl (.mappedSeed (.head _) (.head _))
    (.mappedSeed (.tail _ (.head _)) (.head _)) (.mapped t u u v rfl)

theorem mappedReaderC2LocalButC5Transitive :
    entryGate [w,mappedR] [] (ordinaryQuery 11) = false ∧
    pairedGate [w,mappedR] [] (ordinaryQuery 11) (ordinaryQuery 10) = true ∧
    Nonempty (DirectEntry [w,mappedR] 0 ret (.colored v)) ∧
    Nonempty (Full [w,mappedR] 0 p ret (.mapped t v)) :=
  ⟨rfl,rfl,⟨⟨mappedR,.tail _ (.head _),.head _,rfl,rfl⟩⟩,⟨mappedReturnPath⟩⟩

theorem unmatchedIntermediateMustExpand :
    (ordinaryQuery 10).accepts cf = false ∧
    (ordinaryQuery 10).accepts p = true ∧
    Nonempty (Full [w,mappedR] 0 p ret (.mapped t v)) := ⟨rfl,rfl,⟨mappedReturnPath⟩⟩

/-- A caller-provided carry result survives with no graph and false gates;
    it is not manufactured as a named-field vertex/path. -/
theorem carryWithoutGraphNeedsNoSearch :
    entryGate [] [] (staticQuery 12) = false ∧
    pairedGate [] [] (staticQuery 12) (staticQuery 12) = false ∧
    Nonempty (LazyInitial (Initial := Nat) [] 0 [42]
      ⟨(fun _ => false),(fun _ => false),(fun _ _ => []),
        (fun member => nomatch member)⟩ 42) :=
  ⟨rfl,rfl,⟨.ordinary (.head _)⟩⟩

#print axioms nonstaticTargetLocal
#print axioms nonstaticSourceLocal
#print axioms lastFromStatic
#print axioms firstToStatic
#print axioms pairedTargetHit
#print axioms pairedSourceHit
#print axioms classifyPair
#print axioms negativePairGateIsLocal
#print axioms flowReaderEntryHit
#print axioms inheritedEntryHit
#print axioms classifyEntry
#print axioms fullEntryChoice
#print axioms negativeEntryGateIsLocal
#print axioms mappedTerminalOutput
#print axioms mappedTerminalLocal
#print axioms flowActualDirect
#print axioms flowActualNonstaticLocal
#print axioms flowReturnPath
#print axioms writerReaderWithoutB
#print axioms coloredNonstaticReturn
#print axioms noPrimitiveColoredFlowReturn
#print axioms mappedReturnPath
#print axioms mappedReaderC2LocalButC5Transitive
#print axioms unmatchedIntermediateMustExpand
#print axioms carryWithoutGraphNeedsNoSearch

end DemandStorageNext.LookupStrategies
