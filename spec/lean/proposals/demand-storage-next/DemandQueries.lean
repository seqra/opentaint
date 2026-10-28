/-
  PROPOSAL ONLY. Read-only demand queries over one transition-built snapshot.
  Reuse the finite symbolic static closure and entry-projection model. No
  unrestricted AP composition/reassociation is assumed.

  The emitter and paired reducer are the SAME executable adapters on both
  sides. Their necessary geometry/mark gates are explicit locality contracts.
  AP tails, E/mx, limits, protection, ND, producer coverage, real ZERO/carry
  adapters, visibility construction and scheduling remain production duties.
  Native NORMAL records are not a part of the demand snapshot or its gates.
-/
import «proposals».«restricted-demand-next».EntryProjection

namespace DemandStorageNext.DemandQueries
open RestrictedDemandNext.EntryProjection
set_option autoImplicit false

def input : Label → EntrySlot
  | .flow => .abstract
  | .mapped mark _ => .colored mark

/-- A FLOW primitive is TOP for a maybe-affected guard. It is NOT a concrete
    entry producer. A composed colored row can end at a FLOW primitive. -/
def OutputBound (primitive derived : Label) : Prop :=
  match primitive with
  | .flow => True
  | .mapped _ mark => output derived = .colored mark

def InputBound (primitive derived : Label) : Prop :=
  match primitive with
  | .flow => True
  | .mapped mark _ => input derived = .colored mark

theorem transferOutput {primitive left right result : Label}
    (joined : Join left right result) : OutputBound primitive right → OutputBound primitive result :=
  match primitive with
  | .flow => fun _ => trivial
  | .mapped _ _ =>
      match joined with
      | .flowLeft _ => fun bound => bound
      | .flowRight _ => fun impossible => nomatch impossible
      | .mapped _ _ _ _ _ => fun bound => bound

theorem transferInput {primitive left right result : Label}
    (joined : Join left right result) : InputBound primitive left → InputBound primitive result :=
  match primitive with
  | .flow => fun _ => trivial
  | .mapped _ _ =>
      match joined with
      | .flowLeft _ => fun impossible => nomatch impossible
      | .flowRight _ => fun bound => bound
      | .mapped _ _ _ _ _ => fun bound => bound

structure LastSeed (seeds : List Seed) (method : Nat) (target : Vertex) (label : Label) where
  seed : Seed
  member : seed ∈ seeds
  visible : method ∈ seed.visibleTo
  endpoint : seed.target = target
  outputBound : OutputBound seed.label label

structure FirstSeed (seeds : List Seed) (method : Nat) (source : Vertex) (label : Label) where
  seed : Seed
  member : seed ∈ seeds
  visible : method ∈ seed.visibleTo
  endpoint : seed.source = source
  inputBound : InputBound seed.label label

def lastSeed {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) : LastSeed seeds method b label :=
  match path with
  | .flowSeed member visible => ⟨_,member,visible,rfl,trivial⟩
  | .mappedSeed member visible => ⟨_,member,visible,rfl,rfl⟩
  | .compose _ _ after joined =>
      let found := lastSeed after
      ⟨found.seed,found.member,found.visible,found.endpoint,transferOutput joined found.outputBound⟩

def firstSeed {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) : FirstSeed seeds method a label :=
  match path with
  | .flowSeed member visible => ⟨_,member,visible,rfl,trivial⟩
  | .mappedSeed member visible => ⟨_,member,visible,rfl,rfl⟩
  | .compose _ before _ joined =>
      let found := firstSeed before
      ⟨found.seed,found.member,found.visible,found.endpoint,transferInput joined found.inputBound⟩

/-- Finite executable envelopes. They inspect seed endpoints, not all pairs. -/
def anyRow {α : Type} (rows : List α) (test : α → Bool) : Bool :=
  match rows with
  | [] => false
  | head :: rest => test head || anyRow rest test

theorem any_member {α : Type} {rows : List α} {row : α} {test : α → Bool}
    (member : row ∈ rows) (hit : test row = true) : anyRow rows test = true := by
  induction member with
  | head rest => change (test row || anyRow rest test) = true; rw [hit]; rfl
  | @tail head rest member prior =>
      change (test head || anyRow rest test) = true
      rw [prior]
      cases test head <;> rfl

def natSame (left : Nat) : Nat → Bool :=
  Nat.rec
    (fun right => match right with | 0 => true | .succ _ => false)
    (fun _ earlier right => match right with | 0 => false | .succ rest => earlier rest)
    left

theorem natSame_self (n : Nat) : natSame n n = true :=
  Nat.rec rfl (fun _ earlier => earlier) n

def visible (method : Nat) (seed : Seed) : Bool :=
  anyRow seed.visibleTo (fun owner => natSame owner method)

theorem visible_of_member {method : Nat} {seed : Seed} (member : method ∈ seed.visibleTo) :
    visible method seed = true := any_member member (natSame_self method)

def outputPotential (label : Label) (selector : EntrySlot → Bool) : Bool :=
  match label with
  | .flow => true
  | .mapped _ mark => selector (.colored mark)

def inputPotential (label : Label) (selector : EntrySlot → Bool) : Bool :=
  match label with
  | .flow => true
  | .mapped mark _ => selector (.colored mark)

theorem output_potential_sound {primitive derived : Label} {selector : EntrySlot → Bool}
    (bound : OutputBound primitive derived) (accepted : selector (output derived) = true) :
    outputPotential primitive selector = true :=
  match primitive with
  | .flow => rfl
  | .mapped _ _ => (congrArg selector bound).symm.trans accepted

theorem input_potential_sound {primitive derived : Label} {selector : EntrySlot → Bool}
    (bound : InputBound primitive derived) (accepted : selector (input derived) = true) :
    inputPotential primitive selector = true :=
  match primitive with
  | .flow => rfl
  | .mapped _ _ => (congrArg selector bound).symm.trans accepted

def entryGuard (seeds : List Seed) (method : Nat) (geometry : Vertex → Bool)
    (selector : EntrySlot → Bool) : Bool :=
  anyRow seeds (fun seed => visible method seed && geometry seed.target && outputPotential seed.label selector)

def sourceGuard (seeds : List Seed) (method : Nat) (geometry : Vertex → Bool)
    (selector : EntrySlot → Bool) : Bool :=
  anyRow seeds (fun seed => visible method seed && geometry seed.source && inputPotential seed.label selector)

theorem entry_guard_sound {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    {geometry : Vertex → Bool} {selector : EntrySlot → Bool}
    (path : Full seeds method a b label) (atTarget : geometry b = true)
    (accepted : selector (output label) = true) : entryGuard seeds method geometry selector = true := by
  let found := lastSeed path
  have owner : visible method found.seed = true := visible_of_member found.visible
  have location : geometry found.seed.target = true := (congrArg geometry found.endpoint).trans atTarget
  have mark := output_potential_sound found.outputBound accepted
  exact any_member found.member (by rw [owner,location,mark]; rfl)

theorem source_guard_sound {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    {geometry : Vertex → Bool} {selector : EntrySlot → Bool}
    (path : Full seeds method a b label) (atSource : geometry a = true)
    (accepted : selector (input label) = true) : sourceGuard seeds method geometry selector = true := by
  let found := firstSeed path
  have owner : visible method found.seed = true := visible_of_member found.visible
  have location : geometry found.seed.source = true := (congrArg geometry found.endpoint).trans atSource
  have mark := input_potential_sound found.inputBound accepted
  exact any_member found.member (by rw [owner,location,mark]; rfl)

/-- Target-oriented color search: inspect a matching mapped target, or step
    backwards across one FLOW suffix whose source is static. Stop at mapped.
    This is a derivation contract, not a production worklist/fairness theorem. -/
inductive BackEntry (seeds : List Seed) (method : Nat) : Vertex → EntrySlot → Type where
  | abstract {a b : Vertex} {owners : List Nat}
      (member : (⟨a,b,.flow,owners⟩ : Seed) ∈ seeds) (seen : method ∈ owners) :
      BackEntry seeds method b .abstract
  | colored {a b : Vertex} {i o : Atom} {owners : List Nat}
      (member : (⟨a,b,.mapped i o,owners⟩ : Seed) ∈ seeds) (seen : method ∈ owners) :
      BackEntry seeds method b (.colored o)
  | flowPrefix {middle target : Vertex} {mark : Atom} {owners : List Nat}
      (member : (⟨middle,target,.flow,owners⟩ : Seed) ∈ seeds) (seen : method ∈ owners)
      (staticMiddle : isStatic middle = true) (earlier : BackEntry seeds method middle (.colored mark)) :
      BackEntry seeds method target (.colored mark)

def entryToBack {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (proof : Entries seeds method target slot) : BackEntry seeds method target slot :=
  match proof with
  | .flowSeed member seen => .abstract member seen
  | .mappedSeed member seen => .colored member seen
  | .transport hs prior member seen => .flowPrefix member seen hs (entryToBack prior)

def backToEntry {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (proof : BackEntry seeds method target slot) : Entries seeds method target slot :=
  match proof with
  | .abstract member seen => .flowSeed member seen
  | .colored member seen => .mappedSeed member seen
  | .flowPrefix member seen hs earlier => .transport hs (backToEntry earlier) member seen

theorem targeted_projection_equivalent (seeds : List Seed) (method : Nat) (target : Vertex) (slot : EntrySlot) :
    Nonempty (FullTarget seeds method target slot) ↔ Nonempty (BackEntry seeds method target slot) :=
  ⟨fun ⟨proof⟩ => ⟨entryToBack (targetToEntry proof)⟩,
   fun ⟨proof⟩ => ⟨entryToFull (backToEntry proof)⟩⟩

/-- Query-specific existing bounded AP emitter. Locality is necessary, not
    sufficient: the implementation still runs the SAME complete AP emitter. -/
structure EntryAdapter (Initial : Type) where
  geometry : Vertex → Bool
  selector : EntrySlot → Bool
  emit : Vertex → EntrySlot → List Initial
  locality : ∀ {target slot result}, result ∈ emit target slot →
    geometry target = true ∧ selector slot = true

theorem targetGuard {Initial : Type} {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (adapter : EntryAdapter Initial) (targetProof : FullTarget seeds method target slot)
    {result : Initial} (emitted : result ∈ adapter.emit target slot) :
    entryGuard seeds method adapter.geometry adapter.selector = true :=
  let gates := adapter.locality emitted
  entry_guard_sound targetProof.path gates.1 (targetProof.projection.symm ▸ gates.2)

/-- Ordinary entries, implicit ZERO and same-actual-slot carry stay outside
    the static guard. The existing adapters provide their result list. -/
inductive ExplicitInitial {Initial : Type} (seeds : List Seed) (method : Nat)
    (ordinaryAndAdapters : List Initial) (adapter : EntryAdapter Initial) : Initial → Type where
  | ordinary {result : Initial} (member : result ∈ ordinaryAndAdapters) :
      ExplicitInitial seeds method ordinaryAndAdapters adapter result
  | static {result : Initial} {target : Vertex} {slot : EntrySlot}
      (guide : FullTarget seeds method target slot) (emitted : result ∈ adapter.emit target slot) :
      ExplicitInitial seeds method ordinaryAndAdapters adapter result

inductive LazyInitial {Initial : Type} (seeds : List Seed) (method : Nat)
    (ordinaryAndAdapters : List Initial) (adapter : EntryAdapter Initial) : Initial → Type where
  | ordinary {result : Initial} (member : result ∈ ordinaryAndAdapters) :
      LazyInitial seeds method ordinaryAndAdapters adapter result
  | static {result : Initial} {target : Vertex} {slot : EntrySlot}
      (affected : entryGuard seeds method adapter.geometry adapter.selector = true)
      (guide : BackEntry seeds method target slot) (emitted : result ∈ adapter.emit target slot) :
      LazyInitial seeds method ordinaryAndAdapters adapter result

def initialToLazy {Initial : Type} {seeds : List Seed} {method : Nat}
    {ordinary : List Initial} {adapter : EntryAdapter Initial} {result : Initial}
    (proof : ExplicitInitial seeds method ordinary adapter result) : LazyInitial seeds method ordinary adapter result :=
  match proof with
  | .ordinary member => .ordinary member
  | .static guide emitted => .static (targetGuard adapter guide emitted)
      (entryToBack (targetToEntry guide)) emitted

def initialToExplicit {Initial : Type} {seeds : List Seed} {method : Nat}
    {ordinary : List Initial} {adapter : EntryAdapter Initial} {result : Initial}
    (proof : LazyInitial seeds method ordinary adapter result) : ExplicitInitial seeds method ordinary adapter result :=
  match proof with
  | .ordinary member => .ordinary member
  | .static _ guide emitted => .static (entryToFull (backToEntry guide)) emitted

theorem initial_query_equivalent {Initial : Type} (seeds : List Seed) (method : Nat)
    (ordinary : List Initial) (adapter : EntryAdapter Initial) (result : Initial) :
    Nonempty (ExplicitInitial seeds method ordinary adapter result) ↔
    Nonempty (LazyInitial seeds method ordinary adapter result) :=
  ⟨fun ⟨proof⟩ => ⟨initialToLazy proof⟩,fun ⟨proof⟩ => ⟨initialToExplicit proof⟩⟩

theorem false_not_true (same : false = true) : False := nomatch same

/-- A false static guard selects ordinary lookup, not an empty demand result. -/
theorem falseGuardInitialIsOrdinary {Initial : Type} {seeds : List Seed} {method : Nat}
    {ordinary : List Initial} {adapter : EntryAdapter Initial} {result : Initial}
    (unaffected : entryGuard seeds method adapter.geometry adapter.selector = false)
    (proof : ExplicitInitial seeds method ordinary adapter result) : result ∈ ordinary :=
  match proof with
  | .ordinary member => member
  | .static guide emitted =>
      False.elim (false_not_true (unaffected.symm.trans (targetGuard adapter guide emitted)))

structure Pair where
  source : Vertex
  target : Vertex
  label : Label

/-- Same paired C5 reducer on both sides. In particular entrySelector reads
    the complete initial; exitSelector reads the conclusion, with different
    FLOW/exclusion rules. They must not be replaced by one shared mark test. -/
structure SummaryAdapter (Summary : Type) where
  entryGeometry : Vertex → Bool
  exitGeometry : Vertex → Bool
  entrySelector : EntrySlot → Bool
  exitSelector : EntrySlot → Bool
  reduce : Pair → List Summary
  locality : ∀ {pair result}, result ∈ reduce pair →
    entryGeometry pair.target = true ∧ exitGeometry pair.source = true ∧
    entrySelector (output pair.label) = true ∧ exitSelector (input pair.label) = true

def summaryGuard {Summary : Type} (seeds : List Seed) (method : Nat) (adapter : SummaryAdapter Summary) : Bool :=
  entryGuard seeds method adapter.entryGeometry adapter.entrySelector &&
    sourceGuard seeds method adapter.exitGeometry adapter.exitSelector

theorem summary_guard_sound {Summary : Type} {seeds : List Seed} {method : Nat}
    {source target : Vertex} {label : Label} (adapter : SummaryAdapter Summary)
    (path : Full seeds method source target label) {result : Summary}
    (reduced : result ∈ adapter.reduce ⟨source,target,label⟩) : summaryGuard seeds method adapter = true := by
  let gates := adapter.locality reduced
  have entry := entry_guard_sound path gates.1 gates.2.2.1
  have exit := source_guard_sound path gates.2.1 gates.2.2.2
  unfold summaryGuard
  rw [entry,exit]
  rfl

inductive Direction where | forward | backward

def backwardZero (direction : Direction) (genuineZero : Bool) : Bool :=
  match direction with
  | .forward => false
  | .backward => genuineZero

/-- The backward-ZERO branch is dispatched BEFORE paired C5. It is not
    a demand synthesized from an incoming fact or a current-query permission. -/
inductive ExplicitSummary {Summary : Type} (seeds : List Seed) (method : Nat)
    (direction : Direction) (genuineZero : Bool) (raw ordinary : List Summary)
    (adapter : SummaryAdapter Summary) : Summary → Type where
  | backwardZero {result : Summary} (route : backwardZero direction genuineZero = true)
      (member : result ∈ raw) : ExplicitSummary seeds method direction genuineZero raw ordinary adapter result
  | ordinary {result : Summary} (route : backwardZero direction genuineZero = false)
      (member : result ∈ ordinary) : ExplicitSummary seeds method direction genuineZero raw ordinary adapter result
  | static {result : Summary} {source target : Vertex} {label : Label}
      (route : backwardZero direction genuineZero = false) (path : Full seeds method source target label)
      (reduced : result ∈ adapter.reduce ⟨source,target,label⟩) :
      ExplicitSummary seeds method direction genuineZero raw ordinary adapter result

inductive LazySummary {Summary : Type} (seeds : List Seed) (method : Nat)
    (direction : Direction) (genuineZero : Bool) (raw ordinary : List Summary)
    (adapter : SummaryAdapter Summary) : Summary → Type where
  | backwardZero {result : Summary} (route : backwardZero direction genuineZero = true)
      (member : result ∈ raw) : LazySummary seeds method direction genuineZero raw ordinary adapter result
  | ordinary {result : Summary} (route : backwardZero direction genuineZero = false)
      (member : result ∈ ordinary) : LazySummary seeds method direction genuineZero raw ordinary adapter result
  | static {result : Summary} {source target : Vertex} {label : Label}
      (route : backwardZero direction genuineZero = false)
      (affected : summaryGuard seeds method adapter = true) (path : Full seeds method source target label)
      (reduced : result ∈ adapter.reduce ⟨source,target,label⟩) :
      LazySummary seeds method direction genuineZero raw ordinary adapter result

def summaryToLazy {Summary : Type} {seeds : List Seed} {method : Nat} {direction : Direction}
    {genuineZero : Bool} {raw ordinary : List Summary} {adapter : SummaryAdapter Summary} {result : Summary}
    (proof : ExplicitSummary seeds method direction genuineZero raw ordinary adapter result) :
    LazySummary seeds method direction genuineZero raw ordinary adapter result :=
  match proof with
  | .backwardZero route member => .backwardZero route member
  | .ordinary route member => .ordinary route member
  | .static route path reduced => .static route (summary_guard_sound adapter path reduced) path reduced

def summaryToExplicit {Summary : Type} {seeds : List Seed} {method : Nat} {direction : Direction}
    {genuineZero : Bool} {raw ordinary : List Summary} {adapter : SummaryAdapter Summary} {result : Summary}
    (proof : LazySummary seeds method direction genuineZero raw ordinary adapter result) :
    ExplicitSummary seeds method direction genuineZero raw ordinary adapter result :=
  match proof with
  | .backwardZero route member => .backwardZero route member
  | .ordinary route member => .ordinary route member
  | .static route _ path reduced => .static route path reduced

theorem summary_query_equivalent {Summary : Type} (seeds : List Seed) (method : Nat)
    (direction : Direction) (genuineZero : Bool) (raw ordinary : List Summary)
    (adapter : SummaryAdapter Summary) (result : Summary) :
    Nonempty (ExplicitSummary seeds method direction genuineZero raw ordinary adapter result) ↔
    Nonempty (LazySummary seeds method direction genuineZero raw ordinary adapter result) :=
  ⟨fun ⟨proof⟩ => ⟨summaryToLazy proof⟩,fun ⟨proof⟩ => ⟨summaryToExplicit proof⟩⟩

inductive OrdinarySummary {Summary : Type} (direction : Direction) (genuineZero : Bool)
    (raw ordinary : List Summary) : Summary → Type where
  | backwardZero {result : Summary} (route : backwardZero direction genuineZero = true)
      (member : result ∈ raw) : OrdinarySummary direction genuineZero raw ordinary result
  | restricted {result : Summary} (route : backwardZero direction genuineZero = false)
      (member : result ∈ ordinary) : OrdinarySummary direction genuineZero raw ordinary result

def falseGuardSummaryIsOrdinary {Summary : Type} {seeds : List Seed} {method : Nat} {direction : Direction}
    {genuineZero : Bool} {raw ordinary : List Summary} {adapter : SummaryAdapter Summary} {result : Summary}
    (unaffected : summaryGuard seeds method adapter = false)
    (proof : ExplicitSummary seeds method direction genuineZero raw ordinary adapter result) :
    OrdinarySummary direction genuineZero raw ordinary result :=
  match proof with
  | .backwardZero route member => .backwardZero route member
  | .ordinary route member => .restricted route member
  | .static _ path reduced =>
      False.elim (false_not_true (unaffected.symm.trans (summary_guard_sound adapter path reduced)))

theorem forward_zero_does_not_bypass : backwardZero .forward true = false := rfl

theorem only_genuine_backward_zero_bypasses :
    backwardZero .backward true = true ∧ backwardZero .backward false = false := ⟨rfl,rfl⟩

/-- FLOW rightmost seeds must remain TOP in the guard. Selecting only their
    direct abstract entry would reject this valid colored W;FLOW-R query. -/
def returnGeometry : Vertex → Bool
  | .ordinary slot => natSame slot 1
  | .static _ => false

def onlyU : EntrySlot → Bool
  | .abstract => false
  | .colored (.group _) => false
  | .colored (.full atom group) => natSame atom 8 && natSame group 1

def naiveDirectOutputGuard (seeds : List Seed) (method : Nat) : Bool :=
  anyRow seeds (fun seed => visible method seed && returnGeometry seed.target && onlyU (output seed.label))

theorem colored_suffix_needs_FLOW_TOP_guard :
    entryGuard exampleSeeds 0 returnGeometry onlyU = true ∧
    naiveDirectOutputGuard exampleSeeds 0 = false := ⟨rfl,rfl⟩

def targetedColoredReturn : BackEntry exampleSeeds 0 ret (.colored u) :=
  entryToBack projectedColoredReturn

/-- Once an adapter has proved equal complete payload keys, retain the OR
    of protection at each path/mark membership. Cell can be any finite
    payload-coordinate type. These laws do not change Facts equality and
    do not prove the AP/tree transport or the payload-key adapter. -/
def mergeMask {Cell : Type} (left right : Cell → Bool) (cell : Cell) : Bool :=
  left cell || right cell

theorem mask_merge_commutative {Cell : Type} (left right : Cell → Bool) (cell : Cell) :
    mergeMask left right cell = mergeMask right left cell := by
  change (left cell || right cell) = (right cell || left cell)
  cases left cell <;> cases right cell <;> rfl

theorem mask_merge_associative {Cell : Type} (a b c : Cell → Bool) (cell : Cell) :
    mergeMask (mergeMask a b) c cell = mergeMask a (mergeMask b c) cell := by
  change ((a cell || b cell) || c cell) = (a cell || (b cell || c cell))
  cases a cell <;> cases b cell <;> cases c cell <;> rfl

theorem mask_merge_idempotent {Cell : Type} (mask : Cell → Bool) (cell : Cell) :
    mergeMask mask mask cell = mask cell := by
  change (mask cell || mask cell) = mask cell
  cases mask cell <;> rfl

theorem mask_merge_keeps_late_protection {Cell : Type} (left right : Cell → Bool) (cell : Cell)
    (protectedLater : right cell = true) : mergeMask left right cell = true := by
  change (left cell || right cell) = true
  rw [protectedLater]
  cases left cell <;> rfl

#print axioms transferOutput
#print axioms transferInput
#print axioms lastSeed
#print axioms firstSeed
#print axioms any_member
#print axioms visible_of_member
#print axioms output_potential_sound
#print axioms input_potential_sound
#print axioms entry_guard_sound
#print axioms source_guard_sound
#print axioms entryToBack
#print axioms backToEntry
#print axioms targeted_projection_equivalent
#print axioms targetGuard
#print axioms initialToLazy
#print axioms initialToExplicit
#print axioms initial_query_equivalent
#print axioms falseGuardInitialIsOrdinary
#print axioms summary_guard_sound
#print axioms summaryToLazy
#print axioms summaryToExplicit
#print axioms summary_query_equivalent
#print axioms falseGuardSummaryIsOrdinary
#print axioms forward_zero_does_not_bypass
#print axioms only_genuine_backward_zero_bypasses
#print axioms colored_suffix_needs_FLOW_TOP_guard
#print axioms targetedColoredReturn
#print axioms mask_merge_commutative
#print axioms mask_merge_associative
#print axioms mask_merge_idempotent
#print axioms mask_merge_keeps_late_protection
end DemandStorageNext.DemandQueries
