/-
  PROPOSAL ONLY. Finite symbolic target-entry projection of frozen static
  guidance. A state retains (complete method key, target, output selector).
  It forgets the original left endpoint and left input selector.
  Primitive FLOW emits only an abstract entry. Mapped outputs can traverse
  FLOW suffixes. Visibility and FULL/GROUP entry admission remain explicit.

  The rows are a finite, already-bounded compatible-geometry abstraction.
  This file does not prove AP overlap/index completeness, prescan visibility,
  producer coverage, C5 equivalence, private ZERO/carry adapters, whole JVM
  behavior, or memory savings. The vertices here are nonzero ordinary/static
  endpoints; the symbolic selectors are FULL/GROUP, not a MarkTable inventory.
-/
import Init

namespace RestrictedDemandNext.EntryProjection
set_option autoImplicit false

inductive Vertex where
  | static (slot : Nat)
  | ordinary (slot : Nat)
  deriving DecidableEq, Repr

def isStatic : Vertex → Bool
  | .static _ => true
  | .ordinary _ => false

inductive Atom where
  | full (id group : Nat)
  | group (id : Nat)
  deriving DecidableEq, Repr

/-- Entry matching is directional. A group selector accepts a real FULL
    member; a FULL selector does not manufacture a member from a group. -/
def covers : Atom → Atom → Bool
  | .full a g, .full b h => a == b && g == h
  | .group g, .full _ h => g == h
  | .group g, .group h => g == h
  | .full _ _, .group _ => false

def compatible (left right : Atom) : Bool := covers left right || covers right left

inductive Label where
  | flow
  | mapped (input output : Atom)
  deriving DecidableEq, Repr

inductive EntrySlot where
  | abstract
  | colored (selector : Atom)
  deriving DecidableEq, Repr

def output : Label → EntrySlot
  | .flow => .abstract
  | .mapped _ mark => .colored mark

def admits : EntrySlot → Atom → Bool
  | .abstract, _ => true
  | .colored selector, actual => covers selector actual

/-- Visibility is fixed before projection. An actual adapter must populate
    B visibility from the detached graph and keep W/R exact-key ownership. -/
structure Seed where
  source : Vertex
  target : Vertex
  label : Label
  visibleTo : List Nat
  deriving DecidableEq, Repr

/-- Symbolic joins retain colors. FLOW is diagonal, never a product of all
    concrete marks. A mapped/mapped middle must pass FULL/GROUP compatibility. -/
inductive Join : Label → Label → Label → Type where
  | flowLeft (right : Label) : Join .flow right right
  | flowRight (left : Label) : Join left .flow left
  | mapped (a b c d : Atom) (middleCompatible : compatible b c = true) :
      Join (.mapped a b) (.mapped c d) (.mapped a d)

/-- Full finite-row closure: nonempty paths, static internal vertices only. -/
inductive Full (seeds : List Seed) (method : Nat) : Vertex → Vertex → Label → Type where
  | flowSeed {a b : Vertex} {visible : List Nat}
      (member : (⟨a,b,.flow,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      Full seeds method a b .flow
  | mappedSeed {a b : Vertex} {input out : Atom} {visible : List Nat}
      (member : (⟨a,b,.mapped input out,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      Full seeds method a b (.mapped input out)
  | compose {a middle b : Vertex} {left right result : Label}
      (staticMiddle : isStatic middle = true)
      (before : Full seeds method a middle left) (after : Full seeds method middle b right)
      (joined : Join left right result) : Full seeds method a b result

/-- C2 entry index. Only target and output selector are state coordinates.
    A colored state can move along a visible FLOW edge at a static source. -/
inductive Entries (seeds : List Seed) (method : Nat) : Vertex → EntrySlot → Type where
  | flowSeed {a b : Vertex} {visible : List Nat}
      (member : (⟨a,b,.flow,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      Entries seeds method b .abstract
  | mappedSeed {a b : Vertex} {input out : Atom} {visible : List Nat}
      (member : (⟨a,b,.mapped input out,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      Entries seeds method b (.colored out)
  | transport {middle target : Vertex} {mark : Atom} {visible : List Nat}
      (staticMiddle : isStatic middle = true) (prior : Entries seeds method middle (.colored mark))
      (member : (⟨middle,target,.flow,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      Entries seeds method target (.colored mark)

/-- Full suffixes labeled FLOW contain only FLOW atoms. Recurse on their
    executable path witness, rather than enumerating source/target products. -/
def transportGeneral {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) : label = .flow →
    {mark : Atom} → isStatic a = true → Entries seeds method a (.colored mark) →
    Entries seeds method b (.colored mark) :=
  match path with
  | .flowSeed member seen => fun _ _ hs prior => .transport hs prior member seen
  | .mappedSeed _ _ => fun impossible => nomatch impossible
  | .compose hm before after joined =>
      match joined with
      | .flowLeft _ => fun same _ hs prior =>
          transportGeneral after same hm (transportGeneral before rfl hs prior)
      | .flowRight _ => fun same _ hs prior =>
          transportGeneral after rfl hm (transportGeneral before same hs prior)
      | .mapped _ _ _ _ _ => fun impossible => nomatch impossible
termination_by structural path

def transportFlow {seeds : List Seed} {method : Nat} {a b : Vertex} {mark : Atom}
    (path : Full seeds method a b .flow) (staticStart : isStatic a = true)
    (prior : Entries seeds method a (.colored mark)) : Entries seeds method b (.colored mark) :=
  transportGeneral path rfl staticStart prior

/-- A mapped right relation fixes its output independently of its input.
    Its target entry already exists. Only a FLOW right suffix needs color
    transport from the left path. -/
def fullToEntry {seeds : List Seed} {method : Nat} {a b : Vertex} {label : Label}
    (path : Full seeds method a b label) : Entries seeds method b (output label) :=
  match path with
  | .flowSeed member seen => .flowSeed member seen
  | .mappedSeed member seen => .mappedSeed member seen
  | .compose hm before after joined =>
      match joined with
      | .flowLeft _ => fullToEntry after
      | .flowRight .flow => fullToEntry after
      | .flowRight (.mapped _ _) => transportFlow after hm (fullToEntry before)
      | .mapped _ _ c d _ => fullToEntry (label := .mapped c d) after

termination_by structural path

/-- The inverse returns the discarded source and input relation as explicit
    executable witnesses; no classical choice selects an arbitrary source. -/
structure FullTarget (seeds : List Seed) (method : Nat) (target : Vertex) (slot : EntrySlot) where
  source : Vertex
  label : Label
  path : Full seeds method source target label
  projection : output label = slot

def entryToFull {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (entry : Entries seeds method target slot) : FullTarget seeds method target slot :=
  match entry with
  | .flowSeed (a := a) member seen => ⟨a,.flow,.flowSeed member seen,rfl⟩
  | .mappedSeed (a := a) (input := input) (out := out) member seen =>
      ⟨a,.mapped input out,.mappedSeed member seen,rfl⟩
  | .transport hm prior member seen =>
      let previous := entryToFull prior
      ⟨previous.source,previous.label,
        .compose hm previous.path (.flowSeed member seen) (.flowRight previous.label),
        previous.projection⟩

def targetToEntry {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (targetProof : FullTarget seeds method target slot) : Entries seeds method target slot :=
  targetProof.projection ▸ fullToEntry targetProof.path

theorem target_projection_equivalent (seeds : List Seed) (method : Nat)
    (target : Vertex) (slot : EntrySlot) :
    Nonempty (FullTarget seeds method target slot) ↔ Nonempty (Entries seeds method target slot) :=
  ⟨fun ⟨proof⟩ => ⟨targetToEntry proof⟩,fun ⟨proof⟩ => ⟨entryToFull proof⟩⟩

/-- Admission retains the same actual/selector test after projection. -/
structure FullAdmission (seeds : List Seed) (method : Nat) (target : Vertex) (actual : Atom) where
  slot : EntrySlot
  entry : FullTarget seeds method target slot
  accepted : admits slot actual = true

structure EntryAdmission (seeds : List Seed) (method : Nat) (target : Vertex) (actual : Atom) where
  slot : EntrySlot
  entry : Entries seeds method target slot
  accepted : admits slot actual = true

def projectAdmission {seeds : List Seed} {method : Nat} {target : Vertex} {actual : Atom}
    (proof : FullAdmission seeds method target actual) : EntryAdmission seeds method target actual :=
  ⟨proof.slot,targetToEntry proof.entry,proof.accepted⟩

def expandAdmission {seeds : List Seed} {method : Nat} {target : Vertex} {actual : Atom}
    (proof : EntryAdmission seeds method target actual) : FullAdmission seeds method target actual :=
  ⟨proof.slot,entryToFull proof.entry,proof.accepted⟩

theorem admission_equivalent (seeds : List Seed) (method : Nat) (target : Vertex) (actual : Atom) :
    Nonempty (FullAdmission seeds method target actual) ↔ Nonempty (EntryAdmission seeds method target actual) :=
  ⟨fun ⟨proof⟩ => ⟨projectAdmission proof⟩,fun ⟨proof⟩ => ⟨expandAdmission proof⟩⟩

/-- Every entry target and its visibility have a primitive seed witness. -/
structure VisibleTarget (seeds : List Seed) (method : Nat) (target : Vertex) where
  seed : Seed
  member : seed ∈ seeds
  targetEq : seed.target = target
  visible : method ∈ seed.visibleTo

def visibleTarget {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (proof : Entries seeds method target slot) : VisibleTarget seeds method target :=
  match proof with
  | .flowSeed member seen => ⟨_,member,rfl,seen⟩
  | .mappedSeed member seen => ⟨_,member,rfl,seen⟩
  | .transport _ _ member seen => ⟨_,member,rfl,seen⟩

theorem invisible_seeds_give_no_entry {seeds : List Seed} {method : Nat}
    (none : ∀ seed ∈ seeds, method ∉ seed.visibleTo) {target : Vertex} {slot : EntrySlot} :
    ¬ Nonempty (Entries seeds method target slot) :=
  fun ⟨proof⟩ => let found := visibleTarget proof; none found.seed found.member found.visible

/-- Each color is the output selector of a finite primitive mapped seed.
    This forbids a hidden enumeration of all FULL members for a FLOW seed. -/
structure ColorOrigin (seeds : List Seed) (mark : Atom) where
  source : Vertex
  target : Vertex
  input : Atom
  visibility : List Nat
  member : (⟨source,target,.mapped input mark,visibility⟩ : Seed) ∈ seeds

def OriginAt (seeds : List Seed) : EntrySlot → Type
  | .abstract => Unit
  | .colored mark => ColorOrigin seeds mark

def originGeneral {seeds : List Seed} {method : Nat} {target : Vertex} {slot : EntrySlot}
    (proof : Entries seeds method target slot) : OriginAt seeds slot :=
  match proof with
  | .flowSeed _ _ => ()
  | .mappedSeed member _ => ⟨_,_,_,_,member⟩
  | .transport _ prior _ _ => originGeneral prior
termination_by structural proof

def colorOrigin {seeds : List Seed} {method : Nat} {target : Vertex} {mark : Atom}
    (proof : Entries seeds method target (.colored mark)) : ColorOrigin seeds mark :=
  originGeneral proof

def t : Atom := .full 7 1
def u : Atom := .full 8 1
def v : Atom := .full 9 1
def group1 : Atom := .group 1

theorem full_group_entry_contract :
    admits (.colored group1) t = true ∧ admits (.colored t) u = false ∧
    admits (.colored t) group1 = false ∧ admits (.colored (.group 2)) t = false :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem same_group_distinct_full_not_compatible : compatible u v = false := rfl

theorem full_group_middle_compatible : compatible u group1 = true := rfl

def x : Vertex := .ordinary 0
def c : Vertex := .static 0
def ret : Vertex := .ordinary 1
def writer : Seed := ⟨x,c,.mapped t u,[0]⟩
def reader : Seed := ⟨c,ret,.flow,[0]⟩
def exampleSeeds : List Seed := [writer,reader]

def fullColoredReturn : Full exampleSeeds 0 x ret (.mapped t u) :=
  .compose rfl (.mappedSeed (List.Mem.head _) (List.Mem.head _))
    (.flowSeed (List.Mem.tail writer (List.Mem.head _)) (List.Mem.head _)) (.flowRight _)

def projectedColoredReturn : Entries exampleSeeds 0 ret (.colored u) := fullToEntry fullColoredReturn

/-- The tempting primitive-target-only index omits FLOW color transport. -/
inductive PrimitiveEntries (seeds : List Seed) (method : Nat) : Vertex → EntrySlot → Type where
  | flow {a b : Vertex} {visible : List Nat}
      (member : (⟨a,b,.flow,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      PrimitiveEntries seeds method b .abstract
  | mapped {a b : Vertex} {input out : Atom} {visible : List Nat}
      (member : (⟨a,b,.mapped input out,visible⟩ : Seed) ∈ seeds) (seen : method ∈ visible) :
      PrimitiveEntries seeds method b (.colored out)

theorem member_singleton {row first : Seed} (member : row ∈ [first]) : row = first :=
  match member with
  | .head _ => rfl
  | .tail _ impossible => nomatch impossible

theorem member_pair {row first second : Seed} (member : row ∈ [first,second]) :
    row = first ∨ row = second :=
  match member with
  | .head _ => .inl rfl
  | .tail _ later => .inr (member_singleton later)

theorem bare_primitive_targets_miss_colored_return :
    ¬ Nonempty (PrimitiveEntries exampleSeeds 0 ret (.colored u)) := by
  intro ⟨proof⟩
  cases proof with
  | mapped member _ =>
      have either := member_pair member
      cases either with
      | inl same =>
          have endpoints := congrArg Seed.target same
          change ret = c at endpoints
          cases endpoints
      | inr same =>
          have labels := congrArg Seed.label same
          change Label.mapped _ u = Label.flow at labels
          cases labels

theorem flow_seed_has_no_concrete_enumeration (mark : Atom) :
    ¬ Nonempty (Entries [reader] 0 ret (.colored mark)) := by
  intro ⟨proof⟩
  let origin := colorOrigin proof
  have same := member_singleton origin.member
  have labels := congrArg Seed.label same
  change Label.mapped origin.input mark = Label.flow at labels
  cases labels

#print axioms transportGeneral
#print axioms transportFlow
#print axioms fullToEntry
#print axioms entryToFull
#print axioms targetToEntry
#print axioms target_projection_equivalent
#print axioms projectAdmission
#print axioms expandAdmission
#print axioms admission_equivalent
#print axioms visibleTarget
#print axioms invisible_seeds_give_no_entry
#print axioms originGeneral
#print axioms colorOrigin
#print axioms full_group_entry_contract
#print axioms same_group_distinct_full_not_compatible
#print axioms full_group_middle_compatible
#print axioms fullColoredReturn
#print axioms projectedColoredReturn
#print axioms bare_primitive_targets_miss_colored_return
#print axioms flow_seed_has_no_concrete_enumeration
end RestrictedDemandNext.EntryProjection
