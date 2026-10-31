import SelectedCore

/-!
Run-1 static Target demand completion. This extends the existing static
factored-closure concept with typed ZERO and anonymous DemandTarget endpoints.
No NormalTarget vertex exists. Complete MethodKeys and compatible AP geometry
are runtime adapters. Concrete full-mark vertices give the finite reference
semantics of FULL/GROUP labels; runtime lookup need not enumerate this catalog.
-/
namespace StaticTargetClosure
set_option autoImplicit false
set_option linter.constructorNameAsVariable false

structure FullMark where
  group : Nat
  member : Nat
  deriving DecidableEq, Repr

inductive Vertex where
  | zero
  | static (position : Nat) (mark : FullMark)
  | ordinary (position : Nat) (mark : FullMark)
  | target
  deriving DecidableEq, Repr

def isStatic : Vertex → Bool
  | .static _ _ => true | _ => false

structure Edge where
  owner : Nat
  source : Vertex
  target : Vertex
  deriving DecidableEq, Repr

structure Call where
  parent : Nat
  child : Nat
  deriving DecidableEq, Repr

inductive CallPath (calls : List Call) : Nat → Nat → Type where
  | refl (m : Nat) : CallPath calls m m
  | step {a b c : Nat} (edge : ⟨a,b⟩ ∈ calls)
      (rest : CallPath calls b c) : CallPath calls a c

/-- Eager concept: copy only static/static relations to direct callers,
    and compose through a static middle. Recursion gives transitive callers. -/
inductive Eager (seeds : List Edge) (calls : List Call) : Nat → Vertex → Vertex → Type where
  | seed {m : Nat} {a b : Vertex} (edge : ⟨m,a,b⟩ ∈ seeds) : Eager seeds calls m a b
  | inherit {parent child : Nat} {a b : Vertex}
      (edge : ⟨parent,child⟩ ∈ calls) (ha : isStatic a = true) (hb : isStatic b = true)
      (derived : Eager seeds calls child a b) : Eager seeds calls parent a b
  | compose {m : Nat} {a middle b : Vertex} (hm : isStatic middle = true)
      (left : Eager seeds calls m a middle) (right : Eager seeds calls m middle b) :
      Eager seeds calls m a b

/-- Factored atoms retain each seed at its owner. Static seeds are visible
    through a computed call path; ordinary boundary seeds stay local. -/
inductive Atom (seeds : List Edge) (calls : List Call) : Nat → Vertex → Vertex → Type where
  | local {m : Nat} {a b : Vertex} (edge : ⟨m,a,b⟩ ∈ seeds) : Atom seeds calls m a b
  | inherited {m owner : Nat} {a b : Vertex} (route : CallPath calls m owner)
      (ha : isStatic a = true) (hb : isStatic b = true)
      (edge : ⟨owner,a,b⟩ ∈ seeds) : Atom seeds calls m a b

/-- A nonempty path with static internal vertices. Identity carry is a
    separate zero-length permission, never a broad graph node. -/
inductive Path (seeds : List Edge) (calls : List Call) : Nat → Vertex → Vertex → Type where
  | one {m : Nat} {a b : Vertex} (edge : Atom seeds calls m a b) : Path seeds calls m a b
  | cons {m : Nat} {a middle b : Vertex} (edge : Atom seeds calls m a middle)
      (hm : isStatic middle = true) (rest : Path seeds calls m middle b) :
      Path seeds calls m a b

def append {seeds : List Edge} {calls : List Call} {m : Nat} {a middle b : Vertex}
    (left : Path seeds calls m a middle) (hm : isStatic middle = true)
    (right : Path seeds calls m middle b) : Path seeds calls m a b :=
  match left with
  | .one edge => .cons edge hm right
  | .cons edge hs rest => .cons edge hs (append rest hm right)

def liftAtom {seeds : List Edge} {calls : List Call} {parent child : Nat} {a b : Vertex}
    (edge : ⟨parent,child⟩ ∈ calls) (ha : isStatic a = true) (hb : isStatic b = true)
    (atom : Atom seeds calls child a b) : Atom seeds calls parent a b :=
  match atom with
  | .local seed => .inherited (.step edge (.refl child)) ha hb seed
  | .inherited route hs ht seed => .inherited (.step edge route) hs ht seed

def liftPath {seeds : List Edge} {calls : List Call} {parent child : Nat} {a b : Vertex}
    (edge : ⟨parent,child⟩ ∈ calls) (ha : isStatic a = true) (hb : isStatic b = true)
    (path : Path seeds calls child a b) : Path seeds calls parent a b :=
  match path with
  | .one atom => .one (liftAtom edge ha hb atom)
  | .cons atom hm rest => .cons (liftAtom edge ha hm atom) hm (liftPath edge hm hb rest)

def factor {seeds : List Edge} {calls : List Call} {m : Nat} {a b : Vertex}
    (proof : Eager seeds calls m a b) : Path seeds calls m a b :=
  match proof with
  | .seed edge => .one (.local edge)
  | .inherit edge ha hb derived => liftPath edge ha hb (factor derived)
  | .compose hm left right => append (factor left) hm (factor right)

def liftEager {seeds : List Edge} {calls : List Call} {m owner : Nat} {a b : Vertex}
    (route : CallPath calls m owner) (ha : isStatic a = true) (hb : isStatic b = true)
    (proof : Eager seeds calls owner a b) : Eager seeds calls m a b :=
  match route with
  | .refl _ => proof
  | .step edge rest => .inherit edge ha hb (liftEager rest ha hb proof)

def expandAtom {seeds : List Edge} {calls : List Call} {m : Nat} {a b : Vertex}
    (atom : Atom seeds calls m a b) : Eager seeds calls m a b :=
  match atom with
  | .local edge => .seed edge
  | .inherited route ha hb edge => liftEager route ha hb (.seed edge)

def expand {seeds : List Edge} {calls : List Call} {m : Nat} {a b : Vertex}
    (path : Path seeds calls m a b) : Eager seeds calls m a b :=
  match path with
  | .one edge => expandAtom edge
  | .cons edge hm rest => .compose hm (expandAtom edge) (expand rest)

theorem eager_iff_factored (seeds : List Edge) (calls : List Call) (m : Nat) (a b : Vertex) :
    Nonempty (Eager seeds calls m a b) ↔ Nonempty (Path seeds calls m a b) :=
  ⟨fun ⟨proof⟩ => ⟨factor proof⟩, fun ⟨path⟩ => ⟨expand path⟩⟩

/-- Least inference closure: any relation closed under the stated rules
    contains every eagerly derived edge. No program-flow exactness follows. -/
theorem least {seeds : List Edge} {calls : List Call}
    (r : Nat → Vertex → Vertex → Prop)
    (seed : ∀ {m a b}, (⟨m,a,b⟩ : Edge) ∈ seeds → r m a b)
    (up : ∀ {parent child a b}, (⟨parent,child⟩ : Call) ∈ calls →
      isStatic a = true → isStatic b = true → r child a b → r parent a b)
    (join : ∀ {m a middle b}, isStatic middle = true → r m a middle → r m middle b → r m a b)
    {m : Nat} {a b : Vertex} (proof : Eager seeds calls m a b) : r m a b :=
  match proof with
  | .seed edge => seed edge
  | .inherit edge ha hb derived => up edge ha hb (least r seed up join derived)
  | .compose hm left right => join hm (least r seed up join left) (least r seed up join right)

/-- Executable endpoint provenance. Completion may combine relations but it
    cannot invent a new original (in particular, a ZERO original). -/
structure SourceWitness (seeds : List Edge) (source : Vertex) where
  owner : Nat
  target : Vertex
  member : (⟨owner, source, target⟩ : Edge) ∈ seeds

structure TargetWitness (seeds : List Edge) (target : Vertex) where
  owner : Nat
  source : Vertex
  member : (⟨owner, source, target⟩ : Edge) ∈ seeds

def sourceWitness {seeds : List Edge} {calls : List Call}
    {m : Nat} {a b : Vertex} (proof : Eager seeds calls m a b) : SourceWitness seeds a :=
  match proof with
  | .seed edge => ⟨m, b, edge⟩
  | .inherit _ _ _ derived => sourceWitness derived
  | .compose _ left _ => sourceWitness left

def targetWitness {seeds : List Edge} {calls : List Call}
    {m : Nat} {a b : Vertex} (proof : Eager seeds calls m a b) : TargetWitness seeds b :=
  match proof with
  | .seed edge => ⟨m, a, edge⟩
  | .inherit _ _ _ derived => targetWitness derived
  | .compose _ _ right => targetWitness right

/-- A guide swaps endpoints. This is guidance projection, not an executable
    summary reversal or an assertion that a real backward result exists. -/
structure BackwardGuide (seeds : List Edge) (calls : List Call)
    (m : Nat) (entry exit : Vertex) where
  evidence : Eager seeds calls m exit entry

def completeRequiredRoute {seeds : List Edge} {calls : List Call}
    {m : Nat} {a b : Vertex} (route : Path seeds calls m a b) :
    BackwardGuide seeds calls m b a := ⟨expand route⟩


/-- A Target guide uses the same paired endpoint projection as an AP guide.
The encoded AP is a runtime adapter; the ZERO case needs no such adapter. -/
def projectSource (encode : Vertex → SelectedCore.Atom) : Vertex → SelectedCore.Premise
  | .zero => .zero | vertex => .ap (encode vertex)

def projectTarget (encode : Vertex → SelectedCore.Atom) (owner : Nat)
    (source : Vertex) : SelectedCore.Demand :=
  ⟨owner, .target, projectSource encode source⟩

def terminalGuide {seeds : List Edge} {calls : List Call} {owner : Nat} {source : Vertex}
    (route : Path seeds calls owner source .target) :
    BackwardGuide seeds calls owner .target source := completeRequiredRoute route

theorem zero_target_pair_is_accepted (encode : Vertex → SelectedCore.Atom) (owner : Nat) :
    SelectedCore.c5Accept SelectedCore.exactEntry SelectedCore.exactExit
      (projectTarget encode owner .zero) (SelectedCore.targetSummary owner .zero) = true := by
  change ((decide (owner = owner)) && true && true) = true
  rw [decide_eq_true (Eq.refl owner)]
  rfl

theorem target_pair_admits_zero (encode : Vertex → SelectedCore.Atom) (owner : Nat)
    (source : Vertex) :
    SelectedCore.emittedZero .restricted [projectTarget encode owner source] owner .zero = [.zero] := by
  change (if ((decide (owner = owner)) && true) || false then [SelectedCore.Fact.zero] else []) = _
  rw [decide_eq_true (Eq.refl owner)]
  rfl

theorem nonzero_exit_does_not_accept_target (encode : Vertex → SelectedCore.Atom)
    (owner : Nat) (source : Vertex) (nonzero : source ≠ .zero) :
    SelectedCore.c5Accept SelectedCore.exactEntry SelectedCore.exactExit
      (projectTarget encode owner source) (SelectedCore.targetSummary owner .zero) = false := by
  cases source with
  | zero => exact False.elim (nonzero rfl)
  | static _ _ => exact Bool.and_false _
  | ordinary _ _ => exact Bool.and_false _
  | target => exact Bool.and_false _

/-- D_p ZERO accepts ZERO and every Target identically; AP exits accept neither.
This is a read-only exit probe, not a runtime Target-to-Reach conversion. -/
theorem c5_target_equals_zero_probe
    (entryAP : SelectedCore.Premise → SelectedCore.Premise → Bool)
    (exitAP : SelectedCore.Premise → SelectedCore.Atom → Option SelectedCore.Atom)
    (guide : SelectedCore.Demand) (owner : Nat) (original : SelectedCore.Premise)
    (label : SelectedCore.Target) (layer : SelectedCore.Layer) :
    SelectedCore.c5Accept entryAP exitAP guide ⟨owner, original, .target label, layer⟩ =
      SelectedCore.c5Accept entryAP exitAP guide ⟨owner, original, .zero, layer⟩ := by
  cases guide with
  | mk guideOwner entry exit => cases exit <;> rfl

/-- A visitor may test the same complete local or virtual row with ZERO.
Owner, premise, entry policy and paired exit remain unchanged. -/
theorem any_target_equals_any_zero_probe
    (entryAP : SelectedCore.Premise → SelectedCore.Premise → Bool)
    (exitAP : SelectedCore.Premise → SelectedCore.Atom → Option SelectedCore.Atom)
    (guides : List SelectedCore.Demand) (owner : Nat) (original : SelectedCore.Premise)
    (label : SelectedCore.Target) (layer : SelectedCore.Layer) :
    guides.any (fun guide => SelectedCore.c5Accept entryAP exitAP guide
      ⟨owner, original, .target label, layer⟩) =
    guides.any (fun guide => SelectedCore.c5Accept entryAP exitAP guide
      ⟨owner, original, .zero, layer⟩) := by
  simp only [c5_target_equals_zero_probe]

theorem target_is_not_a_composition_middle : isStatic .target = false := rfl
theorem zero_is_not_a_composition_middle : isStatic .zero = false := rfl

inductive Selector where
  | full (mark : FullMark)
  | group (id : Nat)
  deriving DecidableEq, Repr

def selected : Selector → FullMark → Bool
  | .full wanted, actual => wanted == actual
  | .group wanted, actual => wanted == actual.group

def members (catalog : List FullMark) (selector : Selector) : List FullMark :=
  catalog.filter (selected selector)

theorem membership_precise (catalog : List FullMark) (selector : Selector) (mark : FullMark) :
    mark ∈ members catalog selector ↔ mark ∈ catalog ∧ selected selector mark = true := by
  simp [members]

def terminalSeeds (catalog : List FullMark) (owner position : Nat) (selector : Selector)
    (label : SelectedCore.Target) : List Edge :=
  match label with
  | .normalTarget _ => []
  | .demandTarget => (members catalog selector).map
      (fun mark => ⟨owner, .static position mark, .target⟩)

theorem normal_target_is_not_a_seed (catalog : List FullMark) (owner position id : Nat)
    (selector : Selector) :
    terminalSeeds catalog owner position selector (.normalTarget id) = [] := rfl

theorem terminal_seed_has_writer_mark (catalog : List FullMark) (owner position : Nat)
    (selector : Selector) (mark : FullMark) :
    (⟨owner, .static position mark, .target⟩ : Edge) ∈
      terminalSeeds catalog owner position selector .demandTarget ↔
    mark ∈ catalog ∧ selected selector mark = true := by
  simp [terminalSeeds, members]

def flowSeeds (catalog : List FullMark) (owner fromPos toPos : Nat) : List Edge :=
  catalog.map fun mark => ⟨owner, .static fromPos mark, .static toPos mark⟩

theorem flow_never_changes_mark (catalog : List FullMark) (owner fromPos toPos : Nat)
    (input output : FullMark)
    (hit : (⟨owner,.static fromPos input,.static toPos output⟩ : Edge) ∈ flowSeeds catalog owner fromPos toPos) :
    input = output := by
  obtain ⟨mark, _, same⟩ := List.mem_map.mp hit
  cases same
  rfl

def mappedSeeds (catalog : List FullMark) (owner fromPos toPos : Nat) (input output : Selector) : List Edge :=
  (members catalog input).flatMap fun a => (members catalog output).map
    (fun b => ⟨owner, .static fromPos a, .static toPos b⟩)

theorem mapped_seed_exact (catalog : List FullMark) (owner fromPos toPos : Nat)
    (input output : Selector) (a b : FullMark) :
    (⟨owner, .static fromPos a, .static toPos b⟩ : Edge) ∈ mappedSeeds catalog owner fromPos toPos input output ↔
    (a ∈ catalog ∧ selected input a = true) ∧ (b ∈ catalog ∧ selected output b = true) := by
  simp [mappedSeeds, members]

namespace Controls

def t : FullMark := ⟨1, 10⟩
def u : FullMark := ⟨1, 11⟩
def v : FullMark := ⟨2, 20⟩
def cf : Vertex := .static 4 t
def cg : Vertex := .static 5 t
def ch : Vertex := .static 6 t

def directSeeds : List Edge := [⟨0,.zero,cf⟩,⟨0,cf,.target⟩]
def direct : Eager directSeeds [] 0 .zero .target :=
  .compose (middle := cf) rfl (.seed (by decide)) (.seed (by decide))
def directLazy : Path directSeeds [] 0 .zero .target := factor direct
def directGuide : BackwardGuide directSeeds [] 0 .target .zero := terminalGuide directLazy

def chainSeeds : List Edge :=
  [⟨0,.zero,cf⟩,⟨1,cf,cg⟩,⟨2,cg,ch⟩,⟨0,ch,.target⟩]
def calls : List Call := [⟨0,1⟩,⟨1,2⟩]
def inheritedBridge : Eager chainSeeds calls 0 cg ch :=
  .inherit (child := 1) (by decide) rfl rfl
    (.inherit (child := 2) (by decide) rfl rfl (.seed (by decide)))
def inheritedRoute : Eager chainSeeds calls 0 .zero .target :=
  .compose (middle := cf) rfl (.seed (by decide))
    (.compose (middle := cg) rfl (.inherit (child := 1) (by decide) rfl rfl (.seed (by decide)))
      (.compose (middle := ch) rfl inheritedBridge (.seed (by decide))))
def inheritedLazy : Path chainSeeds calls 0 .zero .target := factor inheritedRoute

theorem local_zero_target_pair (encode : Vertex → SelectedCore.Atom) :
    SelectedCore.c5Accept SelectedCore.exactEntry SelectedCore.exactExit
      (projectTarget encode 0 .zero) (SelectedCore.targetSummary 0 .zero) = true :=
  zero_target_pair_is_accepted encode 0

theorem incompatible_full_marks_do_not_meet :
    Vertex.static 4 t ≠ Vertex.static 4 u := by decide

theorem group_expands_only_its_members :
    terminalSeeds [t,u,v] 0 4 (.group 1) .demandTarget =
      [⟨0,.static 4 t,.target⟩,⟨0,.static 4 u,.target⟩] := rfl

theorem normal_target_remains_absent :
    terminalSeeds [t,u,v] 0 4 (.group 1) (.normalTarget 22) = [] := rfl

end Controls

#print axioms eager_iff_factored
#print axioms factor
#print axioms expand
#print axioms terminalGuide
#print axioms zero_target_pair_is_accepted
#print axioms terminal_seed_has_writer_mark
#print axioms flow_never_changes_mark
#print axioms mapped_seed_exact
#print axioms c5_target_equals_zero_probe
#print axioms any_target_equals_any_zero_probe
#print axioms Controls.directGuide
#print axioms Controls.inheritedLazy
#print axioms Controls.group_expands_only_its_members

end StaticTargetClosure
