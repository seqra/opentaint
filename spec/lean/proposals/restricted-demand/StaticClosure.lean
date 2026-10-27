/-
  Proposal model. Guidance closure only; no executable summary is created.
  Graph vertices are compatible endpoint/mark instances. The symbolic mark
  compiler is checked separately below. AP geometry and JVM adapters remain
  explicit integration obligations, not assumptions of a JVM theorem.
-/
import Init

namespace StaticDemandClosure
set_option autoImplicit false

inductive Vertex where
  | static (position mark : Nat)
  | ordinary (position mark : Nat)
  deriving DecidableEq, Repr

def isStatic : Vertex → Bool
  | .static _ _ => true
  | .ordinary _ _ => false

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

def c1 : Vertex := .static 1 7
def c2 : Vertex := .static 2 7
def c3 : Vertex := .static 3 7
def x : Vertex := .ordinary 10 7
def y : Vertex := .ordinary 11 7
def seeds : List Edge := [⟨1,c1,c2⟩,⟨2,c2,c3⟩,⟨0,x,c1⟩,⟨0,c3,y⟩]
def calls : List Call := [⟨0,1⟩,⟨0,2⟩,⟨9,0⟩]

def staticComposition : Eager seeds calls 0 c1 c3 :=
  .compose (middle := c2) rfl
    (.inherit (child := 1) (by decide) rfl rfl (.seed (by decide)))
    (.inherit (child := 2) (by decide) rfl rfl (.seed (by decide)))

def transitiveCaller : Eager seeds calls 9 c1 c3 :=
  .inherit (by decide) rfl rfl staticComposition

def writerStaticReader : Eager seeds calls 0 x y :=
  .compose rfl (.seed (by decide))
    (.compose rfl staticComposition (.seed (by decide)))

def executableFactoredWitness : Path seeds calls 0 x y := factor writerStaticReader

/- Symbolic mark composition. FLOW is diagonal; it is not a Cartesian
   wildcard which could turn T into U. Exclusions are normalized only on
   guidance as in the existing handoff. Runtime exclusions are unchanged. -/
inductive MarkRelation where
  | flow
  | mapped (input output : Nat)
  deriving DecidableEq, Repr

def holds : MarkRelation → Nat → Nat → Prop
  | .flow, a, b => a = b
  | .mapped input output, a, b => a = input ∧ b = output

def joinMark : MarkRelation → MarkRelation → Option MarkRelation
  | .flow, right => some right
  | left, .flow => some left
  | .mapped a b, .mapped c d => if b = c then some (.mapped a d) else none

def middleMark : MarkRelation → Nat → Nat
  | .flow, actual => actual
  | .mapped _ output, _ => output

theorem joinMark_sound (left right result : MarkRelation) (a c : Nat)
    (joined : joinMark left right = some result) (hit : holds result a c) :
    holds left a (middleMark left a) ∧ holds right (middleMark left a) c := by
  cases left with
  | flow =>
      simp only [joinMark,Option.some.injEq] at joined
      subst result
      exact ⟨rfl,hit⟩
  | mapped input middle =>
      cases right with
      | flow =>
          simp only [joinMark,Option.some.injEq] at joined
          subst result
          exact ⟨⟨hit.1,rfl⟩,hit.2.symm⟩
      | mapped next output =>
          by_cases compatible : middle = next
          · simp only [joinMark,if_pos compatible,Option.some.injEq] at joined
            subst result
            exact ⟨⟨hit.1,rfl⟩,⟨compatible,hit.2⟩⟩
          · simp [joinMark,compatible] at joined

def joinMarkWitness (left right : MarkRelation) (a middle c : Nat)
    (first : holds left a middle) (second : holds right middle c) :
    { result : MarkRelation // joinMark left right = some result ∧ holds result a c } := by
  cases left <;> cases right
  all_goals simp_all [holds,joinMark]
  all_goals first | exact ⟨.flow,rfl,rfl⟩ | exact ⟨.mapped _ _,rfl,by simp⟩

theorem distinct_marks_do_not_join :
    joinMark (.mapped 1 2) (.mapped 3 4) = none := rfl

theorem flow_keeps_mark_relation (a b : Nat) :
    joinMark .flow (.mapped a b) = some (.mapped a b) ∧
    joinMark (.mapped a b) .flow = some (.mapped a b) := ⟨rfl,rfl⟩

theorem marked_round_trip_stays_mapped (a b : Nat) :
    joinMark (.mapped a b) (.mapped b a) = some (.mapped a a) := by
  simp [joinMark]

theorem mapped_is_not_flow (a b : Nat) :
    MarkRelation.mapped a b ≠ MarkRelation.flow := by
  intro impossible
  cases impossible

/- The exit handler is an explicit parameter. The selected JVM adapter binds
   it to NormalExit rules and common summary emission, after return transfer.
   Only the existing unique normal boundary is supplied in normalExits. -/
def exitQueue (normalExits : List Nat) (fact : Nat) : List (Nat × Nat) :=
  normalExits.map (fun exit => (exit,fact))

def exitResults (handler : Nat → Nat → List Nat) (normalExits : List Nat) (fact : Nat) : List Nat :=
  (exitQueue normalExits fact).flatMap (fun (exit,input) => handler exit input)

theorem queued_exit_is_normal (normalExits : List Nat) (fact exit input : Nat)
    (queued : (exit,input) ∈ exitQueue normalExits fact) :
    exit ∈ normalExits ∧ input = fact := by
  obtain ⟨node,member,equal⟩ := List.mem_map.mp queued
  cases equal
  exact ⟨member,rfl⟩

theorem no_exit_has_no_summary (handler : Nat → Nat → List Nat) (fact : Nat) :
    exitResults handler [] fact = [] := rfl

theorem no_direct_summary_bypass (handler : Nat → Nat → List Nat)
    (normalExits : List Nat) (fact output : Nat)
    (produced : output ∈ exitResults handler normalExits fact) :
    ∃ exit, exit ∈ normalExits ∧ output ∈ handler exit fact := by
  obtain ⟨⟨exit,input⟩,queued,result⟩ := List.mem_flatMap.mp produced
  obtain ⟨normal,rfl⟩ := queued_exit_is_normal normalExits fact exit input queued
  exact ⟨exit,normal,result⟩

theorem exit_handler_kill_is_kept (normalExits : List Nat) (fact : Nat) :
    exitResults (fun _ _ => []) normalExits fact = [] := by
  simp [exitResults]

#print axioms eager_iff_factored
#print axioms least
#print axioms factor
#print axioms expand
#print axioms staticComposition
#print axioms transitiveCaller
#print axioms writerStaticReader
#print axioms executableFactoredWitness
#print axioms joinMark_sound
#print axioms joinMarkWitness
#print axioms distinct_marks_do_not_join
#print axioms flow_keeps_mark_relation
#print axioms marked_round_trip_stays_mapped
#print axioms mapped_is_not_flow
#print axioms queued_exit_is_normal
#print axioms no_exit_has_no_summary
#print axioms no_direct_summary_bypass
#print axioms exit_handler_kill_is_kept
end StaticDemandClosure
