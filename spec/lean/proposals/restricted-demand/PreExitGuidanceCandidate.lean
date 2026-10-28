/- Candidate only. No runtime policy is selected by this model.
   Vertices stand for compatible concrete location/mark instances. A FLOW schema
   supplies its diagonal instance for each mark. Actual caller bindings are an
   explicit input, not inferred from the call graph. AP adapters remain obligations. -/
import Init
namespace PreExitGuidanceCandidate
set_option autoImplicit false

inductive Vertex where
  | zero | ordinary (position mark : Nat) | static (position mark : Nat)
  deriving DecidableEq, Repr

def isStatic : Vertex → Bool
  | .static _ _ => true
  | _ => false

structure Edge where
  owner : Nat
  source : Vertex
  target : Vertex
  deriving DecidableEq, Repr

structure Call where
  parent : Nat
  child : Nat
  deriving DecidableEq, Repr

/-- A real call's input projection and satisfaction witness. The source vertices
    are complete concrete instances. Static output coordinates do not change. -/
structure Binding where
  call : Call
  childSource : Vertex
  parentSource : Vertex
  deriving DecidableEq, Repr

/-- Conceptual inference closure. Only B uses call-graph inheritance. A ZERO or
    ordinary W must instead have an explicit actual-binding witness. -/
inductive Guide (seeds : List Edge) (calls : List Call) (bindings : List Binding) :
    Nat → Vertex → Vertex → Type where
  | seed {m : Nat} {a b : Vertex} (member : (⟨m,a,b⟩ : Edge) ∈ seeds) : Guide seeds calls bindings m a b
  | inheritB {parent child : Nat} {a b : Vertex}
      (call : (⟨parent,child⟩ : Call) ∈ calls) (ha : isStatic a = true) (hb : isStatic b = true)
      (body : Guide seeds calls bindings child a b) : Guide seeds calls bindings parent a b
  | bindW {binding : Binding} {out : Vertex} (actual : binding ∈ bindings)
      (nonstatic : isStatic binding.childSource = false) (hs : isStatic out = true)
      (body : Guide seeds calls bindings binding.call.child binding.childSource out) :
      Guide seeds calls bindings binding.call.parent binding.parentSource out
  | compose {m : Nat} {a middle b : Vertex} (hs : isStatic middle = true)
      (left : Guide seeds calls bindings m a middle) (right : Guide seeds calls bindings m middle b) :
      Guide seeds calls bindings m a b

/-- Executable proof transport: preserving all primitive prefix/read keys preserves
    every finite route of the conceptual default closure, with the same bindings. -/
def transport {old captured : List Edge} {calls : List Call} {bindings : List Binding}
    (capture : ∀ e, e ∈ old → e ∈ captured) {m : Nat} {a b : Vertex}
    (route : Guide old calls bindings m a b) : Guide captured calls bindings m a b :=
  match route with
  | .seed h => .seed (capture _ h)
  | .inheritB c ha hb body => .inheritB c ha hb (transport capture body)
  | .bindW actual hn hs body => .bindW actual hn hs (transport capture body)
  | .compose hs left right => .compose hs (transport capture left) (transport capture right)

/-- A post-exit inventory containing only static-source readers cannot create an
    ordinary or ZERO writer. This models the missing-key counterexample. -/
theorem static_source_only {seeds : List Edge} {calls : List Call}
    (allStatic : ∀ e, e ∈ seeds → isStatic e.source = true)
    {m : Nat} {a b : Vertex} (route : Guide seeds calls [] m a b) : isStatic a = true := by
  induction route with
  | seed h => exact allStatic _ h
  | inheritB _ ha _ _ _ => exact ha
  | bindW actual _ _ _ _ => simp at actual
  | compose _ _ _ ih _ => exact ih

structure Origin (seeds : List Edge) (bindings : List Binding) (source : Vertex) where
  seedOrBinding : (∃ e, e ∈ seeds ∧ e.source = source) ∨
    (∃ b, b ∈ bindings ∧ b.parentSource = source)

def origin {seeds : List Edge} {calls : List Call} {bindings : List Binding}
    {m : Nat} {a b : Vertex} (route : Guide seeds calls bindings m a b) : Origin seeds bindings a :=
  match route with
  | .seed h => ⟨.inl ⟨_,h,rfl⟩⟩
  | .inheritB _ _ _ body => origin body
  | .bindW actual _ _ _ => ⟨.inr ⟨_,actual,rfl⟩⟩
  | .compose _ left _ => origin left

-- Uniform m is one concrete instance of a FLOW diagonal. Different mark
-- values can represent colored edges; the static middle must match exactly.
def arg (m : Nat) := Vertex.ordinary 0 m
def ret (m : Nat) := Vertex.ordinary 1 m
def field (m : Nat) := Vertex.static 0 m

def prefixRows (m : Nat) : List Edge :=
  [⟨0,arg m,field m⟩, ⟨0,field m,ret m⟩, ⟨1,field m,ret m⟩, ⟨2,field m,ret m⟩]
def calls : List Call := [⟨1,0⟩,⟨2,1⟩]
def bindings (m : Nat) : List Binding := [⟨⟨1,0⟩,arg m,arg m⟩,⟨⟨2,1⟩,arg m,arg m⟩]

def localReturn (m : Nat) : Guide (prefixRows m) calls (bindings m) 0 (arg m) (ret m) :=
  .compose (middle := field m) rfl (.seed (by simp [prefixRows])) (.seed (by simp [prefixRows]))
def wrappedWriter (m : Nat) : Guide (prefixRows m) calls (bindings m) 1 (arg m) (field m) :=
  .bindW (binding := ⟨⟨1,0⟩,arg m,arg m⟩) (by simp [bindings]) rfl rfl (.seed (by simp [prefixRows]))
def twiceWrappedWriter (m : Nat) : Guide (prefixRows m) calls (bindings m) 2 (arg m) (field m) :=
  .bindW (binding := ⟨⟨2,1⟩,arg m,arg m⟩) (by simp [bindings]) rfl rfl (wrappedWriter m)
def twiceWrappedReturn (m : Nat) : Guide (prefixRows m) calls (bindings m) 2 (arg m) (ret m) :=
  .compose (middle := field m) rfl (twiceWrappedWriter m) (.seed (by simp [prefixRows]))

def zeroPrefix (m : Nat) : List Edge :=
  [⟨0,.zero,field m⟩,⟨2,field m,ret m⟩]
def zeroBindings : List Binding := [⟨⟨1,0⟩,.zero,.zero⟩,⟨⟨2,1⟩,.zero,.zero⟩]
def twiceWrappedZeroReturn (m : Nat) : Guide (zeroPrefix m) calls zeroBindings 2 .zero (ret m) :=
  .compose (middle := field m) rfl
    (.bindW (binding := ⟨⟨2,1⟩,.zero,.zero⟩) (by simp [zeroBindings]) rfl rfl
      (.bindW (binding := ⟨⟨1,0⟩,.zero,.zero⟩) (by simp [zeroBindings]) rfl rfl
        (.seed (by simp [zeroPrefix]))))
    (.seed (by simp [zeroPrefix]))

def onlyReader (m : Nat) : List Edge := [⟨0,field m,ret m⟩]
theorem current_missing_arg_return (m : Nat) :
    ¬ Nonempty (Guide (onlyReader m) calls [] 0 (arg m) (ret m)) := by
  intro ⟨route⟩
  have h := static_source_only (seeds := onlyReader m) (by
    intro e he; simp [onlyReader] at he; subst e; rfl) route
  simp [arg, isStatic] at h

-- This is the concrete relational call-factorization obligation. Nonstatic
-- input/return projection remains present; only the STATIC middle is shared.
structure CallWitness (I A S B O : Type) (input : I → A → Prop) (writer : A → S → Prop)
    (reader : S → B → Prop) (output : B → O → Prop) (i : I) (o : O) where
  a : A
  s : S
  b : B
  hi : input i a
  hw : writer a s
  hr : reader s b
  ho : output b o

structure SplitCallWitness (I A S B O : Type) (input : I → A → Prop) (writer : A → S → Prop)
    (reader : S → B → Prop) (output : B → O → Prop) (i : I) (o : O) where
  s : S
  left : {a : A // input i a ∧ writer a s}
  right : {b : B // reader s b ∧ output b o}

def splitCall {I A S B O : Type} {input : I → A → Prop} {writer : A → S → Prop}
    {reader : S → B → Prop} {output : B → O → Prop} {i : I} {o : O}
    (w : CallWitness I A S B O input writer reader output i o) :
    SplitCallWitness I A S B O input writer reader output i o :=
  ⟨w.s, ⟨w.a,w.hi,w.hw⟩, ⟨w.b,w.hr,w.ho⟩⟩
def joinCall {I A S B O : Type} {input : I → A → Prop} {writer : A → S → Prop}
    {reader : S → B → Prop} {output : B → O → Prop} {i : I} {o : O}
    (w : SplitCallWitness I A S B O input writer reader output i o) :
    CallWitness I A S B O input writer reader output i o :=
  ⟨w.left.val,w.s,w.right.val,w.left.property.1,w.left.property.2,w.right.property.1,w.right.property.2⟩

#print axioms transport
#print axioms static_source_only
#print axioms origin
#print axioms current_missing_arg_return
#print axioms localReturn
#print axioms twiceWrappedReturn
#print axioms twiceWrappedZeroReturn
#print axioms splitCall
#print axioms joinCall
end PreExitGuidanceCandidate
