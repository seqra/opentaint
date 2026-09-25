/-!
# Mark-set shallow scan: shared definitions

This file fixes the vocabulary shared by every other module. It contains
definitions only; properties are proved in the modules that import it.

Conventions:
* Every definition is executable. A finite set of marks is a `List Mark`, and
  set inclusion is `Subset a b := ∀ m ∈ a, m ∈ b`.
* Proofs must be constructive: `#print axioms` of every theorem may mention only
  `propext` and `Quot.sound`. `Classical.choice` and `sorryAx` are forbidden.

Two semantics live here.
* The *engine model* (`PE`, `Fires`) is the reference: an IFDS-style
  derivation system that keeps access-path bases and mirrors how the precise
  engine moves facts. It is an over-approximation of the real engine
  (assumptions E1–E6 in the spec).
* The *mark-set semantics* (`InS`, `Applicable`, `Needed`) erases bases and is
  what the shallow scan computes.
-/
namespace MarkScan

abbrev Mark := Nat
abbrev Node := Nat
abbrev Pc := Nat
abbrev RuleId := Nat
abbrev Base := Nat

def Subset (a b : List Mark) : Prop := ∀ m, m ∈ a → m ∈ b

/-! ## 1. Mark-only residual conditions -/

/-- Tree form of a rule's residual condition after static folding, position
erasure and removal of negated literals (mirrors `TaintMarkAwareConditionExpr`). -/
inductive Cond where
  | tt
  | ff
  | atom (m : Mark)
  | and (a b : Cond)
  | or (a b : Cond)
deriving Repr, DecidableEq, Inhabited

def Cond.sat : Cond → List Mark → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .atom m, s => s.contains m
  | .and a b, s => a.sat s && b.sat s
  | .or a b, s => a.sat s || b.sat s

/-- A conjunction of marks. `[]` is constant true. The length counts literals,
not distinct marks: `[a, a]` came from two literals on different positions and
so needs two facts. -/
abbrev Cube := List Mark
/-- A disjunction of cubes. `[]` is constant false. -/
abbrev Dnf := List Cube

def Dnf.sat (φ : Dnf) (s : List Mark) : Bool :=
  φ.any fun c => c.all fun m => s.contains m

def Cond.toDnf : Cond → Dnf
  | .tt => [[]]
  | .ff => []
  | .atom m => [[m]]
  | .and a b => a.toDnf.flatMap fun x => b.toDnf.map fun y => x ++ y
  | .or a b => a.toDnf ++ b.toDnf

def Dnf.atoms (φ : Dnf) : List Mark := φ.flatten

/-- Option 4* ("any mark suffices"), defined so that constant-true cubes are
kept. -/
def Dnf.relax (φ : Dnf) : Dnf :=
  if φ.any List.isEmpty then [[]] else φ.flatten.map fun m => [m]

/-- The literal reading of option 4*: "the rule is satisfiable if any of its
marks is present". Kept only to exhibit its unsoundness. -/
def Dnf.naiveAny (φ : Dnf) (s : List Mark) : Bool :=
  φ.atoms.any fun m => s.contains m

/-! ## 2. Engine-level rules (positions kept) -/

structure Fact where
  base : Base
  mark : Mark
deriving Repr, DecidableEq, Inhabited

/-- `ContainsMark(base, mark)`, possibly negated. -/
structure ELit where
  fact : Fact
  negated : Bool
deriving Repr, DecidableEq

abbrev ECube := List ELit
abbrev ECond := List ECube

/-- The facts a cube needs. The engine treats a negated mark literal as
satisfied (`TaintFactAwareConditionEvaluator`: `if (literal.negated) return
true`), so negated literals impose nothing. -/
def ECube.positive (c : ECube) : List Fact :=
  ((c.filter fun l => !l.negated).map (·.fact)).eraseDups

inductive Kind where
  | source
  | sink
  | passThrough
deriving Repr, DecidableEq

/-- A rule instantiated at one statement, with its residual condition.
* `assigns`: the `AssignMark` actions. For a sink these are
  `trackFactsReachAnalysisEnd`.
* `copies`: mark-preserving copies (`CopyAllMarks from → to`), used only by
  pass-through rules, which are never restricted.

Cleaners are not sites. They are always delegated, so they are modelled as
the fixed kill predicate `Program.kills`. -/
structure ESite where
  rule : RuleId
  kind : Kind
  cond : ECond
  assigns : List Fact
  copies : List (Base × Base)
deriving Repr

/-! ## 3. Programs as seen after the prescan -/

/-- A call graph over analysis nodes. A node is a `(method, method context)`
pair, i.e. a `MethodEntryPoint`. Each node carries its engine CFG and the
residual rules recorded during the prescan.
* `pcs n` must contain `0`, the entry statement.
* `succ` is the engine's normal CFG. Exceptional edges are excluded, as in the
  engine.
* `mapIn`: caller base at a call → callee base (`none`: not passed).
* `mapOut`: callee exit base → caller base (`none`: dropped).
* `kills`: cleaner and implicit kills. They are per fact, and the selection
  never changes them (assumption E4). -/
structure Program where
  nodes : List Node
  roots : List Node
  pcs : Node → List Pc
  succ : Node → Pc → List Pc
  exits : Node → List Pc
  sites : Node → Pc → List ESite
  calls : Node → Pc → List Node
  mapIn : Node → Pc → Base → Option Base
  mapOut : Node → Pc → Base → Option Base
  kills : Node → Pc → Fact → Bool

def Program.callees (p : Program) (n : Node) : List Node :=
  (p.pcs n).flatMap (p.calls n)

/-- Transitive-reflexive reachability in the call graph. -/
inductive Reaches (p : Program) : Node → Node → Prop
  | refl (n : Node) : Reaches p n n
  | step {a b c : Node} : b ∈ p.callees a → Reaches p b c → Reaches p a c

/-! ## 4. Abstract sites and the mark-set semantics -/

structure Site where
  rule : RuleId
  kind : Kind
  cond : Dnf
  gens : List Mark
deriving Repr

def ESite.abstract (s : ESite) : Site :=
  { rule := s.rule
    kind := s.kind
    cond := s.cond.map fun c => c.positive.map (·.mark)
    gens := s.assigns.map (·.mark) }

/-- The abstract sites of node `n`, paired with their statement. -/
def Program.nodeSites (p : Program) (n : Node) : List (Pc × ESite) :=
  (p.pcs n).flatMap fun pc => (p.sites n pc).map fun s => (pc, s)

/-- The per-root mark sets `S_E` of the flow-insensitive scan, with the D1
correction. A cube of one literal (or none) is evaluated on `S_E`, as the
engine evaluates it on a single fact within one context. A cube of two or
more literals is evaluated on `U(n) = ⋃ {S_E' | E' root, E' reaches n}`,
because the engine joins facts across contexts at one statement
(`TaintSinkTracker` assumptions are keyed by `(rule, statement)`).
`InS p E m` means `m ∈ S_E`. -/
inductive InS (p : Program) : Node → Mark → Prop
  | single {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → c.length ≤ 1 →
      (∀ m, m ∈ c → InS p E m) →
      g ∈ σ.abstract.gens → InS p E g
  | joined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → 2 ≤ c.length →
      (w : Mark → Node) →
      (∀ m, m ∈ c → w m ∈ p.roots) → (∀ m, m ∈ c → Reaches p (w m) n) →
      (∀ m, m ∈ c → InS p (w m) m) →
      g ∈ σ.abstract.gens → InS p E g

/-- The cube `c` of a site at node `n` is satisfiable in the mark-set
semantics. -/
def CubeSat (p : Program) (n : Node) (c : Cube) : Prop :=
  (c.length ≤ 1 ∧ ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ ∀ m, m ∈ c → InS p E m) ∨
  (2 ≤ c.length ∧ ∀ m, m ∈ c → ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ InS p E m)

/-- The site `σ` at `(n, pc)` is applicable: the shallow scan must select it. -/
def Applicable (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧ CubeSat p n c

/-- Marks needed by the full scan (the backward relevance pass). They start
from the condition atoms and the `trackFactsReachAnalysisEnd` marks of
applicable sinks, and close backward over applicable sites that generate a
needed mark. -/
inductive Needed (p : Program) : Mark → Prop
  | sinkAtom {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      Applicable p n pc σ → σ.kind = .sink → m ∈ σ.abstract.cond.atoms → Needed p m
  | sinkGen {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      Applicable p n pc σ → σ.kind = .sink → m ∈ σ.abstract.gens → Needed p m
  | trans {n : Node} {pc : Pc} {σ : ESite} {g m : Mark} :
      Applicable p n pc σ → g ∈ σ.abstract.gens → Needed p g →
      m ∈ σ.abstract.cond.atoms → Needed p m

/-! ## 5. The engine model (reference semantics)

`PE p sel n d0 pc d` is an IFDS path edge: in node `n`, under the entry fact
`d0` (`none` is the zero context), the fact `d` (`none` is the zero fact) holds
at statement `pc`. `sel` is the rule selection installed for the full scan.
Pass-through copies and kills are never restricted. -/

/-- A rule selection. `site` enables a rule instance (for sinks, this
restricts where they are checked). `act` enables its individual
`AssignMark` actions. -/
structure Sel where
  site : Node → Pc → ESite → Bool
  act : Node → Pc → ESite → Fact → Bool

def Sel.all : Sel := ⟨fun _ _ _ => true, fun _ _ _ _ => true⟩

def killsOpt (p : Program) (n : Node) (pc : Pc) : Option Fact → Bool
  | none => false
  | some f => p.kills n pc f

abbrev Ctx := Option Fact

/-- The engine model.
* Generated facts appear at the rule's own statement and flow on through the
  CFG.
* A cube with no positive literal fires in every context that reaches the
  statement.
* A single-literal cube fires on one fact and keeps that fact's context.
* A joined cube may use facts from different contexts. Its facts are placed in
  the zero context, which is delivered to every caller; this over-approximates
  the engine's non-distributive edges. -/
inductive PE (p : Program) (sel : Sel) : Node → Ctx → Pc → Option Fact → Prop
  | root {r : Node} : r ∈ p.roots → PE p sel r none 0 none
  | intra {n : Node} {d0 : Ctx} {pc pc' : Pc} {d : Option Fact} :
      PE p sel n d0 pc d → pc' ∈ p.succ n pc → killsOpt p n pc d = false →
      PE p sel n d0 pc' d
  | callZero {n c : Node} {d0 : Ctx} {pc : Pc} :
      PE p sel n d0 pc none → c ∈ p.calls n pc → PE p sel c none 0 none
  | callFact {n c : Node} {d0 : Ctx} {pc : Pc} {f : Fact} {b : Base} :
      PE p sel n d0 pc (some f) → c ∈ p.calls n pc → p.mapIn n pc f.base = some b →
      p.kills n pc f = false →
      PE p sel c (some ⟨b, f.mark⟩) 0 (some ⟨b, f.mark⟩)
  | retZero {n c : Node} {d0 : Ctx} {pc pc' ex : Pc} {g : Fact} {b : Base} :
      PE p sel n d0 pc none → c ∈ p.calls n pc →
      PE p sel c none ex (some g) → ex ∈ p.exits c →
      p.mapOut n pc g.base = some b → pc' ∈ p.succ n pc →
      PE p sel n d0 pc' (some ⟨b, g.mark⟩)
  | retFact {n c : Node} {d0 : Ctx} {pc pc' ex : Pc} {f g : Fact} {bi b : Base} :
      PE p sel n d0 pc (some f) → c ∈ p.calls n pc →
      p.mapIn n pc f.base = some bi → p.kills n pc f = false →
      PE p sel c (some ⟨bi, f.mark⟩) ex (some g) → ex ∈ p.exits c →
      p.mapOut n pc g.base = some b → pc' ∈ p.succ n pc →
      PE p sel n d0 pc' (some ⟨b, g.mark⟩)
  | genEmpty {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} {σ : ESite} {c : ECube} {a : Fact} :
      σ ∈ p.sites n pc → sel.site n pc σ = true → c ∈ σ.cond → c.positive = [] →
      a ∈ σ.assigns → sel.act n pc σ a = true →
      PE p sel n d0 pc d → PE p sel n d0 pc (some a)
  | genSingle {n : Node} {d0 : Ctx} {pc : Pc} {σ : ESite} {c : ECube} {f a : Fact} :
      σ ∈ p.sites n pc → sel.site n pc σ = true → c ∈ σ.cond → c.positive = [f] →
      a ∈ σ.assigns → sel.act n pc σ a = true →
      PE p sel n d0 pc (some f) → PE p sel n d0 pc (some a)
  | genJoined {n : Node} {pc : Pc} {σ : ESite} {c : ECube} {a : Fact} :
      σ ∈ p.sites n pc → sel.site n pc σ = true → c ∈ σ.cond → 2 ≤ c.positive.length →
      a ∈ σ.assigns → sel.act n pc σ a = true →
      (w : Fact → Ctx) → (∀ f, f ∈ c.positive → PE p sel n (w f) pc (some f)) →
      PE p sel n none pc none → PE p sel n none pc (some a)
  | copy {n : Node} {d0 : Ctx} {pc : Pc} {σ : ESite} {fr to : Base} {m : Mark} :
      σ ∈ p.sites n pc → σ.kind = .passThrough → (fr, to) ∈ σ.copies →
      PE p sel n d0 pc (some ⟨fr, m⟩) → PE p sel n d0 pc (some ⟨to, m⟩)

/-- The cube `c` holds at `(n, pc)` in the engine model under selection `sel`. -/
def ECubeHolds (p : Program) (sel : Sel) (n : Node) (pc : Pc) (c : ECube) : Prop :=
  (c.positive = [] ∧ ∃ (d0 : Ctx) (d : Option Fact), PE p sel n d0 pc d) ∨
  (∃ f, c.positive = [f] ∧ ∃ d0 : Ctx, PE p sel n d0 pc (some f)) ∨
  (2 ≤ c.positive.length ∧ ∀ f, f ∈ c.positive → ∃ d0 : Ctx, PE p sel n d0 pc (some f))

/-- A sink finding: the sink `σ` at `(n, pc)` fires. -/
def Fires (p : Program) (sel : Sel) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ σ.kind = .sink ∧ sel.site n pc σ = true ∧
  ∃ c, c ∈ σ.cond ∧ ECubeHolds p sel n pc c

/-- The selection the shallow scan installs, given decidable over-approximations
`app` of `Applicable` and `need` of `Needed`. -/
def Sel.ofScan (app : Node → Pc → ESite → Bool) (need : Mark → Bool) : Sel :=
  { site := fun n pc σ => σ.kind == .passThrough || app n pc σ
    act := fun n pc σ a => app n pc σ && need a.mark }

end MarkScan
