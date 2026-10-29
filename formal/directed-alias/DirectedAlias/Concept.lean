import DirectedAlias.Concrete

/-!
# Concept C: directed points-to semantics (brief §2.2)

An abstract state maps each variable to a set of origins, and each (origin, cell) to a set
of origins. Sets are lists. The heap is keyed by origin, not by an alias group.
The analysis is a forward transfer over the structured program.
A loop uses bounded iteration with a decidable post-fixpoint check over a finite universe.
If the fuel runs out, the loop result is the top state over the universe.
-/

namespace DirectedAlias

/-- The base of a symbolic origin. -/
inductive ABase where
  | root (r : Root)
  | fresh (s : Site)
  deriving DecidableEq, Repr

/-- An abstract object (origin). Null is no origin. -/
inductive Origin where
  /-- The entry object at abstract path `p` below base `b`. The length of `p` is at most `K`. -/
  | sym (b : ABase) (p : List ACell)
  /-- All entry objects below base `b` deeper than `K` (A3). -/
  | deep (b : ABase)
  /-- All objects of allocation site `s`. -/
  | alloc (s : Site)
  /-- All havoc objects of call site `s`, and all objects below them. -/
  | havoc (s : Site)
  /-- Strict A2 only (`Sound/Havoc`): the object that call site `s` writes into cell `c` of an
  object with key `key`, at abstract path `p` below it. The length of `p` is at most `K`.
  Concept C does not use it. -/
  | hsym (s : Site) (key : Origin) (c : ACell) (p : List ACell)
  /-- Strict A2 only: all objects below a per-cell havoc object deeper than `K`. -/
  | hdeep (s : Site) (key : Origin) (c : ACell)
  deriving DecidableEq, Repr

/-- An origin is outer when code outside the method can know its objects. Only `alloc` is not. -/
def Origin.outer : Origin → Bool
  | .alloc _ => false
  | _ => true

/-- A symbolic origin at path `q`, or the deep summary if `q` is longer than `K`. -/
def symOrDeep (K : Nat) (b : ABase) (q : List ACell) : Origin :=
  if q.length ≤ K then .sym b q else .deep b

/-- The abstraction of a concrete object, with field-depth limit `K`. -/
def alpha (K : Nat) : Obj → Origin
  | .sym (.root r) p => symOrDeep K (.root r) (p.map Cell.abs)
  | .sym (.fresh s _) p => symOrDeep K (.fresh s) (p.map Cell.abs)
  | .sym (.havoc s _ _) _ => .havoc s
  | .alloc s _ => .alloc s

/-- The abstraction of a concrete value: null gives no origin. -/
def alphaV (K : Nat) : Val → List Origin
  | none => []
  | some o => [alpha K o]

/-- The default abstract content of a cell. It matches `cdefault` (see `alphaV_cdefault`). -/
def adefault (K : Nat) : Origin → ACell → List Origin
  | .sym b q, c => [symOrDeep K b (q ++ [c])]
  | .deep b, _ => [.deep b]
  | .alloc _, _ => []
  | .havoc s, _ => [.havoc s]
  | .hsym s k c q, c' => [if (q ++ [c']).length ≤ K then .hsym s k c (q ++ [c']) else .hdeep s k c]
  | .hdeep s k c, _ => [.hdeep s k c]

/-- An origin is unique when it denotes at most one concrete object in one execution:
a symbolic path without array elements on a base that runs once, or an allocation site
that runs once. A deep or havoc origin is never unique. If `entryUnique` is false,
a symbolic origin is never unique (the intended policy of today's DSU for outer bases). -/
def Origin.uniqueB (once : Site → Bool) (entryUnique : Bool := true) : Origin → Bool
  | .sym (.root _) q => entryUnique && !(q.contains .elem)
  | .sym (.fresh s) q => entryUnique && once s && !(q.contains .elem)
  | .deep _ => false
  | .alloc s => once s
  | .havoc _ => false
  | .hsym _ _ _ _ => false
  | .hdeep _ _ _ => false

/-- An abstract state. -/
structure AState where
  env : Var → List Origin
  heap : Origin → ACell → List Origin

/-- The analysis context: depth limit, the `once` test of sites, the finite universe
(cells, variables, origins) of the check, and the loop fuel. -/
structure Ctx where
  K : Nat
  once : Site → Bool
  cells : List ACell
  vars : List Var
  origins : List Origin
  fuel : Nat
  /-- The strong-update policy for symbolic origins. If true (A1), a unique entry or fresh
  symbolic origin gets strong updates. If false (the intended policy of today's DSU for outer bases), only an
  allocation of a once site gets strong updates. -/
  entryUnique : Bool := true

/-! ## Finite universe -/

/-- All abstract paths over `cells` with length at most `n`. -/
def pathsUpTo (cells : List ACell) : Nat → List (List ACell)
  | 0 => [[]]
  | n + 1 => [] :: cells.flatMap (fun c => (pathsUpTo cells n).map (c :: ·))

/-- The abstract cell universe of a field list: its fields and the array element. -/
def cellsOf (fs : List Field) : List ACell :=
  fs.eraseDups.map ACell.fld ++ [.elem]

/-- The origin universe of a program: symbolic paths up to `K` and deep summaries of each base,
allocation sites, and havoc sites. -/
def originsOf (K : Nat) (fr : Frame) (p : Prog) (cells : List ACell) : List Origin :=
  let bases := fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh
  bases.flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.map Origin.alloc ++ p.callSites.map Origin.havoc

/-- The context of program `p` with frame `fr`, depth limit `K`, and extra query fields `qf`.
The fuel is large enough for all strict increases of a state over the universe. -/
def Ctx.ofProg (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  let cells := cellsOf (p.fields ++ qf)
  let vars := (p.vars ++ fr.vars).eraseDups
  let origins := originsOf K fr p cells
  { K := K, once := p.onceB, cells := cells, vars := vars, origins := origins,
    fuel := (vars.length + origins.length * cells.length) * origins.length + 1 }

/-! ## State operations -/

/-- The entry abstract state of a frame. -/
def ainit (K : Nat) (fr : Frame) : AState where
  env := fun x => match fr.root? x with
    | some r => [.sym (.root r) []]
    | none => []
  heap := adefault K

/-- Set variable `x` to the origins `S`. -/
def AState.setVar (X : AState) (x : Var) (S : List Origin) : AState :=
  { X with env := fupd X.env x S }

/-- Set the optional result variable `ret` to the origins `S`. -/
def AState.setRet (X : AState) (ret : Option Var) (S : List Origin) : AState :=
  match ret with
  | none => X
  | some x => X.setVar x S

/-- Strong update: set cell `c` of origin `o` to `S`. -/
def AState.setCell (X : AState) (o : Origin) (c : ACell) (S : List Origin) : AState :=
  { X with heap := fupd2 X.heap o c S }

/-- Weak update: add `S` to cell `c` of each origin in `os`. -/
def AState.weakStore (X : AState) (os : List Origin) (c : ACell) (S : List Origin) : AState :=
  { X with heap := fun o c' => if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c' }

/-- Store `S` into cell `c` through variable `x`: strong if `x` has exactly one origin and it is
unique, otherwise weak. -/
def AState.store (once : Site → Bool) (X : AState) (x : Var) (c : ACell) (S : List Origin)
    (entryUnique : Bool := true) : AState :=
  match single? (X.env x) with
  | some o => if o.uniqueB once entryUnique then X.setCell o c S else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The origins in cell `c` of the origins `S`. -/
def aread (X : AState) (S : List Origin) (c : ACell) : List Origin :=
  uniMap (fun o => X.heap o c) S

/-- The origins in all universe cells of the origins `R`. -/
def succs (cells : List ACell) (X : AState) (R : List Origin) : List Origin :=
  uniMap (fun o => uniMap (X.heap o) cells) R

/-- Close `R` under `succs`. The result is `none` if the fuel runs out. -/
def closeIter (cells : List ACell) (X : AState) : Nat → List Origin → Option (List Origin)
  | 0, _ => none
  | n + 1, R =>
    if subB (succs cells X R) R then some R else closeIter cells X n (uni (succs cells X R) R)

/-- The origins that a call with arguments `args` can reach: all outer origins, and the closure of
the arguments and the outer universe origins. If the closure fails, every origin. -/
def reachB (ctx : Ctx) (X : AState) (args : List Var) : Origin → Bool :=
  match closeIter ctx.cells X (ctx.origins.length + 1)
      (uni (uniMap X.env args) (ctx.origins.filter Origin.outer)) with
  | some R => fun o => o.outer || decide (o ∈ R)
  | none => fun _ => true

/-- Weak havoc of call site `s`: add `havoc s` to each universe cell of each reachable origin. -/
def AState.havoc (ctx : Ctx) (X : AState) (args : List Var) (s : Site) : AState :=
  let r := reachB ctx X args
  { X with heap := fun o c =>
      if c ∈ ctx.cells ∧ r o = true then uni [.havoc s] (X.heap o c) else X.heap o c }

/-- The abstract transfer of one statement. -/
def astep (ctx : Ctx) : Stmt → AState → AState
  | .new x s, X => X.setVar x [.alloc s]
  | .null x, X => X.setVar x []
  | .copy x y, X => X.setVar x (X.env y)
  | .load x y f, X => X.setVar x (aread X (X.env y) (.fld f))
  | .store x f y, X => X.store ctx.once x (.fld f) (X.env y) ctx.entryUnique
  | .aload x y, X => X.setVar x (aread X (X.env y) .elem)
  | .astore x y, X => X.weakStore (X.env x) .elem (X.env y)
  | .unknown x s, X => X.setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (X.havoc ctx args s).setRet ret [.sym (.fresh s) []]

/-- Pointwise union of two abstract states. -/
def join (X Y : AState) : AState where
  env := fun x => uni (X.env x) (Y.env x)
  heap := fun o c => uni (X.heap o c) (Y.heap o c)

/-- Pointwise inclusion of abstract states, on all variables and cells. -/
def AState.Sub (X Y : AState) : Prop :=
  (∀ x, X.env x ⊆ Y.env x) ∧ ∀ o c, X.heap o c ⊆ Y.heap o c

/-- Boolean inclusion of abstract states on the universe of the context. -/
def leOn (ctx : Ctx) (X Y : AState) : Bool :=
  ctx.vars.all (fun x => subB (X.env x) (Y.env x)) &&
    ctx.origins.all (fun o => ctx.cells.all (fun c => subB (X.heap o c) (Y.heap o c)))

/-- The top state above `Y`: add every universe origin to every variable and cell. -/
def top (ctx : Ctx) (Y : AState) : AState where
  env := fun x => uni ctx.origins (Y.env x)
  heap := fun o c => uni ctx.origins (Y.heap o c)

/-- Loop iteration: stop at the first post-fixpoint on the universe, or give the top state
when the fuel runs out. -/
def loopIter (ctx : Ctx) (f : AState → AState) : Nat → AState → AState
  | 0, Y => top ctx Y
  | n + 1, Y => if leOn ctx (f Y) Y then Y else loopIter ctx f n (join Y (f Y))

/-- The abstract analysis of a program. -/
def analyze (ctx : Ctx) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astep ctx s X
  | .seq p q, X => analyze ctx q (analyze ctx p X)
  | .choice p q, X => join (analyze ctx p X) (analyze ctx q X)
  | .loop p, X => loopIter ctx (analyze ctx p) ctx.fuel X

/-! ## Queries -/

/-- Abstract evaluation of a path from a set of origins. -/
def aevalFrom (X : AState) : List Origin → List ACell → List Origin
  | S, [] => S
  | S, c :: cs => aevalFrom X (aread X S c) cs

/-- Abstract evaluation of access path `x.p`. -/
def aevalPath (X : AState) (x : Var) (p : List ACell) : List Origin :=
  aevalFrom X (X.env x) p

/-- May-alias: the two paths have a common origin. -/
def may (X : AState) (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  meetB (aevalPath X x px) (aevalPath X y py)

/-- The fields of an abstract path. -/
def afields (p : List ACell) : List Field :=
  p.filterMap (fun c => match c with | .fld f => some f | .elem => none)

/-- The context of a program, with the query fields `qf` in the universe. -/
def progCtx (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  Ctx.ofProg K fr p qf

/-- The final abstract state of program `p` from frame `fr`. -/
def analyzeProg (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : AState :=
  analyze (progCtx K fr p qf) p (ainit K fr)

/-- May-alias at the end of program `p`. The query fields are in the universe. -/
def mayProg (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProg K fr p (afields px ++ afields py)) x px y py

/-! ## Target statements for the proof agents -/

/-- C-sound with depth limit `K`: each one-execution alias is a may-alias. -/
def CSound (K : Nat) : Prop :=
  ∀ (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell),
    CAlias fr p x px y py → mayProg K fr p x (px.map Cell.abs) y (py.map Cell.abs) = true

/-- C-complete with depth limit `K` in a scope: each may-alias has concrete paths that abstract
to the query paths and that alias across two executions. -/
def CCompleteIn (K : Nat) (scope : Frame → Prog → List ACell → List ACell → Prop) : Prop :=
  ∀ (fr : Frame) (p : Prog) (x : Var) (px : List ACell) (y : Var) (py : List ACell),
    scope fr p px py → mayProg K fr p x px y py = true →
      ∃ cx cy, cx.map Cell.abs = px ∧ cy.map Cell.abs = py ∧ CAliasX fr p x cx y cy

/-! ## Small lemmas -/

/-- The abstraction of a default child is the abstract default content of the parent. -/
theorem alphaV_cdefault (K : Nat) (o : Obj) (c : Cell) :
    alphaV K (cdefault o c) = adefault K (alpha K o) c.abs := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | havoc s n k => rfl
    | root r =>
      simp only [cdefault, alphaV, alpha, symOrDeep, List.map_append, List.length_append,
        List.length_map, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      by_cases h : p.length ≤ K
      · simp [h, adefault, symOrDeep]
      · have h2 : ¬ p.length + 1 ≤ K := by omega
        simp [h, h2, adefault]
    | fresh s n =>
      simp only [cdefault, alphaV, alpha, symOrDeep, List.map_append, List.length_append,
        List.length_map, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      by_cases h : p.length ≤ K
      · simp [h, adefault, symOrDeep]
      · have h2 : ¬ p.length + 1 ≤ K := by omega
        simp [h, h2, adefault]

/-- The entry abstract state abstracts the entry concrete state on each variable. -/
theorem alphaV_init_env (K : Nat) (fr : Frame) (x : Var) :
    alphaV K ((CState.init fr).env x) = (ainit K fr).env x := by
  simp only [CState.init, ainit]
  cases fr.root? x with
  | none => rfl
  | some r => simp [alphaV, alpha, symOrDeep]

/-- Membership in `aread`. -/
theorem mem_aread {X : AState} {S : List Origin} {c : ACell} {o' : Origin} :
    o' ∈ aread X S c ↔ ∃ o ∈ S, o' ∈ X.heap o c := by
  simp [aread, mem_uniMap]

/-- Membership in `succs`. -/
theorem mem_succs {cells : List ACell} {X : AState} {R : List Origin} {o' : Origin} :
    o' ∈ succs cells X R ↔ ∃ o ∈ R, ∃ c ∈ cells, o' ∈ X.heap o c := by
  simp [succs, mem_uniMap]

/-- A result of `closeIter` contains the start set and is closed under `succs`. -/
theorem closeIter_spec {cells : List ACell} {X : AState} :
    ∀ {n : Nat} {R0 R : List Origin}, closeIter cells X n R0 = some R →
      (∀ o ∈ R0, o ∈ R) ∧ ∀ o ∈ succs cells X R, o ∈ R
  | 0, R0, R, h => by simp [closeIter] at h
  | n + 1, R0, R, h => by
    simp only [closeIter] at h
    split at h
    · rename_i hs
      cases h
      exact ⟨fun _ h => h, subB_iff.mp hs⟩
    · obtain ⟨h1, h2⟩ := closeIter_spec h
      exact ⟨fun o ho => h1 o (mem_uni.mpr (Or.inr ho)), h2⟩

/-- `may` is true if and only if the two abstract paths have a common origin. -/
theorem may_iff {X : AState} {x y : Var} {px py : List ACell} :
    may X x px y py = true ↔ ∃ o, o ∈ aevalPath X x px ∧ o ∈ aevalPath X y py :=
  meetB_iff

/-- `may` is symmetric. -/
theorem may_comm (X : AState) (x : Var) (px : List ACell) (y : Var) (py : List ACell) :
    may X x px y py = may X y py x px :=
  meetB_comm _ _

/-- `leOn` is true if and only if inclusion holds on the universe. -/
theorem leOn_iff {ctx : Ctx} {X Y : AState} :
    leOn ctx X Y = true ↔
      (∀ x ∈ ctx.vars, X.env x ⊆ Y.env x) ∧
      ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, X.heap o c ⊆ Y.heap o c := by
  simp only [leOn, Bool.and_eq_true, List.all_eq_true, subB_iff]
  rfl

/-- Inclusion of states is reflexive. -/
theorem AState.Sub.refl (X : AState) : X.Sub X :=
  ⟨fun _ _ h => h, fun _ _ _ h => h⟩

/-- Inclusion of states is transitive. -/
theorem AState.Sub.trans {X Y Z : AState} (h1 : X.Sub Y) (h2 : Y.Sub Z) : X.Sub Z :=
  ⟨fun x _ h => h2.1 x (h1.1 x h), fun o c _ h => h2.2 o c (h1.2 o c h)⟩

/-- The left state is included in the join. -/
theorem sub_join_left (X Y : AState) : X.Sub (join X Y) :=
  ⟨fun _ _ h => mem_uni.mpr (Or.inl h), fun _ _ _ h => mem_uni.mpr (Or.inl h)⟩

/-- The right state is included in the join. -/
theorem sub_join_right (X Y : AState) : Y.Sub (join X Y) :=
  ⟨fun _ _ h => mem_uni.mpr (Or.inr h), fun _ _ _ h => mem_uni.mpr (Or.inr h)⟩

/-- A state is included in its top state. -/
theorem sub_top (ctx : Ctx) (Y : AState) : Y.Sub (top ctx Y) :=
  ⟨fun _ _ h => mem_uni.mpr (Or.inr h), fun _ _ _ h => mem_uni.mpr (Or.inr h)⟩

/-- The loop result includes the loop entry state. -/
theorem sub_loopIter (ctx : Ctx) (f : AState → AState) :
    ∀ (n : Nat) (Y : AState), Y.Sub (loopIter ctx f n Y)
  | 0, Y => sub_top ctx Y
  | n + 1, Y => by
    simp only [loopIter]
    split
    · exact AState.Sub.refl Y
    · exact (sub_join_left Y (f Y)).trans (sub_loopIter ctx f n _)

/-- The loop result is a post-fixpoint on the universe, or a top state. -/
theorem loopIter_post (ctx : Ctx) (f : AState → AState) :
    ∀ (n : Nat) (Y : AState),
      leOn ctx (f (loopIter ctx f n Y)) (loopIter ctx f n Y) = true ∨
      ∃ W, loopIter ctx f n Y = top ctx W
  | 0, Y => Or.inr ⟨Y, rfl⟩
  | n + 1, Y => by
    simp only [loopIter]
    split
    · rename_i h; exact Or.inl h
    · exact loopIter_post ctx f n _

/-- Membership in `pathsUpTo`: the path is short enough and uses only universe cells. -/
theorem mem_pathsUpTo {cells : List ACell} :
    ∀ {n : Nat} {q : List ACell}, q ∈ pathsUpTo cells n ↔ q.length ≤ n ∧ ∀ c ∈ q, c ∈ cells
  | 0, q => by
    cases q with
    | nil => simp [pathsUpTo]
    | cons c cs => simp [pathsUpTo]
  | n + 1, q => by
    cases q with
    | nil => simp [pathsUpTo]
    | cons c cs =>
      simp only [pathsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map,
        List.cons.injEq, List.length_cons, reduceCtorEq, false_or]
      constructor
      · rintro ⟨c', hc', q', hq', rfl, rfl⟩
        obtain ⟨h1, h2⟩ := (mem_pathsUpTo (n := n)).mp hq'
        refine ⟨by omega, ?_⟩
        intro d hd
        cases hd with
        | inl h => exact h ▸ hc'
        | inr h => exact h2 d h
      · rintro ⟨h1, h2⟩
        exact ⟨c, h2 c (Or.inl rfl), cs,
          (mem_pathsUpTo (n := n)).mpr ⟨by omega, fun d hd => h2 d (Or.inr hd)⟩,
          rfl, rfl⟩

end DirectedAlias
