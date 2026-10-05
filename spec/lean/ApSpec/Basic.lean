/-
  ApSpec.Basic — the formal model of the access path (AP) and its operations.

  All definitions are executable. All proofs in this project are constructive:
  only `propext` and `Quot.sound` are permitted (audit with `#print axioms`).

  Reading guide (the spec `spec/ap.md` uses the same names):
    * `Loc`      a concrete marked location: the value at `base.path` carries `mark`.
    * `PFact`    a path fact: (base, path, tail kind, mark). The CONCEPT of a fact.
    * `AFact`    a final path fact plus the LAYER of its edge: `demand = true` is
                 the demand layer (`~`, `Zero~`); every approximation step sets it.
    * `den`      the pair relation of an edge (initial fact -> final fact).
    * `applyEdge` the ONE core operation (delta-concat). It applies a statement
                 micro edge, a call binding edge, or a callee summary edge.
    * `Flow`     the concrete (alias-free, location-level) data flow.
    * `D`        the abstract analysis result: the least set of objects closed
                 under the analysis rules.
-/
namespace ApSpec

abbrev Acc      := Nat
abbrev Base     := Nat
abbrev Mark     := Nat
abbrev MethodId := Nat
abbrev Node     := Nat

/-! ## 1. Concrete level -/

/-- A concrete marked location: the value at `base.path` carries `mark`. -/
structure Loc where
  base : Base
  path : List Acc
  mark : Mark
deriving DecidableEq, Repr

/-- Constructive membership test on accessor lists. -/
def memB (a : Acc) : List Acc → Bool
  | []      => false
  | b :: bs => Nat.beq a b || memB a bs

/-! ## 2. Exclusions -/

/-- Exclusion set of an abstract tail `*`: it excludes the FIRST accessor of a
    non-empty continuation. `set []` is Empty, `univ` is Universe (only the
    empty continuation stays). -/
inductive Excl where
  | set  (xs : List Acc)
  | univ
deriving DecidableEq, Repr

def Excl.empty : Excl := .set []

/-- `e.admits σ`: the continuation `σ` is not excluded. -/
def Excl.admits : Excl → List Acc → Bool
  | _,       []     => true
  | .univ,   _ :: _ => false
  | .set xs, a :: _ => !(memB a xs)

def Excl.union : Excl → Excl → Excl
  | .univ,   _       => .univ
  | .set _,  .univ   => .univ
  | .set xs, .set ys => .set (xs ++ ys)

def Excl.inter : Excl → Excl → Excl
  | .univ,   e       => e
  | .set xs, .univ   => .set xs
  | .set xs, .set ys => .set (xs.filter (fun a => memB a ys))

/-- `e1.subB e2`: e2 excludes at least what e1 excludes
    (so `e2.admits σ → e1.admits σ`). -/
def Excl.subB : Excl → Excl → Bool
  | _,       .univ   => true
  | .univ,   .set _  => false
  | .set xs, .set ys => xs.all (fun a => memB a ys)

def Excl.isEmptyB : Excl → Bool
  | .set []      => true
  | .set (_ :: _) => false
  | .univ        => false

/-! ## 3. Facts -/

/-- The tail kind of a fact path:
    * `star e` — abstract `*`: every continuation admitted by `e`. On a final
      fact it is CORRELATED with the continuation of the initial fact.
    * `any`    — `[any]`: every continuation, not correlated.
    * `exact`  — `$`: the empty continuation only. -/
inductive Kind where
  | star (e : Excl)
  | any
  | exact
deriving DecidableEq, Repr

/-- Taint mark: `star` = abstract (pass the mark of the initial fact through),
    `conc t` = the concrete mark `t`. -/
inductive MarkA where
  | star
  | conc (t : Mark)
deriving DecidableEq, Repr

/-- A path fact: the concept of a fact. -/
structure PFact where
  base : Base
  path : List Acc
  kind : Kind
  mark : MarkA
deriving DecidableEq, Repr

/-- A final path fact with the layer of its edge. `demand = true` (the `~` layer)
    means that some step of its derivation over-approximated. The flag never goes
    back to `false`. -/
structure AFact where
  fact   : PFact
  demand : Bool
deriving DecidableEq, Repr

/-! ## 4. Denotation -/

/-- Admitted continuation of a fact read as a PREMISE (initial fact). -/
def tailI : Kind → List Acc → Prop
  | .star e, σ => e.admits σ = true
  | .any,    _ => True
  | .exact,  σ => σ = []

/-- Continuation relation of a final fact: `σ` is the continuation of the
    initial fact, `τ` the continuation of the final fact. -/
def tailF : Kind → List Acc → List Acc → Prop
  | .star e, σ, τ => τ = σ ∧ e.admits σ = true
  | .any,    _, _ => True
  | .exact,  _, τ => τ = []

def MarkA.admits : MarkA → Mark → Prop
  | .star,   _ => True
  | .conc t, m => m = t

def MarkA.out : MarkA → Mark → Mark
  | .star,   m => m
  | .conc t, _ => t

/-- The location set of a fact read as a premise. -/
def PFact.covers (i : PFact) (l : Loc) : Prop :=
  l.base = i.base ∧ (∃ σ, l.path = i.path ++ σ ∧ tailI i.kind σ) ∧ i.mark.admits l.mark

/-- The pair relation of an edge `i → f`: the value at `l0` on method entry
    flows to `l1` at the edge's statement. -/
def den (i f : PFact) (l0 l1 : Loc) : Prop :=
  l0.base = i.base ∧ l1.base = f.base ∧ i.mark.admits l0.mark ∧
  l1.mark = f.mark.out l0.mark ∧
  ∃ σ τ, l0.path = i.path ++ σ ∧ l1.path = f.path ++ τ ∧ tailI i.kind σ ∧ tailF f.kind σ τ

/-! ## 5. Path utilities -/

/-- `dropPrefix p q = some r` iff `q = p ++ r`. -/
def dropPrefix : List Acc → List Acc → Option (List Acc)
  | [],     q      => some q
  | _ :: _, []     => none
  | a :: p, b :: q => if Nat.beq a b then dropPrefix p q else none

/-- Relative position of a fact path `q` against a premise path `p`. -/
inductive Rel where
  | below (r : List Acc)  -- q = p ++ r   (fact at or below the premise)
  | above (r : List Acc)  -- p = q ++ r, r ≠ []  (fact above the premise)
  | apart
deriving Repr

def relate (p q : List Acc) : Rel :=
  match dropPrefix p q with
  | some r => .below r
  | none   =>
    match dropPrefix q p with
    | some r => .above r
    | none   => .apart

/-- Boolean form of `tailI k r` (decides if the tail admits continuation `r`). -/
def admitsTailB : Kind → List Acc → Bool
  | .star e, r      => e.admits r
  | .any,    _      => true
  | .exact,  []     => true
  | .exact,  _ :: _ => false

/-- The exclusion that a premise tail imposes on the empty relative position. -/
def tailExcl : Kind → Excl
  | .star e => e
  | .any    => Excl.empty
  | .exact  => .univ

def Kind.isStar : Kind → Bool
  | .star _ => true
  | _       => false

def Kind.isAny : Kind → Bool
  | .any => true
  | _    => false

/-! ## 6. The core operation: applyEdge (delta-concat) -/

/-- Result of an operation: new final facts and mark requests. -/
structure Res where
  facts : List AFact
  reqs  : List Mark
deriving Repr

def Res.none : Res := ⟨[], []⟩

def Res.append (a b : Res) : Res := ⟨a.facts ++ b.facts, a.reqs ++ b.reqs⟩

/-- The mark of a result: `star` on the target passes the fact mark through. -/
def markOutA : MarkA → MarkA → MarkA
  | .star,   m => m
  | .conc t, _ => .conc t

/-- Mark gate of a premise mark against a fact mark. -/
inductive Gate where
  | ok
  | no
  | req (t : Mark)

def markGate : MarkA → MarkA → Gate
  | .star,   _        => .ok
  | .conc t, .conc t' => if Nat.beq t t' then .ok else .no
  | .conc t, .star    => .req t

/-- The correlation constraint that an uncorrelated result forgets. A correlated
    `*` fact restricts the initial continuation `σ0` by its own exclusion, and (at
    the premise position, `r = []`) by the premise tail. The result is exact iff
    that restriction is empty. -/
def lostCorr (ck fk : Kind) (r : List Acc) : Bool :=
  match ck, r with
  | .star ec, []     => !(ec.union (tailExcl fk)).isEmptyB
  | .star ec, _ :: _ => !ec.isEmptyB
  | _,        _      => false

/-- Case `below r`: the fact `c` (kind `ck`) is at or below the premise.
    Returns the result path, kind and approximation (demand) bit, or `none` if the
    location sets do not overlap. -/
def belowCase (ck fk : Kind) (r : List Acc) (toPath : List Acc) (tk : Kind) :
    Option (List Acc × Kind × Bool) :=
  if admitsTailB fk r then
    match tk with
    | .star et =>
      match r with
      | _ :: _ =>
        if et.admits r then some (toPath ++ r, ck, false) else none
      | [] =>
        let ex := (tailExcl fk).union et
        match ck, ex with
        | .exact,   _     => some (toPath, .exact, false)
        | .star ec, _     => some (toPath, .star (ec.union ex), false)
        | .any,     .univ => some (toPath, .exact, false)
        | .any,     _     => some (toPath, .any, !ex.isEmptyB)
    | .any =>
      some (toPath, .any, lostCorr ck fk r)
    | .exact =>
      match ck, fk, r with
      | .star _, .exact, [] => some (toPath, .star .univ, false)
      | .star _, _, _       => some (toPath, .exact, lostCorr ck fk r)
      | _, _, _             => some (toPath, .exact, false)
  else none

/-- Case `above r` (r ≠ []): the fact `c` is above the premise. The correlation
    with the initial continuation is lost, so the result is uncorrelated. -/
def aboveCase (ck fk : Kind) (r : List Acc) (toPath : List Acc) (tk : Kind) :
    Option (List Acc × Kind × Bool) :=
  if admitsTailB ck r then
    match tk with
    | .star et =>
      some (toPath, .any, !(ck.isAny && ((tailExcl fk).union et).isEmptyB))
    | .any   => some (toPath, .any, !ck.isAny)
    | .exact => some (toPath, .exact, !ck.isAny)
  else none

/-- Normal form of a final fact. A final `*` tail needs the mark `*` and
    `demand = false` (rule W2 and the demand-layer invariant). Otherwise the
    correlated `*` becomes uncorrelated: `$` for Universe, `[any]` otherwise,
    and the fact moves to the demand layer. -/
def AFact.norm (f : AFact) : AFact :=
  match f.fact.kind, f.fact.mark, f.demand with
  | .star _, .star, false => f
  | .star .univ, _, _ => ⟨⟨f.fact.base, f.fact.path, .exact, f.fact.mark⟩, true⟩
  | .star (.set _), _, _ => ⟨⟨f.fact.base, f.fact.path, .any, f.fact.mark⟩, true⟩
  | _, _, _ => f

/-- The core operation. Apply the edge `fr → to` (a statement micro edge, a call
    binding edge or a callee summary edge) to the final fact `c`. -/
def applyEdge (c : AFact) (fr to : PFact) : Res :=
  if Nat.beq c.fact.base fr.base then
    let geo : Option (List Acc × Kind × Bool) :=
      match relate fr.path c.fact.path with
      | .below r => belowCase c.fact.kind fr.kind r to.path to.kind
      | .above r => aboveCase c.fact.kind fr.kind r to.path to.kind
      | .apart   => none
    match geo with
    | none => Res.none
    | some (p, k, ap) =>
      match markGate fr.mark c.fact.mark with
      | .no    => Res.none
      | .req t => ⟨[], [t]⟩
      | .ok    => ⟨[AFact.norm ⟨⟨to.base, p, k, markOutA to.mark c.fact.mark⟩, c.demand || ap⟩], []⟩
  else Res.none

/-- Apply a callee summary edge `i → g` (the summary carries the layer of its own edge). -/
def applySummary (a : AFact) (i : PFact) (g : AFact) : Res :=
  let r := applyEdge a i g.fact
  ⟨r.facts.map (fun x => AFact.norm ⟨x.fact, x.demand || g.demand⟩), r.reqs⟩

/-! ## 7. Field limit -/

/-- `cutPath counted n q = some p` if `q` has more than `n` counted accessors;
    `p` is the longest prefix with at most `n` counted accessors. -/
def cutPath (counted : Acc → Bool) : Nat → List Acc → Option (List Acc)
  | _,     []      => none
  | n,     a :: as =>
    if counted a then
      match n with
      | 0     => some []
      | m + 1 => (cutPath counted m as).map (a :: ·)
    else (cutPath counted n as).map (a :: ·)

/-- The field limit: a path over the limit is cut and gets the `[any]` tail. -/
def limitF (counted : Acc → Bool) (L : Nat) (f : AFact) : AFact :=
  match cutPath counted L f.fact.path with
  | none   => f
  | some p => ⟨⟨f.fact.base, p, .any, f.fact.mark⟩, true⟩

/-! ## 8. Statements, calls, programs -/

abbrev MicroEdge := PFact × PFact

/-- A statement is its summary: the bases it touches and its micro edges.
    A touched base keeps only what an edge regenerates. -/
structure Stmt where
  touched : List Base
  edges   : List MicroEdge

def Stmt.step (s : Stmt) (l l' : Loc) : Prop :=
  (memB l.base s.touched = false ∧ l' = l) ∨ (∃ e, e ∈ s.edges ∧ den e.1 e.2 l l')

def applyAll (c : AFact) : List MicroEdge → Res
  | []      => Res.none
  | e :: es => (applyEdge c e.1 e.2).append (applyAll c es)

/-- The statement transfer of one final fact. -/
def transfer (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : AFact) : Res :=
  if memB c.fact.base s.touched then
    let r := applyAll c s.edges
    ⟨r.facts.map (limitF counted L), r.reqs⟩
  else ⟨[c], []⟩

/-- A call: caller bases routed through the callee (arguments, result, statics),
    the binding into the callee and the binding back. -/
structure Call where
  callee     : MethodId
  touched    : List Base
  toCallee   : List MicroEdge
  fromCallee : List MicroEdge

inductive Instr where
  | stmt (s : Stmt)
  | call (c : Call)

structure Program where
  entry : MethodId → Node
  exit  : MethodId → Node
  edges : List (MethodId × Node × Instr × Node)

/-- Well-formedness used by the soundness theorem. -/
structure Program.WF (P : Program) : Prop where
  /-- every micro edge reads from a touched base -/
  stmtTouched : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    ∀ e, e ∈ s.edges → memB e.1.base s.touched = true
  /-- call bindings are mark agnostic -/
  toStar   : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e, e ∈ c.toCallee → e.1.mark = .star
  fromStar : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e, e ∈ c.fromCallee → e.1.mark = .star

/-- Concrete data flow: the value at entry location `l0` of method `M` flows to
    location `l` at node `n`. -/
inductive Flow (P : Program) : MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : Flow P M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      Flow P M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      Flow P M l0 n' l'
  | pass {M l0 n l n' c} :
      Flow P M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → Flow P M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3} :
      Flow P M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      Flow P c.callee l1 (P.exit c.callee) l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      Flow P M l0 n' l3

/-! ## 9. Abstraction helpers -/

/-- Start final fact of an initial fact. A `*` tail with a concrete mark is not
    a legal final fact, so its start is the `[any]` tail (a demand fact). -/
def startFact (i : PFact) : AFact :=
  match i.kind, i.mark with
  | .star _, .star   => ⟨i, false⟩
  | .star _, .conc t => ⟨⟨i.base, i.path, .any, .conc t⟩, true⟩
  | .any,    m       => ⟨⟨i.base, i.path, .any, m⟩, true⟩
  | .exact,  _       => ⟨i, false⟩

/-- Tail inclusion at the same position: c's tail ⊆ i's tail. -/
def tailSubB : Kind → Kind → Bool
  | .star ei, .star ec => ei.subB ec
  | .star _,  .exact   => true
  | .star ei, .any     => ei.isEmptyB
  | .any,     _        => true
  | .exact,   .exact   => true
  | .exact,   .star .univ => true
  | .exact,   _        => false

def markSubB : MarkA → MarkA → Bool
  | .star,   _        => true
  | .conc t, .conc t' => Nat.beq t t'
  | .conc _, .star    => false

/-- `coversB i c`: the location set of `c` is inside the location set of `i`. -/
def coversB (i c : PFact) : Bool :=
  Nat.beq i.base c.base && markSubB i.mark c.mark &&
  match dropPrefix i.path c.path with
  | some []       => tailSubB i.kind c.kind
  | some (a :: r) => admitsTailB i.kind (a :: r)
  | none          => false

/-- `applicable i c`: a summary of initial `i` may be applied to caller fact `c`.
    An `[any]` premise needs an `[any]` caller fact (syntactic [any] rule). -/
def applicable (i c : PFact) : Bool :=
  coversB i c && (!i.kind.isAny || c.kind.isAny)

/-- The location sets of two facts (read as premises) overlap; marks ignored. -/
def overlapB (a b : PFact) : Bool :=
  Nat.beq a.base b.base &&
  match relate a.path b.path with
  | .below r => admitsTailB a.kind r
  | .above r => admitsTailB b.kind r
  | .apart   => false

/-! ## 10. Rules: sinks and mark requests -/

inductive Check where
  | triggered
  | request (t : Mark)
  | none
deriving DecidableEq, Repr

/-- Sink check of the final fact `f` (initial `i`) against the sink pattern `s`
    (`s.mark = conc T`; `s.kind` is `exact` or `any`). -/
def check (i : PFact) (f : AFact) (s : PFact) : Check :=
  match s.mark with
  | .star => .none
  | .conc T =>
    if overlapB f.fact s then
      match f.fact.mark with
      | .conc t => if Nat.beq t T then .triggered else .none
      | .star   =>
        match i.mark with
        | .conc t => if Nat.beq t T then .triggered else .none
        | .star   => .request T
    else .none

/-- The initial fact emitted to answer the request `(i, t)` with the added fact
    `a` (bidirectional-task.md §4). An exact match at the requested chain gives the
    exact fact with the mark `t`. Otherwise the answer keeps the requested chain and
    tail with the mark `t`; its start fact is `[any]` (W2), so it starts in the demand
    layer (the `~` premise). The chain is never deeper than the request: no field chain
    without a demand. -/
def answerInit (i a : PFact) (t : Mark) : PFact :=
  match a.kind, dropPrefix i.path a.path with
  | .exact, some [] => ⟨i.base, i.path, .exact, .conc t⟩
  | _,      _       => ⟨i.base, i.path, i.kind, .conc t⟩

/-- A derived fact is COMPLETE if its edge is in the normal layer and its
    conclusion has no `[any]` tail. Complete edges are persisted and reversed. -/
def AFact.complete (f : AFact) : Bool := !f.demand && !f.fact.kind.isAny

/-! ## 11. The abstract analysis result -/

/-- Objects of the analysis result. -/
inductive Obj where
  | init     (M : MethodId) (i : PFact)
  | edge     (M : MethodId) (i : PFact) (n : Node) (f : AFact)
  | added    (M : MethodId) (a : PFact)
  | req      (M : MethodId) (i : PFact) (t : Mark)
  | vuln     (M : MethodId) (n : Node) (s : PFact) (demand : Bool)

/-- The zero fact: always present, carries the zero mark. Sources are micro
    edges from it. -/
def zeroBase : Base := 0
def zeroMark : Mark := 0
def zeroFact : PFact := ⟨zeroBase, [], .exact, .conc zeroMark⟩
def zeroLoc  : Loc   := ⟨zeroBase, [], zeroMark⟩

section Closure
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The analysis result: the least set of objects closed under the rules.
    `α m a` is the abstraction: the initial fact chosen for added fact `a`. -/
inductive D : Obj → Prop where
  | root {M} : M ∈ roots → D (.init M zeroFact)
  | start {M i} : D (.init M i) → D (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      D (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → D (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      D (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs → D (.req M i t)
  | pass {M i n f n' c} :
      D (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → D (.edge M i n' f)
  | added {M i n f n' c e a} :
      D (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      D (.added c.callee a.fact)
  | initA {m a} : D (.added m a) → D (.init m (α m a))
  -- The caller subscribes to EVERY summary edge whose premise its fact satisfies:
  -- the initial fact selected by the abstraction, the answers of requests, and any
  -- other initial fact of the callee that is applicable to the added fact.
  | ret {M i n f n' c e1 a j g r e2 r'} :
      D (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      D (.init c.callee j) →
      applicable j a.fact = true →
      D (.edge c.callee j (P.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      D (.edge M i n' (limitF counted L r'))
  | reqSink {M i n f s t} :
      D (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      D (.req M i t)
  | answer {M i t a} :
      D (.req M i t) → D (.added M a) → a.mark = .conc t →
      overlapB a i = true → D (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      D (.req m j t) → D (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      a.fact.mark = .star → overlapB a.fact j = true → D (.req M ic t)
  | vuln {M i n f s} :
      D (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      D (.vuln M n s f.demand)

end Closure

/-- A concrete vulnerability witness: the zero location of a root flows, through
    a chain of calls, to location `l` at node `n` of method `M`. -/
inductive Reach (P : Program) (roots : List MethodId) : MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → Flow P M zeroLoc n l → Reach P roots M n l
  | down {M n l n' c e l1 n2 l2} :
      Reach P roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      Flow P c.callee l1 n2 l2 → Reach P roots c.callee n2 l2

/-! ## 12. The abstraction policy -/

/-- The abstraction policy of the spec (§7.2, without the closed-reuse step):
    the zero fact serves itself; an added fact that a demand final of the previous
    run overlaps is served by its `*` projection with the mark `*` (the chain comes
    from the added fact, the demand covers it); otherwise the most abstract fact. -/
def policy (demand : MethodId → List PFact) (m : MethodId) (a : PFact) : PFact :=
  if a = zeroFact then zeroFact
  else if (demand m).any (fun d => overlapB d a) then ⟨a.base, a.path, .star Excl.empty, .star⟩
  else ⟨a.base, [], .star Excl.empty, .star⟩

/-! ## 13. Reversal of a record (backward reuse) -/

/-- The tails of a reversed record. The exclusion goes to the NEW conclusion, so the
    new premise has the empty exclusion and serves the most abstract fact. -/
def revKinds : Kind → Kind → Kind × Kind
  | .star ei, .star ef => (.star Excl.empty, .star (ei.union ef))
  | .any,     .star ef => (.star Excl.empty, .star ef)
  | .exact,   .star _  => (.exact, .exact)
  | .exact,   .exact   => (.exact, .exact)
  | .star _,  .exact   => (.exact, .any)
  | .any,     .exact   => (.exact, .any)
  | .exact,   .any     => (.any, .exact)
  | .star _,  .any     => (.any, .any)
  | .any,     .any     => (.any, .any)

/-- Reverse a record `i → f` into `f' → i'`: the exit fact becomes the premise.
    The new premise mark is the mark the record produces. -/
def revEdge (i f : PFact) : PFact × PFact :=
  let pm : MarkA := match f.mark with
    | .star   => i.mark
    | .conc t => .conc t
  let fm : MarkA := match f.mark with
    | .star   => .star
    | .conc _ => i.mark
  (⟨f.base, f.path, (revKinds i.kind f.kind).1, pm⟩, ⟨i.base, i.path, (revKinds i.kind f.kind).2, fm⟩)

end ApSpec
