/-
  ApSpec.Statics — the run-1 rule for STATIC FIELDS: position requests on the static base, raised,
  answered and climbed like mark requests. The rule as formalised, its soundness and exactness
  theorems, examples, and the counterexamples that fix its exact conditions.

  `S` is the static base (`ClassStatic`, the context field `sB`). A static field is the two-accessor
  path `[<C>, f]`; the class accessor `<C>` is not counted by the field limit. A static POSITION
  (`PosIn`) is the premise path of a statement micro edge on `S`, or the path of a sink pattern on
  `S`, TRUNCATED TO THE STATIC FIELD (`take 2`): a read `x = C.f` has the positions `[]` and
  `[<C>, f]`, a deeper read `x = C.f.g` too; a write `C.f = v` has `[]` and `[<C>]` (its keep edges
  `S.* →_{<C>} S.*` and `S.<C>.* →_{f} S.<C>.*`). A path strictly above a position is ABOVE it
  (`AbovePos`); it is the root `[]` or a class `[<C>]` (`abovePos_len`).

  THE FINAL RULE (run 1 only; restricted runs and the backward run are unchanged; `SCtx` with
  `gen = deepAns = wide = ansBelow = true`, `fb = off`, the predicate `Design`):
    1. FIRE (`sreqStmt` with `genFireB`). The propagation edge `i → f` is an IDENTITY static `*` edge
       at the ROOT or at a CLASS position: `i = (S, q, */E0, *)`, `f = (S, q, */E, m)` with
       `|q| ≤ 1` (`q = []` or `q = [<C>]`), `m` abstract (`*` or `*∖X`), normal layer. A statement
       micro edge whose premise is on `S` STRICTLY below `q`, with `E` admitting the rest (a read, a
       write's keep edge, a field-to-field copy), gives no fact and no mark request on this edge;
       the position request `(M, i, p)` is raised for its premise path TRUNCATED to the static field
       (`p = take 2`, `SCtx.reqP`: `[<C>, f]`, or `[<C>]` for a class keep edge). Below a static
       field (an identity edge at `[<C>, f]` or deeper, or any non-identity static fact) nothing
       fires: the ordinary rules of §4.1 apply, as for an instance field.
    2. SINKS on `S` use the ordinary MARK request (`reqSink`, `check`): no sink position request.
    3. ANSWER (`sanswer`, `ansOK`). An added fact of `M` that overlaps `(S, p)` and is AT OR BELOW
       `p` answers `(M, i, p)` with the initial fact `(S, p, *, {}, *)` (start: the identity,
       normal layer). No answer from an added fact above `p`.
    4. CLIMB (`sreqUp`, `climbOK`). Through a caller edge `ic → f` at a call of `M` whose premise `ic`
       is on `S` and whose binding gives an added fact that overlaps `(S, p)` and lies ABOVE `p`,
       the request `(caller, ic, p)` is raised.
    5. NO FALLBACK (`fb = off`: the overlap reading `sret` never applies).
    6. DEEP MARK ANSWER (`ansInit`, the amendment of `CexClean`). A MARK request `(M, i, t)` whose
       premise `i` is on `S`, answered by an added fact `a` at or below `i`, gives `a` itself with the
       mark `t` (`a`'s own position and tail) instead of `answerInit` (the requested chain).
       Cleaners are unchanged (spec §4.7).
  THE CONSTRUCTION HYPOTHESES (`SWF`; positions are the truncated ones, so no hypothesis concerns
  the depth of rule positions): `S` is not the zero base; a statement micro edge from `S` to `S` is
  an identity restriction `S.q.*/E1 → S.q.*/E2` or a FIELD-TO-FIELD edge whose premise and target
  paths are not above a position (`CopyAllMarks(C.f → D.g)`: `S.<C>.f.* → S.<D>.g.*`; `CopyMark`:
  `S.<C>.f.$(T) → S.<D>.g.$(T)`; a pass rule from or to a bare class is a rule error); a statement
  micro edge from another base into `S` writes at or below a position, and above one (the root or
  a bare class) only an exact fact from an exact concrete-mark premise; calls bind `S` only by
  `S.* → S.*`; the field limit never cuts a path to the root or a class above a position (`<C>`
  not counted, limit ≥ 1); a cleaner on `S` removes one mark (`RemoveAllMarks` on a static position
  is the kill of a strong write, not a cleaner); run 1 serves an added fact by its root (`policy1`).

  The other switches of `SCtx` give the earlier variants. The first design (`gen = deepAns =
  false`: the fire on reads at the static root only, `ansBelow = false`: answers from above too,
  `fb = full`: the fallback) is proved sound in §5–6 without construction hypotheses.

  Contents:
    1. Recognisers: `sRootB`, `sReadB`, `sFireB` (first fire), `idEdgeB`, `strictBelowB`, `genFireB`
       (final fire), `sKeepP`, `sAns`, `belowB`, `aboveB`, `climbB`, `sAboveB`.
    2. `Fallback`, `SCtx` (switches `wide`, `ansBelow`, `fb`, `gen`, `deepAns`) with `climbOK`, `ansOK`,
       `fbOK`, `fireB`, `reqP`, `ansInit`; `SObj`; the closure `DS`. `DS_mono`.
    3. Local lemmas.
    4–6. The first design: `edge_concS`, `req_abstractS`, `coverageS`, `vuln_foundS`,
       `vuln_found_policy1S`.
    7. EXACTNESS, for every variant: `DS_edgeOK`, `edge_exactS`, `edge_exact_validS`,
       `complete_exactS`.
    8. No `[any]` read on the static root edge: `read_D` (`D` reads `(x, ., [any], *)`), `read_DS`
       and `read_sreq` (first fire); `gen_read_fires`, `gen_read_DS`, `gen_read_sreq` are in §13.3.
    9. `Example` (`root: C1.f = source(); A()`, `A: B()`, `B: x = C1.f; sink(x)`): `D` reports the
       vulnerability only in the demand layer (`d_only_demand`), `DS` in the normal layer.
    10. `CexAbove` (`caller: C.s = null; r = m(); sink(r)`, `m: y = C.f; return y`): the narrow climb
       misses it (`cex_user_misses`, a record).
    11. `CexAny` (`root: C.* = source(); m()`, `m: x = C.f; sink(x)`): with the FIRST fire, answers
       only from at or below lose the flow (record).
    12. `CexWide` (`caller: t = C.g; C.s = t; K(); r = m(); sink(r)`, `K: C.u = null`): with the
       FIRST fire, a fallback only for non-static premises loses the flow (record).
    13. THE FINAL RULE: `PosIn`, `AbovePos`, `SWF`; `f2f_not_above`; the static invariant `cinv_all`
       and `no_any_above` (no `(S, q, [any], ...)` with `q` the root or a class above a position);
       `Design`; `coverageD`; `reachD`; `vulnD` (THE VULNERABILITY THEOREM of the final rule).
    14. `CexClean` (`caller: K(); r = m(); sink(r)`, `K: clean_7(C.u)`, `m: y = C.s; return y`): the
       deep mark answer is needed. With the shallow mark answer the static invariant fails
       (`shallow_any`, `shallow_degrades`) and the flow is lost (`shallow_misses`), although `SWF`
       holds; with the deep answer it is reported in the normal layer (`deep_vuln_normal`).
    15. `CexAbove` and `CexWide` under the final rule: `above_swf`, `wide_swf`, the vulnerabilities in
       the NORMAL layer (`y_vuln_normal`, `w_vuln_normal`; `above_design_finds`, `wide_design_finds`).
    16. `CopyF2F`: a field-to-field pass rule `CopyAllMarks(C.f → D.g)` at an unresolved call; the
       copy on the static root raises `<C>.f`, the answer flows to `<D>.g`; NORMAL layer
       (`c_vuln_normal`, `copy_design_finds`).
    17. `DeepSink`, `DeepSinkParam`: the deep static sink `ContainsMark(C.f.g)` after `C.f = x` with an
       abstract `x`; the ordinary mark request climbs; NORMAL layer with a static caller premise
       (`e_vuln_normal`), demand layer with a parameter premise (`p_vuln`, as for an instance
       field); both also from `vulnD`.

  Design choices:
    * The static base is a context parameter `sB`; the fire is recognised syntactically. A static path
      starts with its class accessor, so the static field is `take 2` and the root or a class is
      `|q| ≤ 1`.
    * A micro edge on which the rule fires is removed from the statement for this edge (`sKeepP`):
      it gives neither a fact nor a mark request. A mark it needs is asked later, on the answer;
      a deeper premise meets the answer `(S, <C>.f, *)` by the ordinary rules.
    * The soundness proof of the final rule is a strong induction on `posBound X - |path|`: a
      position request is raised strictly below its premise, and every position is bounded by the
      program's statement and sink patterns (`posBound`). The static invariant (`cinv_all`) is what
      makes the climb precise: a non-exact static fact at the root or a class above a position is an
      identity `*` edge, so the climbed premise carries its own location.
    * `CexAny` and `CexWide` refute variants of the FIRST fire, where `(S, <C>, [any], *)` exists.
      `CexAny` needs an `[any]` source on a bare class, which the construction rules exclude
      (`SWF.write`; spec S12 (b)). `CexWide` is found through a normal edge under the final rule
      (§15).

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.Core
import ApSpec.Coverage
import ApSpec.Exact

namespace ApSpec.Statics
open ApSpec

/-! ## 1. Recognisers -/

/-- `sRootB sB i`: `i` is the ABSTRACT STATIC ROOT `(S, [], */E, *)` (any exclusion `E`, the mark
    `*`), where `S = sB` is the static base (`ClassStatic`). -/
def sRootB (sB : Base) : PFact → Bool
  | ⟨b, [], .star _, .star⟩ => Nat.beq b sB
  | _ => false

/-- The conclusion of a propagation edge is the abstract static root in the NORMAL layer. -/
def sRootFB (sB : Base) (f : AFact) : Bool := sRootB sB f.fact && !f.demand

/-- A READ micro edge out of the static base: its premise is on `S` with a NON-EMPTY path, its
    conclusion is on another base (`x = C.s`: `S.<C>.s.* → x.*`). The static write edges
    (`S.* →_{<C>} S.*`, `S.<C>.* →_{s} S.<C>.*`) and the binding `S.* → S.*` have their conclusion
    on `S`, so they are not reads. -/
def sReadB (sB : Base) (e : MicroEdge) : Bool :=
  Nat.beq e.1.base sB && !e.1.path.isEmpty && !Nat.beq e.2.base sB

/-- THE RULE FIRES (case `above` of delta-concat with an overlap): the propagation edge `i → f`
    is `(S, [], *, E0, *) → (S, [], */E, *)` (normal layer), the micro edge `e` is a read out of
    `S`, and `E` admits the premise path `p` of `e`. -/
def sFireB (sB : Base) (i : PFact) (f : AFact) (e : MicroEdge) : Bool :=
  sRootB sB i && sRootFB sB f && sReadB sB e && admitsTailB f.fact.kind e.1.path

/-- The propagation edge `i → f` is an IDENTITY static `*` edge: the premise is the static `*`
    fact `(S, q, */E0, *)` and the conclusion is the static `*` fact at the SAME path
    `(S, q, */E, m)` with an abstract mark `m` (`*` or `*∖X`), in the normal layer. `q = []` is the
    static root, `q = [<C>]` a class answer. -/
def idEdgeB (sB : Base) (i : PFact) (f : AFact) : Bool :=
  Nat.beq i.base sB && i.kind.isStar && decide (i.mark = .star) && Nat.beq f.fact.base sB &&
    decide (f.fact.path = i.path) && f.fact.kind.isStar && Exact.absB f.fact.mark && !f.demand

/-- `p` lies STRICTLY below `q`, and the tail `k` admits the rest. -/
def strictBelowB (k : Kind) (q p : List Acc) : Bool :=
  match dropPrefix q p with
  | some (x :: r) => admitsTailB k (x :: r)
  | _ => false

/-- THE FINAL RULE FIRES: the propagation edge is an identity static `*` edge at the ROOT or at a
    CLASS position (`q = []` or `q = [<C>]`, i.e. `|q| ≤ 1`), and the statement micro edge `e` has
    its premise on `S` strictly below `q` (a read OR a keep edge of a write OR a field-to-field
    copy), the conclusion's exclusion admitting the rest. The request is for the premise path
    truncated to the static field (`SCtx.reqP`). Below a static field nothing fires: the ordinary
    rules apply, as for an instance field. -/
def genFireB (sB : Base) (i : PFact) (f : AFact) (e : MicroEdge) : Bool :=
  idEdgeB sB i f && decide (i.path.length ≤ 1) && Nat.beq e.1.base sB &&
    strictBelowB f.fact.kind f.fact.path e.1.path

/-- A statement without the micro edges that `P` selects (the same touched bases). -/
def sKeepP (P : MicroEdge → Bool) (s : Stmt) : Stmt := ⟨s.touched, s.edges.filter (fun e => !P e)⟩

/-- The statement that the run-1 transfer applies to the edge `i → f` under the first rule: the
    same touched bases, without the micro edges on which the rule fires. -/
abbrev sKeep (sB : Base) (i : PFact) (f : AFact) (s : Stmt) : Stmt := sKeepP (sFireB sB i f) s

/-- The ANSWER of a position request `(m, i, p)`: the abstract fact at the requested position,
    `(S, p, *, {}, *)`. Its start fact is the identity, in the normal layer. -/
def sAns (sB : Base) (p : List Acc) : PFact := ⟨sB, p, .star Excl.empty, .star⟩

/-- The added fact `a` is AT OR BELOW the requested position `p`: its path has `p` as a prefix. -/
def belowB (a : PFact) (p : List Acc) : Bool := (dropPrefix p a.path).isSome

/-- The added fact `a` overlaps the requested position `(S, p)` and lies ABOVE it (it is not at
    or below `p`). -/
def aboveB (sB : Base) (a : PFact) (p : List Acc) : Bool :=
  overlapB a (sAns sB p) && !belowB a p

/-- The NARROW climb condition (the first formalisation, kept for the record `CexAbove`): the added
    fact is the abstract static root `(S, [], */E', *)` and `E'` admits `p`. -/
def climbB (sB : Base) (a : PFact) (p : List Acc) : Bool := sRootB sB a && admitsTailB a.kind p

/-- The guard of the overlap reading `sret` (`fb = full`): a caller added fact `a` that lies ABOVE a static
    initial fact `j` of the callee at a non-root position (they overlap, `j` does not cover `a`, the
    premise mark of `j` admits the marks of `a`), and that is not the climb from the abstract static
    root (the caller premise `i` is the abstract static root and `a` is the static root admitting
    `j`'s path: only there does the climbed answer provably cover the caller's entry location). -/
def sAboveB (sB : Base) (i a j : PFact) : Bool :=
  Nat.beq j.base sB && !j.path.isEmpty && overlapB a j && markSubB j.mark a.mark &&
    !applicable j a && !(sRootB sB i && climbB sB a j.path)

/-! ## 2. The context and the closure `DS` -/

/-- Which caller added facts read a static answer from above (`sret`): none; only those whose
    caller premise is NOT on the static base (the coordinator's fallback); every one except the
    climb from the abstract static root (`sAboveB`, the corrected fallback). -/
inductive Fallback where
  | off
  | nonStatic
  | full
deriving DecidableEq, Repr

/-- The parameters of run 1 with the static rule. `sB` is the static base. Five switches select
    the variant of the rule (§2.1). The final rule is `gen = deepAns = wide = ansBelow = true`,
    `fb = off` (`Design`, proved sound in §13 under `SWF`); the first design is
    `gen = deepAns = false`, `ansBelow = false`, `fb = full` (proved sound in §5–6). -/
structure SCtx where
  P        : Program
  counted  : Acc → Bool
  FL       : Nat
  α        : MethodId → PFact → PFact
  sinks    : List (MethodId × Node × PFact)
  roots    : List MethodId
  sB       : Base
  /-- the climb: `true` = the design's WIDE climb, `false` = the narrow climb (`climbB`) -/
  wide     : Bool
  /-- the answer: `true` = only from an added fact AT OR BELOW `p`, `false` = from every added fact
      that overlaps `(S, p)` -/
  ansBelow : Bool
  /-- the overlap reading of a static answer -/
  fb       : Fallback
  /-- the fire: `true` = the final fire (identity static `*` edges at the root or a class, any
      static premise strictly below, the request truncated to the static field), `false` = the
      first fire (the static root, reads only) -/
  gen      : Bool
  /-- the mark answer on a static premise: `true` = at the answering added fact's own position
      when it is at or below the premise, `false` = the requested chain (`answerInit`) -/
  deepAns  : Bool

/-! ### 2.1 The three conditions of the rule -/

/-- CLIMB: the request `(m, j, p)` climbs through the caller edge `ic → f` whose binding gives the
    added fact `a`. WIDE (the design): the caller premise `ic` is on the static base and `a`
    overlaps `(S, p)` and lies above `p`, with no other condition. NARROW: `climbB`. -/
def SCtx.climbOK (X : SCtx) (ic a : PFact) (p : List Acc) : Bool :=
  if X.wide then Nat.beq ic.base X.sB && aboveB X.sB a p else climbB X.sB a p

/-- ANSWER: the added fact `a` of `m` answers the request `(m, j, p)` with `(S, p, *, {}, *)`: `a`
    overlaps `(S, p)`, and (with `ansBelow`) it is at or below `p`. -/
def SCtx.ansOK (X : SCtx) (a : PFact) (p : List Acc) : Bool :=
  overlapB a (sAns X.sB p) && (!X.ansBelow || belowB a p)

/-- FALLBACK: the caller edge with premise `i` and added fact `a` reads the summaries of the callee
    initial fact `j` from above. -/
def SCtx.fbOK (X : SCtx) (i a j : PFact) : Bool :=
  match X.fb with
  | .off       => false
  | .nonStatic => !Nat.beq i.base X.sB && sAboveB X.sB i a j
  | .full      => sAboveB X.sB i a j

/-- FIRE: the micro edge `e` gives no fact on the edge `i → f` and raises a position request. -/
def SCtx.fireB (X : SCtx) (i : PFact) (f : AFact) (e : MicroEdge) : Bool :=
  if X.gen then genFireB X.sB i f e else sFireB X.sB i f e

/-- The requested position of a fired micro edge with the premise path `p`: under the final rule
    `p` truncated to the static field `[<C>, f]` (or the class `[<C>]`); the first rule requests `p`. -/
def SCtx.reqP (X : SCtx) (p : List Acc) : List Acc :=
  if X.gen then p.take 2 else p

/-- The answer of a MARK request `(m, i, t)` by the concrete added fact `a`. With `deepAns`, on a
    static premise and an added fact at or below it: the added fact itself with the mark `t`;
    otherwise the requested chain (`answerInit`). -/
def SCtx.ansInit (X : SCtx) (i a : PFact) (t : Mark) : PFact :=
  if X.deepAns && Nat.beq i.base X.sB && (dropPrefix i.path a.path).isSome then
    ⟨a.base, a.path, a.kind, .conc t⟩
  else answerInit i a t

/-- Objects of `DS`: the objects of `D` and the POSITION REQUESTS `sreq M i p`. -/
inductive SObj where
  | init  (M : MethodId) (i : PFact)
  | edge  (M : MethodId) (i : PFact) (n : Node) (f : AFact)
  | added (M : MethodId) (a : PFact)
  | req   (M : MethodId) (i : PFact) (t : Mark)
  | sreq  (M : MethodId) (i : PFact) (p : List Acc)
  | vuln  (M : MethodId) (n : Node) (s : PFact) (demand : Bool)
deriving DecidableEq

/-- Run 1 with the static rule: the rules of `D`; the statement transfer and the statement
    request use `sKeep` (no fact and no mark request from a micro edge on which the rule fires);
    the new rules `sreqStmt` (raise), `sanswer` (answer), `sreqUp` (climb) and `sret` (the overlap
    reading of a static answer). A position request works as a mark request (`answer`, `reqUp`),
    with "the added fact has the mark `t`" replaced by "the added fact overlaps the position". -/
inductive DS (X : SCtx) : SObj → Prop where
  | root {M} : M ∈ X.roots → DS X (.init M zeroFact)
  | start {M i} : DS X (.init M i) → DS X (.edge M i (X.P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      DS X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      f' ∈ (transfer X.counted X.FL (sKeepP (X.fireB i f) s) f).facts → DS X (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      DS X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      t ∈ (transfer X.counted X.FL (sKeepP (X.fireB i f) s) f).reqs → DS X (.req M i t)
  -- RAISE: the fired micro edge gives the position request `(M, i, reqP p)` for its premise path `p`
  | sreqStmt {M i n f n' s e} :
      DS X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      e ∈ s.edges → X.fireB i f e = true → DS X (.sreq M i (X.reqP e.1.path))
  | pass {M i n f n' c} :
      DS X (.edge M i n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      memB f.fact.base c.touched = false → DS X (.edge M i n' f)
  | added {M i n f n' c e a} :
      DS X (.edge M i n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → DS X (.added c.callee a.fact)
  | initA {m a} : DS X (.added m a) → DS X (.init m (X.α m a))
  | ret {M i n f n' c e1 a j g r e2 r'} :
      DS X (.edge M i n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DS X (.init c.callee j) → applicable j a.fact = true →
      DS X (.edge c.callee j (X.P.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DS X (.edge M i n' (limitF X.counted X.FL r'))
  -- FALLBACK: an added fact above a static initial fact of the callee reads its summaries
  | sret {M i n f n' c e1 a j g r e2 r'} :
      DS X (.edge M i n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DS X (.init c.callee j) → X.fbOK i a.fact j = true →
      DS X (.edge c.callee j (X.P.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DS X (.edge M i n' (limitF X.counted X.FL r'))
  -- a sink on `S` too raises the ordinary MARK request (`check`)
  | reqSink {M i n f s t} :
      DS X (.edge M i n f) → (M, n, s) ∈ X.sinks →
      check i f s = .request t → DS X (.req M i t)
  | answer {M i t a} :
      DS X (.req M i t) → DS X (.added M a) → a.mark = .conc t →
      overlapB a i = true → DS X (.init M (X.ansInit i a t))
  -- ANSWER: an added fact of `M` that satisfies the request makes the abstract fact at the
  -- requested position
  | sanswer {M i p a} :
      DS X (.sreq M i p) → DS X (.added M a) → X.ansOK a p = true →
      DS X (.init M (sAns X.sB p))
  | reqUp {m j t M ic n f n' c e a} :
      DS X (.req m j t) → DS X (.edge M ic n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DS X (.req M ic t)
  -- CLIMB: the request climbs to the premise of a caller edge
  | sreqUp {m j p M ic n f n' c e a} :
      DS X (.sreq m j p) → DS X (.edge M ic n f) → (M, n, Instr.call c, n') ∈ X.P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      X.climbOK ic a.fact p = true → DS X (.sreq M ic p)
  | vuln {M i n f s} :
      DS X (.edge M i n f) → (M, n, s) ∈ X.sinks → check i f s = .triggered →
      DS X (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DS X (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ X.P.edges →
      f' ∈ (cleanRes cl f).facts → DS X (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      DS X (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ X.P.edges →
      t ∈ (cleanRes cl f).reqs → DS X (.req M i t)
  | filt {M i n f n' b may} :
      DS X (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ X.P.edges →
      (f.fact.base = b → may f.fact.path = true) → DS X (.edge M i n' f)

/-! ### 2.2 The corrected rule only adds objects -/

/-- The answer of the corrected rule (`ansBelow = false`) accepts every added fact that the
    at-or-below answer accepts. -/
theorem ansOK_mono {X : SCtx} {ab ab' : Bool} {fb fb' : Fallback} (hab : ab' = false ∨ ab = ab')
    {a : PFact} {p : List Acc}
    (h : ({ X with ansBelow := ab, fb := fb } : SCtx).ansOK a p = true) :
    ({ X with ansBelow := ab', fb := fb' } : SCtx).ansOK a p = true := by
  unfold SCtx.ansOK at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  rcases hab with rfl | rfl
  · exact ⟨h.1, rfl⟩
  · exact h

/-- The full fallback accepts every caller edge that a weaker fallback accepts. -/
theorem fbOK_mono {X : SCtx} {ab ab' : Bool} {fb fb' : Fallback} (hfb : fb' = .full ∨ fb = fb')
    {i a j : PFact}
    (h : ({ X with ansBelow := ab, fb := fb } : SCtx).fbOK i a j = true) :
    ({ X with ansBelow := ab', fb := fb' } : SCtx).fbOK i a j = true := by
  unfold SCtx.fbOK at h ⊢
  rcases hfb with rfl | rfl
  · cases fb with
    | off => cases h
    | nonStatic =>
      simp only [Bool.and_eq_true] at h
      exact h.2
    | full => exact h
  · cases fb with
    | off => cases h
    | nonStatic => exact h
    | full => exact h

/-- MONOTONICITY. A variant with a weaker answer or a weaker fallback has fewer objects; in
    particular the design as first stated by the coordinator (`ansBelow = true`,
    `fb = nonStatic`) is contained in the corrected rule (`ansBelow = false`, `fb = full`). -/
theorem DS_mono {X : SCtx} {ab ab' : Bool} {fb fb' : Fallback} (hab : ab' = false ∨ ab = ab')
    (hfb : fb' = .full ∨ fb = fb') {o : SObj} (h : DS { X with ansBelow := ab, fb := fb } o) :
    DS { X with ansBelow := ab', fb := fb' } o := by
  induction h with
  | root hM => exact DS.root hM
  | start _ ih => exact DS.start ih
  | step _ he hf ih => exact DS.step ih he hf
  | reqStmt _ he hq ih => exact DS.reqStmt ih he hq
  | sreqStmt _ he hes hfire ih => exact DS.sreqStmt ih he hes hfire
  | pass _ he hm ih => exact DS.pass ih he hm
  | added _ he he1 ha ih => exact DS.added ih he he1 ha
  | initA _ ih => exact DS.initA ih
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact DS.ret ihf he he1 ha ihj hap ihg hr he2 hr'
  | sret _ he he1 ha _ hok _ hr he2 hr' ihf ihj ihg =>
    exact DS.sret ihf he he1 ha ihj (fbOK_mono hfb hok) ihg hr he2 hr'
  | reqSink _ hs hc ih => exact DS.reqSink ih hs hc
  | answer _ _ hm hov ihr iha => exact DS.answer ihr iha hm hov
  | sanswer _ _ hok ihs iha => exact DS.sanswer ihs iha (ansOK_mono hab hok)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf => exact DS.reqUp ihr ihf he hc he1 ha hcl hov
  | sreqUp _ _ he hc he1 ha hcl ihs ihf => exact DS.sreqUp ihs ihf he hc he1 ha hcl
  | vuln _ hs hc ih => exact DS.vuln ih hs hc
  | clean _ he hf ih => exact DS.clean ih he hf
  | reqClean _ he hq ih => exact DS.reqClean ih he hq
  | filt _ he hp ih => exact DS.filt ih he hp

#print axioms DS_mono

/-! ## 3. Local lemmas -/

theorem sRootB_eq {sB : Base} {i : PFact} (h : sRootB sB i = true) :
    ∃ e, i = ⟨sB, [], .star e, .star⟩ := by
  obtain ⟨b, p, k, m⟩ := i
  cases p with
  | cons _ _ => cases k <;> cases m <;> cases h
  | nil =>
    cases k with
    | star e =>
      cases m with
      | star =>
        have hb : b = sB := CoreAux.beq_iff.mp h
        exact ⟨e, by rw [hb]⟩
      | conc _ => cases h
      | starEx _ => cases h
    | any => cases h
    | exact => cases h

theorem sRootB_conc {sB : Base} {i : PFact} {t : Mark} (h : i.mark = .conc t) :
    sRootB sB i = false := by
  obtain ⟨b, p, k, m⟩ := i
  have hm : m = .conc t := h
  subst hm
  cases p <;> cases k <;> rfl

theorem sRootB_sAns {sB : Base} {p : List Acc} (hp : p ≠ []) : sRootB sB (sAns sB p) = false := by
  cases p with
  | nil => exact absurd rfl hp
  | cons _ _ => rfl

theorem sFire_parts {sB : Base} {i : PFact} {f : AFact} {e : MicroEdge}
    (h : sFireB sB i f e = true) :
    sRootB sB i = true ∧ sRootB sB f.fact = true ∧ e.1.base = sB ∧ e.1.path ≠ [] ∧
      e.2.base ≠ sB ∧ admitsTailB f.fact.kind e.1.path = true := by
  unfold sFireB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, hf⟩, hr⟩, h6⟩ := h
  have h2 : sRootB sB f.fact = true := by
    unfold sRootFB at hf
    simp only [Bool.and_eq_true] at hf
    exact hf.1
  unfold sReadB at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨h3, h4⟩, h5⟩ := hr
  refine ⟨h1, h2, CoreAux.beq_iff.mp h3, ?_, ?_, h6⟩
  · intro hp
    rw [hp] at h4
    cases h4
  · intro hb
    rw [hb, Nat.beq_refl] at h5
    cases h5

theorem sKeep_mem {P : MicroEdge → Bool} {s : Stmt} {e : MicroEdge}
    (h : e ∈ (sKeepP P s).edges) : e ∈ s.edges ∧ P e = false := by
  have h' := List.mem_filter.mp h
  refine ⟨h'.1, ?_⟩
  cases hf : P e with
  | false => rfl
  | true => rw [hf] at h'; cases h'.2

theorem mem_sKeep {P : MicroEdge → Bool} {s : Stmt} {e : MicroEdge}
    (he : e ∈ s.edges) (hf : P e = false) : e ∈ (sKeepP P s).edges :=
  List.mem_filter.mpr ⟨he, by rw [hf]; rfl⟩

/-- The rule fires on `e`: `e` is not a micro edge of the transfer of `DS`. -/
theorem fire_drops {P : MicroEdge → Bool} {s : Stmt} {e : MicroEdge}
    (h : P e = true) : e ∉ (sKeepP P s).edges := by
  intro he
  rw [(sKeep_mem he).2] at h
  cases h

theorem sKeep_wf {P : MicroEdge → Bool} {s : Stmt}
    (h : ∀ e, e ∈ s.edges → memB e.1.base s.touched = true) :
    ∀ e, e ∈ (sKeepP P s).edges → memB e.1.base (sKeepP P s).touched = true :=
  fun e he => h e (sKeep_mem he).1

theorem sKeep_step {P : MicroEdge → Bool} {s : Stmt} {l l' : Loc}
    (h : (sKeepP P s).step l l') : s.step l l' := by
  rcases h with ⟨hu, he⟩ | ⟨e, he, hd⟩
  · exact .inl ⟨hu, he⟩
  · exact .inr ⟨e, (sKeep_mem he).1, hd⟩

/-- A statement step is a step of `sKeepP P`, or it goes through a micro edge that `P` selects. -/
theorem step_split {P : MicroEdge → Bool} {s : Stmt} {l l' : Loc} (h : s.step l l') :
    (sKeepP P s).step l l' ∨ ∃ e, e ∈ s.edges ∧ P e = true ∧ den e.1 e.2 l l' := by
  rcases h with ⟨hu, he⟩ | ⟨e, he, hd⟩
  · exact .inl (.inl ⟨hu, he⟩)
  · cases hf : P e with
    | false => exact .inl (.inr ⟨e, mem_sKeep he hf, hd⟩)
    | true => exact .inr ⟨e, he, hf, hd⟩

theorem fireB_old {X : SCtx} (hg : X.gen = false) {i : PFact} {f : AFact} {e : MicroEdge} :
    X.fireB i f e = sFireB X.sB i f e := by
  unfold SCtx.fireB
  rw [hg]
  rfl

theorem fireB_root {X : SCtx} (hg : X.gen = false) {i : PFact} {f : AFact} {e : MicroEdge}
    (h : X.fireB i f e = true) : sRootB X.sB i = true := by
  rw [fireB_old hg] at h
  unfold sFireB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem reqP_old {X : SCtx} (hg : X.gen = false) {p : List Acc} : X.reqP p = p := by
  unfold SCtx.reqP
  rw [hg]
  rfl

theorem reqP_gen {X : SCtx} (hg : X.gen = true) {p : List Acc} : X.reqP p = p.take 2 := by
  unfold SCtx.reqP
  rw [hg]
  rfl

theorem ansInit_shallow {X : SCtx} (hd : X.deepAns = false) {i a : PFact} {t : Mark} :
    X.ansInit i a t = answerInit i a t := by
  unfold SCtx.ansInit
  rw [hd]
  rfl

/-- An edge between two abstract static roots relates locations at the same path of `S`. -/
theorem root_den {sB : Base} {i x : PFact} {l0 l1 : Loc} (hi : sRootB sB i = true)
    (hx : sRootB sB x = true) (hd : den i x l0 l1) : l0.base = sB ∧ l0.path = l1.path := by
  obtain ⟨e, rfl⟩ := sRootB_eq hi
  obtain ⟨e', rfl⟩ := sRootB_eq hx
  obtain ⟨h0b, -, -, -, -, σ, τ, h0p, h1p, -, hτ, -⟩ := hd
  refine ⟨h0b, ?_⟩
  rw [h0p, h1p, hτ]

/-- The answer at the requested position covers every location of `S` below it. -/
theorem sAns_covers {sB : Base} {p σ : List Acc} {l : Loc} (hb : l.base = sB)
    (hp : l.path = p ++ σ) : (sAns sB p).covers l :=
  ⟨hb, ⟨σ, hp, CoreAux.empty_admits σ⟩, trivial⟩

/-- RAISE is sound: when the rule fires on the read `e`, the answer at the premise path of `e`
    covers the entry location of every pair of the static root edge that the read takes. -/
theorem fire_covers {sB : Base} {i : PFact} {f : AFact} {e : MicroEdge} {l0 l l' : Loc}
    (hfire : sFireB sB i f e = true) (hd : den i f.fact l0 l) (hde : den e.1 e.2 l l') :
    (sAns sB e.1.path).covers l0 := by
  obtain ⟨hi, hf, -, -, -, -⟩ := sFire_parts hfire
  obtain ⟨hb, hp⟩ := root_den hi hf hd
  obtain ⟨-, -, -, -, -, σ', -, hlp, -, -, -⟩ := hde
  exact sAns_covers hb (by rw [hp, hlp])

/-- CLIMB is sound: the caller premise and the added fact are abstract static roots, so the
    answer that covers the callee entry location covers the caller entry location. -/
theorem climb_covers {sB : Base} {i a : PFact} {p : List Acc} {l0 l1 : Loc}
    (hi : sRootB sB i = true) (hcl : climbB sB a p = true) (hd : den i a l0 l1)
    (hc : (sAns sB p).covers l1) : (sAns sB p).covers l0 := by
  have ha : sRootB sB a = true := by
    unfold climbB at hcl
    simp only [Bool.and_eq_true] at hcl
    exact hcl.1
  obtain ⟨hb, hp⟩ := root_den hi ha hd
  obtain ⟨-, ⟨σ, hlp, -⟩, -⟩ := hc
  exact sAns_covers hb (hp.trans hlp)

theorem climbB_conc {sB : Base} {a : PFact} {p : List Acc} {t : Mark} (h : a.mark = .conc t) :
    climbB sB a p = false := by
  unfold climbB
  rw [sRootB_conc h]
  rfl

theorem answerInit_base {i a : PFact} {t : Mark} : (answerInit i a t).base = i.base := by
  unfold answerInit
  split <;> rfl

theorem answerInit_path {i a : PFact} {t : Mark} : (answerInit i a t).path = i.path := by
  unfold answerInit
  split <;> rfl

theorem markSub_conc {m : MarkA} {t : Mark} (h : markSubB (.conc t) m = true) : m = .conc t := by
  cases m with
  | star => cases h
  | starEx _ => cases h
  | conc t' =>
    have e : t = t' := CoreAux.beq_iff.mp h
    rw [e]

theorem markSub_refl_conc (t : Mark) : markSubB (.conc t) (.conc t) = true := Nat.beq_refl t

theorem sAboveB_intro {sB : Base} {i a j : PFact} (hb : j.base = sB) (hp : j.path ≠ [])
    (ho : overlapB a j = true) (hm : markSubB j.mark a.mark = true)
    (hap : applicable j a = false)
    (hcl : ¬ (sRootB sB i = true ∧ climbB sB a j.path = true)) : sAboveB sB i a j = true := by
  have h1 : Nat.beq j.base sB = true := by rw [hb]; exact Nat.beq_refl sB
  have h2 : (!j.path.isEmpty) = true := by
    cases hq : j.path with
    | nil => exact absurd hq hp
    | cons _ _ => rfl
  have h3 : (!(sRootB sB i && climbB sB a j.path)) = true := by
    cases h4 : sRootB sB i <;> cases h5 : climbB sB a j.path
    · rfl
    · rfl
    · rfl
    · exact absurd ⟨h4, h5⟩ hcl
  unfold sAboveB
  rw [h1, h2, ho, hm, hap, h3]
  rfl

theorem sAboveB_markSub {sB : Base} {i a j : PFact} (h : sAboveB sB i a j = true) :
    markSubB j.mark a.mark = true := by
  unfold sAboveB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

/-- An applicable summary, or one whose premise mark admits the marks of the added fact, raises
    no request (the form of `Coverage.summary_step` with `markSubB`). -/
theorem summary_stepM {i j : PFact} {a g : AFact} {l0 l1 l2 : Loc}
    (hm : markSubB j.mark a.fact.mark = true) (hda : den i a.fact l0 l1)
    (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    rcases Coverage.mark_cases j.mark with hj | ⟨t, hj⟩
    · rw [Coverage.applySummary_reqs, Coverage.applyEdge_reqs_of_abs hj] at hq
      cases hq
    · rw [hj] at hm
      exact hst t (markSub_conc hm)

/-- With `ansBelow = false` every overlapping added fact answers. -/
theorem ansOK_of {X : SCtx} (hab : X.ansBelow = false) {a : PFact} {p : List Acc}
    (h : overlapB a (sAns X.sB p) = true) : X.ansOK a p = true := by
  unfold SCtx.ansOK
  rw [h, hab]
  rfl

/-- The climb from the abstract static root through the abstract static root is a climb of both
    variants. -/
theorem climbOK_of_root {X : SCtx} {ic a : PFact} {p : List Acc} (hi : sRootB X.sB ic = true)
    (hcl : climbB X.sB a p = true) (hp : p ≠ []) : X.climbOK ic a p = true := by
  unfold SCtx.climbOK
  cases hw : X.wide with
  | false => exact hcl
  | true =>
    obtain ⟨e0, rfl⟩ := sRootB_eq hi
    have ha : sRootB X.sB a = true ∧ admitsTailB a.kind p = true := by
      unfold climbB at hcl
      simpa only [Bool.and_eq_true] using hcl
    obtain ⟨E, rfl⟩ := sRootB_eq ha.1
    obtain ⟨x, r, rfl⟩ : ∃ x r, p = x :: r := by
      cases p with
      | nil => exact absurd rfl hp
      | cons x r => exact ⟨x, r, rfl⟩
    have hE : E.admits (x :: r) = true := ha.2
    simp only [if_true, aboveB, belowB, overlapB, sAns, Nat.beq_refl, relate, dropPrefix,
      admitsTailB, hE, Option.isSome_none, Bool.not_false, Bool.and_self]

theorem fbOK_full {X : SCtx} (hfb : X.fb = .full) {i a j : PFact}
    (h : sAboveB X.sB i a j = true) : X.fbOK i a j = true := by
  unfold SCtx.fbOK
  rw [hfb]
  exact h

theorem fbOK_markSub {X : SCtx} {i a j : PFact} (h : X.fbOK i a j = true) :
    markSubB j.mark a.mark = true := by
  unfold SCtx.fbOK at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    exact sAboveB_markSub h.2
  · exact sAboveB_markSub h

theorem sAboveB_path {sB : Base} {i a j : PFact} (h : sAboveB sB i a j = true) : j.path ≠ [] := by
  intro hp
  unfold sAboveB at h
  rw [hp] at h
  simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_and] at h
  cases h

/-- The overlap reading is only from a static initial fact at a non-root position. -/
theorem fbOK_path {X : SCtx} {i a j : PFact} (h : X.fbOK i a j = true) : j.path ≠ [] := by
  unfold SCtx.fbOK at h
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    exact sAboveB_path h.2
  · exact sAboveB_path h

#print axioms fire_covers
#print axioms climb_covers
#print axioms summary_stepM

/-! ## 4. Mark invariants of `DS` -/

/-- A concrete-mark initial fact has concrete-mark final facts. -/
def EInv : SObj → Prop
  | .edge _ i _ f => ∀ t, i.mark = .conc t → ∃ t', f.fact.mark = .conc t'
  | _ => True

/-- A mark request is on a mark-abstract initial fact. -/
def RInv : SObj → Prop
  | .req _ i _ => ∀ t, i.mark ≠ .conc t
  | _ => True

section Inv
variable {X : SCtx}

theorem eInv_all {o : SObj} (h : DS X o) : EInv o := by
  induction h with
  | start _ =>
    intro t ht
    exact ⟨t, by rw [startFact_mark]; exact ht⟩
  | step _ _ hf' ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    exact transfer_mark_conc h1 hf'
  | pass _ _ _ ih => exact ih
  | ret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨t4, by rw [limitF_mark]; exact h4⟩
  | sret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨t4, by rw [limitF_mark]; exact h4⟩
  | clean _ _ hf' ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    exact cleanRes_mark_conc h1 hf'
  | filt _ _ _ ih => exact ih
  | root _ => trivial
  | reqStmt _ _ _ _ => trivial
  | sreqStmt _ _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | sanswer _ _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | sreqUp _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | reqClean _ _ _ _ => trivial

/-- A concrete-mark initial fact has concrete-mark final facts. -/
theorem edge_concS {M : MethodId} {i : PFact} {n : Node} {f : AFact} {t : Mark}
    (h : DS X (.edge M i n f)) (ht : i.mark = .conc t) : ∃ t', f.fact.mark = .conc t' :=
  (eInv_all h : EInv (.edge M i n f)) t ht

theorem rInv_all {o : SObj} (h : DS X o) : RInv o := by
  induction h with
  | @reqStmt _ i _ _ _ _ _ hf _ hq _ =>
    rcases Coverage.mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_concS hf hm
      rw [transfer_reqs_of_conc h1] at hq
      cases hq
  | reqSink _ _ hc _ => exact check_request_star hc
  | @reqUp _ _ _ _ ic _ _ _ _ _ _ _ hf _ _ _ ha hcl _ _ _ =>
    rcases Coverage.mark_cases ic.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_concS hf hm
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      exact climbsB_abs hcl t2 h2
  | @reqClean _ i _ _ _ _ _ hf _ hq _ =>
    rcases Coverage.mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_concS hf hm
      exact (cleanRes_reqs_abstract hq).1 t1 h1
  | root _ => trivial
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | sreqStmt _ _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | sret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | sanswer _ _ _ _ _ => trivial
  | sreqUp _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | clean _ _ _ _ => trivial
  | filt _ _ _ _ => trivial

/-- Every mark request is on a mark-abstract initial fact. -/
theorem req_abstractS {M : MethodId} {i : PFact} {t : Mark} (h : DS X (.req M i t)) :
    ∀ t', i.mark ≠ .conc t' :=
  (rInv_all h : RInv (.req M i t))

#print axioms edge_concS
#print axioms req_abstractS

end Inv

/-! ## 5. The coverage theorem -/

section Coverage
variable (X : SCtx)

/-- The coverage statement for one initial fact `i` of `M` and the pair `(l0, l)` at `n`: an edge
    of `i` covers the pair; or `DS` has the mark request for the entry mark on `i` (as in
    `Coverage.coverage`); or `i` is the abstract static root and `DS` has a POSITION REQUEST on `i`
    whose answer covers `l0`. -/
abbrev CovS (M : MethodId) (i : PFact) (n : Node) (l0 l : Loc) : Prop :=
  (∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l) ∨ DS X (.req M i l0.mark) ∨
  (sRootB X.sB i = true ∧ ∃ p, p ≠ [] ∧ DS X (.sreq M i p) ∧ (sAns X.sB p).covers l0)

variable {X}

/-- A callee summary that the caller reads: the summary of an applicable initial fact (`ret`),
    or of a static initial fact at a non-root position that the added fact lies above (`sret`). -/
theorem use_summary (hfb : X.fb = .full) (hwf : X.P.WF)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {c : Call} {e1 e2 : MicroEdge}
    {a g : AFact} {j : PFact} {l0 l1 l2 l3 : Loc}
    (hf : DS X (.edge M i n f)) (he : (M, n, Instr.call c, n') ∈ X.P.edges)
    (he1 : e1 ∈ c.toCallee) (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hda : den i a.fact l0 l1)
    (hj : DS X (.init c.callee j)) (hjc : j.covers l1) (hm : markSubB j.mark a.fact.mark = true)
    (huse : applicable j a.fact = true ∨
      (j.base = X.sB ∧ j.path ≠ [] ∧ ¬ (sRootB X.sB i = true ∧ climbB X.sB a.fact j.path = true)))
    (hg : DS X (.edge c.callee j (X.P.exit c.callee) g)) (hdg : den j g.fact l1 l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    ∃ f', DS X (.edge M i n' f') ∧ den i f'.fact l0 l3 := by
  obtain ⟨r, hr, hdr⟩ := summary_stepM hm hda hdg
  obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hwf he he2 hdr hd2
  cases hap : applicable j a.fact with
  | true => exact ⟨_, DS.ret hf he he1 ha hj hap hg hr he2 hr', limitF_sound hdr'⟩
  | false =>
    rcases huse with h | ⟨hb, hp, hcl⟩
    · rw [hap] at h
      cases h
    · have hab := sAboveB_intro hb hp (overlapB_of_common (den_covers_final hda) hjc) hm hap hcl
      exact ⟨_, DS.sret hf he he1 ha hj (fbOK_full hfb hab) hg hr he2 hr', limitF_sound hdr'⟩

/-- THE CALL STEP. A caller edge covers the pair at the call, the binding gives the callee entry
    location `l1`, and the callee coverage theorem holds for every initial fact that covers `l1`.
    Then a caller edge covers the pair after the call, or a request is on the caller premise.

    The callee initial fact `α a` gives: a summary (`ret`); a mark request (it climbs, or a
    concrete added fact answers it, as in `Coverage.coverage`); or a POSITION REQUEST at `p`. Then
    `a` covers `l1`, so it overlaps the position and answers the request (`sanswer`, the overlap
    answer): the answer `(S, p, *, {}, *)` covers `l1`, and its own coverage gives: a summary, which the
    caller reads (`ret` if the answer covers the added fact, `sret` if the added fact lies above
    it), unless the caller premise is the abstract static root and the added fact climbs: then
    the request climbs (`sreqUp`) and its answer covers the caller entry location; or a mark
    request on the answer (it climbs, or it is answered; the concrete answer is read by `ret` or
    `sret`). No position request is on the answer: it is not the static root. -/
theorem call_stepS (hfb : X.fb = .full) (hab : X.ansBelow = false) (_hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {c : Call} {e1 e2 : MicroEdge}
    {l0 l l1 l2 l3 : Loc}
    (hf : DS X (.edge M i n f)) (hd : den i f.fact l0 l)
    (he : (M, n, Instr.call c, n') ∈ X.P.edges) (he1 : e1 ∈ c.toCallee) (hd1 : den e1.1 e1.2 l l1)
    (ihc : ∀ j, DS X (.init c.callee j) → j.covers l1 →
      CovS X c.callee j (X.P.exit c.callee) l1 l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    CovS X M i n' l0 l3 := by
  obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hd hd1
  have hadd := DS.added hf he he1 ha
  have hac : a.fact.covers l1 := den_covers_final hda
  -- a mark request on a callee initial fact whose summaries the caller reads
  have mreq : ∀ j, DS X (.init c.callee j) → j.covers l1 → markSubB j.mark a.fact.mark = true →
      (applicable j a.fact = true ∨ (j.base = X.sB ∧ j.path ≠ [])) →
      DS X (.req c.callee j l1.mark) → CovS X M i n' l0 l3 := by
    intro j hj hjc hm huse hreq
    have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
    rcases Coverage.mark_cases a.fact.mark with ham | ⟨t, ham⟩
    · -- a mark-abstract added fact: the request climbs to the caller premise
      have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hov
      rw [den_mark_abs hda ham] at hup
      exact .inr (.inl hup)
    · -- a concrete added fact answers the request
      have hmk : a.fact.mark = .conc l1.mark := Coverage.den_mark_conc hda ham
      have hans := DS.answer hreq hadd hmk hov
      rw [ansInit_shallow hdeep] at hans
      have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
      rcases ihc _ hans hc' with ⟨g, hg, hdg⟩ | hreq' | ⟨hroot, _⟩
      · refine .inl (use_summary hfb hwf hf he he1 ha hda hans hc' ?_ ?_ hg hdg he2 hd2)
        · rw [answerInit_mark, hmk]
          exact markSub_refl_conc _
        · rcases huse with hap | ⟨hb, hp⟩
          · exact .inl (answerInit_applicable hap hmk)
          · refine .inr ⟨by rw [answerInit_base]; exact hb, by rw [answerInit_path]; exact hp, ?_⟩
            intro hcl
            rw [climbB_conc hmk] at hcl
            cases hcl.2
      · exact absurd answerInit_mark (req_abstractS hreq' l1.mark)
      · rw [sRootB_conc answerInit_mark] at hroot
        cases hroot
  have hapj := hα c.callee a.fact
  have hjc := applicable_sound hapj hac
  have hj0 := DS.initA hadd
  rcases ihc _ hj0 hjc with ⟨g, hg, hdg⟩ | hreq | ⟨_, p, hp, hsreq, hpc⟩
  · exact .inl (use_summary hfb hwf hf he he1 ha hda hj0 hjc (Exact.applicable_markSub hapj)
      (.inl hapj) hg hdg he2 hd2)
  · exact mreq _ hj0 hjc (Exact.applicable_markSub hapj) (.inl hapj) hreq
  · -- the position request: the callee answers it
    have hans := DS.sanswer hsreq hadd (ansOK_of hab (overlapB_of_common hac hpc))
    rcases ihc _ hans hpc with ⟨g, hg, hdg⟩ | hreq' | ⟨hroot', _⟩
    · by_cases hcl : sRootB X.sB i = true ∧ climbB X.sB a.fact p = true
      · -- the caller passes its abstract static root: the request climbs
        exact .inr (.inr ⟨hcl.1, p, hp,
          DS.sreqUp hsreq hf he rfl he1 ha (climbOK_of_root hcl.1 hcl.2 hp),
          climb_covers hcl.1 hcl.2 hda hpc⟩)
      · exact .inl (use_summary hfb hwf hf he he1 ha hda hans hpc rfl (.inr ⟨rfl, hp, hcl⟩)
          hg hdg he2 hd2)
    · exact mreq _ hans hpc rfl (.inr ⟨rfl, hp⟩) hreq'
    · rw [sRootB_sAns hp] at hroot'
      cases hroot'

#print axioms call_stepS

/-- THE COVERAGE THEOREM for `DS` (run 1 with the static rule: the overlap answer, the full
    fallback, either climb). If the initial
    fact `i` of `M` is in `DS` and covers the entry location `l0`, and the value at `l0` flows to
    `l` at `n`, then an edge of `i` at `n` covers the pair; or `DS` has the mark request for the
    entry mark on `i`; or `i` is the abstract static root and `DS` has a position request on `i`
    whose answer `(S, p, *, {}, *)` covers `l0`. -/
theorem coverageS (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow X.P M l0 n l) :
    ∀ i, DS X (.init M i) → i.covers l0 → CovS X M i n l0 l := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, DS.start hi, startFact_sound hc⟩
  | @step M l0 n l n' l' s _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr | hsr
    · rcases step_split (P := X.fireB i f) hs with hs' | ⟨e, hes, hfire, hde⟩
      · rcases transfer_sound (counted := X.counted) (L := X.FL)
            (sKeep_wf (hwf.stmtTouched _ _ _ _ he)) hd hs' with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
        · exact .inl ⟨r, DS.step hf he hr, hdr⟩
        · exact .inr (.inl (DS.reqStmt hf he hq))
      · -- RAISE: the read on the abstract static root edge
        have hfire' : sFireB X.sB i f e = true := by rw [← fireB_old hgen]; exact hfire
        obtain ⟨hroot, -, -, hp, -, -⟩ := sFire_parts hfire'
        have hsr := DS.sreqStmt hf he hes hfire
        rw [reqP_old hgen] at hsr
        exact .inr (.inr ⟨hroot, e.1.path, hp, hsr, fire_covers hfire' hd hde⟩)
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr | hsr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, DS.pass hf he hb, hd⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr | hsr
    · exact call_stepS hfb hab hgen hdeep hwf hα hf hd he he1 hd1 ihc he2 hd2
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr | hsr
    · rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DS.clean hf he hr, hdr⟩
      · exact .inr (.inl (DS.reqClean hf he hq))
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr | hsr
    · exact .inl ⟨f, DS.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hd hl), hd⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)

#print axioms coverageS

/-- Coverage for a concrete-mark initial fact: it has no mark request and no position request,
    so an edge covers the pair. -/
theorem coverage_concS (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow X.P M l0 n l)
    {i : PFact} {t : Mark} (hi : DS X (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l := by
  rcases coverageS hfb hab hgen hdeep hwf hα hfl i hi hc with h | hr | ⟨hroot, _⟩
  · exact h
  · exact absurd ht (req_abstractS hr t)
  · rw [sRootB_conc ht] at hroot
    cases hroot

#print axioms coverage_concS

/-- Coverage at a root: the zero fact covers every flow from the zero location. -/
theorem coverage_rootS (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hM : M ∈ X.roots) (hfl : Flow X.P M zeroLoc n l) :
    ∃ f, DS X (.edge M zeroFact n f) ∧ den zeroFact f.fact zeroLoc l :=
  coverage_concS hfb hab hgen hdeep hwf hα hfl (t := zeroMark) (DS.root hM) Coverage.zeroFact_covers rfl

#print axioms coverage_rootS

/-! ## 6. The vulnerability theorem -/

variable (X)

/-- The strengthened reach statement of `Coverage.reach_strong`, for `DS`. -/
abbrev RS (M : MethodId) (n : Node) (l : Loc) : Prop :=
  ∃ l0 i f, DS X (.edge M i n f) ∧ den i f.fact l0 l ∧
    ((∃ t, i.mark = .conc t) ∨
     ((∀ t, i.mark ≠ .conc t) ∧ (DS X (.req M i l0.mark) →
        ∃ i' f', DS X (.edge M i' n f') ∧ den i' f'.fact l0 l ∧ ∃ t, i'.mark = .conc t)))

variable {X}

/-- THE STRENGTHENED REACH THEOREM for `DS`. A position request in the callee is answered in the
    callee itself; the answer is an initial fact like any other, and it is not the static root,
    so its coverage ends with an edge or a mark request; the mark request is answered as in
    `Coverage.reach_strong`. -/
theorem reach_strongS (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hR : Reach X.P X.roots M n l) : RS X M n l := by
  induction hR with
  | root hM hfl =>
    obtain ⟨f, hf, hd⟩ := coverage_rootS hfb hab hgen hdeep hwf hα hM hfl
    exact ⟨zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨l0, i, f, hf, hd, hdisj⟩ := ih
    obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hd hd1
    have hadd := DS.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    -- a mark request on a callee initial fact that covers `l1` has a concrete answer
    have key : ∀ j, DS X (.init c.callee j) → j.covers l1 → DS X (.req c.callee j l1.mark) →
        ∃ j', DS X (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro j hj hjc hreq
      have hconc : ∃ a', DS X (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases Coverage.mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- the request climbs to the caller; the caller has a concrete-mark edge
          have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapB_of_common hac hjc)
          rw [den_mark_abs hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exact absurd ht (req_abstractS hup t)
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := Coverage.bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_concS hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, DS.added hf' he he1 ha', den_covers_final hda',
              Coverage.den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, Coverage.den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := DS.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      rw [ansInit_shallow hdeep] at hans
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    -- an edge of a callee initial fact that covers `l1`
    have fin : ∀ j g, DS X (.init c.callee j) → j.covers l1 → DS X (.edge c.callee j n2 g) →
        den j g.fact l1 l2 → RS X c.callee n2 l2 := by
      intro j g hj hjc hg hdg
      refine ⟨l1, j, g, hg, hdg, ?_⟩
      rcases Coverage.mark_cases j.mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key j hj hjc hreq
        obtain ⟨g', hg', hdg'⟩ := coverage_concS hfb hab hgen hdeep hwf hα hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    -- a mark request on a callee initial fact that covers `l1`
    have viaReq : ∀ j, DS X (.init c.callee j) → j.covers l1 → DS X (.req c.callee j l1.mark) →
        RS X c.callee n2 l2 := by
      intro j hj hjc hreq
      obtain ⟨j', hj', hjc', t, ht⟩ := key j hj hjc hreq
      obtain ⟨g', hg', hdg'⟩ := coverage_concS hfb hab hgen hdeep hwf hα hfc hj' hjc' ht
      exact ⟨l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩
    have hapj := hα c.callee a.fact
    have hjc := applicable_sound hapj hac
    have hj0 := DS.initA hadd
    rcases coverageS hfb hab hgen hdeep hwf hα hfc _ hj0 hjc with ⟨g, hg, hdg⟩ | hreq | ⟨_, p, hp, hsreq, hpc⟩
    · exact fin _ g hj0 hjc hg hdg
    · exact viaReq _ hj0 hjc hreq
    · -- the position request is answered in the callee
      have hans := DS.sanswer hsreq hadd (ansOK_of hab (overlapB_of_common hac hpc))
      rcases coverageS hfb hab hgen hdeep hwf hα hfc _ hans hpc with ⟨g, hg, hdg⟩ | hreq | ⟨hroot, _⟩
      · exact fin _ g hans hpc hg hdg
      · exact viaReq _ hans hpc hreq
      · rw [sRootB_sAns hp] at hroot
        cases hroot

#print axioms reach_strongS

/-- THE VULNERABILITY THEOREM for `DS` (the analogue of `Coverage.vuln_found`). A concrete flow
    from the zero location of a root, through a chain of calls, to a location `l` at a sink node
    with a covering sink pattern gives a `vuln` object. Hypotheses: those of the base theorem
    (`Program.WF` and the abstraction contract C1); the overlap answer (`ansBelow = false`) and the full fallback
    (`fb = full`); either climb. -/
theorem vuln_foundS (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.P X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, DS X (.vuln M n s b) := by
  obtain ⟨l0, i, f, hf, hd, hdisj⟩ := reach_strongS hfb hab hgen hdeep hwf hα hR
  rcases check_sound hT hd hsc with htr | ⟨hrq, hist⟩
  · exact ⟨_, DS.vuln hf hs htr⟩
  · have hreq := DS.reqSink hf hs hrq
    rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
    · exact absurd ht (hist t)
    · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hreq
      rcases check_sound hT hd' hsc with htr' | ⟨_, hist'⟩
      · exact ⟨_, DS.vuln hf' hs htr'⟩
      · exact absurd ht (hist' t)

#print axioms vuln_foundS

/-- The vulnerability theorem for run 1 (`policy` with the empty demand, `policy1`). -/
theorem vuln_found_policy1S (hfb : X.fb = .full) (hab : X.ansBelow = false) (hgen : X.gen = false)
    (hdeep : X.deepAns = false) (hwf : X.P.WF)
    (hα1 : X.α = policy (fun _ => []))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.P X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, DS X (.vuln M n s b) :=
  vuln_foundS hfb hab hgen hdeep hwf (fun m a => by rw [hα1]; exact policy_applicable _ m a) hR hs hT hsc

#print axioms vuln_found_policy1S

end Coverage

/-! ## 7. Exactness of the normal layer -/

/-- The motive of `Exact.D_edgeOK` on the objects of `DS`: an abstract initial mark gives an
    abstract final mark, and a normal-layer edge denotes only real flows (for valid end
    locations; the start location is then valid too). -/
def SEdgeOK (P : Program) (ok : Loc → Prop) : SObj → Prop
  | .edge M i n f => (Exact.absB i.mark = true → Exact.absB f.fact.mark = true) ∧
      (f.demand = false → ∀ l0 l, den i f.fact l0 l → ok l → Flow P M l0 n l ∧ ok l0)
  | _ => True

/-- THE EXACTNESS INVARIANT for `DS` (the analogue of `Exact.D_edgeOK`). The step of `DS` uses a
    sub-statement (`sKeep`), so its normal results are real steps; an answer is an initial fact
    whose start is the identity; `sret` is a summary application like `ret`, its premise mark
    admits the marks of the added fact (`sAboveB`). -/
theorem DS_edgeOK {X : SCtx} {ok : Loc → Prop} (hmw : Exact.MarkWF X.P)
    (hfo : Exact.FiltOK X.P ok) (hbo : Exact.BackOK X.P ok) {o : SObj} (h : DS X o) :
    SEdgeOK X.P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun hi => by rw [Exact.startFact_mark]; exact hi, ?_⟩
    intro ha l0 l hd hok
    have e := Exact.startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    have hmk : ∀ e, e ∈ (sKeepP (X.fireB i f) s).edges → Exact.markEdgeB e.1.mark e.2.mark = true :=
      fun e he => hmw.stmt _ _ _ _ hE e (sKeep_mem he).1
    refine ⟨fun hi => Exact.transfer_abs hmk (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact hmk hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e (sKeep_mem he).1 _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE (sKeep_step hs), hok0⟩
  | reqStmt => trivial
  | sreqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    refine ⟨fun hi => ?_, ?_⟩
    · have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD.1 hi) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := ihG.1 (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · intro hla l0 l hd hok
      have e := Exact.limitF_exact hla
      rw [e] at hd hla
      have hra := Exact.applyEdge_demand hr' hla
      obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
      have haa := Exact.applyEdge_demand hx hxa
      have hfa := Exact.applyEdge_demand ha haa
      have hp2 : Exact.premOKB j.mark a.fact.mark = true :=
        Exact.premOK_of_sub (Exact.applicable_markSub happ)
      have hc2 : Exact.concOKB g.fact.mark a.fact.mark = true :=
        Exact.concOK_of (fun hA => ihG.1 (Exact.gate_abs (Exact.applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihD.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | @sret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hab _ hr he2 hr' ihD _ ihG =>
    refine ⟨fun hi => ?_, ?_⟩
    · have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD.1 hi) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := ihG.1 (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · intro hla l0 l hd hok
      have e := Exact.limitF_exact hla
      rw [e] at hd hla
      have hra := Exact.applyEdge_demand hr' hla
      obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
      have haa := Exact.applyEdge_demand hx hxa
      have hfa := Exact.applyEdge_demand ha haa
      have hp2 : Exact.premOKB j.mark a.fact.mark = true :=
        Exact.premOK_of_sub (fbOK_markSub hab)
      have hc2 : Exact.concOKB g.fact.mark a.fact.mark = true :=
        Exact.concOK_of (fun hA => ihG.1 (Exact.gate_abs (Exact.applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihD.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | sanswer => trivial
  | reqUp => trivial
  | sreqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨fun hi => Exact.cleanRes_abs (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms DS_edgeOK

/-- THE EXACTNESS THEOREM for `DS` (the analogue of `Exact.edge_exact`): under `MarkWF` and
    `FiltUp`, a normal-layer edge of `DS` denotes only real flows. -/
theorem edge_exactS {X : SCtx} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (hmw : Exact.MarkWF X.P) (hup : Exact.FiltUp X.P)
    (h : DS X (.edge M i n f)) (ha : f.demand = false) (hd : den i f.fact l0 l) :
    Flow X.P M l0 n l :=
  ((DS_edgeOK (ok := fun _ => True) hmw (Exact.filtUp_ok hup) (Exact.backOK_true X.P) h).2
    ha l0 l hd trivial).1

#print axioms edge_exactS

/-- THE EXACTNESS THEOREM FOR VALID LOCATIONS (the analogue of `Exact.edge_exact_valid`). -/
theorem edge_exact_validS {X : SCtx} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {l0 l : Loc} {ok : Loc → Prop} (hmw : Exact.MarkWF X.P) (hv : Exact.FiltValid X.P ok)
    (hbo : Exact.BackOK X.P ok)
    (h : DS X (.edge M i n f)) (ha : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow X.P M l0 n l ∧ ok l0 :=
  (DS_edgeOK hmw (Exact.filtValid_ok hv) hbo h).2 ha l0 l hd hok

#print axioms edge_exact_validS

/-- A complete edge of `DS` denotes only real flows (the hypotheses of `edge_exactS`). -/
theorem complete_exactS {X : SCtx} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {l0 l : Loc} (hmw : Exact.MarkWF X.P) (hup : Exact.FiltUp X.P)
    (h : DS X (.edge M i n f)) (hc : f.complete = true) (hd : den i f.fact l0 l) :
    Flow X.P M l0 n l :=
  edge_exactS hmw hup h (Exact.complete_demand hc) hd

#print axioms complete_exactS

/-! ## 8. The effect of the rule: no `[any]` read on the static root edge -/

theorem norm_base (x : AFact) : x.norm.fact.base = x.fact.base := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  unfold AFact.norm
  cases k with
  | star e => cases m <;> cases d <;> cases e <;> rfl
  | any => rfl
  | exact => rfl

theorem limitF_base {counted : Acc → Bool} {L : Nat} (f : AFact) :
    (limitF counted L f).fact.base = f.fact.base := by
  unfold limitF
  cases cutPath counted L f.fact.path <;> rfl

/-- A result of delta-concat is on the base of the target. -/
theorem applyEdge_base {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    r.fact.base = to.base := by
  obtain ⟨p, k, ap, m, _, _, _, hr⟩ := CoreAux.mem_applyEdge_facts_inv h
  rw [hr, norm_base]

/-- Every result of the step of `DS` is the untouched fact, or a result of a micro edge on which
    the rule does not fire. -/
theorem ds_step_from_kept {counted : Acc → Bool} {L : Nat} {P : MicroEdge → Bool} {f f' : AFact}
    {s : Stmt} (h : f' ∈ (transfer counted L (sKeepP P s) f).facts) :
    (memB f.fact.base s.touched = false ∧ f' = f) ∨
    ∃ e, e ∈ s.edges ∧ P e = false ∧
      ∃ y, y ∈ (applyEdge f e.1 e.2).facts ∧ f' = limitF counted L y := by
  rcases Exact.transfer_mem h with ⟨-, y, hy, rfl⟩ | ⟨hu, rfl⟩
  · obtain ⟨e, he, hye⟩ := Exact.applyAll_mem hy
    obtain ⟨he', hf⟩ := sKeep_mem he
    exact .inr ⟨e, he', hf, y, hye, rfl⟩
  · exact .inl ⟨hu, rfl⟩

/-- The micro edge `b.p.*` of the interpreter (the `*`-tail pattern with the mark `*`). -/
def pat (b : Base) (p : List Acc) : PFact := ⟨b, p, .star Excl.empty, .star⟩

/-- The interpreter's static read `x = C.s` (`interpreter.md` §2.2): `S.* → S.*`,
    `S.<C>.s.* → x.*`, touched `{S, x}`; `p = [<C>, s]` (Go `x = G`: `p = [<G>]`). -/
def readStmt (sB x : Base) (p : List Acc) : Stmt :=
  ⟨[sB, x], [(pat sB [], pat sB []), (pat sB p, pat x [])]⟩

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (CoreAux.beq_iff.mp hb) h

/-- The rule fires on the read of `readStmt` on the abstract static root edge. -/
theorem read_fires {sB x : Base} {p : List Acc} {E E0 : Excl} (hx : x ≠ sB) (hp : p ≠ [])
    (hE : E.admits p = true) :
    sFireB sB ⟨sB, [], .star E0, .star⟩ ⟨⟨sB, [], .star E, .star⟩, false⟩ (pat sB p, pat x []) = true := by
  have hne : (!p.isEmpty) = true := by
    cases p with
    | nil => exact absurd rfl hp
    | cons _ _ => rfl
  unfold sFireB sRootFB sReadB
  simp only [sRootB, pat, Nat.beq_refl, hne, beq_false_of_ne hx, admitsTailB, hE]
  rfl

/-- THE RULE'S EFFECT, in `D`: the read `x = C.s` on the abstract static root edge
    `(S, [], *, E0, *) → (S, [], */E, *)` gives `(x, ., [any], *)` in the DEMAND layer. -/
theorem read_D {counted : Acc → Bool} {L : Nat} {sB x : Base} {p : List Acc} {E : Excl}
    (hp : p ≠ []) (hE : E.admits p = true) :
    (⟨⟨x, [], .any, .star⟩, true⟩ : AFact) ∈
      (transfer counted L (readStmt sB x p) ⟨⟨sB, [], .star E, .star⟩, false⟩).facts := by
  obtain ⟨a, r, rfl⟩ : ∃ a r, p = a :: r := by
    cases p with
    | nil => exact absurd rfl hp
    | cons a r => exact ⟨a, r, rfl⟩
  have hres : (⟨⟨x, [], .any, .star⟩, true⟩ : AFact) ∈
      (applyEdge ⟨⟨sB, [], .star E, .star⟩, false⟩ (pat sB (a :: r)) (pat x [])).facts := by
    have hE' : E.admits (a :: r) = true := hE
    simp only [applyEdge, pat, Nat.beq_refl, relate, dropPrefix, aboveCase, admitsTailB, hE',
      if_true, markGate, markComp, Kind.isAny, Bool.false_and, Bool.not_false, Bool.or_true]
    exact List.mem_singleton.mpr rfl
  have hmem : sB ∈ (readStmt sB x (a :: r)).touched := List.mem_cons_self
  unfold transfer
  rw [if_pos (CoreAux.memB_iff.mpr hmem)]
  exact List.mem_map.mpr ⟨_, CoreAux.mem_applyAll_facts (List.mem_cons_of_mem _ List.mem_cons_self) hres, rfl⟩

/-- THE RULE'S EFFECT, in `DS`: on the same edge, every result of the step is on the static base:
    there is NO fact on `x`, in particular no `[any]` read. The rule raises the position request
    instead (`read_fires`, rule `sreqStmt`). -/
theorem read_DS {counted : Acc → Bool} {L : Nat} {sB x : Base} {p : List Acc} {E E0 : Excl}
    (hx : x ≠ sB) (hp : p ≠ []) (hE : E.admits p = true) {f' : AFact}
    (h : f' ∈ (transfer counted L (sKeep sB ⟨sB, [], .star E0, .star⟩
      ⟨⟨sB, [], .star E, .star⟩, false⟩ (readStmt sB x p)) ⟨⟨sB, [], .star E, .star⟩, false⟩).facts) :
    f'.fact.base = sB := by
  rcases ds_step_from_kept h with ⟨_, rfl⟩ | ⟨e, he, hf, y, hy, rfl⟩
  · rfl
  · rw [limitF_base, applyEdge_base hy]
    rcases List.mem_cons.mp he with rfl | he'
    · rfl
    · rw [List.mem_singleton.mp he', read_fires hx hp hE] at hf
      cases hf

/-- In `DS` the read raises the position request for `p` on the static root premise. -/
theorem read_sreq {X : SCtx} {M : MethodId} {n n' : Node} {x : Base} {p : List Acc} {E E0 : Excl}
    (hg : X.gen = false) (hx : x ≠ X.sB) (hp : p ≠ []) (hE : E.admits p = true)
    (hf : DS X (.edge M ⟨X.sB, [], .star E0, .star⟩ n ⟨⟨X.sB, [], .star E, .star⟩, false⟩))
    (he : (M, n, Instr.stmt (readStmt X.sB x p), n') ∈ X.P.edges) :
    DS X (.sreq M ⟨X.sB, [], .star E0, .star⟩ p) := by
  have h := DS.sreqStmt (e := (pat X.sB p, pat x [])) hf he
    (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [fireB_old hg]; exact read_fires hx hp hE)
  rw [reqP_old hg] at h
  exact h

#print axioms read_D
#print axioms read_DS
#print axioms read_sreq

theorem applyAll_reqs_star {c : AFact} :
    ∀ {es : List MicroEdge}, (∀ e, e ∈ es → e.1.mark = .star) → (applyAll c es).reqs = []
  | [], _ => rfl
  | e :: es, h => by
    show (applyEdge c e.1 e.2).reqs ++ (applyAll c es).reqs = []
    rw [applyEdge_reqs_of_star (h e List.mem_cons_self),
      applyAll_reqs_star (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    rfl

/-- A statement whose micro edges are mark agnostic raises no mark request. -/
theorem transfer_reqs_star {counted : Acc → Bool} {L : Nat} {s : Stmt} {c : AFact}
    (h : ∀ e, e ∈ s.edges → e.1.mark = .star) : (transfer counted L s c).reqs = [] := by
  unfold transfer
  split
  · exact applyAll_reqs_star h
  · rfl

theorem sKeep_star {P : MicroEdge → Bool} {s : Stmt}
    (h : ∀ e, e ∈ s.edges → e.1.mark = .star) :
    ∀ e, e ∈ (sKeepP P s).edges → e.1.mark = .star :=
  fun e he => h e (sKeep_mem he).1

theorem check_overlap_of {i s : PFact} {f : AFact} {T : Mark} (hs : s.mark = .conc T)
    (h : check i f s ≠ .none) : overlapB f.fact s = true := by
  cases ho : overlapB f.fact s with
  | true => rfl
  | false => exact absurd (CoreAux.check_eq_none hs ho) h

/-! ## 9. Example: the rule turns a demand vulnerability into a normal one

`root: C1.f = source(); A()`, `A: B()`, `B: x = C1.f; sink(x)`. Methods `0` (root), `1` (`A`),
`2` (`B`). The static base is `S = 1`, the class accessor `<C1>` is `10`, the field `f` is `11`,
`x` is base `3`, the source mark is `7`. The source rule writes the static field directly
(`zero → S.<C1>.f.$(7)`); the calls bind `S.* → S.*` both ways; the class accessor is not
counted by the field limit.

`D`: `B` starts from the abstract static root `(S, [], *, {}, *)` (the run-1 abstraction), the
read is the case `above`, and `x` gets `(x, ., [any], *)` in the demand layer. The sink asks for
the mark 7; the request climbs to `A`, `A` answers it with `(S, [], *, {}, 7)` (start `[any]`,
demand), `B` gets `(S, [], [any], 7)` and answers its own request with `(S, [], *, {}, 7)`, whose
read is again `above`: the vulnerability is in the demand layer (`d_vuln`), and `D` has NO
normal-layer vulnerability (`d_only_demand`).

`DS`: the read on `B`'s static root edge gives no fact and the position request
`(B, Sroot, <C1>.f)` (`sB_req`); it climbs to `A` (`sA_req`: `A`'s edge has its premise on `S` and
gives `B` the added fact `(S, [], *, {}, *)`, above `<C1>.f`). `A`'s added fact `(S, <C1>.f, $, 7)`
is at the position: `A` answers with `(S, <C1>.f, *, {}, *)` (`jA_ans`), passes it to `B`, and this
added fact of `B`, again at the position, answers `B`'s request (`jB_ans`). `B`'s answer reads `x`
in the normal layer (`eB_ans1`); the
sink asks for the mark 7 (`rB_ans`); the request climbs to `A`'s answer (`rA_ans`), which the
root's concrete added fact `(S, <C1>.f, $, 7)` answers EXACTLY (`(S, <C1>.f, $, 7)`, normal); `A`
passes it to `B`, `B` answers with the same exact fact, and the read gives `(x, ., $, 7)` in the
normal layer: the vulnerability is in the normal layer (`ds_vuln_normal`). -/

namespace Example

def S : Base := 1
def xB : Base := 3
def C1 : Acc := 10
def fA : Acc := 11
def T : Mark := 7

/-- The abstract static root `(S, [], *, {}, *)`. -/
def Sroot : PFact := pat S []
/-- The binding `S.* → S.*`. -/
def bindS : MicroEdge := (pat S [], pat S [])
/-- The tainted static field `(S, <C1>.f, $, 7)`. -/
def wS : PFact := ⟨S, [C1, fA], .exact, .conc T⟩
/-- The answer of the position request: `(S, <C1>.f, *, {}, *)`. -/
def Ans : PFact := sAns S [C1, fA]
/-- `C1.f = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, wS)]⟩
/-- `x = C1.f`. -/
def rd : Stmt := readStmt S xB [C1, fA]
def readE : MicroEdge := (pat S [C1, fA], pat xB [])
def cA : Call := ⟨1, [S], [bindS], [bindS]⟩
def cB : Call := ⟨2, [S], [bindS], [bindS]⟩
def prog : Program :=
  ⟨fun _ => 0, fun M => if M = 0 then 2 else 1,
   [(0, 0, .stmt src, 1), (0, 1, .call cA, 2), (1, 0, .call cB, 1), (2, 0, .stmt rd, 1)]⟩
def sinkPat : PFact := ⟨xB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(2, 1, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C1
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- Run 1 with the static rule (wide climb, overlap answer, full fallback). -/
def X : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, false, .full, false, false⟩

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := List.mem_cons_self
theorem m_cA : (0, 1, Instr.call cA, 2) ∈ prog.edges :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem m_cB : (1, 0, Instr.call cB, 1) ∈ prog.edges :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem m_rd : (2, 0, Instr.stmt rd, 1) ∈ prog.edges :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
theorem m_sink : (2, 1, sinkPat) ∈ sinks := List.mem_cons_self

/-! ### `DS`: the derivation of the normal-layer vulnerability -/

theorem r_start : DS X (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) :=
  DS.start (DS.root List.mem_cons_self)
/-- The root writes the tainted static field. -/
theorem r_src : DS X (.edge 0 zeroFact 1 ⟨wS, false⟩) :=
  DS.step r_start m_src (by decide)
theorem aA_w : DS X (.added 1 wS) :=
  DS.added (a := ⟨wS, false⟩) r_src m_cA List.mem_cons_self (by decide)
theorem jA_root : DS X (.init 1 Sroot) := by
  have h : X.α 1 wS = Sroot := by decide
  exact h ▸ DS.initA aA_w
theorem eA_root : DS X (.edge 1 Sroot 0 ⟨Sroot, false⟩) := DS.start jA_root
theorem aB_root : DS X (.added 2 Sroot) :=
  DS.added (a := ⟨Sroot, false⟩) eA_root m_cB List.mem_cons_self (by decide)
theorem jB_root : DS X (.init 2 Sroot) := by
  have h : X.α 2 Sroot = Sroot := by decide
  exact h ▸ DS.initA aB_root
/-- `B`'s static root edge at the read. -/
theorem eB_root : DS X (.edge 2 Sroot 0 ⟨Sroot, false⟩) := DS.start jB_root
/-- On `B`'s static root edge the read gives NO fact: the only result is the static root. -/
theorem eB_root_step :
    (transfer X.counted X.FL (sKeep X.sB Sroot ⟨Sroot, false⟩ rd) ⟨Sroot, false⟩).facts =
      [⟨Sroot, false⟩] := by decide
/-- RAISE: the position request `(B, Sroot, <C1>.f)`. -/
theorem sB_req : DS X (.sreq 2 Sroot [C1, fA]) :=
  DS.sreqStmt (e := readE) eB_root m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- CLIMB: `A` passes its abstract static root into `B`. -/
theorem sA_req : DS X (.sreq 1 Sroot [C1, fA]) :=
  DS.sreqUp (a := ⟨Sroot, false⟩) (e := bindS) sB_req eA_root m_cB rfl List.mem_cons_self
    (by decide) (by decide)
/-- ANSWER in `A`, at the first place that can satisfy the request: `A`'s added fact
    `(S, <C1>.f, $, 7)` is at the requested position; the answer is `(S, <C1>.f, *, {}, *)`. -/
theorem jA_ans : DS X (.init 1 Ans) := DS.sanswer sA_req aA_w (by decide)
theorem eA_ans : DS X (.edge 1 Ans 0 ⟨Ans, false⟩) := DS.start jA_ans
/-- `A` passes the answer to `B`: an added fact of `B` at the requested position, which answers. -/
theorem aB_ans : DS X (.added 2 Ans) :=
  DS.added (a := ⟨Ans, false⟩) eA_ans m_cB List.mem_cons_self (by decide)
theorem jB_ans : DS X (.init 2 Ans) := DS.sanswer sB_req aB_ans (by decide)
theorem eB_ans0 : DS X (.edge 2 Ans 0 ⟨Ans, false⟩) := DS.start jB_ans
/-- The answer reads `x` in the NORMAL layer: `(x, ., *, {}, *)`. -/
theorem eB_ans1 : DS X (.edge 2 Ans 1 ⟨pat xB [], false⟩) :=
  DS.step eB_ans0 m_rd (by decide)
/-- The sink asks for the mark 7 on `B`'s answer. -/
theorem rB_ans : DS X (.req 2 Ans T) := DS.reqSink eB_ans1 m_sink (by decide)
/-- The mark request climbs to `A`'s answer (its added fact `(S, <C1>.f, *, {}, *)`). -/
theorem rA_ans : DS X (.req 1 Ans T) :=
  DS.reqUp (a := ⟨Ans, false⟩) (e := bindS) rB_ans eA_ans m_cB rfl List.mem_cons_self
    (by decide) (by decide) (by decide)
/-- The root's concrete added fact answers it EXACTLY: `(S, <C1>.f, $, 7)`. -/
theorem jA_w : DS X (.init 1 wS) := by
  have h : X.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer rA_ans aA_w rfl (by decide)
theorem eA_w : DS X (.edge 1 wS 0 ⟨wS, false⟩) := DS.start jA_w
theorem aB_w : DS X (.added 2 wS) :=
  DS.added (a := ⟨wS, false⟩) eA_w m_cB List.mem_cons_self (by decide)
theorem jB_w : DS X (.init 2 wS) := by
  have h : X.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer rB_ans aB_w rfl (by decide)
theorem eB_w0 : DS X (.edge 2 wS 0 ⟨wS, false⟩) := DS.start jB_w
/-- The exact read: `(x, ., $, 7)` in the normal layer. -/
theorem eB_w1 : DS X (.edge 2 wS 1 ⟨⟨xB, [], .exact, .conc T⟩, false⟩) :=
  DS.step eB_w0 m_rd (by decide)
/-- THE NORMAL-LAYER VULNERABILITY of `DS`. -/
theorem ds_vuln_normal : DS X (.vuln 2 1 sinkPat false) :=
  DS.vuln eB_w1 m_sink (by decide)

#print axioms ds_vuln_normal

/-! ### `D`: only a demand-layer vulnerability -/

/-- Run 1 without the static rule (the base closure `D`). -/
abbrev DD : Obj → Prop := D prog counted 2 α1 sinks [0]

theorem d_start : DD (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) := D.start (D.root List.mem_cons_self)
theorem d_src : DD (.edge 0 zeroFact 1 ⟨wS, false⟩) := D.step d_start m_src (by decide)
theorem d_aA : DD (.added 1 wS) :=
  D.added (a := ⟨wS, false⟩) d_src m_cA List.mem_cons_self (by decide)
theorem d_jA : DD (.init 1 Sroot) := by
  have h : α1 1 wS = Sroot := by decide
  exact h ▸ D.initA d_aA
theorem d_eA : DD (.edge 1 Sroot 0 ⟨Sroot, false⟩) := D.start d_jA
theorem d_aB : DD (.added 2 Sroot) :=
  D.added (a := ⟨Sroot, false⟩) d_eA m_cB List.mem_cons_self (by decide)
theorem d_jB : DD (.init 2 Sroot) := by
  have h : α1 2 Sroot = Sroot := by decide
  exact h ▸ D.initA d_aB
theorem d_eB0 : DD (.edge 2 Sroot 0 ⟨Sroot, false⟩) := D.start d_jB
/-- `D`: the read on the static root edge is `(x, ., [any], *)` in the DEMAND layer. -/
theorem d_eB1 : DD (.edge 2 Sroot 1 ⟨⟨xB, [], .any, .star⟩, true⟩) := D.step d_eB0 m_rd (by decide)
theorem d_rB : DD (.req 2 Sroot T) := D.reqSink d_eB1 m_sink (by decide)
theorem d_rA : DD (.req 1 Sroot T) :=
  D.reqUp (a := ⟨Sroot, false⟩) (e := bindS) d_rB d_eA m_cB rfl List.mem_cons_self
    (by decide) (by decide) (by decide)
/-- The answer at the static root: `(S, [], *, {}, 7)`, which starts as `[any]` (demand). -/
def SrootT : PFact := ⟨S, [], .star Excl.empty, .conc T⟩
theorem d_jAT : DD (.init 1 SrootT) := by
  have h : answerInit Sroot wS T = SrootT := by decide
  exact h ▸ D.answer d_rA d_aA rfl (by decide)
theorem d_eAT : DD (.edge 1 SrootT 0 ⟨⟨S, [], .any, .conc T⟩, true⟩) := D.start d_jAT
theorem d_aBT : DD (.added 2 ⟨S, [], .any, .conc T⟩) :=
  D.added (a := ⟨⟨S, [], .any, .conc T⟩, true⟩) d_eAT m_cB List.mem_cons_self (by decide)
theorem d_jBT : DD (.init 2 SrootT) := by
  have h : answerInit Sroot ⟨S, [], .any, .conc T⟩ T = SrootT := by decide
  exact h ▸ D.answer d_rB d_aBT rfl (by decide)
theorem d_eBT0 : DD (.edge 2 SrootT 0 ⟨⟨S, [], .any, .conc T⟩, true⟩) := D.start d_jBT
theorem d_eBT1 : DD (.edge 2 SrootT 1 ⟨⟨xB, [], .any, .conc T⟩, true⟩) :=
  D.step d_eBT0 m_rd (by decide)
/-- `D` reports the vulnerability in the DEMAND layer. -/
theorem d_vuln : DD (.vuln 2 1 sinkPat true) := D.vuln d_eBT1 m_sink (by decide)

#print axioms d_vuln

/-! The invariant of `D` on this program: `B` (method 2) has initial facts only at the static
root position (the run-1 abstraction and the mark answers keep the base and the path), so every
read of `x` in `B` is the case `above` or an `[any]` fact: a demand-layer fact. -/

theorem startFact_base (i : PFact) : (startFact i).fact.base = i.base := by
  obtain ⟨b, p, k, m⟩ := i
  cases k <;> cases m <;> rfl

theorem startFact_path (i : PFact) : (startFact i).fact.path = i.path := by
  obtain ⟨b, p, k, m⟩ := i
  cases k <;> cases m <;> rfl

theorem startFact_any (i : PFact) :
    (startFact i).fact.kind = .any → (startFact i).demand = true := by
  obtain ⟨b, p, k, m⟩ := i
  cases k <;> cases m <;> intro h <;> first | rfl | cases h

theorem limitF_demand_true {counted : Acc → Bool} {L : Nat} {y : AFact} (h : y.demand = true) :
    (limitF counted L y).demand = true := by
  unfold limitF
  cases cutPath counted L y.fact.path with
  | none => exact h
  | some _ => rfl

/-- The case `above` on a fact at the empty path gives a demand-layer result, unless the fact is
    an `[any]` fact in the normal layer. -/
theorem above_demand {c r : AFact} {fr to : PFact} (hcp : c.fact.path = []) (hfp : fr.path ≠ [])
    (hany : c.fact.kind = .any → c.demand = true) (hr : r ∈ (applyEdge c fr to).facts) :
    r.demand = true := by
  obtain ⟨p, k, ap, m, hg, -, -, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hr
  have hd : (c.demand || ap) = true := by
    obtain ⟨a, rest, hfr⟩ : ∃ a rest, fr.path = a :: rest := by
      cases h : fr.path with
      | nil => exact absurd h hfp
      | cons a rest => exact ⟨a, rest, rfl⟩
    unfold CoreAux.geo at hg
    rw [hfr, hcp] at hg
    change aboveCase c.fact.kind fr.kind (a :: rest) to.path to.kind = some (p, k, ap) at hg
    cases hk : c.fact.kind with
    | any => rw [hany hk]; rfl
    | exact =>
      rw [hk] at hg
      cases hg
    | star e =>
      rw [hk] at hg
      unfold aboveCase at hg
      split at hg
      · cases hto : to.kind <;> rw [hto] at hg <;>
          simp only [Option.some.injEq, Prod.mk.injEq] at hg <;>
          obtain ⟨-, -, rfl⟩ := hg <;> simp [Kind.isAny]
      · cases hg
  rw [hd]
  exact Exact.norm_true_demand _

theorem check_overlap {i s : PFact} {f : AFact} {T : Mark} (hs : s.mark = .conc T)
    (h : check i f s = .triggered) : overlapB f.fact s = true := by
  cases ho : overlapB f.fact s with
  | true => rfl
  | false =>
    rw [CoreAux.check_eq_none hs ho] at h
    cases h

theorem overlap_base {a b : PFact} (h : overlapB a b = true) : a.base = b.base := by
  unfold overlapB at h
  simp only [Bool.and_eq_true] at h
  exact CoreAux.beq_iff.mp h.1

theorem edges2 {n n' : Node} {ins : Instr} (h : (2, n, ins, n') ∈ prog.edges) :
    n = 0 ∧ ins = Instr.stmt rd ∧ n' = 1 := by
  simp [prog] at h
  exact h

theorem calls {M : MethodId} {n n' : Node} {c : Call} (h : (M, n, Instr.call c, n') ∈ prog.edges) :
    c = cA ∨ c = cB := by
  simp [prog] at h
  rcases h with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
  · exact .inl h
  · exact .inr h

theorem policy_root {m : MethodId} {a : PFact} (hb : a.base = S) :
    (α1 m a).base = S ∧ (α1 m a).path = [] := by
  unfold α1 policy
  split
  · rename_i hz
    rw [hz] at hb
    exact absurd hb (by decide)
  · split
    · rename_i h
      cases h
    · exact ⟨hb, rfl⟩

/-- The invariant of `D` on the example program. -/
def DInv : Obj → Prop
  | .init M i => M = 2 → i.base = S ∧ i.path = []
  | .edge M i n f => M = 2 → i.base = S ∧ i.path = [] ∧
      (n = 0 → f.fact.base = S ∧ f.fact.path = [] ∧ (f.fact.kind = .any → f.demand = true)) ∧
      (n = 1 → f.fact.base = xB → f.demand = true)
  | .added M a => M = 2 → a.base = S
  | .req M i _ => M = 2 → i.base = S ∧ i.path = []
  | .vuln _ _ _ d => d = true

theorem dInv_all {o : Obj} (h : DD o) : DInv o := by
  induction h with
  | root hM =>
    intro h2
    rw [List.mem_singleton.mp hM] at h2
    exact absurd h2 (by decide)
  | @start M i _ ih =>
    intro h2
    obtain ⟨hb, hp⟩ := ih h2
    refine ⟨hb, hp, fun _ => ⟨by rw [startFact_base, hb], by rw [startFact_path, hp],
      startFact_any i⟩, fun h1 => ?_⟩
    have h1' : (0 : Nat) = 1 := h1
    exact absurd h1' (by decide)
  | @step M i n f n' s f' _ he hf ih =>
    intro h2
    subst h2
    obtain ⟨hn, hs, hn'⟩ := edges2 he
    subst hn hn'
    cases hs
    obtain ⟨hib, hip, h0, -⟩ := ih rfl
    obtain ⟨hfb, hfp, hfa⟩ := h0 rfl
    refine ⟨hib, hip, fun h => absurd h (by decide), fun _ hx => ?_⟩
    rcases Exact.transfer_mem hf with ⟨-, y, hy, rfl⟩ | ⟨hu, rfl⟩
    · obtain ⟨e, he', hye⟩ := Exact.applyAll_mem hy
      rcases List.mem_cons.mp he' with rfl | he''
      · rw [limitF_base, applyEdge_base hye] at hx
        exact absurd hx (by decide)
      · rw [List.mem_singleton.mp he''] at hye
        exact limitF_demand_true (above_demand hfp (by decide) hfa hye)
    · rw [hfb] at hu
      exact absurd hu (by decide)
  | @reqStmt M i n f n' s t _ _ _ ih =>
    intro h2
    obtain ⟨hb, hp, _⟩ := ih h2
    exact ⟨hb, hp⟩
  | @pass M i n f n' c _ he _ ih =>
    intro h2
    subst h2
    cases (edges2 he).2.1
  | @added M i n f n' c e a _ he he1 ha ih =>
    intro h2
    rcases calls he with rfl | rfl
    · exact absurd h2 (by decide)
    · rw [List.mem_singleton.mp he1] at ha
      exact applyEdge_base ha
  | @initA m a _ ih =>
    intro h2
    exact policy_root (ih h2)
  | @ret M i n f n' c e1 a j g r e2 r' _ he _ _ _ _ _ _ _ _ _ _ _ =>
    intro h2
    subst h2
    cases (edges2 he).2.1
  | @reqSink M i n f s t _ _ _ ih =>
    intro h2
    obtain ⟨hb, hp, _⟩ := ih h2
    exact ⟨hb, hp⟩
  | @answer M i t a _ _ _ _ ihr _ =>
    intro h2
    obtain ⟨hb, hp⟩ := ihr h2
    exact ⟨by rw [answerInit_base]; exact hb, by rw [answerInit_path]; exact hp⟩
  | @reqUp m j t M ic n f n' c e a _ _ he _ _ _ _ _ _ _ =>
    intro h2
    subst h2
    cases (edges2 he).2.1
  | @vuln M i n f s _ hs hc ih =>
    simp only [sinks, List.mem_singleton, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact (ih rfl).2.2.2 rfl (overlap_base (check_overlap rfl hc))
  | @clean M i n f n' cl f' _ he _ _ =>
    intro h2
    subst h2
    cases (edges2 he).2.1
  | @reqClean M i n f n' cl t _ he _ _ =>
    intro h2
    subst h2
    cases (edges2 he).2.1
  | @filt M i n f n' b may _ he _ _ =>
    intro h2
    subst h2
    cases (edges2 he).2.1

/-- `D` has NO normal-layer vulnerability on this program: every vulnerability is in the demand
    layer. -/
theorem d_only_demand {M : MethodId} {n : Node} {s : PFact} {d : Bool}
    (h : DD (.vuln M n s d)) : d = true :=
  dInv_all h

#print axioms d_only_demand

/-- THE EXAMPLE (theorem 3). On `root: C1.f = source(); A()`, `A: B()`, `B: x = C1.f; sink(x)`,
    run 1 without the rule (`D`) reports the vulnerability only in the demand layer, and run 1
    with the rule (`DS`) reports it in the normal layer. -/
theorem example_effect :
    DD (.vuln 2 1 sinkPat true) ∧ (∀ M n s d, DD (.vuln M n s d) → d = true) ∧
    DS X (.vuln 2 1 sinkPat false) :=
  ⟨d_vuln, fun _ _ _ _ h => d_only_demand h, ds_vuln_normal⟩

#print axioms example_effect

end Example

/-! ## 10. The record of the narrow climb: `CexAbove`

`root: C.f = source(); caller()`, `caller: C.s = null; r = m(); sink(r)`, `m: y = C.f; return y`.
Methods `0` (root), `1` (`caller`), `2` (`m`); static base `S = 1`; `<C> = 10`, `f = 11`,
`s = 12`; `r = 2`, `y = 3`, `ret = 4`; mark 7. `C.s = null` is the strong static write
`S.* →_{<C>} S.*`, `S.<C>.* →_{s} S.<C>.*` (the value is untracked).

The flow `S.<C>.f (7)` → `caller` (untouched by the write of `C.s`) → `m` reads it → `ret` → `r` →
sink is real (`cex_reach`). In `caller` (static root `(S, [], *, {}, *)`) the write gives
`(S, [], */{<C>}, *)` and, by the case `above` of the keep edge `S.<C>.* →_{s} S.<C>.*`,
`(S, <C>, [any], *)` (demand), the fact that covers `S.<C>.f` at the call.

THE RECORD (`Xu`: the NARROW climb, which climbs only through an added fact that is the static
root, and no fallback). The added fact `(S, <C>, [any], *)` lies above `m`'s answer
`(S, <C>.f, *, {}, *)` and is not the static root, and `(S, [], */{<C>}, *)` does not admit `<C>.f`:
nothing climbs and nothing reads the answer; there is no vulnerability object
(`cex_user_misses`). This refutes the NARROW climb (my first formalisation), not the design.

THE FIRST DESIGN WITH THE WIDE CLIMB (`Xd`; the final rule is `Design`, §14). The WIDE climb goes through the caller edge `Sroot → (S, <C>, [any], *)` (its
premise is on `S`); the caller's added fact `(S, <C>.f, $, 7)` answers at the requested position;
the answer `(S, <C>.f, *, {}, *)` passes `C.s = null` precisely and `m` gets it as an added fact at
the position. The vulnerability is reported in the NORMAL layer (`x_vuln_normal`). (The full
fallback also gives the demand result, as `D` does.) -/

namespace CexAbove

def S : Base := 1
def rB : Base := 2
def yB : Base := 3
def retB : Base := 4
def C : Acc := 10
def fA : Acc := 11
def sA : Acc := 12
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- The tainted static field `(S, <C>.f, $, 7)`. -/
def wS : PFact := ⟨S, [C, fA], .exact, .conc T⟩
def wF : AFact := ⟨wS, false⟩
/-- The answer `(S, <C>.f, *, {}, *)`. -/
def Ans : PFact := sAns S [C, fA]
/-- The caller's facts after `C.s = null`: `(S, [], */{<C>}, *)` and `(S, <C>, [any], *)`. -/
def a1 : PFact := ⟨S, [], .star (.set [C]), .star⟩
def a2 : PFact := ⟨S, [C], .any, .star⟩
def a1F : AFact := ⟨a1, false⟩
def a2F : AFact := ⟨a2, true⟩
/-- root: `C.f = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, wS)]⟩
/-- caller: `C.s = null`. -/
def wr : Stmt :=
  ⟨[S], [(⟨S, [], .star (.set [C]), .star⟩, pat S []), (⟨S, [C], .star (.set [sA]), .star⟩, pat S [C])]⟩
/-- m: `y = C.f`. -/
def rd : Stmt := readStmt S yB [C, fA]
def readE : MicroEdge := (pat S [C, fA], pat yB [])
/-- m: `return y`. -/
def rt : Stmt := ⟨[retB, yB], [(pat yB [], pat yB []), (pat yB [], pat retB [])]⟩
def retE : MicroEdge := (pat retB [], pat rB [])
def cC : Call := ⟨1, [S], [bindS], [bindS]⟩
def cm : Call := ⟨2, [S, rB], [bindS], [bindS, retE]⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 2,
   [(0, 0, .stmt src, 1), (0, 1, .call cC, 2), (1, 0, .stmt wr, 1), (1, 1, .call cm, 2),
    (2, 0, .stmt rd, 1), (2, 1, .stmt rt, 2)]⟩
def sinkPat : PFact := ⟨rB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(1, 2, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- The NARROW climb without a fallback (the first formalisation). -/
def Xu : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, false, false, .off, false, false⟩
/-- The corrected design: the wide climb, the overlap answer, the full fallback. -/
def Xd : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, false, .full, false, false⟩
/-- Run 1 without the rule. -/
abbrev DD : Obj → Prop := D prog counted 2 α1 sinks [0]

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cC : (0, 1, Instr.call cC, 2) ∈ prog.edges := by simp [prog]
theorem m_wr : (1, 0, Instr.stmt wr, 1) ∈ prog.edges := by simp [prog]
theorem m_cm : (1, 1, Instr.call cm, 2) ∈ prog.edges := by simp [prog]
theorem m_rd : (2, 0, Instr.stmt rd, 1) ∈ prog.edges := by simp [prog]
theorem m_rt : (2, 1, Instr.stmt rt, 2) ∈ prog.edges := by simp [prog]
theorem m_sink : (1, 2, sinkPat) ∈ sinks := List.mem_cons_self

/-- Every program edge. -/
theorem edgesU {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cC ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt wr ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .call cm ∧ n' = 2) ∨
    (M = 2 ∧ n = 0 ∧ ins = .stmt rd ∧ n' = 1) ∨ (M = 2 ∧ n = 1 ∧ ins = .stmt rt ∧ n' = 2) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The program is well formed (the hypothesis of the base vulnerability theorem). -/
theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

#print axioms wf

/-- THE CONCRETE FLOW: the source at `S.<C>.f` reaches `r` at the sink of `caller`. -/
theorem cex_reach : Reach prog [0] 1 2 ⟨rB, [], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, fA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, wS), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have hm1 : Flow prog 2 ⟨S, [C, fA], T⟩ 1 ⟨yB, [], T⟩ :=
    Flow.step (Flow.start 2 ⟨S, [C, fA], T⟩) m_rd
      (.inr ⟨readE, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have hm2 : Flow prog 2 ⟨S, [C, fA], T⟩ 2 ⟨retB, [], T⟩ :=
    Flow.step hm1 m_rt
      (.inr ⟨(pat yB [], pat retB []), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have hc1 : Flow prog 1 ⟨S, [C, fA], T⟩ 1 ⟨S, [C, fA], T⟩ :=
    Flow.step (Flow.start 1 ⟨S, [C, fA], T⟩) m_wr
      (.inr ⟨(⟨S, [C], .star (.set [sA]), .star⟩, pat S [C]),
        List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [fA], [fA], rfl, rfl, rfl, rfl, rfl⟩)
  have hc2 : Flow prog 1 ⟨S, [C, fA], T⟩ 2 ⟨rB, [], T⟩ :=
    Flow.call hc1 m_cm List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, fA], [C, fA], rfl, rfl, rfl, rfl, rfl⟩ hm2
      (List.mem_cons_of_mem _ List.mem_cons_self)
      ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
  exact Reach.down (Reach.root List.mem_cons_self h0) m_cC List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, fA], [C, fA], rfl, rfl, rfl, rfl, rfl⟩ hc2

theorem cex_covers : sinkPat.covers ⟨rB, [], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms cex_reach

/-! ### `D` reports the vulnerability (demand layer) -/

theorem d_start : DD (.edge 0 zeroFact 0 zfF) := D.start (D.root List.mem_cons_self)
theorem d_src : DD (.edge 0 zeroFact 1 wF) := D.step d_start m_src (by decide)
theorem d_aC : DD (.added 1 wS) := D.added (a := wF) d_src m_cC List.mem_cons_self (by decide)
theorem d_jC : DD (.init 1 Sroot) := by
  have h : α1 1 wS = Sroot := by decide
  exact h ▸ D.initA d_aC
theorem d_eC0 : DD (.edge 1 Sroot 0 SrootF) := D.start d_jC
theorem d_eC1 : DD (.edge 1 Sroot 1 a2F) := D.step d_eC0 m_wr (by decide)
theorem d_am : DD (.added 2 a2) := D.added (a := a2F) d_eC1 m_cm List.mem_cons_self (by decide)
theorem d_jm : DD (.init 2 Sroot) := by
  have h : α1 2 a2 = Sroot := by decide
  exact h ▸ D.initA d_am
theorem d_em0 : DD (.edge 2 Sroot 0 SrootF) := D.start d_jm
theorem d_em1 : DD (.edge 2 Sroot 1 ⟨⟨yB, [], .any, .star⟩, true⟩) := D.step d_em0 m_rd (by decide)
theorem d_em2 : DD (.edge 2 Sroot 2 ⟨⟨retB, [], .any, .star⟩, true⟩) := D.step d_em1 m_rt (by decide)
/-- `caller` reads `m`'s static-root summary with its `[any]` static fact. -/
theorem d_eC2 : DD (.edge 1 Sroot 2 ⟨⟨rB, [], .any, .star⟩, true⟩) :=
  D.ret (a := a2F) (r := ⟨⟨retB, [], .any, .star⟩, true⟩) (r' := ⟨⟨rB, [], .any, .star⟩, true⟩)
    (e2 := retE) d_eC1 m_cm List.mem_cons_self (by decide) d_jm (by decide) d_em2 (by decide)
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem d_rC : DD (.req 1 Sroot T) := D.reqSink d_eC2 m_sink (by decide)
def SrootT : PFact := ⟨S, [], .star Excl.empty, .conc T⟩
theorem d_jCT : DD (.init 1 SrootT) := by
  have h : answerInit Sroot wS T = SrootT := by decide
  exact h ▸ D.answer d_rC d_aC rfl (by decide)
theorem d_eCT0 : DD (.edge 1 SrootT 0 ⟨⟨S, [], .any, .conc T⟩, true⟩) := D.start d_jCT
theorem d_eCT1 : DD (.edge 1 SrootT 1 ⟨⟨S, [C], .any, .conc T⟩, true⟩) := D.step d_eCT0 m_wr (by decide)
theorem d_eCT2 : DD (.edge 1 SrootT 2 ⟨⟨rB, [], .any, .conc T⟩, true⟩) :=
  D.ret (a := ⟨⟨S, [C], .any, .conc T⟩, true⟩) (r := ⟨⟨retB, [], .any, .conc T⟩, true⟩)
    (r' := ⟨⟨rB, [], .any, .conc T⟩, true⟩) (e2 := retE) d_eCT1 m_cm List.mem_cons_self
    (by decide) d_jm (by decide) d_em2 (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)
/-- `D` reports the vulnerability (in the demand layer). -/
theorem cex_D : DD (.vuln 1 2 sinkPat true) := D.vuln d_eCT2 m_sink (by decide)

#print axioms cex_D

/-! ### The design reports it, through a NORMAL-layer edge

`m`'s request climbs through the caller edge `Sroot → (S, <C>, [any], *)` (WIDE climb: the premise
is on `S`, the added fact lies above `<C>.f`). The caller's first place that satisfies it is its
added fact `(S, <C>.f, $, 7)`: the caller answers `(S, <C>.f, *, {}, *)`, which passes `C.s = null`
precisely; `m` gets it as an added fact at the requested position and answers too. The answer's
summary returns `r` in the normal layer; the sink asks for the mark 7, the root's fact answers it
exactly, and the vulnerability is reported in the normal layer. -/

theorem x_start : DS Xd (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem x_src : DS Xd (.edge 0 zeroFact 1 wF) := DS.step x_start m_src (by decide)
theorem x_aC : DS Xd (.added 1 wS) := DS.added (a := wF) x_src m_cC List.mem_cons_self (by decide)
theorem x_jC : DS Xd (.init 1 Sroot) := by
  have h : Xd.α 1 wS = Sroot := by decide
  exact h ▸ DS.initA x_aC
theorem x_eC0 : DS Xd (.edge 1 Sroot 0 SrootF) := DS.start x_jC
theorem x_eC1 : DS Xd (.edge 1 Sroot 1 a2F) := DS.step x_eC0 m_wr (by decide)
theorem x_am : DS Xd (.added 2 a2) := DS.added (a := a2F) x_eC1 m_cm List.mem_cons_self (by decide)
theorem x_jm : DS Xd (.init 2 Sroot) := by
  have h : Xd.α 2 a2 = Sroot := by decide
  exact h ▸ DS.initA x_am
theorem x_em0 : DS Xd (.edge 2 Sroot 0 SrootF) := DS.start x_jm
/-- RAISE in `m`. -/
theorem x_sreq : DS Xd (.sreq 2 Sroot [C, fA]) :=
  DS.sreqStmt (e := readE) x_em0 m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- CLIMB through the `[any]` caller edge from the static root. -/
theorem x_sreqC : DS Xd (.sreq 1 Sroot [C, fA]) :=
  DS.sreqUp (a := a2F) (e := bindS) x_sreq x_eC1 m_cm rfl List.mem_cons_self (by decide)
    (by decide)
/-- ANSWER in the caller from its added fact `(S, <C>.f, $, 7)`. -/
theorem x_jCA : DS Xd (.init 1 Ans) := DS.sanswer x_sreqC x_aC (by decide)
theorem x_eCA0 : DS Xd (.edge 1 Ans 0 ⟨Ans, false⟩) := DS.start x_jCA
/-- The answer passes `C.s = null` precisely. -/
theorem x_eCA1 : DS Xd (.edge 1 Ans 1 ⟨Ans, false⟩) := DS.step x_eCA0 m_wr (by decide)
theorem x_amA : DS Xd (.added 2 Ans) :=
  DS.added (a := ⟨Ans, false⟩) x_eCA1 m_cm List.mem_cons_self (by decide)
/-- ANSWER in `m` from the precise added fact. -/
theorem x_jmA : DS Xd (.init 2 Ans) := DS.sanswer x_sreq x_amA (by decide)
theorem x_emA0 : DS Xd (.edge 2 Ans 0 ⟨Ans, false⟩) := DS.start x_jmA
theorem x_emA1 : DS Xd (.edge 2 Ans 1 ⟨pat yB [], false⟩) := DS.step x_emA0 m_rd (by decide)
theorem x_emA2 : DS Xd (.edge 2 Ans 2 ⟨pat retB [], false⟩) := DS.step x_emA1 m_rt (by decide)
/-- The caller reads the answer's summary: `r` in the normal layer. -/
theorem x_eCA2 : DS Xd (.edge 1 Ans 2 ⟨pat rB [], false⟩) :=
  DS.ret (a := ⟨Ans, false⟩) (r := ⟨pat retB [], false⟩) (r' := ⟨pat rB [], false⟩) (e2 := retE)
    x_eCA1 m_cm List.mem_cons_self (by decide) x_jmA (by decide) x_emA2 (by decide)
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem x_rC : DS Xd (.req 1 Ans T) := DS.reqSink x_eCA2 m_sink (by decide)
/-- The root's fact answers the mark request exactly: `(S, <C>.f, $, 7)`. -/
theorem x_jCw : DS Xd (.init 1 wS) := by
  have h : Xd.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer x_rC x_aC rfl (by decide)
theorem x_eCw0 : DS Xd (.edge 1 wS 0 wF) := DS.start x_jCw
theorem x_eCw1 : DS Xd (.edge 1 wS 1 wF) := DS.step x_eCw0 m_wr (by decide)
theorem x_eCw2 : DS Xd (.edge 1 wS 2 ⟨⟨rB, [], .exact, .conc T⟩, false⟩) :=
  DS.ret (a := wF) (r := ⟨⟨retB, [], .exact, .conc T⟩, false⟩)
    (r' := ⟨⟨rB, [], .exact, .conc T⟩, false⟩) (e2 := retE) x_eCw1 m_cm List.mem_cons_self
    (by decide) x_jmA (by decide) x_emA2 (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)
/-- The first design with the wide climb reports the vulnerability in the normal layer. -/
theorem x_vuln_normal : DS Xd (.vuln 1 2 sinkPat false) := DS.vuln x_eCw2 m_sink (by decide)

#print axioms x_vuln_normal

/-! ### The rule as stated misses it

An invariant of `DS Xu`: the root starts from the zero fact only; `caller` has only the static
root as initial fact, and its facts after the write are `(S, [], */{<C>}, *)` and
`(S, <C>, [any], *)`; `m`'s static-root edges carry the static root only (the read fires), and
its initial facts are the static root and the answer; the only position request is
`(m, Sroot, <C>.f)`; there is no mark request and no vulnerability. -/

def InitOK : MethodId → PFact → Prop
  | 0, i => i = zeroFact
  | 1, i => i = Sroot
  | 2, i => i = Sroot ∨ i = Ans
  | _, _ => True

def EdgeOK : MethodId → PFact → Node → AFact → Prop
  | 0, i, 0, f => i = zeroFact ∧ f = zfF
  | 0, i, 1, f => i = zeroFact ∧ (f = zfF ∨ f = wF)
  | 0, i, _, _ => i = zeroFact
  | 1, i, 0, f => i = Sroot ∧ f = SrootF
  | 1, i, 1, f => i = Sroot ∧ (f = a1F ∨ f = a2F)
  | 1, i, _, f => i = Sroot ∧ f.fact.base = S
  | 2, i, _, f => (i = Sroot ∧ f = SrootF) ∨ i = Ans
  | _, _, _, _ => True

def AddedOK : MethodId → PFact → Prop
  | 0, _ => False
  | 1, a => a = wS
  | 2, a => a = a1 ∨ a = a2
  | _, _ => True

def UInv : SObj → Prop
  | .init M i => InitOK M i
  | .edge M i n f => EdgeOK M i n f
  | .added M a => AddedOK M a
  | .req _ _ _ => False
  | .sreq M i p => M = 2 ∧ i = Sroot ∧ p = [C, fA]
  | .vuln _ _ _ _ => False

/-- The sink of `caller` reads `r`; a fact on `S` does not reach it. -/
theorem sink_off {i : PFact} {f : AFact} (hb : f.fact.base = S) : check i f sinkPat = .none := by
  cases h : check i f sinkPat with
  | none => rfl
  | triggered =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    unfold overlapB at ho
    rw [hb] at ho
    cases ho
  | request t =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    unfold overlapB at ho
    rw [hb] at ho
    cases ho

theorem uInv_all {o : SObj} (h : DS Xu o) : UInv o := by
  induction h with
  | root hM =>
    rw [List.mem_singleton.mp hM]
    exact (rfl : zeroFact = zeroFact)
  | @start M i _ ih =>
    show EdgeOK M i 0 (startFact i)
    rcases M with _ | _ | _ | M
    · have hi : i = zeroFact := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · have hi : i = Sroot := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · rcases (ih : i = Sroot ∨ i = Ans) with rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr rfl
    · trivial
  | @step M i n f n' s f' _ he hf ih =>
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have key : ∀ x, x ∈ (transfer Xu.counted Xu.FL (sKeepP (Xu.fireB zeroFact zfF) src) zfF).facts →
          x = zfF ∨ x = wF := by decide
      exact ⟨rfl, key f' hf⟩
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ x, x ∈ (transfer Xu.counted Xu.FL (sKeepP (Xu.fireB Sroot SrootF) wr) SrootF).facts →
          x = a1F ∨ x = a2F := by decide
      exact ⟨rfl, key f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = Ans) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ x, x ∈ (transfer Xu.counted Xu.FL (sKeepP (Xu.fireB Sroot SrootF) rd) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · exact .inr rfl
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = Ans) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ x, x ∈ (transfer Xu.counted Xu.FL (sKeepP (Xu.fireB Sroot SrootF) rt) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · exact .inr rfl
  | @reqStmt M i n f n' s t _ he hq ih =>
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have hr : (transfer Xu.counted Xu.FL (sKeepP (Xu.fireB zeroFact zfF) src) zfF).reqs = [] := by
        decide
      rw [hr] at hq
      cases hq
    all_goals
      rw [transfer_reqs_star (sKeep_star (by decide))] at hq
      cases hq
  | @sreqStmt M i n f n' s e _ he hes hfire ih =>
    have hroot := fireB_root rfl hfire
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, -⟩ := (ih : i = zeroFact ∧ f = zfF)
      exact absurd hroot (by decide)
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ e, e ∈ wr.edges → Xu.fireB Sroot SrootF e = false := by decide
      rw [key e hes] at hfire
      cases hfire
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = Ans) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ e, e ∈ rd.edges → Xu.fireB Sroot SrootF e = true → e.1.path = [C, fA] := by
          decide
        exact ⟨rfl, rfl, key e hes hfire⟩
      · exact absurd hroot (by decide)
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = Ans) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ e, e ∈ rt.edges → Xu.fireB Sroot SrootF e = false := by decide
        rw [key e hes] at hfire
        cases hfire
      · exact absurd hroot (by decide)
  | @pass M i n f n' c _ he hm ih =>
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ih : i = zeroFact ∧ (f = zfF ∨ f = wF)).1
    · obtain ⟨rfl, hf⟩ := (ih : i = Sroot ∧ (f = a1F ∨ f = a2F))
      rcases hf with rfl | rfl <;> exact absurd hm (by decide)
  | @added M i n f n' c e a _ he he1 ha ih =>
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨-, hf⟩ := (ih : i = zeroFact ∧ (f = zfF ∨ f = wF))
      rw [List.mem_singleton.mp he1] at ha
      show a.fact = wS
      rcases hf with rfl | rfl
      · have key : ∀ x, x ∈ (applyEdge zfF bindS.1 bindS.2).facts → x.fact = wS := by decide
        exact key a ha
      · have key : ∀ x, x ∈ (applyEdge wF bindS.1 bindS.2).facts → x.fact = wS := by decide
        exact key a ha
    · obtain ⟨-, hf⟩ := (ih : i = Sroot ∧ (f = a1F ∨ f = a2F))
      rw [List.mem_singleton.mp he1] at ha
      show a.fact = a1 ∨ a.fact = a2
      rcases hf with rfl | rfl
      · have key : ∀ x, x ∈ (applyEdge a1F bindS.1 bindS.2).facts → x.fact = a1 ∨ x.fact = a2 := by
          decide
        exact key a ha
      · have key : ∀ x, x ∈ (applyEdge a2F bindS.1 bindS.2).facts → x.fact = a1 ∨ x.fact = a2 := by
          decide
        exact key a ha
  | @initA m a _ ih =>
    rcases m with _ | _ | _ | m
    · exact (ih : False).elim
    · have ha : a = wS := ih
      subst ha
      show Xu.α 1 wS = Sroot
      decide
    · rcases (ih : a = a1 ∨ a = a2) with rfl | rfl
      · exact .inl (by decide)
      · exact .inl (by decide)
    · trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ihf : i = zeroFact ∧ (f = zfF ∨ f = wF)).1
    · obtain ⟨rfl, hf⟩ := (ihf : i = Sroot ∧ (f = a1F ∨ f = a2F))
      refine ⟨rfl, ?_⟩
      rw [List.mem_singleton.mp he1] at ha
      rcases (ihj : j = Sroot ∨ j = Ans) with rfl | rfl
      · rcases (ihg : (Sroot = Sroot ∧ g = SrootF) ∨ Sroot = Ans) with ⟨-, rfl⟩ | hS
        · rcases hf with rfl | rfl
          · have key : ∀ a, a ∈ (applyEdge a1F bindS.1 bindS.2).facts →
                ∀ r, r ∈ (applySummary a Sroot SrootF).facts → ∀ e2, e2 ∈ cm.fromCallee →
                ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
                (limitF Xu.counted Xu.FL r').fact.base = S := by decide
            exact key a ha r hr e2 he2 r' hr'
          · have key : ∀ a, a ∈ (applyEdge a2F bindS.1 bindS.2).facts →
                ∀ r, r ∈ (applySummary a Sroot SrootF).facts → ∀ e2, e2 ∈ cm.fromCallee →
                ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
                (limitF Xu.counted Xu.FL r').fact.base = S := by decide
            exact key a ha r hr e2 he2 r' hr'
        · exact absurd hS (by decide)
      · rcases hf with rfl | rfl
        · have key : ∀ a, a ∈ (applyEdge a1F bindS.1 bindS.2).facts →
              applicable Ans a.fact = false := by decide
          rw [key a ha] at hap
          cases hap
        · have key : ∀ a, a ∈ (applyEdge a2F bindS.1 bindS.2).facts →
              applicable Ans a.fact = false := by decide
          rw [key a ha] at hap
          cases hap
  | sret _ _ _ _ _ hok => exact absurd hok Bool.false_ne_true
  | @reqSink M i n f s t _ hs hc ih =>
    have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_off (ih : i = Sroot ∧ f.fact.base = S).2] at hc
    cases hc
  | @answer M i t a _ _ _ _ ihr _ => exact ihr.elim
  | @sanswer M i p a _ _ _ ihs _ =>
    obtain ⟨rfl, -, rfl⟩ := (ihs : M = 2 ∧ i = Sroot ∧ p = [C, fA])
    exact .inr rfl
  | @reqUp m j t M ic n f n' c e a _ _ _ _ _ _ _ _ ihr _ => exact ihr.elim
  | @sreqUp m j p M ic n f n' c e a _ _ he hc he1 ha hcl ihs ihf =>
    obtain ⟨rfl, -, rfl⟩ := (ihs : m = 2 ∧ j = Sroot ∧ p = [C, fA])
    rcases edgesU he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact absurd hc (by decide)
    · obtain ⟨-, hf⟩ := (ihf : ic = Sroot ∧ (f = a1F ∨ f = a2F))
      rw [List.mem_singleton.mp he1] at ha
      rcases hf with rfl | rfl
      · have key : ∀ a, a ∈ (applyEdge a1F bindS.1 bindS.2).facts →
            climbB Xu.sB a.fact [C, fA] = false := by decide
        have hcl' : climbB Xu.sB a.fact [C, fA] = true := hcl
        rw [key a ha] at hcl'
        cases hcl'
      · have key : ∀ a, a ∈ (applyEdge a2F bindS.1 bindS.2).facts →
            climbB Xu.sB a.fact [C, fA] = false := by decide
        have hcl' : climbB Xu.sB a.fact [C, fA] = true := hcl
        rw [key a ha] at hcl'
        cases hcl'
  | @vuln M i n f s _ hs hc ih =>
    have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_off (ih : i = Sroot ∧ f.fact.base = S).2] at hc
    cases hc
  | @clean M i n f n' cl f' _ he _ _ =>
    rcases edgesU he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @reqClean M i n f n' cl t _ he _ _ =>
    rcases edgesU he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @filt M i n f n' b may _ he _ _ =>
    rcases edgesU he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- THE NARROW CLIMB WITHOUT A FALLBACK MISSES THE VULNERABILITY: `DS Xu` has no `vuln` object at
    all on this program. -/
theorem cex_user_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xu (.vuln M n s d) :=
  fun h => uInv_all h

#print axioms cex_user_misses

/-- THE RECORD (summary). The program is well formed, the flow from the source to the sink is real
    and the sink pattern covers its end location; `D` reports the vulnerability (demand layer); the
    design reports it in the NORMAL layer; the narrow climb without a fallback does not report it. -/
theorem counterexample :
    prog.WF ∧ Reach prog [0] 1 2 ⟨rB, [], T⟩ ∧ (1, 2, sinkPat) ∈ sinks ∧ sinkPat.mark = .conc T ∧
    sinkPat.covers ⟨rB, [], T⟩ ∧ Xu.α = policy (fun _ => []) ∧
    DD (.vuln 1 2 sinkPat true) ∧ DS Xd (.vuln 1 2 sinkPat false) ∧
    ∀ d, ¬ DS Xu (.vuln 1 2 sinkPat d) :=
  ⟨wf, cex_reach, m_sink, rfl, cex_covers, rfl, cex_D, x_vuln_normal, fun _ => cex_user_misses⟩

#print axioms counterexample

end CexAbove

/-! ## 11. A first-design variant: `CexAny` (excluded by the construction rules of the final rule)

`root: C.* = source(); m()`, `m: x = C.f; sink(x)`. The source rule taints every static field of
`C` (`AnyField` on `ClassStatic(C)`): `(S, <C>, [any], 7)`. Methods `0` (root) and `1` (`m`).

`m`'s only added fact `(S, <C>, [any], 7)` lies ABOVE the requested position `<C>.f`, and its caller
premise is the zero fact, not on the static base: the request cannot climb, and no added fact is
at or below `<C>.f`. If the answer waits for such a fact (`ansBelow = true`), `m` never analyses
`(S, <C>.f, *, {}, *)`; the read on its static root gives nothing, and the sink, which is INSIDE
`m`, is never reached. The overlap reading `sret` does not help: it reads a callee summary on the
caller's side. So the at-or-below answer loses the flow even with the full fallback
(`any_below_misses`), and so does the coordinator's rule (`any_coordinator_misses`). `D` reports it
(the demand layer), and so does the corrected rule (`any_corrected_finds`, by `vuln_foundS`): there
the request is answered by every added fact that OVERLAPS the position. -/

namespace CexAny

def S : Base := 1
def xB : Base := 2
def C : Acc := 10
def fA : Acc := 11
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- Every static field of `C` is tainted: `(S, <C>, [any], 7)`. -/
def anyC : PFact := ⟨S, [C], .any, .conc T⟩
def aF : AFact := ⟨anyC, false⟩
/-- root: `C.* = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, anyC)]⟩
/-- m: `x = C.f`. -/
def rd : Stmt := readStmt S xB [C, fA]
def readE : MicroEdge := (pat S [C, fA], pat xB [])
def cm : Call := ⟨1, [S], [bindS], [bindS]⟩
def prog : Program :=
  ⟨fun _ => 0, fun M => if M = 0 then 2 else 1,
   [(0, 0, .stmt src, 1), (0, 1, .call cm, 2), (1, 0, .stmt rd, 1)]⟩
def sinkPat : PFact := ⟨xB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(1, 1, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- The corrected design. -/
def X0 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, false, .full, false, false⟩
/-- The answer only from an added fact at or below the position, with the full fallback. -/
def Xb : SCtx := { X0 with ansBelow := true, fb := .full }
/-- The coordinator's rule: the at-or-below answer and the fallback only for non-static premises. -/
def Xc : SCtx := { X0 with ansBelow := true, fb := .nonStatic }

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cm : (0, 1, Instr.call cm, 2) ∈ prog.edges := by simp [prog]
theorem m_rd : (1, 0, Instr.stmt rd, 1) ∈ prog.edges := by simp [prog]
theorem m_sink : (1, 1, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesA {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cm ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt rd ∧ n' = 1) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesA hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;>
      decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesA hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;>
      decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesA hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;>
      decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesA hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- THE CONCRETE FLOW: `S.<C>.f` is tainted by the source, `m` reads it into `x` at the sink. -/
theorem any_reach : Reach prog [0] 1 1 ⟨xB, [], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, fA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, anyC), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [fA], rfl, rfl, rfl, trivial⟩)
  have hm : Flow prog 1 ⟨S, [C, fA], T⟩ 1 ⟨xB, [], T⟩ :=
    Flow.step (Flow.start 1 ⟨S, [C, fA], T⟩) m_rd
      (.inr ⟨readE, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  exact Reach.down (Reach.root List.mem_cons_self h0) m_cm List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, fA], [C, fA], rfl, rfl, rfl, rfl, rfl⟩ hm

theorem any_covers : sinkPat.covers ⟨xB, [], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms any_reach

def InitOK : MethodId → PFact → Prop
  | 0, i => i = zeroFact
  | 1, i => i = Sroot
  | _, _ => True

def EdgeOK : MethodId → PFact → Node → AFact → Prop
  | 0, i, 0, f => i = zeroFact ∧ f = zfF
  | 0, i, _, f => i = zeroFact ∧ (f = zfF ∨ f = aF)
  | 1, i, _, f => i = Sroot ∧ f = SrootF
  | _, _, _, _ => True

def AddedOK : MethodId → PFact → Prop
  | 0, _ => False
  | 1, a => a = anyC
  | _, _ => True

/-- The invariant of `DS Xb`: `m` has only the static root as initial fact, its read gives
    nothing, and nothing is answered. -/
def UInv : SObj → Prop
  | .init M i => InitOK M i
  | .edge M i n f => EdgeOK M i n f
  | .added M a => AddedOK M a
  | .req _ _ _ => False
  | .sreq M i p => M = 1 ∧ i = Sroot ∧ p = [C, fA]
  | .vuln _ _ _ _ => False

theorem sink_off {i : PFact} {f : AFact} (hb : f.fact.base = S) : check i f sinkPat = .none := by
  cases h : check i f sinkPat with
  | none => rfl
  | triggered =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    unfold overlapB at ho
    rw [hb] at ho
    cases ho
  | request t =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    unfold overlapB at ho
    rw [hb] at ho
    cases ho

theorem uInv_all {o : SObj} (h : DS Xb o) : UInv o := by
  induction h with
  | root hM =>
    rw [List.mem_singleton.mp hM]
    exact (rfl : zeroFact = zeroFact)
  | @start M i _ ih =>
    show EdgeOK M i 0 (startFact i)
    rcases M with _ | _ | M
    · have hi : i = zeroFact := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · have hi : i = Sroot := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · trivial
  | @step M i n f n' s f' _ he hf ih =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have key : ∀ x, x ∈ (transfer Xb.counted Xb.FL (sKeepP (Xb.fireB zeroFact zfF) src) zfF).facts →
          x = zfF ∨ x = aF := by decide
      exact ⟨rfl, key f' hf⟩
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ x, x ∈ (transfer Xb.counted Xb.FL (sKeepP (Xb.fireB Sroot SrootF) rd) SrootF).facts →
          x = SrootF := by decide
      exact ⟨rfl, key f' hf⟩
  | @reqStmt M i n f n' s t _ he hq ih =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have hr : (transfer Xb.counted Xb.FL (sKeepP (Xb.fireB zeroFact zfF) src) zfF).reqs = [] := by
        decide
      rw [hr] at hq
      cases hq
    · rw [transfer_reqs_star (sKeep_star (by decide))] at hq
      cases hq
  | @sreqStmt M i n f n' s e _ he hes hfire ih =>
    have hroot := fireB_root rfl hfire
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, -⟩ := (ih : i = zeroFact ∧ f = zfF)
      exact absurd hroot (by decide)
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ e, e ∈ rd.edges → Xb.fireB Sroot SrootF e = true → e.1.path = [C, fA] := by
        decide
      exact ⟨rfl, rfl, key e hes hfire⟩
  | @pass M i n f n' c _ he hm ih =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    exact (ih : i = zeroFact ∧ (f = zfF ∨ f = aF))
  | @added M i n f n' c e a _ he he1 ha ih =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    obtain ⟨-, hf⟩ := (ih : i = zeroFact ∧ (f = zfF ∨ f = aF))
    rw [List.mem_singleton.mp he1] at ha
    show a.fact = anyC
    rcases hf with rfl | rfl
    · have key : ∀ x, x ∈ (applyEdge zfF bindS.1 bindS.2).facts → x.fact = anyC := by decide
      exact key a ha
    · have key : ∀ x, x ∈ (applyEdge aF bindS.1 bindS.2).facts → x.fact = anyC := by decide
      exact key a ha
  | @initA m a _ ih =>
    rcases m with _ | _ | m
    · exact (ih : False).elim
    · have ha : a = anyC := ih
      subst ha
      show Xb.α 1 anyC = Sroot
      decide
    · trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    obtain ⟨rfl, hf⟩ := (ihf : i = zeroFact ∧ (f = zfF ∨ f = aF))
    have hj : j = Sroot := ihj
    subst hj
    obtain ⟨-, rfl⟩ := (ihg : Sroot = Sroot ∧ g = SrootF)
    rw [List.mem_singleton.mp he1] at ha
    refine ⟨rfl, ?_⟩
    rcases hf with rfl | rfl
    · have key : ∀ a, a ∈ (applyEdge zfF bindS.1 bindS.2).facts →
          ∀ r, r ∈ (applySummary a Sroot SrootF).facts → ∀ e2, e2 ∈ cm.fromCallee →
          ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
          limitF Xb.counted Xb.FL r' = zfF ∨ limitF Xb.counted Xb.FL r' = aF := by decide
      exact key a ha r hr e2 he2 r' hr'
    · have key : ∀ a, a ∈ (applyEdge aF bindS.1 bindS.2).facts →
          ∀ r, r ∈ (applySummary a Sroot SrootF).facts → ∀ e2, e2 ∈ cm.fromCallee →
          ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
          limitF Xb.counted Xb.FL r' = zfF ∨ limitF Xb.counted Xb.FL r' = aF := by decide
      exact key a ha r hr e2 he2 r' hr'
  | @sret M i n f n' c e1 a j g r e2 r' _ he _ _ _ hok _ _ _ _ _ ihj _ =>
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    have hj : j = Sroot := ihj
    subst hj
    exact absurd rfl (fbOK_path hok)
  | @reqSink M i n f s t _ hs hc ih =>
    have hs' : (M, n, s) = (1, 1, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    obtain ⟨-, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
    rw [sink_off rfl] at hc
    cases hc
  | @answer M i t a _ _ _ _ ihr _ => exact ihr.elim
  | @sanswer M i p a _ _ hok ihs iha =>
    obtain ⟨rfl, -, rfl⟩ := (ihs : M = 1 ∧ i = Sroot ∧ p = [C, fA])
    have ha : a = anyC := iha
    subst ha
    exact absurd hok (by decide)
  | @reqUp m j t M ic n f n' c e a _ _ _ _ _ _ _ _ ihr _ => exact ihr.elim
  | @sreqUp m j p M ic n f n' c e a _ _ he hc he1 ha hcl ihs ihf =>
    obtain ⟨rfl, -, rfl⟩ := (ihs : m = 1 ∧ j = Sroot ∧ p = [C, fA])
    rcases edgesA he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    obtain ⟨rfl, -⟩ := (ihf : ic = zeroFact ∧ (f = zfF ∨ f = aF))
    have hno : Xb.climbOK zeroFact a.fact [C, fA] = false := rfl
    rw [hno] at hcl
    cases hcl
  | @vuln M i n f s _ hs hc ih =>
    have hs' : (M, n, s) = (1, 1, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    obtain ⟨-, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
    rw [sink_off rfl] at hc
    cases hc
  | @clean M i n f n' cl f' _ he _ _ =>
    rcases edgesA he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @reqClean M i n f n' cl t _ he _ _ =>
    rcases edgesA he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @filt M i n f n' b may _ he _ _ =>
    rcases edgesA he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- The at-or-below answer loses the flow, even with the full fallback: no `vuln` object. -/
theorem any_below_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xb (.vuln M n s d) :=
  fun h => uInv_all h

/-- The coordinator's rule loses it too (it has fewer objects, `DS_mono`). -/
theorem any_coordinator_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xc (.vuln M n s d) :=
  fun h => any_below_misses (DS_mono (X := X0) (ab := true) (ab' := true) (fb := .nonStatic)
    (fb' := .full) (.inr rfl) (.inl rfl) h)

/-- `D` reports it (the base vulnerability theorem). -/
theorem any_D_finds : ∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 1 sinkPat b) :=
  Coverage.vuln_found_policy prog counted 2 sinks [0] wf (fun _ => []) any_reach m_sink rfl
    any_covers

/-- The corrected rule reports it (`vuln_foundS`). -/
theorem any_corrected_finds : ∃ b, DS X0 (.vuln 1 1 sinkPat b) :=
  vuln_foundS (X := X0) rfl rfl rfl rfl wf (fun m a => policy_applicable _ m a) any_reach m_sink rfl
    any_covers

/-- THE COUNTEREXAMPLE to the at-or-below answer (summary). -/
theorem counterexample :
    prog.WF ∧ Reach prog [0] 1 1 ⟨xB, [], T⟩ ∧ (1, 1, sinkPat) ∈ sinks ∧ sinkPat.covers ⟨xB, [], T⟩ ∧
    (∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 1 sinkPat b)) ∧
    (∃ b, DS X0 (.vuln 1 1 sinkPat b)) ∧
    (∀ d, ¬ DS Xb (.vuln 1 1 sinkPat d)) ∧ (∀ d, ¬ DS Xc (.vuln 1 1 sinkPat d)) :=
  ⟨wf, any_reach, m_sink, any_covers, any_D_finds, any_corrected_finds,
    fun _ => any_below_misses, fun _ => any_coordinator_misses⟩

#print axioms counterexample

end CexAny

/-! ## 12. The fallback must cover static premises too: `CexWide`

`root: C.g = source(); caller()`,
`caller: t = C.g; C.s = t; K(); r = m(); sink(r)`, `K: C.u = null`, `m: y = C.s; return y`.
Methods `0` (root), `1` (`caller`), `2` (`K`), `3` (`m`).

The real flow moves `S.<C>.g` into `t` and `t` into `S.<C>.s`; `K` does not touch `S.<C>.s`; `m`
reads it. In `caller`, the read on the static root raises `<C>.g`, answered by the root's fact:
`(S, <C>.g, *, {}, *)`. From it the write gives the precise `(S, <C>.s, *)`. But `K`'s only summary
is the one of its static root, and its keep edge `S.<C>.* →_{u} S.<C>.*` (case `above`) makes it
uncorrelated: the caller's precise fact comes back as `(S, <C>, [any], *)`, DEMAND, with the premise
`(S, <C>.g, *)` on the static base. At the call of `m` this fact lies above `<C>.s`. The wide climb
asks `caller` for `<C>.s` at the premise `(S, <C>.g, *)`, but that premise's entry location is
`S.<C>.g`, not `S.<C>.s`: the climbed request is answered by nothing that carries the flow (no
caller added fact overlaps `<C>.s`). If the overlap reading is kept only for caller premises off
the static base (`fb = nonStatic`), nothing reads `m`'s answer and the flow is lost
(`wide_nonstatic_misses`), also under the coordinator's rule (`wide_coordinator_misses`). `D`
reports it in the demand layer, and so does the corrected rule (`wide_corrected_finds`): its
fallback reads `m`'s answer from above. The climb is only provably right when the caller edge
relates the same static location (the static root to the static root, `climb_covers`). -/

namespace CexWide

def S : Base := 1
def tB : Base := 2
def rB : Base := 3
def yB : Base := 4
def retB : Base := 5
def C : Acc := 10
def gA : Acc := 11
def sA : Acc := 12
def uA : Acc := 13
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- The tainted static field `(S, <C>.g, $, 7)`. -/
def wg : PFact := ⟨S, [C, gA], .exact, .conc T⟩
def wgF : AFact := ⟨wg, false⟩
/-- The answers `(S, <C>.g, *, {}, *)` and `(S, <C>.s, *, {}, *)`. -/
def Ag : PFact := sAns S [C, gA]
def AgF : AFact := ⟨Ag, false⟩
def As : PFact := sAns S [C, sA]
def AsF : AFact := ⟨As, false⟩
def tF : AFact := ⟨pat tB [], false⟩
def a1F : AFact := ⟨⟨S, [], .star (.set [C]), .star⟩, false⟩
def a1F2 : AFact := ⟨⟨S, [], .star (.set [C, C]), .star⟩, false⟩
/-- The degraded static fact `(S, <C>, [any], *)`. -/
def a2F : AFact := ⟨⟨S, [C], .any, .star⟩, true⟩
/-- root: `C.g = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, wg)]⟩
/-- caller: `t = C.g`. -/
def rdg : Stmt := readStmt S tB [C, gA]
def readG : MicroEdge := (pat S [C, gA], pat tB [])
/-- caller: `C.s = t`. -/
def wrs : Stmt :=
  ⟨[S, tB], [(⟨S, [], .star (.set [C]), .star⟩, pat S []),
    (⟨S, [C], .star (.set [sA]), .star⟩, pat S [C]), (pat tB [], pat tB []), (pat tB [], pat S [C, sA])]⟩
/-- K: `C.u = null`. -/
def wru : Stmt :=
  ⟨[S], [(⟨S, [], .star (.set [C]), .star⟩, pat S []), (⟨S, [C], .star (.set [uA]), .star⟩, pat S [C])]⟩
/-- m: `y = C.s`. -/
def rds : Stmt := readStmt S yB [C, sA]
def readS : MicroEdge := (pat S [C, sA], pat yB [])
/-- m: `return y`. -/
def rt : Stmt := ⟨[retB, yB], [(pat yB [], pat yB []), (pat yB [], pat retB [])]⟩
def retE : MicroEdge := (pat retB [], pat rB [])
def cC : Call := ⟨1, [S], [bindS], [bindS]⟩
def cK : Call := ⟨2, [S], [bindS], [bindS]⟩
def cm : Call := ⟨3, [S, rB], [bindS], [bindS, retE]⟩
def exitOf : MethodId → Node
  | 0 => 2
  | 1 => 4
  | 2 => 1
  | _ => 2
def prog : Program :=
  ⟨fun _ => 0, exitOf,
   [(0, 0, .stmt src, 1), (0, 1, .call cC, 2),
    (1, 0, .stmt rdg, 1), (1, 1, .stmt wrs, 2), (1, 2, .call cK, 3), (1, 3, .call cm, 4),
    (2, 0, .stmt wru, 1),
    (3, 0, .stmt rds, 1), (3, 1, .stmt rt, 2)]⟩
def sinkPat : PFact := ⟨rB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(1, 4, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- The corrected design. -/
def X0 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, false, .full, false, false⟩
/-- The wide climb, the overlap answer, and the fallback only for non-static caller premises. -/
def Xn : SCtx := { X0 with ansBelow := false, fb := .nonStatic }
/-- The coordinator's rule. -/
def Xc : SCtx := { X0 with ansBelow := true, fb := .nonStatic }

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cC : (0, 1, Instr.call cC, 2) ∈ prog.edges := by simp [prog]
theorem m_rdg : (1, 0, Instr.stmt rdg, 1) ∈ prog.edges := by simp [prog]
theorem m_wrs : (1, 1, Instr.stmt wrs, 2) ∈ prog.edges := by simp [prog]
theorem m_cK : (1, 2, Instr.call cK, 3) ∈ prog.edges := by simp [prog]
theorem m_cm : (1, 3, Instr.call cm, 4) ∈ prog.edges := by simp [prog]
theorem m_wru : (2, 0, Instr.stmt wru, 1) ∈ prog.edges := by simp [prog]
theorem m_rds : (3, 0, Instr.stmt rds, 1) ∈ prog.edges := by simp [prog]
theorem m_rt : (3, 1, Instr.stmt rt, 2) ∈ prog.edges := by simp [prog]
theorem m_sink : (1, 4, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesW {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cC ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt rdg ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .stmt wrs ∧ n' = 2) ∨
    (M = 1 ∧ n = 2 ∧ ins = .call cK ∧ n' = 3) ∨ (M = 1 ∧ n = 3 ∧ ins = .call cm ∧ n' = 4) ∨
    (M = 2 ∧ n = 0 ∧ ins = .stmt wru ∧ n' = 1) ∨
    (M = 3 ∧ n = 0 ∧ ins = .stmt rds ∧ n' = 1) ∨ (M = 3 ∧ n = 1 ∧ ins = .stmt rt ∧ n' = 2) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

#print axioms wf

/-- THE CONCRETE FLOW: `S.<C>.g` → `t` → `S.<C>.s` → (through `K`) → `m` reads it → `r` at the sink. -/
theorem wide_reach : Reach prog [0] 1 4 ⟨rB, [], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, gA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, wg), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have c1 : Flow prog 1 ⟨S, [C, gA], T⟩ 1 ⟨tB, [], T⟩ :=
    Flow.step (Flow.start 1 ⟨S, [C, gA], T⟩) m_rdg
      (.inr ⟨readG, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have c2 : Flow prog 1 ⟨S, [C, gA], T⟩ 2 ⟨S, [C, sA], T⟩ :=
    Flow.step c1 m_wrs
      (.inr ⟨(pat tB [], pat S [C, sA]), by simp [wrs],
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have k1 : Flow prog 2 ⟨S, [C, sA], T⟩ 1 ⟨S, [C, sA], T⟩ :=
    Flow.step (Flow.start 2 ⟨S, [C, sA], T⟩) m_wru
      (.inr ⟨(⟨S, [C], .star (.set [uA]), .star⟩, pat S [C]),
        List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [sA], [sA], rfl, rfl, rfl, rfl, rfl⟩)
  have c3 : Flow prog 1 ⟨S, [C, gA], T⟩ 3 ⟨S, [C, sA], T⟩ :=
    Flow.call c2 m_cK List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩ k1
      List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩
  have mm1 : Flow prog 3 ⟨S, [C, sA], T⟩ 1 ⟨yB, [], T⟩ :=
    Flow.step (Flow.start 3 ⟨S, [C, sA], T⟩) m_rds
      (.inr ⟨readS, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have mm2 : Flow prog 3 ⟨S, [C, sA], T⟩ 2 ⟨retB, [], T⟩ :=
    Flow.step mm1 m_rt
      (.inr ⟨(pat yB [], pat retB []), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have c4 : Flow prog 1 ⟨S, [C, gA], T⟩ 4 ⟨rB, [], T⟩ :=
    Flow.call c3 m_cm List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩ mm2
      (List.mem_cons_of_mem _ List.mem_cons_self)
      ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
  exact Reach.down (Reach.root List.mem_cons_self h0) m_cC List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, gA], [C, gA], rfl, rfl, rfl, rfl, rfl⟩ c4

theorem wide_covers : sinkPat.covers ⟨rB, [], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms wide_reach

/-! ### The fallback only for non-static premises misses it -/

theorem α1_S {m : MethodId} {a : PFact} (hb : a.base = S) : α1 m a = Sroot := by
  unfold α1 policy
  split
  · rename_i hz
    rw [hz] at hb
    exact absurd hb (by decide)
  · split
    · rename_i h
      cases h
    · obtain ⟨b, p, k, mk⟩ := a
      have hb' : b = S := hb
      subst hb'
      rfl

theorem fbOK_S {i a j : PFact} (hi : i.base = S) : Xn.fbOK i a j = false := by
  unfold SCtx.fbOK
  show (!Nat.beq i.base S && sAboveB S i a j) = false
  rw [hi, Nat.beq_refl]
  rfl

theorem sink_off {i : PFact} {f : AFact} (hb : f.fact.base ≠ rB) : check i f sinkPat = .none := by
  cases h : check i f sinkPat with
  | none => rfl
  | triggered =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    exact absurd (Example.overlap_base ho) hb
  | request t =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    exact absurd (Example.overlap_base ho) hb

def InitOK : MethodId → PFact → Prop
  | 0, i => i = zeroFact
  | 1, i => i = Sroot ∨ i = Ag
  | 2, i => i = Sroot
  | 3, i => i = Sroot ∨ i = As
  | _, _ => True

/-- The edges of `caller`, by node: from the static root and from the answer `(S, <C>.g, *)`. -/
def CallerOK : PFact → Node → AFact → Prop
  | i, 0, f => (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ f = AgF)
  | i, 1, f => (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ (f = AgF ∨ f = tF))
  | i, 2, f => (i = Sroot ∧ (f = a1F ∨ f = a2F)) ∨ (i = Ag ∧ (f = AgF ∨ f = tF ∨ f = AsF))
  | i, 3, f => (i = Sroot ∧ (f = a1F2 ∨ f = a2F)) ∨ (i = Ag ∧ (f = a2F ∨ f = tF))
  | i, _, f => (i = Sroot ∨ i = Ag) ∧ f.fact.base ≠ rB

def EdgeOK : MethodId → PFact → Node → AFact → Prop
  | 0, i, 0, f => i = zeroFact ∧ f = zfF
  | 0, i, 1, f => i = zeroFact ∧ (f = zfF ∨ f = wgF)
  | 0, i, _, _ => i = zeroFact
  | 1, i, n, f => CallerOK i n f
  | 2, i, 0, f => i = Sroot ∧ f = SrootF
  | 2, i, _, f => i = Sroot ∧ (f = a1F ∨ f = a2F)
  | 3, i, _, f => (i = Sroot ∧ f = SrootF) ∨ i = As
  | _, _, _, _ => True

def AddedOK : MethodId → PFact → Prop
  | 0, _ => False
  | 1, a => a = wg
  | 2, a => a.base = S
  | 3, a => a.base = S
  | _, _ => True

/-- The invariant of `DS Xn`: no fact on `r` in `caller`, no mark request, no vulnerability. -/
def UInv : SObj → Prop
  | .init M i => InitOK M i
  | .edge M i n f => EdgeOK M i n f
  | .added M a => AddedOK M a
  | .req _ _ _ => False
  | .sreq M i p =>
      (M = 1 ∧ (i = Sroot ∨ i = Ag) ∧ (p = [C, gA] ∨ p = [C, sA])) ∨ (M = 3 ∧ i = Sroot ∧ p = [C, sA])
  | .vuln _ _ _ _ => False

theorem uInv_all {o : SObj} (h : DS Xn o) : UInv o := by
  induction h with
  | root hM =>
    rw [List.mem_singleton.mp hM]
    exact (rfl : zeroFact = zeroFact)
  | @start M i _ ih =>
    show EdgeOK M i 0 (startFact i)
    rcases M with _ | _ | _ | _ | M
    · have hi : i = zeroFact := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · rcases (ih : i = Sroot ∨ i = Ag) with rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨rfl, rfl⟩
    · have hi : i = Sroot := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · rcases (ih : i = Sroot ∨ i = As) with rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr rfl
    · trivial
  | @step M i n f n' s f' _ he hf ih =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB zeroFact zfF) src) zfF).facts →
          x = zfF ∨ x = wgF := by decide
      exact ⟨rfl, key f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ f = AgF)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Sroot SrootF) rdg) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Ag AgF) rdg) AgF).facts →
            x = AgF ∨ x = tF := by decide
        exact .inr ⟨rfl, key f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ (f = AgF ∨ f = tF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, hf0⟩
      · have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Sroot SrootF) wrs) SrootF).facts →
            x = a1F ∨ x = a2F := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · have key : ∀ g, g ∈ [AgF, tF] →
            ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Ag g) wrs) g).facts →
            x = AgF ∨ x = tF ∨ x = AsF := by decide
        exact .inr ⟨rfl, key f (by rcases hf0 with rfl | rfl <;> decide) f' hf⟩
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Sroot SrootF) wru) SrootF).facts →
          x = a1F ∨ x = a2F := by decide
      exact ⟨rfl, key f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = As) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Sroot SrootF) rds) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · exact .inr rfl
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = As) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ x, x ∈ (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB Sroot SrootF) rt) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · exact .inr rfl
  | @reqStmt M i n f n' s t _ he hq ih =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have hr : (transfer Xn.counted Xn.FL (sKeepP (Xn.fireB zeroFact zfF) src) zfF).reqs = [] := by
        decide
      rw [hr] at hq
      cases hq
    all_goals
      rw [transfer_reqs_star (sKeep_star (by decide))] at hq
      cases hq
  | @sreqStmt M i n f n' s e _ he hes hfire ih =>
    have hroot := fireB_root rfl hfire
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, -⟩ := (ih : i = zeroFact ∧ f = zfF)
      exact absurd hroot (by decide)
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ f = AgF)) with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · have key : ∀ e, e ∈ rdg.edges → Xn.fireB Sroot SrootF e = true →
            e.1.path = [C, gA] := by decide
        exact .inl ⟨rfl, .inl rfl, .inl (key e hes hfire)⟩
      · exact absurd hroot (by decide)
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = Ag ∧ (f = AgF ∨ f = tF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · have key : ∀ e, e ∈ wrs.edges → Xn.fireB Sroot SrootF e = false := by decide
        rw [key e hes] at hfire
        cases hfire
      · exact absurd hroot (by decide)
    · obtain ⟨rfl, rfl⟩ := (ih : i = Sroot ∧ f = SrootF)
      have key : ∀ e, e ∈ wru.edges → Xn.fireB Sroot SrootF e = false := by decide
      rw [key e hes] at hfire
      cases hfire
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = As) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ e, e ∈ rds.edges → Xn.fireB Sroot SrootF e = true →
            e.1.path = [C, sA] := by decide
        exact .inr ⟨rfl, rfl, key e hes hfire⟩
      · exact absurd hroot (by decide)
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ i = As) with ⟨rfl, rfl⟩ | rfl
      · have key : ∀ e, e ∈ rt.edges → Xn.fireB Sroot SrootF e = false := by decide
        rw [key e hes] at hfire
        cases hfire
      · exact absurd hroot (by decide)
  | @pass M i n f n' c _ he hm ih =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ih : i = zeroFact ∧ (f = zfF ∨ f = wgF)).1
    · rcases (ih : (i = Sroot ∧ (f = a1F ∨ f = a2F)) ∨ (i = Ag ∧ (f = AgF ∨ f = tF ∨ f = AsF))) with
        ⟨rfl, hf | hf⟩ | ⟨rfl, hf | hf | hf⟩ <;> subst hf
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact .inr ⟨rfl, .inr rfl⟩
      · exact absurd hm (by decide)
    · rcases (ih : (i = Sroot ∧ (f = a1F2 ∨ f = a2F)) ∨ (i = Ag ∧ (f = a2F ∨ f = tF))) with
        ⟨rfl, hf | hf⟩ | ⟨rfl, hf | hf⟩ <;> subst hf
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact absurd hm (by decide)
      · exact ⟨.inr rfl, by decide⟩
  | @added M i n f n' c e a _ he he1 ha ih =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨-, hf⟩ := (ih : i = zeroFact ∧ (f = zfF ∨ f = wgF))
      rw [List.mem_singleton.mp he1] at ha
      show a.fact = wg
      have key : ∀ g, g ∈ [zfF, wgF] → ∀ x, x ∈ (applyEdge g bindS.1 bindS.2).facts → x.fact = wg := by
        decide
      exact key f (by rcases hf with rfl | rfl <;> decide) a ha
    · rw [List.mem_singleton.mp he1] at ha
      exact applyEdge_base ha
    · rw [List.mem_singleton.mp he1] at ha
      exact applyEdge_base ha
  | @initA m a _ ih =>
    rcases m with _ | _ | _ | _ | m
    · exact (ih : False).elim
    · have ha : a = wg := ih
      subst ha
      exact .inl (α1_S (m := 1) (a := wg) rfl)
    · exact α1_S (m := 2) ih
    · exact .inl (α1_S (m := 3) ih)
    · trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ihf : i = zeroFact ∧ (f = zfF ∨ f = wgF)).1
    · -- the call of `K`
      rw [List.mem_singleton.mp he1] at ha
      have hj : j = Sroot := ihj
      subst hj
      obtain ⟨-, hg⟩ := (ihg : Sroot = Sroot ∧ (g = a1F ∨ g = a2F))
      have hgm : g ∈ [a1F, a2F] := by rcases hg with rfl | rfl <;> decide
      rcases (ihf : (i = Sroot ∧ (f = a1F ∨ f = a2F)) ∨ (i = Ag ∧ (f = AgF ∨ f = tF ∨ f = AsF))) with
        ⟨rfl, hf⟩ | ⟨rfl, hf⟩
      · have key : ∀ f, f ∈ [a1F, a2F] → ∀ g, g ∈ [a1F, a2F] →
            ∀ a, a ∈ (applyEdge f bindS.1 bindS.2).facts →
            ∀ r, r ∈ (applySummary a Sroot g).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
            limitF Xn.counted Xn.FL r' = a1F2 ∨ limitF Xn.counted Xn.FL r' = a2F := by decide
        exact .inl ⟨rfl, key f (by rcases hf with rfl | rfl <;> decide) g hgm a ha r hr e2 he2 r' hr'⟩
      · have key : ∀ f, f ∈ [AgF, tF, AsF] → ∀ g, g ∈ [a1F, a2F] →
            ∀ a, a ∈ (applyEdge f bindS.1 bindS.2).facts →
            ∀ r, r ∈ (applySummary a Sroot g).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
            limitF Xn.counted Xn.FL r' = a2F ∨ limitF Xn.counted Xn.FL r' = tF := by decide
        exact .inr ⟨rfl, key f (by rcases hf with rfl | rfl | rfl <;> decide) g hgm a ha r hr e2 he2
          r' hr'⟩
    · -- the call of `m`
      rw [List.mem_singleton.mp he1] at ha
      have hf3 : (i = Sroot ∨ i = Ag) ∧ f ∈ [a1F2, a2F, tF] := by
        rcases (ihf : (i = Sroot ∧ (f = a1F2 ∨ f = a2F)) ∨ (i = Ag ∧ (f = a2F ∨ f = tF))) with
          ⟨rfl, hf | hf⟩ | ⟨rfl, hf | hf⟩ <;> subst hf <;> exact ⟨by simp, by decide⟩
      refine ⟨hf3.1, ?_⟩
      rcases (ihj : j = Sroot ∨ j = As) with rfl | rfl
      · rcases (ihg : (Sroot = Sroot ∧ g = SrootF) ∨ Sroot = As) with ⟨-, rfl⟩ | hS
        · have key : ∀ f, f ∈ [a1F2, a2F, tF] → ∀ a, a ∈ (applyEdge f bindS.1 bindS.2).facts →
              ∀ r, r ∈ (applySummary a Sroot SrootF).facts → ∀ e2, e2 ∈ cm.fromCallee →
              ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
              (limitF Xn.counted Xn.FL r').fact.base ≠ rB := by decide
          exact key f hf3.2 a ha r hr e2 he2 r' hr'
        · exact absurd hS (by decide)
      · have key : ∀ f, f ∈ [a1F2, a2F, tF] → ∀ a, a ∈ (applyEdge f bindS.1 bindS.2).facts →
            applicable As a.fact = false := by decide
        rw [key f hf3.2 a ha] at hap
        cases hap
  | @sret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hok _ _ _ _ ihf ihj _ =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · -- the root's edge: the caller's initial facts are the static root and `(S, <C>.g, *)`
      obtain ⟨rfl, hf⟩ := (ihf : i = zeroFact ∧ (f = zfF ∨ f = wgF))
      rw [List.mem_singleton.mp he1] at ha
      rcases (ihj : j = Sroot ∨ j = Ag) with rfl | rfl
      · exact absurd rfl (fbOK_path hok)
      · have key : ∀ g, g ∈ [zfF, wgF] → ∀ a, a ∈ (applyEdge g bindS.1 bindS.2).facts →
            Xn.fbOK zeroFact a.fact Ag = false := by decide
        rw [key f (by rcases hf with rfl | rfl <;> decide) a ha] at hok
        cases hok
    · -- the caller's premises are on the static base
      rcases (ihf : (i = Sroot ∧ (f = a1F ∨ f = a2F)) ∨ (i = Ag ∧ (f = AgF ∨ f = tF ∨ f = AsF))) with
        ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [fbOK_S rfl] at hok <;> cases hok
    · rcases (ihf : (i = Sroot ∧ (f = a1F2 ∨ f = a2F)) ∨ (i = Ag ∧ (f = a2F ∨ f = tF))) with
        ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [fbOK_S rfl] at hok <;> cases hok
  | @reqSink M i n f s t _ hs hc ih =>
    have hs' : (M, n, s) = (1, 4, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_off (ih : (i = Sroot ∨ i = Ag) ∧ f.fact.base ≠ rB).2] at hc
    cases hc
  | @answer M i t a _ _ _ _ ihr _ => exact ihr.elim
  | @sanswer M i p a _ _ hok ihs iha =>
    rcases (ihs : (M = 1 ∧ (i = Sroot ∨ i = Ag) ∧ (p = [C, gA] ∨ p = [C, sA])) ∨
        (M = 3 ∧ i = Sroot ∧ p = [C, sA])) with ⟨rfl, -, rfl | rfl⟩ | ⟨rfl, -, rfl⟩
    · exact .inr rfl
    · have ha : a = wg := iha
      subst ha
      exact absurd hok (by decide)
    · exact .inr rfl
  | @reqUp m j t M ic n f n' c e a _ _ _ _ _ _ _ _ ihr _ => exact ihr.elim
  | @sreqUp m j p M ic n f n' c e a _ _ he hc he1 ha hcl ihs ihf =>
    rcases edgesW he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · -- through the root's edge: its premise is the zero fact, not on the static base
      obtain ⟨rfl, -⟩ := (ihf : ic = zeroFact ∧ (f = zfF ∨ f = wgF))
      have hno : Xn.climbOK zeroFact a.fact p = false := rfl
      rw [hno] at hcl
      cases hcl
    · -- `K` raises no position request
      rcases (ihs : (m = 1 ∧ (j = Sroot ∨ j = Ag) ∧ (p = [C, gA] ∨ p = [C, sA])) ∨
          (m = 3 ∧ j = Sroot ∧ p = [C, sA])) with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact absurd hc (by decide)
    · -- through the call of `m`: the request climbs to a caller premise
      rcases (ihs : (m = 1 ∧ (j = Sroot ∨ j = Ag) ∧ (p = [C, gA] ∨ p = [C, sA])) ∨
          (m = 3 ∧ j = Sroot ∧ p = [C, sA])) with ⟨rfl, -⟩ | ⟨-, -, rfl⟩
      · exact absurd hc (by decide)
      · rcases (ihf : (ic = Sroot ∧ (f = a1F2 ∨ f = a2F)) ∨ (ic = Ag ∧ (f = a2F ∨ f = tF))) with
          ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact .inl ⟨rfl, .inl rfl, .inr rfl⟩
        · exact .inl ⟨rfl, .inr rfl, .inr rfl⟩
  | @vuln M i n f s _ hs hc ih =>
    have hs' : (M, n, s) = (1, 4, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_off (ih : (i = Sroot ∨ i = Ag) ∧ f.fact.base ≠ rB).2] at hc
    cases hc
  | @clean M i n f n' cl f' _ he _ _ =>
    rcases edgesW he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @reqClean M i n f n' cl t _ he _ _ =>
    rcases edgesW he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  | @filt M i n f n' b may _ he _ _ =>
    rcases edgesW he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- The fallback only for non-static premises loses the flow: no `vuln` object. -/
theorem wide_nonstatic_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xn (.vuln M n s d) :=
  fun h => uInv_all h

/-- The coordinator's rule loses it too (it has fewer objects, `DS_mono`). -/
theorem wide_coordinator_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xc (.vuln M n s d) :=
  fun h => wide_nonstatic_misses (DS_mono (X := X0) (ab := true) (ab' := false) (fb := .nonStatic)
    (fb' := .nonStatic) (.inl rfl) (.inr rfl) h)

/-- `D` reports it (the base vulnerability theorem). -/
theorem wide_D_finds : ∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 4 sinkPat b) :=
  Coverage.vuln_found_policy prog counted 2 sinks [0] wf (fun _ => []) wide_reach m_sink rfl
    wide_covers

/-- The corrected rule reports it (`vuln_foundS`). -/
theorem wide_corrected_finds : ∃ b, DS X0 (.vuln 1 4 sinkPat b) :=
  vuln_foundS (X := X0) rfl rfl rfl rfl wf (fun m a => policy_applicable _ m a) wide_reach m_sink rfl
    wide_covers

/-- THE COUNTEREXAMPLE to the fallback restricted to non-static premises (summary). -/
theorem counterexample :
    prog.WF ∧ Reach prog [0] 1 4 ⟨rB, [], T⟩ ∧ (1, 4, sinkPat) ∈ sinks ∧ sinkPat.covers ⟨rB, [], T⟩ ∧
    (∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 4 sinkPat b)) ∧
    (∃ b, DS X0 (.vuln 1 4 sinkPat b)) ∧
    (∀ d, ¬ DS Xn (.vuln 1 4 sinkPat d)) ∧ (∀ d, ¬ DS Xc (.vuln 1 4 sinkPat d)) :=
  ⟨wf, wide_reach, m_sink, wide_covers, wide_D_finds, wide_corrected_finds,
    fun _ => wide_nonstatic_misses, fun _ => wide_coordinator_misses⟩

#print axioms counterexample

end CexWide

/-! ## 13. The final rule: construction hypotheses and the static invariant

The final rule (`gen = true`, `deepAns = true`, `wide = true`, `ansBelow = true`, `fb = off`): the
fire on identity static `*` edges at the root or a class (`|q| ≤ 1`), for statement micro edges
strictly below (reads, keep edges of writes, field-to-field copies), with the request truncated to the
static field; sinks raise the ordinary mark request; answers only from added facts AT OR BELOW the
requested position; the wide climb; no fallback; a MARK request on a static premise is answered at the
answering added fact's own position.

A static POSITION is the premise path of a statement micro edge on `S` or the path of a sink pattern
on `S`, truncated to the static field (`PosIn`). A path is ABOVE a position if it is a strict prefix
of one (`AbovePos`): the root or a class. The construction hypotheses (`SWF`) say how the program
touches `S`. Under them, every static fact that is not exact and lies above a position is an
identity static `*` fact (`cinv_all`): the root or a class answer, carrying its own location. So
`(S, <C>, [any], ...)` is impossible by construction when a field of `C` is a position. Below a
static field the ordinary rules apply and no invariant is claimed. -/

/-- `P` is a static position of the program: a static premise or sink path truncated to the static
    field (`[<C>, f]`, `[<C>]` or the root). -/
def PosIn (X : SCtx) (P : List Acc) : Prop :=
  (∃ M n s n' e, (M, n, Instr.stmt s, n') ∈ X.P.edges ∧ e ∈ s.edges ∧ e.1.base = X.sB ∧
    e.1.path.take 2 = P) ∨
  (∃ M n s, (M, n, s) ∈ X.sinks ∧ s.base = X.sB ∧ s.path.take 2 = P)

/-- `q` lies strictly above a static position. -/
def AbovePos (X : SCtx) (q : List Acc) : Prop := ∃ P r, PosIn X P ∧ r ≠ [] ∧ P = q ++ r

theorem abovePos_prefix {X : SCtx} {q r : List Acc} (h : AbovePos X (q ++ r)) : AbovePos X q := by
  obtain ⟨P, r', hP, hr', rfl⟩ := h
  refine ⟨_, r ++ r', hP, ?_, by rw [List.append_assoc]⟩
  intro h
  exact hr' (List.append_eq_nil_iff.mp h).2

/-- A position is at most a static field: `[<C>, f]` or `[<C>]` (or the root). -/
theorem posIn_len {X : SCtx} {P : List Acc} (h : PosIn X P) : P.length ≤ 2 := by
  rcases h with ⟨_, _, _, _, e, _, _, _, rfl⟩ | ⟨_, _, s, _, _, rfl⟩
  · exact List.length_take_le 2 _
  · exact List.length_take_le 2 _

/-- A path above a position is the root or a class position. -/
theorem abovePos_len {X : SCtx} {q : List Acc} (h : AbovePos X q) : q.length ≤ 1 := by
  obtain ⟨P, r, hP, hne, rfl⟩ := h
  have h2 := posIn_len hP
  have h1 := List.length_pos_iff.mpr hne
  rw [List.length_append] at h2
  omega

/-- A static fact, not exact, above a position. -/
def AboveNE (X : SCtx) (f : PFact) : Prop := f.base = X.sB ∧ AbovePos X f.path ∧ f.kind ≠ .exact

/-- THE CONSTRUCTION HYPOTHESES of the final rule. -/
structure SWF (X : SCtx) : Prop where
  /-- the static base is not the zero base -/
  base : X.sB ≠ zeroBase
  /-- a statement micro edge from `S` to `S` is an IDENTITY RESTRICTION `S.q.* →_E S.q.*` (the read
      keeps `S.* → S.*`, a write keeps `S.* →_{<C>} S.*` and `S.<C>.* →_{s} S.<C>.*`) or a
      FIELD-TO-FIELD edge: its premise path and its target path are not above a position (a pass
      rule `CopyAllMarks(C.f → D.g)` gives `S.<C>.f.* → S.<D>.g.*`, `CopyMark` gives
      `S.<C>.f.$(T) → S.<D>.g.$(T)`), with any tail and mark. A pass rule from or to a bare class
      position is a rule error. The proofs use only the target half (`f2f_not_above`). -/
  ss : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ X.P.edges → ∀ e, e ∈ s.edges →
    e.1.base = X.sB → e.2.base = X.sB →
    (∃ q E1 E2, e.1 = ⟨X.sB, q, .star E1, .star⟩ ∧ e.2 = ⟨X.sB, q, .star E2, .star⟩) ∨
    (¬ AbovePos X e.1.path ∧ ¬ AbovePos X e.2.path)
  /-- a statement micro edge from another base into `S` writes at or below a position; above a
      position (the root or a bare class) only an exact fact from an exact concrete-mark premise (a
      rule on a synthetic class position, `(S, <C>, $, T)`). No `[any]` source on a bare class. -/
  write : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ X.P.edges → ∀ e, e ∈ s.edges →
    e.1.base ≠ X.sB → e.2.base = X.sB → AbovePos X e.2.path →
    e.2.kind = .exact ∧ e.1.kind = .exact ∧ ∃ t, e.1.mark = .conc t
  /-- a call binds `S` only by `S.* → S.*` (both ways) -/
  toC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.toCallee →
    (e.1.base = X.sB ∨ e.2.base = X.sB) →
    ∃ E1 E2, e.1 = ⟨X.sB, [], .star E1, .star⟩ ∧ e.2 = ⟨X.sB, [], .star E2, .star⟩
  fromC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.fromCallee →
    (e.1.base = X.sB ∨ e.2.base = X.sB) →
    ∃ E1 E2, e.1 = ⟨X.sB, [], .star E1, .star⟩ ∧ e.2 = ⟨X.sB, [], .star E2, .star⟩
  /-- the field limit never cuts a path to a path above a position, i.e. to the root or a class (the
      limit is at least 1 and the class accessor is not counted) -/
  cut : ∀ q r, cutPath X.counted X.FL q = some r → ¬ AbovePos X r
  /-- a cleaner on `S` removes one mark -/
  clean : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ X.P.edges → cl.base = X.sB →
    ∃ t, cl.mark = some t
  /-- run 1 serves an added fact by its root (`policy1`) -/
  alpha : X.α = policy (fun _ => [])

/-! ### 13.1 Local shape lemmas -/

/-- W2 on a final fact: a `*` tail has an abstract mark and is in the normal layer. -/
def W2A (f : AFact) : Prop := ∀ E, f.fact.kind = .star E → Exact.absB f.fact.mark = true ∧ f.demand = false

theorem norm_path (x : AFact) : x.norm.fact.path = x.fact.path := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  unfold AFact.norm
  cases k with
  | star e => cases m <;> cases d <;> cases e <;> rfl
  | any => rfl
  | exact => rfl

theorem norm_w2 (x : AFact) : W2A x.norm := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  intro E hE
  unfold AFact.norm at hE ⊢
  cases k with
  | star e => cases m <;> cases d <;> cases e <;> first | exact ⟨rfl, rfl⟩ | cases hE
  | any => cases hE
  | exact => cases hE

theorem norm_exact {x : AFact} (h : x.fact.kind = .exact) : x.norm.fact.kind = .exact := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  subst h
  rfl

theorem norm_keep {x : AFact} {E : Excl} (hk : x.fact.kind = .star E) (hm : Exact.absB x.fact.mark = true)
    (hd : x.demand = false) : x.norm = x := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  simp only at hk hm hd
  subst hk hd
  cases m with
  | conc t => cases hm
  | star => unfold AFact.norm; cases E <;> rfl
  | starEx y => unfold AFact.norm; cases E <;> rfl

theorem applyEdge_w2 {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) : W2A r := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := CoreAux.mem_applyEdge_facts_inv h
  exact norm_w2 _

theorem limitF_w2 {counted : Acc → Bool} {L : Nat} {f : AFact} (h : W2A f) :
    W2A (limitF counted L f) := by
  unfold limitF
  cases cutPath counted L f.fact.path with
  | none => exact h
  | some _ => intro E hE; cases hE

theorem applyEdge_base_eq {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    c.fact.base = fr.base := by
  unfold applyEdge at h
  split at h
  next hb => exact CoreAux.beq_iff.mp hb
  next => cases h

theorem markComp_star {m m' : MarkA} (h : markComp .star m = some m') : m' = m := by
  simp only [markComp, Option.some.injEq] at h
  exact h.symm

/-- The case `below` with a `*` target: the path is the target path and the rest; an exact fact
    stays exact; a `*` fact stays `*` without a demand step. -/
theorem below_star_tk {ck fk : Kind} {r tp : List Acc} {et : Excl} {p : List Acc} {k : Kind}
    {ap : Bool} (h : belowCase ck fk r tp (.star et) = some (p, k, ap)) :
    p = tp ++ r ∧ (ck = .exact → k = .exact) ∧ (∀ ec, ck = .star ec → (∃ e', k = .star e') ∧ ap = false) := by
  unfold belowCase at h
  split at h
  next =>
    cases r with
    | cons x rs =>
      dsimp only at h
      split at h
      next =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, id, fun ec hc => ⟨⟨ec, hc⟩, rfl⟩⟩
      next => cases h
    | nil =>
      dsimp only at h
      cases ck with
      | exact =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨by rw [List.append_nil], fun _ => rfl, fun ec hc => Kind.noConfusion hc⟩
      | star ec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨by rw [List.append_nil], fun hc => Kind.noConfusion hc, fun _ _ => ⟨⟨_, rfl⟩, rfl⟩⟩
      | any =>
        refine ⟨?_, fun hc => Kind.noConfusion hc, fun ec hc => Kind.noConfusion hc⟩
        split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> rw [← h.1, List.append_nil]
  next => cases h

/-- The case `above`: the result is at the target path, the fact's tail admits the rest, and a target
    that is not exact gives `[any]`. -/
theorem above_tk {ck fk : Kind} {r tp : List Acc} {tk : Kind} {p : List Acc} {k : Kind} {ap : Bool}
    (h : aboveCase ck fk r tp tk = some (p, k, ap)) :
    p = tp ∧ admitsTailB ck r = true ∧ (tk ≠ .exact → k = .any) ∧ (tk = .exact → k = .exact) := by
  unfold aboveCase at h
  split at h
  next hadm =>
    cases tk with
    | star et =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, hadm, fun _ => rfl, fun hc => Kind.noConfusion hc⟩
    | any =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, hadm, fun _ => rfl, fun hc => Kind.noConfusion hc⟩
    | exact =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, hadm, fun hc => absurd rfl hc, fun _ => rfl⟩
  next => cases h

/-- The shape of a result of delta-concat, by the relative position of the fact and the premise. -/
theorem apply_shape {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts) :
    ∃ p k ap m, c.fact.base = fr.base ∧ markGate fr.mark c.fact.mark = .ok ∧
      markComp to.mark c.fact.mark = some m ∧ r = AFact.norm ⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ ∧
      ((∃ rr, c.fact.path = fr.path ++ rr ∧ belowCase c.fact.kind fr.kind rr to.path to.kind = some (p, k, ap)) ∨
       (∃ rr, fr.path = c.fact.path ++ rr ∧ rr ≠ [] ∧
          aboveCase c.fact.kind fr.kind rr to.path to.kind = some (p, k, ap))) := by
  have hfb := applyEdge_base_eq hr
  obtain ⟨p, k, ap, m, hg, hgate, hmc, hrr⟩ := CoreAux.mem_applyEdge_facts_inv hr
  refine ⟨p, k, ap, m, hfb, hgate, hmc, hrr, ?_⟩
  unfold CoreAux.geo at hg
  cases hrel : relate fr.path c.fact.path with
  | below rr =>
    rw [hrel] at hg
    exact .inl ⟨rr, CoreAux.relate_below_inv hrel, hg⟩
  | above rr =>
    rw [hrel] at hg
    obtain ⟨hqp, hne⟩ := CoreAux.relate_above_inv hrel
    exact .inr ⟨rr, hqp, hne, hg⟩
  | apart =>
    rw [hrel] at hg
    cases hg

/-- A static identity restriction `S.q.* →_E S.q.*` applied to a fact: below its premise the path is
    kept, an exact fact stays exact and an abstract normal `*` fact stays one with its mark; above its
    premise the result is at `q` and the fact's tail admits the rest. -/
theorem id_apply {sB : Base} {q : List Acc} {E1 E2 : Excl} {f r : AFact}
    (hr : r ∈ (applyEdge f ⟨sB, q, .star E1, .star⟩ ⟨sB, q, .star E2, .star⟩).facts) :
    r.fact.base = sB ∧ f.fact.base = sB ∧
    ((∃ rr, f.fact.path = q ++ rr ∧ r.fact.path = f.fact.path ∧
        (f.fact.kind = .exact → r.fact.kind = .exact) ∧
        (∀ E, f.fact.kind = .star E → Exact.absB f.fact.mark = true → f.demand = false →
          (∃ E', r.fact.kind = .star E') ∧ r.fact.mark = f.fact.mark ∧ r.demand = false)) ∨
     (∃ rr, q = f.fact.path ++ rr ∧ rr ≠ [] ∧ r.fact.path = q ∧ admitsTailB f.fact.kind rr = true)) := by
  obtain ⟨p, k, ap, m, hfb, -, hmc, hrr, hgeo⟩ := apply_shape hr
  have hm : m = f.fact.mark := markComp_star hmc
  subst hm
  have hpath : r.fact.path = p := by rw [hrr, norm_path]
  refine ⟨by rw [hrr, norm_base], hfb, ?_⟩
  rcases hgeo with ⟨rr, hfp, hb⟩ | ⟨rr, hqp, hne, ha⟩
  · obtain ⟨hp, hex, hst⟩ := below_star_tk hb
    refine .inl ⟨rr, hfp, by rw [hpath, hp, hfp], fun hk => ?_, fun E hk ha hd => ?_⟩
    · rw [hrr]; exact norm_exact (hex hk)
    · obtain ⟨⟨e', hk'⟩, hap⟩ := hst E hk
      have hx := norm_keep (x := ⟨⟨sB, p, k, f.fact.mark⟩, f.demand || ap⟩) (E := e') hk' ha
        (by rw [hd, hap]; rfl)
      rw [hrr, hx]
      exact ⟨⟨e', hk'⟩, rfl, by rw [hd, hap]; rfl⟩
  · obtain ⟨hp, hadm, -, -⟩ := above_tk ha
    exact .inr ⟨rr, hqp, hne, by rw [hpath, hp], hadm⟩


/-- The case `below` with an `[any]` target. -/
theorem below_any_tk {ck fk : Kind} {r tp : List Acc} {p : List Acc} {k : Kind} {ap : Bool}
    (h : belowCase ck fk r tp .any = some (p, k, ap)) : p = tp ∧ k = .any := by
  unfold belowCase at h
  split at h
  next =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm⟩
  next => cases h

/-- The case `below` with a `$` target: the result is exact, or `*/Universe` from a `*` fact at an
    exact premise. -/
theorem below_exact_tk {ck fk : Kind} {r tp : List Acc} {p : List Acc} {k : Kind} {ap : Bool}
    (h : belowCase ck fk r tp .exact = some (p, k, ap)) :
    p = tp ∧ (k = .exact ∨ ((∃ ec, ck = .star ec) ∧ fk = .exact ∧ r = [])) := by
  unfold belowCase at h
  split at h
  next =>
    dsimp only at h
    cases ck with
    | star ec =>
      cases fk with
      | exact =>
        cases r with
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨h.1.symm, .inr ⟨⟨ec, rfl⟩, rfl, rfl⟩⟩
        | cons x rs =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨h.1.symm, .inl h.2.1.symm⟩
      | star e =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, .inl h.2.1.symm⟩
      | any =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, .inl h.2.1.symm⟩
    | any =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, .inl h.2.1.symm⟩
    | exact =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, .inl h.2.1.symm⟩
  next => cases h

/-- The binding `S.* → S.*` keeps the path, an exact fact exact, and an abstract normal `*` fact. -/
theorem bind_apply {sB : Base} {E1 E2 : Excl} {f r : AFact}
    (hr : r ∈ (applyEdge f ⟨sB, [], .star E1, .star⟩ ⟨sB, [], .star E2, .star⟩).facts) :
    r.fact.base = sB ∧ f.fact.base = sB ∧ r.fact.path = f.fact.path ∧
      (f.fact.kind = .exact → r.fact.kind = .exact) ∧
      (∀ E, f.fact.kind = .star E → Exact.absB f.fact.mark = true → f.demand = false →
        (∃ E', r.fact.kind = .star E') ∧ r.fact.mark = f.fact.mark ∧ r.demand = false) := by
  obtain ⟨hb, hfb, ⟨rr, -, hp, hex, hst⟩ | ⟨rr, hq, hne, -, -⟩⟩ := id_apply hr
  · exact ⟨hb, hfb, hp, hex, hst⟩
  · exfalso
    have h0 := congrArg List.length hq
    rw [List.length_append, List.length_nil] at h0
    cases rr with
    | nil => exact hne rfl
    | cons x rs => simp at h0

theorem cleanPos_base_eq {cl : Cleaner} {c : PFact} (h : cleanPos cl c ≠ .disjoint) :
    c.base = cl.base := by
  cases hb : Nat.beq c.base cl.base with
  | true => exact CoreAux.beq_iff.mp hb
  | false =>
    exfalso
    apply h
    unfold cleanPos
    rw [hb]
    rfl

/-- The results of the cleaner on a fact: the fact itself; the fact without one mark; the
    concrete part; the `[any]` normal form, only for a cleaner of every mark. -/
theorem cleanRes_cases {cl : Cleaner} {c r : AFact} (hr : r ∈ (cleanRes cl c).facts) :
    r = c ∨
    (c.fact.base = cl.base ∧ ∃ t, Exact.absB c.fact.mark = true ∧ cl.mark = some t ∧
      r = ⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩) ∨
    (∃ t, c.fact.mark = .conc t ∧ r = concPart cl c) ∨
    (c.fact.base = cl.base ∧ cl.mark = none ∧ r = AFact.norm ⟨c.fact, true⟩) := by
  unfold cleanRes at hr
  cases hpos : cleanPos cl c.fact with
  | disjoint =>
    rw [hpos] at hr
    cases hr with
    | head => exact .inl rfl
    | tail _ h => cases h
  | inside =>
    have hb := cleanPos_base_eq (c := c.fact) (cl := cl) (by rw [hpos]; intro h; cases h)
    rw [hpos] at hr
    obtain ⟨⟨cb, cp, ck, cm⟩, cd⟩ := c
    obtain ⟨clb, clp, clr, clm⟩ := cl
    cases cm with
    | conc t =>
      dsimp only at hr
      split at hr
      next => cases hr
      next =>
        cases hr with
        | head => exact .inl rfl
        | tail _ h => cases h
    | star =>
      cases clm with
      | none => cases hr
      | some t =>
        cases hr with
        | head => exact .inr (.inl ⟨hb, t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
    | starEx x =>
      cases clm with
      | none => cases hr
      | some t =>
        cases hr with
        | head => exact .inr (.inl ⟨hb, t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
  | part =>
    have hb := cleanPos_base_eq (c := c.fact) (cl := cl) (by rw [hpos]; intro h; cases h)
    rw [hpos] at hr
    obtain ⟨⟨cb, cp, ck, cm⟩, cd⟩ := c
    obtain ⟨clb, clp, clr, clm⟩ := cl
    cases cm with
    | conc t =>
      dsimp only at hr
      split at hr
      next =>
        cases hr with
        | head => exact .inr (.inr (.inl ⟨t, rfl, rfl⟩))
        | tail _ h => cases h
      next =>
        cases hr with
        | head => exact .inl rfl
        | tail _ h => cases h
    | star =>
      cases clm with
      | none =>
        cases hr with
        | head => exact .inr (.inr (.inr ⟨hb, rfl, rfl⟩))
        | tail _ h => cases h
      | some t =>
        cases hr with
        | head => exact .inr (.inl ⟨hb, t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
    | starEx x =>
      cases clm with
      | none =>
        cases hr with
        | head => exact .inr (.inr (.inr ⟨hb, rfl, rfl⟩))
        | tail _ h => cases h
      | some t =>
        cases hr with
        | head => exact .inr (.inl ⟨hb, t, rfl, rfl, rfl⟩)
        | tail _ h => cases h

theorem startFact_w2 (i : PFact) : W2A (startFact i) := by
  obtain ⟨b, p, k, m⟩ := i
  intro E hE
  cases k <;> cases m <;> first | exact ⟨rfl, rfl⟩ | cases hE

theorem cleanRes_w2 {cl : Cleaner} {c r : AFact} (hc : W2A c) (hr : r ∈ (cleanRes cl c).facts) :
    W2A r := by
  rcases cleanRes_cases hr with rfl | ⟨-, t, ha, -, rfl⟩ | ⟨t, hct, rfl⟩ | ⟨-, -, rfl⟩
  · exact hc
  · intro E hE
    exact ⟨Exact.addEx_abs t ha, (hc E hE).2⟩
  · intro E hE
    rcases Exact.concPart_cases cl c with ⟨-, -, -, hcp⟩ | hcp
    · rw [hcp] at hE; cases hE
    · rw [hcp] at hE
      have := (hc E hE).1
      rw [hct] at this
      cases this
  · exact norm_w2 _

/-- The identity edge recogniser holds for an identity static `*` edge. -/
theorem idEdge_true {sB : Base} {q : List Acc} {E0 E : Excl} {m : MarkA}
    (hm : Exact.absB m = true) :
    idEdgeB sB ⟨sB, q, .star E0, .star⟩ ⟨⟨sB, q, .star E, m⟩, false⟩ = true := by
  unfold idEdgeB
  simp only [Nat.beq_refl, Kind.isStar, decide_true, hm, Bool.not_false, Bool.and_self]

theorem strictBelow_app {k : Kind} {q rr : List Acc} (hne : rr ≠ []) (h : admitsTailB k rr = true) :
    strictBelowB k q (q ++ rr) = true := by
  unfold strictBelowB
  rw [Exact.dropPrefix_append]
  cases rr with
  | nil => exact absurd rfl hne
  | cons x rs => exact h

theorem limitF_keep {X : SCtx} (hs : SWF X) {y : AFact}
    (h : AbovePos X (limitF X.counted X.FL y).fact.path) : limitF X.counted X.FL y = y := by
  unfold limitF at h ⊢
  cases hc : cutPath X.counted X.FL y.fact.path with
  | none => rfl
  | some r =>
    rw [hc] at h
    exact absurd h (hs.cut _ _ hc)

theorem aboveNE_kind {X : SCtx} {f : PFact} (h : AboveNE X f) : f.kind ≠ .exact := h.2.2

theorem admits_exact_nil {r : List Acc} (hne : r ≠ []) : admitsTailB .exact r = false := by
  cases r with
  | nil => exact absurd rfl hne
  | cons x rs => rfl

theorem idEdge_of {sB : Base} {i : PFact} {f : AFact} {E0 E : Excl}
    (hi : i = ⟨sB, f.fact.path, .star E0, .star⟩) (hb : f.fact.base = sB) (hk : f.fact.kind = .star E)
    (ha : Exact.absB f.fact.mark = true) (hd : f.demand = false) : idEdgeB sB i f = true := by
  subst hi
  obtain ⟨⟨fb, fp, fk, fm⟩, fd⟩ := f
  simp only at hb hk hd ha ⊢
  subst hb hk hd
  exact idEdge_true ha

theorem gate_conc_abs {t : Mark} {m : MarkA} (hg : markGate (.conc t) m = .ok) :
    Exact.absB m = false := by
  cases ha : Exact.absB m with
  | false => rfl
  | true => exact absurd (Exact.gate_abs hg ha) Bool.false_ne_true

theorem applicable_path {j a : PFact} (h : applicable j a = true) : ∃ r0, a.path = j.path ++ r0 := by
  unfold applicable coversB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, hd⟩, -⟩ := h
  cases hdp : dropPrefix j.path a.path with
  | none => rw [hdp] at hd; cases hd
  | some r0 => exact ⟨r0, CoreAux.dropPrefix_some.mp hdp⟩

/-! ### 13.2 The static invariant -/

/-- W2 on an added fact. -/
def W2P (a : PFact) : Prop := ∀ E, a.kind = .star E → Exact.absB a.mark = true

/-- THE STATIC INVARIANT. An initial fact that is exact has a concrete mark, and one above a
    position that is not exact is `(S, q, */E, *)`. An edge whose fact is static, not exact and above
    a position is an identity static `*` edge (abstract mark, normal layer), its premise at the same
    path. W2 on every edge and added fact. -/
def CInv (X : SCtx) : SObj → Prop
  | .init _ i => (i.kind = .exact → ∃ t, i.mark = .conc t) ∧
      (AboveNE X i → (∃ E, i.kind = .star E) ∧ i.mark = .star)
  | .edge _ i _ f => W2A f ∧
      (AboveNE X f.fact → (∃ E0, i = ⟨X.sB, f.fact.path, .star E0, .star⟩) ∧
        (∃ E, f.fact.kind = .star E) ∧ Exact.absB f.fact.mark = true ∧ f.demand = false)
  | .added _ a => W2P a ∧ (AboveNE X a → (∃ E, a.kind = .star E) ∧ Exact.absB a.mark = true)
  | _ => True

/-- A write into `S` from another base gives no non-exact fact above a position. -/
theorem write_inv {X : SCtx} (hs : SWF X) {M : MethodId} {n n' : Node} {s : Stmt} {e : MicroEdge}
    {f y : AFact} (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges) (he : e ∈ s.edges)
    (h1 : e.1.base ≠ X.sB) (h2 : e.2.base = X.sB) (hw : W2A f)
    (hy : y ∈ (applyEdge f e.1 e.2).facts) : ¬ AboveNE X y.fact := by
  intro hab
  obtain ⟨p, k, ap, m, -, hgate, -, hrr, hgeo⟩ := apply_shape hy
  have hyp : y.fact.path = p := by rw [hrr, norm_path]
  have hyk : k = .exact → y.fact.kind = .exact := fun hk => by rw [hrr]; exact norm_exact hk
  have hapos : AbovePos X p := by rw [← hyp]; exact hab.2.1
  have hwr := hs.write _ _ _ _ hE e he h1 h2
  rcases hgeo with ⟨rr, -, hb⟩ | ⟨rr, -, -, ha⟩
  · cases htk : e.2.kind with
    | star et =>
      rw [htk] at hb
      obtain ⟨hp, -, -⟩ := below_star_tk hb
      rw [hp] at hapos
      have := (hwr (abovePos_prefix hapos)).1
      rw [htk] at this; cases this
    | any =>
      rw [htk] at hb
      obtain ⟨hp, -⟩ := below_any_tk hb
      rw [hp] at hapos
      have := (hwr hapos).1
      rw [htk] at this; cases this
    | exact =>
      rw [htk] at hb
      obtain ⟨hp, hk | ⟨⟨ec, hck⟩, -, -⟩⟩ := below_exact_tk hb
      · exact hab.2.2 (hyk hk)
      · rw [hp] at hapos
        obtain ⟨-, -, t, hmt⟩ := hwr hapos
        rw [hmt] at hgate
        have := (hw ec hck).1
        rw [gate_conc_abs hgate] at this
        cases this
  · obtain ⟨hp, -, -, hex⟩ := above_tk ha
    rw [hp] at hapos
    exact hab.2.2 (hyk (hex (hwr hapos).1))

/-- A result of delta-concat lies at or below the target path of the micro edge. -/
theorem apply_path_prefix {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts) :
    ∃ rr, r.fact.path = to.path ++ rr := by
  obtain ⟨p, k, ap, m, -, -, -, hrr, hgeo⟩ := apply_shape hr
  have hrp : r.fact.path = p := by rw [hrr, norm_path]
  rw [hrp]
  rcases hgeo with ⟨rr, -, hb⟩ | ⟨rr, -, -, ha⟩
  · cases htk : to.kind with
    | star et =>
      rw [htk] at hb
      exact ⟨rr, (below_star_tk hb).1⟩
    | any =>
      rw [htk] at hb
      exact ⟨[], by rw [(below_any_tk hb).1, List.append_nil]⟩
    | exact =>
      rw [htk] at hb
      exact ⟨[], by rw [(below_exact_tk hb).1, List.append_nil]⟩
  · exact ⟨[], by rw [(above_tk ha).1, List.append_nil]⟩

/-- A FIELD-TO-FIELD micro edge (its target path is not above a position) gives no fact above a
    position, whatever the fact, the tails and the marks. -/
theorem f2f_not_above {X : SCtx} {c r : AFact} {fr to : PFact} (hn : ¬ AbovePos X to.path)
    (hr : r ∈ (applyEdge c fr to).facts) : ¬ AbovePos X r.fact.path := by
  intro h
  obtain ⟨rr, hp⟩ := apply_path_prefix hr
  rw [hp] at h
  exact hn (abovePos_prefix h)

#print axioms f2f_not_above

/-- THE STEP keeps the invariant: an identity restriction keeps an identity static `*` edge; in the
    case `above` the fact is at the root or a class, so the final rule fires (no fact); a
    field-to-field edge lands at or below its target, which is not above a position; a read leaves
    `S`; a write lands at or below a position; the field limit never cuts above a position. -/
theorem step_inv {X : SCtx} (hs : SWF X) (hgen : X.gen = true) {M : MethodId} {i : PFact}
    {n n' : Node} {s : Stmt} {f f' : AFact} (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges)
    (ih : CInv X (.edge M i n f))
    (hf : f' ∈ (transfer X.counted X.FL (sKeepP (X.fireB i f) s) f).facts) :
    CInv X (.edge M i n' f') := by
  obtain ⟨hw, hid⟩ := (ih : W2A f ∧ _)
  rcases ds_step_from_kept hf with ⟨-, rfl⟩ | ⟨e, he, hfe, y, hy, hfy⟩
  · exact ⟨hw, hid⟩
  · subst hfy
    refine ⟨limitF_w2 (applyEdge_w2 hy), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL y).fact.path := hab.2.1
    rw [limitF_keep hs hab0] at hab ⊢
    have hyb : y.fact.base = e.2.base := by
      obtain ⟨_, _, _, _, _, _, _, hrr, _⟩ := apply_shape hy
      rw [hrr, norm_base]
    by_cases h1 : e.1.base = X.sB
    · by_cases h2 : e.2.base = X.sB
      · rcases hs.ss _ _ _ _ hE e he h1 h2 with ⟨q, E1, E2, he1, he2⟩ | ⟨-, hn2⟩
        rotate_left
        · exact absurd hab.2.1 (f2f_not_above hn2 hy)
        rw [he1, he2] at hy
        obtain ⟨-, hfb, ⟨rr, -, hyp, hex, hst⟩ | ⟨rr, hq, hne, hyq, hadm⟩⟩ := id_apply hy
        · have hfne : f.fact.kind ≠ .exact := fun hk => hab.2.2 (hex hk)
          have hfab : AboveNE X f.fact := ⟨hfb, by rw [← hyp]; exact hab.2.1, hfne⟩
          obtain ⟨⟨E0, hi⟩, ⟨E, hk⟩, ha, hd⟩ := hid hfab
          obtain ⟨hyk, hym, hyd⟩ := hst E hk ha hd
          exact ⟨⟨E0, by rw [hyp]; exact hi⟩, hyk, by rw [hym]; exact ha, hyd⟩
        · exfalso
          have hfne : f.fact.kind ≠ .exact := fun hk => by
            rw [hk, admits_exact_nil hne] at hadm; cases hadm
          have hqa : AbovePos X q := by rw [← hyq]; exact hab.2.1
          rw [hq] at hqa
          have hfab : AboveNE X f.fact := ⟨hfb, abovePos_prefix hqa, hfne⟩
          obtain ⟨⟨E0, hi⟩, ⟨E, hk⟩, ha, hd⟩ := hid hfab
          have hlen : i.path.length ≤ 1 := by rw [hi]; exact abovePos_len hfab.2.1
          have hfire : X.fireB i f e = true := by
            unfold SCtx.fireB
            rw [hgen, if_pos rfl]
            unfold genFireB
            rw [idEdge_of hi hfb hk ha hd, decide_eq_true hlen, h1, Nat.beq_refl, he1]
            simp only [Bool.true_and]
            rw [hq]
            exact strictBelow_app hne hadm
          rw [hfire] at hfe
          cases hfe
      · exact absurd (hyb.symm.trans hab.1) h2
    · by_cases h2 : e.2.base = X.sB
      · exact absurd hab (write_inv hs hE he h1 h2 hw hy)
      · exact absurd (hyb.symm.trans hab.1) h2

/-- THE RETURN keeps the invariant: a result above a position comes from a callee identity summary
    `(S, q, *) → (S, q, */E)` applied to an identity caller fact at the same path. -/
theorem ret_inv {X : SCtx} (hs : SWF X) {M : MethodId} {i : PFact} {n n' : Node} {f : AFact}
    {c : Call} {e1 e2 : MicroEdge} {a g r r' : AFact} {j : PFact}
    (hE : (M, n, Instr.call c, n') ∈ X.P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hap : applicable j a.fact = true)
    (hr : r ∈ (applySummary a j g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts)
    (ihf : CInv X (.edge M i n f)) (ihj : CInv X (.init c.callee j))
    (ihg : CInv X (.edge c.callee j (X.P.exit c.callee) g)) :
    CInv X (.edge M i n' (limitF X.counted X.FL r')) := by
  obtain ⟨-, hidf⟩ := (ihf : W2A f ∧ _)
  obtain ⟨hjex, -⟩ := (ihj : (j.kind = .exact → ∃ t, j.mark = .conc t) ∧ _)
  obtain ⟨-, hidg⟩ := (ihg : W2A g ∧ _)
  refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
  have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
  rw [limitF_keep hs hab0] at hab ⊢
  -- the binding back
  have hr'b : r'.fact.base = e2.2.base := by
    obtain ⟨_, _, _, _, _, _, _, hrr, _⟩ := apply_shape hr'
    rw [hrr, norm_base]
  obtain ⟨E1, E2, he21, he22⟩ := hs.fromC _ _ _ _ hE e2 he2 (.inr (hr'b.symm.trans hab.1))
  rw [he21, he22] at hr'
  obtain ⟨-, hrb, hr'p, hrex, hrst⟩ := bind_apply hr'
  -- the summary
  obtain ⟨x, hx, hrx⟩ := List.mem_map.mp hr
  have hrx' : r = AFact.norm ⟨x.fact, x.demand || g.demand⟩ := hrx.symm
  have hrne : r.fact.kind ≠ .exact := fun hk => hab.2.2 (hrex hk)
  have hrp : r.fact.path = x.fact.path := by rw [hrx', norm_path]
  have hrb' : r.fact.base = x.fact.base := by rw [hrx', norm_base]
  have hxne : x.fact.kind ≠ .exact := fun hk => hrne (by rw [hrx']; exact norm_exact hk)
  obtain ⟨p, k, ap, m, hajb, -, hmc, hxx, hgeo⟩ := apply_shape hx
  have hxp : x.fact.path = p := by rw [hxx, norm_path]
  have hxb : x.fact.base = g.fact.base := by rw [hxx, norm_base]
  have hkx : k = .exact → x.fact.kind = .exact := fun hk => by rw [hxx]; exact norm_exact hk
  have hgb : g.fact.base = X.sB := by rw [← hxb, ← hrb', hrb]
  have hAP : AbovePos X p := by
    have h0 := hab.2.1
    rw [hr'p, hrp, hxp] at h0
    exact h0
  obtain ⟨r0, har0⟩ := applicable_path hap
  obtain ⟨rr, hrr, hb⟩ : ∃ rr, a.fact.path = j.path ++ rr ∧
      belowCase a.fact.kind j.kind rr g.fact.path g.fact.kind = some (p, k, ap) := by
    rcases hgeo with ⟨rr, hrr, hb⟩ | ⟨rr, hjp, hne, -⟩
    · exact ⟨rr, hrr, hb⟩
    · exfalso
      have h0 := congrArg List.length (har0.trans (by rw [hjp, List.append_assoc]) :
        a.fact.path = a.fact.path ++ (rr ++ r0))
      rw [List.length_append, List.length_append] at h0
      cases rr with
      | nil => exact hne rfl
      | cons x rs =>
        have h1 : (x :: rs).length + r0.length = 0 :=
          Nat.add_left_cancel (h0.symm.trans (Nat.add_zero _).symm)
        rw [List.length_cons, Nat.add_right_comm] at h1
        exact Nat.succ_ne_zero _ h1
  cases hgk : g.fact.kind with
  | star Eg =>
    rw [hgk] at hb
    obtain ⟨hp, hex, hst⟩ := below_star_tk hb
    have hgab : AboveNE X g.fact := ⟨hgb, abovePos_prefix (hp ▸ hAP), by rw [hgk]; intro h; cases h⟩
    obtain ⟨⟨Ej, hj⟩, -, hga, hgd⟩ := hidg hgab
    have hjp : j.path = g.fact.path := by rw [hj]
    have hap' : a.fact.path = p := by rw [hrr, hjp, hp]
    have hab' : a.fact.base = X.sB := by rw [hajb, hj]
    have hane : a.fact.kind ≠ .exact := fun hk => hxne (hkx (hex hk))
    -- the caller fact behind the added fact
    have hae : a.fact.base = e1.2.base := by
      obtain ⟨_, _, _, _, _, _, _, hrr', _⟩ := apply_shape ha
      rw [hrr', norm_base]
    obtain ⟨F1, F2, he11, he12⟩ := hs.toC _ _ _ _ hE e1 he1 (.inr (hae.symm.trans hab'))
    rw [he11, he12] at ha
    obtain ⟨-, hfb, hafp, hfex, hfst⟩ := bind_apply ha
    have hfne : f.fact.kind ≠ .exact := fun hk => hane (hfex hk)
    have hfab : AboveNE X f.fact := ⟨hfb, by rw [← hafp, hap']; exact hAP, hfne⟩
    obtain ⟨⟨E0, hi⟩, ⟨Ef, hfk⟩, hfa, hfd⟩ := hidf hfab
    obtain ⟨⟨Ea, hak⟩, ham, had⟩ := hfst Ef hfk hfa hfd
    obtain ⟨⟨e', hk⟩, hap0⟩ := hst Ea hak
    have hmabs : Exact.absB m = true := Exact.comp_abs hga (by rw [ham]; exact hfa) hmc
    have hx' : x = ⟨⟨g.fact.base, p, .star e', m⟩, false⟩ := by
      rw [hxx, hk, had, hap0]
      exact norm_keep rfl hmabs rfl
    have hr2 : r = ⟨⟨g.fact.base, p, .star e', m⟩, false⟩ := by
      rw [hrx', hx', hgd]
      exact norm_keep rfl hmabs rfl
    obtain ⟨hr'k, hr'm, hr'd⟩ := hrst e' (by rw [hr2]) (by rw [hr2]; exact hmabs) (by rw [hr2])
    refine ⟨⟨E0, ?_⟩, hr'k, by rw [hr'm, hr2]; exact hmabs, hr'd⟩
    rw [hr'p, hrp, hxp, ← hap', hafp]
    exact hi
  | any =>
    rw [hgk] at hb
    obtain ⟨hp, -⟩ := below_any_tk hb
    have hgab : AboveNE X g.fact := ⟨hgb, hp ▸ hAP, by rw [hgk]; intro h; cases h⟩
    obtain ⟨-, ⟨E, hgk'⟩, -, -⟩ := hidg hgab
    rw [hgk] at hgk'
    cases hgk'
  | exact =>
    rw [hgk] at hb
    obtain ⟨-, hk | ⟨⟨ec, hak⟩, hjk, -⟩⟩ := below_exact_tk hb
    · exact absurd (hkx hk) hxne
    · obtain ⟨t, hjt⟩ := hjex hjk
      have hms := Exact.applicable_markSub hap
      rw [hjt] at hms
      have ham := markSub_conc hms
      have := (applyEdge_w2 ha ec hak).1
      rw [ham] at this
      cases this

/-- THE STATIC INVARIANT HOLDS (the final rule, under the construction hypotheses). In
    particular no static fact `(S, <C>, [any], ...)` (nor any non-exact, non-identity static fact
    above a position) exists: `(S, <C>, [any], ...)` is impossible by construction. -/
theorem cinv_all {X : SCtx} (hs : SWF X) (hgen : X.gen = true) (hdeep : X.deepAns = true)
    (hfb : X.fb = .off) {o : SObj} (h : DS X o) : CInv X o := by
  induction h with
  | root _ =>
    exact ⟨fun _ => ⟨zeroMark, rfl⟩, fun hab => absurd hab.1.symm hs.base⟩
  | @start M i _ ih =>
    obtain ⟨-, hab⟩ := (ih : (i.kind = .exact → ∃ t, i.mark = .conc t) ∧ _)
    refine ⟨startFact_w2 i, fun habs => ?_⟩
    obtain ⟨b, p, k, m⟩ := i
    have hsb := Example.startFact_base ⟨b, p, k, m⟩
    have hsp := Example.startFact_path ⟨b, p, k, m⟩
    have hine : k ≠ .exact := fun hk => habs.2.2 (by subst hk; cases m <;> rfl)
    obtain ⟨⟨E, hk⟩, hm⟩ := hab ⟨by rw [← hsb]; exact habs.1, by rw [← hsp]; exact habs.2.1, hine⟩
    simp only at hk hm
    subst hk hm
    have hb : b = X.sB := habs.1
    subst hb
    exact ⟨⟨E, rfl⟩, ⟨E, rfl⟩, rfl, rfl⟩
  | step _ hE hf ih => exact step_inv hs hgen hE ih hf
  | reqStmt _ _ _ _ => trivial
  | sreqStmt _ _ _ _ _ => trivial
  | pass _ _ _ ih => exact ih
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨-, hid⟩ := (ih : W2A f ∧ _)
    refine ⟨fun E hk => (applyEdge_w2 ha E hk).1, fun hab => ?_⟩
    have hae : a.fact.base = e.2.base := by
      obtain ⟨_, _, _, _, _, _, _, hrr, _⟩ := apply_shape ha
      rw [hrr, norm_base]
    obtain ⟨E1, E2, he1, he2⟩ := hs.toC _ _ _ _ hE e he (.inr (hae.symm.trans hab.1))
    rw [he1, he2] at ha
    obtain ⟨-, hfb, hafp, hfex, hfst⟩ := bind_apply ha
    have hfne : f.fact.kind ≠ .exact := fun hk => hab.2.2 (hfex hk)
    obtain ⟨-, ⟨Ef, hfk⟩, hfa, hfd⟩ := hid ⟨hfb, by rw [← hafp]; exact hab.2.1, hfne⟩
    obtain ⟨hak, ham, -⟩ := hfst Ef hfk hfa hfd
    exact ⟨hak, by rw [ham]; exact hfa⟩
  | @initA m a _ _ =>
    rw [hs.alpha]
    unfold policy
    split
    · exact ⟨fun _ => ⟨zeroMark, rfl⟩, fun hab => absurd hab.1.symm hs.base⟩
    · split
      · rename_i h
        cases h
      · exact ⟨(fun hk => by cases hk), fun _ => ⟨⟨_, rfl⟩, rfl⟩⟩
  | ret _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact ret_inv hs hE he1 ha hap hr he2 hr' ihf ihj ihg
  | sret _ _ _ _ _ hok _ _ _ _ _ _ _ =>
    unfold SCtx.fbOK at hok
    rw [hfb] at hok
    cases hok
  | reqSink _ _ _ _ => trivial
  | @answer M i t a _ _ hm hov _ iha =>
    obtain ⟨-, haab⟩ := (iha : W2P a ∧ _)
    refine ⟨fun _ => ⟨t, ?_⟩, fun hab => ?_⟩
    · unfold SCtx.ansInit
      split
      · rfl
      · exact answerInit_mark
    · unfold SCtx.ansInit at hab
      rw [hdeep] at hab
      split at hab
      · have := (haab ⟨hab.1, hab.2.1, hab.2.2⟩).2
        rw [hm] at this
        cases this
      · rename_i hcond
        have hib : i.base = X.sB := by rw [← answerInit_base (a := a) (t := t)]; exact hab.1
        have hiap : AbovePos X i.path := by rw [← answerInit_path (a := a) (t := t)]; exact hab.2.1
        have hdp : dropPrefix i.path a.path = none := by
          cases hdp : dropPrefix i.path a.path with
          | none => rfl
          | some r =>
            exfalso
            apply hcond
            rw [hib, Nat.beq_refl, hdp]
            rfl
        unfold overlapB at hov
        simp only [Bool.and_eq_true] at hov
        obtain ⟨hbeq, hrel⟩ := hov
        cases hrl : relate a.path i.path with
        | below r =>
          rw [hrl] at hrel
          have hip := CoreAux.relate_below_inv hrl
          cases r with
          | nil =>
            rw [hip, List.append_nil, Exact.dropPrefix_self] at hdp
            cases hdp
          | cons x rs =>
            have hane : a.kind ≠ .exact := fun hk => by rw [hk] at hrel; cases hrel
            have hab' : a.base = X.sB := (CoreAux.beq_iff.mp hbeq).trans hib
            have := (haab ⟨hab', abovePos_prefix (hip ▸ hiap), hane⟩).2
            rw [hm] at this
            cases this
        | above r =>
          obtain ⟨hap, -⟩ := CoreAux.relate_above_inv hrl
          rw [hap, Exact.dropPrefix_append] at hdp
          cases hdp
        | apart =>
          rw [hrl] at hrel
          cases hrel
  | sanswer _ _ _ _ _ => exact ⟨(fun hk => by cases hk), fun _ => ⟨⟨_, rfl⟩, rfl⟩⟩
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | sreqUp _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨hw, hid⟩ := (ih : W2A f ∧ _)
    refine ⟨cleanRes_w2 hw hf, fun hab => ?_⟩
    rcases cleanRes_cases hf with rfl | ⟨-, t, ha, -, rfl⟩ | ⟨t, hct, rfl⟩ | ⟨hcb, hcm, rfl⟩
    · exact hid hab
    · obtain ⟨hi, hk, -, hd⟩ := hid ⟨hab.1, hab.2.1, hab.2.2⟩
      exact ⟨hi, hk, Exact.addEx_abs t ha, hd⟩
    · rcases Exact.concPart_cases cl f with ⟨-, -, -, hcp⟩ | hcp
      · rw [hcp] at hab
        exact absurd rfl hab.2.2
      · rw [hcp] at hab
        have := (hid hab).2.2.1
        rw [hct] at this
        cases this
    · have hfb' : f.fact.base = X.sB := by
        have h0 := hab.1
        rw [norm_base] at h0
        exact h0
      obtain ⟨t, ht⟩ := hs.clean _ _ _ _ hE (hcb ▸ hfb')
      rw [hcm] at ht
      cases ht
  | reqClean _ _ _ _ => trivial
  | filt _ _ _ ih => exact ih

#print axioms cinv_all
#print axioms id_apply
#print axioms step_inv
#print axioms ret_inv

/-! ### 13.3 Requests, answers and the bound on positions -/

/-- The final rule. -/
structure Design (X : SCtx) : Prop where
  gen  : X.gen = true
  deep : X.deepAns = true
  wide : X.wide = true
  below : X.ansBelow = true
  fb   : X.fb = .off

/-- NO `[any]` ON THE STATIC BASE ABOVE A POSITION: under the construction hypotheses the final rule
    derives no edge `(S, q, [any], ...)` with `q` strictly above a (truncated) static position, i.e.
    `q` the root or a class `[<C>]` of which a field is a position; in particular no
    `(S, <C>, [any], ...)`. A non-exact static fact there is an identity static `*` edge in the
    normal layer. (Below a static field the ordinary rules apply: `(S, <C>.f, [any], ...)` may
    exist, as for an instance field.) -/
theorem no_any_above {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DS X (.edge M i n f)) (hb : f.fact.base = X.sB)
    (hp : AbovePos X f.fact.path) :
    f.fact.kind ≠ .any ∧ (f.fact.kind ≠ .exact → f.demand = false ∧
      ∃ E0, i = ⟨X.sB, f.fact.path, .star E0, .star⟩) := by
  have hc := (cinv_all hs hd.gen hd.deep hd.fb h).2
  refine ⟨fun hk => ?_, fun hne => ?_⟩
  · obtain ⟨-, ⟨E, hE⟩, -⟩ := hc ⟨hb, hp, by rw [hk]; decide⟩
    rw [hk] at hE
    cases hE
  · obtain ⟨hi, -, -, hd0⟩ := hc ⟨hb, hp, hne⟩
    exact ⟨hd0, hi⟩

#print axioms no_any_above

/-- The final rule fires on the read of `readStmt` on the abstract static root edge. -/
theorem gen_read_fires {sB x : Base} {p : List Acc} {E E0 : Excl} (hp : p ≠ [])
    (hE : E.admits p = true) :
    genFireB sB ⟨sB, [], .star E0, .star⟩ ⟨⟨sB, [], .star E, .star⟩, false⟩ (pat sB p, pat x []) =
      true := by
  obtain ⟨a, r, rfl⟩ : ∃ a r, p = a :: r := by
    cases p with
    | nil => exact absurd rfl hp
    | cons a r => exact ⟨a, r, rfl⟩
  have hE' : E.admits (a :: r) = true := hE
  have h1 : idEdgeB sB ⟨sB, [], .star E0, .star⟩ ⟨⟨sB, [], .star E, .star⟩, false⟩ = true := by
    unfold idEdgeB
    rw [Nat.beq_refl]
    all_goals rfl
  unfold genFireB strictBelowB
  rw [h1]
  show (true && Nat.beq sB sB && admitsTailB (.star E) (a :: r)) = true
  rw [Nat.beq_refl]
  exact hE'

/-- THE FINAL RULE'S EFFECT on a read: on the abstract static root edge every result of the step is
    on the static base, so there is NO fact on `x`, in particular no `[any]` read. -/
theorem gen_read_DS {counted : Acc → Bool} {L : Nat} {sB x : Base} {p : List Acc} {E E0 : Excl}
    (hp : p ≠ []) (hE : E.admits p = true) {f' : AFact}
    (h : f' ∈ (transfer counted L (sKeepP (genFireB sB ⟨sB, [], .star E0, .star⟩
      ⟨⟨sB, [], .star E, .star⟩, false⟩) (readStmt sB x p)) ⟨⟨sB, [], .star E, .star⟩, false⟩).facts) :
    f'.fact.base = sB := by
  rcases ds_step_from_kept h with ⟨_, rfl⟩ | ⟨e, he, hf, y, hy, rfl⟩
  · rfl
  · rw [limitF_base, applyEdge_base hy]
    rcases List.mem_cons.mp he with rfl | he'
    · rfl
    · rw [List.mem_singleton.mp he', gen_read_fires hp hE] at hf
      cases hf

/-- Under the final rule the read raises the position request for `p` truncated to the static field
    (`[<C>, s]` for `x = C.s`; `[<C>, s]` also for a deeper read `x = C.s.g`) on the static root
    premise. -/
theorem gen_read_sreq {X : SCtx} {M : MethodId} {n n' : Node} {x : Base} {p : List Acc}
    {E E0 : Excl} (hg : X.gen = true) (hp : p ≠ []) (hE : E.admits p = true)
    (hf : DS X (.edge M ⟨X.sB, [], .star E0, .star⟩ n ⟨⟨X.sB, [], .star E, .star⟩, false⟩))
    (he : (M, n, Instr.stmt (readStmt X.sB x p), n') ∈ X.P.edges) :
    DS X (.sreq M ⟨X.sB, [], .star E0, .star⟩ (p.take 2)) := by
  have h := DS.sreqStmt (e := (pat X.sB p, pat x [])) hf he
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (by unfold SCtx.fireB; rw [hg, if_pos rfl]; exact gen_read_fires hp hE)
  rw [reqP_gen hg] at h
  exact h

#print axioms gen_read_DS
#print axioms gen_read_sreq

def edgesBound (sB : Base) : List MicroEdge → Nat
  | [] => 0
  | e :: es => max (if Nat.beq e.1.base sB then e.1.path.length else 0) (edgesBound sB es)

def stmtBound (sB : Base) : List (MethodId × Node × Instr × Node) → Nat
  | [] => 0
  | (_, _, .stmt s, _) :: es => max (edgesBound sB s.edges) (stmtBound sB es)
  | _ :: es => stmtBound sB es

def sinkBound (sB : Base) : List (MethodId × Node × PFact) → Nat
  | [] => 0
  | (_, _, s) :: ss => max (if Nat.beq s.base sB then s.path.length else 0) (sinkBound sB ss)

/-- An upper bound on the length of a static position. -/
def posBound (X : SCtx) : Nat := max (stmtBound X.sB X.P.edges) (sinkBound X.sB X.sinks)

theorem edgesBound_le {sB : Base} {e : MicroEdge} (hb : e.1.base = sB) :
    ∀ {es : List MicroEdge}, e ∈ es → e.1.path.length ≤ edgesBound sB es
  | [], h => absurd h List.not_mem_nil
  | e' :: es, h => by
    show _ ≤ max _ _
    rcases List.mem_cons.mp h with rfl | h'
    · rw [hb, Nat.beq_refl, if_pos rfl]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (edgesBound_le hb h') (Nat.le_max_right _ _)

theorem stmtBound_le {sB : Base} {M n n' : Nat} {s : Stmt} {e : MicroEdge} (he : e ∈ s.edges)
    (hb : e.1.base = sB) :
    ∀ {es : List (MethodId × Node × Instr × Node)}, (M, n, Instr.stmt s, n') ∈ es →
      e.1.path.length ≤ stmtBound sB es
  | [], h => absurd h List.not_mem_nil
  | (a, b, ins, d) :: es, h => by
    rcases List.mem_cons.mp h with h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨-, -, rfl, -⟩ := h'
      exact Nat.le_trans (edgesBound_le hb he) (Nat.le_max_left _ _)
    · have ih := stmtBound_le he hb h'
      cases ins with
      | stmt s' => exact Nat.le_trans ih (Nat.le_max_right _ _)
      | call _ => exact ih
      | clean _ => exact ih
      | filt _ _ => exact ih

theorem sinkBound_le {sB : Base} {M n : Nat} {s : PFact} (hb : s.base = sB) :
    ∀ {ss : List (MethodId × Node × PFact)}, (M, n, s) ∈ ss → s.path.length ≤ sinkBound sB ss
  | [], h => absurd h List.not_mem_nil
  | (a, b, s') :: ss, h => by
    show _ ≤ max _ _
    rcases List.mem_cons.mp h with h' | h'
    · simp only [Prod.mk.injEq] at h'
      obtain ⟨-, -, rfl⟩ := h'
      rw [hb, Nat.beq_refl, if_pos rfl]
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (sinkBound_le hb h') (Nat.le_max_right _ _)

theorem posIn_le {X : SCtx} {p : List Acc} (h : PosIn X p) : p.length ≤ posBound X := by
  rcases h with ⟨M, n, s, n', e, hE, he, hb, rfl⟩ | ⟨M, n, s, hs, hb, rfl⟩
  · exact Nat.le_trans (List.length_take_le' 2 _)
      (Nat.le_trans (stmtBound_le he hb hE) (Nat.le_max_left _ _))
  · exact Nat.le_trans (List.length_take_le' 2 _)
      (Nat.le_trans (sinkBound_le hb hs) (Nat.le_max_right _ _))

/-- An added fact above the requested position: it overlaps it and its path is a strict prefix. -/
theorem above_parts {sB : Base} {a : PFact} {p : List Acc} (h : aboveB sB a p = true) :
    a.base = sB ∧ ∃ r, r ≠ [] ∧ p = a.path ++ r ∧ admitsTailB a.kind r = true := by
  unfold aboveB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hov, hnb⟩ := h
  unfold overlapB at hov
  simp only [Bool.and_eq_true] at hov
  obtain ⟨hb, hrel⟩ := hov
  refine ⟨CoreAux.beq_iff.mp hb, ?_⟩
  cases hrl : relate a.path (sAns sB p).path with
  | below r =>
    rw [hrl] at hrel
    have hp : p = a.path ++ r := CoreAux.relate_below_inv hrl
    cases r with
    | nil =>
      exfalso
      unfold belowB at hnb
      rw [hp, List.append_nil, Exact.dropPrefix_self] at hnb
      cases hnb
    | cons x rs => exact ⟨x :: rs, List.cons_ne_nil _ _, hp, hrel⟩
  | above r =>
    exfalso
    obtain ⟨hap, -⟩ := CoreAux.relate_above_inv hrl
    unfold belowB at hnb
    have hap' : a.path = p ++ r := hap
    rw [hap', Exact.dropPrefix_append] at hnb
    cases hnb
  | apart =>
    rw [hrl] at hrel
    cases hrel

theorem aboveNE_of_above {X : SCtx} {a : PFact} {p : List Acc} (hp : PosIn X p)
    (h : aboveB X.sB a p = true) : AboveNE X a := by
  obtain ⟨hb, r, hne, hpr, hadm⟩ := above_parts h
  refine ⟨hb, ⟨p, r, hp, hne, hpr⟩, fun hk => ?_⟩
  rw [hk, admits_exact_nil hne] at hadm
  cases hadm

/-- An identity static `*` premise and a static `*` fact at the same path relate the same path. -/
theorem id_den {sB : Base} {q : List Acc} {E0 : Excl} {x : PFact} {l0 l1 : Loc}
    (hx : x.base = sB) (hxp : x.path = q) (hxk : ∃ E, x.kind = .star E)
    (hd : den ⟨sB, q, .star E0, .star⟩ x l0 l1) : l0.base = sB ∧ l0.path = l1.path := by
  obtain ⟨E, hk⟩ := hxk
  obtain ⟨xb, xp, xk, xm⟩ := x
  simp only at hx hxp hk
  subst hx hxp hk
  obtain ⟨h0b, -, -, -, -, σ, τ, h0p, h1p, -, hτ, -⟩ := hd
  exact ⟨h0b, by rw [h0p, h1p, hτ]⟩

/-- Behind an added fact above a position stands an identity static `*` caller edge. -/
theorem bind_identity {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {i : PFact}
    {n n' : Node} {f : AFact} {c : Call} {e : MicroEdge} {a : AFact}
    (hf : DS X (.edge M i n f)) (hE : (M, n, Instr.call c, n') ∈ X.P.edges) (he : e ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e.1 e.2).facts) (hab : AboveNE X a.fact) :
    (∃ E0, i = ⟨X.sB, a.fact.path, .star E0, .star⟩) ∧ (∃ E, a.fact.kind = .star E) ∧
      Exact.absB a.fact.mark = true := by
  obtain ⟨-, hid⟩ := (cinv_all hs hd.gen hd.deep hd.fb hf : W2A f ∧ _)
  have hae : a.fact.base = e.2.base := by
    obtain ⟨_, _, _, _, _, _, _, hrr, _⟩ := apply_shape ha
    rw [hrr, norm_base]
  obtain ⟨E1, E2, he1, he2⟩ := hs.toC _ _ _ _ hE e he (.inr (hae.symm.trans hab.1))
  rw [he1, he2] at ha
  obtain ⟨-, hfb, hafp, hfex, hfst⟩ := bind_apply ha
  have hfne : f.fact.kind ≠ .exact := fun hk => hab.2.2 (hfex hk)
  obtain ⟨⟨E0, hi⟩, ⟨Ef, hfk⟩, hfa, hfd⟩ := hid ⟨hfb, by rw [← hafp]; exact hab.2.1, hfne⟩
  obtain ⟨hak, ham, -⟩ := hfst Ef hfk hfa hfd
  exact ⟨⟨E0, by rw [hafp]; exact hi⟩, hak, by rw [ham]; exact hfa⟩

/-- The motive of `sreq_inv`. -/
def SReqInv (X : SCtx) : SObj → Prop
  | .sreq _ i p => i.mark = .star ∧ i.base = X.sB ∧ PosIn X p ∧ ∃ r, r ≠ [] ∧ p = i.path ++ r
  | _ => True

theorem idEdge_parts {sB : Base} {i : PFact} {f : AFact} (h : idEdgeB sB i f = true) :
    (∃ E0, i = ⟨sB, i.path, .star E0, .star⟩) ∧ f.fact.base = sB ∧ f.fact.path = i.path ∧
      (∃ E, f.fact.kind = .star E) ∧ Exact.absB f.fact.mark = true ∧ f.demand = false := by
  unfold idEdgeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hib, hik⟩, him⟩, hfb⟩, hfp⟩, hfk⟩, hfa⟩, hfd⟩ := h
  refine ⟨?_, CoreAux.beq_iff.mp hfb, hfp, ?_, hfa, hfd⟩
  · obtain ⟨b, p, k, m⟩ := i
    simp only at hib hik him
    cases k with
    | star E0 =>
      subst him
      exact ⟨E0, by rw [CoreAux.beq_iff.mp hib]⟩
    | any => cases hik
    | exact => cases hik
  · cases hk : f.fact.kind with
    | star E => exact ⟨E, rfl⟩
    | any => rw [hk] at hfk; cases hfk
    | exact => rw [hk] at hfk; cases hfk

theorem strictBelow_parts {k : Kind} {q p : List Acc} (h : strictBelowB k q p = true) :
    ∃ r, r ≠ [] ∧ p = q ++ r ∧ admitsTailB k r = true := by
  unfold strictBelowB at h
  cases hd : dropPrefix q p with
  | none => rw [hd] at h; cases h
  | some r =>
    rw [hd] at h
    cases r with
    | nil => cases h
    | cons x rs => exact ⟨x :: rs, List.cons_ne_nil _ _, CoreAux.dropPrefix_some.mp hd, h⟩

theorem genFire_parts {sB : Base} {i : PFact} {f : AFact} {e : MicroEdge}
    (h : genFireB sB i f e = true) :
    idEdgeB sB i f = true ∧ i.path.length ≤ 1 ∧ e.1.base = sB ∧ ∃ r, r ≠ [] ∧
      e.1.path = f.fact.path ++ r ∧ admitsTailB f.fact.kind r = true := by
  unfold genFireB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hid, hl⟩, hb⟩, hs⟩ := h
  exact ⟨hid, hl, CoreAux.beq_iff.mp hb, strictBelow_parts hs⟩

/-- A request truncated to the static field from an identity edge at the root or a class position
    is strictly below it. -/
theorem take2_split {q r : List Acc} (hq : q.length ≤ 1) (hne : r ≠ []) :
    ∃ r', r' ≠ [] ∧ (q ++ r).take 2 = q ++ r' := by
  cases r with
  | nil => exact absurd rfl hne
  | cons x rs =>
    cases q with
    | nil => exact ⟨x :: rs.take 1, List.cons_ne_nil _ _, rfl⟩
    | cons c q' =>
      cases q' with
      | nil => exact ⟨[x], List.cons_ne_nil _ _, rfl⟩
      | cons d q'' =>
        exfalso
        rw [List.length_cons, List.length_cons] at hq
        omega

/-- Every position request of the final rule is on an identity static `*` premise, for a
    position strictly below it. -/
theorem sreq_inv {X : SCtx} (hs : SWF X) (hd : Design X) {o : SObj} (h : DS X o) : SReqInv X o := by
  induction h with
  | @sreqStmt M i n f n' s e _ hE he hfire _ =>
    unfold SCtx.fireB at hfire
    rw [hd.gen, if_pos rfl] at hfire
    obtain ⟨hid, hl, heb, r, hne, hp, -⟩ := genFire_parts hfire
    obtain ⟨⟨E0, hi⟩, -, hfp, -⟩ := idEdge_parts hid
    have hp' : e.1.path = i.path ++ r := by rw [hp, hfp]
    obtain ⟨r', hne', ht⟩ := take2_split hl hne
    rw [reqP_gen hd.gen]
    refine ⟨by rw [hi], by rw [hi], .inl ⟨M, n, s, n', e, hE, he, heb, rfl⟩, r', hne', ?_⟩
    rw [hp', ht]
  | @sreqUp m j p M ic n f n' c e a _ hf hE _ he ha hcl ihs _ =>
    obtain ⟨-, -, hpos, -⟩ := (ihs : j.mark = .star ∧ j.base = X.sB ∧ PosIn X p ∧ _)
    unfold SCtx.climbOK at hcl
    rw [hd.wide, if_pos rfl] at hcl
    simp only [Bool.and_eq_true] at hcl
    obtain ⟨-, habv⟩ := hcl
    have hab := aboveNE_of_above hpos habv
    obtain ⟨⟨E0, hi⟩, -, -⟩ := bind_identity hs hd hf hE he ha hab
    obtain ⟨-, r, hne, hpr, -⟩ := above_parts habv
    refine ⟨by rw [hi], by rw [hi], hpos, r, hne, ?_⟩
    rw [hpr, hi]
  | root _ => trivial
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | reqStmt _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | sret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | sanswer _ _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | clean _ _ _ _ => trivial
  | reqClean _ _ _ _ => trivial
  | filt _ _ _ _ => trivial

theorem sreq_parts {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {i : PFact}
    {p : List Acc} (h : DS X (.sreq M i p)) :
    i.mark = .star ∧ i.base = X.sB ∧ PosIn X p ∧ ∃ r, r ≠ [] ∧ p = i.path ++ r :=
  sreq_inv hs hd h

#print axioms sreq_parts

/-! The answer of a mark request in the final rule. -/

theorem ansInit_mark {X : SCtx} {i a : PFact} {t : Mark} : (X.ansInit i a t).mark = .conc t := by
  unfold SCtx.ansInit
  split
  · rfl
  · exact answerInit_mark

theorem ansInit_covers {X : SCtx} {i a : PFact} {t : Mark} {l : Loc} (hi : i.covers l)
    (ha : a.covers l) (hm : l.mark = t) : (X.ansInit i a t).covers l := by
  unfold SCtx.ansInit
  split
  · exact ⟨ha.1, ha.2.1, hm⟩
  · exact answerInit_covers hi ha hm

theorem ansInit_applicable {X : SCtx} {i a : PFact} {t : Mark} (hap : applicable i a = true)
    (hm : a.mark = .conc t) : applicable (X.ansInit i a t) a = true := by
  unfold SCtx.ansInit
  split
  · obtain ⟨ab, ap, ak, am⟩ := a
    simp only at hm
    subst hm
    unfold applicable coversB
    simp only [Nat.beq_refl, markSubB, Exact.dropPrefix_self, tailSubB_refl, Bool.true_and,
      Bool.and_true]
    cases ak <;> rfl
  · exact answerInit_applicable hap hm

theorem ansInit_path {X : SCtx} {i a : PFact} {t : Mark} :
    ∃ r, (X.ansInit i a t).path = i.path ++ r := by
  unfold SCtx.ansInit
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨-, hs⟩ := hc
    cases hd : dropPrefix i.path a.path with
    | none => rw [hd] at hs; cases hs
    | some r => exact ⟨r, CoreAux.dropPrefix_some.mp hd⟩
  · exact ⟨[], by rw [answerInit_path, List.append_nil]⟩

/-- An answer to a position request covers the added facts at or below the position. -/
theorem sAns_applicable {sB : Base} {a : PFact} {p : List Acc} (hb : a.base = sB)
    (h : belowB a p = true) : applicable (sAns sB p) a = true := by
  unfold belowB at h
  cases hd : dropPrefix p a.path with
  | none => rw [hd] at h; cases h
  | some r =>
    dsimp only [applicable, coversB, sAns]
    rw [hb, Nat.beq_refl, hd]
    cases r with
    | nil =>
      cases a.kind with
      | star e => cases e <;> rfl
      | any => rfl
      | exact => rfl
    | cons x rs => rfl

/-! ### 13.4 The coverage theorem of the final rule -/

/-- Strong induction on a natural measure (constructive). -/
theorem strong_ind {α : Type} (μ : α → Nat) {P : α → Prop}
    (h : ∀ x, (∀ y, μ y < μ x → P y) → P x) : ∀ x, P x := by
  have key : ∀ n x, μ x ≤ n → P x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact h x (fun y hy => absurd (Nat.lt_of_lt_of_le hy hx) (Nat.not_lt_zero _))
    | succ n ih =>
      intro x hx
      exact h x (fun y hy => ih y (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hy hx)))
  exact fun x => key _ x (Nat.le_refl _)

/-- A request strictly below a premise lowers the measure `posBound - |path|`. -/
theorem measure_lt {X : SCtx} {q p r : List Acc} (hpos : PosIn X p) (hne : r ≠ [])
    (hpr : p = q ++ r) : posBound X - p.length < posBound X - q.length := by
  have h1 := posIn_le hpos
  have h2 : q.length < p.length := by
    rw [hpr, List.length_append]
    exact Nat.lt_add_of_pos_right (List.length_pos_iff.mpr hne)
  exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le h2 h1) h2

/-- The coverage statement of the final rule: an edge, a mark request, or a position request
    whose answer covers the entry location. -/
abbrev CovD (X : SCtx) (M : MethodId) (i : PFact) (n : Node) (l0 l : Loc) : Prop :=
  (∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l) ∨ DS X (.req M i l0.mark) ∨
  (∃ p, DS X (.sreq M i p) ∧ (sAns X.sB p).covers l0)

theorem α_applicable {X : SCtx} (hs : SWF X) : ∀ m a, applicable (X.α m a) a = true :=
  fun m a => by rw [hs.alpha]; exact policy_applicable _ m a

/-- A concrete initial fact has neither a mark request nor a position request. -/
theorem covD_conc {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {i : PFact} {n : Node}
    {l0 l : Loc} {t : Mark} (hc : CovD X M i n l0 l) (ht : i.mark = .conc t) :
    ∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l := by
  rcases hc with h | hr | ⟨p, hsr, -⟩
  · exact h
  · exact absurd ht (req_abstractS hr t)
  · have := (sreq_parts hs hd hsr).1
    rw [ht] at this
    cases this

/-- THE CALL STEP of the final rule. A callee position request is answered by the added fact if
    it is at or below the position (the answer is then read as usual, and its own requests are
    resolved in turn: they are strictly lower), or else it climbs: the added fact is an identity
    static `*` fact (`cinv_all`), so the caller premise is the identity at the same path, and the
    answer covers the caller entry location. No answer from above, no fallback. -/
theorem call_stepD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {c : Call} {e1 e2 : MicroEdge}
    {l0 l l1 l2 l3 : Loc}
    (hf : DS X (.edge M i n f)) (hdn : den i f.fact l0 l)
    (he : (M, n, Instr.call c, n') ∈ X.P.edges) (he1 : e1 ∈ c.toCallee) (hd1 : den e1.1 e1.2 l l1)
    (ihc : ∀ j, DS X (.init c.callee j) → j.covers l1 →
      CovD X c.callee j (X.P.exit c.callee) l1 l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    CovD X M i n' l0 l3 := by
  obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hdn hd1
  have hadd := DS.added hf he he1 ha
  have hac : a.fact.covers l1 := den_covers_final hda
  have useRet : ∀ j g, DS X (.init c.callee j) → applicable j a.fact = true →
      DS X (.edge c.callee j (X.P.exit c.callee) g) → den j g.fact l1 l2 →
      ∃ f', DS X (.edge M i n' f') ∧ den i f'.fact l0 l3 := by
    intro j g hj hap hg hdg
    obtain ⟨r, hr, hdr⟩ := summary_stepM (Exact.applicable_markSub hap) hda hdg
    obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hwf he he2 hdr hd2
    exact ⟨_, DS.ret hf he he1 ha hj hap hg hr he2 hr', limitF_sound hdr'⟩
  have key := strong_ind (α := PFact) (fun j => posBound X - j.path.length)
    (P := fun j => DS X (.init c.callee j) → j.covers l1 → applicable j a.fact = true →
      CovD X M i n' l0 l3) (by
    intro j rec hj hjc hap
    rcases ihc j hj hjc with ⟨g, hg, hdg⟩ | hreq | ⟨p, hsr, hpc⟩
    · exact .inl (useRet j g hj hap hg hdg)
    · -- a mark request on the callee initial fact
      have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
      rcases Coverage.mark_cases a.fact.mark with ham | ⟨t, ham⟩
      · have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hov
        rw [den_mark_abs hda ham] at hup
        exact .inr (.inl hup)
      · have hmk : a.fact.mark = .conc l1.mark := Coverage.den_mark_conc hda ham
        have hans := DS.answer hreq hadd hmk hov
        have hc' := ansInit_covers (X := X) (t := l1.mark) hjc hac rfl
        have hap' := ansInit_applicable (X := X) hap hmk
        obtain ⟨g, hg, hdg⟩ := covD_conc hs hd (ihc _ hans hc') ansInit_mark
        exact .inl (useRet _ g hans hap' hg hdg)
    · -- a position request on the callee initial fact
      obtain ⟨-, -, hpos, r, hne, hpr⟩ := sreq_parts hs hd hsr
      have hov : overlapB a.fact (sAns X.sB p) = true := overlapB_of_common hac hpc
      have hab0 : a.fact.base = X.sB := by
        unfold overlapB at hov
        simp only [Bool.and_eq_true] at hov
        exact CoreAux.beq_iff.mp hov.1
      cases hbl : belowB a.fact p with
      | true =>
        -- ANSWER: the added fact is at or below the position
        have hok : X.ansOK a.fact p = true := by
          unfold SCtx.ansOK
          rw [hov, hbl, Bool.or_true]
          rfl
        have hans := DS.sanswer hsr hadd hok
        exact rec (sAns X.sB p) (measure_lt hpos hne hpr) hans hpc (sAns_applicable hab0 hbl)
      | false =>
        -- CLIMB: the added fact is above the position
        have habv : aboveB X.sB a.fact p = true := by
          unfold aboveB
          rw [hov, hbl]
          rfl
        have hab := aboveNE_of_above hpos habv
        obtain ⟨⟨E0, hi⟩, hak, -⟩ := bind_identity hs hd hf he he1 ha hab
        have hib : i.base = X.sB := by rw [hi]
        have hcl : X.climbOK i a.fact p = true := by
          unfold SCtx.climbOK
          rw [hd.wide, if_pos rfl, hib, Nat.beq_refl, habv]
          rfl
        have hup := DS.sreqUp hsr hf he rfl he1 ha hcl
        rw [hi] at hda
        obtain ⟨h0b, h0p⟩ := id_den hab.1 rfl hak hda
        obtain ⟨-, ⟨σ, hlp, -⟩, -⟩ := hpc
        exact .inr (.inr ⟨p, hup, sAns_covers h0b (h0p.trans hlp)⟩))
  exact key _ (DS.initA hadd) (applicable_sound (α_applicable hs c.callee a.fact) hac)
    (α_applicable hs c.callee a.fact)

#print axioms call_stepD

/-- THE COVERAGE THEOREM of the final rule (no answer from above, no fallback), under the
    construction hypotheses. -/
theorem coverageD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow X.P M l0 n l) :
    ∀ i, DS X (.init M i) → i.covers l0 → CovD X M i n l0 l := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, DS.start hi, startFact_sound hc⟩
  | @step M l0 n l n' l' s _ he hst ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn⟩ | hr | hsr
    · rcases step_split (P := X.fireB i f) hst with hs' | ⟨e, hes, hfire, hde⟩
      · rcases transfer_sound (counted := X.counted) (L := X.FL)
            (sKeep_wf (hwf.stmtTouched _ _ _ _ he)) hdn hs' with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
        · exact .inl ⟨r, DS.step hf he hr, hdr⟩
        · exact .inr (.inl (DS.reqStmt hf he hq))
      · -- RAISE
        have hfire' := hfire
        unfold SCtx.fireB at hfire'
        rw [hd.gen, if_pos rfl] at hfire'
        obtain ⟨hid, -, -, -, -, -, -⟩ := genFire_parts hfire'
        obtain ⟨⟨E0, hi'⟩, hfb, hfp, hfk, -, -⟩ := idEdge_parts hid
        rw [hi'] at hdn
        obtain ⟨h0b, h0p⟩ := id_den hfb hfp hfk hdn
        obtain ⟨-, -, -, -, -, σ', -, hlp, -, -, -⟩ := hde
        refine .inr (.inr ⟨X.reqP e.1.path, DS.sreqStmt hf he hes hfire, ?_⟩)
        rw [reqP_gen hd.gen]
        exact sAns_covers h0b (h0p.trans (hlp.trans (by
          rw [← List.append_assoc, List.take_append_drop])))
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn⟩ | hr | hsr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hdn.2.1]
        exact hm
      exact .inl ⟨f, DS.pass hf he hb, hdn⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn⟩ | hr | hsr
    · exact call_stepD hs hd hwf hf hdn he he1 hd1 ihc he2 hd2
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn⟩ | hr | hsr
    · rcases cleanRes_sound hdn hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DS.clean hf he hr, hdr⟩
      · exact .inr (.inl (DS.reqClean hf he hq))
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn⟩ | hr | hsr
    · exact .inl ⟨f, DS.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hdn hl), hdn⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)

#print axioms coverageD

/-! ### 13.5 The vulnerability theorem of the final rule -/

mutual
/-- A GOOD initial fact of `M` for the pair `(l0, l)` at `n`: it is in `DS` and covers `l0`; an edge
    of it covers the pair; a mark request on it with the entry mark has a concrete good answer; a
    position request on it whose answer covers `l0` has a good initial fact at or below the
    position. -/
inductive GoodD (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : PFact → Prop where
  | mk {j : PFact} : DS X (.init M j) → j.covers l0 →
      (∃ f, DS X (.edge M j n f) ∧ den j f.fact l0 l) →
      (DS X (.req M j l0.mark) → GoodC X M n l0 l) →
      (∀ p, DS X (.sreq M j p) → (sAns X.sB p).covers l0 → GoodP X M n l0 l p) →
      GoodD X M n l0 l j
/-- A concrete good initial fact. -/
inductive GoodC (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : Prop where
  | mk {j : PFact} {t : Mark} : GoodD X M n l0 l j → j.mark = .conc t → GoodC X M n l0 l
/-- A good initial fact at or below the position `p`. -/
inductive GoodP (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : List Acc → Prop where
  | mk {j : PFact} {p r : List Acc} : GoodD X M n l0 l j → j.path = p ++ r → GoodP X M n l0 l p
end

/-- A concrete initial fact that covers the entry location is good. -/
theorem good_conc {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF) {M : MethodId}
    {n : Node} {l0 l : Loc} {j : PFact} {t : Mark} (hfl : Flow X.P M l0 n l)
    (hj : DS X (.init M j)) (hc : j.covers l0) (ht : j.mark = .conc t) : GoodD X M n l0 l j :=
  .mk hj hc (covD_conc hs hd (coverageD hs hd hwf hfl j hj hc) ht)
    (fun hr => absurd ht (req_abstractS hr t))
    (fun _ hsr _ => by
      have h1 := (sreq_parts hs hd hsr).1
      rw [ht] at h1
      cases h1)

/-- THE REACH THEOREM of the final rule: a real execution from a root to `(M, n, l)` has a good
    initial fact. -/
theorem reachD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF) {M : MethodId} {n : Node}
    {l : Loc} (hR : Reach X.P X.roots M n l) : ∃ l0 j, GoodD X M n l0 l j := by
  induction hR with
  | root hM hfl =>
    exact ⟨zeroLoc, zeroFact, good_conc hs hd hwf hfl (DS.root hM) Coverage.zeroFact_covers rfl⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨l0, i, hgi⟩ := ih
    cases hgi with
    | mk hi hic hedge hmark hpos =>
    obtain ⟨f, hf, hdn⟩ := hedge
    obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hdn hd1
    have hadd := DS.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    -- a mark request on a callee initial fact: a concrete good answer at or below it
    have markRes : ∀ j, DS X (.init c.callee j) → j.covers l1 → DS X (.req c.callee j l1.mark) →
        ∃ j', GoodD X c.callee n2 l1 l2 j' ∧ (∃ t, j'.mark = .conc t) ∧ ∃ r, j'.path = j.path ++ r := by
      intro j hj hjc hreq
      have hconc : ∃ a', DS X (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases Coverage.mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapB_of_common hac hjc)
          rw [den_mark_abs hda ham] at hup
          obtain ⟨hg', ht⟩ := hmark hup
          cases hg' with
          | mk hj' hjc' hedge' _ _ =>
          obtain ⟨f', hf', hdn'⟩ := hedge'
          obtain ⟨a', ha', hda'⟩ := Coverage.bind_in hwf he he1 hdn' hd1
          obtain ⟨t1, h1⟩ := edge_concS hf' ht
          obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
          exact ⟨a'.fact, DS.added hf' he he1 ha', den_covers_final hda',
            Coverage.den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, Coverage.den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := DS.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      obtain ⟨r, hr⟩ := ansInit_path (X := X) (i := j) (a := a') (t := l1.mark)
      exact ⟨_, good_conc hs hd hwf hfc hans (ansInit_covers hjc hac' rfl) ansInit_mark,
        ⟨_, ansInit_mark⟩, r, hr⟩
    have key := strong_ind (α := PFact) (fun j => posBound X - j.path.length)
      (P := fun j => DS X (.init c.callee j) → j.covers l1 →
        ∃ j', GoodD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = j.path ++ r) (by
      intro j rec hj hjc
      -- a position request on `j`: answered at or below it, or after the climb
      have posRes : ∀ p, DS X (.sreq c.callee j p) → (sAns X.sB p).covers l1 →
          ∃ j', GoodD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = p ++ r := by
        intro p hsr hpc
        obtain ⟨-, -, hpos', r, hne, hpr⟩ := sreq_parts hs hd hsr
        have hlt := measure_lt hpos' hne hpr
        -- an added fact at or below the position answers it
        have answerFrom : ∀ a', DS X (.added c.callee a') → a'.covers l1 → belowB a' p = true →
            ∃ j', GoodD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = p ++ r := by
          intro a' hadd' hac' hbl
          have hov := overlapB_of_common hac' hpc
          have hok : X.ansOK a' p = true := by
            unfold SCtx.ansOK
            rw [hov, hbl, Bool.or_true]
            rfl
          exact rec (sAns X.sB p) hlt (DS.sanswer hsr hadd' hok) hpc
        have hov : overlapB a.fact (sAns X.sB p) = true := overlapB_of_common hac hpc
        cases hbl : belowB a.fact p with
        | true => exact answerFrom a.fact hadd hac hbl
        | false =>
          -- the climb to the caller premise, answered there at or below the position
          have habv : aboveB X.sB a.fact p = true := by
            unfold aboveB
            rw [hov, hbl]
            rfl
          have hab := aboveNE_of_above hpos' habv
          obtain ⟨⟨E0, hi'⟩, hak, -⟩ := bind_identity hs hd hf he he1 ha hab
          have hib : i.base = X.sB := by rw [hi']
          have hcl : X.climbOK i a.fact p = true := by
            unfold SCtx.climbOK
            rw [hd.wide, if_pos rfl, hib, Nat.beq_refl, habv]
            rfl
          have hup := DS.sreqUp hsr hf he rfl he1 ha hcl
          have hda' := hda
          rw [hi'] at hda'
          obtain ⟨h0b, h0p⟩ := id_den hab.1 rfl hak hda'
          have hpc0 : (sAns X.sB p).covers l0 := by
            obtain ⟨-, ⟨σ, hlp, -⟩, -⟩ := hpc
            exact sAns_covers h0b (h0p.trans hlp)
          cases hpos p hup hpc0 with
          | @mk jc pp rc hgc hrc =>
          cases hgc with
          | mk hjc' _ hedge' _ _ =>
          obtain ⟨f'', hf'', hdn''⟩ := hedge'
          obtain ⟨a'', ha'', hda''⟩ := Coverage.bind_in hwf he he1 hdn'' hd1
          have hac'' : a''.fact.covers l1 := den_covers_final hda''
          cases hbl'' : belowB a''.fact p with
          | true => exact answerFrom a''.fact (DS.added hf'' he he1 ha'') hac'' hbl''
          | false =>
            exfalso
            have hov'' := overlapB_of_common hac'' hpc
            have habv'' : aboveB X.sB a''.fact p = true := by
              unfold aboveB
              rw [hov'', hbl'']
              rfl
            obtain ⟨⟨E1, hjc''⟩, -, -⟩ :=
              bind_identity hs hd hf'' he he1 ha'' (aboveNE_of_above hpos' habv'')
            obtain ⟨-, r3, hne3, hp3, -⟩ := above_parts habv''
            have hjp : jc.path = a''.fact.path := by rw [hjc'']
            have h0 := congrArg List.length (hrc.symm.trans hjp)
            rw [hp3, List.length_append, List.length_append] at h0
            cases r3 with
            | nil => exact hne3 rfl
            | cons x rs =>
              have h1 : (x :: rs).length + rc.length = 0 :=
                Nat.add_left_cancel ((Nat.add_assoc _ _ _).symm.trans (h0.trans (Nat.add_zero _).symm))
              rw [List.length_cons, Nat.add_right_comm] at h1
              exact Nat.succ_ne_zero _ h1
      rcases coverageD hs hd hwf hfc j hj hjc with ⟨g, hg, hdg⟩ | hreq | ⟨p, hsr, hpc⟩
      · refine ⟨j, .mk hj hjc ⟨g, hg, hdg⟩ (fun hreq => ?_) (fun p hsr hpc => ?_),
          [], by rw [List.append_nil]⟩
        · obtain ⟨j', hg', ⟨t, ht⟩, -⟩ := markRes j hj hjc hreq
          exact .mk hg' ht
        · obtain ⟨j', hg', r, hr⟩ := posRes p hsr hpc
          exact .mk hg' hr
      · obtain ⟨j', hg', -, r, hr⟩ := markRes j hj hjc hreq
        exact ⟨j', hg', r, hr⟩
      · obtain ⟨-, -, -, r, -, hpr⟩ := sreq_parts hs hd hsr
        obtain ⟨j', hg', r', hr'⟩ := posRes p hsr hpc
        exact ⟨j', hg', r ++ r', by rw [hr', hpr, List.append_assoc]⟩)
    obtain ⟨j', hg', -⟩ := key _ (DS.initA hadd)
      (applicable_sound (α_applicable hs c.callee a.fact) hac)
    exact ⟨l1, j', hg'⟩

#print axioms reachD

/-- THE VULNERABILITY THEOREM of the final rule: the fire at the root or a class with the request
    truncated to the static field, sinks by the ordinary mark request, answers only from added
    facts at or below the position, the wide climb, NO answer from above and NO fallback, deep
    mark answers on static premises. Under the construction hypotheses `SWF` and `Program.WF`, a
    concrete flow from a root to a covered sink gives a `vuln` object. -/
theorem vulnD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF) {M : MethodId} {n : Node}
    {l : Loc} {s : PFact} {T : Mark} (hR : Reach X.P X.roots M n l) (hsk : (M, n, s) ∈ X.sinks)
    (hT : s.mark = .conc T) (hsc : s.covers l) : ∃ b, DS X (.vuln M n s b) := by
  obtain ⟨l0, j, hg⟩ := reachD hs hd hwf hR
  have key := strong_ind (α := PFact) (fun j => posBound X - j.path.length)
    (P := fun j => GoodD X M n l0 l j → ∃ b, DS X (.vuln M n s b)) (by
    intro j rec hgj
    cases hgj with
    | mk hj hjc hedge hmark hpos =>
    obtain ⟨f, hf, hdn⟩ := hedge
    rcases check_sound hT hdn hsc with htr | ⟨hrq, hist⟩
    · exact ⟨_, DS.vuln hf hsk htr⟩
    · cases hmark (DS.reqSink hf hsk hrq) with
      | @mk j' t hg' ht =>
      cases hg' with
      | mk _ _ hedge' _ _ =>
      obtain ⟨f', hf', hdn'⟩ := hedge'
      rcases check_sound hT hdn' hsc with htr' | ⟨_, hist'⟩
      · exact ⟨_, DS.vuln hf' hsk htr'⟩
      · exact absurd ht (hist' t))
  exact key j hg

#print axioms vulnD

/-! ## 14. The deep mark answer is needed: `CexClean`

`root: C.s = source(); caller()`, `caller: K(); r = m(); sink(r)`, `K: clean_7(C.u)`,
`m: y = C.s; return y`. Methods `0` (root), `1` (`caller`), `2` (`K`), `3` (`m`). The cleaner removes
the mark 7 at `S.<C>.u` only. The program satisfies the construction hypotheses (`clean_swf`).

`K`'s static root meets the cleaner in the case `part`: it continues as `(S, [], */{}, *∖{7})` and
raises the MARK request `(K, Sroot, 7)`, which climbs to the caller. With the answer on the requested
chain (`Xs`: `deepAns = false`, `answerInit`) the caller and `K` answer it from `(S, <C>.s, $, 7)` with
`(S, [], *, {}, 7)`, whose start is `(S, [], [any], 7)`: a demand fact above the position `<C>.s`
(`shallow_any`), which the static invariant forbids. `K`'s summary of that answer turns the caller's
precise `(S, <C>.s, $, 7)` into `(S, [], [any], 7)` (`shallow_degrades`), and the summary of the static
root excludes 7. So the mark 7 reaches `m` only in `[any]` facts above `<C>.s`: `m` answers its position
request only from `(S, <C>.s, */{}, *∖{7})`, the climb asks the caller again, there is no fallback,
and the vulnerability is lost (`shallow_misses`), although the construction hypotheses hold
(`clean_swf_s`). With the DEEP answer (`Xd`, the final rule) the request is answered by
`(S, <C>.s, $, 7)` itself, `K`'s summary keeps it (the cleaner is apart), `m` answers from it, and the
vulnerability is reported in the NORMAL layer (`deep_vuln_normal`). `D` reports it in the demand
layer (`clean_D_finds`). -/

/-! ### 14.0 Shared lemmas for the construction hypotheses of concrete programs -/

theorem prefix_nil {q r : List Acc} (hne : r ≠ []) (h : ([] : List Acc) = q ++ r) : False := by
  cases r with
  | nil => exact hne rfl
  | cons x rs => cases q <;> cases h

theorem prefix_one {a : Acc} {q r : List Acc} (hne : r ≠ []) (h : [a] = q ++ r) : q = [] := by
  cases q with
  | nil => rfl
  | cons y q' => exact (prefix_nil hne (List.cons.inj h).2).elim

theorem prefix_two {a b : Acc} {q r : List Acc} (hne : r ≠ []) (h : [a, b] = q ++ r) :
    q = [] ∨ q = [a] := by
  cases q with
  | nil => exact .inl rfl
  | cons y q' =>
    have h2 := List.cons.inj h
    rw [prefix_one hne h2.2, h2.1]
    exact .inr rfl

/-- The number of counted accessors of a path. -/
def countC (counted : Acc → Bool) : List Acc → Nat
  | [] => 0
  | a :: as => (if counted a then 1 else 0) + countC counted as

theorem cutPath_count {counted : Acc → Bool} :
    ∀ {n : Nat} {q r : List Acc}, cutPath counted n q = some r → countC counted r = n
  | _, [], _, h => by cases h
  | n, a :: as, r, h => by
    cases n with
    | zero =>
      have e : cutPath counted 0 (a :: as) =
          if counted a then some [] else (cutPath counted 0 as).map (a :: ·) := rfl
      rw [e] at h
      cases ha : counted a with
      | true =>
        rw [if_pos ha] at h
        cases h
        rfl
      | false =>
        rw [if_neg (by rw [ha]; exact Bool.false_ne_true)] at h
        cases hc : cutPath counted 0 as with
        | none => rw [hc] at h; cases h
        | some r' =>
          rw [hc] at h
          cases h
          show (if counted a then 1 else 0) + countC counted r' = 0
          rw [ha, if_neg Bool.false_ne_true, Nat.zero_add, cutPath_count hc]
    | succ m =>
      have e : cutPath counted (m + 1) (a :: as) =
          if counted a then (cutPath counted m as).map (a :: ·)
          else (cutPath counted (m + 1) as).map (a :: ·) := rfl
      rw [e] at h
      cases ha : counted a with
      | true =>
        rw [if_pos ha] at h
        cases hc : cutPath counted m as with
        | none => rw [hc] at h; cases h
        | some r' =>
          rw [hc] at h
          cases h
          show (if counted a then 1 else 0) + countC counted r' = m + 1
          rw [ha, if_pos rfl, cutPath_count hc, Nat.add_comm]
      | false =>
        rw [if_neg (by rw [ha]; exact Bool.false_ne_true)] at h
        cases hc : cutPath counted (m + 1) as with
        | none => rw [hc] at h; cases h
        | some r' =>
          rw [hc] at h
          cases h
          show (if counted a then 1 else 0) + countC counted r' = m + 1
          rw [ha, if_neg Bool.false_ne_true, Nat.zero_add, cutPath_count hc]

/-- A decidable form of the hypothesis `SWF.ss` on one micro edge. -/
def ssB (e : MicroEdge) : Bool :=
  decide (e.1.path = e.2.path) && e.1.kind.isStar && e.2.kind.isStar && decide (e.1.mark = .star) &&
    decide (e.2.mark = .star)

theorem ssB_sound {sB : Base} {e : MicroEdge} (h : ssB e = true) (h1 : e.1.base = sB)
    (h2 : e.2.base = sB) :
    ∃ q E1 E2, e.1 = ⟨sB, q, .star E1, .star⟩ ∧ e.2 = ⟨sB, q, .star E2, .star⟩ := by
  obtain ⟨⟨b1, p1, k1, m1⟩, ⟨b2, p2, k2, m2⟩⟩ := e
  unfold ssB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp, hk1⟩, hk2⟩, hm1⟩, hm2⟩ := h
  have h1' : b1 = sB := h1
  have h2' : b2 = sB := h2
  have hp' : p1 = p2 := hp
  have hm1' : m1 = .star := hm1
  have hm2' : m2 = .star := hm2
  subst h1' h2' hp' hm1' hm2'
  cases k1 with
  | star E1 =>
    cases k2 with
    | star E2 => exact ⟨p1, E1, E2, rfl, rfl⟩
    | any => cases hk2
    | exact => cases hk2
  | any => cases hk1
  | exact => cases hk1

theorem bind_sound {sB : Base} {e : MicroEdge} (h : ssB e = true) (hp : e.1.path = [])
    (h1 : e.1.base = sB) (h2 : e.2.base = sB) :
    ∃ E1 E2, e.1 = ⟨sB, [], .star E1, .star⟩ ∧ e.2 = ⟨sB, [], .star E2, .star⟩ := by
  obtain ⟨q, E1, E2, he1, he2⟩ := ssB_sound h h1 h2
  rw [he1] at hp
  have hq : q = [] := hp
  subst hq
  exact ⟨E1, E2, he1, he2⟩

namespace CexClean

def S : Base := 1
def rB : Base := 3
def yB : Base := 4
def retB : Base := 5
def C : Acc := 10
def sA : Acc := 12
def uA : Acc := 13
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- The tainted static field `(S, <C>.s, $, 7)`. -/
def ws : PFact := ⟨S, [C, sA], .exact, .conc T⟩
def wsF : AFact := ⟨ws, false⟩
def As : PFact := sAns S [C, sA]
def AsF : AFact := ⟨As, false⟩
/-- `K`'s static root after the cleaner: `(S, [], */{}, *∖{7})`. -/
def STF : AFact := ⟨⟨S, [], .star Excl.empty, .starEx [T]⟩, false⟩
/-- root: `C.s = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, ws)]⟩
/-- K: the cleaner of the mark 7 at `S.<C>.u`. -/
def clU : Cleaner := ⟨S, [C, uA], .atAndBelow, some T⟩
/-- m: `y = C.s`, `return y`. -/
def rd : Stmt := readStmt S yB [C, sA]
def readS : MicroEdge := (pat S [C, sA], pat yB [])
def rt : Stmt := ⟨[retB, yB], [(pat yB [], pat yB []), (pat yB [], pat retB [])]⟩
def retE : MicroEdge := (pat retB [], pat rB [])
def cC : Call := ⟨1, [S], [bindS], [bindS]⟩
def cK : Call := ⟨2, [S], [bindS], [bindS]⟩
def cm : Call := ⟨3, [S, rB], [bindS], [bindS, retE]⟩
def exitOf : MethodId → Node
  | 2 => 1
  | _ => 2
def prog : Program :=
  ⟨fun _ => 0, exitOf,
   [(0, 0, .stmt src, 1), (0, 1, .call cC, 2),
    (1, 0, .call cK, 1), (1, 1, .call cm, 2),
    (2, 0, .clean clU, 1),
    (3, 0, .stmt rd, 1), (3, 1, .stmt rt, 2)]⟩
def sinkPat : PFact := ⟨rB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(1, 2, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- The final rule. -/
def Xd : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩
/-- The same with the mark answer on the requested chain. -/
def Xs : SCtx := { Xd with deepAns := false }

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cC : (0, 1, Instr.call cC, 2) ∈ prog.edges := by simp [prog]
theorem m_cK : (1, 0, Instr.call cK, 1) ∈ prog.edges := by simp [prog]
theorem m_cm : (1, 1, Instr.call cm, 2) ∈ prog.edges := by simp [prog]
theorem m_clU : (2, 0, Instr.clean clU, 1) ∈ prog.edges := by simp [prog]
theorem m_rd : (3, 0, Instr.stmt rd, 1) ∈ prog.edges := by simp [prog]
theorem m_rt : (3, 1, Instr.stmt rt, 2) ∈ prog.edges := by simp [prog]
theorem m_sink : (1, 2, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesK {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cC ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .call cK ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .call cm ∧ n' = 2) ∨
    (M = 2 ∧ n = 0 ∧ ins = .clean clU ∧ n' = 1) ∨
    (M = 3 ∧ n = 0 ∧ ins = .stmt rd ∧ n' = 1) ∨ (M = 3 ∧ n = 1 ∧ ins = .stmt rt ∧ n' = 2) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- The static positions of the program are `[]` and `<C>.s`. -/
theorem posIn_cases {X : SCtx} (hP : X.P = prog) (hk : X.sinks = sinks) (hb : X.sB = S)
    {p : List Acc} (h : PosIn X p) : p = [] ∨ p = [C, sA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rw [hP] at hE
    rw [hb] at heb
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert heb <;> revert e <;> decide
  · rw [hk] at hs
    rw [hb] at hsb
    have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    exact absurd hsb (by decide)

theorem abovePos_cases {X : SCtx} (hP : X.P = prog) (hk : X.sinks = sinks) (hb : X.sB = S)
    {q : List Acc} (h : AbovePos X q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP', hne, hPr⟩ := h
  cases r with
  | nil => exact absurd rfl hne
  | cons x rs =>
    rcases posIn_cases hP hk hb hP' with rfl | rfl
    · exfalso
      cases q <;> cases hPr
    · cases q with
      | nil => exact .inl rfl
      | cons y q' =>
        cases q' with
        | nil =>
          have hy := (List.cons.inj hPr).1
          exact .inr (by rw [← hy])
        | cons z q'' =>
          exfalso
          have h3 := (List.cons.inj (List.cons.inj hPr).2).2
          cases q'' <;> cases h3

/-- The program satisfies the construction hypotheses. -/
theorem clean_swf : SWF Xd where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd h1 (by decide)
      · rw [List.mem_singleton.mp he'] at h1; exact absurd h1 (by decide)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact .inl ⟨[], .set [], .set [], rfl, rfl⟩
      · rw [List.mem_singleton.mp he'] at h2; exact absurd h2 (by decide)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd h1 (by decide)
      · rw [List.mem_singleton.mp he'] at h1; exact absurd h1 (by decide)
  write := by
    intro M n s n' hE e he h1 h2 hab
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd h2 (by decide)
      · rw [List.mem_singleton.mp he'] at hab
        rcases abovePos_cases rfl rfl rfl hab with h | h <;> exact absurd h (by decide)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd h1 (by decide)
      · rw [List.mem_singleton.mp he'] at h1; exact absurd h1 (by decide)
    · rcases List.mem_cons.mp he with rfl | he'
      · exact absurd h2 (by decide)
      · rw [List.mem_singleton.mp he'] at h2; exact absurd h2 (by decide)
  toC := by
    intro M n c n' hE e he hb
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> rw [List.mem_singleton.mp he] <;>
      exact ⟨.set [], .set [], rfl, rfl⟩
  fromC := by
    intro M n c n' hE e he hb
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
    · rw [List.mem_singleton.mp he]; exact ⟨.set [], .set [], rfl, rfl⟩
    · rw [List.mem_singleton.mp he]; exact ⟨.set [], .set [], rfl, rfl⟩
    · rcases List.mem_cons.mp he with rfl | he'
      · exact ⟨.set [], .set [], rfl, rfl⟩
      · rw [List.mem_singleton.mp he'] at hb
        rcases hb with hb | hb <;> exact absurd hb (by decide)
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases rfl rfl rfl hab with rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesK hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
    exact ⟨T, rfl⟩
  alpha := rfl

#print axioms clean_swf

/-! ### The facts of the counterexample -/

/-- The shallow answer to the mark request `(K, Sroot, 7)`: `(S, [], *, {}, 7)`. -/
def A7 : PFact := ⟨S, [], .star Excl.empty, .conc T⟩
/-- Its start: `(S, [], [any], 7)`, demand. -/
def A7F : AFact := ⟨⟨S, [], .any, .conc T⟩, true⟩
/-- `(S, <C>.s, *, {}, *∖{7})`. -/
def AsX : AFact := ⟨⟨S, [C, sA], .star Excl.empty, .starEx [T]⟩, false⟩
def rX : AFact := ⟨⟨rB, [], .star Excl.empty, .starEx [T]⟩, false⟩
def yF : AFact := ⟨pat yB [], false⟩
def retF : AFact := ⟨pat retB [], false⟩
def retT : AFact := ⟨⟨retB, [], .exact, .conc T⟩, false⟩
def rT : AFact := ⟨⟨rB, [], .exact, .conc T⟩, false⟩

/-- The concrete flow: `S.<C>.s` → (through `K`, whose cleaner is apart) → `m` reads it → `r`. -/
theorem clean_reach : Reach prog [0] 1 2 ⟨rB, [], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, sA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, ws), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have k1 : Flow prog 2 ⟨S, [C, sA], T⟩ 1 ⟨S, [C, sA], T⟩ :=
    Flow.clean (Flow.start 2 ⟨S, [C, sA], T⟩) m_clU (by decide)
  have c1 : Flow prog 1 ⟨S, [C, sA], T⟩ 1 ⟨S, [C, sA], T⟩ :=
    Flow.call (Flow.start 1 ⟨S, [C, sA], T⟩) m_cK List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩ k1
      List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩
  have mm1 : Flow prog 3 ⟨S, [C, sA], T⟩ 1 ⟨yB, [], T⟩ :=
    Flow.step (Flow.start 3 ⟨S, [C, sA], T⟩) m_rd
      (.inr ⟨readS, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have mm2 : Flow prog 3 ⟨S, [C, sA], T⟩ 2 ⟨retB, [], T⟩ :=
    Flow.step mm1 m_rt
      (.inr ⟨(pat yB [], pat retB []), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have c2 : Flow prog 1 ⟨S, [C, sA], T⟩ 2 ⟨rB, [], T⟩ :=
    Flow.call c1 m_cm List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩ mm2
      (List.mem_cons_of_mem _ List.mem_cons_self)
      ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
  exact Reach.down (Reach.root List.mem_cons_self h0) m_cC List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, sA], [C, sA], rfl, rfl, rfl, rfl, rfl⟩ c2

theorem clean_covers : sinkPat.covers ⟨rB, [], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms clean_reach

/-- The construction hypotheses hold for the shallow variant too (they do not read `deepAns`). -/
theorem clean_swf_s : SWF Xs :=
  { base := clean_swf.base, ss := clean_swf.ss, write := clean_swf.write, toC := clean_swf.toC,
    fromC := clean_swf.fromC, cut := clean_swf.cut, clean := clean_swf.clean,
    alpha := clean_swf.alpha }

/-! ### The design reports it, in the NORMAL layer -/

theorem x_start : DS Xd (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem x_src : DS Xd (.edge 0 zeroFact 1 wsF) := DS.step x_start m_src (by decide)
theorem x_aC : DS Xd (.added 1 ws) := DS.added (a := wsF) x_src m_cC List.mem_cons_self (by decide)
theorem x_jC : DS Xd (.init 1 Sroot) := by
  have h : Xd.α 1 ws = Sroot := by decide
  exact h ▸ DS.initA x_aC
theorem x_eC0 : DS Xd (.edge 1 Sroot 0 SrootF) := DS.start x_jC
theorem x_aK : DS Xd (.added 2 Sroot) :=
  DS.added (a := SrootF) x_eC0 m_cK List.mem_cons_self (by decide)
theorem x_jK : DS Xd (.init 2 Sroot) := by
  have h : Xd.α 2 Sroot = Sroot := by decide
  exact h ▸ DS.initA x_aK
theorem x_eK0 : DS Xd (.edge 2 Sroot 0 SrootF) := DS.start x_jK
/-- The cleaner on `K`'s static root (case `part`) raises the mark request for 7. -/
theorem x_rK : DS Xd (.req 2 Sroot T) := DS.reqClean x_eK0 m_clU (by decide)
theorem x_rC : DS Xd (.req 1 Sroot T) :=
  DS.reqUp (a := SrootF) (e := bindS) x_rK x_eC0 m_cK rfl List.mem_cons_self (by decide) (by decide)
    (by decide)
/-- THE DEEP ANSWER: the root's fact answers at its own position, `(S, <C>.s, $, 7)`. -/
theorem x_jCw : DS Xd (.init 1 ws) := by
  have h : Xd.ansInit Sroot ws T = ws := by decide
  exact h ▸ DS.answer x_rC x_aC rfl (by decide)
theorem x_eCw0 : DS Xd (.edge 1 ws 0 wsF) := DS.start x_jCw
theorem x_aKw : DS Xd (.added 2 ws) :=
  DS.added (a := wsF) x_eCw0 m_cK List.mem_cons_self (by decide)
theorem x_jKw : DS Xd (.init 2 ws) := by
  have h : Xd.ansInit Sroot ws T = ws := by decide
  exact h ▸ DS.answer x_rK x_aKw rfl (by decide)
theorem x_eKw0 : DS Xd (.edge 2 ws 0 wsF) := DS.start x_jKw
/-- The cleaner at `S.<C>.u` is apart from `S.<C>.s`. -/
theorem x_eKw1 : DS Xd (.edge 2 ws 1 wsF) := DS.clean x_eKw0 m_clU (by decide)
/-- `K`'s summary keeps the precise fact. -/
theorem x_eCw1 : DS Xd (.edge 1 ws 1 wsF) :=
  DS.ret (a := wsF) (r := wsF) (r' := wsF) (e2 := bindS) x_eCw0 m_cK List.mem_cons_self (by decide)
    x_jKw (by decide) x_eKw1 (by decide) List.mem_cons_self (by decide)
theorem x_aMw : DS Xd (.added 3 ws) :=
  DS.added (a := wsF) x_eCw1 m_cm List.mem_cons_self (by decide)
theorem x_jM : DS Xd (.init 3 Sroot) := by
  have h : Xd.α 3 ws = Sroot := by decide
  exact h ▸ DS.initA x_aMw
theorem x_eM0 : DS Xd (.edge 3 Sroot 0 SrootF) := DS.start x_jM
/-- RAISE in `m`. -/
theorem x_sreqM : DS Xd (.sreq 3 Sroot [C, sA]) :=
  DS.sreqStmt (e := readS) x_eM0 m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER in `m` from its added fact at the position. -/
theorem x_jMA : DS Xd (.init 3 As) := DS.sanswer x_sreqM x_aMw (by decide)
theorem x_eMA0 : DS Xd (.edge 3 As 0 AsF) := DS.start x_jMA
theorem x_eMA1 : DS Xd (.edge 3 As 1 yF) := DS.step x_eMA0 m_rd (by decide)
theorem x_eMA2 : DS Xd (.edge 3 As 2 retF) := DS.step x_eMA1 m_rt (by decide)
theorem x_eCw2 : DS Xd (.edge 1 ws 2 rT) :=
  DS.ret (a := wsF) (r := retT) (r' := rT) (e2 := retE) x_eCw1 m_cm List.mem_cons_self (by decide)
    x_jMA (by decide) x_eMA2 (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- THE DESIGN REPORTS THE VULNERABILITY IN THE NORMAL LAYER. -/
theorem deep_vuln_normal : DS Xd (.vuln 1 2 sinkPat false) := DS.vuln x_eCw2 m_sink (by decide)

#print axioms deep_vuln_normal

/-- The same from the soundness theorem of the final rule. -/
theorem deep_finds : ∃ b, DS Xd (.vuln 1 2 sinkPat b) :=
  vulnD clean_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf clean_reach m_sink rfl clean_covers

/-- `D` reports it (the base vulnerability theorem). -/
theorem clean_D_finds : ∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 2 sinkPat b) :=
  Coverage.vuln_found_policy prog counted 2 sinks [0] wf (fun _ => []) clean_reach m_sink rfl
    clean_covers

/-! ### The shallow answer makes `(S, [], [any], 7)` and degrades the precise fact -/

theorem s_start : DS Xs (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem s_src : DS Xs (.edge 0 zeroFact 1 wsF) := DS.step s_start m_src (by decide)
theorem s_aC : DS Xs (.added 1 ws) := DS.added (a := wsF) s_src m_cC List.mem_cons_self (by decide)
theorem s_jC : DS Xs (.init 1 Sroot) := by
  have h : Xs.α 1 ws = Sroot := by decide
  exact h ▸ DS.initA s_aC
theorem s_eC0 : DS Xs (.edge 1 Sroot 0 SrootF) := DS.start s_jC
theorem s_aK : DS Xs (.added 2 Sroot) :=
  DS.added (a := SrootF) s_eC0 m_cK List.mem_cons_self (by decide)
theorem s_jK : DS Xs (.init 2 Sroot) := by
  have h : Xs.α 2 Sroot = Sroot := by decide
  exact h ▸ DS.initA s_aK
theorem s_eK0 : DS Xs (.edge 2 Sroot 0 SrootF) := DS.start s_jK
theorem s_eK1 : DS Xs (.edge 2 Sroot 1 STF) := DS.clean s_eK0 m_clU (by decide)
theorem s_rK : DS Xs (.req 2 Sroot T) := DS.reqClean s_eK0 m_clU (by decide)
theorem s_rC : DS Xs (.req 1 Sroot T) :=
  DS.reqUp (a := SrootF) (e := bindS) s_rK s_eC0 m_cK rfl List.mem_cons_self (by decide) (by decide)
    (by decide)
/-- The shallow answer on the requested chain: `(S, [], *, {}, 7)`. -/
theorem s_jCA : DS Xs (.init 1 A7) := by
  have h : Xs.ansInit Sroot ws T = A7 := by decide
  exact h ▸ DS.answer s_rC s_aC rfl (by decide)
/-- Its start is `(S, [], [any], 7)`: a non-exact static fact above the position `<C>.s`. -/
theorem shallow_any : DS Xs (.edge 1 A7 0 A7F) := DS.start s_jCA

theorem shallow_any_above : AboveNE Xs A7F.fact :=
  ⟨rfl, ⟨[C, sA], [C, sA], .inl ⟨3, 0, rd, 1, readS, m_rd,
    List.mem_cons_of_mem _ List.mem_cons_self, rfl, rfl⟩, by decide, rfl⟩, by decide⟩

theorem s_eC1 : DS Xs (.edge 1 Sroot 1 STF) :=
  DS.ret (a := SrootF) (r := STF) (r' := STF) (e2 := bindS) s_eC0 m_cK List.mem_cons_self
    (by decide) s_jK (by decide) s_eK1 (by decide) List.mem_cons_self (by decide)
theorem s_aM : DS Xs (.added 3 STF.fact) :=
  DS.added (a := STF) s_eC1 m_cm List.mem_cons_self (by decide)
theorem s_jM : DS Xs (.init 3 Sroot) := by
  have h : Xs.α 3 STF.fact = Sroot := by decide
  exact h ▸ DS.initA s_aM
theorem s_eM0 : DS Xs (.edge 3 Sroot 0 SrootF) := DS.start s_jM
theorem s_sreqM : DS Xs (.sreq 3 Sroot [C, sA]) :=
  DS.sreqStmt (e := readS) s_eM0 m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem s_sreqC : DS Xs (.sreq 1 Sroot [C, sA]) :=
  DS.sreqUp (a := STF) (e := bindS) s_sreqM s_eC1 m_cm rfl List.mem_cons_self (by decide)
    (by decide)
theorem s_jCs : DS Xs (.init 1 As) := DS.sanswer s_sreqC s_aC (by decide)
theorem s_eCs0 : DS Xs (.edge 1 As 0 AsF) := DS.start s_jCs
theorem s_rCs : DS Xs (.req 1 As T) :=
  DS.reqUp (a := AsF) (e := bindS) s_rK s_eCs0 m_cK rfl List.mem_cons_self (by decide) (by decide)
    (by decide)
theorem s_jCw : DS Xs (.init 1 ws) := by
  have h : Xs.ansInit As ws T = ws := by decide
  exact h ▸ DS.answer s_rCs s_aC rfl (by decide)
theorem s_eCw0 : DS Xs (.edge 1 ws 0 wsF) := DS.start s_jCw
theorem s_aKw : DS Xs (.added 2 ws) :=
  DS.added (a := wsF) s_eCw0 m_cK List.mem_cons_self (by decide)
theorem s_jKA : DS Xs (.init 2 A7) := by
  have h : Xs.ansInit Sroot ws T = A7 := by decide
  exact h ▸ DS.answer s_rK s_aKw rfl (by decide)
theorem s_eKA0 : DS Xs (.edge 2 A7 0 A7F) := DS.start s_jKA
theorem s_eKA1 : DS Xs (.edge 2 A7 1 A7F) := DS.clean s_eKA0 m_clU (by decide)
/-- `K` TURNS THE CALLER'S PRECISE `(S, <C>.s, $, 7)` INTO `(S, [], [any], 7)`. -/
theorem shallow_degrades : DS Xs (.edge 1 ws 1 A7F) :=
  DS.ret (a := wsF) (r := A7F) (r' := A7F) (e2 := bindS) s_eCw0 m_cK List.mem_cons_self
    (by decide) s_jKA (by decide) s_eKA1 (by decide) List.mem_cons_self (by decide)

#print axioms shallow_degrades

/-! ### The shallow answer misses the vulnerability

An invariant of `DS Xs`. The caller's initial facts are the static root, `A7`, `(S, <C>.s, *)` and
`(S, <C>.s, $, 7)`; `K`'s are the static root and `A7`; `m`'s are the static root and
`(S, <C>.s, *)`. The only fact on `r` is `(r, *∖{7})` (the `7` part was split off by the cleaner and
went into `A7`, i.e. `[any]`), so the sink neither triggers nor asks. -/

def InitOK : MethodId → PFact → Prop
  | 0, i => i = zeroFact
  | 1, i => i = Sroot ∨ i = A7 ∨ i = As ∨ i = ws
  | 2, i => i = Sroot ∨ i = A7
  | 3, i => i = Sroot ∨ i = As
  | _, _ => True

def CallerOK : PFact → Node → AFact → Prop
  | i, 0, f => (i = Sroot ∧ f = SrootF) ∨ (i = A7 ∧ f = A7F) ∨ (i = As ∧ f = AsF) ∨ (i = ws ∧ f = wsF)
  | i, 1, f => (i = Sroot ∧ f = STF) ∨ ((i = A7 ∨ i = ws) ∧ f = A7F) ∨ (i = As ∧ f = AsX)
  | i, _, f => (i = Sroot ∧ f = STF) ∨ ((i = A7 ∨ i = ws) ∧ f = A7F) ∨ (i = As ∧ (f = AsX ∨ f = rX))

def EdgeOK : MethodId → PFact → Node → AFact → Prop
  | 0, i, 0, f => i = zeroFact ∧ f = zfF
  | 0, i, 1, f => i = zeroFact ∧ (f = zfF ∨ f = wsF)
  | 0, i, _, _ => i = zeroFact
  | 1, i, n, f => CallerOK i n f
  | 2, i, 0, f => (i = Sroot ∧ f = SrootF) ∨ (i = A7 ∧ f = A7F)
  | 2, i, _, f => (i = Sroot ∧ f = STF) ∨ (i = A7 ∧ f = A7F)
  | 3, i, _, f => (i = Sroot ∧ f = SrootF) ∨ (i = As ∧ (f = AsF ∨ f = yF ∨ f = retF))
  | _, _, _, _ => True

def AddedOK : MethodId → PFact → Prop
  | 0, _ => False
  | 1, a => a = ws
  | 2, a => a = Sroot ∨ a = A7F.fact ∨ a = As ∨ a = ws
  | 3, a => a.base = S
  | _, _ => True

def UInv : SObj → Prop
  | .init M i => InitOK M i
  | .edge M i n f => EdgeOK M i n f
  | .added M a => AddedOK M a
  | .req M i t => (M = 2 ∧ i = Sroot ∧ t = T) ∨ (M = 1 ∧ (i = Sroot ∨ i = As) ∧ t = T)
  | .sreq M i p => (M = 3 ∧ i = Sroot ∧ p = [C, sA]) ∨ (M = 1 ∧ p = [C, sA])
  | .vuln _ _ _ _ => False

theorem α1_S {m : MethodId} {a : PFact} (hb : a.base = S) : α1 m a = Sroot := by
  unfold α1 policy
  split
  · rename_i hz
    rw [hz] at hb
    exact absurd hb (by decide)
  · split
    · rename_i h
      cases h
    · obtain ⟨b, p, k, mk⟩ := a
      have hb' : b = S := hb
      subst hb'
      rfl

theorem sink_off {i : PFact} {f : AFact} (hb : f.fact.base ≠ rB) : check i f sinkPat = .none := by
  cases h : check i f sinkPat with
  | none => rfl
  | triggered =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    exact absurd (Example.overlap_base ho) hb
  | request t =>
    have ho := check_overlap_of (T := T) rfl (by rw [h]; exact Check.noConfusion)
    exact absurd (Example.overlap_base ho) hb

theorem sink_none {i : PFact} {f : AFact} (h : CallerOK i 2 f) : check i f sinkPat = .none := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · exact sink_off (by decide)
  · exact sink_off (by decide)
  · exact sink_off (by decide)
  · decide

theorem uInv_all {o : SObj} (h : DS Xs o) : UInv o := by
  induction h with
  | root hM =>
    rw [List.mem_singleton.mp hM]
    exact (rfl : zeroFact = zeroFact)
  | @start M i _ ih =>
    show EdgeOK M i 0 (startFact i)
    rcases M with _ | _ | _ | _ | M
    · have hi : i = zeroFact := ih
      subst hi
      exact ⟨rfl, rfl⟩
    · rcases (ih : i = Sroot ∨ i = A7 ∨ i = As ∨ i = ws) with rfl | rfl | rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
      · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    · rcases (ih : i = Sroot ∨ i = A7) with rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨rfl, rfl⟩
    · rcases (ih : i = Sroot ∨ i = As) with rfl | rfl
      · exact .inl ⟨rfl, rfl⟩
      · exact .inr ⟨rfl, .inl rfl⟩
    · trivial
  | @step M i n f n' s f' _ he hf ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have key : ∀ x, x ∈ (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB zeroFact zfF) src) zfF).facts →
          x = zfF ∨ x = wsF := by decide
      exact ⟨rfl, key f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = As ∧ (f = AsF ∨ f = yF ∨ f = retF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, hf0⟩
      · have key : ∀ x, x ∈ (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB Sroot SrootF) rd) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · have key : ∀ g, g ∈ [AsF, yF, retF] →
            ∀ x, x ∈ (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB As g) rd) g).facts →
            x = AsF ∨ x = yF ∨ x = retF := by decide
        exact .inr ⟨rfl, key f (by rcases hf0 with rfl | rfl | rfl <;> decide) f' hf⟩
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = As ∧ (f = AsF ∨ f = yF ∨ f = retF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, hf0⟩
      · have key : ∀ x, x ∈ (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB Sroot SrootF) rt) SrootF).facts →
            x = SrootF := by decide
        exact .inl ⟨rfl, key f' hf⟩
      · have key : ∀ g, g ∈ [AsF, yF, retF] →
            ∀ x, x ∈ (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB As g) rt) g).facts →
            x = AsF ∨ x = yF ∨ x = retF := by decide
        exact .inr ⟨rfl, key f (by rcases hf0 with rfl | rfl | rfl <;> decide) f' hf⟩
  | @reqStmt M i n f n' s t _ he hq ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have hr : (transfer Xs.counted Xs.FL (sKeepP (Xs.fireB zeroFact zfF) src) zfF).reqs = [] := by
        decide
      rw [hr] at hq
      cases hq
    all_goals
      rw [transfer_reqs_star (sKeep_star (by decide))] at hq
      cases hq
  | @sreqStmt M i n f n' s e _ he hes hfire ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, rfl⟩ := (ih : i = zeroFact ∧ f = zfF)
      have key : ∀ e, e ∈ src.edges → Xs.fireB zeroFact zfF e = false := by decide
      rw [key e hes] at hfire
      cases hfire
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = As ∧ (f = AsF ∨ f = yF ∨ f = retF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, hf0⟩
      · have key : ∀ e, e ∈ rd.edges → Xs.fireB Sroot SrootF e = true → e.1.path = [C, sA] := by
          decide
        refine .inl ⟨rfl, rfl, ?_⟩
        rw [reqP_gen (X := Xs) rfl, key e hes hfire]
        all_goals rfl
      · have key : ∀ g, g ∈ [AsF, yF, retF] → ∀ e, e ∈ rd.edges → Xs.fireB As g e = false := by
          decide
        rw [key f (by rcases hf0 with rfl | rfl | rfl <;> decide) e hes] at hfire
        cases hfire
    · rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = As ∧ (f = AsF ∨ f = yF ∨ f = retF))) with
        ⟨rfl, rfl⟩ | ⟨rfl, hf0⟩
      · have key : ∀ e, e ∈ rt.edges → Xs.fireB Sroot SrootF e = false := by decide
        rw [key e hes] at hfire
        cases hfire
      · have key : ∀ g, g ∈ [AsF, yF, retF] → ∀ e, e ∈ rt.edges → Xs.fireB As g e = false := by
          decide
        rw [key f (by rcases hf0 with rfl | rfl | rfl <;> decide) e hes] at hfire
        cases hfire
  | @pass M i n f n' c _ he hm ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ih : i = zeroFact ∧ (f = zfF ∨ f = wsF)).1
    · rcases (ih : CallerOK i 0 f) with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact absurd hm (by decide)
    · rcases (ih : CallerOK i 1 f) with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        exact absurd hm (by decide)
  | @added M i n f n' c e a _ he he1 ha ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨-, hf⟩ := (ih : i = zeroFact ∧ (f = zfF ∨ f = wsF))
      rw [List.mem_singleton.mp he1] at ha
      show a.fact = ws
      have key : ∀ g, g ∈ [zfF, wsF] → ∀ x, x ∈ (applyEdge g bindS.1 bindS.2).facts → x.fact = ws := by
        decide
      exact key f (by rcases hf with rfl | rfl <;> decide) a ha
    · rw [List.mem_singleton.mp he1] at ha
      have key : ∀ g, g ∈ [SrootF, A7F, AsF, wsF] → ∀ x, x ∈ (applyEdge g bindS.1 bindS.2).facts →
          x.fact = Sroot ∨ x.fact = A7F.fact ∨ x.fact = As ∨ x.fact = ws := by decide
      exact key f (by rcases (ih : CallerOK i 0 f) with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
        decide) a ha
    · rw [List.mem_singleton.mp he1] at ha
      exact applyEdge_base ha
  | @initA m a _ ih =>
    rcases m with _ | _ | _ | _ | m
    · exact (ih : False).elim
    · have ha : a = ws := ih
      subst ha
      exact .inl (α1_S (m := 1) (a := ws) rfl)
    · rcases (ih : a = Sroot ∨ a = A7F.fact ∨ a = As ∨ a = ws) with rfl | rfl | rfl | rfl <;>
        exact .inl (by decide)
    · exact .inl (α1_S (m := 3) ih)
    · trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · exact (ihf : i = zeroFact ∧ (f = zfF ∨ f = wsF)).1
    · -- the call of `K`
      rw [List.mem_singleton.mp he1] at ha
      have hjg : (j, g) ∈ [(Sroot, STF), (A7, A7F)] := by
        rcases (ihg : (j = Sroot ∧ g = STF) ∨ (j = A7 ∧ g = A7F)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          decide
      rcases (ihf : CallerOK i 0 f) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have key : ∀ jg, jg ∈ [(Sroot, STF), (A7, A7F)] →
            ∀ a, a ∈ (applyEdge SrootF bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = STF := by decide
        exact .inl ⟨rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩
      · have key : ∀ jg, jg ∈ [(Sroot, STF), (A7, A7F)] →
            ∀ a, a ∈ (applyEdge A7F bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = A7F := by decide
        exact .inr (.inl ⟨.inl rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩)
      · have key : ∀ jg, jg ∈ [(Sroot, STF), (A7, A7F)] →
            ∀ a, a ∈ (applyEdge AsF bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = AsX := by decide
        exact .inr (.inr ⟨rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩)
      · have key : ∀ jg, jg ∈ [(Sroot, STF), (A7, A7F)] →
            ∀ a, a ∈ (applyEdge wsF bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cK.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = A7F := by decide
        exact .inr (.inl ⟨.inr rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩)
    · -- the call of `m`
      rw [List.mem_singleton.mp he1] at ha
      have hjg : (j, g) ∈ [(Sroot, SrootF), (As, AsF), (As, yF), (As, retF)] := by
        rcases (ihg : (j = Sroot ∧ g = SrootF) ∨ (j = As ∧ (g = AsF ∨ g = yF ∨ g = retF))) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;> decide
      rcases (ihf : CallerOK i 1 f) with ⟨rfl, rfl⟩ | ⟨hi, rfl⟩ | ⟨rfl, rfl⟩
      · have key : ∀ jg, jg ∈ [(Sroot, SrootF), (As, AsF), (As, yF), (As, retF)] →
            ∀ a, a ∈ (applyEdge STF bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cm.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = STF := by decide
        exact .inl ⟨rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩
      · have key : ∀ jg, jg ∈ [(Sroot, SrootF), (As, AsF), (As, yF), (As, retF)] →
            ∀ a, a ∈ (applyEdge A7F bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cm.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts → limitF Xs.counted Xs.FL r' = A7F := by decide
        exact .inr (.inl ⟨hi, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩)
      · have key : ∀ jg, jg ∈ [(Sroot, SrootF), (As, AsF), (As, yF), (As, retF)] →
            ∀ a, a ∈ (applyEdge AsX bindS.1 bindS.2).facts → applicable jg.1 a.fact = true →
            ∀ r, r ∈ (applySummary a jg.1 jg.2).facts → ∀ e2, e2 ∈ cm.fromCallee →
            ∀ r', r' ∈ (applyEdge r e2.1 e2.2).facts →
            limitF Xs.counted Xs.FL r' = AsX ∨ limitF Xs.counted Xs.FL r' = rX := by decide
        exact .inr (.inr ⟨rfl, key (j, g) hjg a ha hap r hr e2 he2 r' hr'⟩)
  | @sret M i n f n' c e1 a j g r e2 r' _ he he1 ha _ hok _ _ _ _ _ _ _ =>
    have hno : Xs.fbOK i a.fact j = false := rfl
    rw [hno] at hok
    cases hok
  | @reqSink M i n f s t _ hs hc ih =>
    have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_none (ih : CallerOK i 2 f)] at hc
    cases hc
  | @answer M i t a _ _ _ _ ihr iha =>
    rw [ansInit_shallow (X := Xs) rfl]
    rcases (ihr : (M = 2 ∧ i = Sroot ∧ t = T) ∨ (M = 1 ∧ (i = Sroot ∨ i = As) ∧ t = T)) with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, hi, rfl⟩
    · rcases (iha : a = Sroot ∨ a = A7F.fact ∨ a = As ∨ a = ws) with rfl | rfl | rfl | rfl <;>
        exact .inr (by decide)
    · have ha : a = ws := iha
      subst ha
      rcases hi with rfl | rfl
      · exact .inr (.inl (by decide))
      · exact .inr (.inr (.inr (by decide)))
  | @sanswer M i p a _ _ _ ihs _ =>
    rcases (ihs : (M = 3 ∧ i = Sroot ∧ p = [C, sA]) ∨ (M = 1 ∧ p = [C, sA])) with
      ⟨rfl, -, rfl⟩ | ⟨rfl, rfl⟩
    · exact .inr rfl
    · exact .inr (.inr (.inl rfl))
  | @reqUp m j t M ic n f n' c e a _ _ he hc he1 ha hcl _ ihr ihf =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · -- the root's call of the caller: its added fact has a concrete mark
      obtain ⟨-, hf⟩ := (ihf : ic = zeroFact ∧ (f = zfF ∨ f = wsF))
      rw [List.mem_singleton.mp he1] at ha
      rcases (ihr : (m = 2 ∧ j = Sroot ∧ t = T) ∨ (m = 1 ∧ (j = Sroot ∨ j = As) ∧ t = T)) with
        ⟨hm, -, -⟩ | ⟨-, -, rfl⟩
      · exact absurd (hc.trans hm) (by decide)
      · have key : ∀ g, g ∈ [zfF, wsF] → ∀ x, x ∈ (applyEdge g bindS.1 bindS.2).facts →
            climbsB x.fact.mark T = false := by decide
        rw [key f (by rcases hf with rfl | rfl <;> decide) a ha] at hcl
        cases hcl
    · -- the caller's call of `K`
      rcases (ihr : (m = 2 ∧ j = Sroot ∧ t = T) ∨ (m = 1 ∧ (j = Sroot ∨ j = As) ∧ t = T)) with
        ⟨-, -, rfl⟩ | ⟨hm, -, -⟩
      · rw [List.mem_singleton.mp he1] at ha
        rcases (ihf : CallerOK ic 0 f) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, .inl rfl, rfl⟩
        · have key : ∀ x, x ∈ (applyEdge A7F bindS.1 bindS.2).facts → climbsB x.fact.mark T = false := by
            decide
          rw [key a ha] at hcl
          cases hcl
        · exact .inr ⟨rfl, .inr rfl, rfl⟩
        · have key : ∀ x, x ∈ (applyEdge wsF bindS.1 bindS.2).facts → climbsB x.fact.mark T = false := by
            decide
          rw [key a ha] at hcl
          cases hcl
      · exact absurd (hc.trans hm) (by decide)
    · -- the caller's call of `m`: `m` raises no mark request
      rcases (ihr : (m = 2 ∧ j = Sroot ∧ t = T) ∨ (m = 1 ∧ (j = Sroot ∨ j = As) ∧ t = T)) with
        ⟨hm, -, -⟩ | ⟨hm, -, -⟩ <;> exact absurd (hc.trans hm) (by decide)
  | @sreqUp m j p M ic n f n' c e a _ _ he hc he1 ha hcl ihs ihf =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    · obtain ⟨rfl, -⟩ := (ihf : ic = zeroFact ∧ (f = zfF ∨ f = wsF))
      have hno : Xs.climbOK zeroFact a.fact p = false := rfl
      rw [hno] at hcl
      cases hcl
    · rcases (ihs : (m = 3 ∧ j = Sroot ∧ p = [C, sA]) ∨ (m = 1 ∧ p = [C, sA])) with
        ⟨hm, -⟩ | ⟨hm, -⟩ <;> exact absurd (hc.trans hm) (by decide)
    · rcases (ihs : (m = 3 ∧ j = Sroot ∧ p = [C, sA]) ∨ (m = 1 ∧ p = [C, sA])) with
        ⟨-, -, rfl⟩ | ⟨hm, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd (hc.trans hm) (by decide)
  | @vuln M i n f s _ hs hc ih =>
    have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨rfl, rfl, rfl⟩ := hs'
    rw [sink_none (ih : CallerOK i 2 f)] at hc
    cases hc
  | @clean M i n f n' cl f' _ he hf ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = A7 ∧ f = A7F)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have key : ∀ x, x ∈ (cleanRes clU SrootF).facts → x = STF := by decide
      exact .inl ⟨rfl, key f' hf⟩
    · have key : ∀ x, x ∈ (cleanRes clU A7F).facts → x = A7F := by decide
      exact .inr ⟨rfl, key f' hf⟩
  | @reqClean M i n f n' cl t _ he ht ih =>
    rcases edgesK he with ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ |
      ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ | ⟨rfl, rfl, h, rfl⟩ <;> cases h
    rcases (ih : (i = Sroot ∧ f = SrootF) ∨ (i = A7 ∧ f = A7F)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have key : ∀ x, x ∈ (cleanRes clU SrootF).reqs → x = T := by decide
      exact .inl ⟨rfl, rfl, key t ht⟩
    · have key : (cleanRes clU A7F).reqs = [] := by decide
      rw [key] at ht
      cases ht
  | @filt M i n f n' b may _ he _ _ =>
    rcases edgesK he with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- THE SHALLOW MARK ANSWER LOSES THE FLOW: no `vuln` object. -/
theorem shallow_misses {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    ¬ DS Xs (.vuln M n s d) :=
  fun h => uInv_all h

#print axioms shallow_misses

/-- THE COUNTEREXAMPLE to the final rule with the mark answer on the requested chain (summary):
    the construction hypotheses hold, the flow is real, `D` and the design with the deep answer report
    it (the latter in the normal layer), the shallow variant does not, and it derives the non-exact
    static fact `(S, [], [any], 7)` above a position from the precise `(S, <C>.s, $, 7)`. -/
theorem counterexample :
    SWF Xs ∧ prog.WF ∧ Reach prog [0] 1 2 ⟨rB, [], T⟩ ∧ (1, 2, sinkPat) ∈ sinks ∧
    sinkPat.covers ⟨rB, [], T⟩ ∧
    (∃ b, D prog counted 2 α1 sinks [0] (.vuln 1 2 sinkPat b)) ∧
    DS Xd (.vuln 1 2 sinkPat false) ∧ (∀ d, ¬ DS Xs (.vuln 1 2 sinkPat d)) ∧
    DS Xs (.edge 1 ws 1 A7F) ∧ AboveNE Xs A7F.fact :=
  ⟨clean_swf_s, wf, clean_reach, m_sink, clean_covers, clean_D_finds, deep_vuln_normal,
    fun _ => shallow_misses, shallow_degrades, shallow_any_above⟩

#print axioms counterexample

end CexClean

/-! ## 15. The records under the final rule: `CexAbove` and `CexWide` through NORMAL edges

Both programs satisfy the construction hypotheses (`above_swf`, `wide_swf`), so `vulnD` reports their
vulnerabilities. The explicit derivations show HOW, and that the reported edge is in the normal layer.

* `CexAbove`: the write `C.s = null` in `caller` has the class keep edge `S.<C>.* →_{s} S.<C>.*`,
  strictly below the static root: it raises `<C>` instead of producing `(S, <C>, [any], *)`. The
  caller answers `(S, <C>, *, {}, *)` from its added fact `(S, <C>.f, $, 7)`, which passes the write
  as `(S, <C>, */{s}, *)`. `m`'s request `<C>.f` climbs through that edge (above `<C>.f`), the caller
  answers `(S, <C>.f, *)`, and the rest is as in the first design.
* `CexWide`: `K` raises `<C>` at its keep edge `S.<C>.* →_{u} S.<C>.*` and answers
  `(S, <C>, *, {}, *)` from the caller's `(S, <C>.s, *)`; its summary
  `(S, <C>, *) → (S, <C>, */{u}, *)` keeps `.s`, so the caller's precise facts come back precise. -/

namespace CexAbove

/-- The final rule on the `CexAbove` program. -/
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩
def AC : PFact := sAns S [C]
def ACs : AFact := ⟨⟨S, [C], .star (.set [sA]), .star⟩, false⟩
/-- The class keep edge of `C.s = null`. -/
def wrKeep : MicroEdge := (⟨S, [C], .star (.set [sA]), .star⟩, pat S [C])

theorem posIn_cases {p : List Acc} (h : PosIn X2 p) : p = [] ∨ p = [C] ∨ p = [C, fA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert heb <;> revert e <;> decide
  · have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    exact absurd hsb (by decide)

theorem abovePos_cases {q : List Acc} (h : AbovePos X2 q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · exact .inl (prefix_one hne hPr)
  · exact prefix_two hne hPr

/-- The program satisfies the construction hypotheses. -/
theorem above_swf : SWF X2 where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    refine .inl (ssB_sound ?_ h1 h2)
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert h2 h1 <;> revert e <;> decide
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hq h2 h1 <;> revert e <;> decide
  toC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
        ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  fromC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
        ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesU hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  alpha := rfl

#print axioms above_swf

theorem y_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem y_src : DS X2 (.edge 0 zeroFact 1 wF) := DS.step y_start m_src (by decide)
theorem y_aC : DS X2 (.added 1 wS) := DS.added (a := wF) y_src m_cC List.mem_cons_self (by decide)
theorem y_jC : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wS = Sroot := by decide
  exact h ▸ DS.initA y_aC
theorem y_eC0 : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start y_jC
/-- The static root passes the write as `(S, [], */{<C>}, *)` only: no `(S, <C>, [any], *)`. -/
theorem y_eC1 : DS X2 (.edge 1 Sroot 1 a1F) := DS.step y_eC0 m_wr (by decide)
/-- RAISE at the class keep edge `S.<C>.* →_{s} S.<C>.*`, strictly below the static root. -/
theorem y_sreqCC : DS X2 (.sreq 1 Sroot [C]) :=
  DS.sreqStmt (e := wrKeep) y_eC0 m_wr (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER from the caller's added fact `(S, <C>.f, $, 7)`, below `<C>`. -/
theorem y_jCC : DS X2 (.init 1 AC) := DS.sanswer y_sreqCC y_aC (by decide)
theorem y_eCC0 : DS X2 (.edge 1 AC 0 ⟨AC, false⟩) := DS.start y_jCC
/-- The class answer passes `C.s = null` precisely: `(S, <C>, */{s}, *)`. -/
theorem y_eCC1 : DS X2 (.edge 1 AC 1 ACs) := DS.step y_eCC0 m_wr (by decide)
theorem y_amC : DS X2 (.added 2 ACs.fact) :=
  DS.added (a := ACs) y_eCC1 m_cm List.mem_cons_self (by decide)
theorem y_jm : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 ACs.fact = Sroot := by decide
  exact h ▸ DS.initA y_amC
theorem y_em0 : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start y_jm
/-- RAISE in `m`. -/
theorem y_sreq : DS X2 (.sreq 2 Sroot [C, fA]) :=
  DS.sreqStmt (e := readE) y_em0 m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- CLIMB through the caller edge `AC → (S, <C>, */{s}, *)`, whose added fact lies above `<C>.f`. -/
theorem y_sreqC : DS X2 (.sreq 1 AC [C, fA]) :=
  DS.sreqUp (a := ACs) (e := bindS) y_sreq y_eCC1 m_cm rfl List.mem_cons_self (by decide)
    (by decide)
/-- ANSWER in the caller from `(S, <C>.f, $, 7)`. -/
theorem y_jCA : DS X2 (.init 1 Ans) := DS.sanswer y_sreqC y_aC (by decide)
theorem y_eCA0 : DS X2 (.edge 1 Ans 0 ⟨Ans, false⟩) := DS.start y_jCA
theorem y_eCA1 : DS X2 (.edge 1 Ans 1 ⟨Ans, false⟩) := DS.step y_eCA0 m_wr (by decide)
theorem y_amA : DS X2 (.added 2 Ans) :=
  DS.added (a := ⟨Ans, false⟩) y_eCA1 m_cm List.mem_cons_self (by decide)
/-- ANSWER in `m` from the precise added fact. -/
theorem y_jmA : DS X2 (.init 2 Ans) := DS.sanswer y_sreq y_amA (by decide)
theorem y_emA0 : DS X2 (.edge 2 Ans 0 ⟨Ans, false⟩) := DS.start y_jmA
theorem y_emA1 : DS X2 (.edge 2 Ans 1 ⟨pat yB [], false⟩) := DS.step y_emA0 m_rd (by decide)
theorem y_emA2 : DS X2 (.edge 2 Ans 2 ⟨pat retB [], false⟩) := DS.step y_emA1 m_rt (by decide)
theorem y_eCA2 : DS X2 (.edge 1 Ans 2 ⟨pat rB [], false⟩) :=
  DS.ret (a := ⟨Ans, false⟩) (r := ⟨pat retB [], false⟩) (r' := ⟨pat rB [], false⟩) (e2 := retE)
    y_eCA1 m_cm List.mem_cons_self (by decide) y_jmA (by decide) y_emA2 (by decide)
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem y_rC : DS X2 (.req 1 Ans T) := DS.reqSink y_eCA2 m_sink (by decide)
/-- The deep answer of the mark request: `(S, <C>.f, $, 7)` itself. -/
theorem y_jCw : DS X2 (.init 1 wS) := by
  have h : X2.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer y_rC y_aC rfl (by decide)
theorem y_eCw0 : DS X2 (.edge 1 wS 0 wF) := DS.start y_jCw
theorem y_eCw1 : DS X2 (.edge 1 wS 1 wF) := DS.step y_eCw0 m_wr (by decide)
theorem y_eCw2 : DS X2 (.edge 1 wS 2 ⟨⟨rB, [], .exact, .conc T⟩, false⟩) :=
  DS.ret (a := wF) (r := ⟨⟨retB, [], .exact, .conc T⟩, false⟩)
    (r' := ⟨⟨rB, [], .exact, .conc T⟩, false⟩) (e2 := retE) y_eCw1 m_cm List.mem_cons_self
    (by decide) y_jmA (by decide) y_emA2 (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)
/-- THE FINAL RULE (`Design`) REPORTS `CexAbove` IN THE NORMAL LAYER. -/
theorem y_vuln_normal : DS X2 (.vuln 1 2 sinkPat false) := DS.vuln y_eCw2 m_sink (by decide)

#print axioms y_vuln_normal

/-- The same from the soundness theorem of the final rule. -/
theorem above_design_finds : ∃ b, DS X2 (.vuln 1 2 sinkPat b) :=
  vulnD above_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf cex_reach m_sink rfl cex_covers

#print axioms above_design_finds

end CexAbove

namespace CexWide

/-- The final rule on the `CexWide` program. -/
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩
def AC : PFact := sAns S [C]
def ACF : AFact := ⟨AC, false⟩
def ACu : AFact := ⟨⟨S, [C], .star (.set [uA]), .star⟩, false⟩
/-- The class keep edge of `C.u = null`. -/
def wruKeep : MicroEdge := (⟨S, [C], .star (.set [uA]), .star⟩, pat S [C])
def tT : AFact := ⟨⟨tB, [], .exact, .conc T⟩, false⟩
def wsT : AFact := ⟨⟨S, [C, sA], .exact, .conc T⟩, false⟩
def retT : AFact := ⟨⟨retB, [], .exact, .conc T⟩, false⟩
def rT : AFact := ⟨⟨rB, [], .exact, .conc T⟩, false⟩

theorem posIn_cases {p : List Acc} (h : PosIn X2 p) :
    p = [] ∨ p = [C] ∨ p = [C, gA] ∨ p = [C, sA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert heb <;>
      revert e <;> decide
  · have hs' : (M, n, s) = (1, 4, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    exact absurd hsb (by decide)

theorem abovePos_cases {q : List Acc} (h : AbovePos X2 q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · exact .inl (prefix_one hne hPr)
  · exact prefix_two hne hPr
  · exact prefix_two hne hPr

/-- The program satisfies the construction hypotheses. -/
theorem wide_swf : SWF X2 where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    refine .inl (ssB_sound ?_ h1 h2)
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert h2 h1 <;>
      revert e <;> decide
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hq h2 h1 <;>
      revert e <;> decide
  toC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
        ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
        revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  fromC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
        ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
        revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  alpha := rfl

#print axioms wide_swf

theorem w_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem w_src : DS X2 (.edge 0 zeroFact 1 wgF) := DS.step w_start m_src (by decide)
theorem w_aC : DS X2 (.added 1 wg) := DS.added (a := wgF) w_src m_cC List.mem_cons_self (by decide)
theorem w_jC : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wg = Sroot := by decide
  exact h ▸ DS.initA w_aC
theorem w_eC0 : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start w_jC
/-- RAISE at the read `t = C.g`. -/
theorem w_sreqG : DS X2 (.sreq 1 Sroot [C, gA]) :=
  DS.sreqStmt (e := readG) w_eC0 m_rdg (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem w_jAg : DS X2 (.init 1 Ag) := DS.sanswer w_sreqG w_aC (by decide)
theorem w_eAg0 : DS X2 (.edge 1 Ag 0 AgF) := DS.start w_jAg
theorem w_eAg1 : DS X2 (.edge 1 Ag 1 tF) := DS.step w_eAg0 m_rdg (by decide)
/-- `C.s = t`: the precise `(S, <C>.s, *)`. -/
theorem w_eAg2 : DS X2 (.edge 1 Ag 2 AsF) := DS.step w_eAg1 m_wrs (by decide)
theorem w_aK : DS X2 (.added 2 As) := DS.added (a := AsF) w_eAg2 m_cK List.mem_cons_self (by decide)
theorem w_jK : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 As = Sroot := by decide
  exact h ▸ DS.initA w_aK
theorem w_eK0 : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start w_jK
/-- RAISE in `K` at its class keep edge `S.<C>.* →_{u} S.<C>.*`. -/
theorem w_sreqK : DS X2 (.sreq 2 Sroot [C]) :=
  DS.sreqStmt (e := wruKeep) w_eK0 m_wru (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER `(S, <C>, *, {}, *)` from the caller's `(S, <C>.s, *)`. -/
theorem w_jKC : DS X2 (.init 2 AC) := DS.sanswer w_sreqK w_aK (by decide)
theorem w_eKC0 : DS X2 (.edge 2 AC 0 ACF) := DS.start w_jKC
/-- `K`'s summary `(S, <C>, *) → (S, <C>, */{u}, *)`. -/
theorem w_eKC1 : DS X2 (.edge 2 AC 1 ACu) := DS.step w_eKC0 m_wru (by decide)
/-- The summary keeps `.s`: the caller's precise fact comes back precise. -/
theorem w_eAg3 : DS X2 (.edge 1 Ag 3 AsF) :=
  DS.ret (a := AsF) (r := AsF) (r' := AsF) (e2 := bindS) w_eAg2 m_cK List.mem_cons_self (by decide)
    w_jKC (by decide) w_eKC1 (by decide) List.mem_cons_self (by decide)
theorem w_am : DS X2 (.added 3 As) := DS.added (a := AsF) w_eAg3 m_cm List.mem_cons_self (by decide)
theorem w_jm : DS X2 (.init 3 Sroot) := by
  have h : X2.α 3 As = Sroot := by decide
  exact h ▸ DS.initA w_am
theorem w_em0 : DS X2 (.edge 3 Sroot 0 SrootF) := DS.start w_jm
theorem w_sreqM : DS X2 (.sreq 3 Sroot [C, sA]) :=
  DS.sreqStmt (e := readS) w_em0 m_rds (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER in `m` from its added fact at the position (no climb). -/
theorem w_jmA : DS X2 (.init 3 As) := DS.sanswer w_sreqM w_am (by decide)
theorem w_emA0 : DS X2 (.edge 3 As 0 AsF) := DS.start w_jmA
theorem w_emA1 : DS X2 (.edge 3 As 1 ⟨pat yB [], false⟩) := DS.step w_emA0 m_rds (by decide)
theorem w_emA2 : DS X2 (.edge 3 As 2 ⟨pat retB [], false⟩) := DS.step w_emA1 m_rt (by decide)
theorem w_eAg4 : DS X2 (.edge 1 Ag 4 ⟨pat rB [], false⟩) :=
  DS.ret (a := AsF) (r := ⟨pat retB [], false⟩) (r' := ⟨pat rB [], false⟩) (e2 := retE)
    w_eAg3 m_cm List.mem_cons_self (by decide) w_jmA (by decide) w_emA2 (by decide)
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem w_rC : DS X2 (.req 1 Ag T) := DS.reqSink w_eAg4 m_sink (by decide)
/-- The deep answer of the mark request: `(S, <C>.g, $, 7)` itself. -/
theorem w_jCw : DS X2 (.init 1 wg) := by
  have h : X2.ansInit Ag wg T = wg := by decide
  exact h ▸ DS.answer w_rC w_aC rfl (by decide)
theorem w_eCw0 : DS X2 (.edge 1 wg 0 wgF) := DS.start w_jCw
theorem w_eCw1 : DS X2 (.edge 1 wg 1 tT) := DS.step w_eCw0 m_rdg (by decide)
theorem w_eCw2 : DS X2 (.edge 1 wg 2 wsT) := DS.step w_eCw1 m_wrs (by decide)
theorem w_eCw3 : DS X2 (.edge 1 wg 3 wsT) :=
  DS.ret (a := wsT) (r := wsT) (r' := wsT) (e2 := bindS) w_eCw2 m_cK List.mem_cons_self (by decide)
    w_jKC (by decide) w_eKC1 (by decide) List.mem_cons_self (by decide)
theorem w_eCw4 : DS X2 (.edge 1 wg 4 rT) :=
  DS.ret (a := wsT) (r := retT) (r' := rT) (e2 := retE) w_eCw3 m_cm List.mem_cons_self (by decide)
    w_jmA (by decide) w_emA2 (by decide) (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- THE FINAL RULE (`Design`) REPORTS `CexWide` IN THE NORMAL LAYER. -/
theorem w_vuln_normal : DS X2 (.vuln 1 4 sinkPat false) := DS.vuln w_eCw4 m_sink (by decide)

#print axioms w_vuln_normal

/-- The same from the soundness theorem of the final rule. -/
theorem wide_design_finds : ∃ b, DS X2 (.vuln 1 4 sinkPat b) :=
  vulnD wide_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf wide_reach m_sink rfl wide_covers

#print axioms wide_design_finds

end CexWide

/-! ## 16. A field-to-field pass rule at an unresolved call: `CopyF2F`

`root: C.f = source(); A()`, `A: lib(); x = D.g; sink(x)`, where `lib()` is unresolved and has the
pass rule `CopyAllMarks(ClassStatic(C).f → ClassStatic(D).g)`: its statement summary is the keep edge
of the base `S.* → S.*` and the FIELD-TO-FIELD edge `S.<C>.f.* → S.<D>.g.*`. Methods `0` (root) and
`1` (`A`). The program satisfies the (relaxed) construction hypotheses (`copy_swf`).

In run 1, `A`'s static root `(S, [], *)` meets the copy edge strictly below it: the copy gives no
fact and raises the position request for the SOURCE field `<C>.f` (`c_sreq`); the keep edge passes
the static root. `A`'s added fact `(S, <C>.f, $, 7)` answers `(S, <C>.f, *, {}, *)`, and the answer
flows through the copy to the TARGET field `(S, <D>.g, *, {}, *)` (`c_eAf1`) and through the read to
`x`. The sink asks for the mark 7 on the answer, the deep mark answer gives `(S, <C>.f, $, 7)`, and
the vulnerability is reported through a NORMAL edge (`c_vuln_normal`; also `copy_design_finds` from
`vulnD`). -/

namespace CopyF2F

def S : Base := 1
def xB : Base := 2
def C : Acc := 10
def fA : Acc := 11
def D : Acc := 12
def gA : Acc := 13
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- The tainted static field `(S, <C>.f, $, 7)`. -/
def wC : PFact := ⟨S, [C, fA], .exact, .conc T⟩
def wCF : AFact := ⟨wC, false⟩
def wDF : AFact := ⟨⟨S, [D, gA], .exact, .conc T⟩, false⟩
/-- The answer at the source field. -/
def Af : PFact := sAns S [C, fA]
def AfF : AFact := ⟨Af, false⟩
/-- The answer copied to the target field. -/
def AgF : AFact := ⟨pat S [D, gA], false⟩
def xF : AFact := ⟨pat xB [], false⟩
def xT : AFact := ⟨⟨xB, [], .exact, .conc T⟩, false⟩
/-- root: `C.f = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, wC)]⟩
/-- The field-to-field edge of `CopyAllMarks(ClassStatic(C).f → ClassStatic(D).g)`. -/
def copyE : MicroEdge := (pat S [C, fA], pat S [D, gA])
/-- The statement summary of the unresolved call `lib()`: the keep edge of `S` and the copy. -/
def cp : Stmt := ⟨[S], [(pat S [], pat S []), copyE]⟩
/-- A: `x = D.g`. -/
def rd : Stmt := readStmt S xB [D, gA]
def readE : MicroEdge := (pat S [D, gA], pat xB [])
def cA : Call := ⟨1, [S], [bindS], [bindS]⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 2,
   [(0, 0, .stmt src, 1), (0, 1, .call cA, 2), (1, 0, .stmt cp, 1), (1, 1, .stmt rd, 2)]⟩
def sinkPat : PFact := ⟨xB, [], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(1, 2, sinkPat)]
/-- The class accessors are not counted. -/
def counted (a : Acc) : Bool := !(Nat.beq a C || Nat.beq a D)
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
/-- The final rule. -/
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cA : (0, 1, Instr.call cA, 2) ∈ prog.edges := by simp [prog]
theorem m_cp : (1, 0, Instr.stmt cp, 1) ∈ prog.edges := by simp [prog]
theorem m_rd : (1, 1, Instr.stmt rd, 2) ∈ prog.edges := by simp [prog]
theorem m_sink : (1, 2, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesF {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cA ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt cp ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .stmt rd ∧ n' = 2) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- THE CONCRETE FLOW: `S.<C>.f` → (the copy) `S.<D>.g` → `x` at the sink. -/
theorem copy_reach : Reach prog [0] 1 2 ⟨xB, [], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, fA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, wC), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have a1 : Flow prog 1 ⟨S, [C, fA], T⟩ 1 ⟨S, [D, gA], T⟩ :=
    Flow.step (Flow.start 1 ⟨S, [C, fA], T⟩) m_cp
      (.inr ⟨copyE, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  have a2 : Flow prog 1 ⟨S, [C, fA], T⟩ 2 ⟨xB, [], T⟩ :=
    Flow.step a1 m_rd
      (.inr ⟨readE, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩)
  exact Reach.down (Reach.root List.mem_cons_self h0) m_cA List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, fA], [C, fA], rfl, rfl, rfl, rfl, rfl⟩ a2

theorem copy_covers : sinkPat.covers ⟨xB, [], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms copy_reach

theorem posIn_cases {p : List Acc} (h : PosIn X2 p) : p = [] ∨ p = [C, fA] ∨ p = [D, gA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert heb <;> revert e <;> decide
  · have hs' : (M, n, s) = (1, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    exact absurd hsb (by decide)

theorem abovePos_cases {q : List Acc} (h : AbovePos X2 q) : q = [] ∨ q = [C] ∨ q = [D] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · rcases prefix_two hne hPr with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rcases prefix_two hne hPr with h | h
    · exact .inl h
    · exact .inr (.inr h)

/-- The program satisfies the construction hypotheses: the copy is a field-to-field edge. -/
theorem copy_swf : SWF X2 where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    have key : ssB e = true ∨ (e.1.path ≠ [] ∧ e.1.path ≠ [C] ∧ e.1.path ≠ [D] ∧
        e.2.path ≠ [] ∧ e.2.path ≠ [C] ∧ e.2.path ≠ [D]) := by
      rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
        revert h2 h1 <;> revert e <;> decide
    rcases key with hk | ⟨a1, a2, a3, b1, b2, b3⟩
    · exact .inl (ssB_sound hk h1 h2)
    · refine .inr ⟨fun hab => ?_, fun hab => ?_⟩
      · rcases abovePos_cases hab with h | h | h
        · exact a1 h
        · exact a2 h
        · exact a3 h
      · rcases abovePos_cases hab with h | h | h
        · exact b1 h
        · exact b2 h
        · exact b3 h
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert hq h2 h1 <;> revert e <;> decide
  toC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
        revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  fromC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
        revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesF hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  alpha := rfl

#print axioms copy_swf

theorem c_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem c_src : DS X2 (.edge 0 zeroFact 1 wCF) := DS.step c_start m_src (by decide)
theorem c_aA : DS X2 (.added 1 wC) := DS.added (a := wCF) c_src m_cA List.mem_cons_self (by decide)
theorem c_jA : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wC = Sroot := by decide
  exact h ▸ DS.initA c_aA
theorem c_eA0 : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start c_jA
/-- The static root passes the unresolved call by the keep edge only: the copy edge fires. -/
theorem c_eA1 : DS X2 (.edge 1 Sroot 1 SrootF) := DS.step c_eA0 m_cp (by decide)
/-- RAISE: the copy on the static root raises the position request for the SOURCE field. -/
theorem c_sreq : DS X2 (.sreq 1 Sroot [C, fA]) :=
  DS.sreqStmt (e := copyE) c_eA0 m_cp (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER from `A`'s added fact `(S, <C>.f, $, 7)`, at the position. -/
theorem c_jAf : DS X2 (.init 1 Af) := DS.sanswer c_sreq c_aA (by decide)
theorem c_eAf0 : DS X2 (.edge 1 Af 0 AfF) := DS.start c_jAf
/-- The answer flows through the copy to the TARGET field: `(S, <D>.g, *, {}, *)`, normal layer. -/
theorem c_eAf1 : DS X2 (.edge 1 Af 1 AgF) := DS.step c_eAf0 m_cp (by decide)
theorem c_eAf2 : DS X2 (.edge 1 Af 2 xF) := DS.step c_eAf1 m_rd (by decide)
/-- The sink asks for the mark 7 on the answer premise. -/
theorem c_req : DS X2 (.req 1 Af T) := DS.reqSink c_eAf2 m_sink (by decide)
/-- The deep mark answer: `(S, <C>.f, $, 7)` itself. -/
theorem c_jw : DS X2 (.init 1 wC) := by
  have h : X2.ansInit Af wC T = wC := by decide
  exact h ▸ DS.answer c_req c_aA rfl (by decide)
theorem c_ew0 : DS X2 (.edge 1 wC 0 wCF) := DS.start c_jw
/-- The copy moves the exact fact to the target field: `(S, <D>.g, $, 7)`. -/
theorem c_ew1 : DS X2 (.edge 1 wC 1 wDF) := DS.step c_ew0 m_cp (by decide)
theorem c_ew2 : DS X2 (.edge 1 wC 2 xT) := DS.step c_ew1 m_rd (by decide)
/-- THE FINAL RULE REPORTS THE FIELD-TO-FIELD FLOW IN THE NORMAL LAYER. -/
theorem c_vuln_normal : DS X2 (.vuln 1 2 sinkPat false) := DS.vuln c_ew2 m_sink (by decide)

#print axioms c_vuln_normal

/-- The same from the soundness theorem of the final rule (relaxed `SWF`). -/
theorem copy_design_finds : ∃ b, DS X2 (.vuln 1 2 sinkPat b) :=
  vulnD copy_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf copy_reach m_sink rfl copy_covers

#print axioms copy_design_finds

/-- No static `[any]` fact above a position in this program (`no_any_above`). -/
theorem copy_no_any {M : MethodId} {i : PFact} {n : Node} {f : AFact} (h : DS X2 (.edge M i n f))
    (hb : f.fact.base = S) (hp : AbovePos X2 f.fact.path) : f.fact.kind ≠ .any :=
  (no_any_above copy_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ h hb hp).1

end CopyF2F

/-! ## 17. Deep static sinks: the ordinary mark request climbs

Two programs with the deep static sink `ContainsMark(ClassStatic(C).f.g, T)` in a callee `m`, after a
caller write `C.f = x` with an abstract `x`. The sink pattern `(S, <C>.f.g, $, 7)` lies below `m`'s
static root: under the final rule it raises the ordinary MARK request on the premise (`check`), which
climbs to the caller through the caller edge of `C.f = x`, whatever the caller premise. (A sink
position request, as in the earlier draft of the rule, is raised instead of the mark request and
climbs only through a STATIC caller premise for the same location: it lost both flows.)

* `DeepSink`: `root: C.h.g = source(); caller()`, `caller: x = C.h; C.f = x; m()`,
  `m: sink(C.f.g)`. The caller's abstract `x` comes from the answer `(S, <C>.h, *)` of the read; the
  mark request climbs to that static premise, the deep mark answer gives `(S, <C>.h.g, $, 7)` itself,
  and the vulnerability is reported through a NORMAL edge (`e_vuln_normal`).
* `DeepSinkParam`: `root: x.g = source(); caller(x)`, `caller(p): C.f = p; m()`, `m: sink(C.f.g)`.
  The caller premise is the parameter `(p, [], *)`; the mark request climbs to it and is answered as
  for an instance field (`answerInit`: the requested chain, `[any]` in the demand layer), so the
  vulnerability is reported in the DEMAND layer (`p_vuln`), as `D` reports it. -/

namespace DeepSink

def S : Base := 1
def xB : Base := 2
def C : Acc := 10
def fA : Acc := 11
def gA : Acc := 12
def hA : Acc := 13
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
/-- The source `(S, <C>.h.g, $, 7)`. -/
def wHG : PFact := ⟨S, [C, hA, gA], .exact, .conc T⟩
def wHGF : AFact := ⟨wHG, false⟩
def Ah : PFact := sAns S [C, hA]
def AhF : AFact := ⟨Ah, false⟩
def xF : AFact := ⟨pat xB [], false⟩
def WfF : AFact := ⟨pat S [C, fA], false⟩
def xgT : AFact := ⟨⟨xB, [gA], .exact, .conc T⟩, false⟩
def wFG : PFact := ⟨S, [C, fA, gA], .exact, .conc T⟩
def wFGF : AFact := ⟨wFG, false⟩
/-- root: `C.h.g = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, wHG)]⟩
/-- caller: `x = C.h`. -/
def rdh : Stmt := readStmt S xB [C, hA]
def readH : MicroEdge := (pat S [C, hA], pat xB [])
/-- caller: `C.f = x`. -/
def wr : Stmt :=
  ⟨[S, xB], [(⟨S, [], .star (.set [C]), .star⟩, pat S []),
    (⟨S, [C], .star (.set [fA]), .star⟩, pat S [C]), (pat xB [], pat xB []), (pat xB [], pat S [C, fA])]⟩
def cC : Call := ⟨1, [S], [bindS], [bindS]⟩
def cm : Call := ⟨2, [S], [bindS], [bindS]⟩
def exitOf : MethodId → Node
  | 0 => 2
  | 1 => 3
  | _ => 0
def prog : Program :=
  ⟨fun _ => 0, exitOf,
   [(0, 0, .stmt src, 1), (0, 1, .call cC, 2), (1, 0, .stmt rdh, 1), (1, 1, .stmt wr, 2),
    (1, 2, .call cm, 3)]⟩
/-- m: `ContainsMark(ClassStatic(C).f.g, 7)`. -/
def sinkPat : PFact := ⟨S, [C, fA, gA], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(2, 0, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cC : (0, 1, Instr.call cC, 2) ∈ prog.edges := by simp [prog]
theorem m_rdh : (1, 0, Instr.stmt rdh, 1) ∈ prog.edges := by simp [prog]
theorem m_wr : (1, 1, Instr.stmt wr, 2) ∈ prog.edges := by simp [prog]
theorem m_cm : (1, 2, Instr.call cm, 3) ∈ prog.edges := by simp [prog]
theorem m_sink : (2, 0, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesE {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cC ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt rdh ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .stmt wr ∧ n' = 2) ∨
    (M = 1 ∧ n = 2 ∧ ins = .call cm ∧ n' = 3) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;>
      cases h <;> revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;>
      cases h <;> revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;>
      cases h <;> revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;>
      cases h

/-- THE CONCRETE FLOW: `S.<C>.h.g` → `x.g` → `S.<C>.f.g` → the sink in `m`. -/
theorem deep_reach : Reach prog [0] 2 0 ⟨S, [C, fA, gA], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨S, [C, hA, gA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, wHG), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have c1 : Flow prog 1 ⟨S, [C, hA, gA], T⟩ 1 ⟨xB, [gA], T⟩ :=
    Flow.step (Flow.start 1 ⟨S, [C, hA, gA], T⟩) m_rdh
      (.inr ⟨readH, List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, trivial, rfl, trivial, [gA], [gA], rfl, rfl, rfl, rfl, rfl⟩)
  have c2 : Flow prog 1 ⟨S, [C, hA, gA], T⟩ 2 ⟨S, [C, fA, gA], T⟩ :=
    Flow.step c1 m_wr
      (.inr ⟨(pat xB [], pat S [C, fA]), by simp [wr],
        rfl, rfl, trivial, rfl, trivial, [gA], [gA], rfl, rfl, rfl, rfl, rfl⟩)
  exact Reach.down
    (Reach.down (Reach.root List.mem_cons_self h0) m_cC List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [C, hA, gA], [C, hA, gA], rfl, rfl, rfl, rfl, rfl⟩ c2)
    m_cm List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, fA, gA], [C, fA, gA], rfl, rfl, rfl, rfl, rfl⟩
    (Flow.start 2 ⟨S, [C, fA, gA], T⟩)

theorem deep_covers : sinkPat.covers ⟨S, [C, fA, gA], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms deep_reach

theorem posIn_cases {p : List Acc} (h : PosIn X2 p) :
    p = [] ∨ p = [C, hA] ∨ p = [C] ∨ p = [C, fA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;>
      cases h <;> revert heb <;> revert e <;> decide
  · have hs' : (M, n, s) = (2, 0, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    decide

theorem abovePos_cases {q : List Acc} (h : AbovePos X2 q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · exact prefix_two hne hPr
  · exact .inl (prefix_one hne hPr)
  · exact prefix_two hne hPr

/-- The program satisfies the construction hypotheses. -/
theorem deep_swf : SWF X2 where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    refine .inl (ssB_sound ?_ h1 h2)
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert h2 h1 <;> revert e <;> decide
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hq h2 h1 <;> revert e <;> decide
  toC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  fromC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesE hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  alpha := rfl

#print axioms deep_swf

theorem e_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem e_src : DS X2 (.edge 0 zeroFact 1 wHGF) := DS.step e_start m_src (by decide)
theorem e_aC : DS X2 (.added 1 wHG) := DS.added (a := wHGF) e_src m_cC List.mem_cons_self (by decide)
theorem e_jC : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wHG = Sroot := by decide
  exact h ▸ DS.initA e_aC
theorem e_eC0 : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start e_jC
/-- RAISE at the read `x = C.h` on the static root. -/
theorem e_sreqH : DS X2 (.sreq 1 Sroot [C, hA]) :=
  DS.sreqStmt (e := readH) e_eC0 m_rdh (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- ANSWER from the added fact `(S, <C>.h.g, $, 7)`, below `<C>.h`. -/
theorem e_jAh : DS X2 (.init 1 Ah) := DS.sanswer e_sreqH e_aC (by decide)
theorem e_eAh0 : DS X2 (.edge 1 Ah 0 AhF) := DS.start e_jAh
/-- The abstract value `x = (x, [], *)`. -/
theorem e_eAh1 : DS X2 (.edge 1 Ah 1 xF) := DS.step e_eAh0 m_rdh (by decide)
/-- `C.f = x`: `(S, <C>.f, *)`. -/
theorem e_eAh2 : DS X2 (.edge 1 Ah 2 WfF) := DS.step e_eAh1 m_wr (by decide)
theorem e_aM : DS X2 (.added 2 WfF.fact) := DS.added (a := WfF) e_eAh2 m_cm List.mem_cons_self (by decide)
theorem e_jM : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 WfF.fact = Sroot := by decide
  exact h ▸ DS.initA e_aM
theorem e_eM0 : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start e_jM
/-- THE DEEP STATIC SINK RAISES THE ORDINARY MARK REQUEST on `m`'s static root. -/
theorem e_rM : DS X2 (.req 2 Sroot T) := DS.reqSink e_eM0 m_sink (by decide)
/-- It CLIMBS to the caller premise `(S, <C>.h, *)` through the caller edge of `C.f = x`. -/
theorem e_rC : DS X2 (.req 1 Ah T) :=
  DS.reqUp (a := WfF) (e := bindS) e_rM e_eAh2 m_cm rfl List.mem_cons_self (by decide) (by decide)
    (by decide)
/-- The deep mark answer: `(S, <C>.h.g, $, 7)` itself. -/
theorem e_jw : DS X2 (.init 1 wHG) := by
  have h : X2.ansInit Ah wHG T = wHG := by decide
  exact h ▸ DS.answer e_rC e_aC rfl (by decide)
theorem e_ew0 : DS X2 (.edge 1 wHG 0 wHGF) := DS.start e_jw
theorem e_ew1 : DS X2 (.edge 1 wHG 1 xgT) := DS.step e_ew0 m_rdh (by decide)
theorem e_ew2 : DS X2 (.edge 1 wHG 2 wFGF) := DS.step e_ew1 m_wr (by decide)
theorem e_aMw : DS X2 (.added 2 wFG) :=
  DS.added (a := wFGF) e_ew2 m_cm List.mem_cons_self (by decide)
/-- `m` answers its mark request by the deep answer `(S, <C>.f.g, $, 7)`. -/
theorem e_jMw : DS X2 (.init 2 wFG) := by
  have h : X2.ansInit Sroot wFG T = wFG := by decide
  exact h ▸ DS.answer e_rM e_aMw rfl (by decide)
theorem e_eMw0 : DS X2 (.edge 2 wFG 0 wFGF) := DS.start e_jMw
/-- THE DEEP STATIC SINK IS REPORTED THROUGH A NORMAL EDGE. -/
theorem e_vuln_normal : DS X2 (.vuln 2 0 sinkPat false) := DS.vuln e_eMw0 m_sink (by decide)

#print axioms e_vuln_normal

theorem deep_design_finds : ∃ b, DS X2 (.vuln 2 0 sinkPat b) :=
  vulnD deep_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf deep_reach m_sink rfl deep_covers

#print axioms deep_design_finds

end DeepSink

namespace DeepSinkParam

def S : Base := 1
def xB : Base := 2
def pB : Base := 3
def C : Acc := 10
def fA : Acc := 11
def gA : Acc := 12
def T : Mark := 7

def Sroot : PFact := pat S []
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def bindS : MicroEdge := (pat S [], pat S [])
def bindX : MicroEdge := (pat xB [], pat pB [])
def xg : PFact := ⟨xB, [gA], .exact, .conc T⟩
def xgF : AFact := ⟨xg, false⟩
def pg : PFact := ⟨pB, [gA], .exact, .conc T⟩
def P0 : PFact := pat pB []
def P0F : AFact := ⟨P0, false⟩
def WfF : AFact := ⟨pat S [C, fA], false⟩
/-- The caller's answer on its parameter premise (the requested chain). -/
def PT : PFact := ⟨pB, [], .star Excl.empty, .conc T⟩
def MT : PFact := ⟨S, [C, fA], .any, .conc T⟩
/-- root: `x.g = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, xg)]⟩
/-- caller(p): `C.f = p`. -/
def wr : Stmt :=
  ⟨[S, pB], [(⟨S, [], .star (.set [C]), .star⟩, pat S []),
    (⟨S, [C], .star (.set [fA]), .star⟩, pat S [C]), (pat pB [], pat pB []), (pat pB [], pat S [C, fA])]⟩
def cC : Call := ⟨1, [xB], [bindX], []⟩
def cm : Call := ⟨2, [S], [bindS], [bindS]⟩
def exitOf : MethodId → Node
  | 0 => 2
  | 1 => 2
  | _ => 0
def prog : Program :=
  ⟨fun _ => 0, exitOf,
   [(0, 0, .stmt src, 1), (0, 1, .call cC, 2), (1, 0, .stmt wr, 1), (1, 1, .call cm, 2)]⟩
def sinkPat : PFact := ⟨S, [C, fA, gA], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(2, 0, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def α1 : MethodId → PFact → PFact := policy (fun _ => [])
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_cC : (0, 1, Instr.call cC, 2) ∈ prog.edges := by simp [prog]
theorem m_wr : (1, 0, Instr.stmt wr, 1) ∈ prog.edges := by simp [prog]
theorem m_cm : (1, 1, Instr.call cm, 2) ∈ prog.edges := by simp [prog]
theorem m_sink : (2, 0, sinkPat) ∈ sinks := List.mem_cons_self

theorem edgesP {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .call cC ∧ n' = 2) ∨
    (M = 1 ∧ n = 0 ∧ ins = .stmt wr ∧ n' = 1) ∨ (M = 1 ∧ n = 1 ∧ ins = .call cm ∧ n' = 2) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem wf : prog.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  toStar := by
    intro M n c n' hE e he
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  fromStar := by
    intro M n c n' hE e he
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert e <;> decide
  filtPrefix := by
    intro M n b may n' hE
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- THE CONCRETE FLOW: `x.g` → `p.g` → `S.<C>.f.g` → the sink in `m`. -/
theorem param_reach : Reach prog [0] 2 0 ⟨S, [C, fA, gA], T⟩ := by
  have h0 : Flow prog 0 zeroLoc 1 ⟨xB, [gA], T⟩ :=
    Flow.step (Flow.start 0 zeroLoc) m_src
      (.inr ⟨(zeroFact, xg), List.mem_cons_of_mem _ List.mem_cons_self,
        rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩)
  have c1 : Flow prog 1 ⟨pB, [gA], T⟩ 1 ⟨S, [C, fA, gA], T⟩ :=
    Flow.step (Flow.start 1 ⟨pB, [gA], T⟩) m_wr
      (.inr ⟨(pat pB [], pat S [C, fA]), by simp [wr],
        rfl, rfl, trivial, rfl, trivial, [gA], [gA], rfl, rfl, rfl, rfl, rfl⟩)
  exact Reach.down
    (Reach.down (l1 := ⟨pB, [gA], T⟩) (Reach.root List.mem_cons_self h0) m_cC List.mem_cons_self
      ⟨rfl, rfl, trivial, rfl, trivial, [gA], [gA], rfl, rfl, rfl, rfl, rfl⟩ c1)
    m_cm List.mem_cons_self
    ⟨rfl, rfl, trivial, rfl, trivial, [C, fA, gA], [C, fA, gA], rfl, rfl, rfl, rfl, rfl⟩
    (Flow.start 2 ⟨S, [C, fA, gA], T⟩)

theorem param_covers : sinkPat.covers ⟨S, [C, fA, gA], T⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms param_reach

theorem posIn_cases {p : List Acc} (h : PosIn X2 p) : p = [] ∨ p = [C] ∨ p = [C, fA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert heb <;> revert e <;> decide
  · have hs' : (M, n, s) = (2, 0, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    decide

theorem abovePos_cases {q : List Acc} (h : AbovePos X2 q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · exact .inl (prefix_one hne hPr)
  · exact prefix_two hne hPr

/-- The program satisfies the construction hypotheses. -/
theorem param_swf : SWF X2 where
  base := by decide
  ss := by
    intro M n s n' hE e he h1 h2
    refine .inl (ssB_sound ?_ h1 h2)
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert h2 h1 <;> revert e <;> decide
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hq h2 h1 <;> revert e <;> decide
  toC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  fromC := by
    intro M n c n' hE e he hb
    have key : ssB e = true ∧ e.1.path = [] ∧ e.1.base = X2.sB ∧ e.2.base = X2.sB := by
      rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> revert hb <;> revert e <;> decide
    exact bind_sound key.1 key.2.1 key.2.2.1 key.2.2.2
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl <;> exact absurd h2 (by decide)
  clean := by
    intro M n cl n' hE _
    rcases edgesP hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  alpha := rfl

#print axioms param_swf

theorem p_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem p_src : DS X2 (.edge 0 zeroFact 1 xgF) := DS.step p_start m_src (by decide)
theorem p_aC : DS X2 (.added 1 pg) :=
  DS.added (e := bindX) (a := ⟨pg, false⟩) p_src m_cC List.mem_cons_self (by decide)
theorem p_jC : DS X2 (.init 1 P0) := by
  have h : X2.α 1 pg = P0 := by decide
  exact h ▸ DS.initA p_aC
theorem p_eC0 : DS X2 (.edge 1 P0 0 P0F) := DS.start p_jC
/-- `C.f = p`: `(S, <C>.f, *)` on the parameter premise. -/
theorem p_eC1 : DS X2 (.edge 1 P0 1 WfF) := DS.step p_eC0 m_wr (by decide)
theorem p_aM : DS X2 (.added 2 WfF.fact) := DS.added (a := WfF) p_eC1 m_cm List.mem_cons_self (by decide)
theorem p_jM : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 WfF.fact = Sroot := by decide
  exact h ▸ DS.initA p_aM
theorem p_eM0 : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start p_jM
/-- THE DEEP STATIC SINK RAISES THE ORDINARY MARK REQUEST. -/
theorem p_rM : DS X2 (.req 2 Sroot T) := DS.reqSink p_eM0 m_sink (by decide)
/-- It CLIMBS to the caller's parameter premise. -/
theorem p_rC : DS X2 (.req 1 P0 T) :=
  DS.reqUp (a := WfF) (e := bindS) p_rM p_eC1 m_cm rfl List.mem_cons_self (by decide) (by decide)
    (by decide)
/-- The answer on a non-static premise is the requested chain, as for an instance field. -/
theorem p_jCT : DS X2 (.init 1 PT) := by
  have h : X2.ansInit P0 pg T = PT := by decide
  exact h ▸ DS.answer p_rC p_aC rfl (by decide)
theorem p_eCT0 : DS X2 (.edge 1 PT 0 ⟨⟨pB, [], .any, .conc T⟩, true⟩) := DS.start p_jCT
theorem p_eCT1 : DS X2 (.edge 1 PT 1 ⟨MT, true⟩) := DS.step p_eCT0 m_wr (by decide)
theorem p_aMT : DS X2 (.added 2 MT) :=
  DS.added (a := ⟨MT, true⟩) p_eCT1 m_cm List.mem_cons_self (by decide)
theorem p_jMT : DS X2 (.init 2 MT) := by
  have h : X2.ansInit Sroot MT T = MT := by decide
  exact h ▸ DS.answer p_rM p_aMT rfl (by decide)
theorem p_eMT0 : DS X2 (.edge 2 MT 0 ⟨MT, true⟩) := DS.start p_jMT
/-- THE DEEP STATIC SINK IS REPORTED (demand layer, as for an instance field). -/
theorem p_vuln : DS X2 (.vuln 2 0 sinkPat true) := DS.vuln p_eMT0 m_sink (by decide)

#print axioms p_vuln

theorem param_design_finds : ∃ b, DS X2 (.vuln 2 0 sinkPat b) :=
  vulnD param_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf param_reach m_sink rfl param_covers

#print axioms param_design_finds

end DeepSinkParam

end ApSpec.Statics
