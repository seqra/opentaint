/-
  ApSpec.AnyTaintDefs — the DEFINITIONS of the `[any-taint]` tail kind (decision F69).

  This module holds only definitions, small lemmas and `decide` vectors. The proof files
  (`AnyTaint*.lean`) import it. The design brief is `any-taint/DESIGN.md`: §0 gives the user's
  decisions (cited below as "decision k"), §3.2 the Lean plan.

  ## The correspondence (DESIGN §3.1)

  The base model (`Basic.lean`) has three tail kinds. Its closures `D`, `DR` apply no W6, and
  `Exact.edge_exact` / `RExact.edge_exactR` prove EVERY normal-layer edge exact, normal `.any`
  edges included. So the base model already has the `[any-taint]` tail:

  | spec tail                              | base model                                          |
  |----------------------------------------|-----------------------------------------------------|
  | `*/E`                                  | `.star e`                                           |
  | `$`                                    | `.exact`                                            |
  | `[any]`                                | `.any` with `demand = true`                         |
  | `[any-taint]` (conclusion)             | `.any` with `demand = false`                        |
  | `[any-taint]` premise (must-premise)   | NEW: a premise with the flag `must = true` (`TObj`) |

  The base model already has the demotions of decision 5 (`belowCase` with a non-empty `ex`,
  `aboveCase`, `limitF`, `concPart`, `startFact` of an `.any` premise). The new rule W6T demotes
  only the result of a STATEMENT micro edge with an `.any` target that is not a taint edge (a may:
  a pass rule). A demand pattern tail `[any-taint]` is a LABEL (DESIGN §1): `DemandEdge.din` holds
  it as `.any`, and the emission and the restriction do not read the difference.

  ## Contents

  1. Taint edges and W6T: `TaintEdges`, `TaintConc`, `BindNoAny`, `w6t`, `applyEdgeT`, `applyAllT`,
     `transferT`; lemmas `w6t_fact`, `transferT_LL`, `transferT_reqs`, `transferT_mem`,
     `transfer_memT`, `transferT_facts_map`.
  2. Run 1: the closure `D6T` (= `D` with `transferT`), its support `Sup6T` and `ConfirmedT6`.
  3. The restricted forward run with must-premises: `TObj`, `emitTWith`/`emitT`, `startT`,
     `recLayer`, the closure `DRT`; lemmas `startT_fact`, `emitTWith_some`, `limitF_recLayer_fact`;
     the emission vectors (every cell of the table of decision 8).
  4. The predicates of the proof files: `coversF`, `EndExact`, `EdgeOKT`, `RecsExactT`,
     `SupLink`, `SupT`, `ConfirmedT`, `SatInside`.
  5. The fact simulation with `DR`: `TObj.forget`, `SameFact`, `recsDR`, `RestrictFact`, `FactSim`
     (the statement only), `ConcObjT`, `MustAnyT`, `exitRecsT`, `liftRecs`.
  6. Sanity derivations (`Sanity`): a source keeps `[any-taint]` normal, a pass rule demotes.

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.Basic
import ApSpec.Restricted
import ApSpec.Confirmed
import ApSpec.RestrictedExact
import ApSpec.W6

namespace ApSpec.AnyTaint
open ApSpec

/-! ## 1. Taint edges and the rule W6T -/

/-- The taint edges, a parameter of the runs: `taint e = true` marks the SOURCE micro edges with
    an `[any]` target (decision 3; `AssignMarkOnAnyAccessor`, Go `AnyAccessor`; an unconditional or
    a conditional source). Their `[any]` target is a MUST: every location gets the mark. -/
abbrev TaintEdges := MicroEdge → Bool

/-- `TaintConc P taint`: every taint edge of a statement of `P` has the `.any` target, a concrete
    target mark and a concrete premise mark (`zeroMark` or the condition mark `T'`; decision 2:
    `[any-taint]` has a concrete mark only; S7). -/
def TaintConc (P : Program) (taint : TaintEdges) : Prop :=
  ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → ∀ e, e ∈ s.edges → taint e = true →
    e.2.kind = .any ∧ (∃ t, e.2.mark = .conc t) ∧ (∃ t, e.1.mark = .conc t)

/-- No call binding edge of `P` has an `.any` target (the interpreter binds bases only,
    `interpreter.md` §3). W6T reads only STATEMENT micro edges, so a binding edge with an `.any`
    target would give a normal `.any` result with an abstract mark in run 1 (a FLOW
    `[any-taint]`, which decision 2 forbids). The kinds invariant of run 1 (`D6T_any_conc`) needs
    this hypothesis. -/
def BindNoAny (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    (∀ e, e ∈ c.toCallee → e.2.kind.isAny = false) ∧
    (∀ e, e ∈ c.fromCallee → e.2.kind.isAny = false)

/-- Rule W6T (DESIGN §3.1, ap.md §2.3 W6 with decision 1): the result `r` of the statement micro
    edge `e` goes to the demand layer if `e` has an `.any` target and is not a taint edge (a may
    `[any]`: a pass rule). A taint edge keeps its layer: its normal `.any` result is
    `[any-taint]`. -/
def w6t (taint : TaintEdges) (e : MicroEdge) (r : AFact) : AFact :=
  if e.2.kind.isAny && !taint e then ⟨r.fact, true⟩ else r

/-- One statement micro edge with W6T on each result. -/
def applyEdgeT (taint : TaintEdges) (c : AFact) (e : MicroEdge) : Res :=
  ⟨(applyEdge c e.1 e.2).facts.map (w6t taint e), (applyEdge c e.1 e.2).reqs⟩

/-- `applyAll` with W6T after each micro edge. -/
def applyAllT (taint : TaintEdges) (c : AFact) : List MicroEdge → Res
  | []      => Res.none
  | e :: es => (applyEdgeT taint c e).append (applyAllT taint c es)

/-- The statement transfer with W6T (ap.md §4.2): as `transfer`, with `w6t` after each
    `applyEdge`, then the field limit `limitF`. -/
def transferT (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : AFact) :
    Res :=
  if memB c.fact.base s.touched then
    let r := applyAllT taint c s.edges
    ⟨r.facts.map (limitF counted L), r.reqs⟩
  else ⟨[c], []⟩

/-! ### Small lemmas on W6T -/

theorem isAny_eq {k : Kind} (h : k.isAny = true) : k = .any := by
  cases k with
  | star e => cases h
  | any => rfl
  | exact => cases h

/-- W6T keeps the fact. -/
theorem w6t_fact (taint : TaintEdges) (e : MicroEdge) (r : AFact) :
    (w6t taint e r).fact = r.fact := by
  unfold w6t
  cases e.2.kind.isAny && !taint e <;> rfl

#print axioms w6t_fact

/-- W6T keeps the result, or raises it (only for a non-taint micro edge with an `.any` target). -/
theorem w6t_cases (taint : TaintEdges) (e : MicroEdge) (r : AFact) :
    w6t taint e r = r ∨
      (e.2.kind = .any ∧ taint e = false ∧ w6t taint e r = ⟨r.fact, true⟩) := by
  unfold w6t
  cases h : (e.2.kind.isAny && !taint e) with
  | false => exact Or.inl (if_neg Bool.false_ne_true)
  | true =>
    have h1 : e.2.kind.isAny = true := (Bool.and_eq_true _ _).mp h |>.1
    have h2 : (!taint e) = true := (Bool.and_eq_true _ _).mp h |>.2
    refine Or.inr ⟨isAny_eq h1, ?_, if_pos rfl⟩
    cases ht : taint e with
    | false => rfl
    | true => rw [ht] at h2; cases h2

#print axioms w6t_cases

/-- W6T never lowers the layer. -/
theorem w6t_demand (taint : TaintEdges) (e : MicroEdge) {r : AFact} (h : r.demand = true) :
    (w6t taint e r).demand = true := by
  rcases w6t_cases taint e r with e1 | ⟨_, _, e1⟩ <;> rw [e1]
  · exact h

#print axioms w6t_demand

/-- A taint edge: W6T keeps the result. -/
theorem w6t_taint {taint : TaintEdges} {e : MicroEdge} (h : taint e = true) (r : AFact) :
    w6t taint e r = r := by
  unfold w6t
  rw [h]
  cases e.2.kind.isAny <;> rfl

#print axioms w6t_taint

/-- A micro edge without an `.any` target: W6T keeps the result. -/
theorem w6t_not_any {taint : TaintEdges} {e : MicroEdge} (h : e.2.kind.isAny = false)
    (r : AFact) : w6t taint e r = r := by
  unfold w6t
  rw [h]
  rfl

#print axioms w6t_not_any

/-- The geometry with an `.any` target gives the `.any` tail. -/
theorem belowCase_any_target {ck fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (h : belowCase ck fk r tp .any = some (p, k, ap)) : k = .any := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true => rw [ha, if_pos rfl] at h; cases h; rfl

theorem aboveCase_any_target {ck fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (h : aboveCase ck fk r tp .any = some (p, k, ap)) : k = .any := by
  unfold aboveCase at h
  cases ha : admitsTailB ck r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true => rw [ha, if_pos rfl] at h; cases h; rfl

theorem geo_any_target {ck fk : Kind} {P q tp p : List Acc} {k : Kind} {ap : Bool}
    (h : CoreAux.geo ck fk P q tp .any = some (p, k, ap)) : k = .any := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r0 => rw [hrel] at h; exact aboveCase_any_target h
  | below r0 => rw [hrel] at h; exact belowCase_any_target h

/-- Every result of a micro edge with an `.any` target has the `.any` tail. -/
theorem applyEdge_any_target {c r : AFact} {fr to : PFact} (hto : to.kind = .any)
    (h : r ∈ (applyEdge c fr to).facts) : r.fact.kind = .any := by
  obtain ⟨p, k, ap, m, hg, _, rfl⟩ := Invariant.applyEdge_shape h
  rw [hto] at hg
  have hk : k = .any := geo_any_target hg
  subst hk
  rfl

#print axioms applyEdge_any_target

/-- W6T on a result of its own micro edge is in `W6.LE`: the same fact, the same or a raised
    layer, and a raised fact is not `*`. -/
theorem LE_w6t (taint : TaintEdges) {c x : AFact} {e : MicroEdge}
    (hx : x ∈ (applyEdge c e.1 e.2).facts) : W6.LE x (w6t taint e x) := by
  rcases w6t_cases taint e x with e1 | ⟨hk, _, e1⟩
  · rw [e1]; exact W6.LE.refl x
  · rw [e1]
    exact W6.LE.raise (by rw [applyEdge_any_target hk hx]; rfl)

#print axioms LE_w6t

theorem LL_map_self {xs : List AFact} {F : AFact → AFact}
    (h : ∀ x, x ∈ xs → W6.LE x (F x)) : W6.LL xs (xs.map F) := by
  induction xs with
  | nil => exact W6.LL.nil
  | cons x xs ih =>
    exact W6.LL.cons (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- `applyAllT` and `applyAll`: the same facts, the same or a raised layer, the same requests. -/
theorem applyAllT_LL (taint : TaintEdges) (c : AFact) :
    ∀ (es : List MicroEdge), W6.LL (applyAll c es).facts (applyAllT taint c es).facts ∧
      (applyAllT taint c es).reqs = (applyAll c es).reqs
  | [] => ⟨W6.LL.nil, rfl⟩
  | e :: es => by
    obtain ⟨h1, h2⟩ := applyAllT_LL taint c es
    refine ⟨W6.LL.append (LL_map_self (fun x hx => LE_w6t taint hx)) h1, ?_⟩
    show (applyEdge c e.1 e.2).reqs ++ (applyAllT taint c es).reqs =
      (applyEdge c e.1 e.2).reqs ++ (applyAll c es).reqs
    rw [h2]

#print axioms applyAllT_LL

/-- `transferT` and `transfer` (DESIGN §3.2): the same facts, element by element, with the same
    or a raised layer (`W6.LE`), and the same requests. -/
theorem transferT_LL (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) (s : Stmt)
    (c : AFact) :
    W6.LL (transfer counted L s c).facts (transferT taint counted L s c).facts ∧
    (transferT taint counted L s c).reqs = (transfer counted L s c).reqs := by
  unfold transfer transferT
  cases memB c.fact.base s.touched with
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact ⟨W6.LL.refl _, rfl⟩
  | true =>
    rw [if_pos rfl, if_pos rfl]
    obtain ⟨h1, h2⟩ := applyAllT_LL taint c s.edges
    exact ⟨h1.map (fun _ _ _ hxy => W6.limitF_LE hxy), h2⟩

#print axioms transferT_LL

/-- The requests of `transferT` are the requests of `transfer`. -/
theorem transferT_reqs (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) (s : Stmt)
    (c : AFact) : (transferT taint counted L s c).reqs = (transfer counted L s c).reqs :=
  (transferT_LL taint counted L s c).2

#print axioms transferT_reqs

/-- A result of `transferT` is a result of `transfer` in the same or a raised layer. -/
theorem transferT_mem {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c f' : AFact} (h : f' ∈ (transferT taint counted L s c).facts) :
    ∃ f, f ∈ (transfer counted L s c).facts ∧ W6.LE f f' :=
  (transferT_LL taint counted L s c).1.bwd h

#print axioms transferT_mem

/-- A result of `transfer` is a result of `transferT` in the same or a raised layer. -/
theorem transfer_memT {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c f : AFact} (h : f ∈ (transfer counted L s c).facts) :
    ∃ f', f' ∈ (transferT taint counted L s c).facts ∧ W6.LE f f' :=
  (transferT_LL taint counted L s c).1.fwd h

#print axioms transfer_memT

theorem LL_facts {xs ys : List AFact} (h : W6.LL xs ys) : xs.map AFact.fact = ys.map AFact.fact := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    show _ :: _ = _ :: _
    rw [hxy.fact, ih]

/-- `transferT` and `transfer` give the same facts, in the same order. -/
theorem transferT_facts_map (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (s : Stmt) (c : AFact) :
    (transferT taint counted L s c).facts.map AFact.fact = (transfer counted L s c).facts.map AFact.fact :=
  (LL_facts (transferT_LL taint counted L s c).1).symm

#print axioms transferT_facts_map

/-! ## 2. Run 1 with W6T: the closure `D6T` -/

section Closure6T
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- RUN 1 with W6T (DESIGN §3.2, ap.md §6.2): the rules of `D`, with `transferT` in place of
    `transfer` in `step` and `reqStmt`. Everything else is as `D` (run 1 has no must-premise,
    decision 6). -/
inductive D6T : Obj → Prop where
  | root {M} : M ∈ roots → D6T (.init M zeroFact)
  | start {M i} : D6T (.init M i) → D6T (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      D6T (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferT taint counted L s f).facts → D6T (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      D6T (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferT taint counted L s f).reqs → D6T (.req M i t)
  | pass {M i n f n' c} :
      D6T (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → D6T (.edge M i n' f)
  | added {M i n f n' c e a} :
      D6T (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      D6T (.added c.callee a.fact)
  | initA {m a} : D6T (.added m a) → D6T (.init m (α m a))
  | ret {M i n f n' c e1 a j g r e2 r'} :
      D6T (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      D6T (.init c.callee j) →
      applicable j a.fact = true →
      D6T (.edge c.callee j (P.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      D6T (.edge M i n' (limitF counted L r'))
  | reqSink {M i n f s t} :
      D6T (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      D6T (.req M i t)
  | answer {M i t a} :
      D6T (.req M i t) → D6T (.added M a) → a.mark = .conc t →
      overlapB a i = true → D6T (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      D6T (.req m j t) → D6T (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → D6T (.req M ic t)
  | vuln {M i n f s} :
      D6T (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      D6T (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      D6T (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → D6T (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      D6T (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs → D6T (.req M i t)
  | filt {M i n f n' b may} :
      D6T (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → D6T (.edge M i n' f)

/-- The normal-layer SUPPORT of the initial facts of `D6T`: `Confirmed.Sup` with `D6T` in place
    of `D` (ap.md §4.9 condition 3; the zero fact, or an exact concrete request answer that IS the
    normal added fact). -/
inductive Sup6T : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → Sup6T M zeroFact
  | call {M i n f n' c e a j} :
      Sup6T M i → D6T P taint counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D6T P taint counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D6T P taint counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j = a.fact)) →
      Sup6T c.callee j

/-- A CONFIRMED vulnerability of run 1 with W6T (ap.md §4.9 with F69): a NORMAL sink edge (not
    `complete`: a normal `.any` sink fact, an `[any-taint]`, can be confirmed) under a supported
    initial fact, with a triggered check. -/
def ConfirmedT6 (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D6T P taint counted L α sinks roots (.edge M i n f) ∧
    Sup6T P taint counted L α sinks roots M i ∧
    f.demand = false ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end Closure6T

/-! ## 3. The restricted forward run with must-premises -/

/-- Objects of a restricted forward run with must-premises. The `must` flag of a premise is the
    spec tail `[any-taint]` of the premise (DESIGN §1: a MUST-PREMISE; its edges hold when EVERY
    location of the premise carries the mark):
    * `init M j must`: an initial fact; `must = true` is the premise `[any-taint]`;
    * `edge M j must n f`: an edge of the premise `(j, must)`;
    * `added M a am`: an added fact; `am = true`: the added fact is `[any-taint]` (`.any` and in the
      normal layer on its link);
    * `req M j t`: a mark request. It has NO must flag: a restricted run has no request
      (`RExact.DR_no_request`), the answer of a request is never a must-premise, and without the
      flag the requests of `DRT` and `DR` are the same objects;
    * `vuln M n s demand`: a reported vulnerability and the layer of its sink edge. -/
inductive TObj where
  | init  (M : MethodId) (j : PFact) (must : Bool)
  | edge  (M : MethodId) (j : PFact) (must : Bool) (n : Node) (f : AFact)
  | added (M : MethodId) (a : PFact) (am : Bool)
  | req   (M : MethodId) (j : PFact) (t : Mark)
  | vuln  (M : MethodId) (n : Node) (s : PFact) (demand : Bool)

/-- The emission with the must flag (decision 8), for a given location emission `emit`: the
    emitted premise is a must-premise iff the added fact is `[any-taint]` (`am`) and the emitted
    premise has the `.any` tail. With `emit = emitM` this is the table of decision 8: `emitM`
    keeps the tail of the added fact for two `.any` tails (`meetK .any .any = .any`), and gives
    `$` / `*/E` for a `$` / `*/E` pattern (see the vectors `EmitVec`). -/
def emitTWith (emit : PFact → PFact → Option PFact) (d a : PFact) (am : Bool) :
    Option (PFact × Bool) :=
  (emit d a).map (fun j => (j, am && j.kind.isAny))

/-- The spec emission with the must flag (decision 8, ap.md §6.3): `emitTWith emitM`. -/
def emitT (d a : PFact) (am : Bool) : Option (PFact × Bool) :=
  (emitM d a).map (fun j => (j, am && j.kind.isAny))

theorem emitT_eq : emitT = emitTWith emitM := rfl

/-- The start fact (ap.md §6.5 with F69): a must-premise `(x, p, [any-taint], T)` starts as
    `(x, p, [any-taint], {}, T)` in the NORMAL layer (forward run, DESIGN §1); every other premise
    starts with `startFact`. -/
def startT (j : PFact) (must : Bool) : AFact :=
  if must then ⟨j, false⟩ else startFact j

/-- The layer of a record application (ap.md §4.3 R4 with F69, DESIGN §2 §4.3): a must record
    (`mj = true`) that applies by `applicable` only (the added fact lies inside the premise, and
    `sat` is false) gives a DEMAND result, because the must-premise needs every location. The
    result keeps its fact; only the layer goes up. In every other case the result is unchanged. -/
def recLayer (mj satOk : Bool) (x : AFact) : AFact :=
  if mj && !satOk then ⟨x.fact, true⟩ else x

section ClosureRT
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × Bool × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The RESTRICTED FORWARD RUN with must-premises (DESIGN §3.2). The rules of `DR`, with:
    * `root`: `init M zeroFact false`;
    * `start`: `startT` (a must-premise starts normal);
    * `step`, `reqStmt`: `transferT` (W6T);
    * `added`: the must flag `a.fact.kind.isAny && !a.demand` of the added fact (`[any-taint]` on
      the link);
    * `initR`: the emission `emitTWith emit` (the spec instance is `emit = emitM`, so `emitT`);
    * `ret`: as `DR` (`sat`, `restrict`); the must flag of the callee premise is only carried (the
      initial fact and the exit edge have the same flag), the layer of the result is as in `DR`;
    * `retRec`: the records `recs m (j, mj, g)` carry the must flag `mj`; a record applies if
      `sat j a` or `applicable j a`; a must record that applies by `applicable` only gives a
      demand result (`recLayer`);
    * the other rules lifted, the must flag carried (`answer` gives a non-must premise). -/
inductive DRT : TObj → Prop where
  | root {M} : M ∈ roots → DRT (.init M zeroFact false)
  | start {M j mj} : DRT (.init M j mj) → DRT (.edge M j mj (P.entry M) (startT j mj))
  | step {M i mi n f n' s f'} :
      DRT (.edge M i mi n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferT taint counted L s f).facts → DRT (.edge M i mi n' f')
  | reqStmt {M i mi n f n' s t} :
      DRT (.edge M i mi n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferT taint counted L s f).reqs → DRT (.req M i t)
  | pass {M i mi n f n' c} :
      DRT (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → DRT (.edge M i mi n' f)
  | added {M i mi n f n' c e a} :
      DRT (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DRT (.added c.callee a.fact (a.fact.kind.isAny && !a.demand))
  -- the abstraction follows the demand: only the emission table creates initial facts
  | initR {m a am d j mj} :
      DRT (.added m a am) → demand m d → emitTWith emit d.din a am = some (j, mj) →
      DRT (.init m j mj)
  -- a summary edge of the callee, restricted by a demand edge of the callee
  | ret {M i mi n f n' c e1 a j mj g d g' r e2 r'} :
      DRT (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DRT (.init c.callee j mj) →
      DRT (.edge c.callee j mj (P.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DRT (.edge M i mi n' (limitF counted L r'))
  -- a persisted record of the callee: `sat` or `applicable`; a must record by `applicable`
  -- only gives a demand result
  | retRec {M i mi n f n' c e1 a j mj g r e2 r'} :
      DRT (.edge M i mi n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, mj, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DRT (.edge M i mi n' (limitF counted L (recLayer mj (sat j a.fact) r')))
  | reqSink {M i mi n f s t} :
      DRT (.edge M i mi n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      DRT (.req M i t)
  | answer {M i t a am} :
      DRT (.req M i t) → DRT (.added M a am) → a.mark = .conc t →
      overlapB a i = true → DRT (.init M (answerInit i a t) false)
  | reqUp {m j t M ic mc n f n' c e a} :
      DRT (.req m j t) → DRT (.edge M ic mc n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DRT (.req M ic t)
  | vuln {M i mi n f s} :
      DRT (.edge M i mi n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DRT (.vuln M n s f.demand)
  | clean {M i mi n f n' cl f'} :
      DRT (.edge M i mi n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → DRT (.edge M i mi n' f')
  | reqClean {M i mi n f n' cl t} :
      DRT (.edge M i mi n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs → DRT (.req M i t)
  | filt {M i mi n f n' b may} :
      DRT (.edge M i mi n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → DRT (.edge M i mi n' f)

end ClosureRT

/-! ### Small lemmas on the new rules -/

theorem startT_false (j : PFact) : startT j false = startFact j := rfl

theorem startT_true (j : PFact) : startT j true = ⟨j, false⟩ := rfl

/-- A must-premise starts in the normal layer. -/
theorem startT_true_demand (j : PFact) : (startT j true).demand = false := rfl

/-- The start fact of `startT` has the fact of `startFact` if the premise has the `.any` tail or
    is not a must-premise. (Only the layer differs: `startFact` puts an `.any` premise in the
    demand layer, `startT` puts a must-premise in the normal layer.) -/
theorem startT_fact {j : PFact} {must : Bool} (h : j.kind = .any ∨ must = false) :
    (startT j must).fact = (startFact j).fact := by
  cases must with
  | false => rfl
  | true =>
    rcases h with hk | h
    · obtain ⟨b, p, k, m⟩ := j
      have hk' : k = .any := hk
      subst hk'
      cases m <;> rfl
    · cases h

#print axioms startT_fact

/-- The start fact keeps the premise mark. -/
theorem startT_mark (j : PFact) (must : Bool) : (startT j must).fact.mark = j.mark := by
  cases must with
  | false => exact Exact.startFact_mark j
  | true => rfl

#print axioms startT_mark

theorem emitTWith_some {emit : PFact → PFact → Option PFact} {d a j : PFact} {am mj : Bool}
    (h : emitTWith emit d a am = some (j, mj)) : emit d a = some j ∧ mj = (am && j.kind.isAny) := by
  unfold emitTWith at h
  cases he : emit d a with
  | none => rw [he] at h; cases h
  | some j0 =>
    rw [he] at h
    cases h
    exact ⟨rfl, rfl⟩

#print axioms emitTWith_some

theorem emitTWith_of {emit : PFact → PFact → Option PFact} {d a j : PFact} (h : emit d a = some j)
    (am : Bool) : emitTWith emit d a am = some (j, am && j.kind.isAny) := by
  unfold emitTWith
  rw [h]
  rfl

#print axioms emitTWith_of

/-- A must-premise has the `.any` tail. -/
theorem emitTWith_must_any {emit : PFact → PFact → Option PFact} {d a j : PFact} {am : Bool}
    (h : emitTWith emit d a am = some (j, true)) : j.kind = .any := by
  obtain ⟨_, hm⟩ := emitTWith_some h
  have h2 : j.kind.isAny = true := ((Bool.and_eq_true _ _).mp hm.symm).2
  exact isAny_eq h2

#print axioms emitTWith_must_any

theorem recLayer_fact (mj s : Bool) (x : AFact) : (recLayer mj s x).fact = x.fact := by
  unfold recLayer
  cases mj && !s <;> rfl

#print axioms recLayer_fact

/-- A non-must record, or an application by `sat`: `recLayer` keeps the result. -/
theorem recLayer_keep {mj s : Bool} (h : mj = false ∨ s = true) (x : AFact) : recLayer mj s x = x := by
  unfold recLayer
  rcases h with h | h <;> rw [h]
  · rfl
  · cases mj <;> rfl

#print axioms recLayer_keep

/-- `recLayer` never lowers the layer. -/
theorem recLayer_demand {mj s : Bool} {x : AFact} (h : x.demand = true) :
    (recLayer mj s x).demand = true := by
  unfold recLayer
  cases mj && !s with
  | false => exact h
  | true => rfl

#print axioms recLayer_demand

/-- The fact of the field limit does not read the layer. -/
theorem limitF_fact_eq {counted : Acc → Bool} {L : Nat} {f g : AFact} (h : f.fact = g.fact) :
    (limitF counted L f).fact = (limitF counted L g).fact := by
  unfold limitF
  rw [h]
  cases cutPath counted L g.fact.path with
  | none => exact h
  | some p => rfl

#print axioms limitF_fact_eq

/-- The conclusion of `retRec` has the fact of the conclusion of `DR.retRec`. -/
theorem limitF_recLayer_fact {counted : Acc → Bool} {L : Nat} (mj s : Bool) (x : AFact) :
    (limitF counted L (recLayer mj s x)).fact = (limitF counted L x).fact :=
  limitF_fact_eq (recLayer_fact mj s x)

#print axioms limitF_recLayer_fact

/-! ### The emission vectors: every cell of the table of decision 8

  Rows: the added fact `$` (`aE`), `[any]` (`aA` with `am = false`), `[any-taint]` (`aA` with
  `am = true`). Columns: the entry pattern `$` (`dE`), `*/E` (`dS`, backward only), `[any]`
  (`dA`), `[any-taint]` (`dA` again: in a demand pattern the tail `[any-taint]` is a label, DESIGN
  §1, so its model is the `.any` pattern). The result `(j, true)` is the premise `[any-taint]`,
  `(j, false)` with `j.kind = .any` is the premise `[any]`. The cells are at the same path ("at"
  row of ap.md §6.3); the vectors after them check the "below" and "above" rows (the deeper of the
  two chains). -/
namespace EmitVec

def aE : PFact := ⟨1, [], .exact, .conc 5⟩
def aA : PFact := ⟨1, [], .any, .conc 5⟩
def dE : PFact := ⟨1, [], .exact, .conc 5⟩
def dS : PFact := ⟨1, [], .star (.set [3]), .star⟩
def dA : PFact := ⟨1, [], .any, .conc 5⟩

def jE : PFact := ⟨1, [], .exact, .conc 5⟩
def jS : PFact := ⟨1, [], .star (.set [3]), .conc 5⟩
def jA : PFact := ⟨1, [], .any, .conc 5⟩

-- row `$`: `$` in every column
example : emitT dE aE false = some (jE, false) := by decide
example : emitT dS aE false = some (jE, false) := by decide
example : emitT dA aE false = some (jE, false) := by decide   -- pattern `[any]`
example : emitT dA aE false = some (jE, false) := by decide   -- pattern `[any-taint]` (label)
-- row `[any]`: `$`, `*/E`, `[any]`, `[any]`
example : emitT dE aA false = some (jE, false) := by decide
example : emitT dS aA false = some (jS, false) := by decide
example : emitT dA aA false = some (jA, false) := by decide
example : emitT dA aA false = some (jA, false) := by decide
-- row `[any-taint]`: `$`, `*/E`, `[any-taint]`, `[any-taint]`
example : emitT dE aA true = some (jE, false) := by decide
example : emitT dS aA true = some (jS, false) := by decide
example : emitT dA aA true = some (jA, true) := by decide
example : emitT dA aA true = some (jA, true) := by decide

-- the added fact deeper than the pattern (row "below"): the added fact itself, with its tail
example : emitT dA ⟨1, [7], .any, .conc 5⟩ true = some (⟨1, [7], .any, .conc 5⟩, true) := by decide
example : emitT dA ⟨1, [7], .any, .conc 5⟩ false = some (⟨1, [7], .any, .conc 5⟩, false) := by decide
example : emitT dS ⟨1, [7], .any, .conc 5⟩ true = some (⟨1, [7], .any, .conc 5⟩, true) := by decide
example : emitT dS ⟨1, [3], .any, .conc 5⟩ true = none := by decide   -- `*/{3}` does not admit `3`
example : emitT dE ⟨1, [7], .any, .conc 5⟩ true = none := by decide   -- `$` has no location below
example : emitT dA ⟨1, [7], .exact, .conc 5⟩ false = some (⟨1, [7], .exact, .conc 5⟩, false) := by
  decide
-- the pattern deeper than the added fact (row "above"): the demand chain with the pattern tail
example : emitT ⟨1, [7], .any, .conc 5⟩ aA true = some (⟨1, [7], .any, .conc 5⟩, true) := by decide
example : emitT ⟨1, [7], .any, .conc 5⟩ aA false = some (⟨1, [7], .any, .conc 5⟩, false) := by decide
example : emitT ⟨1, [7], .exact, .conc 5⟩ aA true = some (⟨1, [7], .exact, .conc 5⟩, false) := by
  decide
example : emitT ⟨1, [7], .star (.set [3]), .star⟩ aA true =
    some (⟨1, [7], .star (.set [3]), .conc 5⟩, false) := by decide
example : emitT ⟨1, [7], .any, .conc 5⟩ aE false = none := by decide   -- `$` above: no location
-- the mark: a `T` pattern needs the mark `T`; a `*` pattern copies the mark of the added fact
example : emitT dA ⟨1, [], .any, .conc 6⟩ true = none := by decide
example : emitT ⟨1, [], .any, .star⟩ ⟨1, [], .any, .conc 6⟩ true =
    some (⟨1, [], .any, .conc 6⟩, true) := by decide

end EmitVec

/-! ## 4. The predicates of the proof files -/

/-- The locations of a conclusion fact with a concrete mark (DESIGN §1): the base, the paths
    `f.path ++ τ` that the tail admits (`tailI f.kind τ`), the mark. A normal `[any-taint]`
    conclusion says that EVERY such location carries the mark. A conclusion with an abstract mark
    has no location here (a restricted run is concrete, `RExact.DR_concrete`). -/
def coversF (f : PFact) (l : Loc) : Prop :=
  l.base = f.base ∧ (∃ τ, l.path = f.path ++ τ ∧ tailI f.kind τ) ∧ ∃ t, f.mark = .conc t ∧ l.mark = t

/-- `coversF` is the location set `PFact.covers` of a concrete-mark fact. -/
theorem coversF_iff (f : PFact) (l : Loc) : coversF f l ↔ f.covers l ∧ ∃ t, f.mark = .conc t := by
  constructor
  · rintro ⟨hb, hp, t, ht, hm⟩
    refine ⟨⟨hb, hp, ?_⟩, t, ht⟩
    rw [ht]
    exact hm
  · rintro ⟨⟨hb, hp, hadm⟩, t, ht⟩
    rw [ht] at hadm
    exact ⟨hb, hp, t, ht, hadm⟩

#print axioms coversF_iff

/-- END-EXACT (DESIGN §1, the edges of a must-premise): every valid location `l` of the
    conclusion `f` at the node `n` of the method `M` gets the value of SOME valid location `l0` of
    the premise `i` (`i.covers l0`, `Flow P M l0 n l`). Not pair by pair: the start relates every
    `σ` to every `τ`. -/
def EndExact (P : Program) (ok : Loc → Prop) (M : MethodId) (i : PFact) (n : Node) (f : PFact) :
    Prop :=
  ∀ l, coversF f l → ok l → ∃ l0, i.covers l0 ∧ Flow P M l0 n l ∧ ok l0

/-- The exactness motive of `DRT` (DESIGN §3.2 `AnyTaintExact.lean`), for a normal-layer edge:
    * `must = false`: exactly `RExact.EdgeOKR` (an abstract premise mark gives an abstract final
      mark, and every pair of `den` to a valid end location is a real flow from a valid start);
    * `must = true`: the same first conjunct, and END-EXACT (`EndExact`).
    `True` for the other objects. -/
def EdgeOKT (P : Program) (ok : Loc → Prop) : TObj → Prop
  | .edge M i false n f => RExact.EdgeOKR P ok (.edge M i n f)
  | .edge M i true n f => f.demand = false →
      (Exact.absB i.mark = true → Exact.absB f.fact.mark = true) ∧ EndExact P ok M i n f.fact
  | _ => True

/-- The persisted records with must flags are exact (for valid locations): the motive `EdgeOKT`
    on each record (pair-exact for a non-must record, as `RExact.RecsExactV`; end-exact for a
    must record). -/
def RecsExactT (P : Program) (ok : Loc → Prop) (recs : MethodId → PFact × Bool × AFact → Prop) :
    Prop :=
  ∀ m j mj g, recs m (j, mj, g) → EdgeOKT P ok (.edge m j mj (P.exit m) g)

/-- The non-must records of an exact record set with must flags are exact in the sense of `DR`. -/
theorem RecsExactT.nonMust {P : Program} {ok : Loc → Prop}
    {recs : MethodId → PFact × Bool × AFact → Prop} (h : RecsExactT P ok recs) :
    RExact.RecsExactV P ok (fun m jg => recs m (jg.1, false, jg.2)) :=
  fun m j g hr => h m j false g hr

#print axioms RecsExactT.nonMust

/-- The satisfaction reads the premise as INSIDE the added fact (ap.md §4.3, restricted run): the
    location part of `a` covers `j`, and the premise mark is a sub-mark of the fact mark. A summary
    of a must-premise is exact only if the added fact has every location of the premise, so the
    exactness of `DRT.ret` for a generic `sat` needs this hypothesis. `satI` has it. -/
def SatInside (sat : PFact → PFact → Bool) : Prop :=
  ∀ j a, sat j a = true →
    coversB ⟨a.base, a.path, a.kind, .star⟩ j = true ∧ markSubB j.mark a.mark = true

theorem satI_inside : SatInside satI := by
  intro j a h
  exact ⟨RExact.bool_and_left h, RExact.bool_and_right h⟩

#print axioms satI_inside

/-- The link condition of the support (DESIGN §3.2 `SupT`): the normal added fact `a` gives the
    callee premise `(j, mj)` if
    * both are the zero fact; or
    * `a` is exact with a concrete mark, `j = a`, and `j` is not a must-premise; or
    * `a` is `[any-taint]` (`.any`, concrete mark; the caller checks the normal layer), `j` has the
      mark of `a` and lies inside `a` (`satI`), and `j` is exact and not must, or `j` has the
      `.any` tail and is a must-premise.
    (The equality of the marks is not in the brief: `satI` alone admits a premise with the mark
    `*`, whose locations with other marks are not real.) -/
def SupLink (a j : PFact) (mj : Bool) : Prop :=
  (j = zeroFact ∧ a = zeroFact) ∨
  (a.kind = .exact ∧ (∃ t, a.mark = .conc t) ∧ j = a ∧ mj = false) ∨
  (a.kind = .any ∧ (∃ t, a.mark = .conc t) ∧ j.mark = a.mark ∧ satI j a = true ∧
    ((j.kind = .exact ∧ mj = false) ∨ (j.kind = .any ∧ mj = true)))

section SupportT
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × Bool × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The normal-layer SUPPORT of the premises of `DRT` (ap.md §4.9 condition 3 with F69): the zero
    fact at a root; in a callee, a premise `(j, mj)` that a normal binding `a` of a normal caller
    edge with a supported premise gives (`SupLink`). A supported must-premise is `[any-taint]`
    inside an `[any-taint]` added fact, so every location of it is real. -/
inductive SupT : MethodId → PFact → Bool → Prop where
  | root {M} : M ∈ roots → SupT M zeroFact false
  | call {M i mi n f n' c e a j mj} :
      SupT M i mi →
      DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f) →
      f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DRT P taint counted L demand emit sat restrict recs sinks roots (.init c.callee j mj) →
      SupLink a.fact j mj →
      SupT c.callee j mj

/-- A CONFIRMED vulnerability of `DRT` (ap.md §4.9 with F69): a NORMAL sink edge (`f.demand =
    false`; it can be `[any-taint]`) under a supported premise, with a triggered check. -/
def ConfirmedT (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i mi f, DRT P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi n f) ∧
    SupT P taint counted L demand emit sat restrict recs sinks roots M i mi ∧
    f.demand = false ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end SupportT

/-! ## 5. The fact simulation with `DR` -/

/-- Forget the must flags. -/
def TObj.forget : TObj → Obj
  | .init M j _     => .init M j
  | .edge M j _ n f => .edge M j n f
  | .added M a _    => .added M a
  | .req M j t      => .req M j t
  | .vuln M n s d   => .vuln M n s d

/-- The same object up to the must flags and the layers: the same method, premise, node, fact,
    added fact, request or sink. -/
def SameFact : TObj → Obj → Prop
  | .init M j _,     .init M' j'       => M = M' ∧ j = j'
  | .edge M j _ n f, .edge M' j' n' f' => M = M' ∧ j = j' ∧ n = n' ∧ f.fact = f'.fact
  | .added M a _,    .added M' a'      => M = M' ∧ a = a'
  | .req M j t,      .req M' j' t'     => M = M' ∧ j = j' ∧ t = t'
  | .vuln M n s _,   .vuln M' n' s' _  => M = M' ∧ n = n' ∧ s = s'
  | _,               _                 => False

theorem sameFact_forget (o : TObj) : SameFact o o.forget := by
  cases o with
  | init M j _ => exact ⟨rfl, rfl⟩
  | edge M j _ n f => exact ⟨rfl, rfl, rfl, rfl⟩
  | added M a _ => exact ⟨rfl, rfl⟩
  | req M j t => exact ⟨rfl, rfl, rfl⟩
  | vuln M n s d => exact ⟨rfl, rfl, rfl⟩

#print axioms sameFact_forget

/-- The record set that `DR` reads for the records with must flags: the flags forgotten. -/
def recsDR (recs : MethodId → PFact × Bool × AFact → Prop) : MethodId → PFact × AFact → Prop :=
  fun m jg => ∃ mj, recs m (jg.1, mj, jg.2)

/-- The fact of a restriction result does not read the layer of the summary edge. The fact
    simulation needs it for a generic `restrict` (the layers of `DRT` and `DR` differ). -/
def RestrictFact (restrict : PFact → AFact → DemandEdge → Option AFact) : Prop :=
  ∀ j g g' d, g.fact = g'.fact → (restrict j g d).map AFact.fact = (restrict j g' d).map AFact.fact

theorem restrictConcU_fact {g g' : AFact} (p : PFact) (h : g.fact = g'.fact) :
    (restrictConcU g p).map AFact.fact = (restrictConcU g' p).map AFact.fact := by
  obtain ⟨gf, gd⟩ := g
  obtain ⟨gf', gd'⟩ := g'
  have e : gf = gf' := h
  subst e
  unfold restrictConcU
  dsimp only
  cases Nat.beq gf.base p.base with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl]
    cases relate p.path gf.path with
    | below r => dsimp only; cases admitsTailB p.kind r <;> rfl
    | above r => dsimp only; cases gf.kind <;> rfl
    | apart => rfl

#print axioms restrictConcU_fact

/-- The spec restriction `restrictU` satisfies `RestrictFact`. -/
theorem restrictU_fact : RestrictFact restrictU := by
  intro j g g' d h
  show (restrictWith restrictConcU j g d).map AFact.fact =
    (restrictWith restrictConcU j g' d).map AFact.fact
  unfold restrictWith
  cases d.dout with
  | none => rfl
  | some p =>
    dsimp only
    cases overlapB j d.din with
    | false => rfl
    | true => exact restrictConcU_fact p h

#print axioms restrictU_fact

/-- THE FACT SIMULATION (the statement; the proof file proves it, DESIGN §3.2): every object of
    `DRT` has an object of `DR` with the same fact (any layer), and conversely; `DR` reads the
    record set `recsDR recs`. Expected hypotheses: `EmitCopiesMark emit` (the run is concrete, so
    no `*` fact, and the normal form does not read the layer) and `RestrictFact restrict`. -/
def FactSim (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (demand : MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : MethodId → PFact × Bool × AFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Prop :=
  (∀ o, DRT P taint counted L demand emit sat restrict recs sinks roots o →
    ∃ o', DR P counted L demand emit sat restrict (recsDR recs) sinks roots o' ∧ SameFact o o') ∧
  (∀ o', DR P counted L demand emit sat restrict (recsDR recs) sinks roots o' →
    ∃ o, DRT P taint counted L demand emit sat restrict recs sinks roots o ∧ SameFact o o')

/-- The concreteness motive of `DRT`: `RExact.ConcObj` with the must flags forgotten (every
    premise, fact and added fact has a concrete mark; no request). -/
def ConcObjT (o : TObj) : Prop := RExact.ConcObj o.forget

/-- The kind invariant of the must flag: a must-premise has the `.any` tail (decision 6: an
    `[any-taint]` premise). -/
def MustAnyT : TObj → Prop
  | .init _ j true     => j.kind = .any
  | .edge _ j true _ _ => j.kind = .any
  | _                  => True

/-- The exit edges of a run with must flags, as a record set with must flags. -/
def exitRecsT (P : Program) (R : TObj → Prop) (m : MethodId) (x : PFact × Bool × AFact) : Prop :=
  R (.edge m x.1 x.2.1 (P.exit m) x.2.2)

/-- A record set without must flags (run 1, `D6T`: no must-premise) as non-must records. -/
def liftRecs (recs : MethodId → PFact × AFact → Prop) (m : MethodId) (x : PFact × Bool × AFact) :
    Prop :=
  x.2.1 = false ∧ recs m (x.1, x.2.2)

/-- Exact records without must flags are exact non-must records. -/
theorem liftRecs_exactT {P : Program} {ok : Loc → Prop} {recs : MethodId → PFact × AFact → Prop}
    (h : RExact.RecsExactV P ok recs) : RecsExactT P ok (liftRecs recs) := by
  intro m j mj g hr
  obtain ⟨hmj, hr'⟩ := hr
  have hmj' : mj = false := hmj
  subst hmj'
  exact h m j g hr'

#print axioms liftRecs_exactT

/-! ## 6. Sanity derivations

  One method, one statement: the micro edge `zero → zero` and the source `src : zero →
  (1, [], [any], 5)`. With `src` a taint edge, the source result is `[any-taint]` (normal) in run
  1 (`D6T`) and in a restricted run (`DRT`). With no taint edge (the same micro edge read as a
  pass rule, a may), W6T puts the result in the demand layer (`[any]`). -/
namespace Sanity

def src : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 5⟩)
def s : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), src]⟩
def P : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .stmt s, 1)]⟩
def taintSrc : MicroEdge → Bool := fun e => decide (e = src)
def noTaint : MicroEdge → Bool := fun _ => false
def cnt : Acc → Bool := fun _ => true
def fNormal : AFact := ⟨⟨1, [], .any, .conc 5⟩, false⟩
def fDemand : AFact := ⟨⟨1, [], .any, .conc 5⟩, true⟩

theorem transferT_src : fNormal ∈ (transferT taintSrc cnt 3 s ⟨zeroFact, false⟩).facts := by decide
theorem transferT_pass : fDemand ∈ (transferT noTaint cnt 3 s ⟨zeroFact, false⟩).facts := by decide
theorem transferT_pass_not_normal : fNormal ∉ (transferT noTaint cnt 3 s ⟨zeroFact, false⟩).facts := by
  decide
-- without W6T (`transfer`) the may result stays in the normal layer
theorem transfer_pass_normal : fNormal ∈ (transfer cnt 3 s ⟨zeroFact, false⟩).facts := by decide

theorem mem_P : ((0 : MethodId), (0 : Node), Instr.stmt s, (1 : Node)) ∈ P.edges :=
  List.mem_singleton.mpr rfl

/-- Run 1: the source result is a normal `[any-taint]` edge of `D6T`. -/
theorem d6t_src : D6T P taintSrc cnt 3 policy1 [] [0] (.edge 0 zeroFact 1 fNormal) :=
  D6T.step (D6T.start (D6T.root (List.mem_singleton.mpr rfl))) mem_P transferT_src

#print axioms d6t_src

/-- Run 1, the micro edge read as a pass rule: the result is in the demand layer. -/
theorem d6t_pass : D6T P noTaint cnt 3 policy1 [] [0] (.edge 0 zeroFact 1 fDemand) :=
  D6T.step (D6T.start (D6T.root (List.mem_singleton.mpr rfl))) mem_P transferT_pass

#print axioms d6t_pass

/-- A restricted run: the root is `init 0 zeroFact false`, and the source result is a normal
    `[any-taint]` edge of `DRT`. -/
theorem drt_src :
    DRT P taintSrc cnt 3 (fun _ _ => False) emitM satI restrictU (fun _ _ => False) [] [0]
      (.edge 0 zeroFact false 1 fNormal) :=
  DRT.step (DRT.start (DRT.root (List.mem_singleton.mpr rfl))) mem_P transferT_src

#print axioms drt_src

end Sanity

end ApSpec.AnyTaint
