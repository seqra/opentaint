/-
  ApSpec.ND — the non-distributive (ND) extension of the model: mark conjunctions and
  edges with a LIST of premises (spec §4.6). Run 1 only (the unrestricted closure). The
  restricted runs are concrete; the spec argues them.

  Contents:
    * `Conj`, `NProg`: conjunctive micro edges beside the instruction edges. A binary
      conjunction is enough: a k-ary conjunction `l1 ∧ … ∧ lk → z` is a chain of binary
      ones through fresh intermediate exact positions with fresh marks
      (`l1 ∧ l2 → z1`, `z1 ∧ l3 → z2`, …).
    * `TaintN`, `SupAll`: the concrete SUPPORT semantics (a mutual inductive). A location
      is tainted at a node together with the list of entry locations that its derivation
      needs. It contains `Flow` (`flow_taintN`).
    * `DN`: the abstract closure with premise lists, the conjunction rule `conj`/`reqConj`,
      and the ND summary application `ndOpen`/`ndBind`/`ndRet` (a STANDING partial match
      `npart`: one caller edge per callee premise, as the conjunction store of spec §8.9).
    * `ndInv_all` and its corollaries `ndConclusion_uncorrelated` (W7), `premises_ne_nil`,
      `edge_conc`, `req_abstract`.
    * `answer_loop`: a request on one position of a callee support is answered (a concrete
      initial fact) or it climbs to the caller; the coverage theorem applies again.
    * `nd_coverage` (with `nd_coverage_sup`, `call_step`): THE ND COVERAGE THEOREM.
      Corollaries `nd_coverage_unfolded`, `nd_coverage_single`, `nd_coverage_flow`,
      `nd_coverage_conc`.
    * `nd_vuln`, `nd_vuln_root`: the ND vulnerability theorems for a method with concrete
      premises and for a root.
    * `ReachN`, `ReachAll`: the vulnerability witness is a TREE; `reach_strong`,
      `nd_vuln_reach`, and `nd_vuln_found` (the `Reach` chain of the base model).
    * `D_sub_DN`: `DN` contains `D` (a single-premise edge is the list `[i]`).
    * `Example`: the `NDRule` sample of the code gives a normal-layer ND edge and a `vuln`.

  Design choices:
    * A premise list is a LIST (not a set): `P1 ++ P2` at a conjunction. Duplicates and order
      do not change the meaning of `∀ p ∈ P`; the code keeps a set.
    * The zero edge has the premise list `[zeroFact]`: the zero location is an ordinary
      support location (as `Reach` treats it). The code drops the zero premise (`{}`): the
      zero location is tainted in every context.
    * A request comes only from a single-premise edge. An edge with two or more premises has a
      concrete mark (W7), so a gate never asks it for a mark.
    * The sink check of an edge reads one premise `i ∈ P`; for a concrete-mark conclusion the
      check does not read the premise (`check_conc_indep`).
    * The conjunction result is in the demand layer only if an input is demand or its literal
      does not cover it (`conjLayer`). Literals on exclusive paths are the expected
      over-approximation of a path-insensitive engine; `TaintN` is path-insensitive in the same
      way. The exactness of the normal layer is in `ApSpec.NDExact`.
    * The target of a conjunction has a concrete mark and no `*` tail (`NProg.WF.target`).
    * The ND summary application is a chain of three rules over a standing partial match
      (`npart`) instead of one rule with a list of caller edges. The chain gives exactly the
      same edges, and `DN` stays one (not mutual) inductive.
    * The coverage theorem gives the edge keyed by EXACTLY the given initial facts (not only
      a sub-list of them).

  The import is `ApSpec.Core` only: the helpers of `ApSpec.Coverage` that this file needs
  are copied below in their version-5 form.
-/
import ApSpec.Core

namespace ApSpec.ND
open ApSpec

/-! ## 1. Programs with conjunctions -/

/-- A binary conjunctive micro edge `lit1 ∧ lit2 → target`. The intended literals are exact
    positions with concrete marks `(x, ρ, $, T1)`, `(y, π, $, T2)`; the target is
    `(z, κ, $, T)`. Only the target has a well-formedness condition (`NProg.WF`). -/
structure Conj where
  lit1   : PFact
  lit2   : PFact
  target : PFact

/-- A program with conjunctions. `(M, n, cj, n')` is a conjunctive gen edge from node `n` to
    node `n'` of method `M`, beside the instruction edge. (The interpreter places conjunctive
    SOURCE rules at call statements.) -/
structure NProg where
  prog  : Program
  conjs : List (MethodId × Node × Conj × Node)

/-- Well-formedness: the program is well formed, and the target of every conjunction has a
    concrete mark and no `*` tail (a `*` tail is the correlation with ONE premise). -/
structure NProg.WF (Q : NProg) : Prop where
  prog   : Q.prog.WF
  target : ∀ M n cj n', (M, n, cj, n') ∈ Q.conjs →
    (∃ T, cj.target.mark = .conc T) ∧ cj.target.kind.isStar = false

/-! ## 2. The concrete support semantics -/

mutual
/-- `TaintN Q M n l L0`: the value at `l` at node `n` of method `M` is tainted if every
    location of the SUPPORT `L0` is tainted at the entry of `M`. -/
inductive TaintN (Q : NProg) : MethodId → Node → Loc → List Loc → Prop where
  | start (M : MethodId) (l : Loc) : TaintN Q M (Q.prog.entry M) l [l]
  | step {M n l L0 n' l' s} :
      TaintN Q M n l L0 → (M, n, Instr.stmt s, n') ∈ Q.prog.edges → s.step l l' →
      TaintN Q M n' l' L0
  | pass {M n l L0 n' c} :
      TaintN Q M n l L0 → (M, n, Instr.call c, n') ∈ Q.prog.edges →
      memB l.base c.touched = false → TaintN Q M n' l L0
  | clean {M n l L0 n' cl} :
      TaintN Q M n l L0 → (M, n, Instr.clean cl, n') ∈ Q.prog.edges →
      cl.cleansB l = false → TaintN Q M n' l L0
  | filt {M n l L0 n' b may} :
      TaintN Q M n l L0 → (M, n, Instr.filt b may, n') ∈ Q.prog.edges →
      (l.base = b → may l.path = true) → TaintN Q M n' l L0
  -- the conjunction: both literals hold at `n`; the target is tainted at `n'`
  | conj {M n l1 L1 l2 L2 n' cj l'} :
      TaintN Q M n l1 L1 → TaintN Q M n l2 L2 → (M, n, cj, n') ∈ Q.conjs →
      cj.lit1.covers l1 → cj.lit2.covers l2 → cj.target.covers l' →
      TaintN Q M n' l' (L1 ++ L2)
  -- a call: a callee derivation whose every entry location is bound from a caller location
  -- tainted at the call node; the support is the concatenation of the caller supports
  | call {M n n' c K L0 l2 e2 l3} :
      (M, n, Instr.call c, n') ∈ Q.prog.edges →
      TaintN Q c.callee (Q.prog.exit c.callee) l2 K → SupAll Q M n c K L0 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 → TaintN Q M n' l3 L0

/-- `SupAll Q M n c K L0`: every callee entry location `k ∈ K` is bound (by a binding edge of
    the call `c`) from a caller location tainted at the node `n`; `L0` is the concatenation of
    the caller supports. -/
inductive SupAll (Q : NProg) : MethodId → Node → Call → List Loc → List Loc → Prop where
  | nil {M n c} : SupAll Q M n c [] []
  | cons {M n c lk Lk e1 k K L0} :
      TaintN Q M n lk Lk → e1 ∈ c.toCallee → den e1.1 e1.2 lk k →
      SupAll Q M n c K L0 → SupAll Q M n c (k :: K) (Lk ++ L0)
end

/-- The support semantics contains the data flow: a flow from `l0` has the support `[l0]`. -/
theorem flow_taintN {Q : NProg} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : Flow Q.prog M l0 n l) : TaintN Q M n l [l0] := by
  induction h with
  | start M l0 => exact .start M l0
  | step _ he hs ih => exact .step ih he hs
  | pass _ he hm ih => exact .pass ih he hm
  | call _ he he1 hd1 _ he2 hd2 ih ihc =>
    exact .call he ihc (.cons ih he1 hd1 .nil) he2 hd2
  | clean _ he hc ih => exact .clean ih he hc
  | filt _ he hf ih => exact .filt ih he hf

#print axioms flow_taintN

/-! ## 3. The abstract closure with premise lists -/

/-- Objects of the ND analysis result. `nedge M P n f`: an edge with the premise list `P`
    (a single-premise edge has `[i]`; the zero edge has `[zeroFact]`). `npart M n c n' rest P g`:
    a STANDING partial application of the callee ND summary `g` at the call `(M, n, c, n')`;
    the callee premises `rest` still need a caller edge, and `P` is the concatenation of the
    premise lists of the caller edges matched so far. -/
inductive NObj where
  | ninit  (M : MethodId) (i : PFact)
  | nedge  (M : MethodId) (P : List PFact) (n : Node) (f : AFact)
  | nadded (M : MethodId) (a : PFact)
  | nreq   (M : MethodId) (i : PFact) (t : Mark)
  | nvuln  (M : MethodId) (n : Node) (s : PFact) (demand : Bool)
  | npart  (M : MethodId) (n : Node) (c : Call) (n' : Node) (rest P : List PFact) (g : AFact)

/-- The parameters of a run: the program, the field limit, the abstraction, the sinks and
    the roots. -/
structure Ctx where
  Q       : NProg
  counted : Acc → Bool
  FL      : Nat
  α       : MethodId → PFact → PFact
  sinks   : List (MethodId × Node × PFact)
  roots   : List MethodId

/-- The layer of a conjunction result: the demand layer if an input is demand or its literal
    does not cover it (`!coversB lit f`: the input has a location that is not the literal's).
    The engine is path-insensitive: the literals can hold on paths that exclude each other
    (`if c then a := srcA else b := srcB; r := pass(a, b)`). This is the expected over-approximation, not a demand step: the
    reference semantics `TaintN` is path-insensitive in the same way (spec §4.6, F49). -/
def conjLayer (cj : Conj) (f1 f2 : AFact) : Bool :=
  f1.demand || f2.demand || !coversB cj.lit1 f1.fact || !coversB cj.lit2 f2.fact

/-- The conclusion of a conjunction: the target, uncorrelated (W7). -/
def conjFact (cj : Conj) (f1 f2 : AFact) : AFact := ⟨cj.target, conjLayer cj f1 f2⟩

/-- The ND analysis result: the least set of objects closed under the rules. The rules of
    `D` are lifted to premise lists. A request is raised only on a single-premise edge: an
    edge with two or more premises has a concrete mark (`ndConclusion_uncorrelated`), so it
    raises none. -/
inductive DN (X : Ctx) : NObj → Prop where
  | root {M} : M ∈ X.roots → DN X (.ninit M zeroFact)
  | start {M i} : DN X (.ninit M i) → DN X (.nedge M [i] (X.Q.prog.entry M) (startFact i))
  | step {M P n f n' s f'} :
      DN X (.nedge M P n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      f' ∈ (transfer X.counted X.FL s f).facts → DN X (.nedge M P n' f')
  | reqStmt {M i n f n' s t} :
      DN X (.nedge M [i] n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      t ∈ (transfer X.counted X.FL s f).reqs → DN X (.nreq M i t)
  | pass {M P n f n' c} :
      DN X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      memB f.fact.base c.touched = false → DN X (.nedge M P n' f)
  | added {M P n f n' c e a} :
      DN X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → DN X (.nadded c.callee a.fact)
  | initA {m a} : DN X (.nadded m a) → DN X (.ninit m (X.α m a))
  -- a single-premise callee summary keeps the premise list of the caller edge
  | ret {M P n f n' c e1 a j g r e2 r'} :
      DN X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DN X (.ninit c.callee j) → applicable j a.fact = true →
      DN X (.nedge c.callee [j] (X.Q.prog.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DN X (.nedge M P n' (limitF X.counted X.FL r'))
  -- an ND callee summary (two or more premises) opens a standing partial match at a call
  | ndOpen {M n c n' Pc g} :
      (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      DN X (.nedge c.callee Pc (X.Q.prog.exit c.callee) g) → 2 ≤ Pc.length →
      DN X (.npart M n c n' Pc [] g)
  -- one caller edge whose binding satisfies the next callee premise; its layer joins the
  -- layer of the partial match (the result is demand if a caller edge or the summary is)
  | ndBind {M n c n' p ps P g Pf f e1 a} :
      DN X (.npart M n c n' (p :: ps) P g) → DN X (.nedge M Pf n f) →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts → applicable p a.fact = true →
      DN X (.npart M n c n' ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩)
  -- every callee premise is matched: the conclusion is used as it is (no delta), bound back
  | ndRet {M n c n' P g e2 r} :
      DN X (.npart M n c n' [] P g) → e2 ∈ c.fromCallee →
      r ∈ (applyEdge g e2.1 e2.2).facts → DN X (.nedge M P n' (limitF X.counted X.FL r))
  | reqSink {M i n f s t} :
      DN X (.nedge M [i] n f) → (M, n, s) ∈ X.sinks → check i f s = .request t →
      DN X (.nreq M i t)
  | answer {M i t a} :
      DN X (.nreq M i t) → DN X (.nadded M a) → a.mark = .conc t →
      overlapB a i = true → DN X (.ninit M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DN X (.nreq m j t) → DN X (.nedge M [ic] n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DN X (.nreq M ic t)
  -- the sink check reads the mark of a premise only for a mark-abstract conclusion; an ND
  -- conclusion has a concrete mark, so the choice of the premise does not matter
  | vuln {M P n f s i} :
      DN X (.nedge M P n f) → (M, n, s) ∈ X.sinks → i ∈ P → check i f s = .triggered →
      DN X (.nvuln M n s f.demand)
  | clean {M P n f n' cl f'} :
      DN X (.nedge M P n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      f' ∈ (cleanRes cl f).facts → DN X (.nedge M P n' f')
  | reqClean {M i n f n' cl t} :
      DN X (.nedge M [i] n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      t ∈ (cleanRes cl f).reqs → DN X (.nreq M i t)
  | filt {M P n f n' b may} :
      DN X (.nedge M P n f) → (M, n, Instr.filt b may, n') ∈ X.Q.prog.edges →
      (f.fact.base = b → may f.fact.path = true) → DN X (.nedge M P n' f)
  -- the conjunction: one edge per literal; the premise lists are concatenated
  | conj {M P1 n f1 P2 f2 cj n'} :
      DN X (.nedge M P1 n f1) → DN X (.nedge M P2 n f2) → (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      DN X (.nedge M (P1 ++ P2) n' (conjFact cj f1 f2))
  -- a literal on a mark-abstract fact raises the request of the literal mark (run 1)
  | reqConj {M i n f cj n' lit t} :
      DN X (.nedge M [i] n f) → (M, n, cj, n') ∈ X.Q.conjs → (lit = cj.lit1 ∨ lit = cj.lit2) →
      overlapB f.fact lit = true → markGate lit.mark f.fact.mark = .req t → DN X (.nreq M i t)

/-! ## 4. Lists: pointwise alignment and positions -/

/-- `Al R I L`: the lists `I` and `L` have the same length and `R` holds at each position. -/
inductive Al {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Al R [] []
  | cons {a b as bs} : R a b → Al R as bs → Al R (a :: as) (b :: bs)

/-- `PairIn a b I L`: `a` and `b` are at the same position of `I` and `L`. -/
inductive PairIn {α β : Type} : α → β → List α → List β → Prop where
  | head {a b as bs} : PairIn a b (a :: as) (b :: bs)
  | tail {a b a' b' as bs} : PairIn a b as bs → PairIn a b (a' :: as) (b' :: bs)

namespace Al
variable {α β : Type} {R : α → β → Prop}

theorem length : ∀ {I : List α} {L : List β}, Al R I L → I.length = L.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by
    show _ + 1 = _ + 1
    rw [length h]

theorem append : ∀ {I1 : List α} {L1 : List β} {I2 L2}, Al R I1 L1 → Al R I2 L2 →
    Al R (I1 ++ I2) (L1 ++ L2)
  | _, _, _, _, .nil, h2 => h2
  | _, _, _, _, .cons h h1, h2 => .cons h (append h1 h2)

theorem split : ∀ {L1 : List β} {L2 : List β} {I : List α}, Al R I (L1 ++ L2) →
    ∃ I1 I2, I = I1 ++ I2 ∧ Al R I1 L1 ∧ Al R I2 L2
  | [], _, I, h => ⟨[], I, rfl, .nil, h⟩
  | _ :: L1, _, _, .cons hab h => by
    obtain ⟨I1, I2, he, h1, h2⟩ := split h
    exact ⟨_ :: I1, I2, by rw [he]; rfl, .cons hab h1, h2⟩

theorem get : ∀ {I : List α} {L : List β} {a b}, Al R I L → PairIn a b I L → R a b
  | _, _, _, _, .cons h _, .head => h
  | _, _, _, _, .cons _ h, .tail hp => get h hp

theorem single {i : α} {L : List β} (h : Al R [i] L) : ∃ l, L = [l] ∧ R i l := by
  cases h with
  | cons hr hn =>
    cases hn with
    | nil => exact ⟨_, rfl, hr⟩

theorem nil_right {I : List α} (h : Al R I ([] : List β)) : I = [] := by
  cases h
  rfl

theorem map {γ : Type} {R' : α → γ → Prop} {f : β → γ} (hf : ∀ a b, R a b → R' a (f b)) :
    ∀ {I : List α} {L : List β}, Al R I L → Al R' I (L.map f)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hf _ _ h) (map hf hs)

theorem of_map {γ : Type} {R' : α → γ → Prop} {f : γ → α} :
    ∀ {L : List γ}, (∀ b, b ∈ L → R' (f b) b) → Al R' (L.map f) L
  | [], _ => .nil
  | _ :: _, hf => .cons (hf _ List.mem_cons_self)
      (of_map (fun b hb => hf b (List.mem_cons_of_mem _ hb)))

theorem singleton_right {i : β} {I : List α} (h : Al R I [i]) : ∃ a, I = [a] ∧ R a i := by
  cases h with
  | cons hr hn =>
    cases hn with
    | nil => exact ⟨_, rfl, hr⟩

theorem mono {R' : α → β → Prop} (hf : ∀ a b, R a b → R' a b) :
    ∀ {I : List α} {L : List β}, Al R I L → Al R' I L
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hf _ _ h) (mono hf hs)

end Al

namespace PairIn
variable {α β : Type}

theorem appL {a : α} {b : β} : ∀ {I1 L1} (I2 : List α) (L2 : List β), PairIn a b I1 L1 →
    PairIn a b (I1 ++ I2) (L1 ++ L2)
  | _, _, _, _, .head => .head
  | _, _, I2, L2, .tail h => .tail (appL I2 L2 h)

theorem appR {a : α} {b : β} {I2 : List α} {L2 : List β} : ∀ {I1 : List α} {L1 : List β},
    I1.length = L1.length → PairIn a b I2 L2 → PairIn a b (I1 ++ I2) (L1 ++ L2)
  | [], [], _, h => h
  | _ :: _, [], hl, _ => nomatch hl
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, _ :: _, hl, h => .tail (appR (Nat.succ.inj hl) h)

theorem mem_left {a : α} {b : β} : ∀ {I L}, PairIn a b I L → a ∈ I
  | _, _, .head => List.mem_cons_self
  | _, _, .tail h => List.mem_cons_of_mem _ (mem_left h)

theorem mem_right {a : α} {b : β} : ∀ {I L}, PairIn a b I L → b ∈ L
  | _, _, .head => List.mem_cons_self
  | _, _, .tail h => List.mem_cons_of_mem _ (mem_right h)

/-- A position in a mapped list is the image of a position. -/
theorem of_map {γ : Type} {f : γ → β} {a : α} {b : β} :
    ∀ {I : List α} {S : List γ}, PairIn a b I (S.map f) → ∃ s, PairIn a s I S ∧ b = f s := by
  intro I S h
  induction S generalizing I with
  | nil => cases h
  | cons s S ih =>
    cases h with
    | head => exact ⟨s, .head, rfl⟩
    | tail h =>
      obtain ⟨s', hs, hb⟩ := ih h
      exact ⟨s', .tail hs, hb⟩

/-- A position inside the block of one element of `S` is a position of the flattened lists. -/
theorem flat {γ : Type} {f : γ → List α} {g : γ → List β} {a : α} {b : β} :
    ∀ {S : List γ} {s : γ}, s ∈ S → (∀ s, s ∈ S → (f s).length = (g s).length) →
    PairIn a b (f s) (g s) → PairIn a b (S.map f).flatten (S.map g).flatten
  | [], _, hs, _, _ => absurd hs List.not_mem_nil
  | s' :: S, s, hs, hl, h => by
    show PairIn a b (f s' ++ (S.map f).flatten) (g s' ++ (S.map g).flatten)
    rcases List.mem_cons.mp hs with he | he
    · rw [he] at h
      exact appL _ _ h
    · exact appR (hl s' List.mem_cons_self)
        (flat he (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h)

end PairIn

/-! ## 5. Small facts about marks and the local operations -/

/-- A mark is concrete or not. -/
theorem mark_dich (m : MarkA) : (∃ t, m = .conc t) ∨ ∀ t, m ≠ .conc t := by
  cases m with
  | conc t => exact .inl ⟨t, rfl⟩
  | star => exact .inr (fun _ h => MarkA.noConfusion h)
  | starEx _ => exact .inr (fun _ h => MarkA.noConfusion h)

/-- Every fact relates each of its locations to itself (the fact read as its own premise). -/
theorem den_refl {f : PFact} {l : Loc} (h : f.covers l) : den f f l l := by
  obtain ⟨hb, ⟨σ, hp, ht⟩, hm⟩ := h
  have hps : f.mark.passes l.mark := CoreAux.passes_of_admits hm
  refine ⟨hb, hb, hm, CoreAux.out_of_admits hm, hps, σ, σ, hp, hp, ht, ?_⟩
  obtain ⟨b, p, k, m⟩ := f
  cases k with
  | star e => exact ⟨rfl, ht⟩
  | any => trivial
  | exact => exact ht

/-- The zero fact covers the zero location. -/
theorem zeroFact_covers : zeroFact.covers zeroLoc := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

/-- A concrete mark on an abstract-premise gate: the gate asks only of an abstract fact. -/
theorem gate_req_abs {fm cm : MarkA} {t : Mark} (h : markGate fm cm = .req t) :
    ∀ t', cm ≠ .conc t' := by
  intro t' hc
  subst hc
  cases fm with
  | star => exact Gate.noConfusion h
  | starEx _ => exact Gate.noConfusion h
  | conc t0 =>
    have h' : (if Nat.beq t0 t' = true then Gate.ok else Gate.no) = Gate.req t := h
    cases hq : Nat.beq t0 t' with
    | true => rw [hq, if_pos rfl] at h'; exact Gate.noConfusion h'
    | false => rw [hq, if_neg Bool.false_ne_true] at h'; exact Gate.noConfusion h'

/-- The binding into the callee raises no request (WF: it is mark agnostic). -/
theorem bind_in {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he1 : e ∈ c.toCallee)
    {i : PFact} {f : AFact} {l0 l l1 : Loc}
    (hd : den i f.fact l0 l) (hd1 : den e.1 e.2 l l1) :
    ∃ a, a ∈ (applyEdge f e.1 e.2).facts ∧ den i a.fact l0 l1 := by
  rcases applyEdge_sound hd hd1 with h | ⟨_, hq⟩
  · exact h
  · rw [applyEdge_reqs_of_star (hwf.toStar M n c n' he e he1)] at hq
    cases hq

/-- The binding back from the callee raises no request (WF: it is mark agnostic). -/
theorem bind_out {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he2 : e ∈ c.fromCallee)
    {i : PFact} {r : AFact} {l0 l l1 : Loc}
    (hd : den i r.fact l0 l) (hd2 : den e.1 e.2 l l1) :
    ∃ r', r' ∈ (applyEdge r e.1 e.2).facts ∧ den i r'.fact l0 l1 := by
  rcases applyEdge_sound hd hd2 with h | ⟨_, hq⟩
  · exact h
  · rw [applyEdge_reqs_of_star (hwf.fromStar M n c n' he e he2)] at hq
    cases hq

/-- An applicable summary raises no request (version 5: a `*∖x` premise passes the gate). -/
theorem summary_step {i j : PFact} {a g : AFact} {l0 l1 l2 : Loc}
    (hap : applicable j a.fact = true) (hda : den i a.fact l0 l1) (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    have hq' : l0.mark ∈ (applyEdge a j g.fact).reqs := hq
    have hnr : ∀ t, markGate j.mark a.fact.mark ≠ .req t := by
      intro t ht
      cases hj : j.mark with
      | star => rw [hj] at ht; exact Gate.noConfusion ht
      | starEx _ => rw [hj] at ht; exact Gate.noConfusion ht
      | conc t0 => exact hst t0 (applicable_mark hap hj)
    rw [CoreAux.reqs_of_gate hnr] at hq'
    cases hq'

/-- The normal form of a concrete-mark fact has no `*` tail (W2). -/
theorem norm_conc_nonstar {f : AFact} {t : Mark} (h : f.fact.mark = .conc t) :
    f.norm.fact.kind.isStar = false := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := f
  have hm : m = .conc t := h
  subst hm
  cases k with
  | star e => cases e <;> cases d <;> rfl
  | any => rfl
  | exact => rfl

/-- A result of `applyEdge` on a concrete-mark fact has no `*` tail. -/
theorem applyEdge_nonstar {c r : AFact} {fr to : PFact} {t : Mark}
    (hc : c.fact.mark = .conc t) (hr : r ∈ (applyEdge c fr to).facts) :
    r.fact.kind.isStar = false := by
  obtain ⟨p, k, ap, m, _, _, hmc, hre⟩ := CoreAux.mem_applyEdge_facts_inv hr
  rw [hc] at hmc
  obtain ⟨t', ht'⟩ := CoreAux.markComp_conc hmc
  rw [hre]
  exact norm_conc_nonstar (t := t') ht'

/-- The field limit keeps a fact without a `*` tail without one. -/
theorem limitF_nonstar {counted : Acc → Bool} {FL : Nat} {f : AFact}
    (h : f.fact.kind.isStar = false) : (limitF counted FL f).fact.kind.isStar = false := by
  unfold limitF
  cases cutPath counted FL f.fact.path with
  | none => exact h
  | some _ => rfl

/-- The statement transfer keeps a concrete-mark fact without a `*` tail without one. -/
theorem transfer_nonstar {counted : Acc → Bool} {FL : Nat} {s : Stmt} {c r : AFact} {t : Mark}
    (hc : c.fact.mark = .conc t) (hk : c.fact.kind.isStar = false)
    (hr : r ∈ (transfer counted FL s c).facts) : r.fact.kind.isStar = false := by
  unfold transfer at hr
  cases hb : memB c.fact.base s.touched with
  | true =>
    rw [hb, if_pos rfl] at hr
    obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hr
    obtain ⟨e, _, hxe⟩ := CoreAux.applyAll_facts_inv hx
    rw [← hxr]
    exact limitF_nonstar (applyEdge_nonstar hc hxe)
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at hr
    rw [List.mem_singleton.mp hr]
    exact hk

/-- The cleaner keeps a concrete-mark fact without a `*` tail without one. -/
theorem cleanRes_nonstar {cl : Cleaner} {c r : AFact} {t : Mark}
    (hc : c.fact.mark = .conc t) (hk : c.fact.kind.isStar = false)
    (hr : r ∈ (cleanRes cl c).facts) : r.fact.kind.isStar = false := by
  unfold cleanRes at hr
  cases hpos : cleanPos cl c.fact with
  | disjoint =>
    rw [hpos] at hr
    rw [List.mem_singleton.mp hr]
    exact hk
  | inside =>
    rw [hpos, hc] at hr
    have h' : r ∈ (if cl.markB t = true then Res.none else (⟨[c], []⟩ : Res)).facts := hr
    cases hmt : cl.markB t with
    | true => rw [hmt, if_pos rfl] at h'; exact absurd h' List.not_mem_nil
    | false =>
      rw [hmt, if_neg Bool.false_ne_true] at h'
      rw [List.mem_singleton.mp h']
      exact hk
  | part =>
    rw [hpos, hc] at hr
    have h' : r ∈ (if cl.markB t = true then (⟨[concPart cl c], []⟩ : Res)
      else ⟨[c], []⟩).facts := hr
    cases hmt : cl.markB t with
    | true =>
      rw [hmt, if_pos rfl] at h'
      rw [List.mem_singleton.mp h']
      unfold concPart
      obtain ⟨⟨b, p, k, m⟩, d⟩ := c
      cases k with
      | star e => exact Bool.noConfusion hk
      | any =>
        cases cl.reach <;> (try rfl)
        cases relate cl.path p with
        | below r => cases r <;> rfl
        | above _ => rfl
        | apart => rfl
      | exact => rfl
    | false =>
      rw [hmt, if_neg Bool.false_ne_true] at h'
      rw [List.mem_singleton.mp h']
      exact hk

/-- The sink check of a concrete-mark conclusion does not read the premise. -/
theorem check_conc_indep {i i' s : PFact} {f : AFact} {t : Mark} (h : f.fact.mark = .conc t) :
    check i f s = check i' f s := by
  unfold check
  rw [h]

/-- Two non-empty lists have a concatenation that is not a singleton. -/
theorem app_ne_single {α : Type} {A B : List α} {i : α} (hA : A ≠ []) (hB : B ≠ []) :
    A ++ B ≠ [i] := by
  intro h
  cases A with
  | nil => exact hA rfl
  | cons a A' =>
    have h' : A' ++ B = [] := (List.cons.inj h).2
    exact hB (List.append_eq_nil_iff.mp h').2

/-! ## 6. Invariants of `DN` -/

/-- The edge invariant: the premise list is not empty; a concrete-mark single premise gives a
    concrete-mark conclusion; an ND conclusion (two or more premises) has a concrete mark and no
    `*` tail (W7). -/
abbrev EdgeOK (P : List PFact) (f : AFact) : Prop :=
  P ≠ [] ∧ (∀ i t, P = [i] → i.mark = .conc t → ∃ t', f.fact.mark = .conc t') ∧
    (2 ≤ P.length → (∃ t, f.fact.mark = .conc t) ∧ f.fact.kind.isStar = false)

/-- The partial match invariant: the callee ND conclusion has a concrete mark and no `*` tail,
    and the final premise list will have two or more premises. -/
abbrev PartOK (rest P : List PFact) (g : AFact) : Prop :=
  (∃ t, g.fact.mark = .conc t) ∧ g.fact.kind.isStar = false ∧ 2 ≤ P.length + rest.length

/-- The request invariant: a request is on a mark-abstract premise. -/
abbrev ReqOK (i : PFact) : Prop := ∀ t, i.mark ≠ .conc t

def NInv : NObj → Prop
  | .nedge _ P _ f => EdgeOK P f
  | .npart _ _ _ _ rest P g => PartOK rest P g
  | .nreq _ i _ => ReqOK i
  | _ => True

theorem ndInv_all {X : Ctx} (hwf : X.Q.WF) {o : NObj} (h : DN X o) : NInv o := by
  induction h with
  | root _ => trivial
  | @start M i _ _ =>
    show EdgeOK [i] (startFact i)
    refine ⟨List.cons_ne_nil _ _, fun i' t hP ht => ⟨t, ?_⟩, fun h2 => absurd h2 (Nat.not_succ_le_self 1)⟩
    rw [startFact_mark, (List.cons.inj hP).1]
    exact ht
  | step _ _ hf' ih =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      exact transfer_mark_conc h1 hf'
    · obtain ⟨⟨t1, h1⟩, hk⟩ := hnd h2
      exact ⟨transfer_mark_conc h1 hf', transfer_nonstar h1 hk hf'⟩
  | @reqStmt M i n f n' s t _ _ hq ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    rw [transfer_reqs_of_conc h1] at hq
    exact List.not_mem_nil hq
  | pass _ _ _ ih => exact ih
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
      obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
      exact ⟨t4, by rw [limitF_mark]; exact h4⟩
    · obtain ⟨⟨t1, h1⟩, _⟩ := hnd h2
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
      obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
      exact ⟨⟨t4, by rw [limitF_mark]; exact h4⟩, limitF_nonstar (applyEdge_nonstar h3 hr')⟩
  | @ndOpen M n c n' Pc g _ _ h2 ih =>
    show PartOK Pc [] g
    obtain ⟨_, _, hnd⟩ := ih
    obtain ⟨hc, hk⟩ := hnd h2
    refine ⟨hc, hk, ?_⟩
    rw [List.length_nil, Nat.zero_add]
    exact h2
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ _ _ _ ihp ihf =>
    show PartOK ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩
    obtain ⟨hc, hk, hlen⟩ := ihp
    obtain ⟨hne, _, _⟩ := ihf
    refine ⟨hc, hk, ?_⟩
    have h1 : 0 < Pf.length := List.length_pos_iff.mpr hne
    have h2 : (p :: ps).length = ps.length + 1 := rfl
    rw [List.length_append]
    omega
  | @ndRet M n c n' P g e2 r _ _ hr ih =>
    show EdgeOK P (limitF X.counted X.FL r)
    obtain ⟨⟨t, ht⟩, _, hlen⟩ := ih
    have h2 : 2 ≤ P.length := hlen
    refine ⟨fun he => ?_, fun i t' hP _ => ?_, fun _ => ?_⟩
    · rw [he] at h2
      exact absurd h2 (by decide)
    · rw [hP] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)
    · obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht hr
      exact ⟨⟨t1, by rw [limitF_mark]; exact h1⟩, limitF_nonstar (applyEdge_nonstar ht hr)⟩
  | reqSink _ _ hc _ => exact check_request_star hc
  | answer _ _ _ _ _ _ => trivial
  | @reqUp m j t M ic n f n' c e a _ _ _ _ _ ha hcl _ _ ihf =>
    show ReqOK ic
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ihf
    obtain ⟨t1, h1⟩ := hs ic t0 rfl ht0
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    exact climbsB_abs hcl t2 h2
  | vuln _ _ _ _ _ => trivial
  | clean _ _ hf' ih =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      exact cleanRes_mark_conc h1 hf'
    · obtain ⟨⟨t1, h1⟩, hk⟩ := hnd h2
      exact ⟨cleanRes_mark_conc h1 hf', cleanRes_nonstar h1 hk hf'⟩
  | @reqClean M i n f n' cl t _ _ hq ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    exact (cleanRes_reqs_abstract hq).1 t1 h1
  | filt _ _ _ ih => exact ih
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj _ _ _ _ ih1 ih2 =>
    show EdgeOK (P1 ++ P2) (conjFact cj f1 f2)
    obtain ⟨hne1, _, _⟩ := ih1
    obtain ⟨hne2, _, _⟩ := ih2
    obtain ⟨hT, hk⟩ := hwf.target _ _ _ _ hcj
    refine ⟨fun he => hne1 (List.append_eq_nil_iff.mp he).1,
      fun i t hP _ => absurd hP (app_ne_single hne1 hne2), fun _ => ⟨hT, hk⟩⟩
  | @reqConj M i n f cj n' lit t _ _ _ _ hg ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    exact gate_req_abs hg t1 h1

/-- W7, the strongest true form: an ND conclusion (two or more premises) has no `*` tail, and
    its mark is concrete. -/
theorem ndConclusion_uncorrelated {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DN X (.nedge M P n f)) (h2 : 2 ≤ P.length) :
    f.fact.kind.isStar = false ∧ ∃ t, f.fact.mark = .conc t :=
  let ⟨_, _, hnd⟩ := (ndInv_all hwf h : EdgeOK P f)
  ⟨(hnd h2).2, (hnd h2).1⟩

#print axioms ndConclusion_uncorrelated

/-- Every premise list is not empty. -/
theorem premises_ne_nil {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DN X (.nedge M P n f)) : P ≠ [] :=
  (ndInv_all hwf h : EdgeOK P f).1

#print axioms premises_ne_nil

/-- A concrete-mark single premise gives a concrete-mark conclusion. -/
theorem edge_conc {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {t : Mark} (h : DN X (.nedge M [i] n f)) (ht : i.mark = .conc t) :
    ∃ t', f.fact.mark = .conc t' :=
  (ndInv_all hwf h : EdgeOK [i] f).2.1 i t rfl ht

#print axioms edge_conc

/-- Every request is on a mark-abstract premise. -/
theorem req_abstract {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {i : PFact} {t : Mark}
    (h : DN X (.nreq M i t)) : ∀ t', i.mark ≠ .conc t' :=
  (ndInv_all hwf h : ReqOK i)

#print axioms req_abstract

/-- A mark-abstract conclusion has exactly one premise; its support has one location. -/
theorem single_of_abs {X : Ctx} (hwf : X.Q.WF) {β : Type} {R : PFact → β → Prop}
    {M : MethodId} {I : List PFact} {n : Node} {f : AFact} {L0 : List β}
    (h : DN X (.nedge M I n f)) (habs : ∀ t, f.fact.mark ≠ .conc t) (hI : Al R I L0) :
    ∃ i l0, I = [i] ∧ L0 = [l0] := by
  obtain ⟨hne, _, hnd⟩ := (ndInv_all hwf h : EdgeOK I f)
  match I, hI with
  | [], _ => exact absurd rfl hne
  | [i], hI =>
    obtain ⟨l0, hL, _⟩ := Al.single hI
    exact ⟨i, l0, rfl, hL⟩
  | _ :: _ :: _, _ =>
    obtain ⟨⟨t, ht⟩, _⟩ := hnd (by show 2 ≤ _ + 1 + 1; omega)
    exact absurd ht (habs t)

/-! ## 7. The answer loop

A callee derivation has one entry location per position; each position has its own initial
fact. A request on one position is answered (the answer has a concrete mark) or it climbs to
the caller. After an answer the coverage theorem of the callee applies again; a new request
can come at another position. Each answer replaces a mark-abstract initial fact by a
concrete one, and a request is only on a mark-abstract initial fact. So the loop stops. -/

/-- The number of mark-abstract facts in a list. -/
def absOne : MarkA → Nat
  | .conc _ => 0
  | _ => 1

def absCount : List PFact → Nat
  | [] => 0
  | j :: js => absOne j.mark + absCount js

theorem absOne_abs {m : MarkA} (h : ∀ t, m ≠ .conc t) : absOne m = 1 := by
  cases m with
  | conc t => exact absurd rfl (h t)
  | star => rfl
  | starEx _ => rfl

theorem absOne_conc {m : MarkA} {t : Mark} (h : m = .conc t) : absOne m = 0 := by
  rw [h]
  rfl

/-- Replace a mark-abstract fact at a position by a concrete one: the count goes down. -/
theorem replace_pos {σ : Type} {R : PFact → σ → Prop} {j j' : PFact} {s : σ}
    (hj : ∀ t, j.mark ≠ .conc t) (hj' : ∃ t, j'.mark = .conc t) (hR : R j' s) :
    ∀ {Ic : List PFact} {S : List σ}, PairIn j s Ic S → Al R Ic S →
      ∃ Ic', Al R Ic' S ∧ absCount Ic' < absCount Ic
  | _, _, .head, .cons _ hAl => by
    obtain ⟨t, ht⟩ := hj'
    refine ⟨j' :: _, .cons hR hAl, ?_⟩
    show absOne j'.mark + _ < absOne j.mark + _
    rw [absOne_conc ht, absOne_abs hj, Nat.zero_add, Nat.add_comm 1]
    exact Nat.lt_succ_self _
  | _, _, .tail hp, .cons hr hAl => by
    obtain ⟨Ic', hAl', hlt⟩ := replace_pos hj hj' hR hp hAl
    refine ⟨_ :: Ic', .cons hr hAl', ?_⟩
    show absOne _ + absCount Ic' < absOne _ + absCount _
    exact Nat.add_lt_add_left hlt _

/-- THE LOOP. `orc` is the coverage theorem of the callee for every choice of initial facts,
    `ans` answers a request (or gives `Bad`: the request climbed to the caller). -/
theorem answer_loop {σ : Type} {S : List σ} {R : PFact → σ → Prop}
    {Goal : List PFact → Prop} {Req : PFact → σ → Prop} {Bad : Prop}
    (orc : ∀ Ic, Al R Ic S → Goal Ic ∨ ∃ j s, PairIn j s Ic S ∧ Req j s)
    (abs : ∀ j s, Req j s → ∀ t, j.mark ≠ .conc t)
    (ans : ∀ j s, s ∈ S → R j s → Req j s → Bad ∨ ∃ j', R j' s ∧ ∃ t, j'.mark = .conc t) :
    ∀ N Ic, absCount Ic ≤ N → Al R Ic S → (∃ Ic, Al R Ic S ∧ Goal Ic) ∨ Bad := by
  intro N
  induction N with
  | zero =>
    intro Ic hN hAl
    rcases orc Ic hAl with hg | ⟨j, s, hp, hq⟩
    · exact .inl ⟨Ic, hAl, hg⟩
    · rcases ans j s (PairIn.mem_right hp) (Al.get hAl hp) hq with hb | ⟨j', hj', hc⟩
      · exact .inr hb
      · obtain ⟨_, _, hlt⟩ := replace_pos (abs j s hq) hc hj' hp hAl
        exact absurd (Nat.lt_of_lt_of_le hlt hN) (Nat.not_lt_zero _)
  | succ N ih =>
    intro Ic hN hAl
    rcases orc Ic hAl with hg | ⟨j, s, hp, hq⟩
    · exact .inl ⟨Ic, hAl, hg⟩
    · rcases ans j s (PairIn.mem_right hp) (Al.get hAl hp) hq with hb | ⟨j', hj', hc⟩
      · exact .inr hb
      · obtain ⟨Ic', hAl', hlt⟩ := replace_pos (abs j s hq) hc hj' hp hAl
        exact ih Ic' (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hN)) hAl'

#print axioms answer_loop

/-! ## 8. The ND coverage theorem -/

section Coverage
variable (X : Ctx)

/-- The initial fact `i` of `M` is in `DN` and covers the support location `k`. -/
abbrev IC (M : MethodId) (i : PFact) (k : Loc) : Prop := DN X (.ninit M i) ∧ i.covers k

/-- The relation of an edge with the premise list `I` to the location `l`, for the support
    `L0`: the conclusion covers `l`; for one premise and one support location it also covers
    the PAIR (the correlation with the premise). -/
abbrev NRel (I : List PFact) (L0 : List Loc) (f : PFact) (l : Loc) : Prop :=
  f.covers l ∧ ∀ i l0, I = [i] → L0 = [l0] → den i f l0 l

/-- The request disjunct: a request on the initial fact of one support position, with the
    mark of the support location at that position. -/
abbrev ReqAt (M : MethodId) (I : List PFact) (L0 : List Loc) : Prop :=
  ∃ i k, PairIn i k I L0 ∧ DN X (.nreq M i k.mark)

/-- The statement of the coverage theorem for a derivation `TaintN Q M n l L0`. -/
abbrev CovT (M : MethodId) (n : Node) (l : Loc) (L0 : List Loc) : Prop :=
  ∀ I, Al (IC X M) I L0 →
    (∃ f, DN X (.nedge M I n f) ∧ NRel I L0 f.fact l) ∨ ReqAt X M I L0

/-- One position of a callee support: the callee entry location `k`, the added fact `a`, and
    the caller edge `(Ip, fp)` (support `Lp`) whose binding by `e1` gives `a`. -/
structure Slot where
  k  : Loc
  a  : AFact
  Ip : List PFact
  Lp : List Loc
  fp : AFact
  e1 : MicroEdge

/-- The single-premise witness: the pair `(ic, l0')` is `(i, l0)` when `I = [i]`, `L0 = [l0]`. -/
abbrev SW (I : List PFact) (L0 : List Loc) (ic : PFact) (l0' : Loc) : Prop :=
  ∀ i l0, I = [i] → L0 = [l0] → ic = i ∧ l0' = l0

/-- A slot is in `DN`: the caller edge is in `DN`, its binding gives the added fact, its
    premises cover its support, and the added fact covers the pair of the entry location. -/
abbrev SlotOK (M : MethodId) (n : Node) (c : Call) (s : Slot) : Prop :=
  DN X (.nedge M s.Ip n s.fp) ∧ s.e1 ∈ c.toCallee ∧ s.a ∈ (applyEdge s.fp s.e1.1 s.e1.2).facts ∧
  Al (IC X M) s.Ip s.Lp ∧ ∃ ic l0', den ic s.a.fact l0' s.k ∧ SW s.Ip s.Lp ic l0'

/-- The statement for `SupAll Q M n c K L0`: one slot per callee entry location, or a request. -/
abbrev CovS (M : MethodId) (n : Node) (c : Call) (K L0 : List Loc) : Prop :=
  ∀ n', (M, n, Instr.call c, n') ∈ X.Q.prog.edges → ∀ I, Al (IC X M) I L0 →
    (∃ S : List Slot, K = S.map Slot.k ∧ I = (S.map Slot.Ip).flatten ∧
      L0 = (S.map Slot.Lp).flatten ∧ ∀ s, s ∈ S → SlotOK X M n c s) ∨ ReqAt X M I L0

/-- A callee initial fact for a slot: in `DN`, it covers the entry location, and it is
    applicable to the added fact. -/
abbrev Cand (c : Call) (s : Slot) (j : PFact) : Prop :=
  DN X (.ninit c.callee j) ∧ j.covers s.k ∧ applicable j s.a.fact = true

variable {X}

theorem wit_of_rel {I : List PFact} {L0 : List Loc} {f : PFact} {l : Loc}
    (h : NRel I L0 f l) : ∃ ic l0', den ic f l0' l ∧ SW I L0 ic l0' := by
  match I, L0, h with
  | [i], [l0], h =>
    exact ⟨i, l0, h.2 i l0 rfl rfl, fun i' l0' hI hL => ⟨(List.cons.inj hI).1, (List.cons.inj hL).1⟩⟩
  | [], _, h => exact ⟨f, l, den_refl h.1, fun _ _ hI _ => nomatch hI⟩
  | [_], [], h => exact ⟨f, l, den_refl h.1, fun _ _ _ hL => nomatch hL⟩
  | [_], _ :: _ :: _, h =>
    exact ⟨f, l, den_refl h.1, fun _ _ _ hL => nomatch (List.cons.inj hL).2⟩
  | _ :: _ :: _, _, h =>
    exact ⟨f, l, den_refl h.1, fun _ _ hI _ => nomatch (List.cons.inj hI).2⟩

theorem rel_of_wit {I : List PFact} {L0 : List Loc} {f ic : PFact} {l0' l : Loc}
    (hd : den ic f l0' l) (hw : SW I L0 ic l0') : NRel I L0 f l :=
  ⟨den_covers_final hd, fun i l0 hI hL => by
    obtain ⟨h1, h2⟩ := hw i l0 hI hL
    rw [← h1, ← h2]
    exact hd⟩

/-- The gate of a literal on a covering fact passes, or it asks for the entry mark. -/
theorem litGate {ic f lit : PFact} {l0 l : Loc} (hd : den ic f l0 l) (hc : lit.covers l) :
    markGate lit.mark f.mark = .ok ∨
      ((∀ t, f.mark ≠ .conc t) ∧ markGate lit.mark f.mark = .req l0.mark) := by
  have hadm : lit.mark.admits (f.mark.out l0.mark) := by
    rw [← hd.2.2.2.1]
    exact hc.2.2
  exact CoreAux.gate_cases hadm hd.2.2.2.2.1

/-- The ND summary chain: the slots match the callee premises one by one. The conclusion
    keeps its fact; its layer collects the layers of the caller edges. -/
theorem nd_chain {M : MethodId} {n n' : Node} {c : Call} :
    ∀ {g : AFact} {S : List Slot} {Ic P0 : List PFact}, (∀ s, s ∈ S → SlotOK X M n c s) →
      Al (fun j s => Cand X c s j) Ic S → DN X (.npart M n c n' Ic P0 g) →
      ∃ g', g'.fact = g.fact ∧ DN X (.npart M n c n' [] (P0 ++ (S.map Slot.Ip).flatten) g')
  | g, [], _, P0, _, hAl, h => by
    rw [Al.nil_right hAl] at h
    refine ⟨g, rfl, ?_⟩
    show DN X (.npart M n c n' [] (P0 ++ []) g)
    rw [List.append_nil]
    exact h
  | _, s :: S, _, P0, hok, .cons hR hAl, h => by
    obtain ⟨hf, he1, ha, _⟩ := hok s List.mem_cons_self
    have h' := DN.ndBind h hf he1 ha hR.2.2
    obtain ⟨g'', hgf, h''⟩ := nd_chain (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hAl h'
    rw [List.append_assoc] at h''
    exact ⟨g'', hgf, h''⟩

/-- An answered or climbed request at one slot. -/
theorem answer_slot (hwf : X.Q.WF) {M : MethodId} {n n' : Node} {c : Call} {I : List PFact}
    {L0 : List Loc} {S : List Slot} (he : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (hIS : I = (S.map Slot.Ip).flatten) (hLS : L0 = (S.map Slot.Lp).flatten)
    (hSok : ∀ s, s ∈ S → SlotOK X M n c s) {j : PFact} {s : Slot} (hs : s ∈ S)
    (hR : Cand X c s j) (hq : DN X (.nreq c.callee j s.k.mark)) :
    ReqAt X M I L0 ∨ ∃ j', Cand X c s j' ∧ ∃ t, j'.mark = .conc t := by
  obtain ⟨hf, he1, ha, hAl, ic, l0', hda, hsw⟩ := hSok s hs
  have hac : s.a.fact.covers s.k := den_covers_final hda
  have hov : overlapB s.a.fact j = true := overlapB_of_common hac hR.2.1
  rcases mark_dich s.a.fact.mark with ⟨t, ht⟩ | habs
  · -- a concrete added fact answers the request
    right
    have hkm : s.k.mark = t := by
      have h0 := hac.2.2
      rw [ht] at h0
      exact h0
    rw [hkm] at hq
    have hans := DN.answer hq (DN.added hf he he1 ha) ht hov
    exact ⟨answerInit j s.a.fact t,
      ⟨hans, answerInit_covers hR.2.1 hac hkm, answerInit_applicable hR.2.2 ht⟩,
      t, answerInit_mark⟩
  · -- a mark-abstract added fact: the request climbs to the single caller premise
    left
    have hfabs : ∀ t, s.fp.fact.mark ≠ .conc t := fun t ht =>
      let ⟨t', h'⟩ := applyEdge_mark_conc ht ha
      habs t' h'
    obtain ⟨i, l0, hIp, hLp⟩ := single_of_abs hwf hf hfabs hAl
    obtain ⟨hic, hl0⟩ := hsw i l0 hIp hLp
    have hcl := climbsB_of_covers hac rfl habs
    rw [hIp] at hf
    have hup := DN.reqUp hq hf he rfl he1 ha hcl hov
    have hkm : s.k.mark = l0.mark := by
      rw [← hl0]
      exact den_mark_abs hda habs
    rw [hkm] at hup
    have hlen : ∀ x, x ∈ S → x.Ip.length = x.Lp.length :=
      fun x hx => Al.length (hSok x hx).2.2.2.1
    have hp : PairIn i l0 s.Ip s.Lp := by
      rw [hIp, hLp]
      exact .head
    rw [hIS, hLS]
    exact ⟨i, l0, PairIn.flat hs hlen hp, hup⟩

/-- Two non-empty blocks give a flattened list that is not a singleton. -/
theorem flat_ne_single {s1 s2 : Slot} {S : List Slot} {i : PFact}
    (h1 : s1.Ip ≠ []) (h2 : s2.Ip ≠ []) : ((s1 :: s2 :: S).map Slot.Ip).flatten ≠ [i] := by
  show s1.Ip ++ (s2.Ip ++ (S.map Slot.Ip).flatten) ≠ [i]
  exact app_ne_single h1 (fun h => h2 (List.append_eq_nil_iff.mp h).1)

/-- THE CALL STEP. The slots of the callee support, the coverage theorem of the callee, and
    the binding back give a caller edge, or a request. -/
theorem call_step (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n n' : Node} {c : Call} {l2 l3 : Loc} {e2 : MicroEdge} {I : List PFact}
    {L0 : List Loc} (S : List Slot) (he : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (ihc : CovT X c.callee (X.Q.prog.exit c.callee) l2 (S.map Slot.k))
    (hIS : I = (S.map Slot.Ip).flatten) (hLS : L0 = (S.map Slot.Lp).flatten)
    (hSok : ∀ s, s ∈ S → SlotOK X M n c s)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    (∃ f, DN X (.nedge M I n' f) ∧ NRel I L0 f.fact l3) ∨ ReqAt X M I L0 := by
  -- the initial choice: the abstraction of each added fact
  have hIc0 : Al (fun j s => Cand X c s j) (S.map (fun s => X.α c.callee s.a.fact)) S := by
    apply Al.of_map
    intro s hs
    obtain ⟨hf, he1, ha, _, ic, l0', hda, _⟩ := hSok s hs
    exact ⟨DN.initA (DN.added hf he he1 ha),
      applicable_sound (hα _ _) (den_covers_final hda), hα _ _⟩
  have hloop := answer_loop
    (Goal := fun Ic => ∃ g, DN X (.nedge c.callee Ic (X.Q.prog.exit c.callee) g) ∧
      NRel Ic (S.map Slot.k) g.fact l2)
    (Req := fun j s => DN X (.nreq c.callee j s.k.mark))
    (Bad := ReqAt X M I L0)
    (fun Ic hIc => by
      rcases ihc Ic (Al.map (fun _ _ h => ⟨h.1, h.2.1⟩) hIc) with hg | ⟨j, k, hp, hq⟩
      · exact .inl hg
      · obtain ⟨s, hps, hk⟩ := PairIn.of_map hp
        rw [hk] at hq
        exact .inr ⟨j, s, hps, hq⟩)
    (fun j _ hq => req_abstract hwf hq)
    (fun j s hs hR hq => answer_slot hwf he hIS hLS hSok hs hR hq)
    _ _ (Nat.le_refl _) hIc0
  rcases hloop with ⟨Ic, hAl, g, hg, hrel⟩ | hb
  · cases hAl with
    | nil => exact absurd rfl (premises_ne_nil hwf hg)
    | @cons j s Ic1 S1 hR hAl1 =>
      cases hAl1 with
      | nil =>
        -- one callee premise: the summary application keeps the caller premise list
        obtain ⟨hf, he1, ha, _, ic, l0', hda, hsw⟩ := hSok s List.mem_cons_self
        have hdg : den j g.fact s.k l2 := hrel.2 j s.k rfl rfl
        obtain ⟨r, hr, hdr⟩ := summary_step hR.2.2 hda hdg
        obtain ⟨r', hr', hdr'⟩ := bind_out hwf.prog he he2 hdr hd2
        have hI : I = s.Ip := by rw [hIS]; exact List.append_nil _
        have hL : L0 = s.Lp := by rw [hLS]; exact List.append_nil _
        subst hI hL
        exact .inl ⟨_, DN.ret hf he he1 ha hR.1 hR.2.2 hg hr he2 hr',
          rel_of_wit (limitF_sound hdr') hsw⟩
      | @cons j2 s2 Ic' S' hR2 hAl2 =>
        -- two or more callee premises: the ND summary chain
        have hopen := DN.ndOpen (n := n) (n' := n') he hg
          (by show 2 ≤ Ic'.length + 1 + 1; exact Nat.le_add_left 2 _)
        obtain ⟨g', hgf, hch⟩ := nd_chain hSok (.cons hR (.cons hR2 hAl2)) hopen
        obtain ⟨r, hr, hdr⟩ := bind_out (r := g') hwf.prog he he2
          (by rw [hgf]; exact den_refl hrel.1) hd2
        have hres := DN.ndRet hch he2 hr
        rw [List.nil_append, ← hIS] at hres
        refine .inl ⟨_, hres, den_covers_final (limitF_sound hdr), fun i _ hI _ => ?_⟩
        have h1 := premises_ne_nil hwf (hSok s List.mem_cons_self).1
        have h2 := premises_ne_nil hwf (hSok s2 (List.mem_cons_of_mem _ List.mem_cons_self)).1
        rw [hIS] at hI
        exact absurd hI (flat_ne_single h1 h2)
  · exact .inr hb

#print axioms call_step

mutual
/-- THE ND COVERAGE THEOREM (run 1). Let a derivation `TaintN Q M n l L0` be given, and one
    initial fact of `M` in `DN` for each support location, which covers it (the list `I`).
    Then the edge keyed by EXACTLY those premises is at `n` and covers `l` (with the pair, for
    one premise and one support location), or `DN` has a request on the initial fact of one
    position, with the mark of the support location at that position. -/
theorem nd_coverage (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true) :
    ∀ {M n l L0}, TaintN X.Q M n l L0 → CovT X M n l L0
  | _, _, _, _, .start M l => by
    intro I hI
    obtain ⟨i, rfl, hi, hc⟩ := Al.singleton_right hI
    refine .inl ⟨startFact i, DN.start hi, den_covers_final (startFact_sound hc), ?_⟩
    intro i' l0 hI hL
    rw [← (List.cons.inj hI).1, ← (List.cons.inj hL).1]
    exact startFact_sound hc
  | _, _, _, _, .step h he hs => by
    intro I hI
    rcases nd_coverage hwf hα h I hI with ⟨f, hf, hrel⟩ | hr
    · obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      rcases transfer_sound (counted := X.counted) (L := X.FL)
          (hwf.prog.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨habs, hq⟩
      · exact .inl ⟨r, DN.step hf he hr, rel_of_wit hdr hsw⟩
      · obtain ⟨i, l0, hI1, hL1⟩ := single_of_abs hwf hf habs hI
        obtain ⟨hic, hl0⟩ := hsw i l0 hI1 hL1
        rw [hI1] at hf
        rw [hl0] at hq
        exact .inr ⟨i, l0, by rw [hI1, hL1]; exact .head, DN.reqStmt hf he hq⟩
    · exact .inr hr
  | _, _, _, _, .pass h he hm => by
    intro I hI
    rcases nd_coverage hwf hα h I hI with ⟨f, hf, hrel⟩ | hr
    · rw [hrel.1.1] at hm
      exact .inl ⟨f, DN.pass hf he hm, hrel⟩
    · exact .inr hr
  | _, _, _, _, .clean h he hc => by
    intro I hI
    rcases nd_coverage hwf hα h I hI with ⟨f, hf, hrel⟩ | hr
    · obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      rcases cleanRes_sound hd hc with ⟨r, hr, hdr⟩ | ⟨habs, hq⟩
      · exact .inl ⟨r, DN.clean hf he hr, rel_of_wit hdr hsw⟩
      · obtain ⟨i, l0, hI1, hL1⟩ := single_of_abs hwf hf habs hI
        obtain ⟨hic, hl0⟩ := hsw i l0 hI1 hL1
        rw [hI1] at hf
        rw [hl0] at hq
        exact .inr ⟨i, l0, by rw [hI1, hL1]; exact .head, DN.reqClean hf he hq⟩
    · exact .inr hr
  | _, _, _, _, .filt h he hl => by
    intro I hI
    rcases nd_coverage hwf hα h I hI with ⟨f, hf, hrel⟩ | hr
    · obtain ⟨ic, l0', hd, _⟩ := wit_of_rel hrel
      exact .inl ⟨f, DN.filt hf he (filt_keeps (hwf.prog.filtPrefix _ _ _ _ _ he) hd hl), hrel⟩
    · exact .inr hr
  | _, _, _, _, .conj h1 h2 hcj hc1 hc2 hct => by
    intro I hI
    obtain ⟨I1, I2, rfl, hI1, hI2⟩ := Al.split hI
    rcases nd_coverage hwf hα h1 I1 hI1 with ⟨f1, hf1, hrel1⟩ | ⟨i, k, hp, hq⟩
    · rcases nd_coverage hwf hα h2 I2 hI2 with ⟨f2, hf2, hrel2⟩ | ⟨i, k, hp, hq⟩
      · obtain ⟨ic1, l01, hd1, hsw1⟩ := wit_of_rel hrel1
        obtain ⟨ic2, l02, hd2, hsw2⟩ := wit_of_rel hrel2
        have ho1 := overlapB_of_common hrel1.1 hc1
        have ho2 := overlapB_of_common hrel2.1 hc2
        rcases litGate hd1 hc1 with hg1 | ⟨habs1, hg1⟩
        · rcases litGate hd2 hc2 with hg2 | ⟨habs2, hg2⟩
          · -- both literals hold: the conjunction
            refine .inl ⟨_, DN.conj hf1 hf2 hcj ho1 hg1 ho2 hg2, hct, fun i _ hP _ => ?_⟩
            exact absurd hP (app_ne_single (premises_ne_nil hwf hf1) (premises_ne_nil hwf hf2))
          · -- the second literal on a mark-abstract fact: the request
            obtain ⟨i, l0, hI1', hL1'⟩ := single_of_abs hwf hf2 habs2 hI2
            obtain ⟨_, hl0⟩ := hsw2 i l0 hI1' hL1'
            rw [hI1'] at hf2
            rw [hl0] at hg2
            exact .inr ⟨i, l0, PairIn.appR (Al.length hI1) (by rw [hI1', hL1']; exact .head),
              DN.reqConj hf2 hcj (.inr rfl) ho2 hg2⟩
        · -- the first literal on a mark-abstract fact: the request
          obtain ⟨i, l0, hI1', hL1'⟩ := single_of_abs hwf hf1 habs1 hI1
          obtain ⟨_, hl0⟩ := hsw1 i l0 hI1' hL1'
          rw [hI1'] at hf1
          rw [hl0] at hg1
          exact .inr ⟨i, l0, PairIn.appL _ _ (by rw [hI1', hL1']; exact .head),
            DN.reqConj hf1 hcj (.inl rfl) ho1 hg1⟩
      · exact .inr ⟨i, k, PairIn.appR (Al.length hI1) hp, hq⟩
    · exact .inr ⟨i, k, PairIn.appL _ _ hp, hq⟩
  | _, _, _, _, .call he hcal hsup he2 hd2 => by
    intro I hI
    have ihc := nd_coverage hwf hα hcal
    rcases nd_coverage_sup hwf hα hsup _ he I hI with ⟨S, hK, hIS, hLS, hSok⟩ | hr
    · subst hK
      exact call_step hwf hα S he ihc hIS hLS hSok he2 hd2
    · exact .inr hr

/-- The coverage statement for the callee entry locations of a call (`SupAll`). -/
theorem nd_coverage_sup (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true) :
    ∀ {M n c K L0}, SupAll X.Q M n c K L0 → CovS X M n c K L0
  | _, _, _, _, _, .nil => by
    intro n' he I hI
    exact .inl ⟨[], rfl, Al.nil_right hI, rfl, fun _ h => absurd h List.not_mem_nil⟩
  | _, _, _, _, _, @SupAll.cons _ M n c lk Lk e1 k K L0 hT he1 hd1 hS => by
    intro n' he I hI
    obtain ⟨I1, I2, rfl, hI1, hI2⟩ := Al.split hI
    rcases nd_coverage hwf hα hT I1 hI1 with ⟨f, hf, hrel⟩ | ⟨i, k', hp, hq⟩
    · obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      obtain ⟨a, ha, hda⟩ := bind_in hwf.prog he he1 hd hd1
      rcases nd_coverage_sup hwf hα hS n' he I2 hI2 with ⟨S, hK, hIS, hLS, hSok⟩ | ⟨i, k', hp, hq⟩
      · refine .inl ⟨⟨k, a, I1, Lk, f, e1⟩ :: S, by rw [hK]; rfl, by rw [hIS]; rfl,
          by rw [hLS]; rfl, ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with hs' | hs'
        · rw [hs']
          exact ⟨hf, he1, ha, hI1, ic, l0', hda, hsw⟩
        · exact hSok s hs'
      · exact .inr ⟨i, k', PairIn.appR (Al.length hI1) hp, hq⟩
    · exact .inr ⟨i, k', PairIn.appL _ _ hp, hq⟩
end

#print axioms nd_coverage
#print axioms nd_coverage_sup

/-- THE ND COVERAGE THEOREM with the abbreviations unfolded. -/
theorem nd_coverage_unfolded (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} (h : TaintN X.Q M n l L0)
    (I : List PFact) (hI : Al (fun i k => DN X (.ninit M i) ∧ i.covers k) I L0) :
    (∃ f, DN X (.nedge M I n f) ∧ f.fact.covers l ∧
        ∀ i l0, I = [i] → L0 = [l0] → den i f.fact l0 l) ∨
      ∃ i k, PairIn i k I L0 ∧ DN X (.nreq M i k.mark) :=
  nd_coverage hwf hα h I hI

#print axioms nd_coverage_unfolded

end Coverage

/-! ## 9. Corollaries: one premise, concrete premises, and the vulnerability theorem -/

section Corollaries
variable {X : Ctx}

/-- One support location and one premise: the edge `[i]` covers the PAIR, or `DN` has the
    request for the entry mark on `i` (the form of `Coverage.coverage`). -/
theorem nd_coverage_single (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l l0 : Loc} {i : PFact} (h : TaintN X.Q M n l [l0])
    (hi : DN X (.ninit M i)) (hc : i.covers l0) :
    (∃ f, DN X (.nedge M [i] n f) ∧ den i f.fact l0 l) ∨ DN X (.nreq M i l0.mark) := by
  rcases nd_coverage hwf hα h [i] (.cons ⟨hi, hc⟩ .nil) with ⟨f, hf, hrel⟩ | ⟨i', k, hp, hq⟩
  · exact .inl ⟨f, hf, hrel.2 i l0 rfl rfl⟩
  · cases hp with
    | head => exact .inr hq
    | tail hp' => cases hp'

#print axioms nd_coverage_single

/-- The data flow of the base model: `DN` covers it as `D` does (`Coverage.coverage`). -/
theorem nd_coverage_flow (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l l0 : Loc} {i : PFact} (h : Flow X.Q.prog M l0 n l)
    (hi : DN X (.ninit M i)) (hc : i.covers l0) :
    (∃ f, DN X (.nedge M [i] n f) ∧ den i f.fact l0 l) ∨ DN X (.nreq M i l0.mark) :=
  nd_coverage_single hwf hα (flow_taintN h) hi hc

#print axioms nd_coverage_flow

/-- Concrete-mark premises raise no request: the edge keyed by them covers the location. -/
theorem nd_coverage_conc (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} {I : List PFact}
    (h : TaintN X.Q M n l L0) (hI : Al (IC X M) I L0)
    (hconc : ∀ i, i ∈ I → ∃ t, i.mark = .conc t) :
    ∃ f, DN X (.nedge M I n f) ∧ NRel I L0 f.fact l := by
  rcases nd_coverage hwf hα h I hI with hok | ⟨i, k, hp, hq⟩
  · exact hok
  · obtain ⟨t, ht⟩ := hconc i (PairIn.mem_left hp)
    exact absurd ht (req_abstract hwf hq t)

#print axioms nd_coverage_conc

/-- The sink check on a covering edge: it triggers, or (one premise, mark-abstract) it raises
    the request for the entry mark on the premise. -/
theorem nd_check {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} {I : List PFact}
    {f : AFact} {s : PFact} {T : Mark} (hwf : X.Q.WF)
    (hf : DN X (.nedge M I n f)) (hrel : NRel I L0 f.fact l) (hI : Al (IC X M) I L0)
    (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T) (hsc : s.covers l) :
    (∃ b, DN X (.nvuln M n s b)) ∨ ∃ i l0, I = [i] ∧ L0 = [l0] ∧ DN X (.nreq M i l0.mark) := by
  rcases mark_dich f.fact.mark with ⟨t, ht⟩ | habs
  · -- a concrete conclusion: the check does not read the premise
    rcases check_sound hT (den_refl hrel.1) hsc with htr | ⟨_, hn⟩
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil I (premises_ne_nil hwf hf)
      left
      exact ⟨_, DN.vuln hf hs hi (by rw [check_conc_indep (i' := f.fact) ht]; exact htr)⟩
    · exact absurd ht (hn t)
  · obtain ⟨i, l0, hI1, hL1⟩ := single_of_abs hwf hf habs hI
    rw [hI1] at hf
    rcases check_sound hT (hrel.2 i l0 hI1 hL1) hsc with htr | ⟨hrq, _⟩
    · exact .inl ⟨_, DN.vuln hf hs List.mem_cons_self htr⟩
    · exact .inr ⟨i, l0, hI1, hL1, DN.reqSink hf hs hrq⟩

/-- THE ND VULNERABILITY THEOREM (concrete premises). A derivation of a location that a sink
    pattern covers, from support locations that concrete-mark initial facts cover, gives a
    `vuln` object. -/
theorem nd_vuln (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} {I : List PFact} {s : PFact} {T : Mark}
    (h : TaintN X.Q M n l L0) (hI : Al (IC X M) I L0)
    (hconc : ∀ i, i ∈ I → ∃ t, i.mark = .conc t)
    (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T) (hsc : s.covers l) :
    ∃ b, DN X (.nvuln M n s b) := by
  obtain ⟨f, hf, hrel⟩ := nd_coverage_conc hwf hα h hI hconc
  rcases nd_check hwf hf hrel hI hs hT hsc with hv | ⟨i, _, hI1, _, hq⟩
  · exact hv
  · obtain ⟨t, ht⟩ := hconc i (by rw [hI1]; exact List.mem_cons_self)
    exact absurd ht (req_abstract hwf hq t)

#print axioms nd_vuln

/-- THE ND VULNERABILITY THEOREM at a root: a derivation whose support is the zero location
    only gives a `vuln` object. -/
theorem nd_vuln_root (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} {s : PFact} {T : Mark}
    (hM : M ∈ X.roots) (h : TaintN X.Q M n l L0) (hz : ∀ k, k ∈ L0 → k = zeroLoc)
    (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T) (hsc : s.covers l) :
    ∃ b, DN X (.nvuln M n s b) := by
  refine nd_vuln hwf hα h (I := L0.map (fun _ => zeroFact))
    (Al.of_map (fun k hk => ⟨DN.root hM, by rw [hz k hk]; exact zeroFact_covers⟩)) ?_ hs hT hsc
  intro i hi
  obtain ⟨_, _, hk⟩ := List.mem_map.mp hi
  exact ⟨zeroMark, by rw [← hk]; rfl⟩

#print axioms nd_vuln_root

end Corollaries

/-! ## 10. `DN` contains `D` -/

/-- An object of `D` as an object of `DN`: a single-premise edge has the premise list `[i]`. -/
def liftObj : Obj → NObj
  | .init M i => .ninit M i
  | .edge M i n f => .nedge M [i] n f
  | .added M a => .nadded M a
  | .req M i t => .nreq M i t
  | .vuln M n s d => .nvuln M n s d

/-- `DN` is a conservative extension of `D`: every object of `D` (on the same program without
    the conjunctions) is an object of `DN`. -/
theorem D_sub_DN {X : Ctx} {o : Obj}
    (h : D X.Q.prog X.counted X.FL X.α X.sinks X.roots o) : DN X (liftObj o) := by
  induction h with
  | root hM => exact DN.root hM
  | start _ ih => exact DN.start ih
  | step _ he hf ih => exact DN.step ih he hf
  | reqStmt _ he hq ih => exact DN.reqStmt ih he hq
  | pass _ he hb ih => exact DN.pass ih he hb
  | added _ he he1 ha ih => exact DN.added ih he he1 ha
  | initA _ ih => exact DN.initA ih
  | ret _ he he1 ha _ hap _ hr he2 hr' ih ihj ihg =>
    exact DN.ret ih he he1 ha ihj hap ihg hr he2 hr'
  | reqSink _ hs hc ih => exact DN.reqSink ih hs hc
  | answer _ _ hm hov ihr iha => exact DN.answer ihr iha hm hov
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf => exact DN.reqUp ihr ihf he hc he1 ha hcl hov
  | vuln _ hs hc ih => exact DN.vuln ih hs List.mem_cons_self hc
  | clean _ he hf ih => exact DN.clean ih he hf
  | reqClean _ he hq ih => exact DN.reqClean ih he hq
  | filt _ he hf ih => exact DN.filt ih he hf

#print axioms D_sub_DN

/-! ## 11. The vulnerability witness is a tree

A sink inside a callee is reached through a call: the callee derivation needs one caller
location per entry location, and each caller location has its own witness (a TREE of
derivations). `ReachN` generalises `Reach`: a `Reach` chain is a tree whose every call node
has one child (`reach_reachN`). -/

mutual
/-- `ReachN Q roots M n l`: the location `l` at node `n` of `M` is tainted in a real execution
    from a root. -/
inductive ReachN (Q : NProg) (roots : List MethodId) : MethodId → Node → Loc → Prop where
  | root {M n l L0} : M ∈ roots → TaintN Q M n l L0 → (∀ k, k ∈ L0 → k = zeroLoc) →
      ReachN Q roots M n l
  | down {M n n' c K n2 l2} : (M, n, Instr.call c, n') ∈ Q.prog.edges →
      ReachAll Q roots M n c K → TaintN Q c.callee n2 l2 K → ReachN Q roots c.callee n2 l2

/-- Every callee entry location of `K` is bound from a caller location that `ReachN` reaches
    at the call node. -/
inductive ReachAll (Q : NProg) (roots : List MethodId) : MethodId → Node → Call → List Loc → Prop where
  | nil {M n c} : ReachAll Q roots M n c []
  | cons {M n c lk e1 k K} : ReachN Q roots M n lk → e1 ∈ c.toCallee → den e1.1 e1.2 lk k →
      ReachAll Q roots M n c K → ReachAll Q roots M n c (k :: K)
end

/-- A `Reach` chain is a tree witness. -/
theorem reach_reachN {Q : NProg} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : Reach Q.prog roots M n l) : ReachN Q roots M n l := by
  induction h with
  | root hM hfl => exact .root hM (flow_taintN hfl) (fun k hk => List.mem_singleton.mp hk)
  | down _ he he1 hd1 hfc ih => exact .down he (.cons ih he1 hd1 .nil) (flow_taintN hfc)

#print axioms reach_reachN

theorem Al.exists_of_forall {α β : Type} {R : α → β → Prop} :
    ∀ {K : List β}, (∀ k, k ∈ K → ∃ j, R j k) → ∃ I, Al R I K
  | [], _ => ⟨[], .nil⟩
  | k :: K, h => by
    obtain ⟨j, hj⟩ := h k List.mem_cons_self
    obtain ⟨I, hI⟩ := Al.exists_of_forall (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    exact ⟨j :: I, .cons hj hI⟩

section Tree
variable (X : Ctx)

/-- A good initial fact for a support location: in `DN`, it covers the location, and a request
    on it with the mark of the location has a concrete-mark answer that covers the location. -/
abbrev Good (M : MethodId) (j : PFact) (k : Loc) : Prop :=
  DN X (.ninit M j) ∧ j.covers k ∧
    (DN X (.nreq M j k.mark) → ∃ j', DN X (.ninit M j') ∧ j'.covers k ∧ ∃ t, j'.mark = .conc t)

/-- The strengthened reach statement: a derivation of `l` with good initial facts for its
    support. -/
abbrev RS (M : MethodId) (n : Node) (l : Loc) : Prop :=
  ∃ L0 I, TaintN X.Q M n l L0 ∧ Al (Good X M) I L0

/-- A callee entry location: an added fact covers it, and every request on a covering initial
    fact with its mark has a concrete-mark answer that covers it. -/
abbrev GoodC (m : MethodId) (k : Loc) : Prop :=
  (∃ a, DN X (.nadded m a) ∧ a.covers k) ∧
  ∀ j, DN X (.ninit m j) → j.covers k → DN X (.nreq m j k.mark) →
    ∃ j', DN X (.ninit m j') ∧ j'.covers k ∧ ∃ t, j'.mark = .conc t

abbrev RSAll (M : MethodId) (n : Node) (c : Call) (K : List Loc) : Prop :=
  ∀ n', (M, n, Instr.call c, n') ∈ X.Q.prog.edges → ∀ k, k ∈ K → GoodC X c.callee k

variable {X}

theorem good_conc (hwf : X.Q.WF) {M : MethodId} {j : PFact} {k : Loc}
    (hj : DN X (.ninit M j)) (hc : j.covers k) (ht : ∃ t, j.mark = .conc t) : Good X M j k :=
  ⟨hj, hc, fun hq => let ⟨t, ht⟩ := ht; absurd ht (req_abstract hwf hq t)⟩

/-- The loop in one method: good initial facts give a covering edge (no request is left). -/
theorem good_edge (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} {I : List PFact}
    (hT : TaintN X.Q M n l L0) (hI : Al (Good X M) I L0) :
    ∃ Ic, Al (Good X M) Ic L0 ∧ ∃ f, DN X (.nedge M Ic n f) ∧ NRel Ic L0 f.fact l := by
  have hloop := answer_loop (S := L0) (R := Good X M)
    (Goal := fun Ic => ∃ f, DN X (.nedge M Ic n f) ∧ NRel Ic L0 f.fact l)
    (Req := fun j k => DN X (.nreq M j k.mark)) (Bad := False)
    (fun Ic hIc => nd_coverage hwf hα hT Ic (Al.mono (fun _ _ h => ⟨h.1, h.2.1⟩) hIc))
    (fun j _ hq => req_abstract hwf hq)
    (fun _ _ _ hG hq =>
      let ⟨j', hj', hc', hconc⟩ := hG.2.2 hq
      .inr ⟨j', good_conc hwf hj' hc' hconc, hconc⟩)
    _ _ (Nat.le_refl _) hI
  rcases hloop with h | h
  · exact h
  · exact h.elim

mutual
/-- THE STRENGTHENED REACH THEOREM: a tree witness has a derivation with good initial facts. -/
theorem reach_strong (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true) :
    ∀ {M n l}, ReachN X.Q X.roots M n l → RS X M n l
  | _, _, _, .root hM hT hz =>
    ⟨_, _, hT, Al.of_map (fun k hk => ⟨DN.root hM, by rw [hz k hk]; exact zeroFact_covers,
      fun hq => absurd rfl (req_abstract hwf hq zeroMark)⟩)⟩
  | _, _, _, @ReachN.down _ _ M n n' c K n2 l2 he hall hT => by
    have ih := reach_strong_all hwf hα hall _ he
    obtain ⟨I, hI⟩ := Al.exists_of_forall (R := Good X c.callee) (fun k hk => by
      obtain ⟨⟨a, ha, hac⟩, hres⟩ := ih k hk
      have hjc := applicable_sound (hα c.callee a) hac
      exact ⟨_, DN.initA ha, hjc, fun hq => hres _ (DN.initA ha) hjc hq⟩)
    exact ⟨_, I, hT, hI⟩

/-- The callee entry locations of a tree witness are good. -/
theorem reach_strong_all (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true) :
    ∀ {M n c K}, ReachAll X.Q X.roots M n c K → RSAll X M n c K
  | _, _, _, _, .nil => fun _ _ _ hk => absurd hk List.not_mem_nil
  | _, _, _, _, @ReachAll.cons _ _ M n c lk e1 k K hR he1 hd1 hrest => by
    have ihR := reach_strong hwf hα hR
    have ihrest := reach_strong_all hwf hα hrest
    intro n' he k' hk'
    rcases List.mem_cons.mp hk' with hkk | hk''
    · rw [hkk]
      obtain ⟨L0, I0, hT, hI0⟩ := ihR
      obtain ⟨I, hI, f, hf, hrel⟩ := good_edge hwf hα hT hI0
      obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      obtain ⟨a, ha, hda⟩ := bind_in hwf.prog he he1 hd hd1
      have hac : a.fact.covers k := den_covers_final hda
      have hadd := DN.added hf he he1 ha
      refine ⟨⟨a.fact, hadd, hac⟩, fun j hj hjc hq => ?_⟩
      have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
      rcases mark_dich a.fact.mark with ⟨t, ht⟩ | habs
      · -- a concrete added fact answers the request
        have hkm : k.mark = t := by
          have h0 := hac.2.2
          rw [ht] at h0
          exact h0
        rw [hkm] at hq
        exact ⟨_, DN.answer hq hadd ht hov, answerInit_covers hjc hac hkm, t, answerInit_mark⟩
      · -- the request climbs to the single caller premise; the caller answers it
        have hfabs : ∀ t, f.fact.mark ≠ .conc t := fun t ht =>
          let ⟨t', h'⟩ := applyEdge_mark_conc ht ha
          habs t' h'
        obtain ⟨i, l0, hI1, hL1⟩ := single_of_abs hwf hf hfabs hI
        obtain ⟨_, hl0⟩ := hsw i l0 hI1 hL1
        have hkm : k.mark = l0.mark := by
          rw [← hl0]
          exact den_mark_abs hda habs
        rw [hI1] at hf
        have hup := DN.reqUp hq hf he rfl he1 ha (climbsB_of_covers hac rfl habs) hov
        rw [hkm] at hup
        rw [hI1, hL1] at hI
        obtain ⟨_, hil, hres⟩ := Al.get hI .head
        obtain ⟨i', hi', hic', t', ht'⟩ := hres hup
        rw [hL1] at hT
        rcases nd_coverage_single hwf hα hT hi' hic' with ⟨f', hf', hd'⟩ | hq'
        · obtain ⟨t1, h1⟩ := edge_conc hwf hf' ht'
          obtain ⟨a', ha', hda'⟩ := bind_in hwf.prog he he1 hd' hd1
          obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
          have hac' : a'.fact.covers k := den_covers_final hda'
          have hkm' : k.mark = t2 := by
            have h0 := hac'.2.2
            rw [h2] at h0
            exact h0
          rw [hkm'] at hq
          have hov' : overlapB a'.fact j = true := overlapB_of_common hac' hjc
          exact ⟨_, DN.answer hq (DN.added hf' he he1 ha') h2 hov',
            answerInit_covers hjc hac' hkm', t2, answerInit_mark⟩
        · exact absurd ht' (req_abstract hwf hq' t')
    · exact ihrest n' he k' hk''
end

#print axioms reach_strong
#print axioms reach_strong_all

/-- THE ND VULNERABILITY THEOREM for a tree witness: a real execution from a root that taints
    a location covered by a sink pattern gives a `vuln` object. -/
theorem nd_vuln_reach (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : ReachN X.Q X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DN X (.nvuln M n s b) := by
  obtain ⟨L0, I, hTn, hI⟩ := reach_strong hwf hα hR
  have hloop := answer_loop (S := L0) (R := Good X M)
    (Goal := fun _ => ∃ b, DN X (.nvuln M n s b))
    (Req := fun j k => DN X (.nreq M j k.mark)) (Bad := False)
    (fun Ic hIc => by
      have hIc' : Al (IC X M) Ic L0 := Al.mono (fun _ _ h => ⟨h.1, h.2.1⟩) hIc
      rcases nd_coverage hwf hα hTn Ic hIc' with ⟨f, hf, hrel⟩ | hreq
      · rcases nd_check hwf hf hrel hIc' hs hT hsc with hv | ⟨i, l0, hI1, hL1, hq⟩
        · exact .inl hv
        · exact .inr ⟨i, l0, by rw [hI1, hL1]; exact .head, hq⟩
      · exact .inr hreq)
    (fun j _ hq => req_abstract hwf hq)
    (fun _ _ _ hG hq =>
      let ⟨j', hj', hc', hconc⟩ := hG.2.2 hq
      .inr ⟨j', good_conc hwf hj' hc' hconc, hconc⟩)
    _ _ (Nat.le_refl _) hI
  rcases hloop with ⟨_, _, hv⟩ | hb
  · exact hv
  · exact hb.elim

#print axioms nd_vuln_reach

/-- The vulnerability theorem of the base model holds for `DN` (`Coverage.vuln_found`). -/
theorem nd_vuln_found (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.Q.prog X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DN X (.nvuln M n s b) :=
  nd_vuln_reach hwf hα (reach_reachN hR) hs hT hsc

#print axioms nd_vuln_found

end Tree

/-! ## 12. Example: the `NDRule` sample of the code

`$A = src(); $B = src(); $C = pass($A, $B); sink($C)` (ExampleTest `test nd rule`). Root
method `0`; node `0` → `1` sets `A` (base 1, mark 7), node `1` → `2` sets `B` (base 2,
mark 8), the conjunction `A ∧ B → C` (base 3, mark 9) goes from node `2` to node `3`, and the
sink is at node `3`. Both sources come from the zero fact, so the conclusion has the premise
list `[zeroFact, zeroFact]` (the code makes a zero-to-fact edge: its zero premise adds no
precondition). The edge is in the normal layer, and the vulnerability is found. -/

namespace Example

def zA : PFact := ⟨1, [], .exact, .conc 7⟩
def zB : PFact := ⟨2, [], .exact, .conc 8⟩
def zC : PFact := ⟨3, [], .exact, .conc 9⟩
def srcA : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, zA)]⟩
def srcB : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, zB)]⟩
def nop : Stmt := ⟨[], []⟩
def cj : Conj := ⟨zA, zB, zC⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 3, [(0, 0, .stmt srcA, 1), (0, 1, .stmt srcB, 2), (0, 2, .stmt nop, 3)]⟩
def X : Ctx := ⟨⟨prog, [(0, 2, cj, 3)]⟩, fun _ => true, 5, fun _ a => a, [(0, 3, zC)], [0]⟩

theorem z1 : DN X (.nedge 0 [zeroFact] 1 ⟨zeroFact, false⟩) :=
  DN.step (DN.start (DN.root List.mem_cons_self)) List.mem_cons_self (by decide)

theorem a1 : DN X (.nedge 0 [zeroFact] 1 ⟨zA, false⟩) :=
  DN.step (DN.start (DN.root List.mem_cons_self)) List.mem_cons_self (by decide)

theorem a2 : DN X (.nedge 0 [zeroFact] 2 ⟨zA, false⟩) :=
  DN.step a1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)

theorem b2 : DN X (.nedge 0 [zeroFact] 2 ⟨zB, false⟩) :=
  DN.step z1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)

theorem c3 : DN X (.nedge 0 [zeroFact, zeroFact] 3 (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩)) :=
  DN.conj a2 b2 List.mem_cons_self (by decide) rfl (by decide) rfl

/-- The conclusion is in the normal layer: both inputs are normal and cover their literals. -/
theorem c3_normal : (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩).demand = false := by decide

theorem vuln3 : DN X (.nvuln 0 3 zC false) :=
  DN.vuln c3 List.mem_cons_self List.mem_cons_self (by decide)

#print axioms vuln3

end Example

end ApSpec.ND
