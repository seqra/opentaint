/-
  ApSpec.StaticsConfirmed — the CONFIRMATION of a run-1 vulnerability WITH THE STATIC RULE (spec
  §4.9, §4.10, §0.1): a confirmed vulnerability of `Statics.DS` is real for the reference semantics.

  `Confirmed.Sup`/`Confirmed.Confirmed` are stated for the plain run-1 closure `D`. Run 1 with the
  static rule is `Statics.DS`: it adds the position requests (`sreqStmt`, `sreqUp`), their answers
  `(S, p, *, {}, *)` (`sanswer`), the overlap reading `sret` (off in the final rule), and it answers a
  MARK request on a static premise by the added fact itself (`SCtx.ansInit`, the deep answer).

  THE SUPPORT OVER `DS` (`SupS`, the condition 3 of §4.9):
    * at a root, the zero fact is supported;
    * in a callee, the initial fact `j` is supported if a normal caller edge `(i, normal) → c` at a
      call to the callee has a SUPPORTED premise `i`, the binding of `c` gives the added fact `a` in
      the normal layer, and `j = a` (base, path, tail and mark): `j` and `a` are the zero fact, or
      `a` is exact with a concrete mark `t` and `j` is the answer of a mark request `(callee, k, t)`
      of `DS` by `a`, read with the answer rule of `DS` (`j = X.ansInit k a t`): the chain answer
      `answerInit` (only when `k` is at the position of `a`), or the DEEP answer `a` itself (a
      request on a static premise answered from an added fact at or below it, `ansInit_deep_self`).
    * nothing else is supported.
  The position answer `(S, p, *, {}, *)` is never supported (`sAns_not_supS`: it is a `*` fact). It
  takes part in a confirmation only as the premise `k` of the mark request whose answer is the
  supported premise (`Example`, `CexAbove`, `CexWide`: `k = (S, <C>.f, *, {}, *)`). Allowing an
  abstract-mark initial fact (a position answer, a static root) as the CALLER premise of a support
  step changes nothing: under `MarkWF` every fact under it has an abstract mark, so its binding is
  never the zero fact or an exact concrete fact (`supR_iff`). And it is never the premise of a
  triggered sink edge (`abs_premise_no_trigger`).

  Main results (every theorem holds for EVERY `SCtx`, every variant of the rule; `SWF` and `Design`
  are not needed: the proof uses only the exactness of `DS`, `edge_exactS`, `edge_exact_validS`, and
  the support; the final rule is the instance `Design X`):
    * `confirmedS_vuln`: a confirmed vulnerability is a normal-layer `vuln` object of `DS`.
    * `supS_entry`, `supS_entry_valid`: a supported initial fact is exact with a concrete mark, and its
      unique location is real at the entry of the method (`Confirmed.EntryReach`).
    * `confirmed_realS` (`MarkWF`, `FiltUp`), `confirmed_realS_valid` (`MarkWF`, `FiltValid`,
      `BackOK`, every location of the sink pattern valid), with the `_of` forms: THE CONFIRMATION
      THEOREM OF RUN 1 WITH THE STATIC RULE. A confirmed vulnerability of `DS` is real (`Reach`).
    * `D_sub_DS_of`, `D_sub_DS`, `DS_sub_D`, `DS_iff_D`, `sup_supS`, `supS_sup`, `confirmed_liftS_of`,
      `confirmedS_iff`: where the static rule never fires, the two runs and the two confirmations
      are the same. The weakest form (`confirmed_liftS_of`: no fire on an edge of `D`, the deep
      answer equals the chain answer on every request of `D`) lifts a base confirmation to a
      `ConfirmedS`; with no initial fact of `D` on the static base (`NoStaticInit`) the two
      confirmations are equivalent (`confirmedS_iff`). `noStaticInit_of`: a program with no call
      binding into `S` (with `policy1` and `S ≠ zero`) has no such initial fact.
    * `ExampleConf` (`Statics.Example` under the final rule): CONFIRMED in run 1 (`confirmed`), real
      (`real`), while run 1 without the static rule confirms nothing (`not_confirmed_D`).
      `AboveConf`, `WideConf` (`CexAbove`, `CexWide` under the final rule): CONFIRMED and real.
      `CleanConf` (`CexClean` under the final rule): CONFIRMED and real through the DEEP answer
      (`deep_needed`: the chain answer of that request is not the added fact).
    * `CexS.cexS_filt`, `CexS.cexS_mark`: each hypothesis is necessary EVEN UNDER `SWF` AND
      `Design`: the base counterexamples `Confirmed.CexConfFilt` (no `FiltUp`) and
      `Confirmed.CexConfMark` (no `MarkWF`) with an unused static base (`swf_of_fresh`,
      `noStaticInit_of_fresh`, `confirmed_alpha`) are confirmed in `DS` and not real.

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.Statics
import ApSpec.Confirmed

namespace ApSpec.StaticsConfirmed
open ApSpec ApSpec.Statics

/-! ## 1. Under a non-`*` initial fact every final fact of `DS` is non-`*` -/

/-- The motive: under a non-`*` initial fact the final fact is non-`*`. -/
def NSS : SObj → Prop
  | .edge _ i _ f => i.kind.isStar = false → f.fact.kind.isStar = false
  | _ => True

/-- A summary application keeps a non-`*` caller fact non-`*`. -/
theorem ret_nonstar {counted : Acc → Bool} {L : Nat} {f a r r' g : AFact} {e1 e2 : MicroEdge}
    {j : PFact} (hf : f.fact.kind.isStar = false) (ha : a ∈ (applyEdge f e1.1 e1.2).facts)
    (hr : r ∈ (applySummary a j g).facts) (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) :
    (limitF counted L r').fact.kind.isStar = false := by
  have h1 := Confirmed.applyEdge_nonstar hf ha
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
  have h2 := Confirmed.applyEdge_nonstar h1 hx
  have h3 : (AFact.norm ⟨x.fact, x.demand || g.demand⟩).fact.kind.isStar = false := by
    rw [Confirmed.norm_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) h2]
    exact h2
  exact Confirmed.limitF_nonstar (Confirmed.applyEdge_nonstar h3 hr')

/-- The analogue of `Confirmed.D_NS` for `DS`. -/
theorem DS_NS {X : SCtx} {o : SObj} (h : DS X o) : NSS o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact fun hi => Confirmed.startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf' ih => exact fun hi => Confirmed.transfer_nonstar (ih hi) hf'
  | reqStmt => trivial
  | sreqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | ret _ _ _ ha _ _ _ hr _ hr' ihF _ _ => exact fun hi => ret_nonstar (ihF hi) ha hr hr'
  | sret _ _ _ ha _ _ _ hr _ hr' ihF _ _ => exact fun hi => ret_nonstar (ihF hi) ha hr hr'
  | reqSink => trivial
  | answer => trivial
  | sanswer => trivial
  | reqUp => trivial
  | sreqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih => exact fun hi => Confirmed.cleanRes_nonstar (ih hi) hf'
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DS_NS

/-! ## 2. Support and confirmation over `DS` -/

/-- The normal-layer SUPPORT of initial facts of run 1 with the static rule (§4.9 condition 3).
    The answer of a mark request is read with the answer rule of `DS` (`X.ansInit`: the deep answer
    on a static premise, else the chain answer), and it must BE the added fact (`j = a.fact`). -/
inductive SupS (X : SCtx) : MethodId → PFact → Prop where
  | root {M} : M ∈ X.roots → SupS X M zeroFact
  | call {M i n f n' c e a j} :
      SupS X M i → DS X (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ X.P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DS X (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DS X (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = X.ansInit k a.fact t ∧ j = a.fact)) →
      SupS X c.callee j

/-- A CONFIRMED vulnerability of run 1 with the static rule: a complete sink edge of `DS` (normal
    layer, no `[any]`) under a supported initial fact, and a triggered sink check. -/
def ConfirmedS (X : SCtx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, DS X (.edge M i n f) ∧ SupS X M i ∧ f.complete = true ∧ (M, n, s) ∈ X.sinks ∧
    check i f s = .triggered

/-- A confirmed vulnerability is a `vuln` object of `DS` in the normal layer. -/
theorem confirmedS_vuln {X : SCtx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedS X M n s) : DS X (.vuln M n s false) := by
  obtain ⟨i, f, hD, _, hc, hs, hch⟩ := h
  have hv := DS.vuln hD hs hch
  rw [Exact.complete_demand hc] at hv
  exact hv

#print axioms confirmedS_vuln

/-- One step of the support: the added fact is exact with a concrete mark and it is `j`. -/
theorem supS_step {X : SCtx} {a : AFact} {j : PFact} {Q : PFact → Mark → Prop}
    (hj : (j = zeroFact ∧ a.fact = zeroFact) ∨
      (∃ k t, Q k t ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = X.ansInit k a.fact t ∧
        j = a.fact)) :
    ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
  rcases hj with ⟨hj0, hz⟩ | ⟨_, t, _, hak, ham, _, hja⟩
  · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
  · exact ⟨t, hak, ham, hja⟩

/-- Condition 2 follows from condition 3: a supported initial fact is exact with a concrete
    mark. -/
theorem supS_exactConc {X : SCtx} {M : MethodId} {i : PFact} (h : SupS X M i) :
    i.kind = .exact ∧ ∃ t, i.mark = .conc t := by
  cases h with
  | root _ => exact ⟨rfl, zeroMark, rfl⟩
  | call _ _ _ _ _ _ _ _ hj =>
    obtain ⟨t, hak, ham, rfl⟩ := supS_step hj
    exact ⟨hak, t, ham⟩

#print axioms supS_exactConc

/-- A POSITION ANSWER `(S, p, *, {}, *)` is never a supported premise. -/
theorem sAns_not_supS {X : SCtx} {M : MethodId} {sB : Base} {p : List Acc} :
    ¬ SupS X M (sAns sB p) := by
  intro h
  have hk := (supS_exactConc h).1
  cases hk

#print axioms sAns_not_supS

/-- THE DEEP ANSWER IS THE ADDED FACT: a mark request on a static premise `k`, answered (with the
    deep answer) by an added fact `a` with the mark `t` at or below `k`, gives `a` itself. So the
    support condition `j = X.ansInit k a t ∧ j = a` holds for every exact such `a`. -/
theorem ansInit_deep_self {X : SCtx} {k a : PFact} {t : Mark} (hd : X.deepAns = true)
    (hb : k.base = X.sB) (hbel : (dropPrefix k.path a.path).isSome = true)
    (hm : a.mark = .conc t) : X.ansInit k a t = a := by
  have h1 : Nat.beq k.base X.sB = true := by rw [hb]; exact Nat.beq_refl _
  unfold SCtx.ansInit
  rw [hd, h1, hbel]
  obtain ⟨b, p, kd, m⟩ := a
  have hm' : m = .conc t := hm
  subst hm'
  rfl

#print axioms ansInit_deep_self

/-- The chain answer is the added fact when the request premise is at the position of `a`. -/
theorem answerInit_self {k a : PFact} {t : Mark} (hb : k.base = a.base) (hp : k.path = a.path)
    (hk : a.kind = .exact) (hm : a.mark = .conc t) : answerInit k a t = a := by
  obtain ⟨b, p, kd, m⟩ := a
  obtain ⟨kb, kp, kk, km⟩ := k
  have hb' : kb = b := hb
  have hp' : kp = p := hp
  have hk' : kd = .exact := hk
  have hm' : m = .conc t := hm
  subst hb' hp' hk' hm'
  unfold answerInit
  rw [Exact.dropPrefix_self]

#print axioms answerInit_self

/-! ### 2.1 What the support needs: abstract caller premises add nothing -/

/-- Under `MarkWF`, an edge of `DS` under an abstract-mark initial fact has an abstract mark
    (the first part of `DS_edgeOK`). -/
theorem edge_abs {X : SCtx} (hmw : Exact.MarkWF X.P) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DS X (.edge M i n f)) (hi : Exact.absB i.mark = true) :
    Exact.absB f.fact.mark = true :=
  (DS_edgeOK (ok := fun _ => False) hmw (fun _ _ _ _ _ _ _ _ _ _ _ hok _ => hok.elim)
    ⟨fun _ _ _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ _ _ _ _ h => h.elim,
     fun _ _ _ _ _ _ _ _ _ _ h => h.elim⟩ h).1 hi

/-- The RELAXED support: a caller premise of a support step may also be ANY initial fact of `DS`
    with an abstract mark (a position answer `(S, p, *, {}, *)`, a static root, a policy fact). -/
inductive SupR (X : SCtx) : MethodId → PFact → Prop where
  | root {M} : M ∈ X.roots → SupR X M zeroFact
  | call {M i n f n' c e a j} :
      SupR X M i → DS X (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ X.P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DS X (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DS X (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = X.ansInit k a.fact t ∧ j = a.fact)) →
      SupR X c.callee j
  /-- the relaxation: the caller premise is any initial fact with an abstract mark -/
  | callAbs {M i n f n' c e a j} :
      DS X (.init M i) → Exact.absB i.mark = true → DS X (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ X.P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DS X (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DS X (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = X.ansInit k a.fact t ∧ j = a.fact)) →
      SupR X c.callee j

/-- THE POSITION ANSWER IS NOT NEEDED ON THE SUPPORT CHAIN: under `MarkWF` the relaxed support is
    the support. A support step through a caller edge under an abstract-mark premise is vacuous:
    the bound added fact has an abstract mark, so it is neither the zero fact nor exact concrete. -/
theorem supR_iff {X : SCtx} (hmw : Exact.MarkWF X.P) {M : MethodId} {j : PFact} :
    SupR X M j ↔ SupS X M j := by
  constructor
  · intro h
    induction h with
    | root hM => exact SupS.root hM
    | call _ hD hfd hE he ha had hinit hj ih => exact SupS.call ih hD hfd hE he ha had hinit hj
    | @callAbs M i n f n' c e a j _ habs hD _ hE he ha _ _ hj =>
      exfalso
      have hA : Exact.absB a.fact.mark = true :=
        Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e he) (edge_abs hmw hD habs) ha
      obtain ⟨t, _, ham, _⟩ := supS_step (X := X) hj
      rw [ham] at hA
      cases hA
  · intro h
    induction h with
    | root hM => exact SupR.root hM
    | call _ hD hfd hE he ha had hinit hj ih => exact SupR.call ih hD hfd hE he ha had hinit hj

#print axioms supR_iff

/-- An abstract-mark initial fact (in particular a position answer) is never the premise of a
    TRIGGERED sink edge under `MarkWF`: the sink fact has an abstract mark, and the check then reads
    the abstract premise mark. -/
theorem abs_premise_no_trigger {X : SCtx} (hmw : Exact.MarkWF X.P) {M : MethodId} {i : PFact}
    {n : Node} {f : AFact} {s : PFact} (h : DS X (.edge M i n f)) (hi : Exact.absB i.mark = true) :
    check i f s ≠ .triggered := by
  have hf := edge_abs hmw h hi
  intro hc
  unfold check at hc
  cases hsm : s.mark with
  | star => rw [hsm] at hc; cases hc
  | starEx _ => rw [hsm] at hc; cases hc
  | conc T =>
    rw [hsm] at hc
    cases ho : overlapB f.fact s with
    | false => rw [ho] at hc; cases hc
    | true =>
      rw [ho] at hc
      cases hfm : f.fact.mark with
      | conc _ => rw [hfm] at hf; cases hf
      | star =>
        rw [hfm] at hc
        cases him : i.mark with
        | conc _ => rw [him] at hi; cases hi
        | star => rw [him] at hc; cases hc
        | starEx _ => rw [him] at hc; cases hc
      | starEx x =>
        rw [hfm] at hc
        dsimp only at hc
        cases hx : memB T x with
        | true => rw [hx] at hc; cases hc
        | false =>
          rw [hx] at hc
          cases him : i.mark with
          | conc _ => rw [him] at hi; cases hi
          | star => rw [him] at hc; cases hc
          | starEx _ => rw [him] at hc; cases hc

#print axioms abs_premise_no_trigger

/-! ## 3. A supported initial fact is real at the entry -/

/-- A supported initial fact is exact with a concrete mark, and its unique location is
    entry-reachable (the hypotheses of `edge_exactS`). -/
theorem supS_entry {X : SCtx} {M : MethodId} {i : PFact}
    (hmw : Exact.MarkWF X.P) (hup : Exact.FiltUp X.P) (h : SupS X M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach X.P X.roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := supS_step hj
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hR := Confirmed.entry_reach X.P X.roots hent (edge_exactS hmw hup hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms supS_entry

/-- The same for prefix-closed type filters: the location is entry-reachable if it is valid. -/
theorem supS_entry_valid {X : SCtx} {M : MethodId} {i : PFact} {ok : Loc → Prop}
    (hmw : Exact.MarkWF X.P) (hv : Exact.FiltValid X.P ok) (hbo : Exact.BackOK X.P ok)
    (h : SupS X M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      (ok ⟨i.base, i.path, t⟩ → Confirmed.EntryReach X.P X.roots M ⟨i.base, i.path, t⟩) := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, fun _ => Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := supS_step hj
    refine ⟨t, hak, ham, fun hokj => ?_⟩
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hokl : ok l := hbo.toC _ _ _ _ hE e he _ _ hd2 hokj
    obtain ⟨hfl, hok0⟩ := edge_exact_validS hmw hv hbo hD hfd hd1 hokl
    exact Or.inr ⟨M, n, l, n', c, e, Confirmed.entry_reach X.P X.roots (hent hok0) hfl, hE, rfl,
      he, hd2⟩

#print axioms supS_entry_valid

/-! ## 4. THE CONFIRMATION THEOREM of run 1 with the static rule -/

/-- The sink location of a confirmed vulnerability of `DS` (the analogue of
    `Confirmed.confirmed_sink`). -/
theorem confirmed_sinkS {X : SCtx} {M : MethodId} {n : Node} {s i : PFact} {f : AFact}
    {t0 : Mark} (hD : DS X (.edge M i n f)) (hc : f.complete = true)
    (hch : check i f s = .triggered) (hik : i.kind = .exact) (him : i.mark = .conc t0) :
    den i f.fact ⟨i.base, i.path, t0⟩ ⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩ ∧
      s.covers ⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩ := by
  have hns : f.fact.kind.isStar = false := DS_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo, hps⟩ := Confirmed.check_triggered_passes him hch
  exact ⟨Confirmed.den_exact_exact him hfk hps,
    Confirmed.overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)⟩

#print axioms confirmed_sinkS

/-- THE CONFIRMATION THEOREM OF RUN 1 WITH THE STATIC RULE (programs without a real type filter,
    `FiltUp`): a confirmed vulnerability of `DS` is a real concrete vulnerability. It holds for
    every variant of the rule, in particular the final rule (`Design X`, under `SWF X`). -/
theorem confirmed_realS {X : SCtx} {M : MethodId} {n : Node} {s : PFact}
    (hmw : Exact.MarkWF X.P) (hup : Exact.FiltUp X.P) (h : ConfirmedS X M n s) :
    ∃ l, Reach X.P X.roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := supS_entry hmw hup hS
  obtain ⟨hden, hcov⟩ := confirmed_sinkS hD hc hch hik him
  exact ⟨_, Confirmed.entry_reach X.P X.roots hent
    (edge_exactS hmw hup hD (Exact.complete_demand hc) hden), hcov⟩

#print axioms confirmed_realS

/-- THE CONFIRMATION THEOREM FOR VALID LOCATIONS (prefix-closed type filters): a confirmed
    vulnerability of `DS` has a location in the sink pattern, reached if it is valid. -/
theorem confirmed_realS_valid_of {X : SCtx} {M : MethodId} {n : Node} {s : PFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.P) (hv : Exact.FiltValid X.P ok)
    (hbo : Exact.BackOK X.P ok) (h : ConfirmedS X M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach X.P X.roots M n l) := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := supS_entry_valid hmw hv hbo hS
  obtain ⟨hden, hcov⟩ := confirmed_sinkS hD hc hch hik him
  refine ⟨_, hcov, fun hok => ?_⟩
  obtain ⟨hfl, hok0⟩ := edge_exact_validS hmw hv hbo hD (Exact.complete_demand hc) hden hok
  exact Confirmed.entry_reach X.P X.roots (hent hok0) hfl

#print axioms confirmed_realS_valid_of

/-- THE CONFIRMATION THEOREM FOR A REAL PROGRAM with prefix-closed type filters: if every location
    of the sink pattern is valid, a confirmed vulnerability of `DS` is real. -/
theorem confirmed_realS_valid {X : SCtx} {M : MethodId} {n : Node} {s : PFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.P) (hv : Exact.FiltValid X.P ok)
    (hbo : Exact.BackOK X.P ok) (hok : ∀ l, s.covers l → ok l) (h : ConfirmedS X M n s) :
    ∃ l, Reach X.P X.roots M n l ∧ s.covers l := by
  obtain ⟨l, hcov, hR⟩ := confirmed_realS_valid_of hmw hv hbo h
  exact ⟨l, hR (hok l hcov), hcov⟩

#print axioms confirmed_realS_valid

/-! ## 5. Where the static rule never fires, the confirmations are the same -/

/-- Run 1 without the static rule on the program of `X`. -/
abbrev DX (X : SCtx) : Obj → Prop := D X.P X.counted X.FL X.α X.sinks X.roots

/-- The objects of `D` as objects of `DS`. -/
def liftO : Obj → SObj
  | .init M i => .init M i
  | .edge M i n f => .edge M i n f
  | .added M a => .added M a
  | .req M i t => .req M i t
  | .vuln M n s d => .vuln M n s d

/-- The premise of an edge or a request of `D` is an initial fact of `D`. -/
def PremInit (X : SCtx) : Obj → Prop
  | .edge M i _ _ => DX X (.init M i)
  | .req M i _ => DX X (.init M i)
  | _ => True

theorem premInit_all {X : SCtx} {o : Obj} (h : DX X o) : PremInit X o := by
  induction h with
  | root => trivial
  | start hi _ => exact hi
  | step _ _ _ ih => exact ih
  | reqStmt _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | ret _ _ _ _ _ _ _ _ _ _ ihF _ _ => exact ihF
  | reqSink _ _ _ ih => exact ih
  | answer => trivial
  | reqUp _ _ _ _ _ _ _ _ _ ihF => exact ihF
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih

#print axioms premInit_all

/-- A statement from which nothing is dropped is the statement itself. -/
theorem sKeep_id {P : MicroEdge → Bool} {s : Stmt} (h : ∀ e, e ∈ s.edges → P e = false) :
    sKeepP P s = s := by
  obtain ⟨tc, es⟩ := s
  unfold sKeepP
  have hf : es.filter (fun e => !P e) = es :=
    List.filter_eq_self.mpr (fun e he => by rw [h e he]; rfl)
  rw [hf]

/-- The rule does not fire on an edge whose premise is not on the static base. -/
theorem fireB_off {X : SCtx} {i : PFact} {f : AFact} {e : MicroEdge} (hb : i.base ≠ X.sB) :
    X.fireB i f e = false := by
  have h1 : Nat.beq i.base X.sB = false := beq_false_of_ne hb
  have h2 : sRootB X.sB i = false := by
    cases h : sRootB X.sB i with
    | false => rfl
    | true =>
      obtain ⟨E, rfl⟩ := sRootB_eq h
      exact absurd rfl hb
  unfold SCtx.fireB genFireB idEdgeB sFireB
  rw [h1, h2]
  split <;> rfl

/-- The deep answer is the chain answer on a premise that is not on the static base. -/
theorem ansInit_off {X : SCtx} {i a : PFact} {t : Mark} (hb : i.base ≠ X.sB) :
    X.ansInit i a t = answerInit i a t := by
  have h1 : Nat.beq i.base X.sB = false := beq_false_of_ne hb
  unfold SCtx.ansInit
  rw [h1, Bool.and_false, Bool.false_and]
  rfl

/-- The overlap reading never applies to a callee initial fact that is not on the static base. -/
theorem fbOK_off {X : SCtx} {i a j : PFact} (hb : j.base ≠ X.sB) : X.fbOK i a j = false := by
  have h1 : Nat.beq j.base X.sB = false := beq_false_of_ne hb
  have h2 : sAboveB X.sB i a j = false := by
    unfold sAboveB
    rw [h1]
    rfl
  unfold SCtx.fbOK
  split
  · rfl
  · rw [h2, Bool.and_false]
  · exact h2

/-- THE EMBEDDING, weakest form: if the static rule fires on no edge of `D` and the deep answer is
    the chain answer on every mark request of `D`, every object of `D` is an object of `DS`. -/
theorem D_sub_DS_of {X : SCtx}
    (hfire : ∀ M i n f n' s e, DX X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      e ∈ s.edges → X.fireB i f e = false)
    (hans : ∀ M i t a, DX X (.req M i t) → X.ansInit i a t = answerInit i a t)
    {o : Obj} (h : DX X o) : DS X (liftO o) := by
  induction h with
  | root hM => exact DS.root hM
  | start _ ih => exact DS.start ih
  | @step M i n f n' s f' hD hE hf ih =>
    refine DS.step ih hE ?_
    rw [sKeep_id (fun e he => hfire M i n f n' s e hD hE he)]
    exact hf
  | @reqStmt M i n f n' s t hD hE hq ih =>
    refine DS.reqStmt ih hE ?_
    rw [sKeep_id (fun e he => hfire M i n f n' s e hD hE he)]
    exact hq
  | pass _ hE hm ih => exact DS.pass ih hE hm
  | added _ hE he ha ih => exact DS.added ih hE he ha
  | initA _ ih => exact DS.initA ih
  | ret _ hE he1 ha _ hap _ hr he2 hr' ihF ihJ ihG =>
    exact DS.ret ihF hE he1 ha ihJ hap ihG hr he2 hr'
  | reqSink _ hs hc ih => exact DS.reqSink ih hs hc
  | @answer M i t a hq _ hm hov ihq iha =>
    have e := DS.answer ihq iha hm hov
    rw [hans M i t a hq] at e
    exact e
  | reqUp _ _ hE hc he ha hcl hov ihq ihF => exact DS.reqUp ihq ihF hE hc he ha hcl hov
  | vuln _ hs hc ih => exact DS.vuln ih hs hc
  | clean _ hE hf ih => exact DS.clean ih hE hf
  | reqClean _ hE hq ih => exact DS.reqClean ih hE hq
  | filt _ hE hp ih => exact DS.filt ih hE hp

#print axioms D_sub_DS_of

/-- The support of `D` is a support of `DS` (same hypotheses). -/
theorem sup_supS_of {X : SCtx}
    (hfire : ∀ M i n f n' s e, DX X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      e ∈ s.edges → X.fireB i f e = false)
    (hans : ∀ M i t a, DX X (.req M i t) → X.ansInit i a t = answerInit i a t)
    {M : MethodId} {i : PFact}
    (h : Confirmed.Sup X.P X.counted X.FL X.α X.sinks X.roots M i) : SupS X M i := by
  induction h with
  | root hM => exact SupS.root hM
  | call _ hD hfd hE he ha had hinit hj ih =>
    refine SupS.call ih (D_sub_DS_of hfire hans hD) hfd hE he ha had
      (D_sub_DS_of hfire hans hinit) ?_
    rcases hj with h0 | ⟨k, t, hq, hak, ham, hjk, hja⟩
    · exact .inl h0
    · exact .inr ⟨k, t, D_sub_DS_of hfire hans hq, hak, ham,
        by rw [hans _ _ _ _ hq]; exact hjk, hja⟩

#print axioms sup_supS_of

/-- A BASE CONFIRMATION IS A CONFIRMATION WITH THE STATIC RULE when the rule never fires on run 1:
    no fire on an edge of `D`, and the deep answer is the chain answer on every request of `D`. -/
theorem confirmed_liftS_of {X : SCtx}
    (hfire : ∀ M i n f n' s e, DX X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      e ∈ s.edges → X.fireB i f e = false)
    (hans : ∀ M i t a, DX X (.req M i t) → X.ansInit i a t = answerInit i a t)
    {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed.Confirmed X.P X.counted X.FL X.α X.sinks X.roots M n s) :
    ConfirmedS X M n s := by
  obtain ⟨i, f, hD, hS, hc, hs, hch⟩ := h
  exact ⟨i, f, D_sub_DS_of hfire hans hD, sup_supS_of hfire hans hS, hc, hs, hch⟩

#print axioms confirmed_liftS_of

/-- THE STATIC RULE NEVER FIRES: run 1 without it has no initial fact on the static base. Then no
    edge or request of `D` has a static premise, so nothing fires and the deep answer is the chain
    answer. -/
def NoStaticInit (X : SCtx) : Prop := ∀ M i, DX X (.init M i) → i.base ≠ X.sB

theorem noStatic_fire {X : SCtx} (hns : NoStaticInit X) :
    ∀ M i n f n' s e, DX X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ X.P.edges →
      e ∈ s.edges → X.fireB i f e = false := by
  intro M i n f n' s e hD _ _
  have hi : DX X (.init M i) := premInit_all hD
  exact fireB_off (hns M i hi)

theorem noStatic_ans {X : SCtx} (hns : NoStaticInit X) :
    ∀ M i t a, DX X (.req M i t) → X.ansInit i a t = answerInit i a t := by
  intro M i t a hq
  have hi : DX X (.init M i) := premInit_all hq
  exact ansInit_off (hns M i hi)

theorem D_sub_DS {X : SCtx} (hns : NoStaticInit X) {o : Obj} (h : DX X o) : DS X (liftO o) :=
  D_sub_DS_of (noStatic_fire hns) (noStatic_ans hns) h

#print axioms D_sub_DS

/-- The objects of `DS` that are objects of `D` (a position request is not). -/
def InD (X : SCtx) : SObj → Prop
  | .init M i => DX X (.init M i)
  | .edge M i n f => DX X (.edge M i n f)
  | .added M a => DX X (.added M a)
  | .req M i t => DX X (.req M i t)
  | .sreq _ _ _ => False
  | .vuln M n s d => DX X (.vuln M n s d)

/-- THE CONVERSE EMBEDDING: without an initial fact of `D` on the static base, every object of
    `DS` is an object of `D`, and `DS` raises no position request. -/
theorem DS_sub_D {X : SCtx} (hns : NoStaticInit X) {o : SObj} (h : DS X o) : InD X o := by
  induction h with
  | root hM => exact D.root hM
  | start _ ih => exact D.start ih
  | @step M i n f n' s f' _ hE hf ih =>
    have ih' : DX X (.edge M i n f) := ih
    have hi : DX X (.init M i) := premInit_all ih'
    rw [sKeep_id (fun e _ => fireB_off (hns M i hi))] at hf
    exact D.step ih' hE hf
  | @reqStmt M i n f n' s t _ hE hq ih =>
    have ih' : DX X (.edge M i n f) := ih
    have hi : DX X (.init M i) := premInit_all ih'
    rw [sKeep_id (fun e _ => fireB_off (hns M i hi))] at hq
    exact D.reqStmt ih' hE hq
  | @sreqStmt M i n f n' s e _ _ _ hfire ih =>
    have ih' : DX X (.edge M i n f) := ih
    have hi : DX X (.init M i) := premInit_all ih'
    rw [fireB_off (hns M i hi)] at hfire
    cases hfire
  | pass _ hE hm ih => exact D.pass ih hE hm
  | added _ hE he ha ih => exact D.added ih hE he ha
  | initA _ ih => exact D.initA ih
  | ret _ hE he1 ha _ hap _ hr he2 hr' ihF ihJ ihG =>
    exact D.ret ihF hE he1 ha ihJ hap ihG hr he2 hr'
  | @sret M i n f n' c e1 a j g r e2 r' _ _ _ _ _ hok _ _ _ _ _ ihJ _ =>
    have ihJ' : DX X (.init c.callee j) := ihJ
    rw [fbOK_off (hns _ _ ihJ')] at hok
    cases hok
  | reqSink _ hs hc ih => exact D.reqSink ih hs hc
  | @answer M i t a _ _ hm hov ihq iha =>
    have ihq' : DX X (.req M i t) := ihq
    have hi : DX X (.init M i) := premInit_all ihq'
    show DX X (.init M (X.ansInit i a t))
    rw [ansInit_off (hns M i hi)]
    exact D.answer ihq' iha hm hov
  | sanswer _ _ _ ihs _ => exact ihs.elim
  | reqUp _ _ hE hc he ha hcl hov ihq ihF => exact D.reqUp ihq ihF hE hc he ha hcl hov
  | sreqUp _ _ _ _ _ _ _ ihs _ => exact ihs.elim
  | vuln _ hs hc ih => exact D.vuln ih hs hc
  | clean _ hE hf ih => exact D.clean ih hE hf
  | reqClean _ hE hq ih => exact D.reqClean ih hE hq
  | filt _ hE hp ih => exact D.filt ih hE hp

#print axioms DS_sub_D

/-- Without an initial fact on the static base, `DS` and `D` have the same objects. -/
theorem DS_iff_D {X : SCtx} (hns : NoStaticInit X) (o : Obj) : DS X (liftO o) ↔ DX X o := by
  constructor
  · intro h
    have h' := DS_sub_D hns h
    cases o <;> exact h'
  · exact D_sub_DS hns

#print axioms DS_iff_D

/-- The support of `DS` is a support of `D`. -/
theorem supS_sup {X : SCtx} (hns : NoStaticInit X) {M : MethodId} {i : PFact} (h : SupS X M i) :
    Confirmed.Sup X.P X.counted X.FL X.α X.sinks X.roots M i := by
  induction h with
  | root hM => exact Confirmed.Sup.root hM
  | @call M i n f n' c e a j _ hD hfd hE he ha had hinit hj ih =>
    have hD' : DX X (.edge M i n f) := DS_sub_D hns hD
    have hinit' : DX X (.init c.callee j) := DS_sub_D hns hinit
    refine Confirmed.Sup.call ih hD' hfd hE he ha had hinit' ?_
    rcases hj with h0 | ⟨k, t, hq, hak, ham, hjk, hja⟩
    · exact .inl h0
    · have hq' : DX X (.req c.callee k t) := DS_sub_D hns hq
      have hk : DX X (.init c.callee k) := premInit_all hq'
      exact .inr ⟨k, t, hq', hak, ham, by rw [← ansInit_off (hns _ _ hk)]; exact hjk, hja⟩

#print axioms supS_sup

theorem sup_supS {X : SCtx} (hns : NoStaticInit X) {M : MethodId} {i : PFact}
    (h : Confirmed.Sup X.P X.counted X.FL X.α X.sinks X.roots M i) : SupS X M i :=
  sup_supS_of (noStatic_fire hns) (noStatic_ans hns) h

#print axioms sup_supS

/-- THE TWO CONFIRMATIONS ARE THE SAME where the static rule never fires (no initial fact of run 1
    on the static base). -/
theorem confirmedS_iff {X : SCtx} (hns : NoStaticInit X) {M : MethodId} {n : Node} {s : PFact} :
    ConfirmedS X M n s ↔ Confirmed.Confirmed X.P X.counted X.FL X.α X.sinks X.roots M n s := by
  constructor
  · rintro ⟨i, f, hD, hS, hc, hs, hch⟩
    exact ⟨i, f, DS_sub_D hns hD, supS_sup hns hS, hc, hs, hch⟩
  · rintro ⟨i, f, hD, hS, hc, hs, hch⟩
    exact ⟨i, f, D_sub_DS hns hD, sup_supS hns hS, hc, hs, hch⟩

#print axioms confirmedS_iff

/-! ### 5.1 A syntactic condition: no call binds the static base -/

/-- The motive: initial facts, premises and added facts of `D` are off the static base. -/
def NoS (X : SCtx) : Obj → Prop
  | .init _ i => i.base ≠ X.sB
  | .edge _ i _ _ => i.base ≠ X.sB
  | .added _ a => a.base ≠ X.sB
  | .req _ i _ => i.base ≠ X.sB
  | .vuln _ _ _ _ => True

/-- A program in which NO CALL BINDS INTO THE STATIC BASE (run 1 with `policy1`, `S` not the zero
    base) has no initial fact on `S`: the static rule never fires, and `confirmedS_iff` applies.
    Statements may still read and write statics (under non-static premises). -/
theorem noStaticInit_of {X : SCtx} (hz : X.sB ≠ zeroBase) (hα : X.α = policy (fun _ => []))
    (hbind : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.toCallee →
      e.2.base ≠ X.sB) :
    NoStaticInit X := by
  have key : ∀ {o : Obj}, DX X o → NoS X o := by
    intro o h
    induction h with
    | root => exact fun h => hz h.symm
    | start _ ih => exact ih
    | step _ _ _ ih => exact ih
    | reqStmt _ _ _ ih => exact ih
    | pass _ _ _ ih => exact ih
    | @added M i n f n' c e a _ hE he ha _ =>
      show a.fact.base ≠ X.sB
      rw [applyEdge_base ha]
      exact hbind _ _ _ _ hE e he
    | @initA m a _ ih =>
      show (X.α m a).base ≠ X.sB
      have ih' : a.base ≠ X.sB := ih
      rw [hα]
      unfold policy
      split
      · exact fun h => hz h.symm
      · split
        · exact ih'
        · exact ih'
    | ret _ _ _ _ _ _ _ _ _ _ ihF _ _ => exact ihF
    | reqSink _ _ _ ih => exact ih
    | @answer M i t a _ _ _ _ ihq _ =>
      show (answerInit i a t).base ≠ X.sB
      rw [answerInit_base]
      exact ihq
    | reqUp _ _ _ _ _ _ _ _ _ ihF => exact ihF
    | vuln => trivial
    | clean _ _ _ ih => exact ih
    | reqClean _ _ _ ih => exact ih
    | filt _ _ _ ih => exact ih
  exact fun M i h => key h

#print axioms noStaticInit_of

/-! ## 6. Decidable checks of `MarkWF` and `FiltUp` for concrete programs -/

def edgesMarkB (es : List MicroEdge) : Bool := es.all (fun e => Exact.markEdgeB e.1.mark e.2.mark)

def instrMarkB : Instr → Bool
  | .stmt s => edgesMarkB s.edges
  | .call c => edgesMarkB c.toCallee && edgesMarkB c.fromCallee
  | .clean _ => true
  | .filt _ _ => true

def noFiltB : Instr → Bool
  | .filt _ _ => false
  | _ => true

theorem markWF_of {P : Program} (h : P.edges.all (fun x => instrMarkB x.2.2.1) = true) :
    Exact.MarkWF P where
  stmt := by
    intro M n s n' hE e he
    have h1 : instrMarkB (Instr.stmt s) = true := List.all_eq_true.mp h _ hE
    exact List.all_eq_true.mp h1 e he
  toC := by
    intro M n c n' hE e he
    have h1 : instrMarkB (Instr.call c) = true := List.all_eq_true.mp h _ hE
    have h2 : (edgesMarkB c.toCallee && edgesMarkB c.fromCallee) = true := h1
    rw [Bool.and_eq_true] at h2
    exact List.all_eq_true.mp h2.1 e he
  fromC := by
    intro M n c n' hE e he
    have h1 : instrMarkB (Instr.call c) = true := List.all_eq_true.mp h _ hE
    have h2 : (edgesMarkB c.toCallee && edgesMarkB c.fromCallee) = true := h1
    rw [Bool.and_eq_true] at h2
    exact List.all_eq_true.mp h2.2 e he

theorem filtUp_of {P : Program} (h : P.edges.all (fun x => noFiltB x.2.2.1) = true) :
    Exact.FiltUp P := by
  intro M n b may n' hE
  have h1 : noFiltB (Instr.filt b may) = true := List.all_eq_true.mp h _ hE
  cases h1

/-! ## 7. Examples: the static programs are CONFIRMED in run 1 -/

/-! ### `Statics.Example` under the final rule

`root: C1.f = source(); A()`, `A: B()`, `B: x = C1.f; sink(x)`. The position request of `B`'s read
climbs to `A`, `A` and `B` answer `(S, <C1>.f, *, {}, *)`, the sink's mark request on that answer
climbs to `A`, and the root's `(S, <C1>.f, $, 7)` answers it exactly in `A`; `A` passes it to `B`,
which answers its own request with it. The support chain: root zero fact → `(S, <C1>.f, $, 7)` in
`A` (the answer of `(A, Ans, 7)`) → the same in `B` (the answer of `(B, Ans, 7)`). The position
answer `Ans` is the premise of both requests, never a supported premise. -/

namespace ExampleConf
open ApSpec.Statics.Example

/-- Run 1: the final rule on the example program. -/
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩

theorem x2_design : Design X2 := ⟨rfl, rfl, rfl, rfl, rfl⟩

def wSF : AFact := ⟨wS, false⟩
def AnsF : AFact := ⟨Ans, false⟩
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def xT : AFact := ⟨⟨xB, [], .exact, .conc T⟩, false⟩

theorem r_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem r_src : DS X2 (.edge 0 zeroFact 1 wSF) := DS.step r_start m_src (by decide)
theorem aA_w : DS X2 (.added 1 wS) := DS.added (a := wSF) r_src m_cA List.mem_cons_self (by decide)
theorem jA_root : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wS = Sroot := by decide
  exact h ▸ DS.initA aA_w
theorem eA_root : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start jA_root
theorem aB_root : DS X2 (.added 2 Sroot) :=
  DS.added (a := SrootF) eA_root m_cB List.mem_cons_self (by decide)
theorem jB_root : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 Sroot = Sroot := by decide
  exact h ▸ DS.initA aB_root
theorem eB_root : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start jB_root
theorem sB_req : DS X2 (.sreq 2 Sroot [C1, fA]) :=
  DS.sreqStmt (e := readE) eB_root m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem sA_req : DS X2 (.sreq 1 Sroot [C1, fA]) :=
  DS.sreqUp (a := SrootF) (e := bindS) sB_req eA_root m_cB rfl List.mem_cons_self
    (by decide) (by decide)
theorem jA_ans : DS X2 (.init 1 Ans) := DS.sanswer sA_req aA_w (by decide)
theorem eA_ans : DS X2 (.edge 1 Ans 0 AnsF) := DS.start jA_ans
theorem aB_ans : DS X2 (.added 2 Ans) :=
  DS.added (a := AnsF) eA_ans m_cB List.mem_cons_self (by decide)
theorem jB_ans : DS X2 (.init 2 Ans) := DS.sanswer sB_req aB_ans (by decide)
theorem eB_ans0 : DS X2 (.edge 2 Ans 0 AnsF) := DS.start jB_ans
theorem eB_ans1 : DS X2 (.edge 2 Ans 1 ⟨pat xB [], false⟩) := DS.step eB_ans0 m_rd (by decide)
theorem rB_ans : DS X2 (.req 2 Ans T) := DS.reqSink eB_ans1 m_sink (by decide)
theorem rA_ans : DS X2 (.req 1 Ans T) :=
  DS.reqUp (a := AnsF) (e := bindS) rB_ans eA_ans m_cB rfl List.mem_cons_self
    (by decide) (by decide) (by decide)
theorem ans_w : X2.ansInit Ans wS T = wS := by decide
theorem jA_w : DS X2 (.init 1 wS) := ans_w ▸ DS.answer rA_ans aA_w rfl (by decide)
theorem eA_w : DS X2 (.edge 1 wS 0 wSF) := DS.start jA_w
theorem aB_w : DS X2 (.added 2 wS) := DS.added (a := wSF) eA_w m_cB List.mem_cons_self (by decide)
theorem jB_w : DS X2 (.init 2 wS) := ans_w ▸ DS.answer rB_ans aB_w rfl (by decide)
theorem eB_w1 : DS X2 (.edge 2 wS 1 xT) := DS.step (DS.start jB_w) m_rd (by decide)

/-- The support chain: `(S, <C1>.f, $, 7)` is supported in `A` (from the root's zero fact)… -/
theorem supA : SupS X2 1 wS :=
  SupS.call (c := cA) (e := bindS) (a := wSF) (SupS.root List.mem_cons_self) r_src rfl m_cA
    List.mem_cons_self (by decide) rfl jA_w (.inr ⟨Ans, T, rA_ans, rfl, rfl, ans_w.symm, rfl⟩)

/-- …and in `B` (from `A`'s supported premise). -/
theorem supB : SupS X2 2 wS :=
  SupS.call (c := cB) (e := bindS) (a := wSF) supA eA_w rfl m_cB
    List.mem_cons_self (by decide) rfl jB_w (.inr ⟨Ans, T, rB_ans, rfl, rfl, ans_w.symm, rfl⟩)

/-- THE EXAMPLE IS CONFIRMED IN RUN 1 with the static rule. -/
theorem confirmed : ConfirmedS X2 2 1 sinkPat :=
  ⟨wS, xT, eB_w1, supB, rfl, m_sink, by decide⟩

#print axioms confirmed

theorem markWF : Exact.MarkWF prog := markWF_of (by decide)
theorem filtUp : Exact.FiltUp prog := filtUp_of (by decide)

/-- The confirmed vulnerability is real (`confirmed_realS`). -/
theorem real : ∃ l, Reach prog [0] 2 1 l ∧ sinkPat.covers l :=
  confirmed_realS (X := X2) markWF filtUp confirmed

#print axioms real

/-- Run 1 WITHOUT the static rule confirms nothing on this program: its only vulnerability is in
    the demand layer (`Example.d_only_demand`). -/
theorem not_confirmed_D {M : MethodId} {n : Node} {s : PFact} :
    ¬ Confirmed.Confirmed prog counted 2 α1 sinks [0] M n s := by
  rintro ⟨i, f, hD, _, hc, hs, hch⟩
  have hv := d_only_demand (D.vuln hD hs hch)
  rw [Exact.complete_demand hc] at hv
  cases hv

#print axioms not_confirmed_D

end ExampleConf

/-! ### `CexAbove` under the final rule: confirmed through the answer of a request on a position
answer -/

namespace AboveConf
open ApSpec.Statics.CexAbove

theorem ans_w : X2.ansInit Ans wS T = wS := by decide

theorem supC : SupS X2 1 wS :=
  SupS.call (c := cC) (e := bindS) (a := wF) (SupS.root List.mem_cons_self) y_src rfl m_cC
    List.mem_cons_self (by decide) rfl y_jCw (.inr ⟨Ans, T, y_rC, rfl, rfl, ans_w.symm, rfl⟩)

/-- `CexAbove` IS CONFIRMED IN RUN 1 with the final rule. -/
theorem confirmed : ConfirmedS X2 1 2 sinkPat :=
  ⟨wS, ⟨⟨rB, [], .exact, .conc T⟩, false⟩, y_eCw2, supC, rfl, m_sink, by decide⟩

#print axioms confirmed

theorem markWF : Exact.MarkWF prog := markWF_of (by decide)
theorem filtUp : Exact.FiltUp prog := filtUp_of (by decide)

theorem real : ∃ l, Reach prog [0] 1 2 l ∧ sinkPat.covers l :=
  confirmed_realS (X := X2) markWF filtUp confirmed

#print axioms real

end AboveConf

/-! ### `CexWide` under the final rule -/

namespace WideConf
open ApSpec.Statics.CexWide

theorem ans_g : X2.ansInit Ag wg T = wg := by decide

theorem supC : SupS X2 1 wg :=
  SupS.call (c := cC) (e := bindS) (a := wgF) (SupS.root List.mem_cons_self) w_src rfl m_cC
    List.mem_cons_self (by decide) rfl w_jCw (.inr ⟨Ag, T, w_rC, rfl, rfl, ans_g.symm, rfl⟩)

/-- `CexWide` IS CONFIRMED IN RUN 1 with the final rule. -/
theorem confirmed : ConfirmedS X2 1 4 sinkPat :=
  ⟨wg, rT, w_eCw4, supC, rfl, m_sink, by decide⟩

#print axioms confirmed

theorem markWF : Exact.MarkWF prog := markWF_of (by decide)
theorem filtUp : Exact.FiltUp prog := filtUp_of (by decide)

theorem real : ∃ l, Reach prog [0] 1 4 l ∧ sinkPat.covers l :=
  confirmed_realS (X := X2) markWF filtUp confirmed

#print axioms real

end WideConf

/-! ### `CexClean` under the final rule: the supported premise is a DEEP answer

The cleaner of `K` on the static root raises the mark request `(K, Sroot, 7)`; it climbs to the
caller, and the caller's added fact `(S, <C>.s, $, 7)` answers it at its OWN position (the deep
answer, `SCtx.ansInit`). That answer is the supported premise of the caller; the chain answer of the
same request is `(S, [], *, {}, 7)`, which is not the added fact (`deep_needed`). -/

namespace CleanConf
open ApSpec.Statics.CexClean

theorem ans_deep : Xd.ansInit Sroot ws T = ws := by decide

/-- The chain answer of the same request is not the added fact: the support step needs the deep
    answer (the base condition `j = answerInit k a t` rejects it). -/
theorem deep_needed : answerInit Sroot ws T ≠ ws := by decide

theorem supC : SupS Xd 1 ws :=
  SupS.call (c := cC) (e := bindS) (a := wsF) (SupS.root List.mem_cons_self) x_src rfl m_cC
    List.mem_cons_self (by decide) rfl x_jCw (.inr ⟨Sroot, T, x_rC, rfl, rfl, ans_deep.symm, rfl⟩)

/-- `CexClean` IS CONFIRMED IN RUN 1 with the final rule, through the deep answer. -/
theorem confirmed : ConfirmedS Xd 1 2 sinkPat :=
  ⟨ws, rT, x_eCw2, supC, rfl, m_sink, by decide⟩

#print axioms confirmed

theorem markWF : Exact.MarkWF prog := markWF_of (by decide)
theorem filtUp : Exact.FiltUp prog := filtUp_of (by decide)

theorem real : ∃ l, Reach prog [0] 1 2 l ∧ sinkPat.covers l :=
  confirmed_realS (X := Xd) markWF filtUp confirmed

#print axioms real

end CleanConf

/-! ## 8. The hypotheses are necessary, even under `SWF` and `Design`

A program that never mentions the static base satisfies `SWF` (`swf_of_fresh`) and has no initial
fact on it (`noStaticInit_of_fresh`), so `confirmedS_iff` turns the base counterexamples
`Confirmed.CexConfFilt` (no `FiltUp`) and `Confirmed.CexConfMark` (no `MarkWF`) into counterexamples
of `confirmed_realS` under the final rule. The static base is the unused base `99`. -/

/-- The base `b` is not the static base. -/
def offB (sB b : Base) : Bool := !Nat.beq b sB

theorem offB_ne {sB b : Base} (h : offB sB b = true) : b ≠ sB := by
  intro e
  subst e
  unfold offB at h
  rw [Nat.beq_refl] at h
  cases h

def edgeOffB (sB : Base) (e : MicroEdge) : Bool := offB sB e.1.base && offB sB e.2.base

theorem edgeOff {sB : Base} {e : MicroEdge} (h : edgeOffB sB e = true) :
    e.1.base ≠ sB ∧ e.2.base ≠ sB := by
  unfold edgeOffB at h
  rw [Bool.and_eq_true] at h
  exact ⟨offB_ne h.1, offB_ne h.2⟩

def instrOffB (sB : Base) : Instr → Bool
  | .stmt s => s.edges.all (edgeOffB sB)
  | .call c => c.toCallee.all (edgeOffB sB) && c.fromCallee.all (edgeOffB sB)
  | .clean cl => offB sB cl.base
  | .filt _ _ => true

/-- A decidable check that the program and its sinks never mention the static base. -/
def FreshB (X : SCtx) : Bool :=
  X.P.edges.all (fun x => instrOffB X.sB x.2.2.1) && X.sinks.all (fun x => offB X.sB x.2.2.base)

/-- The program and its sinks never mention the static base. -/
structure Fresh (X : SCtx) : Prop where
  stmt : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ X.P.edges → ∀ e, e ∈ s.edges →
    e.1.base ≠ X.sB ∧ e.2.base ≠ X.sB
  toC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.toCallee →
    e.1.base ≠ X.sB ∧ e.2.base ≠ X.sB
  fromC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.fromCallee →
    e.1.base ≠ X.sB ∧ e.2.base ≠ X.sB
  clean : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ X.P.edges → cl.base ≠ X.sB
  sink : ∀ M n s, (M, n, s) ∈ X.sinks → s.base ≠ X.sB

theorem fresh_of {X : SCtx} (h : FreshB X = true) : Fresh X := by
  unfold FreshB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hp, hs⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M n s n' hE e he
    have h1 : instrOffB X.sB (Instr.stmt s) = true := List.all_eq_true.mp hp _ hE
    exact edgeOff (List.all_eq_true.mp h1 e he)
  · intro M n c n' hE e he
    have h1 : instrOffB X.sB (Instr.call c) = true := List.all_eq_true.mp hp _ hE
    have h2 : (c.toCallee.all (edgeOffB X.sB) && c.fromCallee.all (edgeOffB X.sB)) = true := h1
    rw [Bool.and_eq_true] at h2
    exact edgeOff (List.all_eq_true.mp h2.1 e he)
  · intro M n c n' hE e he
    have h1 : instrOffB X.sB (Instr.call c) = true := List.all_eq_true.mp hp _ hE
    have h2 : (c.toCallee.all (edgeOffB X.sB) && c.fromCallee.all (edgeOffB X.sB)) = true := h1
    rw [Bool.and_eq_true] at h2
    exact edgeOff (List.all_eq_true.mp h2.2 e he)
  · intro M n cl n' hE
    have h1 : instrOffB X.sB (Instr.clean cl) = true := List.all_eq_true.mp hp _ hE
    exact offB_ne h1
  · intro M n s hs'
    exact offB_ne (List.all_eq_true.mp hs _ hs')

/-- A program that never mentions the static base satisfies the construction hypotheses. -/
theorem swf_of_fresh {X : SCtx} (hz : X.sB ≠ zeroBase) (hα : X.α = policy (fun _ => []))
    (hf : Fresh X) : SWF X where
  base := hz
  ss := by
    intro M n s n' hE e he h1 _
    exact absurd h1 (hf.stmt _ _ _ _ hE e he).1
  write := by
    intro M n s n' hE e he _ h2 _
    exact absurd h2 (hf.stmt _ _ _ _ hE e he).2
  toC := by
    intro M n c n' hE e he hb
    rcases hb with h | h
    · exact absurd h (hf.toC _ _ _ _ hE e he).1
    · exact absurd h (hf.toC _ _ _ _ hE e he).2
  fromC := by
    intro M n c n' hE e he hb
    rcases hb with h | h
    · exact absurd h (hf.fromC _ _ _ _ hE e he).1
    · exact absurd h (hf.fromC _ _ _ _ hE e he).2
  cut := by
    intro q r _ hab
    obtain ⟨_, _, hP, _, _⟩ := hab
    rcases hP with ⟨M, n, s, n', e, hE, he, hb, _⟩ | ⟨M, n, s, hs, hb, _⟩
    · exact (hf.stmt _ _ _ _ hE e he).1 hb
    · exact hf.sink _ _ _ hs hb
  clean := by
    intro M n cl n' hE hb
    exact absurd hb (hf.clean _ _ _ _ hE)
  alpha := hα

#print axioms swf_of_fresh

theorem noStaticInit_of_fresh {X : SCtx} (hz : X.sB ≠ zeroBase)
    (hα : X.α = policy (fun _ => [])) (hf : Fresh X) : NoStaticInit X :=
  noStaticInit_of hz hα (fun _ _ _ _ hE e he => (hf.toC _ _ _ _ hE e he).2)

#print axioms noStaticInit_of_fresh

/-- In a program without calls, run 1 does not depend on the abstraction `α` (it is used only for
    added facts, which need a call). -/
def AlphaMot (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Obj → Prop
  | .added _ _ => False
  | o => D P counted L α sinks roots o

theorem D_alpha {P : Program} {counted : Acc → Bool} {L : Nat} {α1 α2 : MethodId → PFact → PFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hnc : ∀ M n c n', (M, n, Instr.call c, n') ∉ P.edges) {o : Obj}
    (h : D P counted L α1 sinks roots o) : AlphaMot P counted L α2 sinks roots o := by
  induction h with
  | root hM => exact D.root hM
  | start _ ih => exact D.start ih
  | step _ hE hf ih => exact D.step ih hE hf
  | reqStmt _ hE hq ih => exact D.reqStmt ih hE hq
  | pass _ hE _ _ => exact absurd hE (hnc _ _ _ _)
  | added _ hE _ _ _ => exact absurd hE (hnc _ _ _ _)
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact absurd hE (hnc _ _ _ _)
  | reqSink _ hs hc ih => exact D.reqSink ih hs hc
  | answer _ _ _ _ _ iha => exact iha.elim
  | reqUp _ _ hE _ _ _ _ _ _ _ => exact absurd hE (hnc _ _ _ _)
  | vuln _ hs hc ih => exact D.vuln ih hs hc
  | clean _ hE hf ih => exact D.clean ih hE hf
  | reqClean _ hE hq ih => exact D.reqClean ih hE hq
  | filt _ hE hp ih => exact D.filt ih hE hp

#print axioms D_alpha

theorem confirmed_alpha {P : Program} {counted : Acc → Bool} {L : Nat}
    {α1 α2 : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hnc : ∀ M n c n', (M, n, Instr.call c, n') ∉ P.edges)
    {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed.Confirmed P counted L α1 sinks roots M n s) :
    Confirmed.Confirmed P counted L α2 sinks roots M n s := by
  obtain ⟨i, f, hD, hS, hc, hs, hch⟩ := h
  have hD' : D P counted L α2 sinks roots (.edge M i n f) := D_alpha hnc hD
  refine ⟨i, f, hD', ?_, hc, hs, hch⟩
  cases hS with
  | root hM => exact Confirmed.Sup.root hM
  | call _ _ _ hE => exact absurd hE (hnc _ _ _ _)

#print axioms confirmed_alpha

namespace CexS

/-- The filter counterexample under the final rule (static base `99`, unused). -/
def XF : SCtx := ⟨Confirmed.CexConfFilt.P, fun _ => true, 3, policy (fun _ => []), Confirmed.CexConfFilt.sinks, [0],
  99, true, true, .off, true, true⟩

theorem xf_fresh : Fresh XF := fresh_of (by decide)
theorem xf_swf : SWF XF := swf_of_fresh (by decide) rfl xf_fresh
theorem xf_design : Design XF := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem xf_nocall : ∀ M n c n', (M, n, Instr.call c, n') ∉ Confirmed.CexConfFilt.P.edges := by
  intro M n c n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- WITHOUT `FiltUp` THE CONFIRMATION THEOREM OF `DS` IS FALSE, even under `SWF` and the final rule
    (`Design`), for a well-formed program with `MarkWF`. -/
theorem cexS_filt :
    SWF XF ∧ Design XF ∧ XF.P.WF ∧ Exact.MarkWF XF.P ∧ ¬ Exact.FiltUp XF.P ∧
    ConfirmedS XF 0 3 Confirmed.CexConfFilt.sinkPat ∧
    ¬ ∃ l, Reach XF.P XF.roots 0 3 l ∧ Confirmed.CexConfFilt.sinkPat.covers l := by
  obtain ⟨hwf, hmw, hnf, hconf, hnr⟩ := Confirmed.CexConfFilt.cex_conf_filt
  have hc : Confirmed.Confirmed XF.P XF.counted XF.FL XF.α XF.sinks XF.roots 0 3
      Confirmed.CexConfFilt.sinkPat := confirmed_alpha xf_nocall hconf
  exact ⟨xf_swf, xf_design, hwf, hmw, hnf,
    (confirmedS_iff (noStaticInit_of_fresh (by decide) rfl xf_fresh)).mpr hc, hnr⟩

#print axioms cexS_filt

/-- The mark counterexample under the final rule (static base `99`, unused). -/
def XM : SCtx := ⟨Confirmed.CexConfMark.P, fun _ => true, 3, Confirmed.CexConfMark.α, Confirmed.CexConfMark.sinks, [1],
  99, true, true, .off, true, true⟩

theorem xm_fresh : Fresh XM := fresh_of (by decide)
theorem xm_swf : SWF XM := swf_of_fresh (by decide) rfl xm_fresh
theorem xm_design : Design XM := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- WITHOUT `MarkWF` THE CONFIRMATION THEOREM OF `DS` IS FALSE, even under `SWF` and the final rule
    (`Design`), for a well-formed program with `FiltUp`. -/
theorem cexS_mark :
    SWF XM ∧ Design XM ∧ XM.P.WF ∧ Exact.FiltUp XM.P ∧ ¬ Exact.MarkWF XM.P ∧
    ConfirmedS XM 1 2 Confirmed.CexConfMark.sinkPat ∧
    ¬ ∃ l, Reach XM.P XM.roots 1 2 l ∧ Confirmed.CexConfMark.sinkPat.covers l := by
  obtain ⟨hwf, hfu, hnm, hconf, hnr⟩ := Confirmed.CexConfMark.cex_conf_mark
  exact ⟨xm_swf, xm_design, hwf, hfu, hnm,
    (confirmedS_iff (noStaticInit_of_fresh (by decide) rfl xm_fresh)).mpr hconf, hnr⟩

#print axioms cexS_mark

end CexS

end ApSpec.StaticsConfirmed
