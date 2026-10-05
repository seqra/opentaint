/-
  ApSpec.NDExact — the PRECISION side of the ND extension (spec §4.6): a normal-layer ND edge
  is EXACT against the support semantics `TaintN`. This is the converse of `ND.nd_coverage`
  for the normal layer, in the form of `Exact.edge_exact`.

  Contents:
    * `PremCov`: the premise list covers the support, position by position.
    * List and support helpers: `al_splitL`, `supAll_append`, `premCov_nonempty`.
    * Fact helpers: every fact covers a location (`covers_nonempty`, no hypothesis: an
      exclusion `univ` still admits the empty continuation, and `*∖x` admits a fresh mark);
      an uncorrelated conclusion (concrete mark, no `*` tail) relates every covered support
      location to every covered end location (`den_uncorr`, `nrel_uncorr`); a normal-layer
      conclusion with a concrete mark has no `*` tail (`startFact_nonstar`,
      `applyEdge_nonstar_n`, `transfer_nonstar_n`, `cleanRes_nonstar_n`).
    * The two new hypotheses: `LitConc` (the literals of a conjunction have concrete marks)
      and `ConjOK` (validity goes back from a conjunction target to its literals, the
      `BackOK` link of a conjunction).
    * The motive `NEdgeOK` and `nd_edgeOK`: THE ND EXACTNESS INVARIANT, by induction on `DN`.
    * `nd_edge_exact_gen` (generic validity), `nd_edge_exact` (THE ND EXACTNESS THEOREM),
      `nd_edge_exact_valid`, `nd_edge_exact_single`, `nd_edge_exact_nd`.
    * `CexLit.cex_lit`: without `LitConc` the statement is FALSE (an abstract literal).
    * `CexConjOK.cex_conjOK`: without `ConjOK` the valid form is FALSE.

  Design check (the point of this file):
    * The conjunction is exact in the normal layer: `conjLayer` keeps the result normal only if
      both inputs are normal and cover their literals, and `TaintN.conj` is path-insensitive in
      the same way as the engine.
    * The statement is "for EVERY support that the premises cover". An input of a
      conjunction or of an ND binding with ONE premise must then relate every location of its
      premise to some location (its pair relation must be TOTAL on the premise). A correlated
      input (`*` tail with an exclusion, or the mark `*∖x`) is not total: the excluded
      locations reach nothing. With an abstract literal such an input passes the gate and the
      cover test, and the claim fails (`CexLit`). With concrete literals (`LitConc`), the gate
      forces a concrete input mark, a normal-layer concrete-mark conclusion has no `*` tail,
      so the input is uncorrelated and total. Under `MarkWF` the premises of every ND edge are
      then concrete too, so an ND summary binds only uncorrelated caller edges.
    * The empty location set is NOT a problem: every fact covers a location
      (`covers_nonempty`).
    * `ndBind` ORs the layer of every bound caller edge into the partial match, so a normal
      ND summary result has a normal callee summary and normal caller bindings; the partial
      match invariant (`NEdgeOK` of `npart`) builds the `SupAll` support block by block.

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.ND
import ApSpec.Exact

namespace ApSpec.NDExact
open ApSpec ApSpec.ND

/-! ## 1. Lists and supports -/

/-- The premises cover the support, position by position. -/
abbrev PremCov (P : List PFact) (L0 : List Loc) : Prop := Al (fun p l0 => p.covers l0) P L0

/-- Split an alignment along a split of the LEFT list. -/
theorem al_splitL {α β : Type} {R : α → β → Prop} :
    ∀ {I1 I2 : List α} {L : List β}, Al R (I1 ++ I2) L →
      ∃ L1 L2, L = L1 ++ L2 ∧ Al R I1 L1 ∧ Al R I2 L2
  | [], _, L, h => ⟨[], L, rfl, .nil, h⟩
  | _ :: _, _, _, .cons hab h => by
    obtain ⟨L1, L2, he, h1, h2⟩ := al_splitL h
    exact ⟨_ :: L1, L2, by rw [he]; rfl, .cons hab h1, h2⟩

/-- Two supports of the same call node concatenate. -/
theorem supAll_append {Q : NProg} {M : MethodId} {n : Node} {c : Call} {K2 L2 : List Loc} :
    ∀ {K1 L1 : List Loc}, SupAll Q M n c K1 L1 → SupAll Q M n c K2 L2 →
      SupAll Q M n c (K1 ++ K2) (L1 ++ L2)
  | _, _, .nil, h2 => h2
  | _, _, .cons hT he hd hS, h2 => by
    rw [List.append_assoc]
    exact .cons hT he hd (supAll_append hS h2)

#print axioms supAll_append

/-! ## 2. Every fact covers a location -/

theorem memB_of_lt : ∀ (x : List Nat) (m : Nat), x.foldr (· + ·) 0 < m → memB m x = false
  | [], _, _ => rfl
  | a :: x, m, h => by
    have h' : a + x.foldr (· + ·) 0 < m := h
    have hne : m ≠ a := by omega
    have hlt : x.foldr (· + ·) 0 < m := by omega
    have hb : Nat.beq m a = false := by
      cases hq : Nat.beq m a with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hq) hne
    show (Nat.beq m a || memB m x) = false
    rw [hb, memB_of_lt x m hlt]
    rfl

/-- A mark outside a finite list. -/
theorem fresh_mark (x : List Mark) : ∃ m, memB m x = false :=
  ⟨x.foldr (· + ·) 0 + 1, memB_of_lt x _ (Nat.lt_succ_self _)⟩

theorem markA_nonempty (m : MarkA) : ∃ t, m.admits t := by
  cases m with
  | star => exact ⟨0, trivial⟩
  | conc t => exact ⟨t, rfl⟩
  | starEx x => exact fresh_mark x

/-- Every fact covers a location: its own position, with a mark that it admits. An exclusion
    (even `univ`) admits the empty continuation. -/
theorem covers_nonempty (f : PFact) : ∃ l, f.covers l :=
  let ⟨t, ht⟩ := markA_nonempty f.mark
  ⟨⟨f.base, f.path, t⟩, rfl, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _⟩, ht⟩

#print axioms covers_nonempty

/-- Every premise list covers some support. -/
theorem premCov_nonempty : ∀ (P : List PFact), ∃ L, PremCov P L
  | [] => ⟨[], .nil⟩
  | p :: P =>
    let ⟨l, hl⟩ := covers_nonempty p
    let ⟨L, hL⟩ := premCov_nonempty P
    ⟨l :: L, .cons hl hL⟩

/-! ## 3. Uncorrelated conclusions -/

theorem absB_false_conc {m : MarkA} (h : Exact.absB m = false) : ∃ t, m = .conc t := by
  cases m with
  | conc t => exact ⟨t, rfl⟩
  | star => cases h
  | starEx _ => cases h

/-- The premise of a pair covers its start location. -/
theorem den_covers_init {i f : PFact} {l0 l : Loc} (h : den i f l0 l) : i.covers l0 :=
  let ⟨hb, _, hm, _, _, σ, _, hp, _, ht, _⟩ := h
  ⟨hb, ⟨σ, hp, ht⟩, hm⟩

/-- An UNCORRELATED conclusion (a concrete mark and no `*` tail) relates every location of
    any premise to every location of the conclusion. -/
theorem den_uncorr {i f : PFact} {l0 l : Loc} (hc : Exact.absB f.mark = false)
    (hk : f.kind.isStar = false) (h0 : i.covers l0) (h1 : f.covers l) : den i f l0 l := by
  obtain ⟨t, ht⟩ := absB_false_conc hc
  obtain ⟨fb, fp, fk, fm⟩ := f
  have ht' : fm = .conc t := ht
  subst ht'
  obtain ⟨hb0, ⟨σ, hp0, ht0⟩, hm0⟩ := h0
  obtain ⟨hb1, ⟨τ, hp1, ht1⟩, hm1⟩ := h1
  refine ⟨hb0, hb1, hm0, hm1, trivial, σ, τ, hp0, hp1, ht0, ?_⟩
  cases fk with
  | star e => cases hk
  | any => trivial
  | exact => exact ht1

#print axioms den_uncorr

/-- The relation `NRel` of an uncorrelated conclusion holds for every covered support and
    every covered end location. -/
theorem nrel_uncorr {P : List PFact} {L0 : List Loc} {f : PFact} {l : Loc}
    (hc : Exact.absB f.mark = false) (hk : ∀ i, P = [i] → f.kind.isStar = false)
    (hP : PremCov P L0) (hl : f.covers l) : NRel P L0 f l := by
  refine ⟨hl, fun i l0 hPi hLi => ?_⟩
  subst hPi hLi
  exact den_uncorr hc (hk i rfl) (Al.get hP .head) hl

/-- A concrete gate passes only the same concrete mark. -/
theorem gate_conc_ok {T : Mark} {m : MarkA} (hg : markGate (.conc T) m = .ok) : m = .conc T := by
  cases m with
  | conc t =>
    have h' : (if Nat.beq T t = true then Gate.ok else Gate.no) = Gate.ok := hg
    cases hq : Nat.beq T t with
    | true => rw [Nat.eq_of_beq_eq_true hq]
    | false => rw [hq, if_neg Bool.false_ne_true] at h'; exact Gate.noConfusion h'
  | star => exact Gate.noConfusion hg
  | starEx x =>
    have h' : (if memB T x = true then Gate.no else Gate.req T) = Gate.ok := hg
    cases hq : memB T x with
    | true => rw [hq, if_pos rfl] at h'; exact Gate.noConfusion h'
    | false => rw [hq, if_neg Bool.false_ne_true] at h'; exact Gate.noConfusion h'

/-! ## 4. A normal-layer concrete-mark conclusion has no `*` tail (W2) -/

theorem startFact_nonstar (i : PFact) (hd : (startFact i).demand = false)
    (hc : Exact.absB (startFact i).fact.mark = false) : (startFact i).fact.kind.isStar = false := by
  obtain ⟨ib, ip, ik, im⟩ := i
  cases ik with
  | star e =>
    cases im with
    | star => cases hc
    | starEx x => cases hc
    | conc t => cases hd
  | any => cases hd
  | exact => rfl

/-- A concrete-mark result of `applyEdge` has no `*` tail (it is a normal form). -/
theorem applyEdge_nonstar_n {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts)
    (hc : Exact.absB r.fact.mark = false) : r.fact.kind.isStar = false := by
  obtain ⟨p, k, ap, m, _, _, _, hre⟩ := CoreAux.mem_applyEdge_facts_inv hr
  obtain ⟨t, ht⟩ := absB_false_conc hc
  subst hre
  rw [CoreAux.norm_mark] at ht
  exact norm_conc_nonstar ht

theorem transfer_nonstar_n {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hns : c.demand = false → Exact.absB c.fact.mark = false → c.fact.kind.isStar = false)
    (hr : r ∈ (transfer counted L s c).facts) (hd : r.demand = false)
    (hc : Exact.absB r.fact.mark = false) : r.fact.kind.isStar = false := by
  rcases Exact.transfer_mem hr with ⟨-, y, hy, rfl⟩ | ⟨-, rfl⟩
  · have e := Exact.limitF_exact hd
    rw [e] at hc ⊢
    obtain ⟨me, _, hye⟩ := Exact.applyAll_mem hy
    exact applyEdge_nonstar_n hye hc
  · exact hns hd hc

theorem cleanRes_nonstar_n {cl : Cleaner} {c r : AFact}
    (hns : c.demand = false → Exact.absB c.fact.mark = false → c.fact.kind.isStar = false)
    (hr : r ∈ (cleanRes cl c).facts) (hd : r.demand = false)
    (hc : Exact.absB r.fact.mark = false) : r.fact.kind.isStar = false := by
  rcases Exact.cleanRes_mem hr with ⟨rfl, -⟩ | ⟨t, hab, -, rfl⟩ | ⟨t, -, -, rfl⟩ | rfl
  · exact hns hd hc
  · have h1 : Exact.absB (addEx c.fact.mark t) = true := Exact.addEx_abs t hab
    have h2 : Exact.absB (addEx c.fact.mark t) = false := hc
    rw [h1] at h2
    cases h2
  · rcases Exact.concPart_cases cl c with ⟨-, -, -, he⟩ | he
    · rw [he]; rfl
    · rw [he] at hd; cases hd
  · rw [Exact.norm_true_demand] at hd
    cases hd

/-! ## 5. THE ND EXACTNESS THEOREM -/

/-- The literals of every conjunction have concrete marks (the intended literals are exact
    positions with concrete marks, `ND.Conj`). Necessary: `CexLit.cex_lit`. -/
def LitConc (Q : NProg) : Prop :=
  ∀ M n cj n', (M, n, cj, n') ∈ Q.conjs →
    (∃ T, cj.lit1.mark = .conc T) ∧ ∃ T, cj.lit2.mark = .conc T

/-- The `BackOK` link of a conjunction: if a location of its target is valid, every location
    of its literals is valid. With `ok := fun _ => True` it holds (`conjOK_true`). Necessary for
    the valid form: `CexConjOK.cex_conjOK`. -/
def ConjOK (Q : NProg) (ok : Loc → Prop) : Prop :=
  ∀ M n cj n', (M, n, cj, n') ∈ Q.conjs → ∀ l1 l', cj.target.covers l' → ok l' →
    (cj.lit1.covers l1 → ok l1) ∧ (cj.lit2.covers l1 → ok l1)

theorem conjOK_true (Q : NProg) : ConjOK Q (fun _ => True) :=
  fun _ _ _ _ _ _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩

/-- The exactness of an edge with the premise list `P`: for EVERY support that the premises
    cover and every end location in the relation `NRel` (the conclusion covers it; for one
    premise, the pair), the location is tainted with exactly that support. For valid end
    locations; the support is then valid too. -/
abbrev NExact (Q : NProg) (ok : Loc → Prop) (M : MethodId) (P : List PFact) (n : Node)
    (f : AFact) : Prop :=
  ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → ok l → TaintN Q M n l L0 ∧ ∀ l0, l0 ∈ L0 → ok l0

/-- The motive.
    For an edge: the premise list is not empty; an abstract premise gives an abstract
    conclusion (the invariant of `Exact.EdgeOK`, for every premise of the list); the premises of
    an ND edge are concrete; a normal-layer concrete-mark conclusion of one premise has no `*`
    tail (W2); a normal-layer edge is exact (`NExact`).
    For a partial match: the call edge exists; the remaining callee premises and the matched
    caller premises are concrete; the final list will have two or more premises; if the
    partial match is in the normal layer, then for each valid end location `l2` of the callee
    conclusion and each support `L0` of the matched caller premises, there are callee entry
    locations `Km` bound from caller locations tainted with `L0` (`SupAll`), such that each
    choice `Kr` of locations of the remaining premises completes a callee derivation of `l2`
    with the support `Km ++ Kr`, and the locations of `Kr` are valid. -/
def NEdgeOK (Q : NProg) (ok : Loc → Prop) : NObj → Prop
  | .nedge M P n f =>
      P ≠ [] ∧
      (∀ p, p ∈ P → Exact.absB p.mark = true → Exact.absB f.fact.mark = true) ∧
      (2 ≤ P.length → ∀ p, p ∈ P → Exact.absB p.mark = false) ∧
      (∀ i, P = [i] → f.demand = false → Exact.absB f.fact.mark = false →
        f.fact.kind.isStar = false) ∧
      (f.demand = false → NExact Q ok M P n f)
  | .npart M n c n' rest P g =>
      (M, n, Instr.call c, n') ∈ Q.prog.edges ∧
      (∀ p, p ∈ rest → Exact.absB p.mark = false) ∧
      (∀ p, p ∈ P → Exact.absB p.mark = false) ∧
      2 ≤ P.length + rest.length ∧
      (g.demand = false → ∀ l2, g.fact.covers l2 → ok l2 → ∀ L0, PremCov P L0 →
        ∃ Km, SupAll Q M n c Km L0 ∧ (∀ l0, l0 ∈ L0 → ok l0) ∧
          ∀ Kr, PremCov rest Kr →
            TaintN Q c.callee (Q.prog.exit c.callee) l2 (Km ++ Kr) ∧ ∀ k, k ∈ Kr → ok k)
  | _ => True

/-- THE ND EXACTNESS INVARIANT. Generic validity `ok` (as `Exact.D_edgeOK`): `MarkWF`, the
    filter condition `FiltOK`, the backward closure `BackOK`, and the two conjunction
    conditions `LitConc` and `ConjOK`. -/
theorem nd_edgeOK {X : Ctx} {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog)
    (hfo : Exact.FiltOK X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {o : NObj} (h : DN X o) : NEdgeOK X.Q ok o := by
  induction h with
  | root _ => trivial
  | @start M i _ _ =>
    refine ⟨List.cons_ne_nil _ _, fun p hp hab => ?_, fun h2 => absurd h2 (Nat.not_succ_le_self 1),
      fun _ _ hd hc => startFact_nonstar i hd hc, ?_⟩
    · rw [List.mem_singleton.mp hp] at hab
      rw [startFact_mark]
      exact hab
    · intro ha L0 l hP hrel hok
      obtain ⟨l0, rfl, _⟩ := Al.single hP
      have hd := hrel.2 i l0 rfl rfl
      have e := Exact.startFact_exact ha hd
      subst e
      exact ⟨TaintN.start M l, fun l0' hl0' => by rw [List.mem_singleton.mp hl0']; exact hok⟩
  | @step M P n f n' s f' _ hE hf ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, fun p hp hab => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (habs p hp hab) hf,
      hcon, fun i hP hd hc => transfer_nonstar_n (fun h1 h2 => hns i hP h1 h2) hf hd hc, ?_⟩
    intro ha L0 l hP hrel hok
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hT, hok0⟩ := hex hfa L0 l1 hP (rel_of_wit hd1 hsw) hok1
    exact ⟨TaintN.step hT hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M P n f n' c _ hE hm ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, habs, hcon, hns, ?_⟩
    intro ha L0 l hP hrel hok
    obtain ⟨hT, hok0⟩ := hex ha L0 l hP hrel hok
    refine ⟨TaintN.pass hT hE ?_, hok0⟩
    rw [hrel.1.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M P n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    obtain ⟨hne, habs, hcon, _, hex⟩ := ihD
    obtain ⟨_, habsG, _, _, hexG⟩ := ihG
    refine ⟨hne, fun p hp hab => ?_, hcon, fun i _ hd hc => ?_, ?_⟩
    · -- the mark invariant
      have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (habs p hp hab) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := habsG j List.mem_cons_self (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · -- W2
      have e := Exact.limitF_exact hd
      rw [e] at hc ⊢
      exact applyEdge_nonstar_n hr' hc
    · intro hla L0 l hP hrel hok
      have e := Exact.limitF_exact hla
      rw [e] at hrel hla
      have hra := Exact.applyEdge_demand hr' hla
      obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      -- the binding back to the caller
      obtain ⟨hp3, hc3⟩ :=
        Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      -- the summary edge
      obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
      have haa := Exact.applyEdge_demand hx hxa
      have hfa := Exact.applyEdge_demand ha haa
      have hp2 : Exact.premOKB j.mark a.fact.mark = true :=
        Exact.premOK_of_sub (Exact.applicable_markSub happ)
      have hc2 : Exact.concOKB g.fact.mark a.fact.mark = true :=
        Exact.concOK_of (fun hA => habsG j List.mem_cons_self
          (Exact.gate_abs (Exact.applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hTG, hok1'⟩ := hexG hga [l1'] l2 (.cons (den_covers_init hdg) .nil)
        ⟨den_covers_final hdg, fun i0 k0 hI hK => by
          rw [← (List.cons.inj hI).1, ← (List.cons.inj hK).1]
          exact hdg⟩ hok2
      -- the binding into the callee
      obtain ⟨hp1, hc1⟩ :=
        Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 (hok1' l1' List.mem_cons_self)
      obtain ⟨hTD, hok0⟩ := hex hfa L0 l1 hP (rel_of_wit hd1 hsw) hok1
      have hS : SupAll X.Q M n c [l1'] (L0 ++ []) := .cons hTD he1 hde1 .nil
      rw [List.append_nil] at hS
      exact ⟨TaintN.call hE hTG hS he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @ndOpen M n c n' Pc g hE _ h2 ih =>
    obtain ⟨_, _, hcon, _, hex⟩ := ih
    refine ⟨hE, hcon h2, fun p hp => absurd hp List.not_mem_nil,
      by rw [List.length_nil, Nat.zero_add]; exact h2, ?_⟩
    intro hg l2 hc2 hok2 L0 hP
    cases hP
    refine ⟨[], SupAll.nil, fun _ h => absurd h List.not_mem_nil, fun Kr hKr => ?_⟩
    have hrel : NRel Pc Kr g.fact l2 := ⟨hc2, fun i _ hPi _ => by
      rw [hPi] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)⟩
    exact hex hg Kr l2 hKr hrel hok2
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ he1 ha happ ihp ihf =>
    obtain ⟨hE, hrest, hPc, hlen, hexp⟩ := ihp
    obtain ⟨hneF, habsF, _, hnsF, hexF⟩ := ihf
    -- the callee premise is concrete, so the added fact and the caller edge are concrete
    obtain ⟨t, hpt⟩ := absB_false_conc (hrest p List.mem_cons_self)
    have hat : a.fact.mark = .conc t := applicable_mark happ hpt
    have haA : Exact.absB a.fact.mark = false := by rw [hat]; rfl
    have hfA : Exact.absB f.fact.mark = false := by
      cases hb : Exact.absB f.fact.mark with
      | false => rfl
      | true =>
        have h1 := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) hb ha
        rw [haA] at h1
        cases h1
    refine ⟨hE, fun q hq => hrest q (List.mem_cons_of_mem _ hq), fun q hq => ?_, ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hPc q hq
      · cases hb : Exact.absB q.mark with
        | false => rfl
        | true =>
          have h1 := habsF q hq hb
          rw [hfA] at h1
          cases h1
    · have h1 : 0 < Pf.length := List.length_pos_iff.mpr hneF
      have h2 : (p :: ps).length = ps.length + 1 := rfl
      rw [List.length_append]
      omega
    · intro hgd l2 hc2 hok2 L hL
      have hgd' : (g.demand || a.demand) = false := hgd
      obtain ⟨hgd1, had⟩ := Exact.or_eq_false hgd'
      obtain ⟨L0, Lf, rfl, hL0, hLf⟩ := al_splitL hL
      obtain ⟨Km, hS, hokL0, hrestT⟩ := hexp hgd1 l2 hc2 hok2 L0 hL0
      have hfd : f.demand = false := Exact.applyEdge_demand ha had
      -- a callee entry location of the added fact; the callee premise covers it
      obtain ⟨k, hak⟩ := covers_nonempty a.fact
      have hpk : p.covers k := applicable_sound happ hak
      obtain ⟨Kr0, hKr0⟩ := premCov_nonempty ps
      have hokk : ok k := (hrestT (k :: Kr0) (.cons hpk hKr0)).2 k List.mem_cons_self
      -- the caller location bound to it
      obtain ⟨hp1, hc1⟩ :=
        Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨lk, hdk, hde⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had (den_refl hak)
      have hoklk : ok lk := hbo.toC _ _ _ _ hE e1 he1 _ _ hde hokk
      have hrel : NRel Pf Lf f.fact lk :=
        nrel_uncorr hfA (fun i hPi => hnsF i hPi hfd hfA) hLf (den_covers_final hdk)
      obtain ⟨hTf, hokLf⟩ := hexF hfd Lf lk hLf hrel hoklk
      have hS1 : SupAll X.Q M n c [k] (Lf ++ []) := .cons hTf he1 hde .nil
      rw [List.append_nil] at hS1
      refine ⟨Km ++ [k], supAll_append hS hS1, fun l0 hl0 => ?_, fun Kr hKr => ?_⟩
      · rcases List.mem_append.mp hl0 with h | h
        · exact hokL0 l0 h
        · exact hokLf l0 h
      · obtain ⟨hT, hokK⟩ := hrestT (k :: Kr) (.cons hpk hKr)
        refine ⟨?_, fun k' hk' => hokK k' (List.mem_cons_of_mem _ hk')⟩
        rw [List.append_assoc]
        exact hT
  | @ndRet M n c n' P g e2 r _ he2 hr ih =>
    obtain ⟨hE, _, hPc, hlen, hexp⟩ := ih
    have h2 : 2 ≤ P.length := hlen
    refine ⟨fun he => ?_, fun p hp hab => ?_, fun _ => hPc, fun i hP _ _ => ?_, ?_⟩
    · rw [he] at h2
      exact absurd h2 (by decide)
    · rw [hPc p hp] at hab
      cases hab
    · rw [hP] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)
    · intro hd L0 l hP hrel hok
      have e := Exact.limitF_exact hd
      rw [e] at hd hrel
      have hgd := Exact.applyEdge_demand hr hd
      obtain ⟨hp3, hc3⟩ :=
        Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr).1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hgd hr hd (den_refl hrel.1)
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      obtain ⟨Km, hS, hokL0, hrestT⟩ := hexp hgd l2 (den_covers_final hd2) hok2 L0 hP
      obtain ⟨hT, _⟩ := hrestT [] .nil
      rw [List.append_nil] at hT
      exact ⟨TaintN.call hE hT hS he2 hde2, hokL0⟩
  | @clean M P n f n' cl f' _ hE hf ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, fun p hp hab => Exact.cleanRes_abs (habs p hp hab) hf, hcon,
      fun i hP hd hc => cleanRes_nonstar_n (fun h1 h2 => hns i hP h1 h2) hf hd hc, ?_⟩
    intro ha L0 l hP hrel hok
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hT, hok0⟩ := hex hfa L0 l hP (rel_of_wit hd1 hsw) hok
    exact ⟨TaintN.clean hT hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M P n f n' b may _ hE hp ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, habs, hcon, hns, ?_⟩
    intro ha L0 l hP hrel hok
    obtain ⟨hT, hok0⟩ := hex ha L0 l hP hrel hok
    refine ⟨TaintN.filt hT hE ?_, hok0⟩
    intro hb
    obtain ⟨hlb, ⟨σ, hlp, _⟩, _⟩ := hrel.1
    exact hfo _ _ _ _ _ hE f.fact.path σ l (hp (hlb.symm.trans hb)) hlp hok hb
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj _ hg1 _ hg2 ih1 ih2 =>
    obtain ⟨hne1, habs1, _, hns1, hex1⟩ := ih1
    obtain ⟨hne2, habs2, _, hns2, hex2⟩ := ih2
    obtain ⟨⟨T1, hT1⟩, ⟨T2, hT2⟩⟩ := hlc _ _ _ _ hcj
    -- a concrete literal passes only a concrete input
    rw [hT1] at hg1
    rw [hT2] at hg2
    have hf1A : Exact.absB f1.fact.mark = false := by rw [gate_conc_ok hg1]; rfl
    have hf2A : Exact.absB f2.fact.mark = false := by rw [gate_conc_ok hg2]; rfl
    -- so every premise is concrete
    have hall : ∀ p, p ∈ P1 ++ P2 → Exact.absB p.mark = false := by
      intro p hp
      cases hb : Exact.absB p.mark with
      | false => rfl
      | true =>
        exfalso
        rcases List.mem_append.mp hp with hp | hp
        · have h1 := habs1 p hp hb
          rw [hf1A] at h1
          cases h1
        · have h1 := habs2 p hp hb
          rw [hf2A] at h1
          cases h1
    refine ⟨fun he => hne1 (List.append_eq_nil_iff.mp he).1, fun p hp hab => ?_,
      fun _ => hall, fun i hP => absurd hP (app_ne_single hne1 hne2), ?_⟩
    · rw [hall p hp] at hab
      cases hab
    · intro hd L l' hP hrel hok
      have hd' : (f1.demand || f2.demand || !coversB cj.lit1 f1.fact ||
          !coversB cj.lit2 f2.fact) = false := hd
      obtain ⟨hd'', hcv2⟩ := Exact.or_eq_false hd'
      obtain ⟨hd''', hcv1⟩ := Exact.or_eq_false hd''
      obtain ⟨hd1, hd2⟩ := Exact.or_eq_false hd'''
      have hcv1' := Exact.not_eq_false_true hcv1
      have hcv2' := Exact.not_eq_false_true hcv2
      obtain ⟨L1, L2, rfl, hL1, hL2⟩ := al_splitL hP
      have hct : cj.target.covers l' := hrel.1
      -- a location of each literal, related to the support of its input
      obtain ⟨l1, hl1⟩ := covers_nonempty f1.fact
      obtain ⟨l2, hl2⟩ := covers_nonempty f2.fact
      have hc1 : cj.lit1.covers l1 := coversB_sound hcv1' hl1
      have hc2 : cj.lit2.covers l2 := coversB_sound hcv2' hl2
      have hok1 : ok l1 := (hco _ _ _ _ hcj l1 l' hct hok).1 hc1
      have hok2 : ok l2 := (hco _ _ _ _ hcj l2 l' hct hok).2 hc2
      obtain ⟨hTa, hokA⟩ := hex1 hd1 L1 l1 hL1
        (nrel_uncorr hf1A (fun i hPi => hns1 i hPi hd1 hf1A) hL1 hl1) hok1
      obtain ⟨hTb, hokB⟩ := hex2 hd2 L2 l2 hL2
        (nrel_uncorr hf2A (fun i hPi => hns2 i hPi hd2 hf2A) hL2 hl2) hok2
      refine ⟨TaintN.conj hTa hTb hcj hc1 hc2 hct, fun l0 hl0 => ?_⟩
      rcases List.mem_append.mp hl0 with h | h
      · exact hokA l0 h
      · exact hokB l0 h
  | reqConj => trivial

#print axioms nd_edgeOK

/-- The exactness of one normal-layer edge, for a generic validity `ok` (the form of
    `Exact.D_edgeOK`). -/
theorem nd_edge_exact_gen {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    (h : DN X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → ok l →
      TaintN X.Q M n l L0 ∧ ∀ l0, l0 ∈ L0 → ok l0 :=
  (nd_edgeOK hmw hfo hbo hlc hco h).2.2.2.2 ha

#print axioms nd_edge_exact_gen

/-- THE ND EXACTNESS THEOREM. A normal-layer edge of `DN` (any number of premises) denotes only
    taintings of `TaintN`: for every support that its premises cover, every end location in the
    relation `NRel` is tainted with exactly that support. The hypotheses: `MarkWF` and `FiltUp`
    (as `Exact.edge_exact`), and `LitConc` (without it the theorem is false: `CexLit`). -/
theorem nd_edge_exact {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    (h : DN X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → TaintN X.Q M n l L0 := fun L0 l hP hrel =>
  (nd_edge_exact_gen (ok := fun _ => True) hmw (Exact.filtUp_ok hup) (Exact.backOK_true _) hlc
    (conjOK_true _) h ha L0 l hP hrel trivial).1

#print axioms nd_edge_exact

/-- THE ND EXACTNESS THEOREM FOR VALID LOCATIONS (as `Exact.edge_exact_valid`): prefix-closed
    type filters, validity closed backwards along the micro edges (`BackOK`) and from a
    conjunction target to its literals (`ConjOK`; without it the theorem is false:
    `CexConjOK`). The support of a valid end location is valid too. -/
theorem nd_edge_exact_valid {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    (h : DN X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → ok l →
      TaintN X.Q M n l L0 ∧ ∀ l0, l0 ∈ L0 → ok l0 :=
  nd_edge_exact_gen hmw (Exact.filtValid_ok hv) hbo hlc hco h ha

#print axioms nd_edge_exact_valid

/-- One premise: the form of `Exact.edge_exact`, with `TaintN` and the support `[l0]`. -/
theorem nd_edge_exact_single {X : Ctx} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {l0 l : Loc} (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    (h : DN X (.nedge M [i] n f)) (ha : f.demand = false) (hd : den i f.fact l0 l) :
    TaintN X.Q M n l [l0] :=
  nd_edge_exact hmw hup hlc h ha [l0] l (.cons (den_covers_init hd) .nil)
    ⟨den_covers_final hd, fun i' l0' hI hL => by
      rw [← (List.cons.inj hI).1, ← (List.cons.inj hL).1]
      exact hd⟩

#print axioms nd_edge_exact_single

/-- Two or more premises (an ND conclusion): EVERY covered support and EVERY location of the
    conclusion give a tainting. The ND conclusion is uncorrelated (W7), so `NRel` is the cover. -/
theorem nd_edge_exact_nd {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    {L0 : List Loc} {l : Loc}
    (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    (h : DN X (.nedge M P n f)) (ha : f.demand = false) (h2 : 2 ≤ P.length)
    (hP : PremCov P L0) (hl : f.fact.covers l) : TaintN X.Q M n l L0 :=
  nd_edge_exact hmw hup hlc h ha L0 l hP ⟨hl, fun i _ hI _ => by
    rw [hI] at h2
    exact absurd h2 (Nat.not_succ_le_self 1)⟩

#print axioms nd_edge_exact_nd

/-! ## 6. Without `LitConc` the theorem is FALSE

  The method `1` (a root) calls the method `0`; the run-1 policy gives the abstract initial fact
  `ic = (1,.,*,{},*)` to the method `0`. The method `0` cleans the mark `5` on the base `1`, which
  gives the correlated fact `c1 = (1,.,*,{},*∖{5})` (exact). A conjunction with the ABSTRACT
  literal `(1,.,[any],{},*)` on both sides passes the gate and the cover test, so its target
  `(2,.,$,{},9)` is in the normal layer with the premises `[ic, ic]`. The support
  `[1 with 5, 1 with 5]` is covered by the premises, but the cleaner removed the location
  `1 with 5`: no derivation of `TaintN` has it in its support after the cleaner. The program is
  well formed (`NProg.WF`), satisfies `MarkWF` and `FiltUp`, and `ConjOK` holds for
  `ok := fun _ => True`; only `LitConc` fails. -/

namespace CexLit

/-- The binding of the zero base of the method `1` to the base `1` of the method `0`. -/
def bnd : MicroEdge := (⟨0, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def cc : Call := ⟨0, [0], [bnd], []⟩
/-- The cleaner of the mark `5` on the base `1` and everything below it. -/
def cl : Cleaner := ⟨1, [], .atAndBelow, some 5⟩
/-- An ABSTRACT literal: every location of the base `1`. -/
def lit : PFact := ⟨1, [], .any, .star⟩
def tgt : PFact := ⟨2, [], .exact, .conc 9⟩
def cj : Conj := ⟨lit, lit, tgt⟩
def prog : Program := ⟨fun _ => 0, fun _ => 2, [(1, 0, .call cc, 1), (0, 0, .clean cl, 1)]⟩
def Q : NProg := ⟨prog, [(0, 1, cj, 2)]⟩
/-- The run-1 abstraction policy (the empty demand). -/
def X : Ctx := ⟨Q, fun _ => true, 3, policy (fun _ => []), [], [1]⟩
def ic : PFact := ⟨1, [], .star (.set []), .star⟩
def c1 : AFact := ⟨⟨1, [], .star (.set []), .starEx [5]⟩, false⟩
/-- The location `1` with the mark `5`: the cleaner removes it. -/
def l0 : Loc := ⟨1, [], 5⟩
def lEnd : Loc := ⟨2, [], 9⟩

theorem wf : Q.WF where
  prog := {
    stmtTouched := by
      intro M n s n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
    toStar := by
      intro M n c n' hE e he
      cases hE with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
    fromStar := by
      intro M n c n' hE e he
      cases hE with
      | head => cases he
      | tail _ h =>
        cases h with
        | tail _ h => cases h
    filtPrefix := by
      intro M n b may n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h => cases h }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem markWF : Exact.MarkWF Q.prog where
  stmt := by
    intro M n s n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  toC := by
    intro M n c n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | head => cases he
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem filtUp : Exact.FiltUp Q.prog := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h => cases h

theorem not_litConc : ¬ LitConc Q := by
  intro h
  obtain ⟨⟨T, hT⟩, _⟩ := h 0 1 cj 2 List.mem_cons_self
  cases hT

theorem d_edge : DN X (.nedge 0 [ic, ic] 2 (conjFact cj c1 c1)) := by
  have h0 : DN X (.ninit 1 zeroFact) := DN.root List.mem_cons_self
  have h1 := DN.start h0
  have h2 : DN X (.nadded 0 ⟨1, [], .exact, .conc 0⟩) :=
    DN.added (a := ⟨⟨1, [], .exact, .conc 0⟩, false⟩) h1 List.mem_cons_self List.mem_cons_self
      (by decide)
  have h3 := DN.initA h2
  have e : X.α 0 ⟨1, [], .exact, .conc 0⟩ = ic := by decide
  rw [e] at h3
  have h4 := DN.start h3
  have h5 : DN X (.nedge 0 [ic] 1 c1) :=
    DN.clean h4 (List.Mem.tail _ List.mem_cons_self) (by decide)
  exact DN.conj h5 h5 List.mem_cons_self (by decide) rfl (by decide) rfl

theorem normal : (conjFact cj c1 c1).demand = false := by decide

theorem ic_covers : ic.covers l0 := ⟨rfl, ⟨[], rfl, rfl⟩, trivial⟩

/-- In the method `0`, a support location of a derivation after the cleaner is not cleaned. -/
theorem taint_inv : ∀ {M n l L}, TaintN Q M n l L → M = 0 →
    (n = 0 → L = [l]) ∧ (n ≠ 0 → ∀ k, k ∈ L → cl.cleansB k = false)
  | _, _, _, _, .start _ l => fun _ => ⟨fun _ => rfl, fun hn => absurd rfl hn⟩
  | _, _, _, _, .step _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | _, _, _, _, .pass _ hE _ => by
    cases hE with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | _, _, _, _, .clean h hE hc => by
    cases hE with
    | tail _ h' =>
      cases h' with
      | head =>
        intro _
        have hL := (taint_inv h rfl).1 rfl
        subst hL
        refine ⟨fun h1 => absurd h1 (by decide), fun _ k hk => ?_⟩
        rw [List.mem_singleton.mp hk]
        exact hc
      | tail _ h'' => cases h''
  | _, _, _, _, .filt _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | _, _, _, _, .conj h1 h2 hcj _ _ _ => by
    cases hcj with
    | head =>
      intro _
      have i1 := (taint_inv h1 rfl).2 (by decide)
      have i2 := (taint_inv h2 rfl).2 (by decide)
      refine ⟨fun h => absurd h (by decide), fun _ k hk => ?_⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact i1 k hk
      · exact i2 k hk
    | tail _ h => cases h
  | _, _, _, _, .call hE _ _ _ _ => by
    cases hE with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem no_taint : ¬ TaintN X.Q 0 2 lEnd [l0, l0] := by
  intro h
  have h1 := (taint_inv h rfl).2 (by decide) l0 List.mem_cons_self
  exact absurd h1 (by decide)

/-- THE LITERAL COUNTEREXAMPLE. Every hypothesis of `nd_edge_exact` except `LitConc` holds (and
    the policy is applicable, the hypothesis of `nd_coverage`). The normal-layer ND edge
    `[ic, ic] → (2,.,$,{},9)` and a support that its premises cover give no `TaintN`. -/
theorem cex_lit :
    Q.WF ∧ Exact.MarkWF Q.prog ∧ Exact.FiltUp Q.prog ∧ ConjOK Q (fun _ => True) ∧
    (∀ m a, applicable (X.α m a) a = true) ∧ ¬ LitConc Q ∧
    DN X (.nedge 0 [ic, ic] 2 (conjFact cj c1 c1)) ∧ (conjFact cj c1 c1).demand = false ∧
    PremCov [ic, ic] [l0, l0] ∧ NRel [ic, ic] [l0, l0] (conjFact cj c1 c1).fact lEnd ∧
    ¬ TaintN X.Q 0 2 lEnd [l0, l0] :=
  ⟨wf, markWF, filtUp, conjOK_true Q, policy_applicable _, not_litConc, d_edge, normal,
    .cons ic_covers (.cons ic_covers .nil),
    ⟨⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩, fun _ _ hI _ => nomatch (List.cons.inj hI).2⟩, no_taint⟩

end CexLit

#print axioms CexLit.wf
#print axioms CexLit.cex_lit

/-! ## 7. Without `ConjOK` the valid form is FALSE

  The `NDRule` sample of `ND.Example`: `$A = src(); $B = src(); $C = pass($A, $B)`. The
  validity `ok l := l.base = 3` (only the conjunction target is valid) satisfies `FiltValid` and
  `BackOK` (no filter, and no micro edge ends at the base `3`), and the literals are concrete
  (`LitConc`). The normal-layer edge `[zeroFact, zeroFact] → C` and the valid end location
  `3 with 9` would need a valid support, but the zero location is not valid. The conjunction is
  a micro edge that `BackOK` does not see; `ConjOK` is its `BackOK` link. -/

namespace CexConjOK
open ND.Example

def ok (l : Loc) : Prop := l.base = 3

theorem markWF : Exact.MarkWF X.Q.prog where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h => cases h
      | tail _ h =>
        cases h with
        | head => cases he
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem filtValid : Exact.FiltValid X.Q.prog ok := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- Every source edge ends at the base `1` or `2` (or the zero base), never at the base `3`. -/
theorem backOK : Exact.BackOK X.Q.prog ok where
  stmt := by
    intro M n s n' hE e he l1 l2 hd hok
    have hb : l2.base = e.2.base := hd.2.1
    have hok' : l2.base = 3 := hok
    cases hE with
    | head =>
      cases he with
      | head => rw [hok'] at hb; cases hb
      | tail _ h =>
        cases h with
        | head => rw [hok'] at hb; cases hb
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rw [hok'] at hb; cases hb
        | tail _ h =>
          cases h with
          | head => rw [hok'] at hb; cases hb
          | tail _ h => cases h
      | tail _ h =>
        cases h with
        | head => cases he
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem litConc : LitConc X.Q := by
  intro M n cj' n' hE
  cases hE with
  | head => exact ⟨⟨7, rfl⟩, ⟨8, rfl⟩⟩
  | tail _ h => cases h

theorem not_ok_zero : ¬ ok zeroLoc := by
  intro h
  have h' : (0 : Nat) = 3 := h
  exact absurd h' (by decide)

theorem not_conjOK : ¬ ConjOK X.Q ok := by
  intro h
  have h1 := (h 0 2 cj 3 List.mem_cons_self ⟨1, [], 7⟩ ⟨3, [], 9⟩ ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
    rfl).1 ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  have h1' : (1 : Nat) = 3 := h1
  exact absurd h1' (by decide)

/-- THE VALIDITY COUNTEREXAMPLE. Every hypothesis of `nd_edge_exact_valid` except `ConjOK` holds;
    the normal-layer ND edge has a valid end location whose support is not valid. -/
theorem cex_conjOK :
    Exact.MarkWF X.Q.prog ∧ Exact.FiltValid X.Q.prog ok ∧ Exact.BackOK X.Q.prog ok ∧
    LitConc X.Q ∧ ¬ ConjOK X.Q ok ∧
    DN X (.nedge 0 [zeroFact, zeroFact] 3 (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩)) ∧
    (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩).demand = false ∧
    PremCov [zeroFact, zeroFact] [zeroLoc, zeroLoc] ∧
    NRel [zeroFact, zeroFact] [zeroLoc, zeroLoc] (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩).fact
      ⟨3, [], 9⟩ ∧
    ok ⟨3, [], 9⟩ ∧ ¬ ok zeroLoc :=
  ⟨markWF, filtValid, backOK, litConc, not_conjOK, c3, c3_normal,
    .cons zeroFact_covers (.cons zeroFact_covers .nil),
    ⟨⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩, fun _ _ hI _ => nomatch (List.cons.inj hI).2⟩,
    rfl, not_ok_zero⟩

end CexConjOK

#print axioms CexConjOK.cex_conjOK

end ApSpec.NDExact
