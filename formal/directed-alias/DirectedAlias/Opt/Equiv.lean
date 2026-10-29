import DirectedAlias.Opt.Machine

/-!
# Optimization O, part 5: functional equivalence of O and C

The join, the top state, the loop and the whole analysis of O represent the C results on the
universe (`analyzeO_rel`). The O loop test (no union changed an id) is the C test `leOn`
(`joinO_flag`). The may-alias answers are equal (`omay_eq`, `mayProgO_eq`).
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-- Inclusion keeps its value when both sides change to set-equal lists. -/
theorem sub_congr {α : Type} {A A' B B' : List α} (hA : SetEq A A') (hB : SetEq B B') :
    B ⊆ A ↔ B' ⊆ A' :=
  ⟨fun h a ha => (hA a).mp (h ((hB a).mpr ha)), fun h a ha => (hA a).mpr (h ((hB a).mp ha))⟩

/-- A key that some map holds is a universe key. -/
theorem inU_of_key {ctx : Ctx} {T : Tbl} {s : OState} (h : EntOK ctx T s) {k : Key}
    (hk : k ∈ s.map Prod.fst) : InU ctx k := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  exact (h.ent p hp).2

/-- The join loop: the table stays good, each key of `ks` gets the union of the two values,
and the flag records a key of `ks` whose second value is not in the first value. -/
theorem jfold_spec {ctx : Ctx} (cc : CtxClosed ctx) {s1 s2 : OState} :
    ∀ (ks : List Key) {T : Tbl} {out : OState} {ch : Bool}, T.Good ctx.origins →
      EntOK ctx T s1 → EntOK ctx T s2 → EntOK ctx T out → (∀ k ∈ ks, InU ctx k) →
      (jfold ctx s1 s2 ks T out ch).1.Good ctx.origins ∧ T.Ext (jfold ctx s1 s2 ks T out ch).1 ∧
      EntOK ctx (jfold ctx s1 s2 ks T out ch).1 (jfold ctx s1 s2 ks T out ch).2.1 ∧
      (∀ k', SetEq (val ctx.K (jfold ctx s1 s2 ks T out ch).1 (jfold ctx s1 s2 ks T out ch).2.1 k')
        (if k' ∈ ks then uni (val ctx.K T s1 k') (val ctx.K T s2 k') else val ctx.K T out k')) ∧
      ((jfold ctx s1 s2 ks T out ch).2.2 = true ↔
        (ch = true ∨ ∃ k ∈ ks, subB (val ctx.K T s2 k) (val ctx.K T s1 k) = false))
  | [], T, out, ch, g, _, _, ho, _ => by
    refine ⟨g, Tbl.Ext.refl T, ho, ?_, ?_⟩
    · intro k'; simp only [jfold, List.not_mem_nil, ite_false]; exact SetEq.refl _
    · simp [jfold]
  | k :: ks, T, out, ch, g, h1, h2, ho, hks => by
    have hk : InU ctx k := hks k List.mem_cons_self
    obtain ⟨ga, ea, ia, ma⟩ := getId_spec cc g h1 hk
    simp only [jfold]
    generalize getId ctx T s1 k = a at ga ea ia ma
    obtain ⟨gb, eb, ib, mb⟩ := getId_spec cc ga (h2.ext ea) hk
    generalize getId ctx a.2 s2 k = b at gb eb ib mb
    have iab : a.1 < b.2.size := Nat.lt_of_lt_of_le ia eb.size_le
    obtain ⟨gu, eu, iu, mu⟩ := Tbl.union_spec gb iab ib
    generalize b.2.union ctx.origins a.1 b.1 = u at gu eu iu mu
    have eT : T.Ext u.2 := ea.trans (eb.trans eu)
    have hA : SetEq (u.2.mem a.1) (val ctx.K T s1 k) := by
      rw [(eb.trans eu).mem_eq ia]; exact ma
    have hB : SetEq (b.2.mem b.1) (val ctx.K T s2 k) := by
      rw [← val_ext h2 ea]; exact mb
    have hU : SetEq (u.2.mem u.1) (uni (val ctx.K T s1 k) (val ctx.K T s2 k)) := by
      rw [eb.mem_eq ia] at mu
      exact mu.trans (SetEq.uni ma hB)
    have hne : (decide (u.1 ≠ a.1) = true) ↔ subB (val ctx.K T s2 k) (val ctx.K T s1 k) = false := by
      have hid := Tbl.id_eq_iff gu iu (Nat.lt_of_lt_of_le ia (eb.trans eu).size_le)
      rw [decide_eq_true_iff]
      constructor
      · intro hn
        cases hs : subB (val ctx.K T s2 k) (val ctx.K T s1 k) with
        | false => rfl
        | true =>
          exfalso; apply hn; apply hid.mpr
          exact hU.trans ((uni_setEq_left_iff.mpr (subB_iff.mp hs)).trans hA.symm)
      · intro hs heq
        have h3 : SetEq (uni (val ctx.K T s1 k) (val ctx.K T s2 k)) (val ctx.K T s1 k) :=
          hU.symm.trans ((hid.mp heq).trans hA)
        have : subB (val ctx.K T s2 k) (val ctx.K T s1 k) = true :=
          subB_iff.mpr (fun a ha => uni_setEq_left_iff.mp h3 ha)
        rw [hs] at this; cases this
    obtain ⟨g4, e4, h4, m4, c4⟩ := jfold_spec cc ks gu (h1.ext eT) (h2.ext eT)
      ((ho.ext eT).oset iu hk) (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (ch := ch || decide (u.1 ≠ a.1))
    simp only [val_ext h1 eT, val_ext h2 eT] at m4 c4
    refine ⟨g4, eT.trans e4, h4, ?_, ?_⟩
    · intro k'
      refine (m4 k').trans ?_
      by_cases hin : k' ∈ ks
      · rw [ite_eq_left hin, ite_eq_left (List.mem_cons_of_mem _ hin)]; exact SetEq.refl _
      · rw [ite_eq_right hin, val_oset]
        by_cases hkk : k' = k
        · subst hkk; rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]; exact hU
        · rw [ite_eq_right hkk, val_ext ho eT]
          have : k' ∉ k :: ks := by simp [hkk, hin]
          rw [ite_eq_right this]; exact SetEq.refl _
    · rw [c4, Bool.or_eq_true, hne]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- The O join: each key gets the union of its two values, and the flag is true if and only if
some key of the second state has an origin that the first state does not have. -/
theorem joinO_spec {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {s1 s2 : OState} (h1 : EntOK ctx T s1) (h2 : EntOK ctx T s2) :
    (joinO ctx T s1 s2).1.Good ctx.origins ∧ T.Ext (joinO ctx T s1 s2).1 ∧
      EntOK ctx (joinO ctx T s1 s2).1 (joinO ctx T s1 s2).2.1 ∧
      (∀ k, SetEq (val ctx.K (joinO ctx T s1 s2).1 (joinO ctx T s1 s2).2.1 k)
        (uni (val ctx.K T s1 k) (val ctx.K T s2 k))) ∧
      ((joinO ctx T s1 s2).2.2 = true ↔
        ∃ k ∈ s1.map Prod.fst ++ s2.map Prod.fst,
          subB (val ctx.K T s2 k) (val ctx.K T s1 k) = false) := by
  have hks : ∀ k ∈ s1.map Prod.fst ++ s2.map Prod.fst, InU ctx k := by
    intro k hk
    cases List.mem_append.mp hk with
    | inl h => exact inU_of_key h1 h
    | inr h => exact inU_of_key h2 h
  obtain ⟨g1, e1, h3, m1, c1⟩ :=
    jfold_spec cc (s1.map Prod.fst ++ s2.map Prod.fst) g h1 h2 (EntOK.nil ctx T) hks
      (ch := false)
  refine ⟨g1, e1, h3, ?_, ?_⟩
  · intro k
    refine (m1 k).trans ?_
    split
    · exact SetEq.refl _
    · rename_i hn
      have n1 : k ∉ s1.map Prod.fst := fun h => hn (List.mem_append_left _ h)
      have n2 : k ∉ s2.map Prod.fst := fun h => hn (List.mem_append_right _ h)
      simp only [val, oget_none_of_not_mem n1, oget_none_of_not_mem n2, oget]
      exact (uni_self_set _).symm
  · unfold joinO; rw [c1]; simp

/-- The O join flag is the negation of the C loop test `leOn`. -/
theorem joinO_flag {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {s1 s2 : OState} {X1 X2 : AState} (r1 : Rel ctx T s1 X1) (r2 : Rel ctx T s2 X2) :
    (joinO ctx T s1 s2).2.2 = !(leOn ctx X2 X1) := by
  obtain ⟨_, _, _, _, c1⟩ := joinO_spec cc g r1.ent r2.ent
  cases hf : (joinO ctx T s1 s2).2.2 with
  | true =>
    obtain ⟨k, hk, hs⟩ := c1.mp hf
    have hu : InU ctx k := by
      cases List.mem_append.mp hk with
      | inl h => exact inU_of_key r1.ent h
      | inr h => exact inU_of_key r2.ent h
    cases hl : leOn ctx X2 X1 with
    | false => rfl
    | true =>
      have hsub := leOn_iff_keys.mp hl k hu
      have : subB (val ctx.K T s2 k) (val ctx.K T s1 k) = true :=
        subB_iff.mpr (fun a ha => (sub_congr (r1.agree k hu) (r2.agree k hu)).mpr hsub ha)
      rw [hs] at this; cases this
  | false =>
    have hall : ∀ k ∈ s1.map Prod.fst ++ s2.map Prod.fst,
        subB (val ctx.K T s2 k) (val ctx.K T s1 k) = true := by
      intro k hk
      cases hs : subB (val ctx.K T s2 k) (val ctx.K T s1 k) with
      | true => rfl
      | false => have := c1.mpr ⟨k, hk, hs⟩; rw [hf] at this; cases this
    have : leOn ctx X2 X1 = true := by
      apply leOn_iff_keys.mpr
      intro k hk
      apply (sub_congr (r1.agree k hk) (r2.agree k hk)).mp
      by_cases hin : k ∈ s1.map Prod.fst ++ s2.map Prod.fst
      · exact subB_iff.mp (hall k hin)
      · have n1 : k ∉ s1.map Prod.fst := fun h => hin (List.mem_append_left _ h)
        have n2 : k ∉ s2.map Prod.fst := fun h => hin (List.mem_append_right _ h)
        simp only [val, oget_none_of_not_mem n1, oget_none_of_not_mem n2]
        exact fun _ h => h
    rw [this]; rfl

/-- The O join represents the C join. -/
theorem joinO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {s1 s2 : OState} {X1 X2 : AState} (r1 : Rel ctx T s1 X1) (r2 : Rel ctx T s2 X2) :
    (joinO ctx T s1 s2).1.Good ctx.origins ∧ T.Ext (joinO ctx T s1 s2).1 ∧
      Rel ctx (joinO ctx T s1 s2).1 (joinO ctx T s1 s2).2.1 (join X1 X2) := by
  obtain ⟨g1, e1, h3, m1, _⟩ := joinO_spec cc g r1.ent r2.ent
  refine ⟨g1, e1, rel_of_vals h3 (r1.supp.join r2.supp) _ m1 ?_⟩
  intro k hk
  rw [cval_join]
  exact SetEq.uni (r1.agree k hk) (r2.agree k hk)

/-- The O top state represents the C top state. -/
theorem topO_rel {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} {Y : AState} (hR : Rel ctx T st Y) :
    (topO ctx T st).1.Good ctx.origins ∧ T.Ext (topO ctx T st).1 ∧
      Rel ctx (topO ctx T st).1 (topO ctx T st).2 (top ctx Y) := by
  obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g (S := ctx.origins) (fun _ h => h)
  unfold topO
  simp only
  generalize T.intern ctx.origins ctx.origins none = u at g1 e1 i1 m1
  obtain ⟨g2, e2, h2, m2⟩ := addAll_spec cc (ukeys ctx) g1 (hR.ent.ext e1)
    (fun k hk => mem_ukeys.mp hk) i1
  refine ⟨g2, e1.trans e2, rel_of_vals h2 hR.supp.top _ m2 ?_⟩
  intro k hk
  rw [ite_eq_left (mem_ukeys.mpr hk), cval_top, val_ext hR.ent e1]
  exact (SetEq.uni (hR.agree k hk) m1).trans (uni_comm_set _ _)

/-- The O loop represents the C loop, if the O body represents the C body. -/
theorem loopO_rel {ctx : Ctx} (cc : CtxClosed ctx) {f : Tbl → OState → Tbl × OState}
    {F : AState → AState}
    (hf : ∀ (T : Tbl) (st : OState) (Y : AState), T.Good ctx.origins → Rel ctx T st Y →
      (f T st).1.Good ctx.origins ∧ T.Ext (f T st).1 ∧ Rel ctx (f T st).1 (f T st).2 (F Y)) :
    ∀ (n : Nat) (T : Tbl) (st : OState) (Y : AState), T.Good ctx.origins → Rel ctx T st Y →
      (loopO ctx f n T st).1.Good ctx.origins ∧ T.Ext (loopO ctx f n T st).1 ∧
      Rel ctx (loopO ctx f n T st).1 (loopO ctx f n T st).2 (loopIter ctx F n Y)
  | 0, T, st, Y, g, hR => topO_rel cc g hR
  | n + 1, T, st, Y, g, hR => by
    obtain ⟨g1, e1, r1⟩ := hf T st Y g hR
    simp only [loopO, loopIter]
    generalize f T st = r at g1 e1 r1
    have r0 := hR.ext e1
    have hflag := joinO_flag cc g1 r0 r1
    obtain ⟨g2, e2, r2⟩ := joinO_rel cc g1 r0 r1
    generalize joinO ctx r.1 st r.2 = j at hflag g2 e2 r2
    rw [hflag]
    cases hl : leOn ctx (F Y) Y with
    | true => exact ⟨g2, e1.trans e2, r0.ext e2⟩
    | false =>
      obtain ⟨g3, e3, r3⟩ := loopO_rel cc hf n j.1 j.2.1 _ g2 r2
      exact ⟨g3, e1.trans (e2.trans e3), r3⟩

/-- The O analysis represents the C analysis on the universe, for each covered program. -/
theorem analyzeO_rel {ctx : Ctx} (cc : CtxClosed ctx) :
    ∀ (q : Prog) (T : Tbl) (st : OState) (X : AState), ProgOK ctx q → T.Good ctx.origins →
      Rel ctx T st X →
      (analyzeO ctx q T st).1.Good ctx.origins ∧ T.Ext (analyzeO ctx q T st).1 ∧
      Rel ctx (analyzeO ctx q T st).1 (analyzeO ctx q T st).2 (analyze ctx q X)
  | .skip, T, _, _, _, g, hR => ⟨g, Tbl.Ext.refl T, hR⟩
  | .stmt s, _, _, _, ok, g, hR => ostep_rel cc g hR (ok s (by simp [Prog.stmts]))
  | .seq p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeO_rel cc p T st X (ProgOK.left ok) g hR
    simp only [analyzeO, analyze]
    generalize analyzeO ctx p T st = r at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeO_rel cc q r.1 r.2 _ (ProgOK.right ok) g1 r1
    exact ⟨g2, e1.trans e2, r2⟩
  | .choice p q, T, st, X, ok, g, hR => by
    obtain ⟨g1, e1, r1⟩ := analyzeO_rel cc p T st X (ProgOK.left ok) g hR
    simp only [analyzeO, analyze]
    generalize analyzeO ctx p T st = a at g1 e1 r1
    obtain ⟨g2, e2, r2⟩ := analyzeO_rel cc q a.1 st X (ProgOK.right ok) g1 (hR.ext e1)
    generalize analyzeO ctx q a.1 st = b at g2 e2 r2
    obtain ⟨g3, e3, r3⟩ := joinO_rel cc g2 (r1.ext e2) r2
    exact ⟨g3, e1.trans (e2.trans e3), r3⟩
  | .loop p, T, st, X, ok, g, hR => by
    simp only [analyzeO, analyze]
    exact loopO_rel cc (fun T' st' Y g' hR' => analyzeO_rel cc p T' st' Y ok g' hR')
      ctx.fuel T st X g hR

/-! ## The entry state -/

/-- The entry fold sets each listed variable to its entry origins. -/
theorem initFold_spec {ctx : Ctx} (fr : Frame) (hsupp : Supp ctx (ainit ctx.K fr)) :
    ∀ (xs : List Var) {T : Tbl} {st : OState}, T.Good ctx.origins → EntOK ctx T st →
      (∀ x ∈ xs, x ∈ ctx.vars) →
      (initFold ctx fr xs T st).1.Good ctx.origins ∧ T.Ext (initFold ctx fr xs T st).1 ∧
      EntOK ctx (initFold ctx fr xs T st).1 (initFold ctx fr xs T st).2 ∧
      ∀ k, SetEq (val ctx.K (initFold ctx fr xs T st).1 (initFold ctx fr xs T st).2 k)
        (if k ∈ xs.map Key.v then cval (ainit ctx.K fr) k else val ctx.K T st k)
  | [], T, st, g, h, _ => by
    refine ⟨g, Tbl.Ext.refl T, h, ?_⟩
    intro k; simp only [initFold, List.map_nil, List.not_mem_nil, ite_false]; exact SetEq.refl _
  | x :: xs, T, st, g, h, hxs => by
    have hx : x ∈ ctx.vars := hxs x List.mem_cons_self
    obtain ⟨g1, e1, h1, m1⟩ := setKey_spec g h (k := .v x) hx (S := (ainit ctx.K fr).env x)
      (hsupp (.v x) hx)
    simp only [initFold]
    generalize setKey ctx T st (.v x) ((ainit ctx.K fr).env x) = r at g1 e1 h1 m1
    obtain ⟨g2, e2, h2, m2⟩ :=
      initFold_spec fr hsupp xs g1 h1 (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    refine ⟨g2, e1.trans e2, h2, ?_⟩
    intro k
    refine (m2 k).trans ?_
    by_cases hin : k ∈ xs.map Key.v
    · rw [ite_eq_left hin, ite_eq_left (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hin)]
      exact SetEq.refl _
    · rw [ite_eq_right hin]
      refine (m1 k).trans ?_
      by_cases hkx : k = .v x
      · subst hkx
        rw [ite_eq_left rfl, ite_eq_left (by simp)]
        exact SetEq.refl _
      · have hn2 : k ∉ (x :: xs).map Key.v := by
          simp only [List.map_cons, List.mem_cons]
          rintro (h | h)
          · exact hkx h
          · exact hin h
        rw [ite_eq_right hkx, ite_eq_right hn2]
        exact SetEq.refl _

/-- The entry O state represents the C entry state. -/
theorem initO_rel {ctx : Ctx} (fr : Frame) (hsupp : Supp ctx (ainit ctx.K fr))
    (hfv : ∀ x ∈ fr.vars, x ∈ ctx.vars) :
    (initO ctx fr).1.Good ctx.origins ∧ Rel ctx (initO ctx fr).1 (initO ctx fr).2 (ainit ctx.K fr) := by
  obtain ⟨g1, _, h1, m1⟩ :=
    initFold_spec fr hsupp fr.vars (Tbl.good_empty ctx.origins) (EntOK.nil ctx _) hfv
  refine ⟨g1, rel_of_vals h1 hsupp _ m1 ?_⟩
  intro k hk
  split
  · exact SetEq.refl _
  · rename_i hn
    rw [val_nil]
    cases k with
    | v x =>
      have hx : x ∉ fr.vars := fun h => hn (List.mem_map.mpr ⟨x, h, rfl⟩)
      have : fr.root? x = none := lookup_none_of_not_mem fr.binds x hx
      simp only [dflt, cval, ainit, this]
      exact SetEq.refl _
    | h o c => exact SetEq.refl _

/-! ## Queries -/

/-- The O path evaluation represents the C path evaluation. -/
theorem oevalFrom_spec {ctx : Ctx} (cc : CtxClosed ctx) {st : OState} {X : AState} :
    ∀ (p : List ACell) {T : Tbl} {i : Nat} {S : List Origin}, T.Good ctx.origins →
      Rel ctx T st X → i < T.size → SetEq (T.mem i) S → S ⊆ ctx.origins →
      (∀ c ∈ p, c ∈ ctx.cells) →
      (oevalFrom ctx st T i p).2.Good ctx.origins ∧ T.Ext (oevalFrom ctx st T i p).2 ∧
      (oevalFrom ctx st T i p).1 < (oevalFrom ctx st T i p).2.size ∧
      SetEq ((oevalFrom ctx st T i p).2.mem (oevalFrom ctx st T i p).1) (aevalFrom X S p)
  | [], T, i, S, g, _, hi, hS, _, _ => ⟨g, Tbl.Ext.refl T, hi, hS⟩
  | c :: cs, T, i, S, g, hR, hi, hS, hSU, hp => by
    have hc : c ∈ ctx.cells := hp c List.mem_cons_self
    obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g (S := []) (fun _ h => by cases h)
    simp only [oevalFrom, aevalFrom]
    generalize T.intern ctx.origins [] none = e at g1 e1 i1 m1
    have h1 : EntOK ctx e.2 st := hR.ent.ext e1
    obtain ⟨g2, e2, i2, m2⟩ := readUnion_spec cc hc (e.2.mem i) g1 h1 (g1.mem_sub i) i1
    generalize readUnion ctx st c e.2 (e.2.mem i) e.1 = r at g2 e2 i2 m2
    have hRr := hR.ext (e1.trans e2)
    have hm : SetEq (r.2.mem r.1) (aread X S c) := by
      intro o'
      rw [m2 o', m1 o']
      simp only [List.not_mem_nil, false_or]
      rw [e1.mem_eq hi]
      have := aread_agree (hR.ext e1) hS hSU hc o'
      exact this
    obtain ⟨g3, e3, i3, m3⟩ := oevalFrom_spec cc cs g2 hRr i2 hm (aread_sub hR.supp hSU hc)
      (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))
    exact ⟨g3, e1.trans (e2.trans e3), i3, m3⟩

/-- The O evaluation of `x.p` represents the C evaluation of `x.p`. -/
theorem oevalPath_spec {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} {st : OState} {X : AState}
    (g : T.Good ctx.origins) (hR : Rel ctx T st X) {x : Var} (hx : x ∈ ctx.vars)
    {p : List ACell} (hp : ∀ c ∈ p, c ∈ ctx.cells) :
    (oevalPath ctx T st x p).2.Good ctx.origins ∧ T.Ext (oevalPath ctx T st x p).2 ∧
      (oevalPath ctx T st x p).1 < (oevalPath ctx T st x p).2.size ∧
      SetEq ((oevalPath ctx T st x p).2.mem (oevalPath ctx T st x p).1) (aevalPath X x p) := by
  obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g hR.ent (k := .v x) hx
  unfold oevalPath aevalPath
  simp only
  generalize getId ctx T st (.v x) = r at g1 e1 i1 m1
  obtain ⟨g2, e2, i2, m2⟩ := oevalFrom_spec cc p g1 (hR.ext e1) i1
    (m1.trans (hR.agree (.v x) hx)) (hR.supp.env hx) hp
  exact ⟨g2, e1.trans e2, i2, m2⟩

/-- O may-alias gives the same Boolean as C may-alias on universe variables and cells. -/
theorem omay_eq {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} {st : OState} {X : AState}
    (g : T.Good ctx.origins) (hR : Rel ctx T st X) {x y : Var} (hx : x ∈ ctx.vars)
    (hy : y ∈ ctx.vars) {px py : List ACell} (hpx : ∀ c ∈ px, c ∈ ctx.cells)
    (hpy : ∀ c ∈ py, c ∈ ctx.cells) : omay ctx T st x px y py = may X x px y py := by
  obtain ⟨g1, e1, i1, m1⟩ := oevalPath_spec cc g hR hx hpx
  unfold omay may
  simp only
  generalize oevalPath ctx T st x px = a at g1 e1 i1 m1
  obtain ⟨_, e2, _, m2⟩ := oevalPath_spec cc g1 (hR.ext e1) hy hpy
  generalize oevalPath ctx a.2 st y py = b at e2 m2
  rw [e2.mem_eq i1]
  exact meetB_congr m1 m2

/-! ## Whole programs -/

/-- The cells of a query path are in the universe of the program context. -/
theorem query_cells (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) (px : List ACell)
    (h : ∀ f ∈ afields px, f ∈ qf) : ∀ c ∈ px, c ∈ (progCtx K fr p qf).cells := by
  intro c hc
  simp only [progCtx, Ctx.ofProg, cellsOf]
  cases c with
  | elem => simp
  | fld f =>
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨f, ?_, rfl⟩
    rw [List.mem_eraseDups]
    apply List.mem_append_right
    apply h
    simp only [afields, List.mem_filterMap]
    exact ⟨.fld f, hc, rfl⟩

/-- For each program, the final O state represents the final C state on the universe. -/
theorem analyzeProgO_rel (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (analyzeProgO K fr p qf).1.Good (progCtx K fr p qf).origins ∧
      Rel (progCtx K fr p qf) (analyzeProgO K fr p qf).1 (analyzeProgO K fr p qf).2
        (analyzeProg K fr p qf) := by
  have cc := ctxClosed_ofProg K fr p qf
  have hfv : ∀ x ∈ fr.vars, x ∈ (progCtx K fr p qf).vars := by
    intro x hx
    simp only [progCtx, Ctx.ofProg]
    rw [List.mem_eraseDups]
    exact List.mem_append_right _ hx
  obtain ⟨g0, r0⟩ := initO_rel (ctx := progCtx K fr p qf) fr (supp_ainit K fr p qf) hfv
  obtain ⟨g1, _, r1⟩ := analyzeO_rel cc p _ _ _ (progOK_ofProg K fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- For each program and each query on program or frame variables, O and C give the same
may-alias answer. -/
theorem mayProgO_eq (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List ACell) (y : Var)
    (py : List ACell) (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgO K fr p x px y py = mayProg K fr p x px y py := by
  have cc := ctxClosed_ofProg K fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgO_rel K fr p (afields px ++ afields py)
  unfold mayProgO mayProg
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (progCtx K fr p (afields px ++ afields py)).vars := by
    intro z hz; simp only [progCtx, Ctx.ofProg]; rw [List.mem_eraseDups]; exact hz
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

/-! ## Both strong-update policies -/

/-- The context of a program with the strong-update policy `eu`. -/
def progCtxE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  { Ctx.ofProg K fr p qf with entryUnique := eu }

/-- The final O state of program `p` with the policy `eu`. -/
def analyzeProgOE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Tbl × OState :=
  let ctx := progCtxE eu K fr p qf
  let i := initO ctx fr
  analyzeO ctx p i.1 i.2

/-- O may-alias at the end of program `p` with the policy `eu`. -/
def mayProgOE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let r := analyzeProgOE eu K fr p (afields px ++ afields py)
  omay (progCtxE eu K fr p (afields px ++ afields py)) r.1 r.2 x px y py

/-- C may-alias at the end of program `p` with the policy `eu`. -/
def mayProgE (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyze (progCtxE eu K fr p (afields px ++ afields py)) p (ainit K fr)) x px y py

/-- The policy context is closed under default content. -/
theorem ctxClosed_E (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxClosed (progCtxE eu K fr p qf) :=
  ⟨(ctxClosed_ofProg K fr p qf).dflt, (ctxClosed_ofProg K fr p qf).elem⟩

/-- The policy context covers the program. -/
theorem progOK_E (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ProgOK (progCtxE eu K fr p qf) p := fun st h =>
  let o := progOK_ofProg K fr p qf st h
  ⟨o.vars, o.fields, o.new, o.fresh, o.call⟩

/-- For each policy and each program, the final O state represents the final C state. -/
theorem analyzeProgOE_rel (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    (analyzeProgOE eu K fr p qf).1.Good (progCtxE eu K fr p qf).origins ∧
      Rel (progCtxE eu K fr p qf) (analyzeProgOE eu K fr p qf).1 (analyzeProgOE eu K fr p qf).2
        (analyze (progCtxE eu K fr p qf) p (ainit K fr)) := by
  have cc := ctxClosed_E eu K fr p qf
  have hfv : ∀ x ∈ fr.vars, x ∈ (progCtxE eu K fr p qf).vars := by
    intro x hx
    simp only [progCtxE, Ctx.ofProg]
    rw [List.mem_eraseDups]
    exact List.mem_append_right _ hx
  obtain ⟨g0, r0⟩ := initO_rel (ctx := progCtxE eu K fr p qf) fr (supp_ainit K fr p qf) hfv
  obtain ⟨g1, _, r1⟩ := analyzeO_rel cc p _ _ _ (progOK_E eu K fr p qf) g0 r0
  exact ⟨g1, r1⟩

/-- For both strong-update policies, O and C give the same may-alias answer. -/
theorem mayProgOE_eq (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List ACell)
    (y : Var) (py : List ACell) (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgOE eu K fr p x px y py = mayProgE eu K fr p x px y py := by
  have cc := ctxClosed_E eu K fr p (afields px ++ afields py)
  obtain ⟨g, hR⟩ := analyzeProgOE_rel eu K fr p (afields px ++ afields py)
  unfold mayProgOE mayProgE
  simp only
  have hv : ∀ z, z ∈ p.vars ++ fr.vars →
      z ∈ (progCtxE eu K fr p (afields px ++ afields py)).vars := by
    intro z hz; simp only [progCtxE, Ctx.ofProg]; rw [List.mem_eraseDups]; exact hz
  exact omay_eq cc g hR (hv x hx) (hv y hy)
    (query_cells K fr p _ px (fun f hf => List.mem_append_left _ hf))
    (query_cells K fr p _ py (fun f hf => List.mem_append_right _ hf))

end DirectedAlias.Opt
