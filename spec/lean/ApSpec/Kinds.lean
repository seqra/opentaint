/-
  ApSpec.Kinds — the three conclusion kinds of an edge (spec `ap.md` §7.2).

  The spec gives the conclusions of one edge group ONE MARK KIND. The premise set gives it:
    * REACH: the premise set `{zero}`, and the conclusion is the zero fact;
    * FLOW: one premise with the mark `*`. The conclusions have abstract marks only. There is no
      `$` leaf. A `*` leaf is normal;
    * TAINT: the zero premise or concrete premises, and EVERY premise set with two or more members.
      The conclusions have concrete marks only. There is no `*` leaf.
  This file proves the partition for the closures of the model. In the model a REACH edge is the
  TAINT edge from the zero fact to the zero fact: both have concrete marks (`zeroMark`).

  Contents.
    1. `ExactTargetConc`: the NEW program condition (the interpreter duty of S8, `interpreter.md`
       I7): a micro edge (a statement edge or a call binding) with a `$` target has a concrete
       premise mark. `InitK`: the premise condition of run 1 (the mark is `*` or concrete, and an
       abstract premise has no `$` and no `*/Universe` tail). The policy satisfies it
       (`policy_initK`).
    2. Local lemmas. A FLOW fact (`FlowF`: an abstract mark, and the tail `[any]` or `*/E` with `E`
       not Universe) stays a FLOW fact through `applyEdge` (`applyEdge_flow`, `micro_flow`), a
       summary (`applySummary_flow`), the field limit, the transfer, the cleaner and the start fact.
    3. The closure invariant `kInv_all`: ONE induction on `D`.
    4. The theorems of run 1 (`D`; run 1 is `α = policy1`):
       * K1 `flow_abstract` (§7.2 FLOW, S7): a `*` premise gives an abstract conclusion mark. The
         only hypothesis is `Exact.MarkWF` (the mark part of `Exact.D_edgeOK`).
       * K2 `flow_no_exact_gen`, `flow_no_exact` (§7.2 FLOW, S7, S8): a `*` premise gives no `$`
         conclusion.
       * K3 `taint_concrete` (§7.2 TAINT, `Coverage.edge_conc`, W2): a concrete premise or the zero
         premise gives a concrete conclusion mark and no `*` tail. No hypothesis.
       * `kinds_D` (§7.2 with §2.3 W2): the partition in one theorem. `flow_leaves`,
         `taint_leaves`: the leaf tails of each kind.
    5. K4 (§4.6, §7.1, §2.3 W7): an ND edge is a TAINT edge.
       * `nd_taint` (`ND.DN`): every member is concrete (the zero fact can be a member), and the
         conclusion is concrete with no `*` tail. From `NDExact.nd_edgeOK` and
         `ND.ndConclusion_uncorrelated`.
       * `ndz_taint` (`NDZ.DNz`): no member is the zero fact, every member is concrete, and the
         conclusion is concrete with no `*` tail. Own invariant `zInv_all`: ONE induction on `DNz`.
    6. The restricted runs (§6.3, §7.2 last paragraph): `kinds_DR` (from `RExact.DR_concrete` and
       `RExact.final_star_legalR`), `kinds_DB` (from `BExact.DB_concrete`) and `kinds_DB_taint`
       (with S11 (f), `SeedTails`; one induction on `DB`, `tInvB_all`): no FLOW edge.
    7. Counterexamples (short runs, checked with `decide` and `rfl`): each hypothesis of K1, K2 and
       K4 is necessary. `CexK` (run 1), `CexND` (`DN` and `DNz`), `ZeroMembers`.

  Design choices.
    * K1 needs only S7 (`MarkWF`). K2 needs S7, the two S8 hypotheses of `Invariant.no_univ_star`
      (`PremConc`, `NoUnivE`), the new `ExactTargetConc`, and `InitK` for the abstraction. The
      reasons: the normal form `AFact.norm` makes `$` from a `*/Universe` fact (after a cleaner of
      all marks, or under a demand summary); a `$` premise with the mark `*` makes `$` from an
      `[any]` fact; a `$` target with the premise mark `*` makes `$` directly. `CexK` has one run
      for each case.
    * The FLOW invariant holds for every abstract premise (`*` or `*∖x`, `Exact.absB`). Run 1 has
      only the premise mark `*` (`InitK`). The theorems use `i.mark = .star`.
    * W6 is not in the model (ap.md §11.2): here an `[any]` leaf of FLOW or TAINT can be in the
      normal layer. The theorems claim nothing about the layer of an `[any]` leaf.
    * The backward run: the mark part (`kinds_DB`) needs no seed tail. The rule `seed` copies the
      seed, so a seed with a `*` tail and a concrete mark gives a `*` leaf with a concrete mark
      (`CexSeedTail.cex_seed_tail`). With S11 (f) (`SeedTails`) the tail part holds too
      (`kinds_DB_taint`, invariant `tInvB_all`); no condition on the reversed program is needed.
    * `DN` keeps the zero fact in a joined premise list. So an ND edge of `DN` can have zero
      members (`ZeroMembers.dn_zero_members`). `DNz` drops them (`ZeroMembers.dnz_zero_members`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.Invariant
import ApSpec.Coverage
import ApSpec.Exact
import ApSpec.Restricted
import ApSpec.NDExact
import ApSpec.NDZ
import ApSpec.RestrictedExact
import ApSpec.BackwardExact

namespace ApSpec.Kinds
open ApSpec

/-! ## 1. Conditions -/

/-- The NEW program condition (S8, the interpreter duty `interpreter.md` I7): every micro edge (a
    statement edge, a binding into the callee, a binding back) with a `$` target has a concrete
    premise mark. Necessary for K2: `CexK.cex_etc`. -/
def ExactTargetConc (P : Program) : Prop :=
  Invariant.AllEdges P (fun e => e.2.kind = .exact → ∃ t, e.1.mark = .conc t)

/-- A tail of a FLOW conclusion: `[any]`, or `*/E` with `E` not Universe. -/
def FlowKind (k : Kind) : Prop := k = .any ∨ ∃ xs, k = .star (.set xs)

/-- A FLOW conclusion: an abstract mark (`*` or `*∖x`) and a FLOW tail. -/
def FlowF (f : AFact) : Prop := Exact.absB f.fact.mark = true ∧ FlowKind f.fact.kind

/-- The premise condition of run 1: the mark is `*` or concrete (never `*∖x`), and an abstract
    premise has a FLOW tail (no `$`, no `*/Universe`). -/
def InitK (i : PFact) : Prop :=
  (i.mark = .star ∨ ∃ t, i.mark = .conc t) ∧ (Exact.absB i.mark = true → FlowKind i.kind)

theorem absB_iff {m : MarkA} : Exact.absB m = true ↔ Invariant.AbsMark m := by
  cases m with
  | star => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | starEx x => exact ⟨fun _ => Or.inr ⟨x, rfl⟩, fun _ => rfl⟩
  | conc t =>
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    rcases h with h | ⟨x, h⟩ <;> cases h

theorem absB_of_conc {m : MarkA} {t : Mark} (h : m = .conc t) : Exact.absB m = false := by
  rw [h]; rfl

theorem not_abs_of_conc {m : MarkA} {t : Mark} (h : m = .conc t) (ha : Exact.absB m = true) :
    False := by
  rw [absB_of_conc h] at ha
  cases ha

theorem flowKind_ne {k : Kind} (h : FlowKind k) : k ≠ .exact ∧ k ≠ .star .univ := by
  rcases h with rfl | ⟨xs, rfl⟩
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem flowKind_of_ne {k : Kind} (h1 : k ≠ .exact) (h2 : k ≠ .star .univ) : FlowKind k := by
  cases k with
  | star e =>
    cases e with
    | set xs => exact Or.inr ⟨xs, rfl⟩
    | univ => exact absurd rfl h2
  | any => exact Or.inl rfl
  | exact => exact absurd rfl h1

/-- The root and every answer satisfy `InitK`: their marks are concrete. -/
theorem initK_conc {i : PFact} {t : Mark} (h : i.mark = .conc t) : InitK i :=
  ⟨Or.inr ⟨t, h⟩, fun ha => (not_abs_of_conc h ha).elim⟩

/-- The run-1 policy (every demand) satisfies `InitK`. -/
theorem policy_initK (demand : MethodId → List PFact) (m : MethodId) (a : PFact) :
    InitK (policy demand m a) := by
  unfold policy
  split
  · exact initK_conc (t := zeroMark) rfl
  · split
    · exact ⟨Or.inl rfl, fun _ => Or.inr ⟨[], rfl⟩⟩
    · exact ⟨Or.inl rfl, fun _ => Or.inr ⟨[], rfl⟩⟩

theorem policy1_initK : ∀ m a, InitK (policy1 m a) := policy_initK (fun _ => [])

#print axioms policy1_initK

/-! ## 2. Local lemmas: a FLOW fact stays a FLOW fact -/

theorem tailExcl_set {fk : Kind} (h : FlowKind fk) : ∃ xs, tailExcl fk = .set xs := by
  rcases h with rfl | ⟨xs, rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨xs, rfl⟩

theorem belowCase_flow {ck fk tk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hc : FlowKind ck) (hf : FlowKind fk) (ht : FlowKind tk)
    (h : belowCase ck fk r tp tk = some (p, k, ap)) : FlowKind k := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    rcases ht with rfl | ⟨ys, rfl⟩
    · cases h; exact Or.inl rfl
    · cases r with
      | cons a r' =>
        dsimp only at h
        cases he : (Excl.set ys).admits (a :: r') with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [he, if_pos rfl] at h; cases h; exact hc
      | nil =>
        dsimp only at h
        obtain ⟨xs, hx⟩ := tailExcl_set hf
        rw [hx] at h
        rcases hc with rfl | ⟨zs, rfl⟩
        · cases h; exact Or.inl rfl
        · cases h; exact Or.inr ⟨_, rfl⟩

theorem aboveCase_flow {ck fk tk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (ht : FlowKind tk) (h : aboveCase ck fk r tp tk = some (p, k, ap)) : FlowKind k := by
  unfold aboveCase at h
  cases ha : admitsTailB ck r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    rcases ht with rfl | ⟨ys, rfl⟩
    · cases h; exact Or.inl rfl
    · cases h; exact Or.inl rfl

/-- The geometry keeps a FLOW tail if the fact, the premise and the target have FLOW tails. -/
theorem geo_flow {ck fk tk : Kind} {P q tp p : List Acc} {k : Kind} {ap : Bool}
    (hc : FlowKind ck) (hf : FlowKind fk) (ht : FlowKind tk)
    (h : CoreAux.geo ck fk P q tp tk = some (p, k, ap)) : FlowKind k := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r => rw [hrel] at h; exact aboveCase_flow ht h
  | below r => rw [hrel] at h; exact belowCase_flow hc hf ht h

/-- The normal form keeps a FLOW tail (it changes `*/E` into `[any]` at most). -/
theorem norm_flow {x : AFact} (h : FlowKind x.fact.kind) : FlowKind x.norm.fact.kind := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  rcases h with h | ⟨xs, h⟩
  · have hk : k = .any := h
    subst hk
    exact Or.inl rfl
  · have hk : k = .star (.set xs) := h
    subst hk
    cases m <;> cases d <;> first | exact Or.inr ⟨xs, rfl⟩ | exact Or.inl rfl

theorem norm_flowF {x : AFact} (h : FlowF x) : FlowF x.norm :=
  ⟨by rw [CoreAux.norm_mark]; exact h.1, norm_flow h.2⟩

/-- THE LOCAL STEP. `applyEdge` keeps a FLOW fact if an abstract premise of the edge has a FLOW
    tail, and its target has an abstract mark and a FLOW tail. (A concrete premise mark stops the
    abstract fact at the gate.) -/
theorem applyEdge_flow {c r : AFact} {fr to : PFact} (hc : FlowF c)
    (hm : Exact.absB fr.mark = true → Exact.absB to.mark = true)
    (hfk : Exact.absB fr.mark = true → FlowKind fr.kind)
    (htk : Exact.absB fr.mark = true → FlowKind to.kind)
    (hr : r ∈ (applyEdge c fr to).facts) : FlowF r := by
  obtain ⟨p, k, ap, m, hg, hgate, hmc, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hr
  have hfa : Exact.absB fr.mark = true := Exact.gate_abs hgate hc.1
  apply norm_flowF
  exact ⟨Exact.comp_abs (hm hfa) hc.1 hmc, geo_flow hc.2 (hfk hfa) (htk hfa) hg⟩

#print axioms applyEdge_flow

/-- A micro edge of the program (S7 `markEdgeB`, S8 `PremConc` and `NoUnivE`, and
    `ExactTargetConc`) keeps a FLOW fact. -/
theorem micro_flow {c r : AFact} {e : MicroEdge}
    (hmk : Exact.markEdgeB e.1.mark e.2.mark = true) (hpc : Invariant.PremConc e)
    (hnu : Invariant.NoUnivE e) (het : e.2.kind = .exact → ∃ t, e.1.mark = .conc t)
    (hc : FlowF c) (hr : r ∈ (applyEdge c e.1 e.2).facts) : FlowF r := by
  refine applyEdge_flow hc (Exact.markEdge_abs hmk) (fun ha => ?_) (fun ha => ?_) hr
  · refine flowKind_of_ne (fun hk => ?_) hnu.1
    obtain ⟨t, ht⟩ := hpc hk
    exact not_abs_of_conc ht ha
  · refine flowKind_of_ne (fun hk => ?_) hnu.2
    obtain ⟨t, ht⟩ := het hk
    exact not_abs_of_conc ht ha

/-- A summary `j → g` keeps a FLOW fact if an abstract premise `j` has a FLOW tail and then `g` is
    a FLOW conclusion (the closure invariant of the callee). -/
theorem applySummary_flow {a r g : AFact} {j : PFact} (ha : FlowF a)
    (hj : Exact.absB j.mark = true → FlowKind j.kind)
    (hg : Exact.absB j.mark = true → FlowF g)
    (hr : r ∈ (applySummary a j g).facts) : FlowF r := by
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
  have hxf := applyEdge_flow ha (fun h => (hg h).1) hj (fun h => (hg h).2) hx
  exact norm_flowF (x := ⟨x.fact, x.demand || g.demand⟩) hxf

theorem limitF_flow {counted : Acc → Bool} {L : Nat} {f : AFact} (h : FlowF f) :
    FlowF (limitF counted L f) := by
  refine ⟨by rw [limitF_mark]; exact h.1, ?_⟩
  rcases Invariant.limitF_cases counted L f with e | ⟨hk, _⟩
  · rw [e]; exact h.2
  · rw [hk]; exact Or.inl rfl

theorem transfer_flow {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hs : ∀ e, e ∈ s.edges → Exact.markEdgeB e.1.mark e.2.mark = true ∧ Invariant.PremConc e ∧
      Invariant.NoUnivE e ∧ (e.2.kind = .exact → ∃ t, e.1.mark = .conc t))
    (hc : FlowF c) (hr : r ∈ (transfer counted L s c).facts) : FlowF r := by
  rcases Invariant.transfer_mem hr with rfl | ⟨x, e, he, hx, rfl⟩
  · exact hc
  · obtain ⟨h1, h2, h3, h4⟩ := hs e he
    exact limitF_flow (micro_flow h1 h2 h3 h4 hc hx)

theorem cleanRes_flow {cl : Cleaner} {c f : AFact} (hc : FlowF c)
    (h : f ∈ (cleanRes cl c).facts) : FlowF f := by
  rcases Invariant.cleanRes_facts_cases h with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨⟨t, ht⟩, _⟩
  · exact hc
  · exact ⟨Exact.addEx_abs t hc.1, hc.2⟩
  · exact norm_flowF (x := ⟨c.fact, true⟩) hc
  · exact (not_abs_of_conc ht hc.1).elim

theorem startFact_flow {i : PFact} (hi : InitK i) (ha : Exact.absB i.mark = true) :
    FlowF (startFact i) := by
  refine ⟨by rw [startFact_mark]; exact ha, ?_⟩
  obtain ⟨b, p, k, m⟩ := i
  rcases hi.2 ha with h | ⟨xs, h⟩
  · have hk : k = .any := h
    subst hk
    cases m <;> exact Or.inl rfl
  · have hk : k = .star (.set xs) := h
    subst hk
    cases m <;> first | exact Or.inr ⟨xs, rfl⟩ | exact Or.inl rfl

/-! ## 3. The closure invariant of run 1 -/

section Run1
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The motive: every initial fact satisfies `InitK`; an edge with an abstract premise has a FLOW
    conclusion. `True` for the other objects. -/
def KInv : Obj → Prop
  | .init _ i => InitK i
  | .edge _ i _ f => InitK i ∧ (Exact.absB i.mark = true → FlowF f)
  | _ => True

/-- THE KINDS INVARIANT of run 1 (one induction on `D`). Hypotheses: S7 (`MarkWF`), S8
    (`PremConc`, `NoUnivE` on every micro edge), `ExactTargetConc`, and `InitK` for the
    abstraction. -/
theorem kInv_all (hmw : Exact.MarkWF P) (het : ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (hα : ∀ m a, InitK (α m a)) {o : Obj} (h : D P counted L α sinks roots o) : KInv o := by
  induction h with
  | root => exact initK_conc (t := zeroMark) rfl
  | start _ ih => exact ⟨ih, fun ha => startFact_flow ih ha⟩
  | @step M i n f n' s f' _ hE hf ih =>
    refine ⟨ih.1, fun ha => transfer_flow (fun e he => ?_) (ih.2 ha) hf⟩
    exact ⟨hmw.stmt _ _ _ _ hE e he, hA.1 _ _ _ _ hE e he, hB.1 _ _ _ _ hE e he,
      het.1 _ _ _ _ hE e he⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => exact hα _ _
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha1 _ _ _ hr he2 hr' ihF ihJ ihG =>
    refine ⟨ihF.1, fun ha => limitF_flow ?_⟩
    have hA1 := micro_flow (hmw.toC _ _ _ _ hE e1 he1) (hA.2.1 _ _ _ _ hE e1 he1)
      (hB.2.1 _ _ _ _ hE e1 he1) (het.2.1 _ _ _ _ hE e1 he1) (ihF.2 ha) ha1
    have hR := applySummary_flow hA1 ihJ.2 ihG.2 hr
    exact micro_flow (hmw.fromC _ _ _ _ hE e2 he2) (hA.2.2 _ _ _ _ hE e2 he2)
      (hB.2.2 _ _ _ _ hE e2 he2) (het.2.2 _ _ _ _ hE e2 he2) hR hr'
  | reqSink => trivial
  | answer => exact initK_conc answerInit_mark
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact ⟨ih.1, fun ha => cleanRes_flow (ih.2 ha) hf⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms kInv_all

/-! ## 4. The theorems of run 1 -/

/-- The empty validity: `Exact.FiltOK` holds for it. The mark part of `Exact.D_edgeOK` needs no
    filter condition, and this validity gives it with no hypothesis. -/
theorem filtOK_false (P : Program) : Exact.FiltOK P (fun _ => False) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hok _ => hok.elim

theorem backOK_false (P : Program) : Exact.BackOK P (fun _ => False) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hok => hok.elim, fun _ _ _ _ _ _ _ _ _ _ hok => hok.elim,
    fun _ _ _ _ _ _ _ _ _ _ hok => hok.elim⟩

/-- K1 (FLOW IS ABSTRACT; ap.md §7.2 FLOW, S7). An edge whose premise has the mark `*` has an
    abstract conclusion mark (`*` or `*∖x`). The only hypothesis is S7 (`MarkWF`); the abstraction
    is free. Necessary: `CexK.cex_markWF`. -/
theorem flow_abstract (hmw : Exact.MarkWF P) {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    Invariant.AbsMark f.fact.mark :=
  absB_iff.mp ((Exact.D_edgeOK hmw (filtOK_false P) (backOK_false P) h).1 (by rw [hi]; rfl))

#print axioms flow_abstract

/-- K2 (FLOW HAS NO `$` LEAF; ap.md §7.2 FLOW, S7, S8), for every abstraction that satisfies
    `InitK`. An edge whose premise has the mark `*` has an abstract conclusion mark and no `$`
    tail (and no `*/Universe` tail). Necessary: `CexK.cex_etc` (`ExactTargetConc`),
    `CexK.cex_premConc` (`PremConc`), `CexK.cex_noUniv` (`NoUnivE`), `CexK.cex_alpha` (`InitK`),
    and `CexK.cex_markWF` (`MarkWF`, through K1). -/
theorem flow_no_exact_gen (hmw : Exact.MarkWF P) (het : ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (hα : ∀ m a, InitK (α m a)) {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    Invariant.AbsMark f.fact.mark ∧ f.fact.kind ≠ .exact ∧ f.fact.kind ≠ .star .univ := by
  have hf := (kInv_all P counted L α sinks roots hmw het hA hB hα h).2 (by rw [hi]; rfl)
  exact ⟨absB_iff.mp hf.1, flowKind_ne hf.2⟩

#print axioms flow_no_exact_gen

/-- K2 for run 1 (`policy1`). -/
theorem flow_no_exact (hmw : Exact.MarkWF P) (het : ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L policy1 sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    Invariant.AbsMark f.fact.mark ∧ f.fact.kind ≠ .exact :=
  let h2 := flow_no_exact_gen P counted L policy1 sinks roots hmw het hA hB policy1_initK h hi
  ⟨h2.1, h2.2.1⟩

#print axioms flow_no_exact

/-- K3 (TAINT IS CONCRETE; ap.md §7.2 TAINT, `Coverage.edge_conc`, W2). An edge whose premise has
    a concrete mark, or is the zero fact, has a concrete conclusion mark and no `*` tail. No
    hypothesis; every abstraction. -/
theorem taint_concrete {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f))
    (hi : (∃ t, i.mark = .conc t) ∨ i = zeroFact) :
    (∃ t, f.fact.mark = .conc t) ∧ f.fact.kind.isStar = false := by
  have hc : ∃ t, i.mark = .conc t := by
    rcases hi with h1 | rfl
    · exact h1
    · exact ⟨zeroMark, rfl⟩
  obtain ⟨t, ht⟩ := hc
  obtain ⟨t', ht'⟩ := Coverage.edge_conc P counted L α sinks roots h ht
  refine ⟨⟨t', ht'⟩, ?_⟩
  cases hk : f.fact.kind with
  | star e =>
    exact absurd ht' ((Invariant.final_star_legal P counted L α sinks roots h hk).1.not_conc t')
  | any => rfl
  | exact => rfl

#print axioms taint_concrete

/-- THE PARTITION OF RUN 1 (ap.md §7.2 with §2.3 W2). For every edge of run 1:
    * the premise mark is `*` (FLOW) or concrete (TAINT; REACH is the zero-to-zero case);
    * a `*` premise gives an abstract conclusion mark and no `$` tail (K1, K2);
    * a concrete premise gives a concrete conclusion mark and no `*` tail (K3);
    * a `*` tail has an abstract mark and is normal (W2, `Invariant.final_star_legal`).
    Hypotheses: S7 (`MarkWF`), S8 (`PremConc`, `NoUnivE`) and `ExactTargetConc`. -/
theorem kinds_D (hmw : Exact.MarkWF P) (het : ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L policy1 sinks roots (.edge M i n f)) :
    (i.mark = .star ∨ ∃ t, i.mark = .conc t) ∧
    (i.mark = .star → Invariant.AbsMark f.fact.mark ∧ f.fact.kind ≠ .exact) ∧
    (∀ t, i.mark = .conc t → (∃ t', f.fact.mark = .conc t') ∧ f.fact.kind.isStar = false) ∧
    (∀ e, f.fact.kind = .star e → Invariant.AbsMark f.fact.mark ∧ f.demand = false) :=
  ⟨(kInv_all P counted L policy1 sinks roots hmw het hA hB policy1_initK h).1.1,
   flow_no_exact P counted L sinks roots hmw het hA hB h,
   fun t ht => taint_concrete P counted L policy1 sinks roots h (Or.inl ⟨t, ht⟩),
   fun _ hk => Invariant.final_star_legal P counted L policy1 sinks roots h hk⟩

#print axioms kinds_D

/-- The leaves of a FLOW edge (ap.md §7.2): a normal `*/E` leaf (`E` not Universe) or an `[any]`
    leaf. (The model has no W6, so the layer of an `[any]` leaf is free, §11.2.) -/
theorem flow_leaves (hmw : Exact.MarkWF P) (het : ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L policy1 sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    (∃ xs, f.fact.kind = .star (.set xs) ∧ f.demand = false) ∨ f.fact.kind = .any := by
  have hf := (kInv_all P counted L policy1 sinks roots hmw het hA hB policy1_initK h).2
    (by rw [hi]; rfl)
  rcases hf.2 with hk | ⟨xs, hk⟩
  · exact Or.inr hk
  · exact Or.inl ⟨xs, hk, (Invariant.final_star_legal P counted L policy1 sinks roots h hk).2⟩

#print axioms flow_leaves

/-- The leaves of a TAINT edge (ap.md §7.2): `$` or `[any]`. No hypothesis. -/
theorem taint_leaves {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D P counted L α sinks roots (.edge M i n f))
    (hi : (∃ t, i.mark = .conc t) ∨ i = zeroFact) :
    f.fact.kind = .exact ∨ f.fact.kind = .any := by
  have hk := (taint_concrete P counted L α sinks roots h hi).2
  cases hf : f.fact.kind with
  | star e => rw [hf] at hk; cases hk
  | any => exact Or.inr rfl
  | exact => exact Or.inl rfl

#print axioms taint_leaves

end Run1

/-! ## 5. K4: an ND edge is a TAINT edge (ap.md §4.6, §7.1, W7) -/

theorem conjOK_false (Q : ND.NProg) : NDExact.ConjOK Q (fun _ => False) :=
  fun _ _ _ _ _ _ _ _ hok => hok.elim

/-- K4 in `ND.DN`. An edge with two or more premises has concrete members only (the zero fact is a
    concrete member: it can occur, `ZeroMembers.dn_zero_members`), a concrete conclusion mark and
    no `*` tail (W7, `ND.ndConclusion_uncorrelated`). Hypotheses: S10 (`NProg.WF`), S7
    (`MarkWF`), S9 (`LitConc`). The members come from `NDExact.nd_edgeOK` with the empty validity.
    Necessary: `NDExact.CexLit` (`LitConc`, see `CexND.dn_needs_litConc`) and
    `CexND.dn_needs_markWF` (`MarkWF`). -/
theorem nd_taint {X : ND.Ctx} (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hlc : NDExact.LitConc X.Q) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : ND.DN X (.nedge M P n f)) (h2 : 2 ≤ P.length) :
    (∀ i, i ∈ P → ∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false := by
  have hok := NDExact.nd_edgeOK hmw (filtOK_false _) (backOK_false _) hlc (conjOK_false _) h
  obtain ⟨hk, hc⟩ := ND.ndConclusion_uncorrelated hwf h h2
  exact ⟨fun i hi => NDExact.absB_false_conc (hok.2.2.1 h2 i hi), hc, hk⟩

#print axioms nd_taint

/-! ### The zero drop -/

theorem dropZ_cases (P : List PFact) :
    (P.filter (fun i => i != zeroFact) = [] ∧ NDZ.dropZ P = [zeroFact]) ∨
    NDZ.dropZ P = P.filter (fun i => i != zeroFact) := by
  unfold NDZ.dropZ
  cases P.filter (fun i => i != zeroFact) with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons a l => exact Or.inr rfl

/-- A member of `dropZ P` is a member of `P` or the zero fact. -/
theorem dropZ_mem {P : List PFact} {i : PFact} (h : i ∈ NDZ.dropZ P) : i ∈ P ∨ i = zeroFact := by
  rcases dropZ_cases P with ⟨_, he⟩ | he
  · rw [he] at h
    exact Or.inr (List.mem_singleton.mp h)
  · rw [he] at h
    exact Or.inl (List.mem_filter.mp h).1

/-- A `dropZ` list with two or more members has no zero member. -/
theorem dropZ_long {P : List PFact} (h2 : 2 ≤ (NDZ.dropZ P).length) :
    ∀ i, i ∈ NDZ.dropZ P → i ∈ P ∧ i ≠ zeroFact := by
  intro i hi
  rcases dropZ_cases P with ⟨_, he⟩ | he
  · rw [he] at h2
    exact absurd h2 (by decide)
  · rw [he] at hi
    obtain ⟨hP, hz⟩ := List.mem_filter.mp hi
    exact ⟨hP, bne_iff_ne.mp hz⟩

#print axioms dropZ_long

/-! ### The invariant of `DNz` -/

/-- The motive of `DNz`. For an edge: an abstract premise gives an abstract conclusion; an edge
    with two or more premises has no zero member and a concrete conclusion with no `*` tail. For a
    partial match: the call edge exists, the remaining callee premises and the matched caller
    premises are concrete, and the callee conclusion is concrete with no `*` tail. -/
def ZInv (Q : ND.NProg) : ND.NObj → Prop
  | .nedge _ P _ f =>
      (∀ p, p ∈ P → Exact.absB p.mark = true → Exact.absB f.fact.mark = true) ∧
      (2 ≤ P.length → (∀ p, p ∈ P → p ≠ zeroFact) ∧ (∃ t, f.fact.mark = .conc t) ∧
        f.fact.kind.isStar = false)
  | .npart M n c n' rest P g =>
      (M, n, Instr.call c, n') ∈ Q.prog.edges ∧
      (∀ p, p ∈ rest → Exact.absB p.mark = false) ∧
      (∀ p, p ∈ P → Exact.absB p.mark = false) ∧
      (∃ t, g.fact.mark = .conc t) ∧ g.fact.kind.isStar = false
  | _ => True

/-- Members that are concrete or the zero fact stay concrete after `dropZ`. -/
theorem dropZ_conc {P : List PFact} (h : ∀ p, p ∈ P → Exact.absB p.mark = false) :
    ∀ p, p ∈ NDZ.dropZ P → Exact.absB p.mark = false := by
  intro p hp
  rcases dropZ_mem hp with hp | rfl
  · exact h p hp
  · rfl

/-- An abstract premise never gives a concrete conclusion, so the members of a concrete
    conclusion are concrete. -/
theorem members_conc {P : List PFact} {f : AFact} {t : Mark}
    (habs : ∀ p, p ∈ P → Exact.absB p.mark = true → Exact.absB f.fact.mark = true)
    (hf : f.fact.mark = .conc t) : ∀ p, p ∈ P → Exact.absB p.mark = false := by
  intro p hp
  cases hb : Exact.absB p.mark with
  | false => rfl
  | true => exact (not_abs_of_conc hf (habs p hp hb)).elim

/-- THE INVARIANT OF `DNz` (one induction on `DNz`). Hypotheses: S10 (`NProg.WF`), S7 (`MarkWF`),
    S9 (`LitConc`). -/
theorem zInv_all {X : ND.Ctx} (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hlc : NDExact.LitConc X.Q) {o : ND.NObj} (h : NDZ.DNz X o) : ZInv X.Q o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun p hp hab => ?_, fun h2 => absurd h2 (Nat.not_succ_le_self 1)⟩
    rw [List.mem_singleton.mp hp] at hab
    rw [startFact_mark]
    exact hab
  | @step M P n f n' s f' _ hE hf ih =>
    obtain ⟨habs, hnd⟩ := ih
    refine ⟨fun p hp hab => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (habs p hp hab) hf,
      fun h2 => ?_⟩
    obtain ⟨hz, ⟨t1, h1⟩, hk⟩ := hnd h2
    exact ⟨hz, transfer_mark_conc h1 hf, ND.transfer_nonstar h1 hk hf⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M P n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihF _ ihG =>
    obtain ⟨habs, hnd⟩ := ihF
    obtain ⟨habsG, _⟩ := ihG
    refine ⟨fun p hp hab => ?_, fun h2 => ?_⟩
    · have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (habs p hp hab) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := habsG j List.mem_cons_self (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · obtain ⟨hz, ⟨t1, h1⟩, _⟩ := hnd h2
      obtain ⟨t2, h2'⟩ := applyEdge_mark_conc h1 ha
      obtain ⟨t3, h3⟩ := applySummary_mark_conc h2' hr
      obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
      exact ⟨hz, ⟨t4, by rw [limitF_mark]; exact h4⟩,
        ND.limitF_nonstar (ND.applyEdge_nonstar h3 hr')⟩
  | @ndOpen M n c n' Pc g hE _ h2 ih =>
    obtain ⟨habs, hnd⟩ := ih
    obtain ⟨_, ⟨t, ht⟩, hk⟩ := hnd h2
    exact ⟨hE, members_conc habs ht, fun p hp => absurd hp List.not_mem_nil, ⟨t, ht⟩, hk⟩
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ he1 ha happ ihp ihf =>
    obtain ⟨hE, hrest, hPc, hgc, hgk⟩ := ihp
    obtain ⟨habsF, _⟩ := ihf
    obtain ⟨t, hpt⟩ := NDExact.absB_false_conc (hrest p List.mem_cons_self)
    have hat : a.fact.mark = .conc t := applicable_mark happ hpt
    have hfA : Exact.absB f.fact.mark = false := by
      cases hb : Exact.absB f.fact.mark with
      | false => rfl
      | true =>
        exact (not_abs_of_conc hat (Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) hb ha)).elim
    refine ⟨hE, fun q hq => hrest q (List.mem_cons_of_mem _ hq), fun q hq => ?_, hgc, hgk⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact hPc q hq
    · cases hb : Exact.absB q.mark with
      | false => rfl
      | true =>
        have h1 := habsF q hq hb
        rw [hfA] at h1
        cases h1
  | @ndRet M n c n' P g e2 r _ _ hr ih =>
    obtain ⟨_, _, hPc, ⟨t, ht⟩, _⟩ := ih
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht hr
    refine ⟨fun p hp hab => ?_, fun h2 => ⟨fun p hp => (dropZ_long h2 p hp).2,
      ⟨t1, by rw [limitF_mark]; exact h1⟩, ND.limitF_nonstar (ND.applyEdge_nonstar ht hr)⟩⟩
    rw [dropZ_conc hPc p hp] at hab
    cases hab
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M P n f n' cl f' _ hE hf ih =>
    obtain ⟨habs, hnd⟩ := ih
    refine ⟨fun p hp hab => Exact.cleanRes_abs (habs p hp hab) hf, fun h2 => ?_⟩
    obtain ⟨hz, ⟨t1, h1⟩, hk⟩ := hnd h2
    exact ⟨hz, cleanRes_mark_conc h1 hf, ND.cleanRes_nonstar h1 hk hf⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj _ hg1 _ hg2 ih1 ih2 =>
    obtain ⟨habs1, _⟩ := ih1
    obtain ⟨habs2, _⟩ := ih2
    obtain ⟨⟨T1, hT1⟩, ⟨T2, hT2⟩⟩ := hlc _ _ _ _ hcj
    rw [hT1] at hg1
    rw [hT2] at hg2
    -- a concrete literal passes only a concrete input, so every premise is concrete
    have h1 := members_conc habs1 (NDExact.gate_conc_ok hg1)
    have h2 := members_conc habs2 (NDExact.gate_conc_ok hg2)
    have hall : ∀ p, p ∈ P1 ++ P2 → Exact.absB p.mark = false := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact h1 p hp
      · exact h2 p hp
    obtain ⟨hT, hk⟩ := hwf.target _ _ _ _ hcj
    refine ⟨fun p hp hab => ?_, fun hl => ⟨fun p hp => (dropZ_long hl p hp).2, hT, hk⟩⟩
    rw [dropZ_conc hall p hp] at hab
    cases hab
  | reqConj => trivial

#print axioms zInv_all

/-- K4 in `NDZ.DNz` (the closure of the spec, ap.md §4.6, analyzer-core.md §5.4). An edge with two
    or more premises has NO zero member, every member has a concrete mark, and the conclusion has
    a concrete mark and no `*` tail. Hypotheses: S10 (`NProg.WF`), S7 (`MarkWF`), S9 (`LitConc`).
    Necessary: `CexND.dnz_needs_litConc`, `CexND.dnz_needs_markWF`. -/
theorem ndz_taint {X : ND.Ctx} (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hlc : NDExact.LitConc X.Q) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : NDZ.DNz X (.nedge M P n f)) (h2 : 2 ≤ P.length) :
    (∀ i, i ∈ P → i ≠ zeroFact ∧ ∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false := by
  obtain ⟨habs, hnd⟩ := zInv_all hwf hmw hlc h
  obtain ⟨hz, ⟨t, ht⟩, hk⟩ := hnd h2
  exact ⟨fun i hi => ⟨hz i hi, NDExact.absB_false_conc (members_conc habs ht i hi)⟩, ⟨t, ht⟩, hk⟩

#print axioms ndz_taint

/-! ## 6. The restricted runs have no FLOW edge (ap.md §6.3, §7.2) -/

section Restricted
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- A forward restricted run with a mark-copying emission has REACH and TAINT edges only: every
    premise and every conclusion has a concrete mark (`RExact.DR_concrete`), so no premise has the
    mark `*`, and no conclusion has a `*` tail (W2, `RExact.final_star_legalR`). -/
theorem kinds_DR (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f)) :
    i.mark ≠ .star ∧ (∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false := by
  obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := RExact.DR_concrete hem h
  refine ⟨fun hs => (by rw [hs] at ht; cases ht), ⟨t, ht⟩, ⟨t', ht'⟩, ?_⟩
  cases hk : f.fact.kind with
  | star e =>
    exact absurd ht' ((RExact.final_star_legalR P counted L demand emit sat restrict recs sinks
      roots h hk).1.not_conc t')
  | any => rfl
  | exact => rfl

#print axioms kinds_DR

/-- The same for the emission of the spec (`emitM`, §6.3). -/
theorem kinds_DR_emitM {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR P counted L demand emitM sat restrict recs sinks roots (.edge M i n f)) :
    i.mark ≠ .star ∧ (∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false :=
  kinds_DR RExact.emitM_copies h

#print axioms kinds_DR_emitM

/-- The backward run with a mark-copying emission and concrete seeds has no FLOW edge: every
    premise and every conclusion has a concrete mark (`BExact.DB_edge_concrete`). (The tail part
    of TAINT needs S11 (f) on the seeds; it is argued, §11.2.) -/
theorem kinds_DB {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : Backward.DB P counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M i n f)) :
    i.mark ≠ .star ∧ (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t := by
  obtain ⟨⟨t, ht⟩, hf⟩ := BExact.DB_edge_concrete hem hsd h
  exact ⟨fun hs => (by rw [hs] at ht; cases ht), ⟨t, ht⟩, hf⟩

#print axioms kinds_DB

/-- S11 (f) (ap.md S11 (f), `interpreter.md` I11 (f)): every seed pattern (a sink pattern) has the
    tail `$` or `[any]`, never `*`. Necessary for `kinds_DB_taint`: `CexSeedTail.cex_seed_tail`. -/
def SeedTails (seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s, (M, n, s) ∈ seeds → s.kind.isStar = false

/-- A concrete start fact has no `*` tail (W2: a `*` premise with a concrete mark starts as
    `[any]`). -/
theorem startFact_nonstar_conc {i : PFact} {t : Mark} (h : i.mark = .conc t) :
    (startFact i).fact.kind.isStar = false := by
  obtain ⟨b, p, k, m⟩ := i
  have hm : m = .conc t := h
  subst hm
  cases k <;> rfl

/-- A summary applied to a concrete fact gives no `*` tail (the normal form of a concrete fact). -/
theorem applySummary_nonstar {a r g : AFact} {j : PFact} {t : Mark} (ha : a.fact.mark = .conc t)
    (hr : r ∈ (applySummary a j g).facts) : r.fact.kind.isStar = false := by
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
  obtain ⟨t', ht'⟩ := applyEdge_mark_conc ha hx
  exact ND.norm_conc_nonstar (f := ⟨x.fact, x.demand || g.demand⟩) ht'

/-- The tail motive of the backward run: no edge conclusion has a `*` tail. -/
def TInvB : Obj → Prop
  | .edge _ _ _ f => f.fact.kind.isStar = false
  | _ => True

/-- THE TAIL INVARIANT OF THE BACKWARD RUN (one induction on `DB`). Every object is concrete
    (`BExact.DB_concrete`), and a concrete fact keeps no `*` tail through every rule; the rule
    `seed` gives the seed itself, so its tail is the hypothesis `SeedTails`. No condition on the
    reversed program is necessary. -/
theorem tInvB_all {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds) (hst : SeedTails seeds)
    {o : Obj}
    (h : Backward.DB P counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    TInvB o := by
  induction h with
  | @start M i hi _ =>
    obtain ⟨t, ht⟩ := BExact.DB_concrete hem hsd hi
    exact startFact_nonstar_conc ht
  | @step M i n f n' s f' hf _ hf' ih =>
    obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete hem hsd hf
    exact ND.transfer_nonstar ht ih hf'
  | pass _ _ _ ih => exact ih
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf _ _ ha _ _ _ _ _ hr _ hr' _ _ _ =>
    obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete hem hsd hf
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    exact ND.limitF_nonstar (ND.applyEdge_nonstar h2 hr')
  | @retRec M i n f n' c e1 a j g r e2 r' hf _ _ ha _ _ hr _ hr' _ =>
    obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete hem hsd hf
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    exact ND.limitF_nonstar (ND.applyEdge_nonstar h2 hr')
  | @clean M i n f n' cl f' hf _ hf' ih =>
    obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete hem hsd hf
    exact ND.cleanRes_nonstar ht ih hf'
  | filt _ _ _ ih => exact ih
  | zpass => rfl
  | @seed M n s hs _ _ => exact ND.limitF_nonstar (f := ⟨s, false⟩) (hst M n s hs)
  | @zret M n n' c g r e2 r' _ _ _ _ hr _ hr' _ _ =>
    obtain ⟨t2, h2⟩ := applySummary_mark_conc (a := Backward.zeroAF) (t := zeroMark) rfl hr
    exact ND.limitF_nonstar (ND.applyEdge_nonstar h2 hr')
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initR => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial
  | zin => trivial

#print axioms tInvB_all

/-- The backward run has REACH and TAINT edges only: with a mark-copying emission, concrete seeds
    and the seed tails of S11 (f), every premise and every conclusion has a concrete mark, so no
    premise has the mark `*`, and no conclusion has a `*` tail. -/
theorem kinds_DB_taint {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds) (hst : SeedTails seeds)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : Backward.DB P counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M i n f)) :
    i.mark ≠ .star ∧ (∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false :=
  let h1 := kinds_DB hem hsd h
  ⟨h1.1, h1.2.1, h1.2.2, tInvB_all hem hsd hst h⟩

#print axioms kinds_DB_taint

end Restricted

/-! ### `SeedTails` is necessary

  A concrete seed with a `*` tail at the entry of a root: the rule `seed` gives the edge
  `zero → (1,.,*,{},5)`, a `*` leaf with a concrete mark. -/

namespace CexSeedTail

def sStar : PFact := ⟨1, [], .star Excl.empty, .conc 5⟩
def seeds : List (MethodId × Node × PFact) := [(0, 0, sStar)]
def Pb : Program := ⟨fun _ => 0, fun _ => 0, []⟩

/-- WITHOUT `SeedTails`, THE TAIL PART OF `kinds_DB_taint` IS FALSE. The seeds are concrete
    (`SeedsConc`); every other parameter of the run is free (so also the emission `emitM`, which
    copies the mark, `RExact.emitM_copies`). -/
theorem cex_seed_tail (counted : Acc → Bool) (L : Nat) (demand : MethodId → DemandEdge → Prop)
    (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool)
    (restrict : PFact → AFact → DemandEdge → Option AFact) (recs : MethodId → PFact × AFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (zbind : Bool) :
    BExact.SeedsConc seeds ∧ ¬ SeedTails seeds ∧
    Backward.DB Pb counted L demand emit sat restrict recs sinks [0] seeds zbind
      (.edge 0 zeroFact 0 ⟨sStar, false⟩) ∧ sStar.kind.isStar = true ∧ sStar.mark = .conc 5 := by
  refine ⟨fun M n s hs => ?_, fun h => ?_, ?_, rfl, rfl⟩
  · cases hs with
    | head => exact ⟨5, rfl⟩
    | tail _ h => cases h
  · have h1 := h 0 0 sStar (List.Mem.head _)
    cases h1
  · have h1 : Backward.DB Pb counted L demand emit sat restrict recs sinks [0] seeds zbind
        (.init 0 zeroFact) := Backward.DB.root (List.Mem.head _)
    have h2 := Backward.DB.start h1
    have h3 := Backward.DB.seed (s := sStar) (List.Mem.head _) h2
    have e : limitF counted L ⟨sStar, false⟩ = ⟨sStar, false⟩ := rfl
    rw [e] at h3
    exact h3

#print axioms cex_seed_tail

end CexSeedTail

/-! ## 7. The hypotheses are necessary

  First, Boolean checks of the program conditions for an explicit program, with their soundness.
  Then the runs. Every run satisfies `Program.WF` (S10) and every condition of its theorem except
  one, and it derives an edge that breaks the theorem. -/

/-- A Boolean property of every micro edge of one instruction. -/
def instrAllB (φ : MicroEdge → Bool) : Instr → Bool
  | .stmt s => s.edges.all φ
  | .call c => c.toCallee.all φ && c.fromCallee.all φ
  | _ => true

theorem allEdges_of_check {P : Program} {Φ : MicroEdge → Prop} (φ : MicroEdge → Bool)
    (hφ : ∀ e, φ e = true → Φ e) (h : P.edges.all (fun x => instrAllB φ x.2.2.1) = true) :
    Invariant.AllEdges P Φ := by
  have hx : ∀ x, x ∈ P.edges → instrAllB φ x.2.2.1 = true :=
    fun x hx => List.all_eq_true.mp h x hx
  refine ⟨fun M n s n' hm e he => ?_, fun M n c n' hm e he => ?_, fun M n c n' hm e he => ?_⟩
  · have h1 : s.edges.all φ = true := hx _ hm
    exact hφ e (List.all_eq_true.mp h1 e he)
  · have h1 : (c.toCallee.all φ && c.fromCallee.all φ) = true := hx _ hm
    rw [Bool.and_eq_true] at h1
    exact hφ e (List.all_eq_true.mp h1.1 e he)
  · have h1 : (c.toCallee.all φ && c.fromCallee.all φ) = true := hx _ hm
    rw [Bool.and_eq_true] at h1
    exact hφ e (List.all_eq_true.mp h1.2 e he)

/-- The Boolean form of `Invariant.PremConc`. -/
def premConcB (e : MicroEdge) : Bool :=
  match e.1.kind, e.1.mark with
  | .exact, .conc _ => true
  | .exact, _ => false
  | _, _ => true

theorem premConcB_sound (e : MicroEdge) (h : premConcB e = true) : Invariant.PremConc e := by
  intro hk
  obtain ⟨⟨b, p, k, m⟩, t⟩ := e
  have hk' : k = .exact := hk
  subst hk'
  cases m with
  | conc t0 => exact ⟨t0, rfl⟩
  | star => cases h
  | starEx _ => cases h

/-- The Boolean form of the condition of `ExactTargetConc` on one micro edge. -/
def etcB (e : MicroEdge) : Bool :=
  match e.2.kind, e.1.mark with
  | .exact, .conc _ => true
  | .exact, _ => false
  | _, _ => true

theorem etcB_sound (e : MicroEdge) (h : etcB e = true) :
    e.2.kind = .exact → ∃ t, e.1.mark = .conc t := by
  intro hk
  obtain ⟨⟨b, p, k0, m⟩, ⟨b', p', k, m'⟩⟩ := e
  have hk' : k = .exact := hk
  subst hk'
  cases m with
  | conc t0 => exact ⟨t0, rfl⟩
  | star => cases h
  | starEx _ => cases h

def notUnivB : Kind → Bool
  | .star .univ => false
  | _ => true

theorem notUnivB_sound {k : Kind} (h : notUnivB k = true) : k ≠ .star .univ := by
  intro hk
  subst hk
  cases h

/-- The Boolean form of `Invariant.NoUnivE`. -/
def noUnivB (e : MicroEdge) : Bool := notUnivB e.1.kind && notUnivB e.2.kind

theorem noUnivB_sound (e : MicroEdge) (h : noUnivB e = true) : Invariant.NoUnivE e := by
  unfold noUnivB at h
  rw [Bool.and_eq_true] at h
  exact ⟨notUnivB_sound h.1, notUnivB_sound h.2⟩

theorem markWF_of_check {P : Program}
    (h : P.edges.all (fun x => instrAllB (fun e => Exact.markEdgeB e.1.mark e.2.mark) x.2.2.1) =
      true) : Exact.MarkWF P :=
  let hA := allEdges_of_check (Φ := fun e => Exact.markEdgeB e.1.mark e.2.mark = true) _
    (fun _ h => h) h
  ⟨hA.1, hA.2.1, hA.2.2⟩

/-- The Boolean form of `Program.WF` for a program without type filters. -/
def wfB : Instr → Bool
  | .stmt s => s.edges.all (fun e => memB e.1.base s.touched)
  | .call c => c.toCallee.all (fun e => e.1.mark == .star) &&
      c.fromCallee.all (fun e => e.1.mark == .star)
  | .clean _ => true
  | .filt _ _ => false

theorem wf_of_check {P : Program} (h : P.edges.all (fun x => wfB x.2.2.1) = true) : P.WF := by
  have hx : ∀ x, x ∈ P.edges → wfB x.2.2.1 = true := fun x hx => List.all_eq_true.mp h x hx
  refine ⟨fun M n s n' hm e he => ?_, fun M n c n' hm e he => ?_, fun M n c n' hm e he => ?_,
    fun M n b may n' hm => ?_⟩
  · have h1 : s.edges.all (fun e => memB e.1.base s.touched) = true := hx _ hm
    exact List.all_eq_true.mp h1 e he
  · have h1 : (c.toCallee.all (fun e => e.1.mark == .star) &&
        c.fromCallee.all (fun e => e.1.mark == .star)) = true := hx _ hm
    rw [Bool.and_eq_true] at h1
    exact beq_iff_eq.mp (List.all_eq_true.mp h1.1 e he)
  · have h1 : (c.toCallee.all (fun e => e.1.mark == .star) &&
        c.fromCallee.all (fun e => e.1.mark == .star)) = true := hx _ hm
    rw [Bool.and_eq_true] at h1
    exact beq_iff_eq.mp (List.all_eq_true.mp h1.2 e he)
  · have h1 : wfB (Instr.filt b may) = true := hx _ hm
    cases h1

/-! ### Run 1: K1 and K2

  The root `0` binds the zero fact (`0.*`) to the base `1` of the method `1` (a call). The added
  fact is `a0 = (1,.,$,0)`, and `policy1` gives the initial fact `i0 = (1,.,*,{},*)`: a FLOW
  premise. Each run adds instructions to the method `1`. -/

namespace CexK

/-- The binding of the zero base of the root `0` to the base `1` of the method `1`. -/
def bnd : MicroEdge := (⟨0, [], .star Excl.empty, .star⟩, ⟨1, [], .star Excl.empty, .star⟩)
def call0 : Call := ⟨1, [0], [bnd], []⟩
/-- The added fact: the zero fact bound to the base `1`. -/
def a0 : PFact := ⟨1, [], .exact, .conc 0⟩
/-- The run-1 initial fact of the method `1`. -/
def i0 : PFact := ⟨1, [], .star Excl.empty, .star⟩
/-- The root `0` calls the method `1`; `rest` are the instructions of the method `1`. -/
def prog (rest : List (MethodId × Node × Instr × Node)) : Program :=
  ⟨fun _ => 0, fun _ => 9, (0, 0, .call call0, 1) :: rest⟩

theorem policy1_a0 : policy1 1 a0 = i0 := by decide

/-- The common start of every run: the start edge of the initial fact `α 1 a0` of the method
    `1`. -/
theorem run_start (rest : List (MethodId × Node × Instr × Node)) (counted : Acc → Bool) (L : Nat)
    (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) :
    D (prog rest) counted L α sinks [0] (.edge 1 (α 1 a0) 0 (startFact (α 1 a0))) := by
  have h1 : D (prog rest) counted L α sinks [0] (.init 0 zeroFact) := D.root (List.Mem.head _)
  have h2 := D.start h1
  have ha : (⟨a0, false⟩ : AFact) ∈ (applyEdge (startFact zeroFact) bnd.1 bnd.2).facts := by
    decide
  have h3 : D (prog rest) counted L α sinks [0] (.added call0.callee a0) :=
    D.added (n' := 1) (e := bnd) (a := ⟨a0, false⟩) h2 (List.Mem.head _) (List.Mem.head _) ha
  have h4 : D (prog rest) counted L α sinks [0] (.init 1 (α 1 a0)) := D.initA h3
  exact D.start h4

theorem run_i0 (rest : List (MethodId × Node × Instr × Node)) (counted : Acc → Bool) (L : Nat)
    (sinks : List (MethodId × Node × PFact)) :
    D (prog rest) counted L policy1 sinks [0] (.edge 1 i0 0 ⟨i0, false⟩) := by
  have h := run_start rest counted L policy1 sinks
  rw [policy1_a0] at h
  exact h

/-- `ExactTargetConc`: the statement `2 := 1` with a `$` target and the premise mark `*`. -/
def sE : Stmt := ⟨[1], [(i0, ⟨2, [], .exact, .star⟩)]⟩
def progE : Program := prog [(1, 0, .stmt sE, 1)]

/-- WITHOUT `ExactTargetConc`, K2 IS FALSE. The program satisfies S10, S7 and S8; run 1 derives
    the normal edge `i0 → (2,.,$,*)`: a `*` premise with a `$` conclusion and an abstract mark. -/
theorem cex_etc (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progE.WF ∧ Exact.MarkWF progE ∧ Invariant.AllEdges progE Invariant.PremConc ∧
    Invariant.AllEdges progE Invariant.NoUnivE ∧ ¬ ExactTargetConc progE ∧
    D progE counted L policy1 sinks [0] (.edge 1 i0 1 ⟨⟨2, [], .exact, .star⟩, false⟩) ∧
    i0.mark = .star := by
  refine ⟨wf_of_check (by decide), markWF_of_check (by decide),
    allEdges_of_check premConcB premConcB_sound (by decide),
    allEdges_of_check noUnivB noUnivB_sound (by decide), fun h => ?_, ?_, rfl⟩
  · obtain ⟨t, ht⟩ :=
      h.1 1 0 sE 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _) rfl
    cases ht
  · have ht : (transfer counted L sE ⟨i0, false⟩).facts = [⟨⟨2, [], .exact, .star⟩, false⟩] := rfl
    exact D.step (s := sE) (run_i0 _ counted L sinks) (List.Mem.tail _ (List.Mem.head _))
      (by rw [ht]; exact List.Mem.head _)

#print axioms cex_etc

/-- `PremConc`: `1.[any] := 1` makes an `[any]` fact with the mark `*`; then a `$` premise with
    the mark `*` and a `*` target. -/
def s1A : Stmt := ⟨[1], [(i0, ⟨1, [], .any, .star⟩)]⟩
def s2P : Stmt := ⟨[1], [(⟨1, [], .exact, .star⟩, ⟨2, [], .star Excl.empty, .star⟩)]⟩
def progP : Program := prog [(1, 0, .stmt s1A, 1), (1, 1, .stmt s2P, 2)]

/-- WITHOUT `PremConc` (S8), K2 IS FALSE: the `[any]` fact meets the `$` premise, and the
    exclusion of the result is Universe, so the result is `$` with the mark `*`. -/
theorem cex_premConc (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progP.WF ∧ Exact.MarkWF progP ∧ ExactTargetConc progP ∧
    Invariant.AllEdges progP Invariant.NoUnivE ∧ ¬ Invariant.AllEdges progP Invariant.PremConc ∧
    D progP counted L policy1 sinks [0] (.edge 1 i0 2 ⟨⟨2, [], .exact, .star⟩, false⟩) := by
  refine ⟨wf_of_check (by decide), markWF_of_check (by decide),
    allEdges_of_check etcB etcB_sound (by decide),
    allEdges_of_check noUnivB noUnivB_sound (by decide), fun h => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := h.1 1 1 s2P 2 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) _
      (List.Mem.head _) rfl
    cases ht
  · have ht1 : (transfer counted L s1A ⟨i0, false⟩).facts = [⟨⟨1, [], .any, .star⟩, false⟩] := rfl
    have ht2 : (transfer counted L s2P ⟨⟨1, [], .any, .star⟩, false⟩).facts =
        [⟨⟨2, [], .exact, .star⟩, false⟩] := rfl
    have h1 : D progP counted L policy1 sinks [0] (.edge 1 i0 1 ⟨⟨1, [], .any, .star⟩, false⟩) :=
      D.step (s := s1A) (run_i0 _ counted L sinks) (List.Mem.tail _ (List.Mem.head _))
        (by rw [ht1]; exact List.Mem.head _)
    exact D.step (s := s2P) h1 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (by rw [ht2]; exact List.Mem.head _)

#print axioms cex_premConc

/-- `NoUnivE`: a `*/Universe` target, then a cleaner of all marks that cleans the fact only partly. -/
def sU : Stmt := ⟨[1], [(i0, ⟨2, [], .star .univ, .star⟩)]⟩
def clU : Cleaner := ⟨2, [], .exact, none⟩
def progU : Program := prog [(1, 0, .stmt sU, 1), (1, 1, .clean clU, 2)]

/-- WITHOUT `NoUnivE` (S8), K2 IS FALSE: the cleaner puts the `*/Universe` fact in the demand layer,
    and its normal form is `$` with the mark `*`. -/
theorem cex_noUniv (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progU.WF ∧ Exact.MarkWF progU ∧ ExactTargetConc progU ∧
    Invariant.AllEdges progU Invariant.PremConc ∧ ¬ Invariant.AllEdges progU Invariant.NoUnivE ∧
    D progU counted L policy1 sinks [0] (.edge 1 i0 2 ⟨⟨2, [], .exact, .star⟩, true⟩) := by
  refine ⟨wf_of_check (by decide), markWF_of_check (by decide),
    allEdges_of_check etcB etcB_sound (by decide),
    allEdges_of_check premConcB premConcB_sound (by decide), fun h => ?_, ?_⟩
  · exact (h.1 1 0 sU 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _)).2 rfl
  · have ht : (transfer counted L sU ⟨i0, false⟩).facts =
        [⟨⟨2, [], .star .univ, .star⟩, false⟩] := rfl
    have h1 : D progU counted L policy1 sinks [0]
        (.edge 1 i0 1 ⟨⟨2, [], .star .univ, .star⟩, false⟩) :=
      D.step (s := sU) (run_i0 _ counted L sinks) (List.Mem.tail _ (List.Mem.head _))
        (by rw [ht]; exact List.Mem.head _)
    have hc : (⟨⟨2, [], .exact, .star⟩, true⟩ : AFact) ∈
        (cleanRes clU ⟨⟨2, [], .star .univ, .star⟩, false⟩).facts := by decide
    exact D.clean (cl := clU) h1 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hc

#print axioms cex_noUniv

/-- `MarkWF`: a micro edge with the premise mark `*` and a concrete target mark. -/
def sM : Stmt := ⟨[1], [(i0, ⟨2, [], .any, .conc 9⟩)]⟩
def progM : Program := prog [(1, 0, .stmt sM, 1)]

/-- WITHOUT `MarkWF` (S7), K1 IS FALSE (and so the FLOW kind): a `*` premise gets the concrete
    conclusion mark `9`. -/
theorem cex_markWF (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progM.WF ∧ ExactTargetConc progM ∧ Invariant.AllEdges progM Invariant.PremConc ∧
    Invariant.AllEdges progM Invariant.NoUnivE ∧ ¬ Exact.MarkWF progM ∧
    D progM counted L policy1 sinks [0] (.edge 1 i0 1 ⟨⟨2, [], .any, .conc 9⟩, false⟩) ∧
    ¬ Invariant.AbsMark (.conc 9) := by
  refine ⟨wf_of_check (by decide), allEdges_of_check etcB etcB_sound (by decide),
    allEdges_of_check premConcB premConcB_sound (by decide),
    allEdges_of_check noUnivB noUnivB_sound (by decide), fun h => ?_, ?_,
    fun h => absurd (absB_iff.mpr h) (by decide)⟩
  · have h1 := h.stmt 1 0 sM 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _)
    cases h1
  · have ht : (transfer counted L sM ⟨i0, false⟩).facts = [⟨⟨2, [], .any, .conc 9⟩, false⟩] := rfl
    exact D.step (s := sM) (run_i0 _ counted L sinks) (List.Mem.tail _ (List.Mem.head _))
      (by rw [ht]; exact List.Mem.head _)

#print axioms cex_markWF

/-- `InitK`: an abstraction that gives the premise `(1,.,$,*)`. -/
def iE : PFact := ⟨1, [], .exact, .star⟩
def progA : Program := prog []

/-- WITHOUT `InitK`, K2 IS FALSE (`flow_no_exact_gen`): the start edge of a `$` premise with the
    mark `*` is `$`. Every program condition holds. -/
theorem cex_alpha (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progA.WF ∧ Exact.MarkWF progA ∧ ExactTargetConc progA ∧
    Invariant.AllEdges progA Invariant.PremConc ∧ Invariant.AllEdges progA Invariant.NoUnivE ∧
    ¬ (∀ m a, InitK ((fun _ _ => iE : MethodId → PFact → PFact) m a)) ∧
    D progA counted L (fun _ _ => iE) sinks [0] (.edge 1 iE 0 ⟨iE, false⟩) := by
  refine ⟨wf_of_check (by decide), markWF_of_check (by decide),
    allEdges_of_check etcB etcB_sound (by decide),
    allEdges_of_check premConcB premConcB_sound (by decide),
    allEdges_of_check noUnivB noUnivB_sound (by decide), fun h => ?_,
    run_start [] counted L (fun _ _ => iE) sinks⟩
  rcases (h 0 a0).2 rfl with hk | ⟨xs, hk⟩ <;> cases hk

#print axioms cex_alpha

end CexK

/-! ### K4: `LitConc` and `MarkWF` are necessary, in `DN` and in `DNz`

  `NDExact.CexLit`: an ABSTRACT literal (`1.[any]` with the mark `*`) passes the abstract fact,
  and the conjunction has the premises `[ic, ic]` with the mark `*`. `CexND` below: concrete
  literals, but a micro edge with the premise mark `*` and the target mark `7` (no `MarkWF`) makes
  a concrete input from the abstract premise `ic`. -/

namespace CexND
open ND

/-- `LitConc` is necessary in `DN` (`NDExact.CexLit`). -/
theorem dn_needs_litConc :
    NDExact.CexLit.X.Q.WF ∧ Exact.MarkWF NDExact.CexLit.X.Q.prog ∧
    ¬ NDExact.LitConc NDExact.CexLit.X.Q ∧
    DN NDExact.CexLit.X (.nedge 0 [NDExact.CexLit.ic, NDExact.CexLit.ic] 2
      (conjFact NDExact.CexLit.cj NDExact.CexLit.c1 NDExact.CexLit.c1)) ∧
    NDExact.CexLit.ic.mark = .star :=
  ⟨NDExact.CexLit.wf, NDExact.CexLit.markWF, NDExact.CexLit.not_litConc, NDExact.CexLit.d_edge,
    rfl⟩

#print axioms dn_needs_litConc

/-- The same run in `DNz`. -/
theorem dnz_needs_litConc :
    NDExact.CexLit.X.Q.WF ∧ Exact.MarkWF NDExact.CexLit.X.Q.prog ∧
    ¬ NDExact.LitConc NDExact.CexLit.X.Q ∧
    NDZ.DNz NDExact.CexLit.X (.nedge 0 [NDExact.CexLit.ic, NDExact.CexLit.ic] 2
      (conjFact NDExact.CexLit.cj NDExact.CexLit.c1 NDExact.CexLit.c1)) ∧
    NDExact.CexLit.ic.mark = .star := by
  refine ⟨NDExact.CexLit.wf, NDExact.CexLit.markWF, NDExact.CexLit.not_litConc, ?_, rfl⟩
  have h0 : NDZ.DNz NDExact.CexLit.X (.ninit 1 zeroFact) := NDZ.DNz.root List.mem_cons_self
  have h1 := NDZ.DNz.start h0
  have h2 : NDZ.DNz NDExact.CexLit.X (.nadded 0 ⟨1, [], .exact, .conc 0⟩) :=
    NDZ.DNz.added (a := ⟨⟨1, [], .exact, .conc 0⟩, false⟩) h1 List.mem_cons_self
      List.mem_cons_self (by decide)
  have h3 := NDZ.DNz.initA h2
  have e : NDExact.CexLit.X.α 0 ⟨1, [], .exact, .conc 0⟩ = NDExact.CexLit.ic := by decide
  rw [e] at h3
  have h4 := NDZ.DNz.start h3
  have h5 : NDZ.DNz NDExact.CexLit.X (.nedge 0 [NDExact.CexLit.ic] 1 NDExact.CexLit.c1) :=
    NDZ.DNz.clean h4 (List.Mem.tail _ List.mem_cons_self) (by decide)
  have h6 := NDZ.DNz.conj h5 h5 List.mem_cons_self (by decide) rfl (by decide) rfl
  have e2 : NDZ.dropZ ([NDExact.CexLit.ic] ++ [NDExact.CexLit.ic]) =
      [NDExact.CexLit.ic, NDExact.CexLit.ic] := by decide
  rw [e2] at h6
  exact h6

#print axioms dnz_needs_litConc

/-- A source with the premise mark `*` and the target mark `7` (no `MarkWF`). -/
def sM : Stmt := ⟨[1], [(⟨1, [], .star Excl.empty, .star⟩, ⟨3, [], .exact, .conc 7⟩)]⟩
def lit : PFact := ⟨3, [], .exact, .conc 7⟩
def tgt : PFact := ⟨4, [], .exact, .conc 8⟩
def cj : Conj := ⟨lit, lit, tgt⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 2, [(1, 0, .call NDExact.CexLit.cc, 1), (0, 0, .stmt sM, 1)]⟩
def Q : NProg := ⟨prog, [(0, 1, cj, 2)]⟩
def X : Ctx := ⟨Q, fun _ => true, 3, policy (fun _ => []), [], [1]⟩
def c1 : AFact := ⟨lit, false⟩

theorem wf : X.Q.WF :=
  ⟨wf_of_check (by decide), fun M n cj' n' hE => by
    cases hE with
    | head => exact ⟨⟨8, rfl⟩, rfl⟩
    | tail _ h => cases h⟩

theorem litConc : NDExact.LitConc X.Q := by
  intro M n cj' n' hE
  cases hE with
  | head => exact ⟨⟨7, rfl⟩, ⟨7, rfl⟩⟩
  | tail _ h => cases h

theorem not_markWF : ¬ Exact.MarkWF X.Q.prog := by
  intro h
  have h1 := h.stmt 0 0 sM 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _)
  cases h1

/-- `MarkWF` is necessary in `DN`: the ND edge `[ic, ic] → (4,.,$,8)` has members with the mark
    `*`. -/
theorem dn_needs_markWF :
    X.Q.WF ∧ NDExact.LitConc X.Q ∧ ¬ Exact.MarkWF X.Q.prog ∧
    DN X (.nedge 0 [NDExact.CexLit.ic, NDExact.CexLit.ic] 2 (conjFact cj c1 c1)) ∧
    NDExact.CexLit.ic.mark = .star := by
  refine ⟨wf, litConc, not_markWF, ?_, rfl⟩
  have h0 : DN X (.ninit 1 zeroFact) := DN.root List.mem_cons_self
  have h1 := DN.start h0
  have h2 : DN X (.nadded 0 ⟨1, [], .exact, .conc 0⟩) :=
    DN.added (a := ⟨⟨1, [], .exact, .conc 0⟩, false⟩) h1 List.mem_cons_self List.mem_cons_self
      (by decide)
  have h3 := DN.initA h2
  have e : X.α 0 ⟨1, [], .exact, .conc 0⟩ = NDExact.CexLit.ic := by decide
  rw [e] at h3
  have h4 := DN.start h3
  have h5 : DN X (.nedge 0 [NDExact.CexLit.ic] 1 c1) :=
    DN.step h4 (List.Mem.tail _ List.mem_cons_self) (by decide)
  exact DN.conj h5 h5 List.mem_cons_self (by decide) rfl (by decide) rfl

#print axioms dn_needs_markWF

/-- `MarkWF` is necessary in `DNz`: the same run. -/
theorem dnz_needs_markWF :
    X.Q.WF ∧ NDExact.LitConc X.Q ∧ ¬ Exact.MarkWF X.Q.prog ∧
    NDZ.DNz X (.nedge 0 [NDExact.CexLit.ic, NDExact.CexLit.ic] 2 (conjFact cj c1 c1)) ∧
    NDExact.CexLit.ic.mark = .star := by
  refine ⟨wf, litConc, not_markWF, ?_, rfl⟩
  have h0 : NDZ.DNz X (.ninit 1 zeroFact) := NDZ.DNz.root List.mem_cons_self
  have h1 := NDZ.DNz.start h0
  have h2 : NDZ.DNz X (.nadded 0 ⟨1, [], .exact, .conc 0⟩) :=
    NDZ.DNz.added (a := ⟨⟨1, [], .exact, .conc 0⟩, false⟩) h1 List.mem_cons_self
      List.mem_cons_self (by decide)
  have h3 := NDZ.DNz.initA h2
  have e : X.α 0 ⟨1, [], .exact, .conc 0⟩ = NDExact.CexLit.ic := by decide
  rw [e] at h3
  have h4 := NDZ.DNz.start h3
  have h5 : NDZ.DNz X (.nedge 0 [NDExact.CexLit.ic] 1 c1) :=
    NDZ.DNz.step h4 (List.Mem.tail _ List.mem_cons_self) (by decide)
  have h6 := NDZ.DNz.conj h5 h5 List.mem_cons_self (by decide) rfl (by decide) rfl
  have e2 : NDZ.dropZ ([NDExact.CexLit.ic] ++ [NDExact.CexLit.ic]) =
      [NDExact.CexLit.ic, NDExact.CexLit.ic] := by decide
  rw [e2] at h6
  exact h6

#print axioms dnz_needs_markWF

end CexND

/-! ### Zero members: `DN` keeps them, `DNz` drops them

  The `NDRule` sample `ND.Example` (`$A = src(); $B = src(); $C = pass($A, $B)`): both inputs of the
  conjunction are zero-premise edges. In `DN` the result has the premise list `[zero, zero]`: two
  members, both the zero fact (`nd_taint` allows it: the zero fact has a concrete mark). In `DNz`
  the result has the premise set `{zero}`: a zero-to-fact (TAINT) edge, not an ND edge. -/

namespace ZeroMembers
open ND ND.Example

theorem dn_zero_members :
    DN ND.Example.X (.nedge 0 [zeroFact, zeroFact] 3 (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩)) :=
  ND.Example.c3

#print axioms dn_zero_members

theorem dnz_zero_members :
    NDZ.DNz ND.Example.X (.nedge 0 [zeroFact] 3 (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩)) := by
  have z1 : NDZ.DNz ND.Example.X (.nedge 0 [zeroFact] 1 ⟨zeroFact, false⟩) :=
    NDZ.DNz.step (NDZ.DNz.start (NDZ.DNz.root List.mem_cons_self)) List.mem_cons_self (by decide)
  have a1 : NDZ.DNz ND.Example.X (.nedge 0 [zeroFact] 1 ⟨zA, false⟩) :=
    NDZ.DNz.step (NDZ.DNz.start (NDZ.DNz.root List.mem_cons_self)) List.mem_cons_self (by decide)
  have a2 : NDZ.DNz ND.Example.X (.nedge 0 [zeroFact] 2 ⟨zA, false⟩) :=
    NDZ.DNz.step a1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
  have b2 : NDZ.DNz ND.Example.X (.nedge 0 [zeroFact] 2 ⟨zB, false⟩) :=
    NDZ.DNz.step z1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
  have h := NDZ.DNz.conj a2 b2 List.mem_cons_self (by decide) rfl (by decide) rfl
  have e : NDZ.dropZ ([zeroFact] ++ [zeroFact]) = [zeroFact] := by decide
  rw [e] at h
  exact h

#print axioms dnz_zero_members

end ZeroMembers

end ApSpec.Kinds
