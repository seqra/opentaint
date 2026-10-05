/-
  ApSpec.RestrictedExact — the PRECISION side of a restricted run (`DR`).

  `Exact.lean` proves that a normal-layer edge of the closure `D` denotes only real
  flows. This module proves the same for the restricted closure `DR` of
  `Restricted.lean`. The rules `initR`, `ret` (restricted) and `retRec` (persisted
  records) are new. Exactness is relative to the initial fact, so `emit` needs no
  hypothesis. These hypotheses are necessary:
    * `Exact.MarkWF P`, and `Exact.FiltUp P` or the valid form (`Exact.FiltValid P ok`,
      `Exact.BackOK P ok`): the hypotheses of `Exact.edge_exact` (round 5: marks `*∖x`,
      cleaners, type filters; `Exact.CexMark`, `Exact.CexFilt`);
    * `SatMark sat` (round 5): a satisfied premise mark is a sub-mark of the fact mark. A premise
      `*∖x` (from an arbitrary emission or record) passes the mark gate but does not admit the
      marks of `x`. Every table of `Restricted.lean` satisfies it (`satO_mark`, `satI_mark`,
      `satU_mark`, `satS_mark`); `CexSat.cex_sat` shows that it is necessary;
    * `RestrictSub restrict`: the restriction only removes pairs and keeps the layer
      (used in the case `ret`);
    * `RecsExact P recs`: a normal-layer persisted record denotes only real flows
      (used in the case `retRec`). The valid form is `RecsExactV P ok recs`.
  The motive is `EdgeOKR` (the motive `Exact.EdgeOK` for normal-layer edges only): an abstract
  initial mark gives an abstract final mark, and the pairs are real flows. At a summary the
  mark part needs an abstract summary conclusion for an abstract caller fact. For `restrict` it
  follows from `RestrictSub` (`abs_of_sub`); for a record it follows from `RecsExact` and
  `MarkWF` (`recs_abs`: a real flow from a location with a FRESH mark keeps that mark).
  The shape invariants (`Invariant.lean`, `Confirmed.D_NS`) need NO hypothesis: the
  caller fact alone gives the shape of the result of `applySummary`, the summary edge
  does not change it. So no shape hypothesis on `restrict`, `recs` or `emit` is used.

  Main results:
    1. `DR_edgeOK`, `edge_exactR`, `edge_exactR_valid`, `complete_exactR`  a normal-layer edge
       of `DR` denotes only real flows.
    2. `flowR_flow`, `closed_exactR`, `closed_exactR_valid`  a closed initial fact of a
       restricted run: every DEMANDED flow (`FlowR`) has a record, and every record is a real
       `Flow`.
    3. `recs_of_DR`, `recs_of_D` (and `_valid`)  the exit records of a run satisfy `RecsExact`,
       so a later run can reuse them (`recs_union`, `recs_mono` join and filter record sets).
    4. `DR_inv`, `final_star_legalR`, `star_final_keeps_initial_exclR`,
       `star_initial_completeR`, `DR_NS`  the shape invariants of `DR`.
    5. `SupR`, `ConfirmedR`, `sup_entryR`, `confirmed_realR`  a confirmed vulnerability
       of a restricted run is a real vulnerability (no false positive).
    6. `restrictU_sub`, `restrictS_sub`  both concrete restrictions satisfy
       `RestrictSub`; `confirmed_realU`, `confirmed_realS` are the instances.

  Version 4 (`emitM`, `satO`, `restrictU`; version 5 replaced `satO` by `satI`: the generic `*_gen`
  theorems serve both, and `RestrictedMain` instantiates `satI`). One hypothesis:
  `EmitCopiesMark emit` (the emission copies the mark of the added fact; `emitM_copies`).
    7. `DR_concrete`  every initial fact, edge (premise and final fact) and added fact of
       the run has a concrete mark, and the run has no request object. A cleaner on a concrete
       fact gives concrete facts and no request (`cleanRes_mark_conc`,
       `cleanRes_reqs_abstract`). Corollaries:
       `added_concrete` (discharges `EmitContractConc.on`, see `emitContractOn_of_conc`),
       `DR_no_request` (no mark request after the first run), `DR_no_answer_init` (every
       initial fact is the root zero fact or an emission).
    8. `final_not_star`  no final fact has the `*` tail (W2).
       `complete_premise_exact`  a normal-layer edge has an EXACT premise; so its premise
       exclusion is empty (`complete_premEmpty`) and every complete record reverses
       exactly (`complete_rev_exact`).
    9. `restrict_U_iff_S`, `restrict_U_eq_S`  the closure with `restrictU` and the closure
       with `restrictS` are the same predicate.
   10. `SupM`, `ConfirmedM`  the support without requests (the callee initial fact IS the
       exact concrete added fact; `emitM_exact_self` shows that `emitM` gives it).
       `supR_supM`, `confirmedR_M`: the version-3 support is a special case.
       `sup_entryM`, `confirmed_realM_gen` (generic), `confirmed_realM` (spec rules): a
       confirmed vulnerability is a real vulnerability. The valid forms (prefix-closed type
       filters, no `FiltUp`): `sup_entryM_valid`, `confirmed_realM_gen_valid_of`,
       `confirmed_realM_gen_valid`, `confirmed_realM_valid`.

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.Restricted
import ApSpec.Exact
import ApSpec.Invariant
import ApSpec.Confirmed
import ApSpec.Reverse

namespace ApSpec.RExact
open ApSpec

/-! ## 0. The record hypothesis -/

/-- The persisted records are exact: a normal-layer record denotes only real flows
    from the method entry to the method exit. -/
def RecsExact (P : Program) (recs : MethodId → PFact × AFact → Prop) : Prop :=
  ∀ m j g, recs m (j, g) → g.demand = false → ∀ l1 l2, den j g.fact l1 l2 →
    Flow P m l1 (P.exit m) l2

/-- The exit edges of a run, as a record set. -/
def exitRecs (P : Program) (R : Obj → Prop) (m : MethodId) (jg : PFact × AFact) : Prop :=
  R (.edge m jg.1 (P.exit m) jg.2)

/-- A subset of an exact record set is exact. -/
theorem recs_mono {P : Program} {recs recs' : MethodId → PFact × AFact → Prop}
    (hsub : ∀ m jg, recs' m jg → recs m jg) (h : RecsExact P recs) : RecsExact P recs' :=
  fun m j g hr hg l1 l2 hd => h m j g (hsub m (j, g) hr) hg l1 l2 hd

#print axioms recs_mono

/-- The union of two exact record sets is exact. -/
theorem recs_union {P : Program} {recs1 recs2 : MethodId → PFact × AFact → Prop}
    (h1 : RecsExact P recs1) (h2 : RecsExact P recs2) :
    RecsExact P (fun m jg => recs1 m jg ∨ recs2 m jg) := by
  intro m j g hr hg l1 l2 hd
  rcases hr with hr | hr
  · exact h1 m j g hr hg l1 l2 hd
  · exact h2 m j g hr hg l1 l2 hd

#print axioms recs_union

/-- The empty record set is exact (the first restricted run after run 1 can start
    without records). -/
theorem recs_empty (P : Program) : RecsExact P (fun _ _ => False) :=
  fun _ _ _ hr => absurd hr id

#print axioms recs_empty

/-! ## 0'. The satisfaction hypothesis (round 5) -/

/-- A satisfied premise mark is a sub-mark of the fact mark (the first part of
    `SatContract`). -/
def SatMark (sat : PFact → PFact → Bool) : Prop :=
  ∀ j a, sat j a = true → markSubB j.mark a.mark = true

theorem satMark_of_contract {sat : PFact → PFact → Bool} (h : SatContract sat) : SatMark sat :=
  h.1

theorem bool_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> first | rfl | cases h

theorem bool_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> first | rfl | cases h

theorem bool_or_cases {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem satO_mark : SatMark satO := fun _ _ h => bool_and_right h

theorem satI_mark : SatMark satI := fun _ _ h => bool_and_right h

theorem satU_mark : SatMark satU := by
  intro j a h
  rcases bool_or_cases h with h1 | h1
  · exact Exact.applicable_markSub h1
  · exact bool_and_right (bool_and_left h1)

theorem satS_mark : SatMark satS := by
  intro j a h
  rcases bool_or_cases h with h1 | h1
  · exact satU_mark j a h1
  · exact bool_and_right (bool_and_left h1)

#print axioms satU_mark
#print axioms satS_mark

/-! ## 0''. Fresh marks

  A summary conclusion with a concrete mark under an abstract premise is not exact for an
  abstract caller fact (`Exact.cex_concOK`). A summary edge that keeps a subset of the pairs of
  an abstract-to-abstract edge cannot have a concrete conclusion mark: a FRESH initial mark
  (admitted by the premise, not the concrete mark) gives a pair that the subset keeps, and the
  abstract edge keeps the mark (`abs_of_sub`). A real flow from a location with a mark that no
  micro edge of the program reads as a concrete premise mark keeps that mark (`flow_keep`, under
  `MarkWF`); so an exact record with an abstract premise has an abstract conclusion mark
  (`recs_abs`). -/

/-- A mark above every mark of a list. -/
def bigM : List Nat → Nat
  | [] => 0
  | b :: bs => b + bigM bs + 1

theorem memB_bigM : ∀ (y : List Nat) (k : Nat), memB (bigM y + k) y = false
  | [], _ => rfl
  | b :: bs, k => by
    show (Nat.beq (b + bigM bs + 1 + k) b || memB (b + bigM bs + 1 + k) bs) = false
    have h1 : Nat.beq (b + bigM bs + 1 + k) b = false := by
      cases h : Nat.beq (b + bigM bs + 1 + k) b with
      | false => rfl
      | true => have := Nat.eq_of_beq_eq_true h; omega
    have e : b + bigM bs + 1 + k = bigM bs + (b + 1 + k) := by omega
    rw [h1, Bool.false_or, e]
    exact memB_bigM bs _

#print axioms memB_bigM

theorem memB_cons_false {m t : Mark} {z : List Mark} (h : memB m (t :: z) = false) :
    m ≠ t ∧ memB m z = false := by
  have h' : (Nat.beq m t || memB m z) = false := h
  obtain ⟨h1, h2⟩ := Exact.or_eq_false h'
  refine ⟨fun e => ?_, h2⟩
  rw [e, Nat.beq_refl] at h1
  cases h1

/-- An abstract premise mark admits a mark that is not `t` and not in `y`. -/
theorem fresh_mark {jm : MarkA} (hj : Exact.absB jm = true) (t : Mark) (y : List Mark) :
    ∃ m, jm.admits m ∧ m ≠ t ∧ memB m y = false := by
  cases jm with
  | conc s => cases hj
  | star =>
    obtain ⟨h1, h2⟩ := memB_cons_false (memB_bigM (t :: y) 0)
    exact ⟨_, trivial, h1, h2⟩
  | starEx x =>
    obtain ⟨h1, h2⟩ := memB_cons_false (memB_bigM (t :: (y ++ x)) 0)
    rw [Exact.memB_append] at h2
    obtain ⟨h3, h4⟩ := Exact.or_eq_false h2
    exact ⟨_, h4, h1, h3⟩

#print axioms fresh_mark

theorem tailF_nil : ∀ (k : Kind), tailF k [] []
  | .star e => ⟨rfl, Exact.admits_nil e⟩
  | .any => trivial
  | .exact => rfl

/-- The pair at the two paths themselves: every edge has it for every admitted mark. -/
theorem den_nil (j g : PFact) {m : Mark} (hj : j.mark.admits m) (hp : g.mark.passes m) :
    den j g ⟨j.base, j.path, m⟩ ⟨g.base, g.path, g.mark.out m⟩ :=
  ⟨rfl, rfl, hj, rfl, hp, [], [], (List.append_nil _).symm, (List.append_nil _).symm,
    Exact.tailI_nil _, tailF_nil _⟩

theorem out_abs {g : MarkA} (h : Exact.absB g = true) (m : Mark) : g.out m = m := by
  cases g with
  | star => rfl
  | starEx x => rfl
  | conc t => cases h

/-- A subset of the pairs of an edge with an abstract premise mark and an abstract conclusion
    mark has an abstract conclusion mark. -/
theorem abs_of_sub {j g g' : PFact} (hj : Exact.absB j.mark = true) (hg : Exact.absB g.mark = true)
    (hs : ∀ l1 l2, den j g' l1 l2 → den j g l1 l2) : Exact.absB g'.mark = true := by
  cases hm : g'.mark with
  | star => rfl
  | starEx x => rfl
  | conc t =>
    exfalso
    obtain ⟨m, hjm, hmt, -⟩ := fresh_mark hj t []
    have hd := hs _ _ (den_nil j g' hjm (by rw [hm]; trivial))
    have h4 : g'.mark.out m = g.mark.out m := hd.2.2.2.1
    rw [hm, out_abs hg] at h4
    exact hmt h4.symm

#print axioms abs_of_sub

/-- The concrete premise marks of a list of micro edges. -/
def concOf : MarkA → List Mark
  | .conc t => [t]
  | _       => []

def concMarks : List MicroEdge → List Mark
  | []      => []
  | e :: es => concOf e.1.mark ++ concMarks es

/-- The concrete premise marks of the micro edges of an instruction. -/
def instrMarks : Instr → List Mark
  | .stmt s    => concMarks s.edges
  | .call c    => concMarks c.toCallee ++ concMarks c.fromCallee
  | .clean _   => []
  | .filt _ _  => []

/-- The concrete premise marks of all micro edges of a program. -/
def progMarks : List (MethodId × Node × Instr × Node) → List Mark
  | []      => []
  | x :: xs => instrMarks x.2.2.1 ++ progMarks xs

theorem concMarks_mem : ∀ {es : List MicroEdge} {e : MicroEdge} {t : Mark},
    e ∈ es → e.1.mark = .conc t → memB t (concMarks es) = true
  | [], _, _, he, _ => nomatch he
  | e' :: es, e, t, he, ht => by
    show memB t (concOf e'.1.mark ++ concMarks es) = true
    rw [Exact.memB_append]
    cases he with
    | head =>
      have h1 : memB t (concOf (.conc t)) = true := by
        show (Nat.beq t t || false) = true
        rw [Nat.beq_refl]; rfl
      rw [ht, h1, Bool.true_or]
    | tail _ h => rw [concMarks_mem h ht, Bool.or_true]

theorem progMarks_mem : ∀ {xs : List (MethodId × Node × Instr × Node)} {x}, x ∈ xs →
    ∀ {t : Mark}, memB t (instrMarks x.2.2.1) = true → memB t (progMarks xs) = true
  | [], _, hx, _, _ => nomatch hx
  | y :: xs, _, hx, t, ht => by
    show memB t (instrMarks y.2.2.1 ++ progMarks xs) = true
    rw [Exact.memB_append]
    cases hx with
    | head => rw [ht, Bool.true_or]
    | tail _ h => rw [progMarks_mem h ht, Bool.or_true]

/-- A location with a fresh mark is not admitted by a concrete premise mark of the program. -/
theorem edge_fresh {P : Program} {M : MethodId} {n n' : Node} {ins : Instr}
    (hE : (M, n, ins, n') ∈ P.edges) {es : List MicroEdge}
    (hsub : ∀ t, memB t (concMarks es) = true → memB t (instrMarks ins) = true)
    {e : MicroEdge} (he : e ∈ es) {m : Mark} (hf : memB m (progMarks P.edges) = false) :
    ∀ t, e.1.mark = .conc t → m ≠ t := by
  intro t ht hmt
  have h := progMarks_mem hE (hsub t (concMarks_mem he ht))
  rw [← hmt, hf] at h
  cases h

/-- A micro edge with `markEdgeB` keeps a mark that no concrete premise mark admits. -/
theorem den_keep {e : MicroEdge} {l l' : Loc} (he : Exact.markEdgeB e.1.mark e.2.mark = true)
    (hd : den e.1 e.2 l l') (hf : ∀ t, e.1.mark = .conc t → l.mark ≠ t) : l'.mark = l.mark := by
  have hm : l'.mark = e.2.mark.out l.mark := hd.2.2.2.1
  have ha : e.1.mark.admits l.mark := hd.2.2.1
  rw [hm]
  cases h2 : e.2.mark with
  | star => rfl
  | starEx x => rfl
  | conc t' =>
    exfalso
    cases h1 : e.1.mark with
    | star => rw [h1, h2] at he; cases he
    | starEx x => rw [h1, h2] at he; cases he
    | conc s => rw [h1] at ha; exact hf s h1 ha

/-- A real flow from a location with a fresh mark keeps the mark (under `MarkWF`). -/
theorem flow_keep {P : Program} (hmw : Exact.MarkWF P) {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : Flow P M l0 n l) :
    memB l0.mark (progMarks P.edges) = false → l.mark = l0.mark := by
  induction h with
  | start => intro _; rfl
  | @step M l0 n l n' l' s _ hE hs ih =>
    intro hf
    have h1 := ih hf
    rcases hs with ⟨_, rfl⟩ | ⟨e, he, hde⟩
    · exact h1
    · rw [den_keep (hmw.stmt _ _ _ _ hE e he) hde
        (edge_fresh hE (fun _ h => h) he (by rw [h1]; exact hf)), h1]
  | pass _ _ _ ih => exact ih
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ hE he1 hd1 _ he2 hd2 ih1 ih2 =>
    intro hf
    have h1 := ih1 hf
    have hto : ∀ t, memB t (concMarks c.toCallee) = true →
        memB t (instrMarks (Instr.call c)) = true := by
      intro t h
      show memB t (concMarks c.toCallee ++ concMarks c.fromCallee) = true
      rw [Exact.memB_append, h, Bool.true_or]
    have hfrom : ∀ t, memB t (concMarks c.fromCallee) = true →
        memB t (instrMarks (Instr.call c)) = true := by
      intro t h
      show memB t (concMarks c.toCallee ++ concMarks c.fromCallee) = true
      rw [Exact.memB_append, h, Bool.or_true]
    have k1 : l1.mark = l.mark := den_keep (hmw.toC _ _ _ _ hE e1 he1) hd1
      (edge_fresh hE hto he1 (by rw [h1]; exact hf))
    have k2 : l2.mark = l1.mark := ih2 (by rw [k1, h1]; exact hf)
    have k3 : l3.mark = l2.mark := den_keep (hmw.fromC _ _ _ _ hE e2 he2) hd2
      (edge_fresh hE hfrom he2 (by rw [k2, k1, h1]; exact hf))
    rw [k3, k2, k1, h1]
  | clean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih

#print axioms flow_keep

/-- An exact normal-layer record with an abstract premise mark has an abstract conclusion
    mark (under `MarkWF`). -/
theorem recs_abs {P : Program} {recs : MethodId → PFact × AFact → Prop} (hmw : Exact.MarkWF P)
    (hrecs : RecsExact P recs) {m : MethodId} {j : PFact} {g : AFact} (hr : recs m (j, g))
    (hg : g.demand = false) (hj : Exact.absB j.mark = true) : Exact.absB g.fact.mark = true := by
  cases hm : g.fact.mark with
  | star => rfl
  | starEx x => rfl
  | conc t =>
    exfalso
    obtain ⟨m0, hjm, hmt, hfr⟩ := fresh_mark hj t (progMarks P.edges)
    have hfl := hrecs m j g hr hg _ _ (den_nil j g.fact hjm (by rw [hm]; trivial))
    have hk : g.fact.mark.out m0 = m0 := flow_keep hmw hfl hfr
    rw [hm] at hk
    exact hmt hk.symm

#print axioms recs_abs

/-! ## 0'''. The motive and the valid records -/

/-- The motive: `Exact.EdgeOK` for a normal-layer edge. An abstract initial mark gives an
    abstract final mark, and the pairs to valid end locations are real flows from valid start
    locations. `True` for other objects. -/
def EdgeOKR (P : Program) (ok : Loc → Prop) : Obj → Prop
  | .edge M i n f => f.demand = false →
      (Exact.absB i.mark = true → Exact.absB f.fact.mark = true) ∧
      ∀ l0 l, den i f.fact l0 l → ok l → Flow P M l0 n l ∧ ok l0
  | _ => True

/-- The persisted records for valid locations: the motive holds on each record. -/
def RecsExactV (P : Program) (ok : Loc → Prop) (recs : MethodId → PFact × AFact → Prop) : Prop :=
  ∀ m j g, recs m (j, g) → EdgeOKR P ok (.edge m j (P.exit m) g)

/-- Exact records are exact for the trivial validity (under `MarkWF`). -/
theorem RecsExact.toV {P : Program} {recs : MethodId → PFact × AFact → Prop}
    (hmw : Exact.MarkWF P) (h : RecsExact P recs) : RecsExactV P (fun _ => True) recs :=
  fun _ j g hr hg => ⟨recs_abs hmw h hr hg, fun l1 l2 hd _ => ⟨h _ j g hr hg l1 l2 hd, trivial⟩⟩

#print axioms RecsExact.toV

/-- The common part of the rules `ret` and `retRec`: the motive on the caller edge and on the
    summary edge `j → g` gives the motive on the result. -/
theorem summary_ok {P : Program} {counted : Acc → Bool} {L : Nat} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i j : PFact} {n n' : Node} {c : Call} {f a g r r' : AFact}
    {e1 e2 : MicroEdge}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee)
    (ha : a ∈ (applyEdge f e1.1 e1.2).facts) (hsm : markSubB j.mark a.fact.mark = true)
    (hr : r ∈ (applySummary a j g).facts) (he2 : e2 ∈ c.fromCallee)
    (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts)
    (ihD : EdgeOKR P ok (.edge M i n f))
    (ihG : EdgeOKR P ok (.edge c.callee j (P.exit c.callee) g)) :
    EdgeOKR P ok (.edge M i n' (limitF counted L r')) := by
  intro hla
  have e := Exact.limitF_exact hla
  rw [e] at hla ⊢
  have hra := Exact.applyEdge_demand hr' hla
  obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
  obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
  have haa := Exact.applyEdge_demand hx hxa
  have hfa := Exact.applyEdge_demand ha haa
  obtain ⟨ihD1, ihD2⟩ := ihD hfa
  obtain ⟨ihG1, ihG2⟩ := ihG hga
  have hgate := (Exact.applyEdge_mark hx).1
  -- an abstract caller fact meets an abstract summary conclusion
  have hG : Exact.absB a.fact.mark = true → Exact.absB g.fact.mark = true :=
    fun hA => ihG1 (Exact.gate_abs hgate hA)
  refine ⟨fun hi => ?_, fun l0 l hd hok => ?_⟩
  · have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD1 hi) ha
    have hR : Exact.absB x.fact.mark = true :=
      Exact.comp_abs (hG hA) hA (Exact.applyEdge_mark hx).2
    exact Exact.applyEdge_abs (c := ⟨x.fact, x.demand || g.demand⟩)
      (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
  · -- the binding back to the caller
    obtain ⟨hp3, hc3⟩ := Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr').1
    obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
    have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
    -- the summary edge
    obtain ⟨l1', hd1', hdg⟩ :=
      Exact.applyEdge_exact (Exact.premOK_of_sub hsm) (Exact.concOK_of hG) haa hx hxa hd2
    obtain ⟨hflG, hok1'⟩ := ihG2 l1' l2 hdg hok2
    -- the binding into the callee
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
    obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
    have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
    obtain ⟨hflD, hok0⟩ := ihD2 l0 l1 hd1 hok1
    exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩

#print axioms summary_ok

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-! ## 1. THE EXACTNESS THEOREM for `DR` -/

/-- The motive `EdgeOKR` holds on every object of a restricted run. ROUND 5: the hypotheses of
    `Exact.D_edgeOK` (`MarkWF`, `FiltOK`, `BackOK`), `SatMark sat`, and the valid records. -/
theorem DR_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs) {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) : EdgeOKR P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro ha
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, fun l0 l hd hok => ?_⟩
    have e := Exact.startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    intro ha
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨ih1, ih2⟩ := ih hfa
    refine ⟨fun hi => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    intro ha
    obtain ⟨ih1, ih2⟩ := ih ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ hres hs hr he2 hr' ihD _ ihG =>
    -- `RestrictSub`: the restricted edge keeps a subset of the pairs, in the same layer
    obtain ⟨hgd, hgsub⟩ := hsub j g d g' hres
    have ihG' : EdgeOKR P ok (.edge c.callee j (P.exit c.callee) g') := by
      intro hg'
      obtain ⟨h1, h2⟩ := ihG (hgd.symm.trans hg')
      exact ⟨fun hJ => abs_of_sub hJ (h1 hJ) hgsub,
        fun l1 l2 hd hok => h2 l1 l2 (hgsub l1 l2 hd) hok⟩
    exact summary_ok hmw hbo hE he1 ha (hsat j a.fact hs) hr he2 hr' ihD ihG'
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hs hr he2 hr' ihD =>
    -- `RecsExactV`: the motive holds on the record
    exact summary_ok hmw hbo hE he1 ha (hsat j a.fact hs) hr he2 hr' ihD (hrecs c.callee j g hrec)
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    intro ha
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨ih1, ih2⟩ := ih hfa
    refine ⟨fun hi => Exact.cleanRes_abs (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    intro ha
    obtain ⟨ih1, ih2⟩ := ih ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms DR_edgeOK

/-- 1. THE EXACTNESS THEOREM for a restricted run. A normal-layer edge of `DR` denotes
    only real flows. ROUND 5: the hypotheses `MarkWF P`, `FiltUp P` (as `Exact.edge_exact`)
    and `SatMark sat` are new. -/
theorem edge_exactR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  ((DR_edgeOK hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) hsat hsub
    (RecsExact.toV hmw hrecs) h ha).2 l0 l hd trivial).1

#print axioms edge_exactR

/-- 1v. THE EXACTNESS THEOREM FOR VALID LOCATIONS (prefix-closed type filters, no `FiltUp`;
    the hypotheses of `Exact.edge_exact_valid`). -/
theorem edge_exactR_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  (DR_edgeOK hmw (Exact.filtValid_ok hv) hbo hsat hsub hrecs h ha).2 l0 l hd hok

#print axioms edge_exactR_valid

/-- 1'. A complete edge of a restricted run denotes only real flows. -/
theorem complete_exactR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hc : f.complete = true) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  edge_exactR hmw hup hsat hsub hrecs h (Exact.complete_demand hc) hd

#print axioms complete_exactR

/-! ## 2. Closed initial fact -/

/-- A demanded flow is a real flow. -/
theorem flowR_flow {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowR P demand M l0 n l) : Flow P M l0 n l := by
  induction h with
  | start M l0 => exact Flow.start M l0
  | step _ hE hs ih => exact Flow.step ih hE hs
  | pass _ hE hm ih => exact Flow.pass ih hE hm
  | call _ hE he1 hd1 _ _ _ _ _ he2 hd2 ih1 ih2 => exact Flow.call ih1 hE he1 hd1 ih2 he2 hd2
  | clean _ hE hc ih => exact Flow.clean ih hE hc
  | filt _ hE hp ih => exact Flow.filt ih hE hp

#print axioms flowR_flow

/-- 2. A closed initial fact of a restricted run. If the exit edges of `i` cover every
    DEMANDED flow (`hcov`) and every exit edge of `i` is in the normal layer (`hcomp`),
    then every demanded flow from the location set of `i` has a record, and every
    record of `i` is a real flow. With `flowR_flow`:
    `FlowR ⊆ records ⊆ Flow`. The records are not inside `FlowR` in general: the
    rule `retRec` and the rule `ret` with `restrictS` keep pairs outside the demand. -/
theorem closed_exactR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact}
    (hcov : ∀ l0 l, i.covers l0 → FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l)
    (hcomp : ∀ g, DR P counted L demand emit sat restrict recs sinks roots
      (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    (FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) ∧
    ((∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) → Flow P M l0 (P.exit M) l) :=
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ => edge_exactR hmw hup hsat hsub hrecs hg (hcomp g hg) hd⟩

#print axioms closed_exactR

/-- 2v. The closed initial fact for a valid end location (the hypotheses of
    `edge_exactR_valid`). -/
theorem closed_exactR_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs)
    {M : MethodId} {i : PFact}
    (hcov : ∀ l0 l, i.covers l0 → FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l)
    (hcomp : ∀ g, DR P counted L demand emit sat restrict recs sinks roots
      (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) (hok : ok l) :
    (FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) ∧
    ((∃ g, DR P counted L demand emit sat restrict recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) → Flow P M l0 (P.exit M) l) :=
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ =>
    (edge_exactR_valid hmw hv hbo hsat hsub hrecs hg (hcomp g hg) hd hok).1⟩

#print axioms closed_exactR_valid

/-! ## 3. The records of a run are exact -/

/-- 3. The exit edges of a restricted run satisfy `RecsExact`. So the persisted records
    of a restricted run (complete exit edges, a subset: `recs_mono`) can be used again by
    a later run. -/
theorem recs_of_DR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (exitRecs P (DR P counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ hr hg _ _ hd => edge_exactR hmw hup hsat hsub hrecs hr hg hd

#print axioms recs_of_DR

/-- 3v. The exit edges of a restricted run satisfy `RecsExactV` (valid locations). -/
theorem recs_of_DR_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs) :
    RecsExactV P ok (exitRecs P (DR P counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ hr => DR_edgeOK hmw (Exact.filtValid_ok hv) hbo hsat hsub hrecs hr

#print axioms recs_of_DR_valid

/-- 3'. The complete exit edges of a restricted run (the persisted records) are exact. -/
theorem recs_complete_of_DR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (fun m jg =>
      exitRecs P (DR P counted L demand emit sat restrict recs sinks roots) m jg ∧
        jg.2.complete = true) :=
  recs_mono (fun _ _ h => h.1) (recs_of_DR hmw hup hsat hsub hrecs)

#print axioms recs_complete_of_DR

/-- 3''. The records of the run sequence: the records of earlier runs together with the
    exit edges of this run are exact. -/
theorem recs_step (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (fun m jg => recs m jg ∨
      exitRecs P (DR P counted L demand emit sat restrict recs sinks roots) m jg) :=
  recs_union hrecs (recs_of_DR hmw hup hsat hsub hrecs)

#print axioms recs_step

end

/-- 3 (run 1). The exit edges of the closure `D` satisfy `RecsExact` (the hypotheses of
    `Exact.edge_exact`). -/
theorem recs_of_D {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) :
    RecsExact P (exitRecs P (D P counted L α sinks roots)) :=
  fun _ _ _ hr hg _ _ hd => Exact.edge_exact hmw hup hr hg hd

#print axioms recs_of_D

/-- 3v (run 1). The exit edges of the closure `D` satisfy `RecsExactV` (valid locations). -/
theorem recs_of_D_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) :
    RecsExactV P ok (exitRecs P (D P counted L α sinks roots)) := by
  intro _ _ _ hr hg
  have h := Exact.D_edgeOK hmw (Exact.filtValid_ok hv) hbo hr
  exact ⟨h.1, h.2 hg⟩

#print axioms recs_of_D_valid

/-! ## 4. Shape invariants of `DR` -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The motive `Invariant.Inv` holds on every object of a restricted run. No hypothesis
    on `emit`, `sat`, `restrict` or `recs` is necessary: in the rules `ret` and `retRec`
    the shape of the result comes from the caller fact (`Invariant.applySummary_Q`,
    `Invariant.applySummary_Legal`), for every summary edge. -/
theorem DR_inv {o : Obj} (h : DR P counted L demand emit sat restrict recs sinks roots o) :
    Invariant.Inv o := by
  induction h with
  | root => trivial
  | @start M i _ =>
    exact ⟨fun e hk => Invariant.startFact_legal hk, fun ei hi => Invariant.startFact_Q hi⟩
  | @step M i n f n' s f' _ _ hf' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases Invariant.transfer_mem hf' with rfl | ⟨x, e, _, hx, rfl⟩
    · exact ⟨ih1, ih2⟩
    · exact ⟨Invariant.limitF_Legal (Invariant.applyEdge_Legal hx),
        fun ei hi => Invariant.limitF_Q (Invariant.applyEdge_Q (ih2 ei hi) ih1 hx)⟩
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨ihL, ihQ⟩ := ihF
    refine ⟨Invariant.limitF_Legal (Invariant.applyEdge_Legal hr'), fun ei hi => ?_⟩
    have qa := Invariant.applyEdge_Q (ihQ ei hi) ihL ha
    have qr := Invariant.applySummary_Q qa (Invariant.applyEdge_Legal ha) hr
    exact Invariant.limitF_Q (Invariant.applyEdge_Q qr (Invariant.applySummary_Legal hr) hr')
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨ihL, ihQ⟩ := ihF
    refine ⟨Invariant.limitF_Legal (Invariant.applyEdge_Legal hr'), fun ei hi => ?_⟩
    have qa := Invariant.applyEdge_Q (ihQ ei hi) ihL ha
    have qr := Invariant.applySummary_Q qa (Invariant.applyEdge_Legal ha) hr
    exact Invariant.limitF_Q (Invariant.applyEdge_Q qr (Invariant.applySummary_Legal hr) hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    exact ⟨Invariant.cleanRes_Legal ih1 hf', fun ei hi => Invariant.cleanRes_Q (ih2 ei hi) hf'⟩
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DR_inv

/-- W2 and the demand-layer invariant for a restricted run: a final `*` fact has an abstract
    mark (`*` or `*∖x`) and is in the normal layer. ROUND 5: the mark can be `*∖x` (a cleaner
    puts it there), as in `Invariant.final_star_legal`. -/
theorem final_star_legalR {M : MethodId} {i : PFact} {n : Node} {f : AFact} {e : Excl}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hk : f.fact.kind = .star e) : Invariant.AbsMark f.fact.mark ∧ f.demand = false :=
  (DR_inv P counted L demand emit sat restrict recs sinks roots h).1 e hk

#print axioms final_star_legalR

/-- A final `*/Ec` under an initial `*/Ei` of a restricted run keeps every exclusion of
    the initial fact. -/
theorem star_final_keeps_initial_exclR {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    {ei ec : Excl}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hi : i.kind = .star ei) (hk : f.fact.kind = .star ec) : ei.subB ec = true :=
  ((DR_inv P counted L demand emit sat restrict recs sinks roots h).2 ei hi).1 ec hk

#print axioms star_final_keeps_initial_exclR

/-- Under a `*/Ei` initial fact of a restricted run, a normal-layer final fact has the
    `*` tail, or `Ei` is empty. -/
theorem star_initial_completeR {M : MethodId} {i : PFact} {n : Node} {f : AFact} {ei : Excl}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hi : i.kind = .star ei) (hc : f.demand = false) :
    f.fact.kind.isStar = true ∨ ei.isEmptyB = true := by
  cases hs : f.fact.kind.isStar with
  | true => exact Or.inl rfl
  | false =>
    rcases ((DR_inv P counted L demand emit sat restrict recs sinks roots h).2 ei hi).2 hs with
      ha | he
    · rw [hc] at ha; cases ha
    · exact Or.inr he

#print axioms star_initial_completeR

end

/-- Port of `Confirmed.D_NS`: under a non-`*` initial fact of a restricted run every
    final fact is non-`*`. No hypothesis is necessary. -/
theorem DR_NS {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) : Confirmed.NS o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact fun hi => Confirmed.startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf' ih => exact fun hi => Confirmed.transfer_nonstar (ih hi) hf'
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hi
    have h1 := Confirmed.applyEdge_nonstar (ihF hi) ha
    obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
    have h2 := Confirmed.applyEdge_nonstar h1 hx
    have h3 : (AFact.norm ⟨x.fact, x.demand || g'.demand⟩).fact.kind.isStar = false := by
      rw [Confirmed.norm_nonstar (x := ⟨x.fact, x.demand || g'.demand⟩) h2]
      exact h2
    exact Confirmed.limitF_nonstar (Confirmed.applyEdge_nonstar h3 hr')
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hi
    have h1 := Confirmed.applyEdge_nonstar (ihF hi) ha
    obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
    have h2 := Confirmed.applyEdge_nonstar h1 hx
    have h3 : (AFact.norm ⟨x.fact, x.demand || g.demand⟩).fact.kind.isStar = false := by
      rw [Confirmed.norm_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) h2]
      exact h2
    exact Confirmed.limitF_nonstar (Confirmed.applyEdge_nonstar h3 hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih => exact fun hi => Confirmed.cleanRes_nonstar (ih hi) hf'
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DR_NS

/-! ## 5. Support and confirmation for `DR` -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The normal-layer SUPPORT of initial facts of a restricted run (as `Confirmed.Sup`,
    with `DR` in place of `D`). -/
inductive SupR : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → SupR M zeroFact
  | call {M i n f n' c e a j} :
      SupR M i →
      DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) →
      f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DR P counted L demand emit sat restrict recs sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DR P counted L demand emit sat restrict recs sinks roots (.req c.callee k t) ∧
          a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧
          j = a.fact)) →
      SupR c.callee j

/-- A CONFIRMED vulnerability of a restricted run: a complete sink edge under a
    supported initial fact. -/
def ConfirmedR (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) ∧
    SupR P counted L demand emit sat restrict recs sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- A supported initial fact of a restricted run is exact with a concrete mark, and its
    unique location is entry-reachable. ROUND 5: the hypotheses of `edge_exactR`. -/
theorem sup_entryR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact}
    (h : SupR P counted L demand emit sat restrict recs sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    have hJ : ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
      rcases hj with ⟨hj0, hz⟩ | ⟨k, t, _, hak, ham, _, hja⟩
      · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
      · exact ⟨t, hak, ham, hja⟩
    obtain ⟨t, hak, ham, rfl⟩ := hJ
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hR := Confirmed.entry_reach P roots hent (edge_exactR hmw hup hsat hsub hrecs hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entryR

/-- 5. THE THEOREM for a restricted run: a confirmed vulnerability of ANY restricted run
    (any `demand`, `emit`; a `sat` with `SatMark`; a `restrict` that only removes pairs; exact
    persisted records) is a real concrete vulnerability (no false positive). ROUND 5: the
    hypotheses `MarkWF P`, `FiltUp P`, `SatMark sat`. -/
theorem confirmed_realR (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entryR hmw hup hsat hsub hrecs hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := DR_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo, hps⟩ := Confirmed.check_triggered_passes him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩, ?_, ?_⟩
  · exact Confirmed.entry_reach P roots hent
      (edge_exactR hmw hup hsat hsub hrecs hD hfd (Confirmed.den_exact_exact him hfk hps))
  · exact Confirmed.overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)

#print axioms confirmed_realR

end

/-! ## 6. The concrete restrictions only remove pairs

  `restrictU` and `restrictS` satisfy `RestrictSub`. So the theorems above apply to the
  runs with the U rules and with the S rules. -/

/-- An `[any]` conclusion at a shorter path holds every pair of a conclusion at a longer
    path with the same base and mark, for every tail kind. -/
theorem den_any_shorter {j : PFact} {b : Base} {q r : List Acc} {k : Kind} {m : MarkA}
    {l1 l2 : Loc} (h : den j ⟨b, q ++ r, k, m⟩ l1 l2) : den j ⟨b, q, .any, m⟩ l1 l2 := by
  obtain ⟨h0b, h2b, h0m, h2m, h2s, σ, τ, h0p, h2p, hI, _⟩ := h
  exact ⟨h0b, h2b, h0m, h2m, h2s, σ, r ++ τ, h0p, by rw [h2p, List.append_assoc], hI, trivial⟩

#print axioms den_any_shorter

/-- The property of a conclusion restriction that `RestrictSub` needs. -/
def ConcSub (rc : AFact → PFact → Option AFact) : Prop :=
  ∀ sc p g', rc sc p = some g' →
    g'.demand = sc.demand ∧ ∀ j l1 l2, den j g'.fact l1 l2 → den j sc.fact l1 l2

theorem restrictWith_sub {rc : AFact → PFact → Option AFact} (hrc : ConcSub rc) :
    RestrictSub (restrictWith rc) := by
  intro j g d g' h
  unfold restrictWith at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases ho : overlapB j d.din with
    | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ho, if_pos rfl] at h
      obtain ⟨h1, h2⟩ := hrc g p g' h
      exact ⟨h1, fun l1 l2 hd => h2 j l1 l2 hd⟩

#print axioms restrictWith_sub

theorem restrictConcU_sub : ConcSub restrictConcU := by
  intro sc p g' h
  obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
  unfold restrictConcU at h
  cases hb : Nat.beq b p.base with
  | false => rw [hb, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hb, if_pos rfl] at h
    cases hrel : relate p.path q with
    | apart => rw [hrel] at h; cases h
    | below r =>
      rw [hrel] at h
      dsimp only at h
      cases ha : admitsTailB p.kind r with
      | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
      | true =>
        rw [ha, if_pos rfl] at h
        cases h
        exact ⟨rfl, fun _ _ _ hd => hd⟩
    | above r =>
      rw [hrel] at h
      have hp := Exact.relate_above hrel
      cases k with
      | star e => cases h
      | exact => cases h
      | any =>
        cases h
        refine ⟨rfl, fun _ _ _ hd => ?_⟩
        rw [hp] at hd
        exact den_any_shorter hd

#print axioms restrictConcU_sub

theorem restrictConcS_sub : ConcSub restrictConcS := by
  intro sc p g' h
  obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
  unfold restrictConcS at h
  cases hb : Nat.beq b p.base with
  | false => rw [hb, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hb, if_pos rfl] at h
    cases hrel : relate p.path q with
    | apart => rw [hrel] at h; cases h
    | below r =>
      rw [hrel] at h
      dsimp only at h
      cases ha : admitsTailB p.kind r with
      | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
      | true =>
        rw [ha, if_pos rfl] at h
        cases h
        exact ⟨rfl, fun _ _ _ hd => hd⟩
    | above r =>
      rw [hrel] at h
      have hp := Exact.relate_above hrel
      cases k with
      | exact => cases h
      | star e =>
        dsimp only at h
        cases ha : e.admits r with
        | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [ha, if_pos rfl] at h
          cases h
          exact ⟨rfl, fun _ _ _ hd => hd⟩
      | any =>
        cases h
        refine ⟨rfl, fun _ _ _ hd => ?_⟩
        rw [hp] at hd
        exact den_any_shorter hd

#print axioms restrictConcS_sub

theorem restrictU_sub : RestrictSub restrictU := restrictWith_sub restrictConcU_sub

#print axioms restrictU_sub

theorem restrictS_sub : RestrictSub restrictS := restrictWith_sub restrictConcS_sub

#print axioms restrictS_sub

/-- 5 (S rules). A confirmed vulnerability of a run with the S restriction (any demand,
    any emission, a satisfaction with `SatMark`, exact persisted records) is a real
    vulnerability. -/
theorem confirmed_realS {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hrecs : RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrictS recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realR hmw hup hsat restrictS_sub hrecs h

#print axioms confirmed_realS

/-- 5 (U rules). The same for a run with the U restriction. -/
theorem confirmed_realU {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hrecs : RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realR hmw hup hsat restrictU_sub hrecs h

#print axioms confirmed_realU

/-! ## 7. Version 4: a restricted run is CONCRETE

  The run starts from the zero fact (concrete mark). The rules keep a concrete mark:
    * a statement, a call binding and a summary application keep a concrete caller mark
      (`transfer_mark_conc`, `applyEdge_mark_conc`, `applySummary_mark_conc`), for ANY
      summary edge and ANY persisted record;
    * a cleaner on a concrete fact gives concrete facts (`cleanRes_mark_conc`) and no request
      (`cleanRes_reqs_abstract`); a type filter keeps the fact;
    * the emission copies the mark of the added fact (`EmitCopiesMark`, `emitM`);
    * a fact with a concrete mark raises no request (`transfer_reqs_of_conc`), and the sink
      check raises no request under a concrete initial fact (`check_request_star`);
    * without a request there is no answer and no `reqUp`.
  So no object of the run is a request. -/

/-- The concreteness motive: every initial fact, every edge (premise and final fact) and
    every added fact has a concrete mark; no request exists. -/
def ConcObj : Obj → Prop
  | .init _ j => ∃ t, j.mark = .conc t
  | .edge _ i _ f => (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t
  | .added _ a => ∃ t, a.mark = .conc t
  | .req _ _ _ => False
  | .vuln _ _ _ _ => True

/-- The premise-layer motive: a normal-layer edge has an exact premise or an abstract-mark
    premise (`*` or `*∖x`). (A premise with a concrete mark and a `*` or `[any]` tail starts in
    the demand layer, and the demand layer never goes back.) ROUND 5: the premise mark can be
    `*∖x` (an arbitrary emission can give it; `startFact` keeps it in the normal layer). -/
def PremLayer : Obj → Prop
  | .edge _ i _ f => f.demand = false → i.kind = .exact ∨ Exact.absB i.mark = true
  | _ => True

/-- `emitM` copies the mark of the added fact. -/
theorem emitM_copies : EmitCopiesMark emitM := by
  intro d a j h
  unfold emitM at h
  cases hc : (Nat.beq d.base a.base && markMatchB d.mark a.mark) with
  | false => rw [hc, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hc, if_pos rfl] at h
    cases hrel : relate d.path a.path with
    | apart => rw [hrel] at h; cases h
    | below r =>
      rw [hrel] at h
      cases r with
      | nil => cases h; rfl
      | cons x r =>
        dsimp only at h
        cases ha : admitsTailB d.kind (x :: r) with
        | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [ha, if_pos rfl] at h; cases h; rfl
    | above r =>
      rw [hrel] at h
      dsimp only at h
      cases ha : admitsTailB a.kind r with
      | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
      | true => rw [ha, if_pos rfl] at h; cases h; rfl

#print axioms emitM_copies

/-- A fact is never strictly above itself: `relate` never gives `.above []`. -/
theorem relate_above_nil {p q : List Acc} (h : relate p q = .above []) : False := by
  unfold relate at h
  cases h1 : dropPrefix p q with
  | some r => rw [h1] at h; cases h
  | none =>
    rw [h1] at h
    dsimp only at h
    cases h2 : dropPrefix q p with
    | none => rw [h2] at h; cases h
    | some r =>
      rw [h2] at h
      cases h
      have hp : p = q ++ [] := CoreAux.dropPrefix_some.mp h2
      rw [List.append_nil] at hp
      have h3 : dropPrefix p q = some [] := CoreAux.dropPrefix_some.mpr (by rw [hp, List.append_nil])
      rw [h3] at h1
      cases h1

theorem meetK_exact_left (k : Kind) : meetK .exact k = .exact := by
  cases k <;> rfl

/-- `emitM` on an EXACT added fact emits the added fact itself (the second disjunct of
    `SupM.call`). -/
theorem emitM_exact_self {d a j : PFact} (hk : a.kind = .exact) (h : emitM d a = some j) :
    j = a := by
  unfold emitM at h
  cases hc : (Nat.beq d.base a.base && markMatchB d.mark a.mark) with
  | false => rw [hc, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hc, if_pos rfl] at h
    cases hrel : relate d.path a.path with
    | apart => rw [hrel] at h; cases h
    | below r =>
      rw [hrel] at h
      cases r with
      | nil =>
        cases h
        rw [hk, meetK_exact_left, ← hk]
      | cons x r =>
        dsimp only at h
        cases ha : admitsTailB d.kind (x :: r) with
        | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [ha, if_pos rfl] at h; cases h; rfl
    | above r =>
      rw [hrel] at h
      dsimp only at h
      cases r with
      | nil => exact (relate_above_nil hrel).elim
      | cons x r =>
        have ha : admitsTailB a.kind (x :: r) = false := by rw [hk]; rfl
        rw [ha, if_neg Bool.false_ne_true] at h
        cases h

#print axioms emitM_exact_self

/-- A correlated `*` conclusion is the only input on which the two conclusion restrictions
    differ. -/
theorem restrictConcU_eq_S {sc : AFact} {p : PFact} (h : sc.fact.kind.isStar = false) :
    restrictConcU sc p = restrictConcS sc p := by
  obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
  cases k with
  | star e => cases h
  | any =>
    unfold restrictConcU restrictConcS
    cases Nat.beq b p.base with
    | false => rfl
    | true => cases relate p.path q <;> rfl
  | exact =>
    unfold restrictConcU restrictConcS
    cases Nat.beq b p.base with
    | false => rfl
    | true => cases relate p.path q <;> rfl

#print axioms restrictConcU_eq_S

/-- `restrictU` and `restrictS` agree on every summary edge without the `*` tail. -/
theorem restrictU_eq_S {j : PFact} {g : AFact} {d : DemandEdge} (h : g.fact.kind.isStar = false) :
    restrictU j g d = restrictS j g d := by
  obtain ⟨din, dout⟩ := d
  cases dout with
  | none => rfl
  | some p =>
    show (if overlapB j din = true then restrictConcU g p else none) =
      (if overlapB j din = true then restrictConcS g p else none)
    rw [restrictConcU_eq_S h]

#print axioms restrictU_eq_S

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- 7. CONCRETENESS. With a mark-copying emission, every object of a restricted run is
    concrete (any demand, satisfaction, restriction and persisted records). -/
theorem DR_concrete (hem : EmitCopiesMark emit) {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) : ConcObj o := by
  induction h with
  | root => exact ⟨zeroMark, rfl⟩
  | @start M i _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨⟨t, ht⟩, t, by rw [startFact_mark, ht]⟩
  | @step M i n f n' s f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    exact ⟨hi, transfer_mark_conc ht hf⟩
  | @reqStmt M i n f n' s t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    rw [transfer_reqs_of_conc h0] at ht
    cases ht
  | pass _ _ _ ih => exact ih
  | @added M i n f n' c e a _ _ _ ha ih =>
    obtain ⟨_, t, ht⟩ := ih
    exact applyEdge_mark_conc ht ha
  | @initR m a d j _ _ hj ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t, by rw [hem _ _ _ hj, ht]⟩
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, h3]⟩
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    obtain ⟨hi, t, ht⟩ := ihF
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨hi, t3, by rw [limitF_mark, h3]⟩
  | @reqSink M i n f s t _ _ hc ih =>
    obtain ⟨⟨t0, h0⟩, _⟩ := ih
    exact check_request_star hc t0 h0
  | answer _ _ _ _ ihR _ => exact ihR.elim
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact ihR.elim
  | vuln => trivial
  -- the cleaner on a concrete fact: concrete facts, no request
  | @clean M i n f n' cl f' _ _ hf ih =>
    obtain ⟨hi, t, ht⟩ := ih
    exact ⟨hi, cleanRes_mark_conc ht hf⟩
  | @reqClean M i n f n' cl t _ _ ht ih =>
    obtain ⟨_, t0, h0⟩ := ih
    exact (cleanRes_reqs_abstract ht).1 t0 h0
  | filt _ _ _ ih => exact ih

#print axioms DR_concrete

/-- Every added fact of a restricted run with a mark-copying emission is concrete. -/
theorem added_concrete (hem : EmitCopiesMark emit) :
    ∀ m a, DR P counted L demand emit sat restrict recs sinks roots (.added m a) →
      ∃ t, a.mark = .conc t :=
  fun _ _ h => DR_concrete hem h

#print axioms added_concrete

/-- Every initial fact of a restricted run with a mark-copying emission is concrete. -/
theorem init_concrete (hem : EmitCopiesMark emit) {m : MethodId} {j : PFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.init m j)) :
    ∃ t, j.mark = .conc t :=
  DR_concrete hem h

#print axioms init_concrete

/-- Every edge of a restricted run with a mark-copying emission is concrete (premise and
    final fact). -/
theorem edge_concrete (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f)) :
    (∃ t, i.mark = .conc t) ∧ ∃ t, f.fact.mark = .conc t :=
  DR_concrete hem h

#print axioms edge_concrete

/-- NO MARK REQUEST after the first run: a restricted run with a mark-copying emission
    contains no request object. -/
theorem DR_no_request (hem : EmitCopiesMark emit) :
    ∀ M i t, ¬ DR P counted L demand emit sat restrict recs sinks roots (.req M i t) :=
  fun _ _ _ h => DR_concrete hem h

#print axioms DR_no_request

/-- Every initial fact of a restricted run with a mark-copying emission is the root zero
    fact or an emission; it is never the answer of a request. -/
theorem DR_no_answer_init (hem : EmitCopiesMark emit) {m : MethodId} {j : PFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.init m j)) :
    (m ∈ roots ∧ j = zeroFact) ∨
    ∃ d a, demand m d ∧ DR P counted L demand emit sat restrict recs sinks roots (.added m a) ∧
      emit d.din a = some j := by
  cases h with
  | root hM => exact Or.inl ⟨hM, rfl⟩
  | initR ha hd hj => exact Or.inr ⟨_, _, hd, ha, hj⟩
  | answer hR _ _ _ => exact (DR_no_request hem _ _ _ hR).elim

#print axioms DR_no_answer_init

/-- With a mark-copying emission, the contract for concrete added facts gives the contract
    for the run (the hypothesis of the coverage theorem). -/
theorem emitContractOn_of_conc (hem : EmitCopiesMark emit) (hc : EmitContractConc emit sat) :
    EmitContractOn (DR P counted L demand emit sat restrict recs sinks roots) emit sat :=
  EmitContractConc.on hc (added_concrete hem)

#print axioms emitContractOn_of_conc

/-- W2 in a concrete run: no final fact has the `*` tail (a `*` final fact has an abstract
    mark). -/
theorem final_not_star (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f)) :
    f.fact.kind.isStar = false := by
  cases hk : f.fact.kind with
  | star e =>
    have h1 := (final_star_legalR P counted L demand emit sat restrict recs sinks roots h hk).1
    obtain ⟨_, t, ht⟩ := DR_concrete hem h
    exact absurd ht (h1.not_conc t)
  | any => rfl
  | exact => rfl

#print axioms final_not_star

/-- The premise-layer motive holds on every object of a restricted run (no hypothesis). -/
theorem DR_premLayer {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) : PremLayer o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro hd
    obtain ⟨ib, ip, ik, im⟩ := i
    cases ik with
    | exact => exact Or.inl rfl
    | any => cases im <;> cases hd
    | star e =>
      cases im with
      | star => exact Or.inr rfl
      | starEx x => exact Or.inr rfl
      | conc t => cases hd
  | step _ _ hf ih => exact fun hd => ih (Exact.transfer_demand hf hd)
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, _⟩ := Exact.or_eq_false hra
    exact ihF (Exact.applyEdge_demand ha (Exact.applyEdge_demand hx hxa))
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hla
    have e := Exact.limitF_exact hla
    rw [e] at hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, _⟩ := Exact.or_eq_false hra
    exact ihF (Exact.applyEdge_demand ha (Exact.applyEdge_demand hx hxa))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact fun hd => ih (Exact.cleanRes_demand hf hd)
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms DR_premLayer

/-- 8. A normal-layer edge of a concrete run has an EXACT premise. -/
theorem complete_premise_exact (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact}
    {n : Node} {f : AFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hd : f.demand = false) : i.kind = .exact := by
  rcases DR_premLayer h hd with hk | hm
  · exact hk
  · obtain ⟨⟨t, ht⟩, _⟩ := DR_concrete hem h
    rw [ht] at hm
    cases hm

#print axioms complete_premise_exact

/-- 8'. The premise of a complete edge of a concrete run has the empty exclusion. -/
theorem complete_premEmpty (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact}
    {n : Node} {f : AFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hc : f.complete = true) : Reverse.PremEmpty i.kind := by
  rw [complete_premise_exact hem h (Exact.complete_demand hc)]
  exact True.intro

#print axioms complete_premEmpty

/-- 8''. Every complete record of a concrete run reverses exactly (the form of
    `Reverse.rev_exact_of_empty_premise`: empty premise exclusion, mark-reversible). -/
theorem complete_rev_exact (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact}
    {n : Node} {f : AFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hc : f.complete = true) {l0 l1 : Loc} :
    den i f.fact l0 l1 ↔ den (revEdge i f.fact).1 (revEdge i f.fact).2 l1 l0 :=
  Reverse.rev_exact_of_empty_premise (complete_premEmpty hem h hc)
    (Or.inr (edge_concrete hem h).1)

#print axioms complete_rev_exact

/-- From the U restriction to the S restriction (each run is concrete, so the summary edge
    has no `*` tail and the two restrictions agree). -/
theorem DR_U_to_S (hem : EmitCopiesMark emit) {o : Obj}
    (h : DR P counted L demand emit sat restrictU recs sinks roots o) :
    DR P counted L demand emit sat restrictS recs sinks roots o := by
  induction h with
  | root hM => exact DR.root hM
  | start _ ih => exact DR.start ih
  | step _ hE hf ih => exact DR.step ih hE hf
  | reqStmt _ hE ht ih => exact DR.reqStmt ih hE ht
  | pass _ hE hm ih => exact DR.pass ih hE hm
  | added _ hE he ha ih => exact DR.added ih hE he ha
  | initR _ hd hj ih => exact DR.initR ih hd hj
  | ret _ hE he1 ha _ hG hd hres hsat hr he2 hr' ihF ihJ ihG =>
    rw [restrictU_eq_S (final_not_star hem hG)] at hres
    exact DR.ret ihF hE he1 ha ihJ ihG hd hres hsat hr he2 hr'
  | retRec _ hE he1 ha hrec hsat hr he2 hr' ihF =>
    exact DR.retRec ihF hE he1 ha hrec hsat hr he2 hr'
  | reqSink _ hs hc ih => exact DR.reqSink ih hs hc
  | answer _ _ hm ho ihR ihA => exact DR.answer ihR ihA hm ho
  | reqUp _ _ hE hc he ha hm ho ihR ihF => exact DR.reqUp ihR ihF hE hc he ha hm ho
  | vuln _ hs hc ih => exact DR.vuln ih hs hc
  | clean _ hE hf ih => exact DR.clean ih hE hf
  | reqClean _ hE ht ih => exact DR.reqClean ih hE ht
  | filt _ hE hp ih => exact DR.filt ih hE hp

#print axioms DR_U_to_S

/-- From the S restriction to the U restriction. -/
theorem DR_S_to_U (hem : EmitCopiesMark emit) {o : Obj}
    (h : DR P counted L demand emit sat restrictS recs sinks roots o) :
    DR P counted L demand emit sat restrictU recs sinks roots o := by
  induction h with
  | root hM => exact DR.root hM
  | start _ ih => exact DR.start ih
  | step _ hE hf ih => exact DR.step ih hE hf
  | reqStmt _ hE ht ih => exact DR.reqStmt ih hE ht
  | pass _ hE hm ih => exact DR.pass ih hE hm
  | added _ hE he ha ih => exact DR.added ih hE he ha
  | initR _ hd hj ih => exact DR.initR ih hd hj
  | ret _ hE he1 ha _ hG hd hres hsat hr he2 hr' ihF ihJ ihG =>
    rw [← restrictU_eq_S (final_not_star hem hG)] at hres
    exact DR.ret ihF hE he1 ha ihJ ihG hd hres hsat hr he2 hr'
  | retRec _ hE he1 ha hrec hsat hr he2 hr' ihF =>
    exact DR.retRec ihF hE he1 ha hrec hsat hr he2 hr'
  | reqSink _ hs hc ih => exact DR.reqSink ih hs hc
  | answer _ _ hm ho ihR ihA => exact DR.answer ihR ihA hm ho
  | reqUp _ _ hE hc he ha hm ho ihR ihF => exact DR.reqUp ihR ihF hE hc he ha hm ho
  | vuln _ hs hc ih => exact DR.vuln ih hs hc
  | clean _ hE hf ih => exact DR.clean ih hE hf
  | reqClean _ hE ht ih => exact DR.reqClean ih hE ht
  | filt _ hE hp ih => exact DR.filt ih hE hp

#print axioms DR_S_to_U

/-- 9. With a mark-copying emission, the closure with `restrictU` and the closure with
    `restrictS` are the same predicate (the version-3 repair of the restriction never fires). -/
theorem restrict_U_iff_S (hem : EmitCopiesMark emit) (o : Obj) :
    DR P counted L demand emit sat restrictU recs sinks roots o ↔
      DR P counted L demand emit sat restrictS recs sinks roots o :=
  ⟨DR_U_to_S hem, DR_S_to_U hem⟩

#print axioms restrict_U_iff_S

theorem restrict_U_eq_S (hem : EmitCopiesMark emit) :
    DR P counted L demand emit sat restrictU recs sinks roots =
      DR P counted L demand emit sat restrictS recs sinks roots :=
  funext fun o => propext (restrict_U_iff_S hem o)

#print axioms restrict_U_eq_S

end

/-! ## 8. Version 4: support and confirmation without requests

  A restricted run with `emitM` has no request, so the request disjunct of `SupR.call`
  never holds. The soundness proof uses only this: the callee initial fact IS the exact
  concrete added fact. `SupM` asks only for that. -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The generalized normal-layer support: a callee initial fact is supported if it is the
    zero fact of the zero added fact, or if it IS the exact concrete added fact. -/
inductive SupM : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → SupM M zeroFact
  | call {M i n f n' c e a j} :
      SupM M i →
      DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) →
      f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DR P counted L demand emit sat restrict recs sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (a.fact.kind = .exact ∧ (∃ t, a.fact.mark = .conc t) ∧ j = a.fact)) →
      SupM c.callee j

/-- A CONFIRMED vulnerability with the generalized support. -/
def ConfirmedM (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) ∧
    SupM P counted L demand emit sat restrict recs sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- The support of version 3 is a special case of the generalized support. -/
theorem supR_supM {M : MethodId} {i : PFact}
    (h : SupR P counted L demand emit sat restrict recs sinks roots M i) :
    SupM P counted L demand emit sat restrict recs sinks roots M i := by
  induction h with
  | root hM => exact SupM.root hM
  | call _ hD hfd hE he ha had hJ hj ih =>
    refine SupM.call ih hD hfd hE he ha had hJ ?_
    rcases hj with h0 | ⟨_, t, _, hak, ham, _, hja⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hak, ⟨t, ham⟩, hja⟩

#print axioms supR_supM

/-- A confirmed vulnerability of version 3 is a confirmed vulnerability with the generalized
    support. -/
theorem confirmedR_M {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrict recs sinks roots M n s) :
    ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s :=
  match h with
  | ⟨i, f, hD, hS, hc, hs, hch⟩ => ⟨i, f, hD, supR_supM hS, hc, hs, hch⟩

#print axioms confirmedR_M

/-- The facts of one step of the generalized support: the added fact `a` is exact with the
    mark `t` and it is the supported initial fact `j`. -/
theorem supM_step {a : AFact} {j : PFact}
    (hj : (j = zeroFact ∧ a.fact = zeroFact) ∨
      (a.fact.kind = .exact ∧ (∃ t, a.fact.mark = .conc t) ∧ j = a.fact)) :
    ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
  rcases hj with ⟨hj0, hz⟩ | ⟨hak, ⟨t, ham⟩, hja⟩
  · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
  · exact ⟨t, hak, ham, hja⟩

/-- A supported initial fact (generalized support) is exact with a concrete mark, and its
    unique location is entry-reachable. ROUND 5: the hypotheses of `edge_exactR`. -/
theorem sup_entryM (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact}
    (h : SupM P counted L demand emit sat restrict recs sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := supM_step hj
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hR := Confirmed.entry_reach P roots hent (edge_exactR hmw hup hsat hsub hrecs hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entryM

/-- The generalized support for valid locations (prefix-closed type filters, no `FiltUp`):
    the unique location of a supported initial fact is entry-reachable if it is valid. -/
theorem sup_entryM_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs)
    {M : MethodId} {i : PFact}
    (h : SupM P counted L demand emit sat restrict recs sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      (ok ⟨i.base, i.path, t⟩ → Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩) := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, fun _ => Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := supM_step hj
    refine ⟨t, hak, ham, fun hokj => ?_⟩
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hokl : ok l := hbo.toC _ _ _ _ hE e he _ _ hd2 hokj
    obtain ⟨hfl, hok0⟩ := edge_exactR_valid hmw hv hbo hsat hsub hrecs hD hfd hd1 hokl
    exact Or.inr ⟨M, n, l, n', c, e, Confirmed.entry_reach P roots (hent hok0) hfl, hE, rfl, he, hd2⟩

#print axioms sup_entryM_valid

/-- 10. THE THEOREM with the generalized support: a confirmed vulnerability of ANY
    restricted run (any `demand`, `emit`; a `sat` with `SatMark`; a `restrict` that only
    removes pairs; exact persisted records) is a real concrete vulnerability (no false
    positive). ROUND 5: the hypotheses `MarkWF P`, `FiltUp P`, `SatMark sat`. -/
theorem confirmed_realM_gen (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entryM hmw hup hsat hsub hrecs hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := DR_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo, hps⟩ := Confirmed.check_triggered_passes him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩, ?_, ?_⟩
  · exact Confirmed.entry_reach P roots hent
      (edge_exactR hmw hup hsat hsub hrecs hD hfd (Confirmed.den_exact_exact him hfk hps))
  · exact Confirmed.overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)

#print axioms confirmed_realM_gen

/-- 10v. THE THEOREM FOR VALID LOCATIONS with the generalized support (prefix-closed type
    filters, no `FiltUp`): a confirmed vulnerability has a location in the sink pattern, and
    this location is reached if it is valid. -/
theorem confirmed_realM_gen_valid_of {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExactV P ok recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entryM_valid hmw hv hbo hsat hsub hrecs hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := DR_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo, hps⟩ := Confirmed.check_triggered_passes him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩,
    Confirmed.overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo), fun hok => ?_⟩
  obtain ⟨hfl, hok0⟩ := edge_exactR_valid hmw hv hbo hsat hsub hrecs hD hfd
    (Confirmed.den_exact_exact him hfk hps) hok
  exact Confirmed.entry_reach P roots (hent hok0) hfl

#print axioms confirmed_realM_gen_valid_of

/-- 10v'. If every location of the sink pattern is valid, a confirmed vulnerability (generalized
    support) is a real concrete vulnerability. -/
theorem confirmed_realM_gen_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hsat : SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RecsExactV P ok recs)
    {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hcov, hR⟩ := confirmed_realM_gen_valid_of hmw hv hbo hsat hsub hrecs h
  exact ⟨l, hR (hok l hcov), hcov⟩

#print axioms confirmed_realM_gen_valid

end

/-! ## 9. Version 4: `emitM`, `satO`, `restrictU` (the spec rules use `satI` since version 5: `RMain`) -/

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- 10 (version 4). A confirmed vulnerability of a version-4 run (`emitM`, `satO`,
    `restrictU`; any demand; exact persisted records) is a real vulnerability. ROUND 5: the
    hypotheses `MarkWF P` and `FiltUp P`. -/
theorem confirmed_realM (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hrecs : RecsExact P recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM P counted L demand emitM satO restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realM_gen hmw hup satO_mark restrictU_sub hrecs h

#print axioms confirmed_realM

/-- 10v (spec rules). The same for valid locations (prefix-closed type filters, no `FiltUp`):
    if every location of the sink pattern is valid, a confirmed vulnerability of a version-4
    run is a real vulnerability. -/
theorem confirmed_realM_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) (hrecs : RecsExactV P ok recs)
    {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedM P counted L demand emitM satO restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realM_gen_valid hmw hv hbo satO_mark restrictU_sub hrecs hok h

#print axioms confirmed_realM_valid

/-- A version-4 run contains no request object. -/
theorem DR_no_requestM {restrict : PFact → AFact → DemandEdge → Option AFact}
    {sat : PFact → PFact → Bool} :
    ∀ M i t, ¬ DR P counted L demand emitM sat restrict recs sinks roots (.req M i t) :=
  DR_no_request emitM_copies

#print axioms DR_no_requestM

/-- Every added fact of a version-4 run is concrete. -/
theorem added_concreteM {restrict : PFact → AFact → DemandEdge → Option AFact}
    {sat : PFact → PFact → Bool} :
    ∀ m a, DR P counted L demand emitM sat restrict recs sinks roots (.added m a) →
      ∃ t, a.mark = .conc t :=
  added_concrete emitM_copies

#print axioms added_concreteM

/-- In a version-4 run, `restrictU` and `restrictS` give the same closure. -/
theorem restrict_U_eq_S_M {sat : PFact → PFact → Bool} :
    DR P counted L demand emitM sat restrictU recs sinks roots =
      DR P counted L demand emitM sat restrictS recs sinks roots :=
  restrict_U_eq_S emitM_copies

#print axioms restrict_U_eq_S_M

/-- Every complete record of a version-4 run has an exact premise and reverses exactly. -/
theorem complete_rev_exactM {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR P counted L demand emitM satO restrictU recs sinks roots (.edge M i n f))
    (hc : f.complete = true) :
    i.kind = .exact ∧ ∀ l0 l1,
      (den i f.fact l0 l1 ↔ den (revEdge i f.fact).1 (revEdge i f.fact).2 l1 l0) :=
  ⟨complete_premise_exact emitM_copies h (Exact.complete_demand hc),
    fun _ _ => complete_rev_exact emitM_copies h hc⟩

#print axioms complete_rev_exactM

end

/-! ## 10. `SatMark` is necessary

  The root `0` calls the method `1` and binds the zero location to `1`. The method `1` has a
  cleaner of the mark `0` (the zero mark) at the base `1`. The persisted record
  `(1,.,$,*∖{0}) → (1,.,$,*)` of the method `1` is exact: every location of the premise has a
  mark other than `0`, and it passes the cleaner. A satisfaction without `SatMark`
  (`fun _ _ => true`) lets the caller fact `(1,.,$,0)` use the record: the gate passes a premise
  `*∖x` without a check, and the result `(2,.,$,0)` is in the normal layer. But the cleaner
  removes the zero mark, so no real flow reaches `2` with the mark `0`. The program satisfies
  `Program.WF`, `MarkWF` and `FiltUp`, the restriction is `restrictU` (`RestrictSub`), and the
  records satisfy `RecsExact`: only `SatMark` is false. -/

namespace CexSat

def bnd : MicroEdge := (⟨0, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def back : MicroEdge := (⟨1, [], .exact, .star⟩, ⟨2, [], .exact, .star⟩)
def cc : Call := ⟨1, [0], [bnd], [back]⟩
def cl : Cleaner := ⟨1, [], .atAndBelow, some 0⟩
def P : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .call cc, 1), (1, 0, .clean cl, 1)]⟩

/-- The record premise `*∖{0}` and the record conclusion `*`. -/
def j : PFact := ⟨1, [], .exact, .starEx [0]⟩
def g : AFact := ⟨⟨1, [], .exact, .star⟩, false⟩
def recs : MethodId → PFact × AFact → Prop := fun m jg => m = 1 ∧ jg = (j, g)

def cnt : Acc → Bool := fun _ => true
def demand : MethodId → DemandEdge → Prop := fun _ _ => False
def emit : PFact → PFact → Option PFact := fun _ _ => none
def sat : PFact → PFact → Bool := fun _ _ => true

def a : AFact := ⟨⟨1, [], .exact, .conc 0⟩, false⟩
def r : AFact := ⟨⟨1, [], .exact, .conc 0⟩, false⟩
def r' : AFact := ⟨⟨2, [], .exact, .conc 0⟩, false⟩
def lEnd : Loc := ⟨2, [], 0⟩

theorem wf : P.WF where
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
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  filtPrefix := by
    intro M n b may n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem markWF : Exact.MarkWF P where
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
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem filtUp : Exact.FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h => cases h

/-- The record is exact: its pairs are the identity on the locations `1` with a mark other
    than `0`, and these pass the cleaner. -/
theorem recsExact : RecsExact P recs := by
  intro m j' g' hr _ l1 l2 hd
  obtain ⟨rfl, hjg⟩ := hr
  cases hjg
  obtain ⟨h1b, h2b, h1m, h2m, -, σ, τ, h1p, h2p, hσ, hτ⟩ := hd
  have hσ' : σ = [] := hσ
  have hτ' : τ = [] := hτ
  have hm : memB l1.mark [0] = false := h1m
  have e1 : l1 = ⟨1, [], l1.mark⟩ := Confirmed.loc_eq h1b (by rw [h1p, hσ']; rfl) rfl
  have e2 : l2 = l1 := by
    rw [e1]
    exact Confirmed.loc_eq h2b (by rw [h2p, hτ']; rfl) h2m
  rw [e2]
  have hcl : cl.cleansB l1 = false := by
    apply Exact.cleansB_mark
    have h0 : (Nat.beq l1.mark 0 || false) = false := hm
    rw [Bool.or_false] at h0
    exact h0
  exact Flow.clean (Flow.start 1 l1) (List.Mem.tail _ (List.Mem.head _)) hcl

theorem not_satMark : ¬ SatMark sat := by
  intro h
  have h1 := h j a.fact rfl
  exact absurd h1 (by decide)

theorem dr_edge : DR P cnt 3 demand emit sat restrictU recs [] [0] (.edge 0 zeroFact 1 r') := by
  have h0 : DR P cnt 3 demand emit sat restrictU recs [] [0] (.init 0 zeroFact) :=
    DR.root (List.Mem.head _)
  have h1 := DR.start h0
  have hlim : limitF cnt 3 r' = r' := rfl
  have h2 := DR.retRec (a := a) (j := j) (g := g) (r := r) (r' := r') (e1 := bnd) (e2 := back)
    h1 (List.Mem.head _) (List.Mem.head _) (by decide) ⟨rfl, rfl⟩ rfl (by decide)
    (List.Mem.head _) (by decide)
  rw [hlim] at h2
  exact h2

/-- In the method `1`, the location `1` with the zero mark flows nowhere: the cleaner
    removes it. -/
theorem flow1 : ∀ {M l0 n l}, Flow P M l0 n l → M = 1 → l0 = ⟨1, [], 0⟩ → n = 0 ∧ l = l0 := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro _ _; exact ⟨rfl, rfl⟩
  | step _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | pass _ hE _ _ =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | clean _ hE hcl ih =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        obtain ⟨_, hll⟩ := ih rfl hl
        rw [hll, hl] at hcl
        exact absurd hcl (by decide)
      | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- In the method `0`, the zero location flows nowhere: the call enters the method `1`, where the
    cleaner removes the zero mark. -/
theorem flow0 : ∀ {M l0 n l}, Flow P M l0 n l → M = 0 → l0 = zeroLoc → n = 0 ∧ l = l0 := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro _ _; exact ⟨rfl, rfl⟩
  | step _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | pass _ hE hm ih =>
    intro hM hl
    cases hE with
    | head =>
      obtain ⟨_, hll⟩ := ih rfl hl
      rw [hll, hl] at hm
      exact absurd hm (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ hE he1 hd1 hfc _ _ ih1 _ =>
    intro hM hl
    cases hE with
    | head =>
      obtain ⟨_, hll⟩ := ih1 rfl hl
      cases he1 with
      | head =>
        obtain ⟨-, h1b, -, h1m, -, σ, τ, -, h1p, -, hτ⟩ := hd1
        have hτ' : τ = [] := hτ
        have hl1 : l1 = ⟨1, [], 0⟩ := by
          refine Confirmed.loc_eq h1b (by rw [h1p, hτ']; rfl) ?_
          rw [h1m, hll, hl]
          rfl
        have h2 := (flow1 hfc rfl hl1).1
        exact absurd h2 (by decide)
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | clean _ hE _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- THE SATISFACTION COUNTEREXAMPLE. All hypotheses of `edge_exactR` except `SatMark` hold. The
    edge `zeroFact → (2,.,$,0)` at the exit of the root is in the normal layer and denotes the
    pair `(zero location, 2)`, but no real flow reaches `2`. -/
theorem cex_sat :
    P.WF ∧ Exact.MarkWF P ∧ Exact.FiltUp P ∧ RestrictSub restrictU ∧ RecsExact P recs ∧
    ¬ SatMark sat ∧
    DR P cnt 3 demand emit sat restrictU recs [] [0] (.edge 0 zeroFact 1 r') ∧
    r'.demand = false ∧ den zeroFact r'.fact zeroLoc lEnd ∧ ¬ Flow P 0 zeroLoc 1 lEnd := by
  refine ⟨wf, markWF, filtUp, restrictU_sub, recsExact, not_satMark, dr_edge, rfl,
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩, ?_⟩
  intro h
  have h1 := (flow0 h rfl rfl).1
  exact absurd h1 (by decide)

end CexSat

#print axioms CexSat.wf
#print axioms CexSat.recsExact
#print axioms CexSat.dr_edge
#print axioms CexSat.cex_sat

end ApSpec.RExact
