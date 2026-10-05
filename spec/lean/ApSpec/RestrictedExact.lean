/-
  ApSpec.RestrictedExact — the PRECISION side of a restricted run (`DR`).

  `Exact.lean` proves that a normal-layer edge of the closure `D` denotes only real
  flows. This module proves the same for the restricted closure `DR` of
  `Restricted.lean`. The rules `initR`, `ret` (restricted) and `retRec` (persisted
  records) are new. Exactness is relative to the initial fact, so `emit` and `sat`
  need no hypothesis. Two hypotheses are necessary:
    * `RestrictSub restrict`: the restriction only removes pairs and keeps the layer
      (used in the case `ret`);
    * `RecsExact P recs`: a normal-layer persisted record denotes only real flows
      (used in the case `retRec`).
  The shape invariants (`Invariant.lean`, `Confirmed.D_NS`) need NO hypothesis: the
  caller fact alone gives the shape of the result of `applySummary`, the summary edge
  does not change it. So no shape hypothesis on `restrict`, `recs` or `emit` is used.

  Main results:
    1. `DR_edgeOK`, `edge_exactR`, `complete_exactR`  a normal-layer edge of `DR`
       denotes only real flows.
    2. `flowR_flow`, `closed_exactR`  a closed initial fact of a restricted run: every
       DEMANDED flow (`FlowR`) has a record, and every record is a real `Flow`.
    3. `recs_of_DR`, `recs_of_D`  the exit records of a run satisfy `RecsExact`, so a
       later run can reuse them (`recs_union`, `recs_mono` join and filter record sets).
    4. `DR_inv`, `final_star_legalR`, `star_final_keeps_initial_exclR`,
       `star_initial_completeR`, `DR_NS`  the shape invariants of `DR`.
    5. `SupR`, `ConfirmedR`, `sup_entryR`, `confirmed_realR`  a confirmed vulnerability
       of a restricted run is a real vulnerability (no false positive).
    6. `restrictU_sub`, `restrictS_sub`  both concrete restrictions satisfy
       `RestrictSub`; `confirmed_realU`, `confirmed_realS` are the instances.

  Version 4 (the spec rules `emitM`, `satO`, `restrictU`). One hypothesis:
  `EmitCopiesMark emit` (the emission copies the mark of the added fact; `emitM_copies`).
    7. `DR_concrete`  every initial fact, edge (premise and final fact) and added fact of
       the run has a concrete mark, and the run has no request object. Corollaries:
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
       confirmed vulnerability is a real vulnerability.

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

/-- The motive `Exact.EdgeOK` holds on every object of a restricted run. -/
theorem DR_edgeOK (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) : Exact.EdgeOK P o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro ha l0 l hd
    have e := Exact.startFact_exact ha hd
    rw [e]
    exact Flow.start M l0
  | @step M i n f n' s f' _ hE hf ih =>
    intro ha l0 l hd
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact hfa hf ha hd
    exact Flow.step (ih hfa l0 l1 hd1) hE hs
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    intro ha l0 l hd
    refine Flow.pass (ih ha l0 l hd) hE ?_
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ hres _ hr he2 hr' ihD _ ihG =>
    intro hla l0 l hd
    have e := Exact.limitF_exact hla
    rw [e] at hd hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hra hr' hla hd
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, hga'⟩ := Exact.or_eq_false hra
    have haa := Exact.applyEdge_demand hx hxa
    have hfa := Exact.applyEdge_demand ha haa
    -- the middle pair is a pair of the restricted edge `g'`
    obtain ⟨l1', hd1', hdg'⟩ := Exact.applyEdge_exact haa hx hxa hd2
    -- `RestrictSub`: it is a pair of the summary edge `g`, in the same layer
    obtain ⟨hgd, hgsub⟩ := hsub j g d g' hres
    have hga : g.demand = false := hgd.symm.trans hga'
    obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hfa ha haa hd1'
    exact Flow.call (ihD hfa l0 l1 hd1) hE he1 hde1 (ihG hga l1' l2 (hgsub l1' l2 hdg')) he2 hde2
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec _ hr he2 hr' ihD =>
    intro hla l0 l hd
    have e := Exact.limitF_exact hla
    rw [e] at hd hla
    have hra := Exact.applyEdge_demand hr' hla
    obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hra hr' hla hd
    obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
    obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
    have haa := Exact.applyEdge_demand hx hxa
    have hfa := Exact.applyEdge_demand ha haa
    obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact haa hx hxa hd2
    obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hfa ha haa hd1'
    -- `RecsExact`: a normal-layer record is a real callee flow
    exact Flow.call (ihD hfa l0 l1 hd1) hE he1 hde1 (hrecs c.callee j g hrec hga l1' l2 hdg) he2 hde2
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial

#print axioms DR_edgeOK

/-- 1. THE EXACTNESS THEOREM for a restricted run. A normal-layer edge of `DR` denotes
    only real flows. -/
theorem edge_exactR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  DR_edgeOK hsub hrecs h ha l0 l hd

#print axioms edge_exactR

/-- 1'. A complete edge of a restricted run denotes only real flows. -/
theorem complete_exactR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hc : f.complete = true) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  edge_exactR hsub hrecs h (Exact.complete_demand hc) hd

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

#print axioms flowR_flow

/-- 2. A closed initial fact of a restricted run. If the exit edges of `i` cover every
    DEMANDED flow (`hcov`) and every exit edge of `i` is in the normal layer (`hcomp`),
    then every demanded flow from the location set of `i` has a record, and every
    record of `i` is a real flow. With `flowR_flow`:
    `FlowR ⊆ records ⊆ Flow`. The records are not inside `FlowR` in general: the
    rule `retRec` and the rule `ret` with `restrictS` keep pairs outside the demand. -/
theorem closed_exactR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
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
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ => edge_exactR hsub hrecs hg (hcomp g hg) hd⟩

#print axioms closed_exactR

/-! ## 3. The records of a run are exact -/

/-- 3. The exit edges of a restricted run satisfy `RecsExact`. So the persisted records
    of a restricted run (complete exit edges, a subset: `recs_mono`) can be used again by
    a later run. -/
theorem recs_of_DR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (exitRecs P (DR P counted L demand emit sat restrict recs sinks roots)) :=
  fun _ _ _ hr hg _ _ hd => edge_exactR hsub hrecs hr hg hd

#print axioms recs_of_DR

/-- 3'. The complete exit edges of a restricted run (the persisted records) are exact. -/
theorem recs_complete_of_DR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (fun m jg =>
      exitRecs P (DR P counted L demand emit sat restrict recs sinks roots) m jg ∧
        jg.2.complete = true) :=
  recs_mono (fun _ _ h => h.1) (recs_of_DR hsub hrecs)

#print axioms recs_complete_of_DR

/-- 3''. The records of the run sequence: the records of earlier runs together with the
    exit edges of this run are exact. -/
theorem recs_step (hsub : RestrictSub restrict) (hrecs : RecsExact P recs) :
    RecsExact P (fun m jg => recs m jg ∨
      exitRecs P (DR P counted L demand emit sat restrict recs sinks roots) m jg) :=
  recs_union hrecs (recs_of_DR hsub hrecs)

#print axioms recs_step

end

/-- 3 (run 1). The exit edges of the closure `D` satisfy `RecsExact`. -/
theorem recs_of_D {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} :
    RecsExact P (exitRecs P (D P counted L α sinks roots)) :=
  fun _ _ _ hr hg _ _ hd => Exact.edge_exact hr hg hd

#print axioms recs_of_D

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

#print axioms DR_inv

/-- W2 and the demand-layer invariant for a restricted run: a final `*` fact has the
    mark `*` and is in the normal layer. -/
theorem final_star_legalR {M : MethodId} {i : PFact} {n : Node} {f : AFact} {e : Excl}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hk : f.fact.kind = .star e) : f.fact.mark = .star ∧ f.demand = false :=
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
    unique location is entry-reachable. -/
theorem sup_entryR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
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
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak
    rw [ham] at hden
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hfd ha had hden
    have hR := Confirmed.entry_reach P roots hent (edge_exactR hsub hrecs hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entryR

/-- 5. THE THEOREM for a restricted run: a confirmed vulnerability of ANY restricted run
    (any `demand`, `emit`, `sat`; a `restrict` that only removes pairs; exact persisted
    records) is a real concrete vulnerability (no false positive). -/
theorem confirmed_realR (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entryR hsub hrecs hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := DR_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo⟩ := Confirmed.check_triggered him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩, ?_, ?_⟩
  · exact Confirmed.entry_reach P roots hent
      (edge_exactR hsub hrecs hD hfd (Confirmed.den_exact_exact him hfk))
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
  obtain ⟨h0b, h2b, h0m, h2m, σ, τ, h0p, h2p, hI, _⟩ := h
  exact ⟨h0b, h2b, h0m, h2m, σ, r ++ τ, h0p, by rw [h2p, List.append_assoc], hI, trivial⟩

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
    any emission, any satisfaction, exact persisted records) is a real vulnerability. -/
theorem confirmed_realS {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hrecs : RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrictS recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realR restrictS_sub hrecs h

#print axioms confirmed_realS

/-- 5 (U rules). The same for a run with the U restriction. -/
theorem confirmed_realU {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hrecs : RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedR P counted L demand emit sat restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realR restrictU_sub hrecs h

#print axioms confirmed_realU

/-! ## 7. Version 4: a restricted run is CONCRETE

  The run starts from the zero fact (concrete mark). The rules keep a concrete mark:
    * a statement, a call binding and a summary application keep a concrete caller mark
      (`transfer_mark_conc`, `applyEdge_mark_conc`, `applySummary_mark_conc`), for ANY
      summary edge and ANY persisted record;
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

/-- The premise-layer motive: a normal-layer edge has an exact premise or a `*`-mark premise.
    (A premise with a concrete mark and a `*` or `[any]` tail starts in the demand layer, and
    the demand layer never goes back.) -/
def PremLayer : Obj → Prop
  | .edge _ i _ f => f.demand = false → i.kind = .exact ∨ i.mark = .star
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
    rw [check_request_star hc] at h0
    cases h0
  | answer _ _ _ _ ihR _ => exact ihR.elim
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact ihR.elim
  | vuln => trivial

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

/-- W2 in a concrete run: no final fact has the `*` tail (a `*` final fact has the mark `*`). -/
theorem final_not_star (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f)) :
    f.fact.kind.isStar = false := by
  cases hk : f.fact.kind with
  | star e =>
    have h1 := (final_star_legalR P counted L demand emit sat restrict recs sinks roots h hk).1
    obtain ⟨_, t, ht⟩ := DR_concrete hem h
    rw [h1] at ht
    cases ht
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

#print axioms DR_premLayer

/-- 8. A normal-layer edge of a concrete run has an EXACT premise. -/
theorem complete_premise_exact (hem : EmitCopiesMark emit) {M : MethodId} {i : PFact}
    {n : Node} {f : AFact}
    (h : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hd : f.demand = false) : i.kind = .exact := by
  rcases DR_premLayer h hd with hk | hm
  · exact hk
  · obtain ⟨⟨t, ht⟩, _⟩ := DR_concrete hem h
    rw [hm] at ht
    cases ht

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

/-- A supported initial fact (generalized support) is exact with a concrete mark, and its
    unique location is entry-reachable. -/
theorem sup_entryM (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {i : PFact}
    (h : SupM P counted L demand emit sat restrict recs sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      Confirmed.EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    have hJ : ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
      rcases hj with ⟨hj0, hz⟩ | ⟨hak, ⟨t, ham⟩, hja⟩
      · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
      · exact ⟨t, hak, ham, hja⟩
    obtain ⟨t, hak, ham, rfl⟩ := hJ
    have hden := Confirmed.den_exact_exact (a := a.fact) him hak
    rw [ham] at hden
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hfd ha had hden
    have hR := Confirmed.entry_reach P roots hent (edge_exactR hsub hrecs hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entryM

/-- 10. THE THEOREM with the generalized support: a confirmed vulnerability of ANY
    restricted run (any `demand`, `emit`, `sat`; a `restrict` that only removes pairs; exact
    persisted records) is a real concrete vulnerability (no false positive). -/
theorem confirmed_realM_gen (hsub : RestrictSub restrict) (hrecs : RecsExact P recs)
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entryM hsub hrecs hS
  have hfd := Exact.complete_demand hc
  have hns : f.fact.kind.isStar = false := DR_NS hD (by rw [hik]; rfl)
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo⟩ := Confirmed.check_triggered him hch
  refine ⟨⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩, ?_, ?_⟩
  · exact Confirmed.entry_reach P roots hent
      (edge_exactR hsub hrecs hD hfd (Confirmed.den_exact_exact him hfk))
  · exact Confirmed.overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)

#print axioms confirmed_realM_gen

end

/-! ## 9. Version 4: the spec rules `emitM`, `satO`, `restrictU` -/

section
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- 10 (spec rules). A confirmed vulnerability of a version-4 run (`emitM`, `satO`,
    `restrictU`; any demand; exact persisted records) is a real vulnerability. -/
theorem confirmed_realM (hrecs : RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM P counted L demand emitM satO restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_realM_gen restrictU_sub hrecs h

#print axioms confirmed_realM

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

end ApSpec.RExact
