/-
  ApSpec.HandoffXCoverage — the forward contract `CoversN` of `HandoffDefs.lean` (decision F70) for
  the restricted forward run WITH THE `[any-taint]` EXCLUSION (decision F69), read on the forgotten
  view, and run 1 with the exclusion.

  The restricted run is `DRX P taint counted L dem emitX satX restrictIX recs sinks roots`
  (`AnyTaintExDefs.lean`, the restriction `restrictIX` of `HandoffXRestrict.lean`). The hand-off and
  the reports read it WITHOUT ITS EXCLUSIONS and must flags (`AnyTaintExCov.forgetX`). Its input
  witness is `Handoff.FlowRR` / `ReachRR` (every call that returns is demanded or crossed by a
  crossable base record of `rc`); a base record `(j, g)` is read by the run as the X record
  `(j, false, Excl.empty, ⟨g, Excl.empty⟩)` (`RecsEmbed`): not must, no exclusion, so `recLayerX`
  does not demote its result.

  Results (constructive; see the `#print axioms` lines):
    XC1 `cross_appliesX`     `CrossSatX satX`: a crossable base premise that covers a location of a
                             concrete added fact (with its exclusion) is satisfied by it (`satX`)
                             or covers it (`applicable`).
    XC2 `coverageRXI`        THE COVERAGE THEOREM of `DRX` for `FlowRR` (generic rules, with the
                             contracts `EmitContractX`, `EmitCopiesMarkX`, `EmitInsideX`,
                             `RestrictInsideX`, `CrossSatX`), and the justified flow
                             `FlowRDN P (forgetX DRX) (pubRXw …) rc`. A demanded call: the
                             emission inside `D-c` (with its mark: the added fact is concrete) and
                             the mark-aware intersection keep the pair (rule `ret`; `FlowRR.call`
                             gives the exit location with its mark in `D-p`, F71).
                             A recorded call: the embedded record (rule `retRec`, no demotion).
    XC3 `reach_strongRXI`, `coversN_DRXI_gen`: the witness form and THE FORWARD CONTRACT.
    XC4 `coversN_DRXI`       THE FORWARD CONTRACT OF THE SPEC RUN (`emitX`, `satX`, `restrictIX`):
                             `CoversN P roots sinks dem rc (forgetX DRX…) (pubRX P DRX… dem)`.
                             Hypotheses: `P.WF` and the record embedding `RecsEmbed rc recs`.
    XC5 `run0X_contract`     RUN 1 WITH THE EXCLUSION (`D6X … policy1 …`, read by `forget6`)
                             justifies every real witness (`ReachRDN … pubD (no record)`) and
                             reports it: `HandoffIter.Run0Contract`.
-/
import ApSpec.HandoffXRestrict
import ApSpec.HandoffCoverage
import ApSpec.HandoffIter

namespace ApSpec.HandoffX
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.Handoff
open ApSpec.AnyTaintExCov (forgetX forget6)

/-! ## 0. The contracts of the generic rules -/

/-- The emission gives, for a CONCRETE added fact, a premise that lies inside its entry pattern,
    with its exclusion and its mark (`insideXB`; the mark-aware restriction, F71). -/
def EmitInsideX (emit : PFact → PFact → Excl → Option (PFact × Excl)) : Prop :=
  ∀ d a aex j jex t, a.mark = .conc t → emit d a aex = some (j, jex) → insideXB j jex d = true

/-- C5 of the intersection with exclusions, MARK-AWARE (F71): if the premise (with its exclusion)
    lies inside `D-c` in its locations and marks, a pair of the edge whose exit location (with its
    mark) `D-p` covers stays, in the same layer. -/
def RestrictInsideX (restrict : PFact → Excl → XFact → DemandEdge → Option XFact) : Prop :=
  ∀ j jex g d p l1 l2, insideXB j jex d.din = true → denX j jex g.af.fact g.ex l1 l2 →
    d.dout = some p → p.covers l2 →
    ∃ g', restrict j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand

/-- A crossable base premise (`$`, or `*` with the Empty exclusion, no premise exclusion) that
    covers a location of a concrete added fact `(a, aex)` is satisfied by it or covers it. -/
def CrossSatX (sat : PFact → Excl → PFact → Excl → Bool) : Prop :=
  ∀ j a aex l t, CrossK j.kind → j.covers l → coversX a aex l → a.mark = .conc t →
    sat j Excl.empty a aex = true ∨ applicable j a = true

/-- THE RECORD EMBEDDING: every crossable base record `(j, g)` of `rc` is the X record
    `(j, false, Excl.empty, ⟨g, Excl.empty⟩)` of the run (not must, no exclusion). -/
def RecsEmbed (rc : Recs) (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j g, rc m (j, g) → Cross j g → recs m (j, false, Excl.empty, ⟨g, Excl.empty⟩)

/-- The spec restriction has the contract `RestrictInsideX` (X2). -/
theorem restrictIX_inside_contract : RestrictInsideX restrictIX :=
  fun _ _ _ _ _ _ _ hin hden hdout hp => restrictIX_contract hin hden hdout hp

/-- The spec emission has the contract `EmitInsideX` (X3, mark-aware: `emitX_insideXB`). -/
theorem emitX_insideX : EmitInsideX emitX :=
  fun _ _ _ _ _ _ ha h => emitX_insideXB h ha

/-- A record that is not must is never demoted. -/
theorem recLayerX_false (s : Bool) (x : XFact) : recLayerX false s x = x := by
  unfold recLayerX
  cases s <;> rfl

#print axioms restrictIX_inside_contract
#print axioms emitX_insideX
#print axioms recLayerX_false

/-! ## 1. XC1: a crossable record applies to a concrete annotated fact -/

theorem applicable_starEmpty {j a : PFact} (hk : j.kind = .star Excl.empty) (hb : j.base = a.base)
    (hms : markSubB j.mark a.mark = true) {r : List Acc} (hq : a.path = j.path ++ r) :
    applicable j a = true := by
  unfold applicable coversB
  rw [hb, Nat.beq_refl, hms, hk, CoreAux.dropPrefix_some.mpr hq]
  cases r with
  | nil => rw [RCore.tailSubB_starEmpty]; rfl
  | cons x r' => rfl

theorem insideExB_at {j a : PFact} {jex aex : Excl} (hq : a.path = j.path)
    (h : aex.subB ((tailExcl j.kind).union jex) = true) : insideExB j jex a aex = true := by
  unfold insideExB
  rw [hq, RCore.relate_self]
  exact h

theorem insideExB_below {j a : PFact} {jex aex : Excl} {x : Acc} {r : List Acc}
    (hq : j.path = a.path ++ x :: r) (h : aex.admits (x :: r) = true) :
    insideExB j jex a aex = true := by
  unfold insideExB
  rw [hq, CoreAux.relate_below (Store.dropPrefix_append _ _)]
  exact h

/-- XC1. A crossable base premise `j` and a concrete added fact `(a, aex)` with a common admitted
    location: `a` satisfies `j` with the exclusions (`satX`), or `j` covers `a` (`applicable`).
    `$`: `a` lies at or above the one path of `j`; at it, `aex` excludes at most the Universe of
    `$`; above it, `aex` admits the step (the common location is admitted). `*/{}`: `a` at or below
    `j` gives `applicable`; `a` above `j` gives `satX` (as for `$`). -/
theorem cross_appliesX : CrossSatX satX := by
  intro j a aex l t hk hj ha ht
  have hc := cross_applies hk hj (coversX_covers ha) ⟨t, ht⟩
  obtain ⟨hba, ⟨τ, hpa, _, hea⟩, hma⟩ := ha
  obtain ⟨hbj, ⟨σ, hpj, htj⟩, hmj⟩ := hj
  have hlt : l.mark = t := by rw [ht] at hma; exact hma
  have hms : markSubB j.mark a.mark = true := by
    rw [ht, ← hlt]
    exact RAux.markSubB_of_conc hmj
  have hpath : j.path ++ σ = a.path ++ τ := by rw [← hpj, ← hpa]
  have mkSat : satI j a = true → insideExB j Excl.empty a aex = true →
      satX j Excl.empty a aex = true := by
    intro h1 h2
    unfold satX
    rw [h1, h2]
    rfl
  rcases CoreAux.relate_common hpath with ⟨r, _, hq, hσ⟩ | ⟨r, _, hP, hr, hτ⟩
  · -- `a` at or below `j`
    cases hjk : j.kind with
    | any => rw [hjk] at hk; exact hk.elim
    | exact =>
      rw [hjk] at htj
      have hσ0 : σ = [] := htj
      rw [hσ0] at hσ
      have hr0 : r = [] := (List.append_eq_nil_iff.mp hσ.symm).1
      rw [hr0, List.append_nil] at hq
      rcases hc with hs | hap
      · left
        refine mkSat hs (insideExB_at hq ?_)
        rw [hjk]
        exact Invariant.subB_univ _
      · exact Or.inr hap
    | star e =>
      rw [hjk] at hk
      have he : e = Excl.empty := hk
      right
      exact applicable_starEmpty (by rw [hjk, he]) (hbj.symm.trans hba) hms hq
  · -- `a` strictly above `j`
    rcases hc with hs | hap
    · left
      cases r with
      | nil => exact absurd rfl hr
      | cons x r' =>
        refine mkSat hs (insideExB_below hP ?_)
        rw [hτ] at hea
        exact AnyTaintExCov.admits_prefix hea
    · exact Or.inr hap

#print axioms applicable_starEmpty
#print axioms insideExB_at
#print axioms insideExB_below
#print axioms cross_appliesX

/-! ## 2. XC2-XC4: the restricted forward run with the exclusion -/

section CoverageNX
open ApSpec.AnyTaintExCov
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (dem : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop) (rc : Recs)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "DRXr" => DRX P taint counted L dem emit sat restrict recs sinks roots

/-- XC2. THE COVERAGE THEOREM OF A RESTRICTED RUN WITH THE EXCLUSION AND THE NEW HAND-OFF. If a
    premise `(i, mi, iex)` of `M` covers the entry location `l0` in its admitted location set, and
    the value at `l0` flows to `l` at `n` along a flow whose calls are demanded or recorded
    (`FlowRR`), then an edge of the premise at `n` covers the pair (exclusions read), and the run,
    read on the forgotten view, justifies the flow (`FlowRDN`, each call by a published piece of
    `pubRXw` or by a crossable record of `rc`). The run has no request (`concX_all`). -/
theorem coverageRXI (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hEi : EmitInsideX emit) (hR : RestrictInsideX restrict) (hC : CrossSatX sat)
    (hrec : RecsEmbed rc recs)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowRR P dem rc M l0 n l) :
    ∀ i mi iex, DRXr (.init M i mi iex) → coversX i iex l0 →
      ∃ f, DRXr (.edge M i mi iex n f) ∧ denX i iex f.af.fact f.ex l0 l ∧
        FlowRDN P (forgetX DRXr) (pubRXw P DRXr restrict dem) rc M l0 n l := by
  have hcx : ∀ {o}, DRXr o → ConcX o :=
    fun h => concX_all P taint counted L dem emit sat restrict recs sinks roots hem h
  induction hfl with
  | start M l0 =>
    intro i mi iex hi hc
    exact ⟨_, DRX.start hi, startX_sound hc, FlowRDN.start M l0⟩
  | step _ he hs ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    rcases transferX_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ⟨r, DRX.step hf he hr, hdr, FlowRDN.step hfr he hs⟩
    · obtain ⟨_, ⟨t, ht⟩, _⟩ := hcx hf
      exact absurd ht (habs t)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    have hb : memB f.af.fact.base c.touched = false := by
      rw [← hd.2.1]
      exact hm
    exact ⟨f, DRX.pass hf he hb, hd, FlowRDN.pass hfr he hm⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 d p _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    -- the caller fact reaches the call; bind it into the callee
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := DRX.added hf he he1 ha
    have hacX : coversX a.af.fact a.ex l1 := denX_end hda
    obtain ⟨t, ht⟩ : ∃ t, a.af.fact.mark = .conc t := hcx hadd
    -- the demand edge covers `l1`: the emitted premise `(j, jex)` lies inside `D-c`
    obtain ⟨j, jex, hemit, hjc, hsat⟩ := hE d.din a.af.fact a.ex l1 t ht hdin hacX
    have hj := DRX.initR hadd hdem (emitTX_of hemit _)
    obtain ⟨g, hg, hdg, hfc'⟩ := ihc j _ jex hj hjc
    -- the intersection keeps the demanded pair (the premise lies inside `D-c` with its mark, and
    -- the demand edge covers the exit location with its mark: the restriction is mark-aware, F71)
    obtain ⟨g', hres, hdg', _⟩ := hR j jex g d p l1 l2 (hEi _ _ _ _ _ _ ht hemit) hdg hdout hp
    obtain ⟨r, hr, hdr⟩ := summary_stepConcX ht hda hdg'
    obtain ⟨r', hr', hdr'⟩ := bind_outX hwf he he2 hdr hd2
    exact ⟨_, DRX.ret hf he he1 ha hj hg hdem hres hsat hr he2 hr', limitFX_sound hdr',
      FlowRDN.call hfr he he1 hd1 hfc' ⟨_, hj, rfl⟩ ⟨_, hg, rfl⟩
        ⟨_, jex, g.ex, g'.ex, d, hg, hdem, hres⟩ (coversX_covers hjc) (denX_den hdg') he2 hd2⟩
  | @rcall M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := DRX.added hf he he1 ha
    obtain ⟨t, ht⟩ : ∃ t, a.af.fact.mark = .conc t := hcx hadd
    -- the crossable record applies to the concrete added fact
    have happ := hC j a.af.fact a.ex l1 t hcr.2.1 hjc (denX_end hda) ht
    obtain ⟨r, hr, hdr⟩ := summary_stepConcX (g := ⟨g, Excl.empty⟩) (jex := Excl.empty) ht hda
      (den_denX hdg)
    obtain ⟨r', hr', hdr'⟩ := bind_outX hwf he he2 hdr hd2
    have hret := DRX.retRec hf he he1 ha (hrec _ _ _ hrc hcr) happ hr he2 hr'
    rw [recLayerX_false] at hret
    exact ⟨_, hret, limitFX_sound hdr', FlowRDN.rcall hfr he he1 hd1 hrc hcr hjc hdg he2 hd2⟩
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    rcases cleanResX_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ⟨r, DRX.clean hf he hr, hdr, FlowRDN.clean hfr he hcl⟩
    · obtain ⟨_, ⟨t, ht⟩, _⟩ := hcx hf
      exact absurd ht (habs t)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    exact ⟨f, DRX.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) (denX_den hd) hl), hd,
      FlowRDN.filt hfr he hl⟩

#print axioms coverageRXI

/-- XC3. THE STRONG REACH STATEMENT: a demanded-or-recorded vulnerability witness is justified by
    the run (forgotten view), and an edge covers the pair at its end (exclusions read). -/
theorem reach_strongRXI (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hEi : EmitInsideX emit) (hR : RestrictInsideX restrict) (hC : CrossSatX sat)
    (hrec : RecsEmbed rc recs)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRR P dem rc roots M n l) :
    ReachRDN P (forgetX DRXr) (pubRXw P DRXr restrict dem) rc roots M n l ∧
    ∃ l0 i mi iex f, DRXr (.edge M i mi iex n f) ∧ denX i iex f.af.fact f.ex l0 l := by
  have hcx : ∀ {o}, DRXr o → ConcX o :=
    fun h => concX_all P taint counted L dem emit sat restrict recs sinks roots hem h
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverageRXI P taint counted L dem emit sat restrict recs rc sinks
      roots hwf hE hem hEi hR hC hrec hfl zeroFact false Excl.empty (DRX.root hM)
      (covers_coversX Coverage.zeroFact_covers)
    exact ⟨ReachRDN.root hM hfr, zeroLoc, zeroFact, false, Excl.empty, f, hf, hd⟩
  | @down M n l n' c e l1 n2 l2 d _ he he1 hd1 hdem hdin hfc ih =>
    obtain ⟨hRR, l0, i, mi, iex, f, hf, hd⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := DRX.added hf he he1 ha
    obtain ⟨t, ht⟩ : ∃ t, a.af.fact.mark = .conc t := hcx hadd
    obtain ⟨j, jex, hemit, hjc, _⟩ := hE d.din a.af.fact a.ex l1 t ht hdin (denX_end hda)
    have hj := DRX.initR hadd hdem (emitTX_of hemit _)
    obtain ⟨g, hg, hdg, hfr⟩ := coverageRXI P taint counted L dem emit sat restrict recs rc sinks
      roots hwf hE hem hEi hR hC hrec hfc j _ jex hj hjc
    exact ⟨ReachRDN.down hRR he he1 hd1 ⟨_, hj, rfl⟩ (coversX_covers hjc) hfr, l1, j, _, jex, g,
      hg, hdg⟩

#print axioms reach_strongRXI

/-- XC3. THE FORWARD CONTRACT of the restricted run with the exclusion, generic rules: every
    demanded-or-recorded witness of a sink pattern with a concrete mark is justified by the run
    (forgotten view), and the run reports its vulnerability (no request: the sink check
    triggers). -/
theorem coversN_DRXI_gen (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hEi : EmitInsideX emit) (hR : RestrictInsideX restrict) (hC : CrossSatX sat)
    (hrec : RecsEmbed rc recs) :
    CoversN P roots sinks dem rc (forgetX DRXr) (pubRXw P DRXr restrict dem) := by
  intro M n l s T hs hT hsc hRe
  obtain ⟨hRR, l0, i, mi, iex, f, hf, hd⟩ :=
    reach_strongRXI P taint counted L dem emit sat restrict recs rc sinks roots hwf hE hem hEi hR
      hC hrec hRe
  refine ⟨hRR, ?_⟩
  rcases checkX_sound hT hd hsc with htr | ⟨hrq, _⟩
  · exact ⟨_, _, DRX.vuln hf hs htr, rfl⟩
  · exact (noReqX P taint counted L dem emit sat restrict recs sinks roots hem
      (DRX.reqSink hf hs hrq)).elim

#print axioms coversN_DRXI_gen

end CoverageNX

/-- XC4. THE FORWARD CONTRACT OF THE SPEC RESTRICTED RUN WITH THE EXCLUSION AND THE INTERSECTION
    (`DRX … emitX satX restrictIX …`), read on the forgotten view with the publication `pubRX`.
    Hypotheses: S10 (`Program.WF`) and the record embedding (`RecsEmbed rc recs`). -/
theorem coversN_DRXI {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {rc : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (hrec : RecsEmbed rc recs) :
    CoversN P roots sinks dem rc
      (forgetX (DRX P taint counted L dem emitX satX restrictIX recs sinks roots))
      (pubRX P (DRX P taint counted L dem emitX satX restrictIX recs sinks roots) dem) :=
  coversN_DRXI_gen P taint counted L dem emitX satX restrictIX recs rc sinks roots hwf
    AnyTaintExCov.emitX_contract emitX_copies emitX_insideX restrictIX_inside_contract
    cross_appliesX hrec

#print axioms coversN_DRXI

/-! ## 3. XC5: run 1 with the exclusion -/

/-- XC5. RUN 1 WITH THE EXCLUSION (`D6X` with `policy1`, read by `forget6`) JUSTIFIES EVERY REAL
    WITNESS with the publication `pubD` and no record, and reports its vulnerability (from
    `AnyTaintExCov.vuln_found6X`). Only hypothesis: S10 (`Program.WF`). -/
theorem run0X_contract {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (hwf : P.WF) :
    HandoffIter.Run0Contract P roots sinks (forget6 (D6X P taint counted L policy1 sinks roots))
      pubD (fun _ _ => False) := by
  intro M n l s T hs hT hsc hRe
  obtain ⟨⟨b, hb⟩, hRR⟩ := AnyTaintExCov.vuln_found6X P taint counted L policy1 sinks roots hwf
    policy1_applicable hRe hs hT hsc
  exact ⟨reachRD_reachRDN hRR, b, _, hb, rfl⟩

#print axioms run0X_contract

end ApSpec.HandoffX
