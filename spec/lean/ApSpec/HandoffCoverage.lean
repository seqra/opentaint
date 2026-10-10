/-
  ApSpec.HandoffCoverage — the forward contract `CoversN` of `HandoffDefs.lean` (decision F70):
  a restricted forward run with the intersection `restrictI` justifies every demanded-or-recorded
  witness and reports its vulnerability; run 1 justifies every real witness.

  Results (constructive; see the `#print axioms` lines):
    C1 `cross_applies`     a crossable premise (`$`, or `*` with the Empty exclusion) that covers
                           a location of a concrete added fact is satisfied by it (`satI`) or
                           covers it (`applicable`): the record applies (rule `DR.retRec`).
    C2 `coverageRN`        THE COVERAGE THEOREM of `DR P counted L dem emitM satI restrictI rc …`
                           for a flow `FlowRR P dem rc`: an edge of the initial fact covers the
                           pair, and the flow is justified by the run (`FlowRDN … (pubR dem) rc`).
                           A demanded call: the emission (`emitM_contract_I`), the premise inside
                           `D-c` (`emitM_inside`), the restriction (`restrictI_contract`), the
                           application (`RCov.sat_step`), the binding back (`bind_out`), rule
                           `DR.ret`. A recorded call: `cross_applies`, `RCov.sat_step` or
                           `Coverage.summary_step`, rule `DR.retRec`. The run is concrete
                           (`RCov.concInvR_all`), so it has no request.
    C3 `reach_strongRN`    the same for a vulnerability witness `ReachRR` (gives `ReachRDN`).
    C4 `coversN_DR`        THE FORWARD CONTRACT `CoversN` for the restricted run. Only `P.WF` is
                           necessary: the run has no request, so the sink tails do not matter.
    C5 `run1_justifies`    run 1 (`D … policy1 …`) justifies every real witness
                           (`ReachRDN … pubD (fun _ _ => False)`) and reports its vulnerability.
                           `run1_reachRDN`: the witness part alone.
-/
import ApSpec.HandoffRestrict

namespace ApSpec.Handoff
open ApSpec ApSpec.Reverse ApSpec.Handoff.RAux

/-! ## 1. C1: a crossable record applies to a concrete fact -/

namespace RAux

/-- A premise mark that admits the mark of a location admits the concrete fact mark of that
    location. -/
theorem markSubB_of_conc {jm : MarkA} {m : Mark} (h : jm.admits m) :
    markSubB jm (.conc m) = true := by
  cases jm with
  | star => rfl
  | conc t =>
    have ht : m = t := h
    show Nat.beq t m = true
    rw [ht]
    exact Nat.beq_refl t
  | starEx x =>
    have hx : memB m x = false := h
    show (!memB m x) = true
    rw [hx]
    rfl

end RAux

/-- C1. A crossable premise `j` (`$`, or `*` with the Empty exclusion) and a concrete added fact
    `a` with a common location: `a` satisfies `j` (`satI`: the location part of `a` covers `j`) or
    `j` covers `a` (`applicable`). For `$`: `a` lies at or above the one path of `j`, so `satI`.
    For `*/{}`: `a` at or below `j` gives `applicable`, `a` above `j` gives `satI`. An `[any]`
    premise is not crossable (`CrossK`). -/
theorem cross_applies {j a : PFact} {l : Loc} (hk : CrossK j.kind) (hj : j.covers l)
    (ha : a.covers l) (hc : ∃ t, a.mark = .conc t) :
    satI j a = true ∨ applicable j a = true := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨hbj, ⟨σ, hpj, htj⟩, hmj⟩ := hj
  obtain ⟨hba, ⟨τ, hpa, hta⟩, hma⟩ := ha
  have hlt : l.mark = t := by rw [ht] at hma; exact hma
  have hms : markSubB j.mark a.mark = true := by
    rw [ht, ← hlt]
    exact markSubB_of_conc hmj
  have hb : Nat.beq a.base j.base = true := by rw [← hba, ← hbj]; exact Nat.beq_refl _
  have hb' : Nat.beq j.base a.base = true := by rw [← hba, ← hbj]; exact Nat.beq_refl _
  have hpath : j.path ++ σ = a.path ++ τ := by rw [← hpj, ← hpa]
  -- `satI` from the location part of `a` covering `j`
  have mkSat0 : dropPrefix a.path j.path = some [] → tailSubB a.kind j.kind = true →
      satI j a = true := by
    intro hdp hr
    unfold satI coversB
    dsimp only
    (rw [hb, hdp, hms, hr]) <;> rfl
  have mkSat1 : ∀ x r', dropPrefix a.path j.path = some (x :: r') →
      admitsTailB a.kind (x :: r') = true → satI j a = true := by
    intro x r' hdp hr
    unfold satI coversB
    dsimp only
    rw [hb, hdp, hms]
    dsimp only
    (rw [hr]) <;> rfl
  rcases CoreAux.relate_common hpath with ⟨r, _, hq, hσ⟩ | ⟨r, _, hP, hr, hτ⟩
  · -- `a` is at or below `j`
    cases hjk : j.kind with
    | any => rw [hjk] at hk; exact hk.elim
    | exact =>
      -- `j` has one location: `a` is at its path
      rw [hjk] at htj
      have hσ0 : σ = [] := htj
      rw [hσ0] at hσ
      have hr0 : r = [] := (List.append_eq_nil_iff.mp hσ.symm).1
      rw [hr0, List.append_nil] at hq
      left
      apply mkSat0
      · rw [hq]; exact dropPrefix_self' j.path
      · rw [hjk]
        cases a.kind with
        | star e => rfl
        | any => rfl
        | exact => rfl
    | star e =>
      -- `j` is `*/{}`: it covers `a`
      rw [hjk] at hk
      have he : e = Excl.empty := hk
      right
      unfold applicable coversB
      rw [hb', hms, hjk, he, CoreAux.dropPrefix_some.mpr hq]
      cases r with
      | nil => rw [RCore.tailSubB_starEmpty]; rfl
      | cons x r' => rfl
  · -- `a` is strictly above `j`: the location part of `a` covers `j`
    left
    cases r with
    | nil => exact absurd rfl hr
    | cons x r' =>
      apply mkSat1 x r' (CoreAux.dropPrefix_some.mpr hP)
      rw [hτ] at hta
      exact CoreAux.tailI_append_admits hta

#print axioms markSubB_of_conc
#print axioms cross_applies

/-! ## 2. C2-C4: the restricted forward run -/

section CoverageN
open ApSpec.Coverage ApSpec.RCov
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (dem : MethodId → DemandEdge → Prop) (rc : Recs)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "DRr" => DR P counted L dem emitM satI restrictI rc sinks roots

/-- Every added fact of the restricted run has a concrete mark. -/
theorem added_concN {m : MethodId} {a : PFact} (h : DRr (.added m a)) : ∃ t, a.mark = .conc t :=
  RCov.added_concR P counted L dem emitM satI restrictI rc sinks roots RCov.emitM_copies h

/-- The restricted run has no request. -/
theorem no_reqN {M : MethodId} {i : PFact} {t : Mark} : ¬ DRr (.req M i t) :=
  RCov.no_reqR P counted L dem emitM satI restrictI rc sinks roots RCov.emitM_copies

#print axioms added_concN
#print axioms no_reqN

/-- C2. THE COVERAGE THEOREM OF A RESTRICTED RUN WITH THE INTERSECTION. If the initial fact `i` of
    `M` is in the run and covers the entry location `l0`, and the value at `l0` flows to `l` at
    the node `n` along a flow whose calls are demanded or recorded (`FlowRR`), then an edge of `i`
    at `n` covers the pair, and the run justifies the flow (`FlowRDN`, each call by a published
    piece of `pubR dem` or by a crossable record of `rc`). -/
theorem coverageRN (hwf : P.WF) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hfl : FlowRR P dem rc M l0 n l) :
    ∀ i, DRr (.init M i) → i.covers l0 →
      ∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowRDN P DRr (pubR dem) rc M l0 n l := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact ⟨_, DR.start hi, startFact_sound hc, FlowRDN.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
    · exact ⟨r, DR.step hf he hr, hdr, FlowRDN.step hfr he hs⟩
    · exact absurd (DR.reqStmt hf he hq) (no_reqN P counted L dem rc sinks roots)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    have hb : memB f.fact.base c.touched = false := by
      rw [← hd.2.1]
      exact hm
    exact ⟨f, DR.pass hf he hb, hd, FlowRDN.pass hfr he hm⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 d p _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    -- The caller fact reaches the call. Bind it into the callee.
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := DR.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    obtain ⟨t, ht⟩ := added_concN P counted L dem rc sinks roots hadd
    -- The demand edge of the callee covers `l1`: the emission gives the initial fact `j`,
    -- which lies inside `D-c`.
    obtain ⟨j, hemit, hjc, hsat⟩ := RCore.emitM_contract_I d.din a.fact l1 t ht hdin hac
    have hj := DR.initR hadd hdem hemit
    obtain ⟨g, hg, hdg, hfc'⟩ := ihc j hj hjc
    -- The intersection keeps the demanded pair.
    obtain ⟨g', hres, hdg', _⟩ := restrictI_contract (emitM_inside hemit) hdg hdout hp
    obtain ⟨r, hr, hdr⟩ := sat_step RCore.satI_contract hsat hda hdg'
    obtain ⟨r', hr', hdr'⟩ := bind_out hwf he he2 hdr hd2
    exact ⟨_, DR.ret hf he he1 ha hj hg hdem hres hsat hr he2 hr', limitF_sound hdr',
      FlowRDN.call hfr he he1 hd1 hfc' hj hg ⟨d, hdem, hres⟩ hjc hdg' he2 hd2⟩
  | @rcall M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := DR.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    -- The crossable record applies to the concrete added fact.
    have happ := cross_applies hcr.2.1 hjc hac (added_concN P counted L dem rc sinks roots hadd)
    obtain ⟨r, hr, hdr⟩ : ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
      rcases happ with hs | hap
      · exact sat_step RCore.satI_contract hs hda hdg
      · exact summary_step hap hda hdg
    obtain ⟨r', hr', hdr'⟩ := bind_out hwf he he2 hdr hd2
    exact ⟨_, DR.retRec hf he he1 ha hrc happ hr he2 hr', limitF_sound hdr',
      FlowRDN.rcall hfr he he1 hd1 hrc hcr hjc hdg he2 hd2⟩
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
    · exact ⟨r, DR.clean hf he hr, hdr, FlowRDN.clean hfr he hcl⟩
    · exact absurd (DR.reqClean hf he hq) (no_reqN P counted L dem rc sinks roots)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i hi hc
    exact ⟨f, DR.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hd hl), hd,
      FlowRDN.filt hfr he hl⟩

#print axioms coverageRN

/-- C3. THE STRONG REACH STATEMENT: a demanded-or-recorded vulnerability witness is justified by
    the run, and an edge covers the pair at its end. -/
theorem reach_strongRN (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc}
    (hRe : ReachRR P dem rc roots M n l) :
    ReachRDN P DRr (pubR dem) rc roots M n l ∧
      ∃ l0 i f, DRr (.edge M i n f) ∧ den i f.fact l0 l := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverageRN P counted L dem rc sinks roots hwf hfl zeroFact
      (DR.root hM) zeroFact_covers
    exact ⟨ReachRDN.root hM hfr, zeroLoc, zeroFact, f, hf, hd⟩
  | @down M n l n' c e l1 n2 l2 d _ he he1 hd1 hdem hdin hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := DR.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    obtain ⟨t, ht⟩ := added_concN P counted L dem rc sinks roots hadd
    obtain ⟨j, hemit, hjc, _⟩ := RCore.emitM_contract_I d.din a.fact l1 t ht hdin hac
    have hj := DR.initR hadd hdem hemit
    obtain ⟨g, hg, hdg, hfr⟩ := coverageRN P counted L dem rc sinks roots hwf hfc j hj hjc
    exact ⟨ReachRDN.down hRR he he1 hd1 hj hjc hfr, l1, j, g, hg, hdg⟩

#print axioms reach_strongRN

/-- C4. THE FORWARD CONTRACT of the restricted run with the intersection: every
    demanded-or-recorded witness of a sink pattern with a concrete mark is justified by the run,
    and the run reports its vulnerability. The run has no request (it is concrete), so the sink
    check triggers. -/
theorem coversN_DR (hwf : P.WF) : CoversN P roots sinks dem rc DRr (pubR dem) := by
  intro M n l s T hs hT hsc hRe
  obtain ⟨hRR, l0, i, f, hf, hd⟩ := reach_strongRN P counted L dem rc sinks roots hwf hRe
  refine ⟨hRR, ?_⟩
  rcases check_sound hT hd hsc with htr | ⟨hrq, _⟩
  · exact ⟨_, DR.vuln hf hs htr⟩
  · exact absurd (DR.reqSink hf hs hrq) (no_reqN P counted L dem rc sinks roots)

#print axioms coversN_DR

end CoverageN

/-! ## 3. C5: run 1 justifies every real witness -/

/-- A den-aware flow of a run is justified by that run with the publication `pubD` (each exit edge
    as it is) and no record. -/
theorem flowRD_flowRDN {P : Program} {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : Backward.FlowRD P R M l0 n l) : FlowRDN P R pubD (fun _ _ => False) M l0 n l := by
  induction h with
  | start M l0 => exact FlowRDN.start M l0
  | step _ he hs ih => exact FlowRDN.step ih he hs
  | pass _ he hm ih => exact FlowRDN.pass ih he hm
  | call _ he he1 hd1 _ hj hg hjc hdg he2 hd2 ih ihc =>
    exact FlowRDN.call ih he he1 hd1 ihc hj hg rfl hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRDN.clean ih he hcl
  | filt _ he hl ih => exact FlowRDN.filt ih he hl

theorem reachRD_reachRDN {P : Program} {R : Obj → Prop} {roots : List MethodId} {M : MethodId}
    {n : Node} {l : Loc} (h : Backward.ReachRD P R roots M n l) :
    ReachRDN P R pubD (fun _ _ => False) roots M n l := by
  induction h with
  | root hM hfl => exact ReachRDN.root hM (flowRD_flowRDN hfl)
  | down _ he he1 hd1 hj hjc hfc ih => exact ReachRDN.down ih he he1 hd1 hj hjc (flowRD_flowRDN hfc)

#print axioms flowRD_flowRDN
#print axioms reachRD_reachRDN

section Run1
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "D1" => D P counted L policy1 sinks roots

/-- The run-1 abstraction `policy1` serves every added fact (contract C1). -/
theorem policy1_applicable : ∀ m a, applicable (policy1 m a) a = true :=
  fun m a => policy_applicable (fun _ => []) m a

/-- C5, the witness part: run 1 justifies every real witness, with the publication `pubD` and no
    record. -/
theorem run1_reachRDN (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc}
    (hRe : Reach P roots M n l) : ReachRDN P D1 pubD (fun _ _ => False) roots M n l :=
  reachRD_reachRDN (Backward.reach_strongDD P counted L policy1 sinks roots hwf
    policy1_applicable hRe).1

/-- C5. RUN 1 JUSTIFIES EVERY REAL WITNESS of a sink pattern with a concrete mark, and reports its
    vulnerability (the `CoversN` form, with every real witness as the input). -/
theorem run1_justifies (hwf : P.WF) :
    ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l → Reach P roots M n l →
      ReachRDN P D1 pubD (fun _ _ => False) roots M n l ∧ ∃ b, D1 (.vuln M n s b) :=
  fun _ _ _ _ _ hs hT hsc hRe =>
    ⟨run1_reachRDN P counted L sinks roots hwf hRe,
     Coverage.vuln_found P counted L policy1 sinks roots hwf policy1_applicable hRe hs hT hsc⟩

#print axioms policy1_applicable
#print axioms run1_reachRDN
#print axioms run1_justifies

end Run1

end ApSpec.Handoff
