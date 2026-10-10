/-
  ApSpec.HandoffSrc — the FORWARD SOURCE SEEDS (`ap.md` §6.1 rule 6, §8.11; `FSeeds`) with the
  hand-off of the DEMAND EDGES only (decision F70).

  After run 1, a forward restricted run fires an unconditional source only if the backward run
  before it reached that source (its SOURCE HIT, `FSeeds.srcHit`): forward run `k + 1` analyses
  `FSeeds.keepSources P (σ k)`, where `σ k` contains the source hits of backward run `k`. The
  backward run runs on the FULL reversed program `Program.rev P`. `FSeeds.iteration_src` proves the
  iteration for the old hand-off; this file proves it for the new one (`handF`, `demOfN`, the
  records `recsBOf` / `rcNextOf`).

  THE CLAIM "A RECORDED CALL NEEDS NO SOURCE SEED INSIDE IT". A record of a crossed callee applies
  whatever the seeds are: a recorded call (`FlowRR.rcall`, `FlowRDN.rcall`) has no inner flow, so
  the witness has no source step inside the callee, and no source step there needs a hit. The
  claim holds in the proof: the record cases of the segment proof (`seg_genN_src`) are those of
  `HandoffBackward.seg_genN` with the call edge of the restricted program, and no case reads a
  seed. A record can also carry the effect of a source that the next run does not seed (for
  example the zero-premise exit edge `zero → (ret,.,$,T)` of a callee `mk() { return source() }`
  is crossable: `src_record_cross`): the restricted run then applies it although `σ` drops that
  source. This adds facts of `P` (the record is an exit edge of an earlier run on `P` or on a
  restriction of `P`); it removes none, so the coverage does not change. (Not a counterexample: it
  is the price of the records, a precision question, not a soundness one.)

  Main results:
    * Part 1. A witness of the restricted program is a witness of `P` (`flowRDN_sim`,
      `reachRDN_sim`, `reachRDN_keep`, `reachRDN_progSrc`; `flowRR_sim`, `reachRR_sim`).
    * Part 2. THE CORE: along a justified witness of `P` the backward run hits every source step,
      so the demanded-or-recorded witness that the backward contract gives lies in
      `keepSources P σ` for every `σ` that contains the hits (`seg_genN_src`, `reach_of_db_genN_src`,
      `demanded_genN_src`), and the backward contract with the source seeds (`B_srcN`, a
      `HandoffUpto.BackwardContractNIn` from `P` to `keepSources P σ`).
    * Part 3. THE ITERATION WITH SOURCE SEEDS, BASE MODEL (`runSeqSrcN`, `iteration_srcN`; the
      finite form `iteration_srcN_upto`; the canonical sequence `canonStateSrc`,
      `iteration_srcN_canon`, with the backward run `HandoffMain.backOf`: demand `handF`, records
      `recsBOf`): every real vulnerability is, at every forward run `k`, reported by run `k` or
      confirmed by an earlier run, with the seeds "confirmed or seeded".
    * Part 4. THE SPEC CLOSURES WITH THE `[any-taint]` EXCLUSION (`runSeqSrcNX`, `pubSeqSrcNX`,
      `iteration_srcNX`, `iteration_srcNX_upto`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffUpto
import ApSpec.ForwardSeeds

namespace ApSpec.HandoffSrc
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffIter
  ApSpec.HandoffUpto

/-! ## Part 0. A source record is crossable -/

/-- The run-1 exit edge `zero → (ret,.,$,T)` of a callee that returns an unconditional source
    (`mk() { return source() }`, ret = 4, mark T = 1) is crossable: the next runs cross the call by
    this record, with no seed. -/
theorem src_record_cross : Cross zeroFact ⟨⟨4, [], .exact, .conc 1⟩, false⟩ := by
  refine ⟨rfl, trivial, Or.inr ⟨_, rfl⟩, ?_⟩
  have h : (revEdge zeroFact (⟨4, [], .exact, .conc 1⟩ : PFact)).1.kind = .exact := by decide
  rw [h]
  trivial

#print axioms src_record_cross

/-! ## Part 1. A witness of the restricted program is a witness of `P` -/

section Sim
variable {P Q : Program} (hs : FSeeds.Sim P Q)
include hs

/-- A justified flow of `P` is a justified flow of every program that simulates `P`. -/
theorem flowRDN_sim {R : Obj → Prop} {pub : Pub} {rc : Recs} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : FlowRDN P R pub rc M l0 n l) : FlowRDN Q R pub rc M l0 n l := by
  induction h with
  | start M l0 => rw [← hs.entry M]; exact FlowRDN.start M l0
  | step _ he hst ih =>
    obtain ⟨s', he', hss⟩ := hs.stmt _ _ _ _ he
    exact FlowRDN.step ih he' (hss _ _ hst)
  | pass _ he hm ih => exact FlowRDN.pass ih (hs.call _ _ _ _ he) hm
  | call _ he he1 hd1 _ hj hg hpub hjc hdg he2 hd2 ih ihc =>
    rw [← hs.exit] at ihc hg
    exact FlowRDN.call ih (hs.call _ _ _ _ he) he1 hd1 ihc hj hg hpub hjc hdg he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRDN.rcall ih (hs.call _ _ _ _ he) he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRDN.clean ih (hs.clean _ _ _ _ he) hcl
  | filt _ he hl ih => exact FlowRDN.filt ih (hs.filt _ _ _ _ _ he) hl

/-- A justified witness of `P` is a justified witness of every program that simulates `P`. -/
theorem reachRDN_sim {R : Obj → Prop} {pub : Pub} {rc : Recs} {roots : List MethodId}
    {M : MethodId} {n : Node} {l : Loc} (h : ReachRDN P R pub rc roots M n l) :
    ReachRDN Q R pub rc roots M n l := by
  induction h with
  | root hM hfl => exact ReachRDN.root hM (flowRDN_sim hs hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachRDN.down ih (hs.call _ _ _ _ he) he1 hd1 hj hjc (flowRDN_sim hs hfc)

/-- A demanded-or-recorded flow of `P` is one of every program that simulates `P`. -/
theorem flowRR_sim {dem : MethodId → DemandEdge → Prop} {rc : Recs} {M : MethodId} {l0 : Loc}
    {n : Node} {l : Loc} (h : FlowRR P dem rc M l0 n l) : FlowRR Q dem rc M l0 n l := by
  induction h with
  | start M l0 => rw [← hs.entry M]; exact FlowRR.start M l0
  | step _ he hst ih =>
    obtain ⟨s', he', hss⟩ := hs.stmt _ _ _ _ he
    exact FlowRR.step ih he' (hss _ _ hst)
  | pass _ he hm ih => exact FlowRR.pass ih (hs.call _ _ _ _ he) hm
  | call _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    rw [← hs.exit] at ihc
    exact FlowRR.call ih (hs.call _ _ _ _ he) he1 hd1 ihc hdem hdin hdout hp he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRR.rcall ih (hs.call _ _ _ _ he) he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRR.clean ih (hs.clean _ _ _ _ he) hcl
  | filt _ he hl ih => exact FlowRR.filt ih (hs.filt _ _ _ _ _ he) hl

/-- A demanded-or-recorded witness of `P` is one of every program that simulates `P`. -/
theorem reachRR_sim {dem : MethodId → DemandEdge → Prop} {rc : Recs} {roots : List MethodId}
    {M : MethodId} {n : Node} {l : Loc} (h : ReachRR P dem rc roots M n l) :
    ReachRR Q dem rc roots M n l := by
  induction h with
  | root hM hfl => exact ReachRR.root hM (flowRR_sim hs hfl)
  | down _ he he1 hd1 hdem hdin hfc ih =>
    exact ReachRR.down ih (hs.call _ _ _ _ he) he1 hd1 hdem hdin (flowRR_sim hs hfc)

end Sim

/-- A justified witness of the restricted program is a justified witness of `P`. -/
theorem reachRDN_keep {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {R : Obj → Prop}
    {pub : Pub} {rc : Recs} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRDN (FSeeds.keepSources P σ) R pub rc roots M n l) :
    ReachRDN P R pub rc roots M n l :=
  reachRDN_sim FSeeds.sim_keep h

/-- A justified witness of the program of forward run `k` is a justified witness of `P`. -/
theorem reachRDN_progSrc {P : Program} {σ : Nat → MethodId → Node → MicroEdge → Bool} {k : Nat}
    {R : Obj → Prop} {pub : Pub} {rc : Recs} {roots : List MethodId} {M : MethodId} {n : Node}
    {l : Loc} (h : ReachRDN (FSeeds.progSrc P σ k) R pub rc roots M n l) :
    ReachRDN P R pub rc roots M n l := by
  cases k with
  | zero => exact h
  | succ k => exact reachRDN_keep h

#print axioms flowRDN_sim
#print axioms reachRDN_sim
#print axioms flowRR_sim
#print axioms reachRR_sim
#print axioms reachRDN_keep
#print axioms reachRDN_progSrc

/-! ## Part 2. The backward run hits every source step of a justified witness -/

section General
variable {P : Program} {Rk : Obj → Prop} {pub : Pub} {rc rcnext : Recs} {counted : Acc → Bool}
  {L : Nat} {demB : MethodId → DemandEdge → Prop} {recsB : MethodId → PFact × AFact → Prop}
  {sinksB : List (MethodId × Node × PFact)} {rootsB : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
  {σ : MethodId → Node → MicroEdge → Bool}

local notation "DBr" =>
  DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB rootsB seeds zbind

/-- THE BACKWARD SEGMENT WITH THE SOURCE SEEDS (`HandoffBackward.seg_genN` with the demanded flow in
    `keepSources P σ`, as `FSeeds.seg_src`). A justified forward flow of `M` in `P` and a concrete
    legal backward edge at its end give a concrete legal backward edge at the forward entry; and the
    flow is demanded or recorded in the next forward run IN THE RESTRICTED PROGRAM, for every `σ`
    that contains the source hits of the backward run. A step uses a source edge only where a
    backward requirement covers its end, so the edge is hit (`FSeeds.keep_step`). A recorded call
    has no inner flow: it reads no seed. -/
theorem seg_genN_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    (hσ : ∀ M n e, FSeeds.srcHit P DBr M n e → σ M n e = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowRDN P Rk pub rc M l0 n l) :
    ∀ i f lX, DBr (.edge M i n f) →
      den i f.fact lX l → (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      (∃ f', DBr (.edge M i (P.entry M) f') ∧ den i f'.fact lX l0 ∧
          (∃ t, f'.fact.mark = .conc t) ∧ Invariant.Legal f') ∧
      FlowRR (FSeeds.keepSources P σ) (demOfN (Program.rev P) DBr (pubR demB)) rcnext M l0 n l := by
  induction hfl with
  | start M l0 =>
    intro i f lX h hd hc hl
    exact ⟨⟨f, h, hd, hc, hl⟩, FlowRR.start M l0⟩
  | @step M l0 n1 l1 n' l' s _ he hst ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.stmt (Stmt.rev s), n1) ∈ (Program.rev P).edges := mem_rev_stmt he
    have hrs : (Stmt.rev s).step l' l1 := Stmt.rev_step_sound (hmr M n1 s n' he) hst
    -- the forward step is a step of the restricted statement: a source edge of it is hit
    have hks : (FSeeds.keepStmt σ M n1 s).step l1 l' := FSeeds.keep_step hσ he h hc hd hst
    obtain ⟨t, ht⟩ := hc
    rcases transfer_sound (counted := counted) (L := L) (rev_touched s) hd hrs with
      ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.step h hEr hr) hdr (transfer_mark_conc ht hr)
        (legal_transfer hl hr)
      exact ⟨res, FlowRR.step hfr (FSeeds.mem_keep_stmt he) hks⟩
    · exact absurd ht (habs t)
  | @pass M l0 n1 l1 n' c _ he hb ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.call (Call.rev c), n1) ∈ (Program.rev P).edges := mem_rev_call he
    have hb' : memB f.fact.base (Call.rev c).touched = false := by
      show memB f.fact.base c.touched = false
      rw [← hd.2.1]
      exact hb
    obtain ⟨res, hfr⟩ := ih i f lX (DB.pass h hEr hb') hd hc hl
    exact ⟨res, FlowRR.pass hfr (FSeeds.mem_keep_call he) hb⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 j g g' _ he he1 hd1 _ hj hg hpub hjc hdg he2 hd2 ih ihc =>
    intro i f lX h hd hc hl
    rcases cross_em j g with hcr | hncr
    · -- a crossable exit edge: the backward run crosses it by its reversal (no seed is read)
      have hdgf : den j g.fact l1 l2 := hpubSub _ _ _ _ hpub _ _ hdg
      obtain ⟨f1, h1, hd1', hc1, hl1⟩ := cross_step hW hT he he1 hd1 he2 hd2
        (hrecB _ (j, g) (Or.inr ⟨hj, hg⟩) hcr) hcr hdgf h hd hc
      obtain ⟨res, hfr⟩ := ih i f1 lX h1 hd1' hc1 hl1
      exact ⟨res, FlowRR.rcall hfr (FSeeds.mem_keep_call he) he1 hd1 (hrcN.fwd _ _ _ hj hg hcr)
        hcr hjc hdgf he2 hd2⟩
    · -- not crossable: the backward run enters the callee by the demand edge `(g', j)`
      obtain ⟨t, ht⟩ := hc
      have hEr : (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges := mem_rev_call he
      have hWr := rev_WF hW hT
      have her2 : revEdge e2.1 e2.2 ∈ (Call.rev c).toCallee := List.mem_map.mpr ⟨e2, he2, rfl⟩
      have hdr2 : den (revEdge e2.1 e2.2).1 (revEdge e2.1 e2.2).2 l3 l2 :=
        revEdge_sound (markRev_star ((hT M n c n' he).2 e2 he2)) hd2
      obtain ⟨a, ha, hda⟩ := Coverage.bind_in hWr hEr her2 hd hdr2
      have hadd : DBr (.added c.callee a.fact) := DB.added (c := Call.rev c) h hEr her2 ha
      obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
      have hdB : demB c.callee ⟨g'.fact, some j⟩ :=
        hdemB _ _ ⟨j, g, g', hj, hg, hncr, hpub, rfl⟩
      obtain ⟨jb, hemit, hjbc, hsat⟩ := RCore.emitM_contract_I g'.fact a.fact l2 ta hta
        (den_covers_final hdg) (den_covers_final hda)
      have hjb : DBr (.init c.callee jb) := DB.initR (m := c.callee) hadd hdB hemit
      have hjbm : jb.mark = .conc ta := by rw [RCov.emitM_copies _ _ _ hemit]; exact hta
      -- the reversed callee flow; the callee flow in the restricted program comes from the
      -- induction hypothesis of the callee
      obtain ⟨⟨gb, hgb, hdgb, _, _⟩, hfrc⟩ := ihc jb (startFact jb) l2 (DB.start hjb)
        (startFact_sound hjbc) ⟨ta, by rw [startFact_mark]; exact hjbm⟩
        (fun _ hk => Invariant.startFact_legal hk)
      -- the intersection restriction by the demand edge keeps the pair
      obtain ⟨gb', hres, hdgb', _⟩ := restrictI_contract_B (d := ⟨g'.fact, some j⟩)
        (emitM_inside_B hemit) hdgb rfl (RCov.covers_loc hjc)
      -- the backward summary piece applied, and the reversed binding into the callee
      obtain ⟨r, hr, hdr⟩ := RCov.sat_step RCore.satI_contract hsat hda hdgb'
      have her1 : revEdge e1.1 e1.2 ∈ (Call.rev c).fromCallee := List.mem_map.mpr ⟨e1, he1, rfl⟩
      have hdr1 : den (revEdge e1.1 e1.2).1 (revEdge e1.1 e1.2).2 l1 l :=
        revEdge_sound (markRev_star ((hT M n c n' he).1 e1 he1)) hd1
      obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hWr hEr her1 hdr hdr1
      have hret := DB.ret (c := Call.rev c) h hEr her2 ha hjb hgb hdB hres hsat hr her1 hr'
      obtain ⟨t1, h1⟩ := applySummary_mark_conc hta hr
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 hr'
      obtain ⟨res, hfr⟩ := ih i _ lX hret (limitF_sound hdr') ⟨t2, by rw [limitF_mark]; exact h2⟩
        (Invariant.limitF_Legal (Invariant.applyEdge_Legal hr'))
      have hne : jb ≠ zeroFact := by
        intro hz
        have hb1 : l2.base = jb.base := hjbc.1
        have hb2 : l2.base = e2.1.base := hd2.1
        rw [hz] at hb1
        exact hNZB M n c n' he e2 he2 (hb2.symm.trans hb1)
      rcases crossB_em jb gb with hcb | hncb
      · -- a normal backward summary with a crossable reversal: a RECORDED call (no seed is read)
        have hrv : den (revRec (jb, gb)).1 (revRec (jb, gb)).2.fact l1 l2 :=
          revEdge_sound (Or.inr ⟨ta, hjbm⟩) hdgb
        exact ⟨res, FlowRR.rcall hfr (FSeeds.mem_keep_call he) he1 hd1
          (hrcN.back _ _ _ hjb hne hgb hcb) hcb.2 (den_covers_init hrv) hrv he2 hd2⟩
      · -- a DEMANDED call (`demOfN`, case 3); the callee flow is in the restricted program
        have hdem : demOfN (Program.rev P) DBr (pubR demB) c.callee ⟨gb'.fact, some jb⟩ :=
          Or.inr (Or.inr ⟨jb, gb, gb', hjb, hne, hgb, hncb, ⟨_, hdB, hres⟩, rfl⟩)
        exact ⟨res, FlowRR.call hfr (FSeeds.mem_keep_call he) he1 hd1 hfrc hdem
          (den_covers_final hdgb') rfl (RCov.covers_loc hjbc) he2 hd2⟩
  | @rcall M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 hrcj hcr hjc hdg he2 hd2 ih =>
    intro i f lX h hd hc hl
    -- a crossable record of `rc`: the backward run crosses it by its reversal (no seed is read)
    obtain ⟨f1, h1, hd1', hc1, hl1⟩ := cross_step hW hT he he1 hd1 he2 hd2
      (hrecB _ (j, g) (Or.inl hrcj) hcr) hcr hdg h hd hc
    obtain ⟨res, hfr⟩ := ih i f1 lX h1 hd1' hc1 hl1
    exact ⟨res, FlowRR.rcall hfr (FSeeds.mem_keep_call he) he1 hd1 (hrcN.old _ _ hrcj) hcr hjc hdg
      he2 hd2⟩
  | @clean M l0 n1 l1 n' cl _ he hcl ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.clean cl, n1) ∈ (Program.rev P).edges := mem_rev_clean he
    obtain ⟨t, ht⟩ := hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.clean h hEr hr) hdr (cleanRes_mark_conc ht hr)
        (Invariant.cleanRes_Legal hl hr)
      exact ⟨res, FlowRR.clean hfr (FSeeds.mem_keep_clean he) hcl⟩
    · exact absurd ht (habs t)
  | @filt M l0 n1 l1 n' b may _ he hmay ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.filt b may, n1) ∈ (Program.rev P).edges := mem_rev_filt he
    have hff : f.fact.base = b → may f.fact.path = true := by
      intro hfb
      obtain ⟨_, hb1, _, _, _, σ, τ, _, hp1, _, _⟩ := hd
      have hm := hmay (hb1.trans hfb)
      rw [hp1] at hm
      exact hW.filtPrefix _ _ _ _ _ he _ _ hm
    obtain ⟨res, hfr⟩ := ih i f lX (DB.filt h hEr hff) hd hc hl
    exact ⟨res, FlowRR.filt hfr (FSeeds.mem_keep_filt he) hmay⟩

#print axioms seg_genN_src

/-- The induction over the calls down (`HandoffBackward.reach_of_db_genN` in the restricted
    program). -/
theorem reach_of_db_genN_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    (hσ : ∀ M n e, FSeeds.srcHit P DBr M n e → σ M n e = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRDN P Rk pub rc roots M n l) :
    ∀ f, DBr (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l →
      (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      ReachRR (FSeeds.keepSources P σ) (demOfN (Program.rev P) DBr (pubR demB)) rcnext roots
        M n l := by
  induction hRe with
  | root hM hfl =>
    intro f h hd hc hl
    exact ReachRR.root hM
      (seg_genN_src hW hT hmr hNZB hdemB hrecB hpubSub hrcN hσ hfl zeroFact f zeroLoc h hd hc
        hl).2
  | @down M n l n' c e l1 n2 l2 j hRe0 hE he hd1 _ _ hfl ih =>
    intro f h hd hc hl
    obtain ⟨⟨f', h', hd', hc', _⟩, hfr⟩ :=
      seg_genN_src hW hT hmr hNZB hdemB hrecB hpubSub hrcN hσ hfl zeroFact f zeroLoc h hd hc hl
    have hz := zero_path (counted := counted) (L := L) (demand := demB) (emit := emitM)
      (sat := satI) (restrict := restrictI) (recs := recsB) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ
      (hX M n' (reachRDN_called hRe0) (CfgPath.step (reachRDN_cfg hRe0) hE))
      (zero_exit (zero_initN hZ hX hzb hroots hRe0))
    obtain ⟨g, hg, hdg, hcg, hlg⟩ := zret_descent hW hT hzb hE he hd1 hz h' hd' hc'
    have hdem : demOfN (Program.rev P) DBr (pubR demB) c.callee ⟨f'.fact, none⟩ :=
      Or.inr (Or.inl ⟨f', h', rfl⟩)
    exact ReachRR.down (ih g hg hdg hcg hlg) (FSeeds.mem_keep_call hE) he hd1 hdem
      (den_covers_final hd') hfr

#print axioms reach_of_db_genN_src

/-- Every justified witness of `P` whose sink is seeded is demanded or recorded in the next
    forward run, in the restricted program (`HandoffBackward.demanded_genN` with source seeds). -/
theorem demanded_genN_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    (hσ : ∀ M n e, FSeeds.srcHit P DBr M n e → σ M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachRDN P Rk pub rc roots M n l) (hseed : (M, n, s) ∈ seeds)
    (hT' : s.mark = .conc T) (hk : s.kind = .exact ∨ s.kind = .any) (hsc : s.covers l) :
    ReachRR (FSeeds.keepSources P σ) (demOfN (Program.rev P) DBr (pubR demB)) rcnext roots M n l :=
  reach_of_db_genN_src hW hT hmr hNZB hZ hX hzb hroots hdemB hrecB hpubSub hrcN hσ hRe _
    (DB.seed hseed (zero_atN hZ hX hzb hroots hRe))
    (limitF_sound (seed_den hT' hk hsc)) ⟨T, by rw [limitF_mark]; exact hT'⟩ (legal_seed hk)

#print axioms demanded_genN_src

end General

/-- THE BACKWARD CONTRACT WITH THE SOURCE SEEDS (`HandoffBackward.B_generalN` with the next forward
    run on `keepSources P σ`, as `FSeeds.B_src`). Under the hypotheses of `B_generalN`, every
    justified witness of `P` of a seeded sink is demanded or recorded in the next forward run IN
    `keepSources P σ`, for every `σ` that contains the source hits of the backward run. -/
theorem B_srcN {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {pub : Pub} {rc rcnext : Recs} {seeds : List (MethodId × Node × PFact)}
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {σ : MethodId → Node → MicroEdge → Bool}
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc
      (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true) rcnext)
    (hσ : ∀ M n e, FSeeds.srcHit P
      (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true) M n e →
      σ M n e = true) :
    BackwardContractNIn P (FSeeds.keepSources P σ) roots sinks seeds Rk pub rc
      (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true)
        (pubR demB))
      rcnext := by
  intro M n l s T hs hT' hsc hRR hseed
  exact demanded_genN_src hW hT hmr hNZB hZ hX rfl (fun _ h => h) hdemB hrecB hpubSub hrcN hσ hRR
    hseed hT' (hk M n s hs) hsc

#print axioms B_srcN

/-- `B_srcN` gives `HandoffBackward.B_generalN` back (every source seeded: the restricted program
    simulates `P`). -/
theorem B_generalN_of_src {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {pub : Pub} {rc rcnext : Recs} {seeds : List (MethodId × Node × PFact)}
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc
      (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true)
      rcnext) :
    BackwardContractN P roots sinks seeds Rk pub rc
      (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true)
        (pubR demB))
      rcnext := by
  intro M n l s T hs hT' hsc hRR hseed
  have h := B_srcN (σ := fun _ _ _ => true) hW hT hmr hNZB hZ hX hk hdemB hrecB hpubSub hrcN
    (fun _ _ _ _ => rfl) M n l s T hs hT' hsc hRR hseed
  exact reachRR_sim FSeeds.sim_keep h

#print axioms B_generalN_of_src

/-! ## Part 3. The iteration with the source seeds, base model -/

open ApSpec.HandoffMain (pubSeqN pubSeqN_sub reachRR_mono reachRDN_mono_rc)

/-- The run sequence with the source seeds and the new hand-off: run 0 is `D … policy1 …` on the
    full program; run `k + 1` is `DR … emitM satI restrictI …` on `keepSources P (σ k)` (only the
    seeded unconditional sources fire), with the demand `dem k` and the records `rc (k + 1)`. Its
    publication is `HandoffMain.pubSeqN dem`. -/
def runSeqSrcN (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool) (dem : Nat → MethodId → DemandEdge → Prop)
    (rc : Nat → Recs) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) :
    Nat → Obj → Prop
  | 0 => D P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR (FSeeds.keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI restrictI
      (rc (k + 1)) sinks roots

section IterSrc
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {counted : Acc → Bool} {Ls LB : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
  {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "RS" => runSeqSrcN P counted Ls σ dem rc sinks roots
local notation "DBk" k => DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k)
  [] roots (seeds k) true

/-- Run 0 (the full program) justifies every real witness and reports it. -/
theorem src_run0 (hW : P.WF) :
    Run0Contract (FSeeds.progSrc P σ 0) roots sinks (RS 0) (pubSeqN dem 0) (rc 0) := by
  intro M' n' l' s' T' hs' hT'' hc' hRe'
  obtain ⟨hR, hv⟩ := run1_justifies P counted (Ls 0) sinks roots hW M' n' l' s' T' hs' hT'' hc'
    hRe'
  exact ⟨reachRDN_mono_rc (fun _ _ h => h.elim) hR, hv⟩

/-- The forward contract of forward run `k + 1`, in its program `keepSources P (σ k)`. -/
theorem src_covers (hW : P.WF) (k : Nat) :
    CoversN (FSeeds.progSrc P σ (k + 1)) roots sinks (dem k) (rc (k + 1)) (RS (k + 1))
      (pubSeqN dem (k + 1)) :=
  coversN_DR (FSeeds.keepSources P (σ k)) counted (Ls (k + 1)) (dem k) (rc (k + 1)) sinks roots
    (FSeeds.keep_WF hW)

/-- The backward contract of round `k`: from forward run `k` in its program to forward run `k + 1`
    in `keepSources P (σ k)`. -/
theorem src_backward (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any) (k : Nat)
    (hdemB : ∀ m d, handF P (RS k) (pubSeqN dem k) m d → demB k m d)
    (hrecB : ∀ m x, (rc k m x ∨ (RS k (.init m x.1) ∧ RS k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrc : NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hσ : ∀ M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true) :
    BackwardContractNIn (FSeeds.progSrc P σ k) (FSeeds.progSrc P σ (k + 1)) roots sinks (seeds k)
      (RS k) (pubSeqN dem k) (rc k) (dem k) (rc (k + 1)) := by
  intro M' n' l' s' T' hs' hT'' hc' hRR hsd
  exact reachRR_mono hdem
    (B_srcN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk hdemB hrecB
      (pubSeqN_sub dem k) hrc hσ M' n' l' s' T' hs' hT'' hc' (reachRDN_progSrc hRR) hsd)

#print axioms src_run0
#print axioms src_covers
#print axioms src_backward

/-- THE ITERATION WITH THE SOURCE SEEDS AND THE NEW HAND-OFF (`FSeeds.iteration_src` with `handF`,
    `demOfN`, `restrictI` and the records). Run 1 analyses the full program; forward run `k + 1`
    fires only the unconditional sources in `σ k`, and `σ k` contains the source hits of the
    backward run after forward run `k` (on the FULL reversed program). The backward demand contains
    `handF` of run `k`, the backward records contain the reversed crossable records of run `k`, the
    demand `dem k` contains the hand-off `demOfN`, the records `rc (k + 1)` contain `rcNextOf`
    (`NextRecs`; the records apply in the restricted program whatever `σ` is), and every reported
    vulnerability of run `k` is confirmed (`C k`) or seeded. Then every real vulnerability of `P`
    is, at every forward run `k`, reported by run `k` or confirmed by an earlier run. Program
    hypotheses as `HandoffMain.iteration_generalN`. -/
theorem iteration_srcN (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hdemB : ∀ k m d, handF P (RS k) (pubSeqN dem k) m d → demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (RS k (.init m x.1) ∧ RS k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ k m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrc : ∀ k, NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hσ : ∀ k M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true)
    (hseeds : ∀ k M n s b, RS k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RS k (.vuln M n s b) :=
  iteration_prog_or (Pr := FSeeds.progSrc P σ) (R := RS) (pub := pubSeqN dem) (rc := rc)
    (dem := dem) (seeds := seeds) (src_run0 hW) (src_covers hW)
    (fun k => src_backward hW hT hmr hNZB hZ hX hk k (hdemB k) (hrecB k) (hdem k) (hrc k) (hσ k))
    hseeds hRe hs hT' hsc

#print axioms iteration_srcN

/-- THE ITERATION WITH THE SOURCE SEEDS, FINITE FORM: the driver stops after forward run `K`, the
    hypotheses of `iteration_srcN` hold for the rounds `k < K`; every forward run `k ≤ K` reports
    every real vulnerability, or a run before `k` confirmed it. -/
theorem iteration_srcN_upto (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop} (K : Nat)
    (hdemB : ∀ k, k < K → ∀ m d, handF P (RS k) (pubSeqN dem k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (RS k (.init m x.1) ∧
        RS k (.edge m x.1 (P.exit m) x.2))) → Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ k, k < K → ∀ m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrc : ∀ k, k < K → NextRecs P (RS k) (rc k) (DBk k) (rc (k + 1)))
    (hσ : ∀ k, k < K → ∀ M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true)
    (hseeds : ∀ k, k < K → ∀ M n s b, RS k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RS k (.vuln M n s b) :=
  iteration_prog_upto (Pr := FSeeds.progSrc P σ) (R := RS) (pub := pubSeqN dem) (rc := rc)
    (dem := dem) (seeds := seeds) K (src_run0 hW) (fun k _ => src_covers hW k)
    (fun k hkK => src_backward hW hT hmr hNZB hZ hX hk k (hdemB k hkK) (hrecB k hkK) (hdem k hkK)
      (hrc k hkK) (hσ k hkK))
    hseeds hRe hs hT' hsc

#print axioms iteration_srcN_upto

end IterSrc

/-! ### The canonical sequence with the source seeds -/

open ApSpec.HandoffMain (RunState state0 backOf demOf rcOf) in
/-- One round with the source seeds: from forward run `k` (state `s`) to forward run `k + 1` on
    `keepSources P (σ k)`, with the canonical hand-offs of `HandoffMain` (the backward run
    `backOf`: demand `handF`, records `recsBOf`, on the FULL reversed program; the demand `demOf`;
    the records `rcOf` = `rcNextOf`). -/
def stepStateSrc (P : Program) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (k : Nat) (s : RunState) : RunState where
  R := DR (FSeeds.keepSources P (σ k)) counted (Ls (k + 1)) (demOf P counted (LB k) roots (seeds k) s)
    emitM satI restrictI (rcOf P counted (LB k) roots (seeds k) s) sinks roots
  pub := pubR (demOf P counted (LB k) roots (seeds k) s)
  rc := rcOf P counted (LB k) roots (seeds k) s

open ApSpec.HandoffMain (RunState state0) in
/-- THE CANONICAL RUN SEQUENCE WITH THE SOURCE SEEDS (`HandoffMain.canonState` with forward run
    `k + 1` on `keepSources P (σ k)`). -/
def canonStateSrc (P : Program) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) (σ : Nat → MethodId → Node → MicroEdge → Bool) :
    Nat → RunState
  | 0 => state0 P counted (Ls 0) sinks roots
  | k + 1 => stepStateSrc P counted Ls LB sinks roots seeds σ k
      (canonStateSrc P counted Ls LB sinks roots seeds σ k)

section CanonSrc
open ApSpec.HandoffMain (backOf demOf)
variable {P : Program} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)} {σ : Nat → MethodId → Node → MicroEdge → Bool}

local notation "CS" => canonStateSrc P counted Ls LB sinks roots seeds σ

/-- Every publication of the sequence only removes pairs. -/
theorem canonSrc_pubSub (k : Nat) :
    ∀ m j g g', (CS k).pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubR_sub _

#print axioms canonSrc_pubSub

/-- THE ITERATION WITH THE SOURCE SEEDS ON THE CANONICAL SEQUENCE. The backward run after forward
    run `k` is `HandoffMain.backOf` (demand `handF`, records `recsBOf`, the full reversed
    program); forward run `k + 1` analyses `keepSources P (σ k)` with the demand `demOfN` and the
    records `rcNextOf` of that backward run, and `σ k` contains its source hits. If every reported
    vulnerability of run `k` is confirmed (`C k`) or seeded, every real vulnerability of `P` is, at
    every forward run `k`, reported by run `k` or confirmed by an earlier run. -/
theorem iteration_srcN_canon (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hσ : ∀ k M n e, FSeeds.srcHit P (backOf P counted (LB k) roots (seeds k) (CS k)) M n e →
      σ k M n e = true)
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_prog_or (Pr := FSeeds.progSrc P σ) (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc) (dem := fun k => demOf P counted (LB k) roots (seeds k) (CS k))
    (seeds := seeds)
    (run1_justifies P counted (Ls 0) sinks roots hW)
    (fun k => coversN_DR (FSeeds.keepSources P (σ k)) counted (Ls (k + 1))
      (demOf P counted (LB k) roots (seeds k) (CS k)) (CS (k + 1)).rc sinks roots
      (FSeeds.keep_WF hW))
    (fun k M' n' l' s' T' hs' hT'' hc' hRR hsd =>
      B_srcN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
        (fun _ _ h => h) recsBOf_spec (canonSrc_pubSub k) rcNextOf_spec (hσ k)
        M' n' l' s' T' hs' hT'' hc' (reachRDN_progSrc hRR) hsd)
    hseeds hRe hs hT' hsc

#print axioms iteration_srcN_canon

end CanonSrc

/-! ## Part 4. The spec closures with the `[any-taint]` exclusion -/

section IterSrcX
open ApSpec.HandoffX ApSpec.AnyTaint ApSpec.AnyTaintEx
open ApSpec.AnyTaintExCov (forgetX forget6)
open ApSpec.HandoffXIter (reachRR_monoX reachRDN_mono_rcX)

/-- The run sequence with the source seeds, the new hand-off and the exclusion: run 0 is
    `D6X … policy1 …` on the full program read by `forget6`; run `k + 1` is
    `DRX … emitX satX restrictIX (recsX k) …` on `keepSources P (σ k)` read by `forgetX`. -/
def runSeqSrcNX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool) (dem : Nat → MethodId → DemandEdge → Prop)
    (recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Obj → Prop
  | 0 => forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
  | k + 1 => forgetX (DRX (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitX satX
      restrictIX (recsX k) sinks roots)

/-- The publications of `runSeqSrcNX` (`pubRX` reads only the exits, which the restriction does not
    change). -/
def pubSeqSrcNX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool) (dem : Nat → MethodId → DemandEdge → Prop)
    (recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Pub
  | 0 => pubD
  | k + 1 => pubRX P (DRX (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitX satX
      restrictIX (recsX k) sinks roots) (dem k)

theorem pubSeqSrcNX_sub {P : Program} {taint : TaintEdges} {counted : Acc → Bool}
    {Ls : Nat → Nat} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (k : Nat) :
    ∀ m j g g', pubSeqSrcNX P taint counted Ls σ dem recsX sinks roots k m j g g' →
      ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubRX_sub P _ _

#print axioms pubSeqSrcNX_sub

variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {σ : Nat → MethodId → Node → MicroEdge → Bool}
  {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
  {recsX : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "RSX" => runSeqSrcNX P taint counted Ls σ dem recsX sinks roots
local notation "PSX" => pubSeqSrcNX P taint counted Ls σ dem recsX sinks roots
local notation "DBk" k => DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k)
  [] roots (seeds k) true

/-- Run 0 (`D6X` on the full program) justifies every real witness and reports it. -/
theorem srcX_run0 (hW : P.WF) :
    Run0Contract (FSeeds.progSrc P σ 0) roots sinks (RSX 0) (PSX 0) (rc 0) := by
  intro M1 n1 l1 s1 T1 hs1 hT1 hsc1 hRe1
  obtain ⟨hRD, hv⟩ := run0X_contract (taint := taint) (counted := counted) (L := Ls 0) hW M1 n1 l1
    s1 T1 hs1 hT1 hsc1 hRe1
  exact ⟨reachRDN_mono_rcX (fun _ _ h => h.elim) hRD, hv⟩

/-- The forward contract of the X run `k + 1`, in its program `keepSources P (σ k)`. -/
theorem srcX_covers (hW : P.WF) (k : Nat) (hrecX : RecsEmbed (rc (k + 1)) (recsX k)) :
    CoversN (FSeeds.progSrc P σ (k + 1)) roots sinks (dem k) (rc (k + 1)) (RSX (k + 1))
      (PSX (k + 1)) :=
  coversN_DRXI (P := FSeeds.keepSources P (σ k)) (FSeeds.keep_WF hW) hrecX

/-- The backward contract of round `k` for the X sequence. -/
theorem srcX_backward (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any) (k : Nat)
    (hdemB : ∀ m d, handF P (RSX k) (PSX k) m d → demB k m d)
    (hrecB : ∀ m x, (rc k m x ∨ (RSX k (.init m x.1) ∧ RSX k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrc : NextRecs P (RSX k) (rc k) (DBk k) (rc (k + 1)))
    (hσ : ∀ M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true) :
    BackwardContractNIn (FSeeds.progSrc P σ k) (FSeeds.progSrc P σ (k + 1)) roots sinks (seeds k)
      (RSX k) (PSX k) (rc k) (dem k) (rc (k + 1)) := by
  intro M' n' l' s' T' hs' hT'' hc' hRR hsd
  exact reachRR_monoX hdem (fun _ _ h => h)
    (B_srcN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk hdemB hrecB
      (pubSeqSrcNX_sub k) hrc hσ M' n' l' s' T' hs' hT'' hc' (reachRDN_progSrc hRR) hsd)

#print axioms srcX_run0
#print axioms srcX_covers
#print axioms srcX_backward

/-- THE ITERATION WITH THE SOURCE SEEDS, THE NEW HAND-OFF AND THE `[any-taint]` EXCLUSION
    (`AnyTaintExCov.iteration_srcX` with the new hand-off; hypotheses as
    `HandoffXIter.iteration_generalNX_incl`, plus `σ k` ⊇ the source hits of backward run `k`).
    Every real vulnerability of `P` is, at every forward run `k`, reported by run `k` or confirmed
    by an earlier run. -/
theorem iteration_srcNX (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hdemB : ∀ k m d, handF P (RSX k) (PSX k) m d → demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (RSX k (.init m x.1) ∧ RSX k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, NextRecs P (RSX k) (rc k) (DBk k) (rc (k + 1)))
    (hdem : ∀ k m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, RecsEmbed (rc (k + 1)) (recsX k))
    (hσ : ∀ k M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true)
    (hseeds : ∀ k M n s b, RSX k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RSX k (.vuln M n s b) :=
  iteration_prog_or (Pr := FSeeds.progSrc P σ) (R := RSX) (pub := PSX) (rc := rc) (dem := dem)
    (seeds := seeds) (srcX_run0 hW) (fun k => srcX_covers hW k (hrecX k))
    (fun k => srcX_backward hW hT hmr hNZB hZ hX hk k (hdemB k) (hrecB k) (hdem k) (hrcN k)
      (hσ k))
    hseeds hRe hs hT' hsc

#print axioms iteration_srcNX

/-- THE ITERATION WITH THE SOURCE SEEDS AND THE EXCLUSION, FINITE FORM (the hypotheses of
    `iteration_srcNX` for the rounds `k < K`, the conclusion for the forward runs `k ≤ K`). -/
theorem iteration_srcNX_upto (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop} (K : Nat)
    (hdemB : ∀ k, k < K → ∀ m d, handF P (RSX k) (PSX k) m d → demB k m d)
    (hrecB : ∀ k, k < K → ∀ m x, (rc k m x ∨ (RSX k (.init m x.1) ∧
        RSX k (.edge m x.1 (P.exit m) x.2))) → Cross x.1 x.2 → recsB k m (revRec x))
    (hrcN : ∀ k, k < K → NextRecs P (RSX k) (rc k) (DBk k) (rc (k + 1)))
    (hdem : ∀ k, k < K → ∀ m d, demOfN (Program.rev P) (DBk k) (pubR (demB k)) m d → dem k m d)
    (hrecX : ∀ k, k < K → RecsEmbed (rc (k + 1)) (recsX k))
    (hσ : ∀ k, k < K → ∀ M n e, FSeeds.srcHit P (DBk k) M n e → σ k M n e = true)
    (hseeds : ∀ k, k < K → ∀ M n s b, RSX k (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, k ≤ K → (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, RSX k (.vuln M n s b) :=
  iteration_prog_upto (Pr := FSeeds.progSrc P σ) (R := RSX) (pub := PSX) (rc := rc) (dem := dem)
    (seeds := seeds) K (srcX_run0 hW) (fun k hkK => srcX_covers hW k (hrecX k hkK))
    (fun k hkK => srcX_backward hW hT hmr hNZB hZ hX hk k (hdemB k hkK) (hrecB k hkK)
      (hdem k hkK) (hrcN k hkK) (hσ k hkK))
    hseeds hRe hs hT' hsc

#print axioms iteration_srcNX_upto

end IterSrcX

/-! ## Part 5. The claim in action: a record crosses a callee whose source is not seeded

```
root():  x = mk();  sink(x);        // method 0: 0 -call mk-> 1 (exit), the sink at 1
mk():    ret = source();            // method 1: 0 -src-> 1 (exit)
```
  Bases zero = 0, x = 1, ret = 2; mark T = 1. Run 1 (`D … policy1 …`) analyses `mk` from the zero
  fact (field limit 1): its exit edge `zero → (ret,.,$,T)` is crossable (`run1_exit`, `exit_cross`), so every
  record set of the next forward run that `NextRecs` allows holds it (`rec_next`). Forward run 2 on
  `keepSources P σ` with NO source seeded (`σ = false`: the source of `mk` is dropped, `src_dropped`)
  still reports the vulnerability, in the NORMAL layer, for every demand: the record crosses the
  call (`found_unseeded`). So a record needs no source seed inside its callee; it can carry the
  effect of a source that `σ` drops (a fact of `P`, so the coverage is kept; the run on
  `keepSources P σ` is not a run of the restricted program alone). -/

namespace SrcRec

/-- `ret = source()`: the zero fact is kept, and one source edge to `(ret,.,$,T)`. -/
def srcM : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨2, [], .exact, .conc 1⟩)]⟩
/-- The bindings of `x = mk()`: the zero fact into the zero fact, `ret → x`. -/
def zb : MicroEdge := (⟨0, [], .star (.set []), .star⟩, ⟨0, [], .star (.set []), .star⟩)
def br : MicroEdge := (⟨2, [], .star (.set []), .star⟩, ⟨1, [], .star (.set []), .star⟩)
def callM : Call := ⟨1, [1], [zb], [br]⟩
def PS : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .call callM, 1), (1, 0, .stmt srcM, 1)]⟩
/-- The sink `sink(x)` at node 1 of the root. -/
def sinkS : PFact := ⟨1, [], .exact, .conc 1⟩
def sinksS : List (MethodId × Node × PFact) := [(0, 1, sinkS)]
/-- The exit fact of `mk`: `(ret,.,$,T)`, normal layer. -/
def Gs : AFact := ⟨⟨2, [], .exact, .conc 1⟩, false⟩
def cnt : Acc → Bool := fun _ => true

theorem hE0 : (0, 0, Instr.call callM, 1) ∈ PS.edges := List.Mem.head _
theorem hE1 : (1, 0, Instr.stmt srcM, 1) ∈ PS.edges := List.Mem.tail _ (List.Mem.head _)

/-- Run 1 (field limit 1) analyses `mk` from the zero fact and gives the exit edge
    `zero → (ret,.,$,T)`. -/
theorem run1_exit :
    D PS cnt 1 policy1 sinksS [0] (.init 1 zeroFact) ∧
    D PS cnt 1 policy1 sinksS [0] (.edge 1 zeroFact (PS.exit 1) Gs) := by
  have e0 : D PS cnt 1 policy1 sinksS [0] (.edge 0 zeroFact 0 Backward.zeroAF) :=
    D.start (D.root (List.Mem.head _))
  have ad : D PS cnt 1 policy1 sinksS [0] (.added 1 zeroFact) :=
    D.added (c := callM) (e := zb) (a := Backward.zeroAF) e0 hE0 (List.Mem.head _) (by decide)
  have i1 : D PS cnt 1 policy1 sinksS [0] (.init 1 (policy1 1 zeroFact)) := D.initA ad
  have hp : policy1 1 zeroFact = zeroFact := by decide
  rw [hp] at i1
  exact ⟨i1, D.step (D.start i1) (s := srcM) hE1 (by decide)⟩

/-- The exit edge is crossable. -/
theorem exit_cross : Cross zeroFact Gs := by
  refine ⟨rfl, trivial, Or.inr ⟨_, rfl⟩, ?_⟩
  have h : (revEdge zeroFact Gs.fact).1.kind = .exact := by decide
  rw [h]
  trivial

/-- Every record set of the next forward run that `NextRecs` allows holds the record. -/
theorem rec_next {rc rcn : Recs} {DBk : Obj → Prop}
    (h : NextRecs PS (D PS cnt 1 policy1 sinksS [0]) rc DBk rcn) : rcn 1 (zeroFact, Gs) :=
  h.fwd _ _ _ run1_exit.1 run1_exit.2 exit_cross

/-- With no source seeded, the source of `mk` is dropped from the restricted program. -/
theorem src_dropped :
    (zeroFact, (⟨2, [], .exact, .conc 1⟩ : PFact)) ∉
      (FSeeds.keepStmt (fun _ _ _ => false) 1 0 srcM).edges :=
  FSeeds.unseeded_dropped (by decide) rfl

/-- THE RECORD CROSSES THE CALL WITH NO SEED: forward run 2 on `keepSources PS σ` (every `σ`, also
    `σ = false`), for every demand and every record set that holds the run-1 record of `mk`,
    reports the vulnerability in the NORMAL layer. -/
theorem found_unseeded (σ : MethodId → Node → MicroEdge → Bool) (L : Nat)
    (dem : MethodId → DemandEdge → Prop) (rc : Recs) (h : rc 1 (zeroFact, Gs)) :
    DR (FSeeds.keepSources PS σ) cnt L dem emitM satI restrictI rc sinksS [0]
      (.vuln 0 1 sinkS false) := by
  have e0 : DR (FSeeds.keepSources PS σ) cnt L dem emitM satI restrictI rc sinksS [0]
      (.edge 0 zeroFact 0 Backward.zeroAF) := DR.start (DR.root (List.Mem.head _))
  have e1 : DR (FSeeds.keepSources PS σ) cnt L dem emitM satI restrictI rc sinksS [0]
      (.edge 0 zeroFact 1 (limitF cnt L ⟨⟨1, [], .exact, .conc 1⟩, false⟩)) :=
    DR.retRec (c := callM) (e1 := zb) (a := Backward.zeroAF) (j := zeroFact) (g := Gs) (r := Gs)
      (e2 := br) e0 (FSeeds.mem_keep_call hE0) (List.Mem.head _) (by decide) h
      (Or.inl (by decide)) (by decide) (List.Mem.head _) (by decide)
  have hl : limitF cnt L (⟨⟨1, [], .exact, .conc 1⟩, false⟩ : AFact) =
      ⟨⟨1, [], .exact, .conc 1⟩, false⟩ := by
    cases L <;> rfl
  rw [hl] at e1
  exact DR.vuln e1 (s := sinkS) (List.Mem.head _) (by decide)

end SrcRec

#print axioms SrcRec.hE0
#print axioms SrcRec.hE1
#print axioms SrcRec.run1_exit
#print axioms SrcRec.exit_cross
#print axioms SrcRec.rec_next
#print axioms SrcRec.src_dropped
#print axioms SrcRec.found_unseeded

end ApSpec.HandoffSrc
