/-
  ApSpec.NDZeroThms — the theorems of the zero-drop closure `NDZ.DNz` (spec ap.md §4.6, §4.9,
  §10.6; analyzer-core.md §5.4). They come from the theorems of `ND.DN` through the
  correspondence of `ApSpec.NDZero`: Z1 (`dn_to_dnz`) for the soundness side, Z2 (`dnz_to_dn`)
  for the precision side.

  Contents:
    * Part 1. `zeroLinks_of_noZeroGen`: the hypothesis `NDZero.ZeroLinks` of Z1 follows from the
      program condition `NDZeroBase.NoZeroGen` and the abstraction condition
      `NDZeroBase.AlphaZero` (the zero base holds only the zero fact, spec §3.5, S11 (c), (d)).
      The invariant `zero_base_inv_dn` is the `DN` form of `NDZeroBase.zero_base_inv`, with one
      more part: a fact on the zero base has only zero premises.
    * Part 2. THE COVERAGE THEOREM of `DNz` (`nd_coverage_z`, through Z1): a derivation of the
      support semantics and initial facts of `DNz` that cover its support give the edge keyed by
      `dropZ` of EXACTLY those initial facts, or a request. `nd_coverage_single_z`: one premise.
      `nd_coverage_zg`: the same form under the program conditions instead of `ZeroLinks`.
    * Part 3. THE VULNERABILITY THEOREM of `DNz` (`nd_vuln_found_z`, `nd_vuln_reach_z`, through
      Z1; `nd_vuln_found_zg` under the program conditions).
    * Part 4. THE EXACTNESS THEOREM of `DNz` (`nd_edge_exact_z`, `nd_edge_exact_valid_z`, through
      Z2): a normal edge of `DNz` is the image of a normal edge of `DN`. Its support `L'` (one
      location per member of `P'`) is a sub-list of a support `L0` that is real for the support
      semantics; the other locations of `L0` are the zero location. So the zero location is the
      only location that `DNz` does not list (the zero fact is everywhere).
    * Part 5. THE CONFIRMATION of `DNz`. `SupNz`/`SupSlotsNz`: the joint support of a `DNz`
      premise set (spec §4.9 condition 3, as `NDConfirmed.SupN`). `ConfirmedNz`: the three
      conditions on a `DNz` sink edge. `confirmedNz_N`: a confirmation of `DNz` is a
      confirmation of the corresponding `DN` vulnerability; the zero members of the `DN` premise
      list are supported by the caller zero edges at the same call (`ZeroData`, Z0). A zero
      member needs, at the call node, a normal caller edge whose premise list is supported and
      whose binding gives the zero fact: the caller zero edge with the zero binding, and
      `SupN [zeroFact]` of the caller (`supN_zero`: every supported list with a member gives
      it). So `SupN` needs no new hypothesis. `confirmedNz_vuln`: a confirmed vulnerability is
      a normal `vuln` of `DNz`. `confirmed_real_Nz`, `confirmed_real_Nz_valid`,
      `confirmed_real_Nz_valid_of`: THE CONFIRMATION THEOREMS of `DNz`.

  Hypotheses: the theorems of `ND.DN` that they use, the Z0 hypotheses (`Backward.ZeroKept`,
  `NDZero.ZeroCalls`, `NDZero.ConjAdj`, the zero abstraction) for Z2, and `NDZero.ZeroLinks` for
  Z1. `NDZeroBase` is the module of the pipeline package; this file uses its program condition
  `NoZeroGen` and its lemmas on the zero base.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.NDZero
import ApSpec.NDZeroBase

namespace ApSpec.NDZero
open ApSpec ApSpec.ND ApSpec.NDZ ApSpec.NDExact ApSpec.NDConfirmed

/-! ## Part 1. `ZeroLinks` from the program conditions -/

section ZeroBase
open NDZeroBase
variable {X : Ctx}

/-- The zero-base invariant of `DN` (`NDZeroBase.ZMot` for `DN`), and one more part: an edge
    whose conclusion is on the zero base has only zero premises. -/
def ZBMot (X : Ctx) : NObj → Prop
  | .ninit _ i => ZOnly i
  | .nedge _ P _ f => (∀ p ∈ P, ZOnly p) ∧ ZOnly f.fact ∧
      (f.fact.base = zeroBase → ∀ p, p ∈ P → p = zeroFact)
  | .nadded _ a => ZOnly a
  | .nreq _ i _ => ZOnly i
  | .nvuln .. => True
  | .npart M n c n' _ P _ => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧ ∀ p ∈ P, ZOnly p

/-- A statement result on the zero base comes from a fact on the zero base. -/
theorem transfer_from_zero {counted : Acc → Bool} {L : Nat} {s : Stmt} {f f' : AFact}
    (hs : ∀ e ∈ s.edges, e.2.base = zeroBase → e = (zeroFact, zeroFact))
    (h : f' ∈ (transfer counted L s f).facts) (hz : f'.fact.base = zeroBase) :
    f.fact.base = zeroBase := by
  unfold transfer at h
  split at h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    obtain ⟨e, he, hre⟩ := mem_applyAll_inv hr
    rw [limitF_base] at hz
    have ⟨hb1, hb2⟩ := applyEdge_base hre
    have he0 := hs e he (hb1 ▸ hz)
    rw [hb2, he0]
    rfl
  · rw [List.mem_singleton.1 h] at hz
    exact hz

/-- THE ZERO-BASE INVARIANT OF `DN` under `NoZeroGen` and `AlphaZero`. -/
theorem zero_base_inv_dn (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {o : NObj} (h : DN X o) :
    ZBMot X o := by
  induction h with
  | root => exact zOnly_zero
  | start _ ih =>
    refine ⟨fun p hp => (List.mem_singleton.1 hp) ▸ ih, ?_, ?_⟩
    · intro hz
      rw [startFact_base] at hz
      rw [ih hz]
      rfl
    · intro hz p hp
      rw [startFact_base] at hz
      rw [List.mem_singleton.1 hp]
      exact ih hz
  | step _ he hf ih =>
    refine ⟨ih.1, transfer_zero (hG.stmt _ _ _ _ he) ih.2.1 hf, fun hz => ?_⟩
    exact ih.2.2 (transfer_from_zero (hG.stmt _ _ _ _ he) hf hz)
  | reqStmt _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | pass _ _ _ ih => exact ih
  | added _ he he1 ha ih =>
    intro hz
    have ⟨hb1, hb2⟩ := applyEdge_base ha
    obtain rfl := hG.toCallee _ _ _ _ he _ he1 (hb1 ▸ hz)
    rw [afact_zero (ih.2.1 hb2), applyEdge_zStar] at ha
    rw [List.mem_singleton.1 ha]
  | initA _ ih =>
    intro hz
    rw [hα.base] at hz
    rw [ih hz, hα.zero]
  | ret _ he _ _ _ _ _ _ he2 hr' ihf =>
    refine ⟨ihf.1, back_not_zero hG he he2 hr', fun hz => ?_⟩
    rw [limitF_base, (applyEdge_base hr').1] at hz
    exact absurd hz (hG.fromCallee _ _ _ _ he _ he2)
  | ndOpen he => exact ⟨he, fun _ hp => absurd hp List.not_mem_nil⟩
  | ndBind _ _ _ _ _ ihp ihf =>
    refine ⟨ihp.1, fun p hp => ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact ihp.2 p hp
    · exact ihf.1 p hp
  | ndRet _ he2 hr ihp =>
    refine ⟨ihp.2, back_not_zero hG ihp.1 he2 hr, fun hz => ?_⟩
    rw [limitF_base, (applyEdge_base hr).1] at hz
    exact absurd hz (hG.fromCallee _ _ _ _ ihp.1 _ he2)
  | reqSink _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | @answer M i t a _ _ hm hov ihr iha =>
    intro hz
    rw [answerInit_base] at hz
    have hi := ihr hz
    subst hi
    have ha := iha ((overlapB_base hov).trans hz)
    subst ha
    cases hm
    rw [answerInit_zero]
    rfl
  | reqUp _ _ _ _ _ _ _ _ _ ihf => exact ihf.1 _ List.mem_cons_self
  | vuln => trivial
  | clean _ _ hf ih =>
    refine ⟨ih.1, fun hz => ?_, fun hz => ih.2.2 (by rw [← cleanRes_base hf]; exact hz)⟩
    rw [cleanRes_base hf] at hz
    rw [afact_zero (ih.2.1 hz)] at hf
    exact cleanRes_zero hf
  | reqClean _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | filt _ _ _ ih => exact ih
  | conj _ _ hcj _ _ _ _ ih1 ih2 =>
    refine ⟨fun p hp => ?_, fun hz => absurd hz (hG.conj _ _ _ _ hcj),
      fun hz => absurd hz (hG.conj _ _ _ _ hcj)⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact ih1.1 p hp
    · exact ih2.1 p hp
  | reqConj _ _ _ _ _ ih => exact ih.1 _ List.mem_cons_self

#print axioms zero_base_inv_dn

/-- `ZeroLinks` holds under the program condition `NoZeroGen` and the abstraction condition
    `AlphaZero` (spec §3.5: the zero base of a callee is bound only by the zero binding, and the
    zero base of the caller holds only the zero fact). -/
theorem zeroLinks_of_noZeroGen (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) : ZeroLinks X := by
  intro M P n f n' c e a hE hf he ha hap
  have hab : a.fact.base = zeroBase := (applicable_base hap).symm
  have ⟨hb1, hb2⟩ := applyEdge_base ha
  have he0 := hG.toCallee _ _ _ _ hE _ he (hb1 ▸ hab)
  subst he0
  exact (zero_base_inv_dn hG hα hf).2.2 hb2

#print axioms zeroLinks_of_noZeroGen

end ZeroBase


/-! ## Part 2. The coverage theorem of `DNz` -/

section Coverage
variable {X : Ctx}

/-- THE COVERAGE THEOREM OF `DNz` (run 1; `ND.nd_coverage` through Z1). Let a derivation
    `TaintN Q M n l L0` be given, and one initial fact of `M` in `DNz` for each support location,
    which covers it (the list `I`). Then the edge of `DNz` keyed by `dropZ I` (the given initial
    facts without the zero fact) is at `n` and covers `l` (with the pair, for one premise and one
    support location), or `DNz` has a request on the initial fact of one position, with the mark
    of the support location at that position. -/
theorem nd_coverage_z (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} (h : TaintN X.Q M n l L0)
    (I : List PFact) (hI : Al (fun i k => DNz X (.ninit M i) ∧ i.covers k) I L0) :
    (∃ f, DNz X (.nedge M (dropZ I) n f) ∧ NRel I L0 f.fact l) ∨
      ∃ i k, PairIn i k I L0 ∧ DNz X (.nreq M i k.mark) := by
  have hI' : Al (IC X M) I L0 :=
    Al.mono (fun _ _ hik => ⟨dnz_to_dn hwf hZ hC hA hαz hik.1, hik.2⟩) hI
  rcases nd_coverage hwf hα h I hI' with ⟨f, hf, hrel⟩ | ⟨i, k, hp, hq⟩
  · obtain ⟨f', hf', hc⟩ := dn_to_dnz hwf hzl hf
    exact .inl ⟨f', hf', by rw [← hc.1]; exact hrel⟩
  · exact .inr ⟨i, k, hp, dn_to_dnz hwf hzl hq⟩

#print axioms nd_coverage_z

/-- One support location and one premise (the form of `ND.nd_coverage_single`). -/
theorem nd_coverage_single_z (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {n : Node} {l l0 : Loc} {i : PFact} (h : TaintN X.Q M n l [l0])
    (hi : DNz X (.ninit M i)) (hc : i.covers l0) :
    (∃ f, DNz X (.nedge M [i] n f) ∧ den i f.fact l0 l) ∨ DNz X (.nreq M i l0.mark) := by
  rcases nd_coverage_z hwf hα hZ hC hA hαz hzl h [i] (.cons ⟨hi, hc⟩ .nil) with
    ⟨f, hf, hrel⟩ | ⟨i', k, hp, hq⟩
  · rw [dropZ_single] at hf
    exact .inl ⟨f, hf, hrel.2 i l0 rfl rfl⟩
  · cases hp with
    | head => exact .inr hq
    | tail hp' => cases hp'

#print axioms nd_coverage_single_z

/-- THE COVERAGE THEOREM OF `DNz` under the program conditions: `NoZeroGen` and `AlphaZero` give
    `ZeroLinks` and the zero abstraction. -/
theorem nd_coverage_zg (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hG : NDZeroBase.NoZeroGen X.Q) (hαZ : NDZeroBase.AlphaZero X.α)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} (h : TaintN X.Q M n l L0)
    (I : List PFact) (hI : Al (fun i k => DNz X (.ninit M i) ∧ i.covers k) I L0) :
    (∃ f, DNz X (.nedge M (dropZ I) n f) ∧ NRel I L0 f.fact l) ∨
      ∃ i k, PairIn i k I L0 ∧ DNz X (.nreq M i k.mark) :=
  nd_coverage_z hwf hα hZ hC hA hαZ.zero (zeroLinks_of_noZeroGen hG hαZ) h I hI

#print axioms nd_coverage_zg

end Coverage

/-! ## Part 3. The vulnerability theorem of `DNz` -/

section Vuln
variable {X : Ctx}

/-- THE VULNERABILITY THEOREM OF `DNz` for a tree witness (`ND.nd_vuln_reach` through Z1). -/
theorem nd_vuln_reach_z (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hzl : ZeroLinks X) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : ReachN X.Q X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNz X (.nvuln M n s b) := by
  obtain ⟨b, hb⟩ := nd_vuln_reach hwf hα hR hs hT hsc
  exact dn_to_dnz hwf hzl hb

#print axioms nd_vuln_reach_z

/-- THE VULNERABILITY THEOREM OF `DNz` (`ND.nd_vuln_found` through Z1): a real execution from a
    root that taints a location covered by a sink pattern gives a `vuln` object of `DNz`. -/
theorem nd_vuln_found_z (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hzl : ZeroLinks X) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.Q.prog X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNz X (.nvuln M n s b) := by
  obtain ⟨b, hb⟩ := nd_vuln_found hwf hα hR hs hT hsc
  exact dn_to_dnz hwf hzl hb

#print axioms nd_vuln_found_z

/-- The vulnerability theorem of `DNz` under the program conditions. -/
theorem nd_vuln_found_zg (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hG : NDZeroBase.NoZeroGen X.Q) (hαZ : NDZeroBase.AlphaZero X.α)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.Q.prog X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNz X (.nvuln M n s b) :=
  nd_vuln_found_z hwf hα (zeroLinks_of_noZeroGen hG hαZ) hR hs hT hsc

#print axioms nd_vuln_found_zg

end Vuln

/-! ## Part 4. The exactness theorem of `DNz` -/

section Exact
variable {X : Ctx}

/-- The zero fact covers only the zero location. -/
theorem zero_covers_only {k : Loc} (h : zeroFact.covers k) : k = zeroLoc := by
  obtain ⟨hb, ⟨σ, hp, hσ⟩, hm⟩ := h
  have hσ' : σ = [] := hσ
  subst hσ'
  obtain ⟨kb, kp, km⟩ := k
  change kb = zeroBase at hb
  change kp = [] ++ [] at hp
  change km = zeroMark at hm
  subst hb hp hm
  rfl

/-- Fill the support of the members that are not the zero fact with zero locations. -/
theorem fill_zero : ∀ {P : List PFact} {L' : List Loc}, PremCov (nz P) L' →
    ∃ L0, PremCov P L0 ∧ L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc
  | [], L', h => by
    have h' : PremCov [] L' := h
    cases h'
    exact ⟨[], .nil, List.Sublist.slnil, fun _ hk => absurd hk List.not_mem_nil⟩
  | p :: P, L', h => by
    by_cases hp : p = zeroFact
    · subst hp
      rw [nz_cons_zero] at h
      obtain ⟨L0, hL0, hsub, hmem⟩ := fill_zero h
      refine ⟨zeroLoc :: L0, .cons zeroFact_covers hL0, hsub.cons _, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · exact .inr rfl
      · exact hmem k hk
    · rw [nz_cons_ne _ hp] at h
      cases h with
      | @cons _ k _ L'' hr hrest =>
        obtain ⟨L0, hL0, hsub, hmem⟩ := fill_zero hrest
        refine ⟨k :: L0, .cons hr hL0, hsub.cons_cons _, fun k' hk => ?_⟩
        rcases List.mem_cons.mp hk with rfl | hk
        · exact .inl List.mem_cons_self
        · rcases hmem k' hk with h1 | h1
          · exact .inl (List.mem_cons_of_mem _ h1)
          · exact .inr h1

/-- A support of `dropZ P` gives a support of `P`: the same locations and zero locations. -/
theorem fill_dropZ {P : List PFact} {L' : List Loc} (hP : P ≠ []) (h : PremCov (dropZ P) L') :
    ∃ L0, PremCov P L0 ∧ L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc := by
  rcases dropZ_cases P with ⟨h1, h2⟩ | ⟨_, h2⟩
  · rw [h2] at h
    obtain ⟨k, rfl, hk⟩ := Al.single h
    have hk0 := zero_covers_only hk
    subst hk0
    have hall := nz_eq_nil_iff.mp h1
    refine ⟨P.map (fun _ => zeroLoc), premCov_zero hall, ?_, fun k hk => .inr (mem_map_zero hk)⟩
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hP
    exact (List.nil_sublist _).cons_cons _
  · rw [h2] at h
    exact fill_zero h

/-- The lift of a normal `DNz` edge and of a support of its premises to `DN`. -/
theorem dnz_edge_lift (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P' : List PFact}
    {n : Node} {f' : AFact} (h : DNz X (.nedge M P' n f')) (ha : f'.demand = false)
    {L' : List Loc} {l : Loc} (hP' : PremCov P' L') (hrel : NRel P' L' f'.fact l) :
    ∃ P f L0, DN X (.nedge M P n f) ∧ f.demand = false ∧ PremCov P L0 ∧ NRel P L0 f.fact l ∧
      L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc := by
  obtain ⟨P, f, hD, hPP, hfa, hfd⟩ := dnz_to_dn_edge hwf hZ hC hA hαz h
  subst hPP
  obtain ⟨L0, hL0, hsub, hmem⟩ := fill_dropZ (premises_ne_nil hwf hD) hP'
  refine ⟨P, f, L0, hD, hfd ha, hL0, ⟨by rw [hfa]; exact hrel.1, fun i l0 hPi hLi => ?_⟩, hsub, hmem⟩
  subst hPi hLi
  rw [dropZ_single] at hP' hrel
  obtain ⟨k, rfl, _⟩ := Al.single hP'
  have hk : k = l0 := List.mem_singleton.mp (List.singleton_sublist.mp hsub)
  subst hk
  rw [hfa]
  exact hrel.2 i k rfl rfl

/-- THE EXACTNESS THEOREM OF `DNz` (`NDExact.nd_edge_exact` through Z2). A normal-layer edge of
    `DNz` denotes only taintings of `TaintN`: for every support `L'` that its premises cover and
    every end location in the relation `NRel`, the location is tainted with a support `L0` that
    contains `L'` as a sub-list, and whose other locations are the zero location (the zero fact
    that `dropZ` removed). The hypotheses: those of `nd_edge_exact`, and those of Z2. -/
theorem nd_edge_exact_z (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hmw : Exact.MarkWF X.Q.prog)
    (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q) {M : MethodId} {P' : List PFact} {n : Node}
    {f' : AFact} (h : DNz X (.nedge M P' n f')) (ha : f'.demand = false) :
    ∀ L' l, PremCov P' L' → NRel P' L' f'.fact l →
      ∃ L0, TaintN X.Q M n l L0 ∧ L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc := by
  intro L' l hP' hrel
  obtain ⟨P, f, L0, hD, hfd, hL0, hrel0, hsub, hmem⟩ := dnz_edge_lift hwf hZ hC hA hαz h ha hP' hrel
  exact ⟨L0, nd_edge_exact hmw hup hlc hD hfd L0 l hL0 hrel0, hsub, hmem⟩

#print axioms nd_edge_exact_z

/-- THE EXACTNESS THEOREM OF `DNz` FOR VALID LOCATIONS (`NDExact.nd_edge_exact_valid` through
    Z2): the support of a valid end location is valid too. -/
theorem nd_edge_exact_valid_z (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) {M : MethodId}
    {P' : List PFact} {n : Node} {f' : AFact} (h : DNz X (.nedge M P' n f'))
    (ha : f'.demand = false) :
    ∀ L' l, PremCov P' L' → NRel P' L' f'.fact l → ok l →
      ∃ L0, TaintN X.Q M n l L0 ∧ L'.Sublist L0 ∧ (∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc) ∧
        ∀ k, k ∈ L0 → ok k := by
  intro L' l hP' hrel hok
  obtain ⟨P, f, L0, hD, hfd, hL0, hrel0, hsub, hmem⟩ := dnz_edge_lift hwf hZ hC hA hαz h ha hP' hrel
  obtain ⟨hT, hokL⟩ := nd_edge_exact_valid hmw hv hbo hlc hco hD hfd L0 l hL0 hrel0 hok
  exact ⟨L0, hT, hsub, hmem, hokL⟩

#print axioms nd_edge_exact_valid_z

end Exact

/-! ## Part 5. The confirmation of `DNz` -/

mutual
/-- `SupNz X M P`: the premise set `P` of an edge of `DNz` is supported JOINTLY (spec §4.9
    condition 3; the form of `NDConfirmed.SupN`).
    * `root`: `M` is a root and every premise is the zero fact;
    * `call`: ONE call statement `(M', n, c, n')` to `M` supplies every premise (`SupSlotsNz`). -/
inductive SupNz (X : Ctx) : MethodId → List PFact → Prop where
  | root {M P} : M ∈ X.roots → (∀ p, p ∈ P → p = zeroFact) → SupNz X M P
  | call {M n c n' J} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → SupSlotsNz X M n c J →
      SupNz X c.callee J

/-- `SupSlotsNz X M n c J`: at the call node `n` of `M` (call `c`), every callee premise `j ∈ J`
    has its own normal caller edge of `DNz` at `n`, whose premise set is supported, whose binding
    gives the normal added fact `a`, and `j = a` (the zero fact, or the exact concrete answer of
    `a`). -/
inductive SupSlotsNz (X : Ctx) : MethodId → Node → Call → List PFact → Prop where
  | nil {M n c} : SupSlotsNz X M n c []
  | cons {M n c Pm f e a j J} :
      SupNz X M Pm → DNz X (.nedge M Pm n f) → f.demand = false →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DNz X (.ninit c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DNz X (.nreq c.callee k t) ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧
          j = answerInit k a.fact t ∧ j = a.fact)) →
      SupSlotsNz X M n c J → SupSlotsNz X M n c (j :: J)
end

/-- A CONFIRMED vulnerability of `DNz`: a complete sink edge of `DNz` with the premise set `P`
    (condition 1), exact concrete premises (condition 2), the joint support of `P` (condition 3),
    and a triggered sink check (spec §4.9). -/
def ConfirmedNz (X : Ctx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ P f, DNz X (.nedge M P n f) ∧ f.complete = true ∧ (∀ p, p ∈ P → ExactConc p) ∧
    SupNz X M P ∧ (M, n, s) ∈ X.sinks ∧ ∃ i, i ∈ P ∧ check i f s = .triggered

/-- A confirmed vulnerability of `DNz` is a normal `vuln` object of `DNz`. -/
theorem confirmedNz_vuln {X : Ctx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedNz X M n s) : DNz X (.nvuln M n s false) := by
  obtain ⟨P, f, hD, hc, _, _, hs, i, hi, hch⟩ := h
  have hv := DNz.vuln hD hs hi hch
  rw [Exact.complete_demand hc] at hv
  exact hv

#print axioms confirmedNz_vuln

section Confirm
variable {X : Ctx}

/-- The zero slot of a call `(M, n, c)`: the caller zero edge is supported, the zero binding
    binds it, and the callee has the zero initial fact (Z0). -/
abbrev ZeroData (X : Ctx) (M : MethodId) (n : Node) (c : Call) : Prop :=
  SupN X M [zeroFact] ∧ DN X (.nedge M [zeroFact] n Backward.zeroAF) ∧
    (zStar, zStar) ∈ c.toCallee ∧ DN X (.ninit c.callee zeroFact)

theorem zero_slot {M : MethodId} {n : Node} {c : Call} {J : List PFact} (hd : ZeroData X M n c)
    (hS : SupSlots X M n c J) : SupSlots X M n c (zeroFact :: J) :=
  SupSlots.cons hd.1 hd.2.1 rfl hd.2.2.1 zero_bind rfl hd.2.2.2 (.inl ⟨rfl, rfl⟩) hS

theorem zero_slots {M : MethodId} {n : Node} {c : Call} (hd : ZeroData X M n c) :
    ∀ {Z J : List PFact}, (∀ z, z ∈ Z → z = zeroFact) → SupSlots X M n c J →
      SupSlots X M n c (Z ++ J)
  | [], _, _, hS => hS
  | z :: Z, _, hz, hS => by
    have hz0 := hz z List.mem_cons_self
    subst hz0
    exact zero_slot hd (zero_slots hd (fun x hx => hz x (List.mem_cons_of_mem _ hx)) hS)

mutual
/-- A supported premise list with a member supports the zero premise `[zeroFact]` too: the zero
    edge of each caller is at the same call node (Z0). -/
theorem supN_zero (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {P : List PFact}, SupN X M P → P ≠ [] → SupN X M [zeroFact]
  | _, _, .root hM _, _ => SupN.root hM (fun _ hp => List.mem_singleton.mp hp)
  | _, _, .call hE hS, hne => slots_zero hwf hZ hC hA hαz hS hE hne

theorem slots_zero (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J : List PFact}, SupSlots X M n c J →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → J ≠ [] →
        SupN X c.callee [zeroFact]
  | _, _, _, _, .nil, _, _, hne => absurd rfl hne
  | _, _, _, _, .cons hSm hf _ _ _ _ _ _ _, _, hE, _ => by
    have hz := supN_zero hwf hZ hC hA hαz hSm (premises_ne_nil hwf hf)
    exact SupN.call hE (zero_slot ⟨hz, zero_edge hZ hC hA hαz hf, (hC _ _ _ _ hE).2,
      zero_callee hZ hC hA hαz hf hE⟩ SupSlots.nil)
end

#print axioms supN_zero

mutual
/-- THE SUPPORT TRANSFER: a joint support of a `DNz` premise set is a joint support of every
    `DN` premise list with the same members that are not the zero fact. The zero members are
    supported by the caller zero edges at the same call (`ZeroData`). -/
theorem supNz_supN (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {P' : List PFact}, SupNz X M P' → P' ≠ [] →
      ∀ P, nz P = nz P' → SupN X M P
  | _, _, .root hM hz, _, _, hnz =>
    SupN.root hM (nz_eq_nil_iff.mp (hnz.trans (nz_eq_nil_iff.mpr hz)))
  | _, _, .call hE hS, hne', P, hnz =>
    SupN.call hE (slotsNz_slots hwf hZ hC hA hαz hS hE (slotsNz_zd hwf hZ hC hA hαz hS hE hne') P hnz)

/-- A call with a slot gives the zero slot at the same call node. -/
theorem slotsNz_zd (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J' : List PFact}, SupSlotsNz X M n c J' →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → J' ≠ [] → ZeroData X M n c
  | _, _, _, _, .nil, _, _, hne => absurd rfl hne
  | _, _, _, _, .cons hSm hf _ _ _ _ _ _ _, _, hE, _ => by
    obtain ⟨Pm0, f0, hD, hPm, _, _⟩ := dnz_to_dn_edge hwf hZ hC hA hαz hf
    have hS0 := supNz_supN hwf hZ hC hA hαz hSm (premInit_z hf).1 Pm0 (by rw [← hPm, nz_dropZ])
    exact ⟨supN_zero hwf hZ hC hA hαz hS0 (premises_ne_nil hwf hD), zero_edge hZ hC hA hαz hD,
      (hC _ _ _ _ hE).2, zero_callee hZ hC hA hαz hD hE⟩

/-- The slots of a `DNz` premise set give the slots of a `DN` premise list with the same members
    that are not the zero fact. -/
theorem slotsNz_slots (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J' : List PFact}, SupSlotsNz X M n c J' →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → ZeroData X M n c →
        ∀ J, nz J = nz J' → SupSlots X M n c J
  | _, _, _, _, .nil, _, _, hd, J, hnz => by
    have h := zero_slots hd (nz_eq_nil_iff.mp hnz) SupSlots.nil
    rw [List.append_nil] at h
    exact h
  | _, _, _, _, @SupSlotsNz.cons _ M n c Pm f e a j J' hSm hf hfd he ha had hj hjc hS, _, hE, hd,
      J, hnz => by
    by_cases hj0 : j = zeroFact
    · subst hj0
      rw [nz_cons_zero] at hnz
      exact slotsNz_slots hwf hZ hC hA hαz hS hE hd J hnz
    · rw [nz_cons_ne _ hj0] at hnz
      obtain ⟨zs, tail, rfl, hzs, htail, _⟩ := nz_eq_cons hnz
      apply zero_slots hd hzs
      obtain ⟨Pm0, f0, hD, hPm, hcf, hdf⟩ := dnz_to_dn hwf hZ hC hA hαz hf
      have hf0d : f0.demand = false := by
        cases hb : f0.demand with
        | false => rfl
        | true =>
          have h1 := hdf hb
          rw [hfd] at h1
          exact absurd h1 Bool.false_ne_true
      obtain ⟨a0, ha0, hka⟩ := applyEdge_corr (corr_symm hcf) ha
      have ha0d : a0.demand = false := by
        cases hb : a0.demand with
        | false => rfl
        | true =>
          have h1 := hka.2.2 hdf hb
          rw [had] at h1
          exact absurd h1 Bool.false_ne_true
      have hS0 := supNz_supN hwf hZ hC hA hαz hSm (premInit_z hf).1 Pm0 (by rw [← hPm, nz_dropZ])
      have hjD : DN X (.ninit c.callee j) := dnz_to_dn hwf hZ hC hA hαz hj
      have hfa : a.fact = a0.fact := hka.1.1
      have hjc' : (j = zeroFact ∧ a0.fact = zeroFact) ∨
          (∃ k t, DN X (.nreq c.callee k t) ∧ a0.fact.kind = .exact ∧ a0.fact.mark = .conc t ∧
            j = answerInit k a0.fact t ∧ j = a0.fact) := by
        rw [← hfa]
        rcases hjc with h1 | ⟨k, t, hq, hak, ham, hans, hja⟩
        · exact .inl h1
        · exact .inr ⟨k, t, dnz_to_dn hwf hZ hC hA hαz hq, hak, ham, hans, hja⟩
      exact SupSlots.cons hS0 hD hf0d he ha0 ha0d hjD hjc'
        (slotsNz_slots hwf hZ hC hA hαz hS hE hd tail htail)
end

#print axioms supNz_supN

/-- A CONFIRMATION OF `DNz` IS A CONFIRMATION OF `DN`: the corresponding `DN` sink edge (Z2) is
    complete, its premises are exact and concrete (a zero member is the zero fact), its premise
    list is supported jointly (the zero members by the caller zero edges, `supNz_supN`), and its
    sink check triggers. -/
theorem confirmedNz_N (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {n : Node}
    {s : PFact} (h : ConfirmedNz X M n s) : ConfirmedN X M n s := by
  obtain ⟨P', f', hD', hc', hex', hS', hs, i, hi, hch⟩ := h
  obtain ⟨P, f, hD, hPP, hfa, hfd⟩ := dnz_to_dn_edge hwf hZ hC hA hαz hD'
  have hne := premises_ne_nil hwf hD
  have hfd' := hfd (Exact.complete_demand hc')
  refine ⟨P, f, hD, ?_, fun p hp => ?_, supNz_supN hwf hZ hC hA hαz hS' (premInit_z hD').1 P
    (by rw [← hPP, nz_dropZ]), hs, i, mem_of_mem_dropZ hne (hPP ▸ hi), ?_⟩
  · unfold AFact.complete at hc' ⊢
    rw [hfd', hfa]
    rw [Exact.complete_demand hc'] at hc'
    exact hc'
  · by_cases hp0 : p = zeroFact
    · rw [hp0]
      exact ⟨rfl, zeroMark, rfl⟩
    · exact hex' p (by rw [← hPP]; exact mem_dropZ.mpr (.inl ⟨hp, hp0⟩))
  · rw [check_corr hfa]
    exact hch

#print axioms confirmedNz_N

/-- THE CONFIRMATION THEOREM OF `DNz` (programs without a real type filter, `FiltUp`;
    `NDConfirmed.confirmed_real_N` through `confirmedNz_N`): a confirmed vulnerability of `DNz` is
    real against the support semantics. -/
theorem confirmed_real_Nz (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNz X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l :=
  confirmed_real_N hwf hmw hup hlc (confirmedNz_N hwf hZ hC hA hαz h)

#print axioms confirmed_real_Nz

/-- THE CONFIRMATION THEOREM OF `DNz`, generic validity (`confirmed_real_N_valid_of`). -/
theorem confirmed_real_Nz_valid_of (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNz X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) :=
  confirmed_real_N_valid_of hwf hmw hv hbo hlc hco (confirmedNz_N hwf hZ hC hA hαz h)

#print axioms confirmed_real_Nz_valid_of

/-- THE CONFIRMATION THEOREM OF `DNz` FOR VALID LOCATIONS (`confirmed_real_N_valid`): if every
    location of the sink pattern is valid, a confirmed vulnerability of `DNz` is real. -/
theorem confirmed_real_Nz_valid (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedNz X M n s) : ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l :=
  confirmed_real_N_valid hwf hmw hv hbo hlc hco hok (confirmedNz_N hwf hZ hC hA hαz h)

#print axioms confirmed_real_Nz_valid

end Confirm

end ApSpec.NDZero
