/-
  ApSpec.PipelineNDZ — the closure `NDZ.DNz` as an instance of the communication pipeline
  (`ApSpec.Pipeline`; analyzer-core.md §5.4, §5.5; ap.md §4.6).

  `DNz` is the ND closure that the spec and the analyzer compute: a conjunction and an ND summary
  application join the premise lists WITHOUT THE ZERO FACT (`NDZ.dropZ`). §7 of `PipelineAP.lean`
  encodes `ND.DN` as `sysDN`. This file encodes `DNz` as `sysDNz` in the same way.

  HOW `sysDNz` DIFFERS FROM `sysDN`. The change is local. Only the premise list of two results
  changes:
    * `RuleNz`: every local rule of `sysDN` but the conjunction (`RuleNz.keep`), and a conjunction
      that gives `dropZ (P1 ++ P2)` (`RuleNz.conj`). The conjunction is the only rule of `sysDN`
      with two edge premises (`TwoEdges`), so `keep` excludes it by the shape of its premises.
    * `JoinNz`: the single-premise join of `sysDN` (`JoinNz.ret`: a join with a `pub`), and a
      k-ary join that gives `dropZ P` of the joined caller premise lists (`JoinNz.nd`).
  The objects `NPObj`, the owners, the topics, the roots, the combinations `Combo`, the filter
  `NoPart` and the meaning of a link `LinkOK` are those of `sysDN` (we use them from
  `PipelineAP`). So the subscriptions, the publications and the k-ary join are as in `sysDN`.

  THE ZERO FACT IN A k-ARY JOIN. An edge of `DNz` with two or more premises has no zero member
  (`dnz_nd_no_zero`). So a publication with several premises has no zero member
  (`clDNz_ndpub_no_zero`), and no index of a k-ary join is the zero fact. In `sysDN`, the
  subscription of the caller zero edge supplies the zero member; in `sysDNz` there is no zero
  member to supply (analyzer-core.md §5.4). The zero subscription also satisfies no OTHER
  member: `applicable p zeroFact` can hold for a premise `p ≠ zeroFact` on the zero base (for
  example `zStar`), but under the program condition `NDZeroBase.NoZeroGen` and the abstraction
  condition `NDZeroBase.AlphaZero` every premise on the zero base is the zero fact
  (`NDZeroBase.dnz_applicable_zero`). So no index of a publication with several premises is
  satisfied by a fact on the zero base (`clDNz_ndpub_zero_base`), in particular not by the zero
  added fact (`clDNz_ndpub_zero_sub`), and every subscription of a k-ary join of the closure
  binds a fact off the zero base (`joinNz_nd_no_zero_sub`).

  Main theorems (the context `X` is a variable):
    * `sysDNz_wf`: `sysDNz` is well formed (`Sys.WF`). The proof uses `sysDN_wf`: each rule and
      each join of `sysDNz` has the premises of a rule or a join of `sysDN` (`ruleNz_shape`,
      `joinNz_shape`), and `Sys.WF` reads only the premises.
    * `clDNz_iff`: `Cl (sysDNz X) (.base o) ↔ DNz X o ∧ NoPart o` (analyzer-core.md §5.5). The
      forms per object: `clDNz_nedge`, `clDNz_ninit`, `clDNz_nadded`, `clDNz_nreq`, `clDNz_nvuln`;
      the partial matches are not objects: `clDNz_npart`.
    * `clDNz_link`, `clDNz_sub`, `clDNz_pub`, `clDNz_ndpub`: the link, the subscription and the
      publications are exactly the data that the rules of `DNz` read.
    * `dnz_nd_no_zero`, `clDNz_ndpub_no_zero`: no zero member in a summary with several premises
      (ap.md §4.6, analyzer-core.md §5.4).
    * `clDNz_ndpub_zero_base`, `clDNz_ndpub_zero_sub`, `joinNz_nd_no_zero_sub` (under
      `NoZeroGen X.Q` and `AlphaZero X.α`): the zero subscription never takes part in a k-ary
      join (analyzer-core.md §5.4).
    * `result_DNz`: at a reachable quiescent state of `sysDNz`, the processed `base` objects are
      exactly the objects of `DNz` without the partial matches (`Pipeline.quiescent_exact`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.PipelineProofs
import ApSpec.PipelineAP
import ApSpec.NDZ
import ApSpec.NDZeroBase

namespace ApSpec.PipelineNDZ
open ApSpec ApSpec.Pipeline ApSpec.PipelineAP ApSpec.ND ApSpec.NDZ ApSpec.NDZeroBase

/-! ## 1. The encoding -/

/-- The premises are two edges. In `sysDN`, only the conjunction `RuleN.conj` has this shape. -/
def TwoEdges (ps : List NPObj) : Prop :=
  ∃ (M1 : MethodId) (P1 : List PFact) (n1 : Node) (f1 : AFact)
    (M2 : MethodId) (P2 : List PFact) (n2 : Node) (f2 : AFact),
    ps = [.base (.nedge M1 P1 n1 f1), .base (.nedge M2 P2 n2 f2)]

theorem notTwo_one {x : NPObj} : ¬ TwoEdges [x] := by
  rintro ⟨_, _, _, _, _, _, _, _, h⟩
  cases h

variable (X : Ctx)

/-- The local rules of `DNz`: the local rules of `sysDN` but the conjunction, and the
    conjunction that joins the premise lists without the zero fact (ap.md §4.6). -/
inductive RuleNz : List NPObj → NPObj → Prop where
  | keep {ps c} : RuleN X ps c → ¬ TwoEdges ps → RuleNz ps c
  | conj {M P1 n f1 P2 f2 cj n'} : (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      RuleNz [.base (.nedge M P1 n f1), .base (.nedge M P2 n f2)]
        (.base (.nedge M (dropZ (P1 ++ P2)) n' (conjFact cj f1 f2)))

/-- The joins of `DNz`: the single-premise join of `sysDN` (with a `pub`), and the k-ary join
    whose result has the joined caller premise lists without the zero fact (analyzer-core.md
    §5.4). -/
inductive JoinNz : List NPObj → NPObj → NPObj → Prop where
  | ret {ss m j g c} : JoinN X ss (.pub m j g) c → JoinNz ss (.pub m j g) c
  | nd {M n n' c Pc ss P d g e2 r} : Combo M n n' c Pc ss P d → 2 ≤ Pc.length →
      e2 ∈ c.fromCallee → r ∈ (applyEdge ⟨g.fact, g.demand || d⟩ e2.1 e2.2).facts →
      JoinNz ss (.ndpub c.callee Pc g)
        (.base (.nedge M (dropZ P) n' (limitF X.counted X.FL r)))

/-- The ND run of the spec as a pipeline system: `sysDN` with the rules `RuleNz` and the joins
    `JoinNz`. -/
def sysDNz : Sys NPObj MethodId MethodId :=
  { sysDN X with rule := RuleNz X, join := JoinNz X }

/-- What a subscription of `DNz` means. -/
def NSubOKz (M : MethodId) (Pc : List PFact) (n n' : Node) (c : Call) (a : AFact) : Prop :=
  ∃ (f : AFact) (e : MicroEdge), DNz X (.nedge M Pc n f) ∧
    (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧ e ∈ c.toCallee ∧ a ∈ (applyEdge f e.1 e.2).facts

/-- The invariant of `sysDNz`. -/
def InvNz : NPObj → Prop
  | .base o => DNz X o ∧ NoPart o
  | .link m a M Pc => LinkOK X.Q.prog (fun M P n f => DNz X (.nedge M P n f)) m a M Pc
  | .sub M Pc n n' c a => NSubOKz X M Pc n n' c a
  | .pub m j g => DNz X (.ninit m j) ∧ DNz X (.nedge m [j] (X.Q.prog.exit m) g)
  | .ndpub m Pc g => DNz X (.nedge m Pc (X.Q.prog.exit m) g) ∧ 2 ≤ Pc.length

/-- The induction motive of the completeness proof (as `MotN` of `PipelineAP`). A partial match
    of `DNz` is a partial combination: a publication `cs ++ rest → g0` in the pipeline closure
    and subscriptions in the pipeline closure that match `cs`. -/
def MotNz : NObj → Prop
  | .npart M n c n' rest P g =>
    (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
    ∃ (cs : List PFact) (g0 : AFact) (ss : List NPObj) (d : Bool),
      Cl (sysDNz X) (.ndpub c.callee (cs ++ rest) g0) ∧ 2 ≤ (cs ++ rest).length ∧
      (∀ s ∈ ss, Cl (sysDNz X) s) ∧ Combo M n n' c cs ss P d ∧ g = ⟨g0.fact, g0.demand || d⟩
  | o => Cl (sysDNz X) (.base o)

variable {X}

/-! ## 2. Well-formedness (from `sysDN_wf`) -/

/-- A rule of `sysDNz` has the premises of a rule of `sysDN`. -/
theorem ruleNz_shape {ps : List NPObj} {c : NPObj} (h : RuleNz X ps c) :
    ∃ c', RuleN X ps c' := by
  cases h with
  | keep h _ => exact ⟨_, h⟩
  | conj hcj ho1 hg1 ho2 hg2 => exact ⟨_, RuleN.conj hcj ho1 hg1 ho2 hg2⟩

/-- A join of `sysDNz` has the subscriptions and the publication of a join of `sysDN`. -/
theorem joinNz_shape {ss : List NPObj} {p c : NPObj} (h : JoinNz X ss p c) :
    ∃ c', JoinN X ss p c' := by
  cases h with
  | ret h => exact ⟨_, h⟩
  | nd hc hlen he2 hr => exact ⟨_, JoinN.nd hc hlen he2 hr⟩

/-- `sysDNz` is well formed. -/
theorem sysDNz_wf : (sysDNz X).WF where
  rule_ne ps _ h :=
    let ⟨_, h'⟩ := ruleNz_shape h
    (sysDN_wf (X := X)).rule_ne ps _ h'
  rule_local ps _ h :=
    let ⟨_, h'⟩ := ruleNz_shape h
    (sysDN_wf (X := X)).rule_local ps _ h'
  join_ne ss p _ h :=
    let ⟨_, h'⟩ := joinNz_shape h
    (sysDN_wf (X := X)).join_ne ss p _ h'
  join_sub ss p _ h :=
    let ⟨_, h'⟩ := joinNz_shape h
    (sysDN_wf (X := X)).join_sub ss p _ h'
  join_pub ss p _ h :=
    let ⟨_, h'⟩ := joinNz_shape h
    (sysDN_wf (X := X)).join_pub ss p _ h'
  join_owner ss p _ h :=
    let ⟨_, h'⟩ := joinNz_shape h
    (sysDN_wf (X := X)).join_owner ss p _ h'

/-! ## 3. Combinations in `DNz` -/

/-- A combination with at least one premise has its call statement in the program. -/
theorem combo_edge_z {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact}
    {ss : List NPObj} {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d)
    (hlen : 2 ≤ cs.length) (hss : ∀ s ∈ ss, InvNz X s) :
    (M, n, Instr.call c, n') ∈ X.Q.prog.edges := by
  cases h with
  | nil => exact absurd hlen (by decide)
  | snoc =>
    obtain ⟨_, _, _, he, _, _⟩ := (hss _ (List.mem_append_right _ List.mem_cons_self) :)
    exact he

/-- A combination is a chain of `DNz.ndBind` (as `combo_chain` for `DN`). -/
theorem combo_chain_z {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact}
    {ss : List NPObj} {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d)
    (hss : ∀ s ∈ ss, InvNz X s) (g : AFact) : ∀ rest, DNz X (.npart M n c n' (cs ++ rest) [] g) →
      DNz X (.npart M n c n' rest P ⟨g.fact, g.demand || d⟩) := by
  induction h with
  | nil =>
    intro rest h0
    rw [Bool.or_false]
    exact h0
  | @snoc cs ss P d p Pf a _ hap ih =>
    intro rest h0
    have ih' := ih (fun s hs => hss s (List.mem_append_left _ hs)) (p :: rest)
      (by rw [List.append_assoc] at h0; exact h0)
    obtain ⟨_, _, hf, _, he1, ha⟩ := (hss _ (List.mem_append_right _ List.mem_cons_self) :)
    have h1 := DNz.ndBind ih' hf he1 ha hap
    rw [Bool.or_assoc] at h1
    exact h1

/-! ## 4. Soundness and completeness -/

theorem inv_of_clDNz {x : NPObj} (h : Cl (sysDNz X) x) : InvNz X x := by
  induction h with
  | root hx =>
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hx
    exact ⟨DNz.root hM, trivial⟩
  | rule hr _ ih =>
    cases hr with
    | keep hr hn =>
      cases hr with
      | conj => exact (hn ⟨_, _, _, _, _, _, _, _, rfl⟩).elim
      | start => exact ⟨DNz.start (fst_of ih :).1, trivial⟩
      | step he hf => exact ⟨DNz.step (fst_of ih :).1 he hf, trivial⟩
      | reqStmt he ht => exact ⟨DNz.reqStmt (fst_of ih :).1 he ht, trivial⟩
      | pass he hm => exact ⟨DNz.pass (fst_of ih :).1 he hm, trivial⟩
      | link he he1 ha => exact ⟨_, _, _, _, _, _, (fst_of ih :).1, he, rfl, he1, ha, rfl⟩
      | added =>
        obtain ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩ := (fst_of ih :)
        exact ⟨DNz.added hf he he1 ha, trivial⟩
      | initA => exact ⟨DNz.initA (fst_of ih :).1, trivial⟩
      | sub he he1 ha => exact ⟨_, _, (fst_of ih :).1, he, he1, ha⟩
      | pub => exact ⟨(fst_of ih :).1, (snd_of ih :).1⟩
      | ndpub hlen => exact ⟨(fst_of ih :).1, hlen⟩
      | reqSink hs hc => exact ⟨DNz.reqSink (fst_of ih :).1 hs hc, trivial⟩
      | answer hm hov => exact ⟨DNz.answer (fst_of ih :).1 (snd_of ih :).1 hm hov, trivial⟩
      | reqUp hcl hov =>
        obtain ⟨_, _, _, _, _, _, hf, he, hc, he1, ha, rfl⟩ := (snd_of ih :)
        exact ⟨DNz.reqUp (fst_of ih :).1 hf he hc he1 ha hcl hov, trivial⟩
      | vuln hs hi hc => exact ⟨DNz.vuln (fst_of ih :).1 hs hi hc, trivial⟩
      | clean he hf => exact ⟨DNz.clean (fst_of ih :).1 he hf, trivial⟩
      | reqClean he ht => exact ⟨DNz.reqClean (fst_of ih :).1 he ht, trivial⟩
      | filt he hp => exact ⟨DNz.filt (fst_of ih :).1 he hp, trivial⟩
      | reqConj hcj hlit hov hg => exact ⟨DNz.reqConj (fst_of ih :).1 hcj hlit hov hg, trivial⟩
    | conj hcj ho1 hg1 ho2 hg2 =>
      exact ⟨DNz.conj (fst_of ih :).1 (snd_of ih :).1 hcj ho1 hg1 ho2 hg2, trivial⟩
  | join hj _ _ ihs ihp =>
    cases hj with
    | ret hj =>
      cases hj with
      | ret hap hr he2 hr' =>
        obtain ⟨_, _, hf, he, he1, ha⟩ := (fst_of ihs :)
        exact ⟨DNz.ret hf he he1 ha ihp.1 hap ihp.2 hr he2 hr', trivial⟩
    | @nd M n n' c Pc ss P d g e2 r hc hlen he2 hr =>
      have h0 : DNz X (.npart M n c n' (Pc ++ []) [] g) := by
        rw [List.append_nil]
        exact DNz.ndOpen (combo_edge_z hc hlen ihs) ihp.1 hlen
      exact ⟨DNz.ndRet (combo_chain_z hc ihs g [] h0) he2 hr, trivial⟩

theorem motNz_of_DNz {o : NObj} (h : DNz X o) : MotNz X o := by
  induction h with
  | root hM => exact Cl.root (List.mem_map.2 ⟨_, hM, rfl⟩)
  | start _ ih => exact Cl.rule (RuleNz.keep RuleN.start notTwo_one) (all_one ih)
  | step _ he hf ih => exact Cl.rule (RuleNz.keep (RuleN.step he hf) notTwo_one) (all_one ih)
  | reqStmt _ he ht ih =>
    exact Cl.rule (RuleNz.keep (RuleN.reqStmt he ht) notTwo_one) (all_one ih)
  | pass _ he hm ih => exact Cl.rule (RuleNz.keep (RuleN.pass he hm) notTwo_one) (all_one ih)
  | added _ he he1 ha ih =>
    exact Cl.rule (RuleNz.keep RuleN.added notTwo_one)
      (all_one (Cl.rule (RuleNz.keep (RuleN.link he he1 ha) notTwo_one) (all_one ih)))
  | initA _ ih => exact Cl.rule (RuleNz.keep RuleN.initA notTwo_one) (all_one ih)
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact Cl.join (JoinNz.ret (JoinN.ret hap hr he2 hr'))
      (all_one (Cl.rule (RuleNz.keep (RuleN.sub he he1 ha) notTwo_one) (all_one ihf)))
      (Cl.rule (RuleNz.keep RuleN.pub (by rintro ⟨_, _, _, _, _, _, _, _, ⟨⟩⟩))
        (all_two ihj ihg))
  | @ndOpen M n c n' Pc g he _ hlen ihg =>
    refine ⟨he, [], g, [], false, ?_, hlen, ?_, Combo.nil, ?_⟩
    · exact Cl.rule (RuleNz.keep (RuleN.ndpub hlen) notTwo_one) (all_one ihg)
    · intro _ hs
      cases hs
    · rw [Bool.or_false]
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ he1 ha hap ihp ihf =>
    obtain ⟨he, cs, g0, ss, d, hpub, hlen, hss, hc, rfl⟩ := ihp
    have hs : Cl (sysDNz X) (.sub M Pf n n' c a) :=
      Cl.rule (RuleNz.keep (RuleN.sub he he1 ha) notTwo_one) (all_one ihf)
    refine ⟨he, cs ++ [p], g0, ss ++ [.sub M Pf n n' c a], d || a.demand, ?_, ?_, ?_,
      Combo.snoc hc hap, ?_⟩
    · rw [List.append_assoc]; exact hpub
    · rw [List.append_assoc]; exact hlen
    · intro s hs'
      rcases combo_snoc_mem hs' with hs' | rfl
      · exact hss s hs'
      · exact hs
    · show (⟨g0.fact, (g0.demand || d) || a.demand⟩ : AFact) =
        ⟨g0.fact, g0.demand || (d || a.demand)⟩
      rw [Bool.or_assoc]
  | ndRet _ he2 hr ihp =>
    obtain ⟨_, cs, g0, ss, d, hpub, hlen, hss, hc, rfl⟩ := ihp
    rw [List.append_nil] at hpub hlen
    exact Cl.join (JoinNz.nd hc hlen he2 hr) hss hpub
  | reqSink _ hs hc ih => exact Cl.rule (RuleNz.keep (RuleN.reqSink hs hc) notTwo_one) (all_one ih)
  | answer _ _ hm hov ihr iha =>
    exact Cl.rule (RuleNz.keep (RuleN.answer hm hov) (by rintro ⟨_, _, _, _, _, _, _, _, ⟨⟩⟩))
      (all_two ihr iha)
  | reqUp _ _ he hc he1 ha hcl hov ihr ihf =>
    subst hc
    exact Cl.rule (RuleNz.keep (RuleN.reqUp hcl hov) (by rintro ⟨_, _, _, _, _, _, _, _, ⟨⟩⟩))
      (all_two ihr (Cl.rule (RuleNz.keep (RuleN.link he he1 ha) notTwo_one) (all_one ihf)))
  | vuln _ hs hi hc ih => exact Cl.rule (RuleNz.keep (RuleN.vuln hs hi hc) notTwo_one) (all_one ih)
  | clean _ he hf ih => exact Cl.rule (RuleNz.keep (RuleN.clean he hf) notTwo_one) (all_one ih)
  | reqClean _ he ht ih =>
    exact Cl.rule (RuleNz.keep (RuleN.reqClean he ht) notTwo_one) (all_one ih)
  | filt _ he hp ih => exact Cl.rule (RuleNz.keep (RuleN.filt he hp) notTwo_one) (all_one ih)
  | conj _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    exact Cl.rule (RuleNz.conj hcj ho1 hg1 ho2 hg2) (all_two ih1 ih2)
  | reqConj _ hcj hlit hov hg ih =>
    exact Cl.rule (RuleNz.keep (RuleN.reqConj hcj hlit hov hg) notTwo_one) (all_one ih)

theorem cl_of_DNz {o : NObj} (h : DNz X o) (hn : NoPart o) : Cl (sysDNz X) (.base o) := by
  have hm := motNz_of_DNz h
  cases o with
  | npart => exact hn.elim
  | ninit => exact hm
  | nedge => exact hm
  | nadded => exact hm
  | nreq => exact hm
  | nvuln => exact hm

/-! ## 5. The main theorem and the objects -/

/-- THE THEOREM for the ND run of the spec: the pipeline closure on the closure objects is
    exactly `DNz` without the partial matches (the state of the k-ary join, not pipeline
    objects). -/
theorem clDNz_iff {o : NObj} : Cl (sysDNz X) (.base o) ↔ DNz X o ∧ NoPart o :=
  ⟨fun h => inv_of_clDNz h, fun ⟨h, hn⟩ => cl_of_DNz h hn⟩

theorem clDNz_nedge {M : MethodId} {P : List PFact} {n : Node} {f : AFact} :
    Cl (sysDNz X) (.base (.nedge M P n f)) ↔ DNz X (.nedge M P n f) :=
  ⟨fun h => (clDNz_iff.1 h).1, fun h => clDNz_iff.2 ⟨h, trivial⟩⟩

theorem clDNz_ninit {M : MethodId} {i : PFact} :
    Cl (sysDNz X) (.base (.ninit M i)) ↔ DNz X (.ninit M i) :=
  ⟨fun h => (clDNz_iff.1 h).1, fun h => clDNz_iff.2 ⟨h, trivial⟩⟩

theorem clDNz_nadded {M : MethodId} {a : PFact} :
    Cl (sysDNz X) (.base (.nadded M a)) ↔ DNz X (.nadded M a) :=
  ⟨fun h => (clDNz_iff.1 h).1, fun h => clDNz_iff.2 ⟨h, trivial⟩⟩

theorem clDNz_nreq {M : MethodId} {i : PFact} {t : Mark} :
    Cl (sysDNz X) (.base (.nreq M i t)) ↔ DNz X (.nreq M i t) :=
  ⟨fun h => (clDNz_iff.1 h).1, fun h => clDNz_iff.2 ⟨h, trivial⟩⟩

theorem clDNz_nvuln {M : MethodId} {n : Node} {s : PFact} {d : Bool} :
    Cl (sysDNz X) (.base (.nvuln M n s d)) ↔ DNz X (.nvuln M n s d) :=
  ⟨fun h => (clDNz_iff.1 h).1, fun h => clDNz_iff.2 ⟨h, trivial⟩⟩

/-- A partial match is not a pipeline object. -/
theorem clDNz_npart {M : MethodId} {n : Node} {c : Call} {n' : Node} {rest P : List PFact}
    {g : AFact} : ¬ Cl (sysDNz X) (.base (.npart M n c n' rest P g)) :=
  fun h => (clDNz_iff.1 h).2

theorem clDNz_link {m : MethodId} {a : PFact} {M : MethodId} {Pc : List PFact} :
    Cl (sysDNz X) (.link m a M Pc) ↔
      LinkOK X.Q.prog (fun M P n f => DNz X (.nedge M P n f)) m a M Pc := by
  refine ⟨fun h => inv_of_clDNz h, ?_⟩
  rintro ⟨_, _, _, _, _, _, hf, he, rfl, he1, ha, rfl⟩
  exact Cl.rule (RuleNz.keep (RuleN.link he he1 ha) notTwo_one) (all_one (clDNz_nedge.2 hf))

theorem clDNz_sub {M : MethodId} {Pc : List PFact} {n n' : Node} {c : Call} {a : AFact} :
    Cl (sysDNz X) (.sub M Pc n n' c a) ↔ NSubOKz X M Pc n n' c a := by
  refine ⟨fun h => inv_of_clDNz h, ?_⟩
  rintro ⟨_, _, hf, he, he1, ha⟩
  exact Cl.rule (RuleNz.keep (RuleN.sub he he1 ha) notTwo_one) (all_one (clDNz_nedge.2 hf))

theorem clDNz_pub {m : MethodId} {j : PFact} {g : AFact} :
    Cl (sysDNz X) (.pub m j g) ↔
      DNz X (.ninit m j) ∧ DNz X (.nedge m [j] (X.Q.prog.exit m) g) := by
  refine ⟨fun h => inv_of_clDNz h, ?_⟩
  rintro ⟨hj, hg⟩
  exact Cl.rule (RuleNz.keep RuleN.pub (by rintro ⟨_, _, _, _, _, _, _, _, ⟨⟩⟩))
    (all_two (clDNz_ninit.2 hj) (clDNz_nedge.2 hg))

theorem clDNz_ndpub {m : MethodId} {Pc : List PFact} {g : AFact} :
    Cl (sysDNz X) (.ndpub m Pc g) ↔
      DNz X (.nedge m Pc (X.Q.prog.exit m) g) ∧ 2 ≤ Pc.length := by
  refine ⟨fun h => inv_of_clDNz h, ?_⟩
  rintro ⟨hg, hlen⟩
  exact Cl.rule (RuleNz.keep (RuleN.ndpub hlen) notTwo_one) (all_one (clDNz_nedge.2 hg))

/-! ## 6. No zero member in a summary with several premises -/

/-- `dropZ P` is `[zeroFact]`, or it has no zero member. -/
theorem dropZ_zero_or {P : List PFact} : dropZ P = [zeroFact] ∨ zeroFact ∉ dropZ P := by
  unfold dropZ
  split
  · exact .inl rfl
  · refine .inr fun hm => ?_
    have := (List.mem_filter.1 hm).2
    simp at this

/-- A `dropZ` list with two or more members has no zero member. -/
theorem dropZ_two_no_zero {P : List PFact} (h : 2 ≤ (dropZ P).length) : zeroFact ∉ dropZ P := by
  rcases dropZ_zero_or (P := P) with he | hn
  · rw [he] at h
    exact absurd h (by decide)
  · exact hn

/-- The motive of `dnz_nd_no_zero`. -/
def NoZ : NObj → Prop
  | .nedge _ P _ _ => 2 ≤ P.length → zeroFact ∉ P
  | _ => True

/-- An edge of `DNz` with two or more premises has no zero member (ap.md §4.6). -/
theorem dnz_nd_no_zero {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNz X (.nedge M P n f)) (hlen : 2 ≤ P.length) : zeroFact ∉ P := by
  have key : ∀ {o : NObj}, DNz X o → NoZ o := by
    intro o h
    induction h with
    | start => intro hl; simp at hl
    | step _ _ _ ih => exact ih
    | pass _ _ _ ih => exact ih
    | ret _ _ _ _ _ _ _ _ _ _ ihf => exact ihf
    | ndRet => intro hl; exact dropZ_two_no_zero hl
    | clean _ _ _ ih => exact ih
    | filt _ _ _ ih => exact ih
    | conj => intro hl; exact dropZ_two_no_zero hl
    | _ => trivial
  exact key h hlen

/-- A publication of `sysDNz` with several premises has no zero member. So no index of a k-ary
    join is the zero fact (analyzer-core.md §5.4). -/
theorem clDNz_ndpub_no_zero {m : MethodId} {Pc : List PFact} {g : AFact}
    (h : Cl (sysDNz X) (.ndpub m Pc g)) : zeroFact ∉ Pc :=
  let ⟨hg, hlen⟩ := clDNz_ndpub.1 h
  dnz_nd_no_zero hg hlen

/-- Every subscription of a combination satisfies its premise. -/
theorem combo_applicable {M : MethodId} {n n' : Node} {c : Call} {cs : List PFact}
    {ss : List NPObj} {P : List PFact} {d : Bool} (h : Combo M n n' c cs ss P d) :
    ∀ s ∈ ss, ∃ p ∈ cs, ∃ (Pf : List PFact) (a : AFact),
      s = .sub M Pf n n' c a ∧ applicable p a.fact = true := by
  induction h with
  | nil => intro s hs; cases hs
  | snoc _ hap ih =>
    intro s hs
    rcases combo_snoc_mem hs with hs | rfl
    · obtain ⟨p, hp, Pf, a, rfl, ha⟩ := ih s hs
      exact ⟨p, List.mem_append_left _ hp, Pf, a, rfl, ha⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, _, _, rfl, hap⟩

/-- No premise of a publication with several premises is satisfied by a fact on the zero
    base. -/
theorem clDNz_ndpub_zero_base (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {m : MethodId}
    {Pc : List PFact} {g : AFact} (h : Cl (sysDNz X) (.ndpub m Pc g)) {p a : PFact}
    (hp : p ∈ Pc) (hz : a.base = zeroBase) : applicable p a = false := by
  cases hap : applicable p a with
  | false => rfl
  | true =>
    have ⟨hg, hlen⟩ := clDNz_ndpub.1 h
    have hpz := dnz_applicable_zero hG hα hg hp hap hz
    exact absurd (hpz ▸ hp) (dnz_nd_no_zero hg hlen)

/-- THE ZERO SUBSCRIPTION: the zero added fact (`NDZeroBase.zero_binding`) satisfies no premise
    of a publication with several premises (analyzer-core.md §5.4). -/
theorem clDNz_ndpub_zero_sub (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {m : MethodId}
    {Pc : List PFact} {g : AFact} (h : Cl (sysDNz X) (.ndpub m Pc g)) :
    ∀ p ∈ Pc, applicable p zeroFact = false :=
  fun _ hp => clDNz_ndpub_zero_base hG hα h hp rfl

/-- Every subscription of a k-ary join with a publication of the closure binds a fact off the
    zero base. So the zero subscription never takes part in a k-ary join. -/
theorem joinNz_nd_no_zero_sub (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {ss : List NPObj}
    {m : MethodId} {Pc : List PFact} {g : AFact} {c0 : NPObj}
    (hj : JoinNz X ss (.ndpub m Pc g) c0) (hp : Cl (sysDNz X) (.ndpub m Pc g)) :
    ∀ s ∈ ss, ∃ (M : MethodId) (Pf : List PFact) (n n' : Node) (c : Call) (a : AFact),
      s = .sub M Pf n n' c a ∧ a.fact.base ≠ zeroBase := by
  cases hj with
  | nd hc =>
    intro s hs
    obtain ⟨p, hp', Pf, a, rfl, hap⟩ := combo_applicable hc s hs
    refine ⟨_, Pf, _, _, _, a, rfl, fun hz => ?_⟩
    have hf := clDNz_ndpub_zero_base hG hα hp hp' hz
    rw [hap] at hf
    cases hf

/-! ## 7. The result of a complete run -/

/-- A complete ND run of the spec: at a reachable quiescent state of `sysDNz`, the processed
    `base` objects are exactly the objects of `DNz` without the partial matches. -/
theorem result_DNz {st : St NPObj MethodId MethodId} (hR : Pipeline.Reach (sysDNz X) st)
    (hQ : st.Quiescent) {o : NObj} : NPObj.base o ∈ st.known ↔ DNz X o ∧ NoPart o :=
  (quiescent_exact sysDNz_wf hR hQ).trans clDNz_iff

/-! ## 8. Axiom audit -/

#print axioms sysDNz_wf
#print axioms clDNz_iff
#print axioms clDNz_nedge
#print axioms clDNz_ninit
#print axioms clDNz_nadded
#print axioms clDNz_nreq
#print axioms clDNz_nvuln
#print axioms clDNz_npart
#print axioms clDNz_link
#print axioms clDNz_sub
#print axioms clDNz_pub
#print axioms clDNz_ndpub
#print axioms dnz_nd_no_zero
#print axioms clDNz_ndpub_no_zero
#print axioms result_DNz
#print axioms clDNz_ndpub_zero_base
#print axioms clDNz_ndpub_zero_sub
#print axioms joinNz_nd_no_zero_sub

end ApSpec.PipelineNDZ
