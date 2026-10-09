/-
  ApSpec.AnyTaintSim — the SOUNDNESS side of the tail kind `[any-taint]` (decision F69).

  The new closures of `AnyTaintDefs` (run 1 `D6T`, the restricted forward run `DRT` with
  must-premises) have the SAME FACTS as the base closures (`D`, `DR`); only the layers of the edges
  differ. So coverage, the vulnerability theorems and the iteration carry over from the base model
  through the simulations. The backward run needs no new closure: `Backward.DB` is the backward run
  of the spec.

  Namespace `ApSpec.AnyTaintSim` (it opens `ApSpec.AnyTaint`, the namespace of the definitions, so
  that the names of this file cannot clash with the other `AnyTaint*` proof files).

  ## Contents

  1. Local lemmas: `LE_trans`; a statement transfer with W6T is a transfer whose `[any]` results
     may be raised (`transfer_memTA`, `transferT_mem_inv`); two inputs with the same non-`*` fact
     give results with the same facts (`applyEdge_same`, `transfer_same`, `cleanRes_same`,
     `applySummary_same`, `check_same`; the proof goes through the common raise `⟨f.fact, true⟩`
     and the `W6.LL` lemmas).
  2. RUN 1 (`D6T`).
     * The simulation both ways: `D_le_D6T`, `D6T_le_D` (relation `W6.LE`, objects `W6.Up` /
       `W6.Down`), under `W6.SummaryStar` (it holds for the policy, `W6.summaryStar_policy`).
       The hypothesis is necessary: `CexT.cex_w6t_changes_fact` (W6T with no taint edge is W6 on
       the statements, and the counterexample of `W6.Cex` works for `D6T`).
     * `D6T_same_shape`, `D6T_normal`, `D6T_normal_1` (a normal edge of `D6T` is a normal edge
       of `D` with the same fact); `edge_exact6T`, `edge_exact_valid6T` (from `Exact`);
     * soundness: `coverage6T`, `vuln_found6T`, `vuln_found_policy6T`;
     * THE KINDS INVARIANT `D6T_any_conc`: a normal `[any]` conclusion (spec `[any-taint]`) has a
       concrete mark (hypotheses `TaintConc`, `BindNoAny`; every abstraction, so no policy
       hypothesis); so a FLOW edge has no `[any-taint]` leaf (`D6T_flow_no_any_taint`); the
       partition of run 1 (`kinds_D6T`). Both hypotheses are necessary: `CexKinds.cex_taintConc`,
       `CexKinds.cex_bindNoAny` (run 1 with `policy1`, S10 and S7 hold);
     * `D6_le_D6T`, `D6_normal_D6T`, `D6_normal_D6T_1`: every normal edge of the W6 run `W6.D6` is
       a normal edge of `D6T`, so the normal edges of `D6T` are between those of `D6` and those
       of `D`.
  3. THE RESTRICTED FORWARD RUN (`DRT`).
     * invariants: `DRT_edge_init`, `DRT_mustAny`;
     * THE FACT SIMULATION `factSim` (`FactSim` of `AnyTaintDefs`), from `DRT_down` and `DR_up`,
       under `EmitCopiesMark emit` and `RestrictFact restrict`; the must flag of a premise changes
       only layers (`DRT_flag_swap`);
     * `DRT_concrete`, `DRT_no_request`, `DRT_final_not_star`, `DRT_must_any`, `kinds_DRT`;
     * soundness: `coverageRT`, `vuln_foundRT`, and the spec rules `coverageRT_M`,
       `vuln_foundRT_M`;
     * the hand-off: `summaryDemandT_iff`, `revSummaryDemandT_iff`, `backward_reads_sameT` (the
       backward run reads the same patterns from `DRT` as from `DR`), `vulnT_iff` (the same
       reported sinks); for run 1 `revSummaryDemand6T_iff`.
  4. THE ITERATION: `runSeqT` (run 1 = `D6T`, run `k + 1` = `DRT` seen through `forgetRun`),
     `runSeqT_up`, `runSeqT_down`, `revSummaryDemand_runSeqT`, `iteration_generalT`,
     `iteration_reportsT` (the form to cite); with forward seeds `runSeqSrcT`, `iteration_srcT`.
  5. THE BACKWARD RUN (no new closure): `startFact_any_demand`, `seed_any_normal`,
     `DB_any_premise_demand`; the backward records of the spec (decision 7) `backRecT` are reversed
     normal backward summaries (`backRecT_sub`), so they are exact forward records
     (`backRec_exact`, `backRec_exactM`, `backRec_flow`); records without must flags read back by
     `DR` are the records themselves (`recsDR_liftRecs`).

  Hypotheses that this file adds to the base theorems (each one is reported where it is used):
    * `W6.SummaryStar` for the run-1 simulation (as W6; necessary, `CexT`; the policy has it);
    * `TaintConc`, `BindNoAny` only for the kinds invariant of run 1 (necessary, `CexKinds`);
    * `EmitCopiesMark emit`, `RestrictFact restrict` for the fact simulation of `DRT` (the spec
      rules `emitM`, `restrictU` have them);
    * no hypothesis on the taint edges for the soundness (coverage, vulnerability, iteration).

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintDefs
import ApSpec.Kinds
import ApSpec.Backward
import ApSpec.BackwardExact
import ApSpec.ForwardSeeds
import ApSpec.RestrictedMain
import ApSpec.RestrictedCoverage
import ApSpec.Coverage

namespace ApSpec.AnyTaintSim
open ApSpec ApSpec.AnyTaint

/-! ## 1. Local lemmas -/

theorem LE_trans {f g h : AFact} (h1 : W6.LE f g) (h2 : W6.LE g h) : W6.LE f h := by
  rcases h1 with rfl | ⟨hns, rfl⟩
  · exact h2
  · rcases h2 with rfl | ⟨_, rfl⟩
    · exact W6.LE.raise hns
    · exact W6.LE.raise hns

/-- A result of `applyAll` gives a result of `applyAllT`: W6T of the same micro edge. -/
theorem applyAllT_of_mem (taint : TaintEdges) (c : AFact) :
    ∀ {es : List MicroEdge} {x : AFact}, x ∈ (applyAll c es).facts →
      ∃ e, e ∈ es ∧ x ∈ (applyEdge c e.1 e.2).facts ∧ w6t taint e x ∈ (applyAllT taint c es).facts
  | [], _, h => absurd h List.not_mem_nil
  | e :: es, x, h => by
    have h' : x ∈ (applyEdge c e.1 e.2).facts ++ (applyAll c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · refine ⟨e, List.mem_cons_self .., h1, ?_⟩
      show w6t taint e x ∈ (applyEdge c e.1 e.2).facts.map (w6t taint e) ++
        (applyAllT taint c es).facts
      exact List.mem_append_left _ (List.mem_map_of_mem (f := w6t taint e) h1)
    · obtain ⟨e', he', hx', hm⟩ := applyAllT_of_mem taint c h1
      refine ⟨e', List.mem_cons_of_mem _ he', hx', ?_⟩
      show w6t taint e' x ∈ (applyEdge c e.1 e.2).facts.map (w6t taint e) ++
        (applyAllT taint c es).facts
      exact List.mem_append_right _ hm

/-- A result of `applyAllT` is W6T of a result of one micro edge. -/
theorem applyAllT_mem_inv (taint : TaintEdges) (c : AFact) :
    ∀ {es : List MicroEdge} {y : AFact}, y ∈ (applyAllT taint c es).facts →
      ∃ e x, e ∈ es ∧ x ∈ (applyEdge c e.1 e.2).facts ∧ y = w6t taint e x
  | [], _, h => absurd h List.not_mem_nil
  | e :: es, y, h => by
    have h' : y ∈ (applyEdge c e.1 e.2).facts.map (w6t taint e) ++
        (applyAllT taint c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h1
      exact ⟨e, x, List.mem_cons_self .., hx, rfl⟩
    · obtain ⟨e', x, he', hx, rfl⟩ := applyAllT_mem_inv taint c h1
      exact ⟨e', x, List.mem_cons_of_mem _ he', hx, rfl⟩

/-- The shape of a result of `transferT`: the fact itself (an untouched base), or the field limit
    of W6T of a result of one micro edge of the statement. -/
theorem transferT_mem_inv {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c r : AFact} (h : r ∈ (transferT taint counted L s c).facts) :
    (memB c.fact.base s.touched = false ∧ r = c) ∨
    ∃ e x, e ∈ s.edges ∧ x ∈ (applyEdge c e.1 e.2).facts ∧ r = limitF counted L (w6t taint e x) := by
  unfold transferT at h
  cases hm : memB c.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    exact Or.inl ⟨rfl, List.mem_singleton.mp h⟩
  | true =>
    rw [hm, if_pos rfl] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
    obtain ⟨e, x, he, hx, rfl⟩ := applyAllT_mem_inv taint c hy
    exact Or.inr ⟨e, x, he, hx, rfl⟩

/-- A result of `transfer` gives a result of `transferT` with the same fact, in the same layer or
    (only an `[any]` result) raised. -/
theorem transfer_memTA {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c f : AFact} (h : f ∈ (transfer counted L s c).facts) :
    ∃ f', f' ∈ (transferT taint counted L s c).facts ∧
      (f' = f ∨ (f.fact.kind = .any ∧ f' = ⟨f.fact, true⟩)) := by
  unfold transfer at h
  unfold transferT
  cases hm : memB c.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    rw [if_neg Bool.false_ne_true]
    exact ⟨f, h, Or.inl rfl⟩
  | true =>
    rw [hm, if_pos rfl] at h
    rw [if_pos rfl]
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    obtain ⟨e, _, hxe, hw⟩ := applyAllT_of_mem taint c hx
    refine ⟨limitF counted L (w6t taint e x), List.mem_map_of_mem (f := limitF counted L) hw, ?_⟩
    rcases w6t_cases taint e x with e1 | ⟨hk, _, e1⟩
    · rw [e1]; exact Or.inl rfl
    · rw [e1]
      have hxk : x.fact.kind = .any := applyEdge_any_target hk hxe
      unfold limitF
      cases cutPath counted L x.fact.path with
      | none => exact Or.inr ⟨hxk, rfl⟩
      | some p => exact Or.inl rfl

/-- Two facts with the same non-`*` fact are below their common raise. -/
theorem LE_up2 {c c' : AFact} (h : c.fact = c'.fact) (hns : c.fact.kind.isStar = false) :
    W6.LE c ⟨c.fact, true⟩ ∧ W6.LE c' ⟨c.fact, true⟩ := by
  refine ⟨W6.LE.raise hns, ?_⟩
  have h2 := W6.LE.raise (f := c') (by rw [← h]; exact hns)
  rw [← h] at h2
  exact h2

theorem LL_same {xs ys zs : List AFact} (h1 : W6.LL xs zs) (h2 : W6.LL ys zs) {x : AFact}
    (hx : x ∈ xs) : ∃ y, y ∈ ys ∧ y.fact = x.fact := by
  obtain ⟨z, hz, hxz⟩ := h1.fwd hx
  obtain ⟨y, hy, hyz⟩ := h2.bwd hz
  exact ⟨y, hy, hyz.fact.trans hxz.fact.symm⟩

/-- THE LAYER DOES NOT CHANGE A FACT (`applyEdge`): two inputs with the same non-`*` fact give
    results with the same facts, and the same requests. -/
theorem applyEdge_same {c c' : AFact} (h : c.fact = c'.fact) (hns : c.fact.kind.isStar = false)
    {fr to : PFact} {x : AFact} (hx : x ∈ (applyEdge c fr to).facts) :
    ∃ y, y ∈ (applyEdge c' fr to).facts ∧ y.fact = x.fact :=
  LL_same (W6.applyEdge_LL (LE_up2 h hns).1).1 (W6.applyEdge_LL (LE_up2 h hns).2).1 hx

theorem applyEdge_reqs_same {c c' : AFact} (h : c.fact = c'.fact)
    (hns : c.fact.kind.isStar = false) {fr to : PFact} :
    (applyEdge c fr to).reqs = (applyEdge c' fr to).reqs :=
  (W6.applyEdge_LL (fr := fr) (to := to) (LE_up2 h hns).1).2.trans
    (W6.applyEdge_LL (fr := fr) (to := to) (LE_up2 h hns).2).2.symm

/-- The same for the statement transfer. -/
theorem transfer_same {counted : Acc → Bool} {L : Nat} {s : Stmt} {c c' : AFact}
    (h : c.fact = c'.fact) (hns : c.fact.kind.isStar = false) {x : AFact}
    (hx : x ∈ (transfer counted L s c).facts) :
    ∃ y, y ∈ (transfer counted L s c').facts ∧ y.fact = x.fact :=
  LL_same (W6.transfer_LL (LE_up2 h hns).1).1 (W6.transfer_LL (LE_up2 h hns).2).1 hx

theorem transfer_reqs_same {counted : Acc → Bool} {L : Nat} {s : Stmt} {c c' : AFact}
    (h : c.fact = c'.fact) (hns : c.fact.kind.isStar = false) :
    (transfer counted L s c).reqs = (transfer counted L s c').reqs :=
  (W6.transfer_LL (counted := counted) (L := L) (s := s) (LE_up2 h hns).1).2.trans
    (W6.transfer_LL (counted := counted) (L := L) (s := s) (LE_up2 h hns).2).2.symm

/-- The same for the cleaner. -/
theorem cleanRes_same {cl : Cleaner} {c c' : AFact} (h : c.fact = c'.fact)
    (hns : c.fact.kind.isStar = false) {x : AFact} (hx : x ∈ (cleanRes cl c).facts) :
    ∃ y, y ∈ (cleanRes cl c').facts ∧ y.fact = x.fact :=
  LL_same (W6.cleanRes_LL (LE_up2 h hns).1).1 (W6.cleanRes_LL (LE_up2 h hns).2).1 hx

theorem cleanRes_reqs_same {cl : Cleaner} {c c' : AFact} (h : c.fact = c'.fact)
    (hns : c.fact.kind.isStar = false) : (cleanRes cl c).reqs = (cleanRes cl c').reqs :=
  (W6.cleanRes_LL (cl := cl) (LE_up2 h hns).1).2.trans
    (W6.cleanRes_LL (cl := cl) (LE_up2 h hns).2).2.symm

/-- A summary applied to a non-`*` fact: the facts of the results are the facts of `applyEdge`
    (the normal form does nothing, the layer of the summary edge is not read). -/
theorem applySummary_fact_of {a g r : AFact} {j : PFact} (hns : a.fact.kind.isStar = false)
    (hr : r ∈ (applySummary a j g).facts) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ x.fact = r.fact := by
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
  refine ⟨x, hx, ?_⟩
  rw [Invariant.norm_id_of_nonstar (x := ⟨x.fact, x.demand || g.demand⟩)
    (Confirmed.applyEdge_nonstar (r := x) hns hx)]

theorem applySummary_of_fact {a g x : AFact} {j : PFact} (hns : a.fact.kind.isStar = false)
    (hx : x ∈ (applyEdge a j g.fact).facts) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ r.fact = x.fact := by
  refine ⟨AFact.norm ⟨x.fact, x.demand || g.demand⟩,
    List.mem_map_of_mem (f := fun x : AFact => AFact.norm (⟨x.fact, x.demand || g.demand⟩ : AFact))
      hx, ?_⟩
  rw [Invariant.norm_id_of_nonstar (x := ⟨x.fact, x.demand || g.demand⟩)
    (Confirmed.applyEdge_nonstar (r := x) hns hx)]

/-- THE LAYER DOES NOT CHANGE A FACT (summary application): the caller facts with the same
    non-`*` fact and the summary edges with the same fact give results with the same facts. -/
theorem applySummary_same {a a' g g' r : AFact} {j : PFact} (ha : a.fact = a'.fact)
    (hns : a.fact.kind.isStar = false) (hg : g.fact = g'.fact)
    (hr : r ∈ (applySummary a j g).facts) :
    ∃ r', r' ∈ (applySummary a' j g').facts ∧ r'.fact = r.fact := by
  obtain ⟨x, hx, hxr⟩ := applySummary_fact_of hns hr
  rw [hg] at hx
  obtain ⟨y, hy, hyx⟩ := applyEdge_same ha hns hx
  obtain ⟨r', hr', hry⟩ := applySummary_of_fact (by rw [← ha]; exact hns) hy
  exact ⟨r', hr', hry.trans (hyx.trans hxr)⟩

theorem applySummary_nonstar' {a g r : AFact} {j : PFact} (hns : a.fact.kind.isStar = false)
    (hr : r ∈ (applySummary a j g).facts) : r.fact.kind.isStar = false := by
  obtain ⟨x, hx, hxr⟩ := applySummary_fact_of hns hr
  rw [← hxr]
  exact Confirmed.applyEdge_nonstar hns hx

/-- The sink check reads only the fact. -/
theorem check_same (i s : PFact) {f g : AFact} (h : f.fact = g.fact) : check i f s = check i g s := by
  obtain ⟨ff, fd⟩ := f
  obtain ⟨gf, gd⟩ := g
  have e : ff = gf := h
  subst e
  rfl

#print axioms transfer_memTA
#print axioms applyEdge_same
#print axioms applySummary_same

/-! ## 2. Run 1: the closure `D6T` -/

section Sim1
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- THE SIMULATION, `D` INTO `D6T` (run 1): every object of `D` is an object of `D6T`; every edge
    has an edge of `D6T` with the same fact in the same or a raised layer (`W6.LE`); every reported
    vulnerability is reported in the same or a raised layer. Hypothesis: `W6.SummaryStar` (as
    `W6.D_le_D6`; it holds for the run-1 policy, `W6.summaryStar_policy`). -/
theorem D_le_D6T (hS : W6.SummaryStar P (D P counted L α sinks roots)) {o : Obj}
    (h : D P counted L α sinks roots o) : W6.Up (D6T P taint counted L α sinks roots) o := by
  induction h with
  | root hM => exact D6T.root hM
  | @start M i _ ih => exact ⟨_, D6T.start ih, W6.LE.refl _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (W6.transfer_LL hle).1.fwd hf
    obtain ⟨g'', hg'', hle''⟩ := transfer_memT (taint := taint) hg'
    exact ⟨_, D6T.step hg hE hg'', LE_trans hle' hle''⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqStmt hg hE (by rw [transferT_reqs, ← (W6.transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6T.pass hg hE (by rw [← hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a', ha', hla⟩ := (W6.applyEdge_LL hle).1.fwd ha
    show D6T P taint counted L α sinks roots (.added c.callee a.fact)
    rw [hla.fact]
    exact D6T.added hg hE he ha'
  | initA _ ih => exact D6T.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' hf hE he1 ha hj happ hg hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f6, hf6, hlf⟩ := ihF
    obtain ⟨g6, hg6, hlg⟩ := ihG
    obtain ⟨a6, ha6, hla⟩ := (W6.applyEdge_LL hlf).1.fwd ha
    have hX : ∀ x, x ∈ (applyEdge a j g.fact).facts → x.fact.kind.isStar = true → g6 = g :=
      fun x hx hxs => hlg.star_eq (hS hf hE he1 ha hj happ hg hx hxs)
    obtain ⟨r6, hr6, hlr⟩ := (W6.applySummary_LL hla hlg hX).fwd hr
    obtain ⟨r6', hr6', hlr'⟩ := (W6.applyEdge_LL hlr).1.fwd hr'
    exact ⟨_, D6T.ret hf6 hE he1 ha6 ihJ (by rw [← hla.fact]; exact happ) hg6 hr6 he2 hr6',
      W6.limitF_LE hlr'⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqSink hg hs (by rw [← W6.check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact D6T.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a', ha', hla⟩ := (W6.applyEdge_LL hle).1.fwd ha
    exact D6T.reqUp ihR hg hE hc he ha' (by rw [← hla.fact]; exact hcl)
      (by rw [← hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, D6T.vuln hg hs (by rw [← W6.check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (W6.cleanRes_LL hle).1.fwd hf
    exact ⟨_, D6T.clean hg hE hg', hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqClean hg hE (by rw [← (W6.cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6T.filt hg hE (by rw [← hle.fact]; exact hp), hle⟩

#print axioms D_le_D6T

/-- THE SIMULATION, `D6T` INTO `D` (run 1): every object of `D6T` is an object of `D`; every edge
    has an edge of `D` with the same fact in the same or a lower layer (`W6.LE`); every reported
    vulnerability is reported in the same or a lower layer. Hypothesis: `W6.SummaryStar`. -/
theorem D6T_le_D (hS : W6.SummaryStar P (D P counted L α sinks roots)) {o : Obj}
    (h : D6T P taint counted L α sinks roots o) : W6.Down (D P counted L α sinks roots) o := by
  induction h with
  | root hM => exact D.root hM
  | @start M i _ ih => exact ⟨_, D.start ih, W6.LE.refl _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨x, hx, hlx⟩ := transferT_mem hf
    obtain ⟨g', hg', hle'⟩ := (W6.transfer_LL hle).1.bwd hx
    exact ⟨g', D.step hg hE hg', LE_trans hle' hlx⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqStmt hg hE (by rw [(W6.transfer_LL hle).2, ← transferT_reqs taint]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D.pass hg hE (by rw [hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hle).1.bwd ha
    show D P counted L α sinks roots (.added c.callee a.fact)
    rw [← hla.fact]
    exact D.added hg hE he ha0
  | initA _ ih => exact D.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' hf hE he1 ha hj happ hg hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f0, hf0, hlf⟩ := ihF
    obtain ⟨g0, hg0, hlg⟩ := ihG
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hlf).1.bwd ha
    have happ0 : applicable j a0.fact = true := by rw [hla.fact]; exact happ
    have hX : ∀ x, x ∈ (applyEdge a0 j g0.fact).facts → x.fact.kind.isStar = true → g = g0 :=
      fun x hx hxs => hlg.star_eq (hS hf0 hE he1 ha0 ihJ happ0 hg0 hx hxs)
    obtain ⟨r0, hr0, hlr⟩ := (W6.applySummary_LL hla hlg hX).bwd hr
    obtain ⟨r0', hr0', hlr'⟩ := (W6.applyEdge_LL hlr).1.bwd hr'
    exact ⟨_, D.ret hf0 hE he1 ha0 ihJ happ0 hg0 hr0 he2 hr0', W6.limitF_LE hlr'⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqSink hg hs (by rw [W6.check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact D.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hle).1.bwd ha
    exact D.reqUp ihR hg hE hc he ha0 (by rw [hla.fact]; exact hcl) (by rw [hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, D.vuln hg hs (by rw [W6.check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (W6.cleanRes_LL hle).1.bwd hf
    exact ⟨g', D.clean hg hE hg', hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqClean hg hE (by rw [(W6.cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D.filt hg hE (by rw [hle.fact]; exact hp), hle⟩

#print axioms D6T_le_D

end Sim1

section Sound1
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- THE SAME SHAPE (run 1): with W6T, run 1 has the same initial facts, added facts, requests,
    edge facts (each edge in the same or another layer) and reported sinks as `D`. So the
    abstraction, the requests and the answers do not see W6T. Hypothesis: `W6.SummaryStar`. -/
theorem D6T_same_shape (hS : W6.SummaryStar P (D P counted L α sinks roots)) :
    (∀ M i, D6T P taint counted L α sinks roots (.init M i) ↔ D P counted L α sinks roots (.init M i)) ∧
    (∀ M a, D6T P taint counted L α sinks roots (.added M a) ↔
      D P counted L α sinks roots (.added M a)) ∧
    (∀ M i t, D6T P taint counted L α sinks roots (.req M i t) ↔
      D P counted L α sinks roots (.req M i t)) ∧
    (∀ M i n p, (∃ g, D6T P taint counted L α sinks roots (.edge M i n g) ∧ g.fact = p) ↔
      (∃ f, D P counted L α sinks roots (.edge M i n f) ∧ f.fact = p)) ∧
    (∀ M n s, (∃ b, D6T P taint counted L α sinks roots (.vuln M n s b)) ↔
      (∃ b, D P counted L α sinks roots (.vuln M n s b))) := by
  have up := fun o (h : D P counted L α sinks roots o) => D_le_D6T P taint counted L α sinks roots hS h
  have down := fun o (h : D6T P taint counted L α sinks roots o) =>
    D6T_le_D P taint counted L α sinks roots hS h
  refine ⟨fun M i => ⟨down _, up _⟩, fun M a => ⟨down _, up _⟩, fun M i t => ⟨down _, up _⟩,
    fun M i n p => ⟨?_, ?_⟩, fun M n s => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hle⟩ := down _ hg
    exact ⟨f, hf, hle.fact⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hle⟩ := up _ hf
    exact ⟨g, hg, hle.fact.symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := down _ hb
    exact ⟨b', hb'⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := up _ hb
    exact ⟨b', hb'⟩

#print axioms D6T_same_shape

/-- EVERY NORMAL EDGE OF `D6T` IS A NORMAL EDGE OF `D`, with the same fact (run 1). So the
    exactness of `D` (`Exact.edge_exact`) holds for the normal edges of `D6T`, normal `[any]`
    conclusions (spec `[any-taint]`) included. Hypothesis: `W6.SummaryStar`. -/
theorem D6T_normal (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (hf : f.demand = false) :
    D P counted L α sinks roots (.edge M i n f) := by
  obtain ⟨g, hg, hle⟩ := D6T_le_D P taint counted L α sinks roots hS h
  rw [hle.eq_of_normal hf]
  exact hg

#print axioms D6T_normal

/-- THE EXACTNESS OF RUN 1 WITH W6T (from `Exact.edge_exact`): a normal edge of `D6T` denotes only
    real flows. Hypotheses: S7 (`Exact.MarkWF`), `Exact.FiltUp`, `W6.SummaryStar`. -/
theorem edge_exact6T (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  Exact.edge_exact hmw hup (D6T_normal P taint counted L α sinks roots hS h ha) ha hd

#print axioms edge_exact6T

/-- The same for valid locations (from `Exact.edge_exact_valid`). -/
theorem edge_exact_valid6T {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  Exact.edge_exact_valid hmw hv hbo (D6T_normal P taint counted L α sinks roots hS h ha) ha hd hok

#print axioms edge_exact_valid6T

/-- COVERAGE OF RUN 1 WITH W6T (from `Coverage.coverage` through the simulation): a real flow from
    a covered entry location is covered by an edge (in some layer), or the run has the request for
    the entry mark. Hypotheses: S10 (`Program.WF`), an applicable abstraction, `W6.SummaryStar`. -/
theorem coverage6T (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, D6T P taint counted L α sinks roots (.init M i) → i.covers l0 →
      (∃ f, D6T P taint counted L α sinks roots (.edge M i n f) ∧ den i f.fact l0 l) ∨
      D6T P taint counted L α sinks roots (.req M i l0.mark) := by
  intro i hi hc
  have hi0 : D P counted L α sinks roots (.init M i) :=
    D6T_le_D P taint counted L α sinks roots hS hi
  rcases Coverage.coverage P counted L α sinks roots hwf hα hfl i hi0 hc with ⟨f, hf, hd⟩ | hr
  · obtain ⟨g, hg, hle⟩ := D_le_D6T P taint counted L α sinks roots hS hf
    exact Or.inl ⟨g, hg, by rw [← hle.fact]; exact hd⟩
  · exact Or.inr (D_le_D6T P taint counted L α sinks roots hS hr)

#print axioms coverage6T

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH W6T: every real source-to-sink flow is reported (in
    some layer). Hypotheses: S10 (`Program.WF`), an applicable abstraction, `W6.SummaryStar`. -/
theorem vuln_found6T (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D6T P taint counted L α sinks roots (.vuln M n s b) := by
  obtain ⟨b, hb⟩ := Coverage.vuln_found P counted L α sinks roots hwf hα hR hs hT hsc
  obtain ⟨b', hb', _⟩ := D_le_D6T P taint counted L α sinks roots hS hb
  exact ⟨b', hb'⟩

#print axioms vuln_found6T

end Sound1

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH W6T, for the policy (run 1 is `policy1 = policy (fun
    _ => [])`): every real source-to-sink flow is reported. The only hypothesis is S10
    (`Program.WF`); no hypothesis on the taint edges. -/
theorem vuln_found_policy6T {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (demand : MethodId → List PFact)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D6T P taint counted L (policy demand) sinks roots (.vuln M n s b) :=
  vuln_found6T P taint counted L (policy demand) sinks roots hwf (policy_applicable demand)
    (W6.summaryStar_policy P counted L demand sinks roots) hR hs hT hsc

#print axioms vuln_found_policy6T

/-- The simulation of run 1 (`policy1`) without hypothesis. -/
theorem D_le_D6T_1 {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {o : Obj}
    (h : D P counted L policy1 sinks roots o) : W6.Up (D6T P taint counted L policy1 sinks roots) o :=
  D_le_D6T P taint counted L policy1 sinks roots
    (W6.summaryStar_policy P counted L (fun _ => []) sinks roots) h

theorem D6T_le_D_1 {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {o : Obj}
    (h : D6T P taint counted L policy1 sinks roots o) : W6.Down (D P counted L policy1 sinks roots) o :=
  D6T_le_D P taint counted L policy1 sinks roots
    (W6.summaryStar_policy P counted L (fun _ => []) sinks roots) h

#print axioms D_le_D6T_1
#print axioms D6T_le_D_1

/-- `D6T_normal` for run 1 (`policy1`), with no hypothesis: a normal edge of `D6T` is a normal edge
    of `D` with the same fact. -/
theorem D6T_normal_1 {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6T P taint counted L policy1 sinks roots (.edge M i n f)) (hf : f.demand = false) :
    D P counted L policy1 sinks roots (.edge M i n f) :=
  D6T_normal P taint counted L policy1 sinks roots
    (W6.summaryStar_policy P counted L (fun _ => []) sinks roots) h hf

#print axioms D6T_normal_1

/-! ### The kinds invariant of run 1: a normal `[any]` conclusion has a concrete mark -/

/-- The motive: a normal `[any]` final fact (the spec `[any-taint]`) has a concrete mark. -/
def AnyConc (f : AFact) : Prop := f.fact.kind = .any → f.demand = false → ∃ t, f.fact.mark = .conc t

theorem norm_anyConc {y : AFact} (h : AnyConc y) : AnyConc y.norm := by
  unfold AFact.norm
  split
  · exact h
  · exact h
  · intro hk; cases hk
  · intro _ hd; cases hd
  · exact h

theorem norm_demand {y : AFact} (h : y.demand = true) : y.norm.demand = true := by
  unfold AFact.norm
  split <;> first | exact h | rfl

theorem belowCase_any_src {ck fk tk : Kind} {r tp p : List Acc} {ap : Bool}
    (h : belowCase ck fk r tp tk = some (p, .any, ap)) : tk = .any ∨ ck = .any := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | any => exact Or.inl rfl
    | star et =>
      cases r with
      | cons a r' =>
        dsimp only at h
        cases he : et.admits (a :: r') with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [he, if_pos rfl] at h; cases h; exact Or.inr rfl
      | nil =>
        dsimp only at h
        cases ck with
        | exact => cases h
        | star ec => cases h
        | any => exact Or.inr rfl
    | exact =>
      cases ck <;> cases fk <;> cases r <;> cases h

theorem aboveCase_any_src {ck fk tk : Kind} {r tp p : List Acc} {ap : Bool}
    (h : aboveCase ck fk r tp tk = some (p, .any, ap)) (hap : ap = false) :
    tk = .any ∨ ck = .any := by
  unfold aboveCase at h
  cases ha : admitsTailB ck r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | any => exact Or.inl rfl
    | exact => cases h
    | star et =>
      cases h
      cases ck with
      | any => exact Or.inr rfl
      | star e => cases hap
      | exact => cases hap

/-- A normal `[any]` result of the geometry comes from an `[any]` target or an `[any]` fact. -/
theorem geo_any_src {ck fk tk : Kind} {P q tp p : List Acc} {ap : Bool}
    (h : CoreAux.geo ck fk P q tp tk = some (p, .any, ap)) (hap : ap = false) :
    tk = .any ∨ ck = .any := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r0 => rw [hrel] at h; exact aboveCase_any_src h hap
  | below r0 => rw [hrel] at h; exact belowCase_any_src h

/-- THE LOCAL STEP. `applyEdge` keeps `AnyConc` if an `[any]` target has a concrete mark. -/
theorem applyEdge_anyConc {c r : AFact} {fr to : PFact} (hc : AnyConc c)
    (hto : to.kind = .any → ∃ t, to.mark = .conc t) (hr : r ∈ (applyEdge c fr to).facts) :
    AnyConc r := by
  obtain ⟨p, k, ap, m, hg, _, hm, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hr
  apply norm_anyConc
  intro hk hd
  have hk' : k = .any := hk
  subst hk'
  obtain ⟨hcd, hap⟩ := Exact.or_eq_false hd
  rcases geo_any_src hg hap with htk | hck
  · obtain ⟨t, ht⟩ := hto htk
    rw [ht] at hm
    cases hm
    exact ⟨t, rfl⟩
  · obtain ⟨t, ht⟩ := hc hck hcd
    rw [ht] at hm
    exact CoreAux.markComp_conc hm

theorem limitF_anyConc {counted : Acc → Bool} {L : Nat} {f : AFact} (h : AnyConc f) :
    AnyConc (limitF counted L f) := by
  rcases Invariant.limitF_cases counted L f with e | ⟨_, hd⟩
  · rw [e]; exact h
  · intro _ hd'
    rw [hd] at hd'
    cases hd'

theorem raise_anyConc (x : AFact) : AnyConc ⟨x.fact, true⟩ := fun _ hd => by cases hd

/-- The statement transfer with W6T keeps `AnyConc` if every taint edge with an `[any]` target has
    a concrete target mark (`TaintConc`). -/
theorem transferT_anyConc {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c r : AFact}
    (hs : ∀ e, e ∈ s.edges → taint e = true → e.2.kind = .any → ∃ t, e.2.mark = .conc t)
    (hc : AnyConc c) (hr : r ∈ (transferT taint counted L s c).facts) : AnyConc r := by
  rcases transferT_mem_inv hr with ⟨_, rfl⟩ | ⟨e, x, he, hx, rfl⟩
  · exact hc
  · apply limitF_anyConc
    unfold w6t
    cases hb : (e.2.kind.isAny && !taint e) with
    | true => rw [if_pos rfl]; exact raise_anyConc x
    | false =>
      rw [if_neg Bool.false_ne_true]
      refine applyEdge_anyConc hc (fun hk => ?_) hx
      have ht : taint e = true := by
        rw [hk] at hb
        cases h2 : taint e with
        | true => rfl
        | false => rw [h2] at hb; cases hb
      exact hs e he ht hk

theorem concPart_mark (cl : Cleaner) (c : AFact) : (concPart cl c).fact.mark = c.fact.mark := by
  unfold concPart
  split <;> rfl

theorem cleanRes_anyConc {cl : Cleaner} {c f : AFact} (hc : AnyConc c)
    (h : f ∈ (cleanRes cl c).facts) : AnyConc f := by
  rcases Invariant.cleanRes_facts_cases h with rfl | ⟨t, _, hnc, rfl⟩ | ⟨_, _, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩
  · exact hc
  · intro hk hd
    obtain ⟨t', ht'⟩ := hc hk hd
    exact absurd ht' (hnc t')
  · intro _ hd
    rw [norm_demand (y := ⟨c.fact, true⟩) rfl] at hd
    cases hd
  · intro _ _
    exact ⟨t, by rw [concPart_mark, ht]⟩

theorem startFact_anyConc (i : PFact) : AnyConc (startFact i) := by
  obtain ⟨b, p, k, m⟩ := i
  intro hk hd
  cases k with
  | star e =>
    cases m with
    | star => cases hk
    | starEx x => cases hk
    | conc t => cases hd
  | any => cases hd
  | exact => cases hk

/-- A summary keeps `AnyConc` if the summary edge has it. -/
theorem applySummary_anyConc {a g r : AFact} {j : PFact} (ha : AnyConc a) (hg : AnyConc g)
    (hr : r ∈ (applySummary a j g).facts) : AnyConc r := by
  obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
  cases hgd : g.demand with
  | true =>
    intro _ hd
    rw [norm_demand (y := ⟨x.fact, x.demand || true⟩) (Bool.or_true _)] at hd
    cases hd
  | false =>
    have hxa : AnyConc x := applyEdge_anyConc ha (fun hk => hg hk hgd) hx
    apply norm_anyConc
    intro hk hd
    exact hxa hk (by rw [Bool.or_false] at hd; exact hd)

/-- The motive of the kinds invariant. -/
def AnyConcObj : Obj → Prop
  | .edge _ _ _ f => AnyConc f
  | _ => True

section Kinds1
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

theorem D6T_anyConc_all (htc : TaintConc P taint) (hbn : BindNoAny P) {o : Obj}
    (h : D6T P taint counted L α sinks roots o) : AnyConcObj o := by
  induction h with
  | start => exact startFact_anyConc _
  | @step M i n f n' s f' _ hE hf ih =>
    refine transferT_anyConc (fun e he ht hk => ?_) ih hf
    exact (htc _ _ _ _ hE e he ht).2.1
  | pass _ _ _ ih => exact ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihF _ ihG =>
    have hno : ∀ e : MicroEdge, e.2.kind.isAny = false → e.2.kind = .any → ∃ t, e.2.mark = .conc t :=
      fun e h1 h2 => by rw [h2] at h1; cases h1
    have hA : AnyConc a :=
      applyEdge_anyConc ihF (hno e1 ((hbn _ _ _ _ hE).1 e1 he1)) ha
    have hR : AnyConc r := applySummary_anyConc hA ihG hr
    exact limitF_anyConc (applyEdge_anyConc hR (hno e2 ((hbn _ _ _ _ hE).2 e2 he2)) hr')
  | clean _ _ hf ih => exact cleanRes_anyConc ih hf
  | filt _ _ _ ih => exact ih
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initA => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

/-- THE KINDS INVARIANT OF RUN 1 (ap.md §7.2 with F69, decision 2): every NORMAL edge of `D6T`
    whose conclusion has the `[any]` tail (a spec `[any-taint]` conclusion) has a CONCRETE mark.
    Hypotheses: `TaintConc` (a taint edge with an `[any]` target has a concrete target mark; the
    interpreter duty of decision 3) and `BindNoAny` (no call binding has an `[any]` target; W6T
    reads only statement micro edges). No hypothesis on the abstraction: the claim holds for every
    `α`, so also for the run-1 policy. Every other normal `[any]` result is a copy of a normal
    `[any]` input (concrete by induction); the start fact, the field limit, the normal form and the
    cleaner give `[any]` only in the demand layer. -/
theorem D6T_any_conc (htc : TaintConc P taint) (hbn : BindNoAny P)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (hk : f.fact.kind = .any)
    (hd : f.demand = false) : ∃ t, f.fact.mark = .conc t :=
  D6T_anyConc_all P taint counted L α sinks roots htc hbn h hk hd

#print axioms D6T_any_conc

/-- A FLOW EDGE OF RUN 1 HAS NO `[any-taint]` LEAF: an edge of `D6T` whose premise has the mark `*`
    has no normal `[any]` conclusion (its mark is abstract, K1 `Kinds.flow_abstract`, and a normal
    `[any]` conclusion has a concrete mark, `D6T_any_conc`). Hypotheses: S7 (`Exact.MarkWF`),
    `TaintConc`, `BindNoAny`, `W6.SummaryStar` (for the simulation; the policy has it). -/
theorem D6T_flow_no_any_taint (hmw : Exact.MarkWF P) (htc : TaintConc P taint)
    (hbn : BindNoAny P) (hS : W6.SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6T P taint counted L α sinks roots (.edge M i n f)) (hi : i.mark = .star) :
    ¬ (f.fact.kind = .any ∧ f.demand = false) := by
  rintro ⟨hk, hd⟩
  obtain ⟨t, ht⟩ := D6T_any_conc P taint counted L α sinks roots htc hbn h hk hd
  obtain ⟨g, hg, hle⟩ := D6T_le_D P taint counted L α sinks roots hS h
  have habs := Kinds.flow_abstract P counted L α sinks roots hmw hg hi
  rw [hle.fact, ht] at habs
  rcases habs with h1 | ⟨x, h1⟩ <;> cases h1

#print axioms D6T_flow_no_any_taint

end Kinds1

/-- THE PARTITION OF RUN 1 WITH W6T (ap.md §7.2 with F69). For every edge of run 1 (`D6T`,
    `policy1`): the four claims of `Kinds.kinds_D` (the premise mark is `*` or concrete; a `*`
    premise gives an abstract conclusion mark and no `$` tail; a concrete premise gives a concrete
    conclusion mark and no `*` tail; a `*` tail has an abstract mark and is normal), and the two
    claims of F69: a normal `[any]` conclusion (`[any-taint]`) has a concrete mark, so a `*`
    premise (FLOW) has no `[any-taint]` conclusion. Hypotheses: those of `Kinds.kinds_D` (S7
    `MarkWF`, S8 `PremConc` and `NoUnivE`, `ExactTargetConc`) and `TaintConc`, `BindNoAny`. -/
theorem kinds_D6T {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (het : Kinds.ExactTargetConc P)
    (hA : Invariant.AllEdges P Invariant.PremConc) (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (htc : TaintConc P taint) (hbn : BindNoAny P)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6T P taint counted L policy1 sinks roots (.edge M i n f)) :
    (i.mark = .star ∨ ∃ t, i.mark = .conc t) ∧
    (i.mark = .star → Invariant.AbsMark f.fact.mark ∧ f.fact.kind ≠ .exact) ∧
    (∀ t, i.mark = .conc t → (∃ t', f.fact.mark = .conc t') ∧ f.fact.kind.isStar = false) ∧
    (∀ e, f.fact.kind = .star e → Invariant.AbsMark f.fact.mark ∧ f.demand = false) ∧
    (f.fact.kind = .any → f.demand = false → ∃ t, f.fact.mark = .conc t) ∧
    (i.mark = .star → ¬ (f.fact.kind = .any ∧ f.demand = false)) := by
  obtain ⟨g, hg, hle⟩ := D6T_le_D_1 (taint := taint) h
  obtain ⟨k1, k2, k3, k4⟩ := Kinds.kinds_D P counted L sinks roots hmw het hA hB hg
  have hf : g.fact = f.fact := hle.fact
  refine ⟨k1, ?_, ?_, ?_, D6T_any_conc P taint counted L policy1 sinks roots htc hbn h,
    fun hi => D6T_flow_no_any_taint P taint counted L policy1 sinks roots hmw htc hbn
      (W6.summaryStar_policy P counted L (fun _ => []) sinks roots) h hi⟩
  · intro hi
    rw [← hf]
    exact k2 hi
  · intro t ht
    rw [← hf]
    exact k3 t ht
  · intro e hk
    have hgk : g.fact.kind = .star e := by rw [hf]; exact hk
    have e1 : f = g := hle.star_eq (by rw [hgk]; rfl)
    rw [e1]
    exact k4 e hgk

#print axioms kinds_D6T

/-! ### The hypotheses of `D6T_any_conc` are necessary

  The program skeleton of `Kinds.CexK`: the root `0` binds the zero fact to the base `1` of the
  method `1`, and `policy1` gives the FLOW premise `i0 = (1,.,*,{},*)`. Two runs of run 1
  (`policy1`), each well-formed (S10) and with S7 (`MarkWF`), each with exactly one of the two
  hypotheses, derive a NORMAL `[any]` edge `i0 → (b,.,[any],*)` with the abstract mark `*` (a FLOW
  `[any-taint]` leaf, which decision 2 forbids):
  * `cex_taintConc`: a taint edge `1.* → 2.[any]` with the target mark `*` (`TaintConc` fails;
    `BindNoAny` holds);
  * `cex_bindNoAny`: a call binding `1.* → 2.[any]` into the method `2` (`BindNoAny` fails; no
    taint edge, so `TaintConc` holds). The callee summary `2.* → 2.*` is applied to the normal
    `[any]` binding and bound back to `3`. -/
namespace CexKinds

abbrev prog : List (MethodId × Node × Instr × Node) → Program := ApSpec.Kinds.CexK.prog
abbrev call0 : Call := ApSpec.Kinds.CexK.call0
abbrev bnd : MicroEdge := ApSpec.Kinds.CexK.bnd
abbrev a0 : PFact := ApSpec.Kinds.CexK.a0
abbrev i0 : PFact := ApSpec.Kinds.CexK.i0

/-- A Boolean check of `BindNoAny` for one instruction. -/
def bindNoAnyB : Instr → Bool
  | .call c => c.toCallee.all (fun e => !e.2.kind.isAny) && c.fromCallee.all (fun e => !e.2.kind.isAny)
  | _ => true

theorem bindNoAny_of_check {P : Program} (h : P.edges.all (fun x => bindNoAnyB x.2.2.1) = true) :
    BindNoAny P := by
  intro M n c n' hE
  have h1 : bindNoAnyB (Instr.call c) = true := List.all_eq_true.mp h _ hE
  have h2 : (c.toCallee.all (fun e => !e.2.kind.isAny) &&
      c.fromCallee.all (fun e => !e.2.kind.isAny)) = true := h1
  rw [Bool.and_eq_true] at h2
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · have h3 := List.all_eq_true.mp h2.1 e he
    cases hk : e.2.kind.isAny with
    | false => rfl
    | true => rw [hk] at h3; cases h3
  · have h3 := List.all_eq_true.mp h2.2 e he
    cases hk : e.2.kind.isAny with
    | false => rfl
    | true => rw [hk] at h3; cases h3

/-- The common start of the runs: the start edge of `i0` in the method `1` (run 1, `D6T`). -/
theorem run_i0T (rest : List (MethodId × Node × Instr × Node)) (taint : TaintEdges)
    (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    D6T (prog rest) taint counted L policy1 sinks [0] (.edge 1 i0 0 ⟨i0, false⟩) := by
  have h1 : D6T (prog rest) taint counted L policy1 sinks [0] (.init 0 zeroFact) :=
    D6T.root (List.Mem.head _)
  have h2 := D6T.start h1
  have ha : (⟨a0, false⟩ : AFact) ∈ (applyEdge (startFact zeroFact) bnd.1 bnd.2).facts := by
    decide
  have h3 : D6T (prog rest) taint counted L policy1 sinks [0] (.added call0.callee a0) :=
    D6T.added (n' := 1) (e := bnd) (a := ⟨a0, false⟩) h2 (List.Mem.head _) (List.Mem.head _) ha
  have h4 : D6T (prog rest) taint counted L policy1 sinks [0] (.init 1 (policy1 1 a0)) :=
    D6T.initA h3
  rw [ApSpec.Kinds.CexK.policy1_a0] at h4
  exact D6T.start h4

/-- The `[any]` target with the mark `*`. -/
def tA : PFact := ⟨2, [], .any, .star⟩
def sT : Stmt := ⟨[1], [(i0, tA)]⟩
def progT : Program := prog [(1, 0, .stmt sT, 1)]
def taintAll : TaintEdges := fun _ => true

/-- WITHOUT `TaintConc`, THE KINDS INVARIANT IS FALSE: a taint edge with the target mark `*` keeps
    its `[any]` result normal, and the FLOW premise `i0` gets the normal `[any]` conclusion
    `(2,.,[any],*)` with an abstract mark. -/
theorem cex_taintConc (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progT.WF ∧ Exact.MarkWF progT ∧ BindNoAny progT ∧ ¬ TaintConc progT taintAll ∧
    D6T progT taintAll counted L policy1 sinks [0] (.edge 1 i0 1 ⟨tA, false⟩) ∧
    i0.mark = .star ∧ tA.kind = .any ∧ ∀ t, tA.mark ≠ .conc t := by
  refine ⟨Kinds.wf_of_check (by decide), Kinds.markWF_of_check (by decide),
    bindNoAny_of_check (by decide), fun h => ?_, ?_, rfl, rfl, fun t ht => by cases ht⟩
  · obtain ⟨_, ⟨t, ht⟩, _⟩ :=
      h 1 0 sT 1 (List.Mem.tail _ (List.Mem.head _)) _ (List.Mem.head _) rfl
    cases ht
  · have ht : (transferT taintAll counted L sT ⟨i0, false⟩).facts = [⟨tA, false⟩] := rfl
    exact D6T.step (s := sT) (run_i0T _ taintAll counted L sinks)
      (List.Mem.tail _ (List.Mem.head _)) (by rw [ht]; exact List.Mem.head _)

#print axioms cex_taintConc

def j2 : PFact := ⟨2, [], .star Excl.empty, .star⟩
def eA : MicroEdge := (i0, tA)
def eB : MicroEdge := (j2, ⟨3, [], .star Excl.empty, .star⟩)
def cA : Call := ⟨2, [1], [eA], [eB]⟩
def sNil : Stmt := ⟨[], []⟩
def progB : Program := prog [(1, 0, .call cA, 1), (2, 0, .stmt sNil, 9)]
def tB : PFact := ⟨3, [], .any, .star⟩

/-- WITHOUT `BindNoAny`, THE KINDS INVARIANT IS FALSE: a call binding with an `[any]` target (W6T
    reads only statement micro edges) gives a normal `[any]` binding with the mark `*`; the callee
    summary `2.* → 2.*` and the binding back give the normal `[any]` conclusion `(3,.,[any],*)` of
    the FLOW premise `i0`. There is no taint edge, so `TaintConc` holds. -/
theorem cex_bindNoAny (counted : Acc → Bool) (L : Nat) (sinks : List (MethodId × Node × PFact)) :
    progB.WF ∧ Exact.MarkWF progB ∧ TaintConc progB (fun _ => false) ∧ ¬ BindNoAny progB ∧
    D6T progB (fun _ => false) counted L policy1 sinks [0] (.edge 1 i0 1 ⟨tB, false⟩) ∧
    i0.mark = .star ∧ tB.kind = .any ∧ ∀ t, tB.mark ≠ .conc t := by
  have htc : TaintConc progB (fun _ => false) := fun _ _ _ _ _ _ _ h => by cases h
  refine ⟨Kinds.wf_of_check (by decide), Kinds.markWF_of_check (by decide),
    htc, fun h => ?_, ?_, rfl, rfl, fun t ht => by cases ht⟩
  · have h1 := (h 1 0 cA 1 (List.Mem.tail _ (List.Mem.head _))).1 eA (List.Mem.head _)
    cases h1
  · have hf := run_i0T [(1, 0, .call cA, 1), (2, 0, .stmt sNil, 9)] (fun _ => false) counted L sinks
    have hE : ((1 : MethodId), (0 : Node), Instr.call cA, (1 : Node)) ∈ progB.edges :=
      List.Mem.tail _ (List.Mem.head _)
    have ha : (⟨tA, false⟩ : AFact) ∈ (applyEdge ⟨i0, false⟩ eA.1 eA.2).facts := by decide
    have hadd : D6T progB (fun _ => false) counted L policy1 sinks [0] (.added 2 tA) :=
      D6T.added (c := cA) (e := eA) (a := ⟨tA, false⟩) hf hE (List.Mem.head _) ha
    have hj : D6T progB (fun _ => false) counted L policy1 sinks [0] (.init 2 j2) := by
      have h0 := D6T.initA hadd
      have e : policy1 2 tA = j2 := by decide
      rw [e] at h0
      exact h0
    have hs : D6T progB (fun _ => false) counted L policy1 sinks [0] (.edge 2 j2 0 ⟨j2, false⟩) :=
      D6T.start hj
    have hx : D6T progB (fun _ => false) counted L policy1 sinks [0] (.edge 2 j2 9 ⟨j2, false⟩) :=
      D6T.step (s := sNil) hs (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        (List.Mem.head _ : (⟨j2, false⟩ : AFact) ∈ [(⟨j2, false⟩ : AFact)])
    have hr : (⟨tA, false⟩ : AFact) ∈ (applySummary ⟨tA, false⟩ j2 ⟨j2, false⟩).facts := by decide
    have hr' : (⟨tB, false⟩ : AFact) ∈ (applyEdge ⟨tA, false⟩ eB.1 eB.2).facts := by decide
    have hret := D6T.ret (c := cA) (e1 := eA) (a := ⟨tA, false⟩) (j := j2) (g := ⟨j2, false⟩)
      (r := ⟨tA, false⟩) (e2 := eB) (r' := ⟨tB, false⟩) hf hE (List.Mem.head _) ha hj
      (by decide) hx hr (List.Mem.head _) hr'
    exact hret

#print axioms cex_bindNoAny

end CexKinds

/-! ### The W6 run is not more precise than `D6T` -/

/-- `W6.ExactInitConc` for `D6T`: a `$` initial fact has a concrete mark if the abstraction gives
    a `$` fact only with a concrete mark (the root and the answers have concrete marks). -/
theorem D6T_eic {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hα : ∀ m a, (α m a).kind = .exact → ∃ t, (α m a).mark = .conc t) :
    W6.ExactInitConc (D6T P taint counted L α sinks roots) := by
  have key : ∀ o, D6T P taint counted L α sinks roots o → W6.EIC o := by
    intro o h
    induction h with
    | root => exact fun _ => ⟨zeroMark, rfl⟩
    | initA => exact hα _ _
    | @answer M i t a _ _ _ _ _ _ => exact fun _ => ⟨t, W6.answerInit_mark i a t⟩
    | start => trivial
    | step => trivial
    | reqStmt => trivial
    | pass => trivial
    | added => trivial
    | ret => trivial
    | reqSink => trivial
    | reqUp => trivial
    | vuln => trivial
    | clean => trivial
    | reqClean => trivial
    | filt => trivial
  exact fun m j h => key _ h

#print axioms D6T_eic

/-- W6 on an `[any]` fact is its raise. -/
theorem w6_of_any {g : AFact} (h : g.fact.kind = .any) : W6.w6 g = ⟨g.fact, true⟩ := by
  unfold W6.w6
  rw [h]
  rfl

section D6Sim
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- THE W6 RUN `W6.D6` INTO `D6T`: every object of `D6` is an object of `D6T`, every edge with the
    same fact in the same or a LOWER layer. (W6T raises only a subset of the results that W6
    raises.) Hypothesis: the abstraction gives a `$` fact only with a concrete mark (the policy
    has it, `W6.policy_eic`). -/
theorem D6_le_D6T (hα : ∀ m a, (α m a).kind = .exact → ∃ t, (α m a).mark = .conc t) {o : Obj}
    (h : W6.D6 P counted L α sinks roots o) : W6.Down (D6T P taint counted L α sinks roots) o := by
  induction h with
  | root hM => exact D6T.root hM
  | @start M i _ ih => exact ⟨_, D6T.start ih, W6.LE_w6_self _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨f0, hf0, hl0⟩ := (W6.transfer_LL hle).1.bwd hf
    obtain ⟨f'', hf'', hrel⟩ := transfer_memTA (taint := taint) hf0
    refine ⟨f'', D6T.step hg hE hf'', ?_⟩
    rcases hrel with rfl | ⟨hk, rfl⟩
    · exact W6.LE_w6 hl0
    · have hk' : f'.fact.kind = .any := by rw [← hl0.fact]; exact hk
      rw [w6_of_any hk', ← hl0.fact]
      exact W6.LE.refl _
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqStmt hg hE (by rw [transferT_reqs, (W6.transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6T.pass hg hE (by rw [hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hle).1.bwd ha
    show D6T P taint counted L α sinks roots (.added c.callee a.fact)
    rw [← hla.fact]
    exact D6T.added hg hE he ha0
  | initA _ ih => exact D6T.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f0, hf0, hlf⟩ := ihF
    obtain ⟨g0, hg0, hlg⟩ := ihG
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hlf).1.bwd ha
    have happ0 : applicable j a0.fact = true := by rw [hla.fact]; exact happ
    have hX : ∀ x, x ∈ (applyEdge a0 j g0.fact).facts → x.fact.kind.isStar = true → g = g0 :=
      fun x hx hxs => hlg.star_eq
        (W6.summary_star (D6T_eic hα _ _ ihJ) (Invariant.applyEdge_Legal ha0) hx hxs)
    obtain ⟨r0, hr0, hlr⟩ := (W6.applySummary_LL (W6.LE_w6 hla) hlg hX).bwd hr
    obtain ⟨r0', hr0', hlr'⟩ := (W6.applyEdge_LL (W6.LE_w6 hlr)).1.bwd hr'
    exact ⟨_, D6T.ret hf0 hE he1 ha0 ihJ happ0 hg0 hr0 he2 hr0', W6.LE_w6 (W6.limitF_LE hlr')⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqSink hg hs (by rw [W6.check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact D6T.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a0, ha0, hla⟩ := (W6.applyEdge_LL hle).1.bwd ha
    exact D6T.reqUp ihR hg hE hc he ha0 (by rw [hla.fact]; exact hcl) (by rw [hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, D6T.vuln hg hs (by rw [W6.check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (W6.cleanRes_LL hle).1.bwd hf
    exact ⟨g', D6T.clean hg hE hg', W6.LE_w6 hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6T.reqClean hg hE (by rw [(W6.cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6T.filt hg hE (by rw [hle.fact]; exact hp), hle⟩

#print axioms D6_le_D6T

/-- THE OLD W6 RUN IS NOT MORE PRECISE: every normal edge of `W6.D6` is a normal edge of `D6T`
    (and every normal edge of `D6T` is a normal edge of `D`, `D6T_normal`): the normal edges of
    `D6T` lie between those of `D6` and those of `D`. Hypothesis: as `D6_le_D6T`. -/
theorem D6_normal_D6T (hα : ∀ m a, (α m a).kind = .exact → ∃ t, (α m a).mark = .conc t)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : W6.D6 P counted L α sinks roots (.edge M i n f)) (hf : f.demand = false) :
    D6T P taint counted L α sinks roots (.edge M i n f) := by
  obtain ⟨g, hg, hle⟩ := D6_le_D6T P taint counted L α sinks roots hα h
  rw [hle.eq_of_normal hf]
  exact hg

#print axioms D6_normal_D6T

end D6Sim

/-- `D6_normal_D6T` for run 1 (`policy1`), with no hypothesis. -/
theorem D6_normal_D6T_1 {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : W6.D6 P counted L policy1 sinks roots (.edge M i n f)) (hf : f.demand = false) :
    D6T P taint counted L policy1 sinks roots (.edge M i n f) :=
  D6_normal_D6T P taint counted L policy1 sinks roots (W6.policy_eic (fun _ => [])) h hf

#print axioms D6_normal_D6T_1

/-! ### The hypothesis `W6.SummaryStar` stays: the W6 counterexample works for `D6T`

  With no taint edge (`taint = fun _ => false`; `TaintConc` and `BindNoAny` hold), W6T demotes
  every statement result with an `[any]` target, as W6 does. The program `W6.Cex.Pc` makes
  `5.[any]` by a statement, so the summary `jX → 3.$` of method `2` is in the demand layer in
  `D6T`, and its application to `2.*/Universe` gives `3.$` (demand) where `D` gives `3.*/Universe`
  (`W6.Cex`). So `D6T` has the exit edge `1.* → 4.$` and `D` has only `1.* → 4.*/Universe` at that
  place: a FACT changes, and `D6T` is not simulated by `D`. -/
namespace CexT
open W6.Cex

theorem taintConc_none : TaintConc Pc (fun _ => false) :=
  fun _ _ _ _ _ _ _ h => by cases h

theorem bindNoAny_Pc : BindNoAny Pc := by
  intro M n c n' hE
  rcases pc_edges hE with h | h | h | h <;> cases h
  · exact ⟨fun e he => by rcases List.mem_singleton.mp he with rfl; rfl,
      fun e he => absurd he List.not_mem_nil⟩
  · exact ⟨fun e he => by rcases List.mem_singleton.mp he with rfl; rfl,
      fun e he => by rcases List.mem_singleton.mp he with rfl; rfl⟩

section Runs
variable (counted : Acc → Bool) (L : Nat)

/-- `D6T` (no taint edge) has the demand exit edge `1.* → 4.$`. -/
theorem d6t_fE : D6T Pc (fun _ => false) counted L αc [] [0] (.edge 1 i0 1 fE) := by
  have h1 : D6T Pc (fun _ => false) counted L αc [] [0] (.init 0 zeroFact) :=
    D6T.root (List.Mem.head _)
  have h2 : D6T Pc (fun _ => false) counted L αc [] [0] (.edge 0 zeroFact 0 zA) := D6T.start h1
  have h3 : D6T Pc (fun _ => false) counted L αc [] [0] (.added 1 a0) :=
    D6T.added (n' := 1) (c := c0) (e := b0) (a := ⟨a0, false⟩) h2 (List.Mem.head _)
      (List.Mem.head _) (by decide)
  have h4 : D6T Pc (fun _ => false) counted L αc [] [0] (.init 1 i0) := D6T.initA h3
  have h5 : D6T Pc (fun _ => false) counted L αc [] [0] (.edge 1 i0 0 ⟨i0, false⟩) := D6T.start h4
  have h6 : D6T Pc (fun _ => false) counted L αc [] [0] (.added 2 aU) :=
    D6T.added (n' := 1) (c := c1) (e := b1) (a := ⟨aU, false⟩) h5
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide)
  have h7 : D6T Pc (fun _ => false) counted L αc [] [0] (.init 2 jX) := D6T.initA h6
  have h8 : D6T Pc (fun _ => false) counted L αc [] [0] (.edge 2 jX 0 ⟨jX, false⟩) := D6T.start h7
  have h9 : D6T Pc (fun _ => false) counted L αc [] [0]
      (.edge 2 jX 2 ⟨⟨5, [], .any, .star⟩, true⟩) :=
    D6T.step (s := sA) h8 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (List.Mem.head _ : (⟨⟨5, [], .any, .star⟩, true⟩ : AFact) ∈
        [(⟨⟨5, [], .any, .star⟩, true⟩ : AFact)])
  have h10 : D6T Pc (fun _ => false) counted L αc [] [0]
      (.edge 2 jX 1 ⟨⟨3, [], .exact, .star⟩, true⟩) :=
    D6T.step (s := sB) h9
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      (List.Mem.head _ : (⟨⟨3, [], .exact, .star⟩, true⟩ : AFact) ∈
        [(⟨⟨3, [], .exact, .star⟩, true⟩ : AFact)])
  exact D6T.ret (n' := 1) (c := c1) (e1 := b1) (a := ⟨aU, false⟩) (j := jX)
    (g := ⟨⟨3, [], .exact, .star⟩, true⟩) (r := ⟨⟨3, [], .exact, .star⟩, true⟩) (e2 := b2)
    (r' := fE) h5 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide) h7
    (by decide) h10 (by decide) (List.Mem.head _) (by decide)

/-- THE HYPOTHESIS OF THE RUN-1 SIMULATION IS NECESSARY FOR `D6T`: a well-formed program with no
    taint edge (so `TaintConc` and `BindNoAny` hold) whose `D6T` has the demand exit edge
    `1.* → 4.$`, while every edge of `D` at that place is the normal `1.* → 4.*/Universe`. W6T
    changes a FACT, so `D6T` is not simulated by `D` (`W6.Down`), and `W6.SummaryStar` fails. -/
theorem cex_w6t_changes_fact :
    Pc.WF ∧ TaintConc Pc (fun _ => false) ∧ BindNoAny Pc ∧
    D6T Pc (fun _ => false) counted L αc [] [0] (.edge 1 i0 1 fE) ∧
    (∀ f, D Pc counted L αc [] [0] (.edge 1 i0 1 f) → f = fU) ∧
    fU.fact ≠ fE.fact ∧
    ¬ W6.SummaryStar Pc (D Pc counted L αc [] [0]) ∧
    ¬ (∀ o, D6T Pc (fun _ => false) counted L αc [] [0] o → W6.Down (D Pc counted L αc [] [0]) o) := by
  obtain ⟨hwf, _, _, hD, _, hne, hS, _⟩ := cex_w6_changes_fact counted L
  refine ⟨hwf, taintConc_none, bindNoAny_Pc, d6t_fE counted L, hD, hne, hS, ?_⟩
  intro hdown
  obtain ⟨f, hf, hle⟩ := hdown _ (d6t_fE counted L)
  rw [hD f hf] at hle
  rcases hle with h | ⟨h, _⟩
  · cases h
  · cases h

#print axioms cex_w6t_changes_fact

end Runs

end CexT

/-! ## 3. The restricted forward run with must-premises (`DRT`) -/

/-- Every edge of a run with must flags has its initial fact (with the same flag). -/
def EdgeHasInit (R : TObj → Prop) : TObj → Prop
  | .edge M j mj _ _ => R (.init M j mj)
  | _ => True

/-- `DRT` objects seen from `DR`: the same initial fact, added fact, request; an edge with the same
    fact (any layer); a vulnerability (any layer). -/
def DownT (R : Obj → Prop) : TObj → Prop
  | .init M j _      => R (.init M j)
  | .edge M j _ n f  => ∃ g, R (.edge M j n g) ∧ g.fact = f.fact
  | .added M a _     => R (.added M a)
  | .req M j t       => R (.req M j t)
  | .vuln M n s _    => ∃ d, R (.vuln M n s d)

/-- `DR` objects seen from `DRT`: some must flag, the same fact (any layer). -/
def UpT (R : TObj → Prop) : Obj → Prop
  | .init M j       => ∃ mj, R (.init M j mj)
  | .edge M j n f   => ∃ mj g, R (.edge M j mj n g) ∧ g.fact = f.fact
  | .added M a      => ∃ am, R (.added M a am)
  | .req M j t      => R (.req M j t)
  | .vuln M n s _   => ∃ d, R (.vuln M n s d)

/-- The must flag of an edge premise changes only layers: for every other flag of the same
    initial fact, an edge with the same fact. -/
def FlagSwap (R : TObj → Prop) : TObj → Prop
  | .edge M j _ n f => ∀ mj', R (.init M j mj') → ∃ g, R (.edge M j mj' n g) ∧ g.fact = f.fact
  | _ => True

section ClosureRT
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

local notation "DRTr" => DRT P taint counted L demand emit sat restrict recs sinks roots
local notation "DRr" => DR P counted L demand emit sat restrict (recsDR recs) sinks roots

theorem mustAny_edge {M M' : MethodId} {j : PFact} {mj : Bool} {n n' : Node} {f f' : AFact}
    (h : MustAnyT (.edge M j mj n f)) : MustAnyT (.edge M' j mj n' f') := by
  cases mj <;> exact h

/-- Every edge of `DRT` has its initial fact, with the same must flag. -/
theorem DRT_edge_init {o : TObj} (h : DRTr o) : EdgeHasInit DRTr o := by
  induction h with
  | start hj _ => exact hj
  | step _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ihF _ _ => exact ihF
  | retRec _ _ _ _ _ _ _ _ _ ihF => exact ihF
  | clean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initR => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms DRT_edge_init

/-- THE MUST FLAG IS AN `[any]` PREMISE: every must-premise of `DRT` (an initial fact or an edge
    premise with `must = true`) has the `.any` tail (decision 6: the premise `[any-taint]`). The
    emission gives the flag only to an `[any]` premise (`emitTWith_must_any`). No hypothesis. -/
theorem DRT_mustAny {o : TObj} (h : DRTr o) : MustAnyT o := by
  induction h with
  | root => trivial
  | @start M j mj _ ih => cases mj; trivial; exact ih
  | step _ _ _ ih => exact mustAny_edge ih
  | pass _ _ _ ih => exact mustAny_edge ih
  | @initR m a am d j mj _ _ hj _ => cases mj; trivial; exact emitTWith_must_any hj
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ihF _ _ => exact mustAny_edge ihF
  | retRec _ _ _ _ _ _ _ _ _ ihF => exact mustAny_edge ihF
  | clean _ _ _ ih => exact mustAny_edge ih
  | filt _ _ _ ih => exact mustAny_edge ih
  | reqStmt => trivial
  | added => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms DRT_mustAny

theorem startT_fact_of {M : MethodId} {j : PFact} {mj : Bool} (h : DRTr (.init M j mj)) :
    (startT j mj).fact = (startFact j).fact := by
  have hma := DRT_mustAny h
  cases mj
  · exact startT_fact (Or.inr rfl)
  · exact startT_fact (Or.inl hma)

/-- The restriction of two summary edges with the same fact. -/
theorem restrict_same (hRF : RestrictFact restrict) {j : PFact} {g g0 g' : AFact} {d : DemandEdge}
    (hg : g.fact = g0.fact) (hres : restrict j g d = some g') :
    ∃ g0', restrict j g0 d = some g0' ∧ g0'.fact = g'.fact := by
  have hR := hRF j g g0 d hg
  rw [hres] at hR
  cases h0 : restrict j g0 d with
  | none => rw [h0] at hR; cases hR
  | some x => rw [h0] at hR; exact ⟨x, rfl, (Option.some.inj hR).symm⟩

/-- THE FACT SIMULATION, `DRT` INTO `DR`: every object of `DRT` has an object of `DR` (with the
    record set `recsDR recs`) with the same fact; the must flags are forgotten, the layers of the
    edges and of the vulnerabilities may differ. Hypotheses: `EmitCopiesMark emit` (the run is
    concrete, so no fact has the `*` tail, and a fact does not depend on its layer:
    `applyEdge_same`, `applySummary_same`, …) and `RestrictFact restrict`. -/
theorem DRT_down (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) {o : TObj}
    (h : DRTr o) : DownT DRr o := by
  induction h with
  | root hM => exact DR.root hM
  | @start M j mj hj ih => exact ⟨_, DR.start ih, (startT_fact_of hj).symm⟩
  | @step M i mi n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    obtain ⟨x, hx, hxf⟩ := transferT_mem hf
    obtain ⟨y, hy, hyx⟩ := transfer_same hgf.symm hns hx
    exact ⟨y, DR.step hg hE hy, hyx.trans hxf.fact⟩
  | @reqStmt M i mi n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    exact DR.reqStmt hg hE (by rw [← transfer_reqs_same hgf.symm hns, ← transferT_reqs taint]; exact ht)
  | @pass M i mi n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    exact ⟨g, DR.pass hg hE (by rw [hgf]; exact hm), hgf⟩
  | @added M i mi n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    obtain ⟨y, hy, hyx⟩ := applyEdge_same hgf.symm hns ha
    show DRr (.added c.callee a.fact)
    rw [← hyx]
    exact DR.added hg hE he hy
  | @initR m a am d j mj _ hd hj ih => exact DR.initR ih hd (emitTWith_some hj).1
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr'
      ihF ihJ ihG =>
    obtain ⟨gf, hgf, hgff⟩ := ihF
    obtain ⟨gg, hgg, hggf⟩ := ihG
    have hnsF : f.fact.kind.isStar = false := by rw [← hgff]; exact RExact.final_not_star hem hgf
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨g0', hres0, hg0'⟩ := restrict_same hRF hggf.symm hres
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA hg0'.symm hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    exact ⟨_, DR.ret hgf hE he1 ha0 ihJ hgg hd hres0 (by rw [ha0f]; exact hsat) hr0 he2 hr0',
      limitF_fact_eq hr0'f⟩
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihF =>
    obtain ⟨gf, hgf, hgff⟩ := ihF
    have hnsF : f.fact.kind.isStar = false := by rw [← hgff]; exact RExact.final_not_star hem hgf
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA rfl hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    refine ⟨_, DR.retRec hgf hE he1 ha0 ⟨mj, hrec⟩ (by rw [ha0f]; exact hsat) hr0 he2 hr0', ?_⟩
    rw [limitF_recLayer_fact]
    exact limitF_fact_eq hr0'f
  | @reqSink M i mi n f s t _ hs hc ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    exact DR.reqSink hg hs (by rw [check_same i s hgf]; exact hc)
  | answer _ _ hm ho ihR ihA => exact DR.answer ihR ihA hm ho
  | @reqUp m j t M ic mc n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hgf⟩ := ihF
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgf.symm hns ha
    exact DR.reqUp ihR hg hE hc he ha0 (by rw [ha0f]; exact hcl) (by rw [ha0f]; exact ho)
  | @vuln M i mi n f s _ hs hc ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    exact ⟨g.demand, DR.vuln hg hs (by rw [check_same i s hgf]; exact hc)⟩
  | @clean M i mi n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    obtain ⟨y, hy, hyx⟩ := cleanRes_same hgf.symm hns hf
    exact ⟨y, DR.clean hg hE hy, hyx⟩
  | @reqClean M i mi n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := by rw [← hgf]; exact RExact.final_not_star hem hg
    exact DR.reqClean hg hE (by rw [← cleanRes_reqs_same hgf.symm hns]; exact ht)
  | @filt M i mi n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hgf⟩ := ih
    exact ⟨g, DR.filt hg hE (by rw [hgf]; exact hp), hgf⟩

#print axioms DRT_down

/-- THE FACT SIMULATION, `DR` INTO `DRT`: every object of `DR` (with the record set
    `recsDR recs`) has an object of `DRT` with the same fact, for some must flags; the layers may
    differ. Hypotheses: `EmitCopiesMark emit` and `RestrictFact restrict`. -/
theorem DR_up (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) {o : Obj}
    (h : DRr o) : UpT DRTr o := by
  induction h with
  | root hM => exact ⟨false, DRT.root hM⟩
  | @start M j _ ih =>
    obtain ⟨mj, hj⟩ := ih
    exact ⟨mj, _, DRT.start hj, startT_fact_of hj⟩
  | @step M i n f n' s f' hf0 hE hf ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨x, hx, hxf⟩ := transfer_same hgf.symm hns hf
    obtain ⟨f'', hf'', hle⟩ := transfer_memT (taint := taint) hx
    exact ⟨mi, f'', DRT.step hg hE hf'', hle.fact.symm.trans hxf⟩
  | @reqStmt M i n f n' s t hf0 hE ht ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    exact DRT.reqStmt hg hE (by rw [transferT_reqs, ← transfer_reqs_same hgf.symm hns]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    exact ⟨mi, g, DRT.pass hg hE (by rw [hgf]; exact hm), hgf⟩
  | @added M i n f n' c e a hf0 hE he ha ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨y, hy, hyx⟩ := applyEdge_same hgf.symm hns ha
    refine ⟨y.fact.kind.isAny && !y.demand, ?_⟩
    rw [← hyx]
    exact DRT.added hg hE he hy
  | @initR m a d j _ hd hj ih =>
    obtain ⟨am, hA⟩ := ih
    exact ⟨_, DRT.initR hA hd (emitTWith_of hj am)⟩
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf0 hE he1 ha _ _ hd hres hsat hr he2 hr'
      ihF _ ihG =>
    obtain ⟨mi, gf, hgf, hgff⟩ := ihF
    obtain ⟨mj, gg, hgg, hggf⟩ := ihG
    have hjT : DRTr (.init c.callee j mj) := DRT_edge_init hgg
    have hnsF : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨g0', hres0, hg0'⟩ := restrict_same hRF hggf.symm hres
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA hg0'.symm hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    exact ⟨mi, _, DRT.ret hgf hE he1 ha0 hjT hgg hd hres0 (by rw [ha0f]; exact hsat) hr0 he2 hr0',
      limitF_fact_eq hr0'f⟩
  | @retRec M i n f n' c e1 a j g r e2 r' hf0 hE he1 ha hrec hsat hr he2 hr' ihF =>
    obtain ⟨mi, gf, hgf, hgff⟩ := ihF
    obtain ⟨mj, hrecT⟩ := hrec
    have hnsF : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA rfl hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    refine ⟨mi, _, DRT.retRec hgf hE he1 ha0 hrecT (by rw [ha0f]; exact hsat) hr0 he2 hr0', ?_⟩
    rw [limitF_recLayer_fact]
    exact limitF_fact_eq hr0'f
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    exact DRT.reqSink hg hs (by rw [check_same i s hgf]; exact hc)
  | answer _ _ hm ho ihR ihA =>
    obtain ⟨am, hA⟩ := ihA
    exact ⟨false, DRT.answer ihR hA hm ho⟩
  | @reqUp m j t M ic n f n' c e a _ hf0 hE hc he ha hcl ho ihR ihF =>
    obtain ⟨mc, g, hg, hgf⟩ := ihF
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgf.symm hns ha
    exact DRT.reqUp ihR hg hE hc he ha0 (by rw [ha0f]; exact hcl) (by rw [ha0f]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    exact ⟨g.demand, DRT.vuln hg hs (by rw [check_same i s hgf]; exact hc)⟩
  | @clean M i n f n' cl f' hf0 hE hf ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    obtain ⟨y, hy, hyx⟩ := cleanRes_same hgf.symm hns hf
    exact ⟨mi, y, DRT.clean hg hE hy, hyx⟩
  | @reqClean M i n f n' cl t hf0 hE ht ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    have hns : f.fact.kind.isStar = false := RExact.final_not_star hem hf0
    exact DRT.reqClean hg hE (by rw [← cleanRes_reqs_same hgf.symm hns]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨mi, g, hg, hgf⟩ := ih
    exact ⟨mi, g, DRT.filt hg hE (by rw [hgf]; exact hp), hgf⟩

#print axioms DR_up

end ClosureRT

/-- THE FACT SIMULATION OF THE RESTRICTED FORWARD RUN (`FactSim` of `AnyTaintDefs`): every object
    of `DRT` has an object of `DR` with the same fact (the must flags forgotten, the layers free),
    and every object of `DR` with the record set `recsDR recs` has an object of `DRT` with the same
    fact. Hypotheses: `EmitCopiesMark emit` (the spec `emitM` has it) and `RestrictFact restrict`
    (the spec `restrictU` has it, `restrictU_fact`). The key: in a concrete run no fact has the `*`
    tail, and then the AP operations give facts that do not depend on the layer of their input. -/
theorem factSim {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) :
    FactSim P taint counted L demand emit sat restrict recs sinks roots := by
  refine ⟨fun o h => ?_, fun o' h => ?_⟩
  · have hd := DRT_down hem hRF h
    cases o with
    | init M j mj => exact ⟨_, hd, rfl, rfl⟩
    | edge M j mj n f =>
      obtain ⟨g, hg, hgf⟩ := hd
      exact ⟨_, hg, rfl, rfl, rfl, hgf.symm⟩
    | added M a am => exact ⟨_, hd, rfl, rfl⟩
    | req M j t => exact ⟨_, hd, rfl, rfl, rfl⟩
    | vuln M n s d =>
      obtain ⟨d', hd'⟩ := hd
      exact ⟨_, hd', rfl, rfl, rfl⟩
  · have hu := DR_up (taint := taint) hem hRF h
    cases o' with
    | init M j =>
      obtain ⟨mj, hj⟩ := hu
      exact ⟨_, hj, rfl, rfl⟩
    | edge M j n f =>
      obtain ⟨mj, g, hg, hgf⟩ := hu
      exact ⟨_, hg, rfl, rfl, rfl, hgf⟩
    | added M a =>
      obtain ⟨am, ha⟩ := hu
      exact ⟨_, ha, rfl, rfl⟩
    | req M j t => exact ⟨_, hu, rfl, rfl, rfl⟩
    | vuln M n s d =>
      obtain ⟨d', hd'⟩ := hu
      exact ⟨_, hd', rfl, rfl, rfl⟩

#print axioms factSim

/-- The spec rules (`emitM`, `restrictU`; every `sat`) satisfy the hypotheses of the fact
    simulation. -/
theorem factSim_M {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {recs : MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} :
    FactSim P taint counted L demand emitM sat restrictU recs sinks roots :=
  factSim RExact.emitM_copies restrictU_fact

#print axioms factSim_M

section ClosureRT2
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

local notation "DRTr" => DRT P taint counted L demand emit sat restrict recs sinks roots
local notation "DRr" => DR P counted L demand emit sat restrict (recsDR recs) sinks roots

/-- CONCRETENESS OF `DRT` (from `RExact.DR_concrete` through the simulation): every initial fact,
    every edge (premise and final fact) and every added fact has a concrete mark, and `DRT` has no
    request object. Hypotheses: `EmitCopiesMark emit`, `RestrictFact restrict`. -/
theorem DRT_concrete (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) {o : TObj}
    (h : DRTr o) : ConcObjT o := by
  have hd := DRT_down hem hRF h
  cases o with
  | init M j mj => exact RExact.DR_concrete hem hd
  | edge M j mj n f =>
    obtain ⟨g, hg, hgf⟩ := hd
    obtain ⟨hj, t, ht⟩ := RExact.DR_concrete hem hg
    exact ⟨hj, t, by rw [← hgf]; exact ht⟩
  | added M a am => exact RExact.DR_concrete hem hd
  | req M j t => exact RExact.DR_concrete hem hd
  | vuln M n s d => trivial

#print axioms DRT_concrete

/-- NO MARK REQUEST IN `DRT` (from `RExact.DR_no_request`). -/
theorem DRT_no_request (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) :
    ∀ M j t, ¬ DRTr (.req M j t) :=
  fun _ _ _ h => DRT_concrete hem hRF h

#print axioms DRT_no_request

/-- No final fact of `DRT` has the `*` tail (W2, from `RExact.final_not_star`). -/
theorem DRT_final_not_star (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    {M : MethodId} {j : PFact} {mj : Bool} {n : Node} {f : AFact} (h : DRTr (.edge M j mj n f)) :
    f.fact.kind.isStar = false := by
  obtain ⟨g, hg, hgf⟩ := DRT_down hem hRF h
  rw [← hgf]
  exact RExact.final_not_star hem hg

#print axioms DRT_final_not_star

/-- EVERY MUST-PREMISE IS AN `[any-taint]` PREMISE: an initial fact of `DRT` with the must flag has
    the `.any` tail and a concrete mark (decision 2, decision 6); the same for the premise of an
    edge. Hypotheses: `EmitCopiesMark emit`, `RestrictFact restrict`. -/
theorem DRT_must_any (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    {M : MethodId} {j : PFact} (h : DRTr (.init M j true)) :
    j.kind = .any ∧ ∃ t, j.mark = .conc t :=
  ⟨DRT_mustAny h, DRT_concrete hem hRF h⟩

theorem DRT_must_any_edge (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    {M : MethodId} {j : PFact} {n : Node} {f : AFact} (h : DRTr (.edge M j true n f)) :
    j.kind = .any ∧ ∃ t, j.mark = .conc t :=
  ⟨DRT_mustAny h, (DRT_concrete hem hRF h).1⟩

#print axioms DRT_must_any
#print axioms DRT_must_any_edge

/-- THE KINDS OF `DRT` (ap.md §7.2 with F69): REACH and TAINT only. Every premise and every
    conclusion has a concrete mark (so no premise has the mark `*`: no FLOW edge), and no
    conclusion has a `*` tail; a must-premise is `[any-taint]` (`DRT_must_any`). Hypotheses:
    `EmitCopiesMark emit`, `RestrictFact restrict`. -/
theorem kinds_DRT (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    {M : MethodId} {i : PFact} {mi : Bool} {n : Node} {f : AFact} (h : DRTr (.edge M i mi n f)) :
    i.mark ≠ .star ∧ (∃ t, i.mark = .conc t) ∧ (∃ t, f.fact.mark = .conc t) ∧
      f.fact.kind.isStar = false ∧ (mi = true → i.kind = .any) := by
  obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := DRT_concrete hem hRF h
  refine ⟨fun hs => (by rw [hs] at ht; cases ht), ⟨t, ht⟩, ⟨t', ht'⟩,
    DRT_final_not_star hem hRF h, fun hm => ?_⟩
  subst hm
  exact DRT_mustAny h

#print axioms kinds_DRT

/-- THE MUST FLAG CHANGES ONLY LAYERS: if the same initial fact `j` of `DRT` has two must flags,
    every edge of one has an edge of the other with the same fact. Hypotheses: as `DRT_down`. -/
theorem DRT_flag_swap (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) {o : TObj}
    (h : DRTr o) : FlagSwap DRTr o := by
  induction h with
  | @start M j mj hj _ =>
    intro mj' hj'
    exact ⟨_, DRT.start hj', (startT_fact_of hj').trans (startT_fact_of hj).symm⟩
  | @step M i mi n f n' s f' hf hE hf' ih =>
    intro mi' hi'
    obtain ⟨g, hg, hgf⟩ := ih mi' hi'
    have hns : f.fact.kind.isStar = false := DRT_final_not_star hem hRF hf
    obtain ⟨x, hx, hxf⟩ := transferT_mem hf'
    obtain ⟨y, hy, hyx⟩ := transfer_same hgf.symm hns hx
    obtain ⟨g', hg', hle⟩ := transfer_memT (taint := taint) hy
    exact ⟨g', DRT.step hg hE hg', hle.fact.symm.trans (hyx.trans hxf.fact)⟩
  | @pass M i mi n f n' c _ hE hm ih =>
    intro mi' hi'
    obtain ⟨g, hg, hgf⟩ := ih mi' hi'
    exact ⟨g, DRT.pass hg hE (by rw [hgf]; exact hm), hgf⟩
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' hf hE he1 ha hJ hG hd hres hsat hr he2 hr'
      ihF _ _ =>
    intro mi' hi'
    obtain ⟨gf, hgf, hgff⟩ := ihF mi' hi'
    have hnsF : f.fact.kind.isStar = false := DRT_final_not_star hem hRF hf
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA rfl hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    exact ⟨_, DRT.ret hgf hE he1 ha0 hJ hG hd hres (by rw [ha0f]; exact hsat) hr0 he2 hr0',
      limitF_fact_eq hr0'f⟩
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' hf hE he1 ha hrec hsat hr he2 hr' ihF =>
    intro mi' hi'
    obtain ⟨gf, hgf, hgff⟩ := ihF mi' hi'
    have hnsF : f.fact.kind.isStar = false := DRT_final_not_star hem hRF hf
    obtain ⟨a0, ha0, ha0f⟩ := applyEdge_same hgff.symm hnsF ha
    have hnsA : a.fact.kind.isStar = false := Confirmed.applyEdge_nonstar hnsF ha
    obtain ⟨r0, hr0, hr0f⟩ := applySummary_same ha0f.symm hnsA rfl hr
    have hnsR : r.fact.kind.isStar = false := applySummary_nonstar' hnsA hr
    obtain ⟨r0', hr0', hr0'f⟩ := applyEdge_same hr0f.symm hnsR hr'
    refine ⟨_, DRT.retRec hgf hE he1 ha0 hrec (by rw [ha0f]; exact hsat) hr0 he2 hr0', ?_⟩
    rw [ha0f, limitF_recLayer_fact, limitF_recLayer_fact]
    exact limitF_fact_eq hr0'f
  | @clean M i mi n f n' cl f' hf hE hf' ih =>
    intro mi' hi'
    obtain ⟨g, hg, hgf⟩ := ih mi' hi'
    have hns : f.fact.kind.isStar = false := DRT_final_not_star hem hRF hf
    obtain ⟨y, hy, hyx⟩ := cleanRes_same hgf.symm hns hf'
    exact ⟨y, DRT.clean hg hE hy, hyx⟩
  | @filt M i mi n f n' b may _ hE hp ih =>
    intro mi' hi'
    obtain ⟨g, hg, hgf⟩ := ih mi' hi'
    exact ⟨g, DRT.filt hg hE (by rw [hgf]; exact hp), hgf⟩
  | root => trivial
  | reqStmt => trivial
  | added => trivial
  | initR => trivial
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | reqClean => trivial

#print axioms DRT_flag_swap

end ClosureRT2

/-! ### The hand-off: the summaries of `DRT` are those of `DR` -/

/-- A run with must flags as a run on `Obj` (the flags forgotten). The backward run and the
    iteration read a forward run through this view. -/
def forgetRun (R : TObj → Prop) (o : Obj) : Prop := ∃ oT, R oT ∧ oT.forget = o

/-- Objects of one run seen in another with the same facts (the layers free). -/
def FUp (R : Obj → Prop) : Obj → Prop
  | .init M i => R (.init M i)
  | .edge M i n f => ∃ g, R (.edge M i n g) ∧ g.fact = f.fact
  | .added M a => R (.added M a)
  | .req M i t => R (.req M i t)
  | .vuln M n s _ => ∃ d, R (.vuln M n s d)

theorem FUp_of_Up {R : Obj → Prop} {o : Obj} (h : W6.Up R o) : FUp R o := by
  cases o with
  | init => exact h
  | edge M i n f =>
    obtain ⟨g, hg, hle⟩ := h
    exact ⟨g, hg, hle.fact.symm⟩
  | added => exact h
  | req => exact h
  | vuln M n s d =>
    obtain ⟨d', hd', _⟩ := h
    exact ⟨d', hd'⟩

theorem FUp_of_Down {R : Obj → Prop} {o : Obj} (h : W6.Down R o) : FUp R o := by
  cases o with
  | init => exact h
  | edge M i n f =>
    obtain ⟨g, hg, hle⟩ := h
    exact ⟨g, hg, hle.fact⟩
  | added => exact h
  | req => exact h
  | vuln M n s d =>
    obtain ⟨d', hd', _⟩ := h
    exact ⟨d', hd'⟩

theorem FUp_of_UpT {R : TObj → Prop} {o : Obj} (h : UpT R o) : FUp (forgetRun R) o := by
  cases o with
  | init M j =>
    obtain ⟨mj, hj⟩ := h
    exact ⟨_, hj, rfl⟩
  | edge M j n f =>
    obtain ⟨mj, g, hg, hgf⟩ := h
    exact ⟨g, ⟨_, hg, rfl⟩, hgf⟩
  | added M a =>
    obtain ⟨am, ha⟩ := h
    exact ⟨_, ha, rfl⟩
  | req M j t => exact ⟨_, h, rfl⟩
  | vuln M n s d =>
    obtain ⟨d', hd'⟩ := h
    exact ⟨d', _, hd', rfl⟩

theorem FUp_of_forget {R : TObj → Prop} {R' : Obj → Prop} (hd : ∀ oT, R oT → DownT R' oT)
    {o : Obj} (h : forgetRun R o) : FUp R' o := by
  obtain ⟨oT, hT, rfl⟩ := h
  have h2 := hd oT hT
  cases oT with
  | init M j mj => exact h2
  | edge M j mj n f => exact h2
  | added M a am => exact h2
  | req M j t => exact h2
  | vuln M n s d => exact h2

theorem summaryDemand_of_FUp {P : Program} {R R' : Obj → Prop} (hup : ∀ o, R o → FUp R' o)
    {m : MethodId} {d : DemandEdge} (h : summaryDemand P R m d) : summaryDemand P R' m d := by
  obtain ⟨hi, hd⟩ := h
  refine ⟨hup _ hi, ?_⟩
  rcases hd with hn | ⟨g, hg, he⟩
  · exact Or.inl hn
  · obtain ⟨g', hg', hgf⟩ := hup _ hg
    exact Or.inr ⟨g', hg', by rw [he, hgf]⟩

theorem revSummaryDemand_of_FUp {P : Program} {R R' : Obj → Prop} (hup : ∀ o, R o → FUp R' o)
    {m : MethodId} {d : DemandEdge} (h : Backward.revSummaryDemand P R m d) :
    Backward.revSummaryDemand P R' m d := by
  obtain ⟨j, g, hsd, he⟩ := h
  exact ⟨j, g, summaryDemand_of_FUp hup hsd, he⟩

section HandOff
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

local notation "DRTr" => DRT P taint counted L demand emit sat restrict recs sinks roots
local notation "DRr" => DR P counted L demand emit sat restrict (recsDR recs) sinks roots

theorem DRT_FUp (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) :
    ∀ o, DRr o → FUp (forgetRun DRTr) o :=
  fun _ h => FUp_of_UpT (DR_up hem hRF h)

theorem DR_FUp (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) :
    ∀ o, forgetRun DRTr o → FUp DRr o :=
  fun _ h => FUp_of_forget (fun _ hT => DRT_down hem hRF hT) h

/-- THE SUMMARY DEMAND OF `DRT` IS THAT OF `DR`: the forward demand that `DRT` hands on (its
    initial facts with their exit facts, the must flags forgotten) is the summary demand of `DR`.
    Hypotheses: `EmitCopiesMark emit`, `RestrictFact restrict`. -/
theorem summaryDemandT_iff (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    (m : MethodId) (d : DemandEdge) :
    summaryDemand P (forgetRun DRTr) m d ↔ summaryDemand P DRr m d :=
  ⟨summaryDemand_of_FUp (DR_FUp hem hRF), summaryDemand_of_FUp (DRT_FUp hem hRF)⟩

#print axioms summaryDemandT_iff

/-- THE BACKWARD RUN READS THE SAME PATTERNS FROM `DRT` AS FROM `DR`: the reversed summary demand
    (the demand of the next backward run) of `DRT` is that of `DR`. So the must flags and the
    layers of `DRT` are not visible to the backward run: a pattern tail `[any-taint]` is a LABEL. -/
theorem revSummaryDemandT_iff (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    (m : MethodId) (d : DemandEdge) :
    Backward.revSummaryDemand P (forgetRun DRTr) m d ↔ Backward.revSummaryDemand P DRr m d :=
  ⟨revSummaryDemand_of_FUp (DR_FUp hem hRF), revSummaryDemand_of_FUp (DRT_FUp hem hRF)⟩

#print axioms revSummaryDemandT_iff

theorem backward_reads_sameT (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) :
    Backward.revSummaryDemand P (forgetRun DRTr) = Backward.revSummaryDemand P DRr :=
  funext fun m => funext fun d => propext (revSummaryDemandT_iff hem hRF m d)

#print axioms backward_reads_sameT

/-- The same sinks are reported (in some layer). -/
theorem vulnT_iff (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) (M : MethodId) (n : Node)
    (s : PFact) : (∃ b, DRTr (.vuln M n s b)) ↔ (∃ b, DRr (.vuln M n s b)) := by
  constructor
  · rintro ⟨b, hb⟩
    exact DRT_down hem hRF hb
  · rintro ⟨b, hb⟩
    exact DR_up hem hRF hb

#print axioms vulnT_iff

end HandOff

/-! ### Soundness of `DRT` -/

section SoundRT
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → PFact × Bool × AFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

local notation "DRTr" => DRT P taint counted L demand emit sat restrict recs sinks roots
local notation "DRr" => DR P counted L demand emit sat restrict (recsDR recs) sinks roots

/-- From a coverage result of `DR` to a coverage result of `DRT` (for every must flag of the
    initial fact). -/
theorem cov_transfer (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} {i : PFact} {mi : Bool}
    (hi : DRTr (.init M i mi))
    (h : (∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧
        FlowR P (summaryDemand P DRr) M l0 n l) ∨ DRr (.req M i l0.mark)) :
    ∃ f, DRTr (.edge M i mi n f) ∧ den i f.fact l0 l ∧
      FlowR P (summaryDemand P (forgetRun DRTr)) M l0 n l := by
  rcases h with ⟨f, hf, hd, hfr⟩ | hr
  · obtain ⟨mj, g, hg, hgf⟩ := DR_up (taint := taint) hem hRF hf
    obtain ⟨g', hg', hg'f⟩ := DRT_flag_swap hem hRF hg mi hi
    exact ⟨g', hg', by rw [hg'f, hgf]; exact hd,
      RCov.flowR_mono (fun _ _ h => (summaryDemandT_iff hem hRF _ _).mpr h) hfr⟩
  · exact absurd hr (RExact.DR_no_request hem _ _ _)

/-- COVERAGE OF THE RESTRICTED FORWARD RUN WITH MUST-PREMISES (from `RCov.coverageR` through the
    fact simulation): a demanded flow from an entry location that an initial fact `(i, mi)` of
    `DRT` covers is covered by an edge of `(i, mi)` (in some layer), and it is demanded by the
    summaries of `DRT`. `DRT` has no request. Hypotheses: those of `RCov.coverageR` (S10
    `Program.WF`, the emission contract for concrete added facts, `SatContract`,
    `RestrictContract`), `EmitCopiesMark emit` and `RestrictFact restrict`. -/
theorem coverageRT (hwf : P.WF) (hE : EmitContractConc emit sat) (hem : EmitCopiesMark emit)
    (hS : SatContract sat) (hR : RestrictContract restrict) (hRF : RestrictFact restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i mi, DRTr (.init M i mi) → i.covers l0 →
      ∃ f, DRTr (.edge M i mi n f) ∧ den i f.fact l0 l ∧
        FlowR P (summaryDemand P (forgetRun DRTr)) M l0 n l := by
  intro i mi hi hc
  have hi0 : DRr (.init M i) := DRT_down hem hRF hi
  exact cov_transfer P taint counted L demand emit sat restrict recs sinks roots hem hRF hi
    (RCov.coverageR P counted L demand emit sat restrict (recsDR recs) sinks roots hwf
      (RCov.emitOn_of_conc P counted L demand emit sat restrict (recsDR recs) sinks roots hE hem)
      hS hR hfl i hi0 hc)

#print axioms coverageRT

/-- THE VULNERABILITY THEOREM OF THE RESTRICTED FORWARD RUN WITH MUST-PREMISES (from
    `RCov.vuln_foundR`): a demanded real source-to-sink witness is reported by `DRT` (in some
    layer), and the summaries of `DRT` demand the witness again. Hypotheses: as `coverageRT`. -/
theorem vuln_foundRT (hwf : P.WF) (hE : EmitContractConc emit sat) (hem : EmitCopiesMark emit)
    (hS : SatContract sat) (hR : RestrictContract restrict) (hRF : RestrictFact restrict)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DRTr (.vuln M n s b)) ∧ ReachR P (summaryDemand P (forgetRun DRTr)) roots M n l := by
  obtain ⟨hv, hRR⟩ := RCov.vuln_foundR P counted L demand emit sat restrict (recsDR recs) sinks
    roots hwf (RCov.emitOn_of_conc P counted L demand emit sat restrict (recsDR recs) sinks roots
      hE hem) hS hR hRe hs hT hsc
  exact ⟨(vulnT_iff hem hRF M n s).mpr hv,
    RCov.reachR_mono (fun _ _ h => (summaryDemandT_iff hem hRF _ _).mpr h) hRR⟩

#print axioms vuln_foundRT

end SoundRT

section SoundRTM
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- COVERAGE OF `DRT` WITH THE SPEC RULES (`emitM`, `satI`, `restrictU`): as `coverageRT`, with the
    only hypothesis S10 (`Program.WF`). (`restrictU` has no `RestrictContract`; the closure with it
    is the closure with `restrictS`, `RMain.runU_eq_S`.) -/
theorem coverageRT_M (hwf : P.WF) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hfl : FlowR P demand M l0 n l) :
    ∀ i mi, DRT P taint counted L demand emitM satI restrictU recs sinks roots (.init M i mi) →
      i.covers l0 →
      ∃ f, DRT P taint counted L demand emitM satI restrictU recs sinks roots (.edge M i mi n f) ∧
        den i f.fact l0 l ∧
        FlowR P (summaryDemand P
          (forgetRun (DRT P taint counted L demand emitM satI restrictU recs sinks roots))) M l0 n l := by
  intro i mi hi hc
  have hi0 : DR P counted L demand emitM satI restrictU (recsDR recs) sinks roots (.init M i) :=
    DRT_down RExact.emitM_copies restrictU_fact hi
  have hcov := RCov.coverageR P counted L demand emitM satI restrictS (recsDR recs) sinks roots hwf
    (RCov.emitOn_of_conc P counted L demand emitM satI restrictS (recsDR recs) sinks roots
      RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract hfl i (by rw [← RMain.runU_eq_S]; exact hi0) hc
  rw [← RMain.runU_eq_S] at hcov
  exact cov_transfer P taint counted L demand emitM satI restrictU recs sinks roots
    RExact.emitM_copies restrictU_fact hi hcov

#print axioms coverageRT_M

/-- THE VULNERABILITY THEOREM OF `DRT` WITH THE SPEC RULES (from `RMain.vuln_found_M`): a demanded
    real witness is reported by `DRT` (in some layer), and the summaries of `DRT` demand it again.
    The only hypothesis is S10 (`Program.WF`). -/
theorem vuln_foundRT_M (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DRT P taint counted L demand emitM satI restrictU recs sinks roots (.vuln M n s b)) ∧
    ReachR P (summaryDemand P
      (forgetRun (DRT P taint counted L demand emitM satI restrictU recs sinks roots))) roots M n l := by
  obtain ⟨hv, hRR⟩ := RMain.vuln_found_M (counted := counted) (L := L) (recs := recsDR recs) hwf
    hRe hs hT hsc
  exact ⟨(vulnT_iff RExact.emitM_copies restrictU_fact M n s).mpr hv,
    RCov.reachR_mono (fun _ _ h =>
      (summaryDemandT_iff RExact.emitM_copies restrictU_fact _ _).mpr h) hRR⟩

#print axioms vuln_foundRT_M

end SoundRTM

/-! ### The hand-off of run 1 -/

/-- THE BACKWARD RUN READS THE SAME PATTERNS FROM RUN 1 WITH W6T AS FROM `D`: the reversed summary
    demand of `D6T` is that of `D` (`W6.revSummaryDemand_iff` through the simulation). Hypothesis:
    `W6.SummaryStar` (the policy has it). -/
theorem revSummaryDemand6T_iff {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hS : W6.SummaryStar P (D P counted L α sinks roots)) (m : MethodId) (d : DemandEdge) :
    Backward.revSummaryDemand P (D P counted L α sinks roots) m d ↔
      Backward.revSummaryDemand P (D6T P taint counted L α sinks roots) m d :=
  W6.revSummaryDemand_iff (fun _ h => D_le_D6T P taint counted L α sinks roots hS h)
    (fun _ h => D6T_le_D P taint counted L α sinks roots hS h) m d

#print axioms revSummaryDemand6T_iff

/-! ## 4. The iteration -/

/-- The run sequence with `[any-taint]`: run 0 (the spec's run 1) is `D6T` with `policy1`; run
    `k + 1` is the restricted forward run with must-premises `DRT` with the demand `dem k` and the
    records `recs k`, seen without its must flags (`forgetRun`; the backward run and the reports
    read it so). -/
def runSeqT (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × Bool × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D6T P taint counted (Ls 0) policy1 sinks roots
  | k + 1 => forgetRun (DRT P taint counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots)

/-- A vulnerability of a forgotten run is a vulnerability of the run. -/
theorem forgetRun_vuln {R : TObj → Prop} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : forgetRun R (.vuln M n s b)) : R (.vuln M n s b) := by
  obtain ⟨oT, hT, he⟩ := h
  cases oT with
  | vuln M' n' s' d => cases he; exact hT
  | init => cases he
  | edge => cases he
  | added => cases he
  | req => cases he

section IterT
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- Run `k` of the base sequence (`RCov.runSeq`, records `recsDR (recs k)`) is simulated by run `k`
    of the `[any-taint]` sequence (the same facts). -/
theorem runSeqT_up (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) (k : Nat) :
    ∀ o, RCov.runSeq P counted Ls dem emit sat restrict (fun k => recsDR (recs k)) sinks roots k o →
      FUp (runSeqT P taint counted Ls dem emit sat restrict recs sinks roots k) o := by
  intro o h
  cases k with
  | zero => exact FUp_of_Up (D_le_D6T_1 h)
  | succ k => exact DRT_FUp hem hRF o h

/-- Run `k` of the `[any-taint]` sequence is simulated by run `k` of the base sequence. -/
theorem runSeqT_down (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) (k : Nat) :
    ∀ o, runSeqT P taint counted Ls dem emit sat restrict recs sinks roots k o →
      FUp (RCov.runSeq P counted Ls dem emit sat restrict (fun k => recsDR (recs k)) sinks roots k) o := by
  intro o h
  cases k with
  | zero => exact FUp_of_Down (D6T_le_D_1 h)
  | succ k => exact DR_FUp hem hRF o h

#print axioms runSeqT_up
#print axioms runSeqT_down

/-- The backward run reads the same demand from run `k` of both sequences. -/
theorem revSummaryDemand_runSeqT (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict)
    (k : Nat) (m : MethodId) (d : DemandEdge) :
    Backward.revSummaryDemand P (runSeqT P taint counted Ls dem emit sat restrict recs sinks roots k) m d ↔
      Backward.revSummaryDemand P
        (RCov.runSeq P counted Ls dem emit sat restrict (fun k => recsDR (recs k)) sinks roots k) m d :=
  ⟨revSummaryDemand_of_FUp (runSeqT_down hem hRF k), revSummaryDemand_of_FUp (runSeqT_up hem hRF k)⟩

#print axioms revSummaryDemand_runSeqT

end IterT

/-- THE GENERAL ITERATION THEOREM WITH `[any-taint]` (from `Backward.iteration_general` through
    the simulations): every forward run of the sequence (run 1 = `D6T`, the backward runs =
    `Backward.DB` of the user's design, the forward restricted runs = `DRT`) reports every real
    vulnerability, in some layer. Hypotheses: those of `Backward.iteration_general`: on the
    program S10 (`Program.WF`), mark-agnostic binding targets (`BindTargetsStar`, S11 (a)),
    mark-reversible statements (`StmtsMarkRev`), no zero binding back (`NoZeroBack`), the zero
    kept by every instruction (`ZeroKept`), every node reaches its exit (`ExitReach`); the sinks
    have the tail `$` or `[any]`; the backward demand contains the reversed summaries of the
    previous forward run, the seeds contain the sinks it reported, and the demand of each
    forward run contains the hand-off of the backward run before it (any backward field limit and
    record set; any forward records `recs`). No hypothesis on the taint edges. -/
theorem iteration_generalT {P : Program} (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    {roots : List MethodId} (hX : Backward.ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) := by
  have up := runSeqT_up (P := P) (taint := taint) (counted := counted) (Ls := Ls) (dem := dem)
    (sat := satI) (recs := recs) (sinks := sinks) (roots := roots) RExact.emitM_copies restrictU_fact
  have h := Backward.iteration_general (counted := counted) (Ls := Ls) (dem := dem)
    (recs := fun k => recsDR (recs k)) hW hT hmr hNZB hZ hX hk LB demB recsB seeds
    (fun k m d hd => hdemB k m d (revSummaryDemand_of_FUp (up k) hd))
    (fun k M' n' s' b hv => by
      obtain ⟨b', hb'⟩ := up k _ hv
      exact hseeds k M' n' s' b' hb')
    hdem hRe hs hT' hsc
  intro k
  obtain ⟨b, hb⟩ := h k
  exact up k _ hb

#print axioms iteration_generalT

/-- EVERY COMPLETE FORWARD RUN REPORTS EVERY REAL VULNERABILITY, IN SOME LAYER (the form to cite;
    `iteration_generalT` with the runs named): run 1 `D6T` reports it, and every forward
    restricted run `DRT` (`k + 1`) reports it. Hypotheses: those of `iteration_generalT`. -/
theorem iteration_reportsT {P : Program} (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    {roots : List MethodId} (hX : Backward.ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqT P taint counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6T P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, DRT P taint counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks roots
      (.vuln M n s b) := by
  have h := iteration_generalT hW hT hmr hNZB hZ hX hk LB demB recsB seeds hdemB hseeds hdem
    hRe hs hT' hsc
  refine ⟨h 0, fun k => ?_⟩
  obtain ⟨b, hb⟩ := h (k + 1)
  exact ⟨b, forgetRun_vuln hb⟩

#print axioms iteration_reportsT

/-! ### The iteration with forward seeds -/

/-- The run sequence with forward seeds and `[any-taint]`: run 0 is `D6T` of the full program;
    run `k + 1` is `DRT` of `FSeeds.keepSources P (σ k)` (only the seeded unconditional sources
    fire), seen without its must flags. -/
def runSeqSrcT (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × Bool × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D6T P taint counted (Ls 0) policy1 sinks roots
  | k + 1 => forgetRun (DRT (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emit sat
      restrict (recs k) sinks roots)

theorem runSeqSrcT_up {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    {σ : Nat → MethodId → Node → MicroEdge → Bool}
    {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hem : EmitCopiesMark emit) (hRF : RestrictFact restrict) (k : Nat) :
    ∀ o, FSeeds.runSeqSrc P counted Ls σ dem emit sat restrict (fun k => recsDR (recs k)) sinks
        roots k o →
      FUp (runSeqSrcT P taint counted Ls σ dem emit sat restrict recs sinks roots k) o := by
  intro o h
  cases k with
  | zero => exact FUp_of_Up (D_le_D6T_1 h)
  | succ k => exact DRT_FUp hem hRF o h

#print axioms runSeqSrcT_up

/-- THE ITERATION THEOREM WITH FORWARD SEEDS AND `[any-taint]` (from `FSeeds.iteration_src`
    through the simulations): run 1 (`D6T`) analyses the full program; forward run `k + 1`
    (`DRT`) fires only the unconditional sources in `σ k`, which contains the source hits of the
    backward run after forward run `k`. Every forward run reports every real vulnerability of `P`,
    in some layer. Hypotheses: those of `FSeeds.iteration_src`. -/
theorem iteration_srcT {P : Program} (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    {roots : List MethodId} (hX : Backward.ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × Bool × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand (FSeeds.progSrc P σ k)
      (runSeqSrcT P taint counted Ls σ dem emitM satI restrictU recs sinks roots k) m d →
      demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqSrcT P taint counted Ls σ dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (Backward.DB (Reverse.Program.rev P) counted (LB k) (demB k)
      emitM satI restrictU (recsB k) [] roots (seeds k) true) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6T P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, DRT (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) emitM satI
      restrictU (recs k) sinks roots (.vuln M n s b) := by
  have up := runSeqSrcT_up (P := P) (taint := taint) (counted := counted) (Ls := Ls) (σ := σ)
    (dem := dem) (sat := satI) (recs := recs) (sinks := sinks) (roots := roots)
    RExact.emitM_copies restrictU_fact
  have h := FSeeds.iteration_src (counted := counted) (Ls := Ls) (dem := dem)
    (recs := fun k => recsDR (recs k)) hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds
    (fun k m d hd => hdemB k m d (revSummaryDemand_of_FUp (up k) hd))
    (fun k M' n' s' b hv => by
      obtain ⟨b', hb'⟩ := up k _ hv
      exact hseeds k M' n' s' b' hb')
    hdem hσ hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h 0
    exact up 0 _ hb
  · obtain ⟨b, hb⟩ := h (k + 1)
    obtain ⟨b', hb'⟩ := up (k + 1) _ hb
    exact ⟨b', forgetRun_vuln hb'⟩

#print axioms iteration_srcT

/-! ## 5. The backward run: no new closure

  `Backward.DB` is the backward run of the spec with `[any-taint]` (DESIGN §3.1): the spec's
  backward `[any-taint]` is an `.any` fact in the NORMAL layer (the seed of an `[any]` sink
  pattern, `seed_any_normal`), and its `[any]` is an `.any` fact in the demand layer. A premise
  with the `.any` tail starts in the demand layer (`startFact_any_demand`), so every edge of an
  `[any-taint]` backward premise is a demand edge (`DB_any_premise_demand`): decision 7 for the
  premise side. Decision 7 for the conclusion side is a filter on the records (`backRecT`). -/

/-- An `[any]` premise starts in the demand layer (the start fact of `Basic.lean`). -/
theorem startFact_any_demand {j : PFact} (h : j.kind = .any) : (startFact j).demand = true := by
  obtain ⟨b, p, k, m⟩ := j
  have hk : k = .any := h
  subst hk
  cases m <;> rfl

#print axioms startFact_any_demand

section BackRun
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)}
  {zbind : Bool}

/-- THE BACKWARD `[any-taint]` SEED: the seed of a sink pattern whose path is within the backward
    field limit is a NORMAL edge of `DB` with the pattern itself. For an `[any]` sink pattern this
    is the spec's backward `[any-taint]` requirement (decision 4: a `ContainsMarkOnAnyField` check
    emits `[any-taint]`). -/
theorem seed_any_normal {M : MethodId} {n : Node} {s : PFact} (hs : (M, n, s) ∈ seeds)
    (hz : Backward.DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M zeroFact n Backward.zeroAF))
    (hcut : cutPath counted L s.path = none) :
    Backward.DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M zeroFact n ⟨s, false⟩) := by
  have h := Backward.DB.seed hs hz
  have e : limitF counted L ⟨s, false⟩ = ⟨s, false⟩ := by
    show (match cutPath counted L s.path with
      | none => (⟨s, false⟩ : AFact)
      | some p => ⟨⟨s.base, p, .any, s.mark⟩, true⟩) = ⟨s, false⟩
    rw [hcut]
  rw [e] at h
  exact h

#print axioms seed_any_normal

/-- DECISION 7, THE PREMISE SIDE: with a mark-copying emission and concrete seeds, every backward
    edge whose premise has the `[any]` tail (a backward `[any-taint]` must-premise or an `[any]`
    premise) is a DEMAND edge, so it is never complete, never persisted, never reversed (from
    `BExact.DB_premise_exact`). -/
theorem DB_any_premise_demand (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    {M : MethodId} {jb : PFact} {n : Node} {gb : AFact}
    (h : Backward.DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind
      (.edge M jb n gb)) (hk : jb.kind = .any) : gb.demand = true := by
  cases hd : gb.demand with
  | true => rfl
  | false =>
    have he := BExact.DB_premise_exact hem hsd h hd
    rw [hk] at he
    cases he

#print axioms DB_any_premise_demand

end BackRun

/-- THE BACKWARD RECORDS OF THE SPEC (decision 7): a NORMAL backward summary (an edge of the
    backward run at its exit, the forward entry) with a non-zero premise and NO `[any]` tail on
    its premise or on its conclusion (so no `[any-taint]` tail), reversed (`revEdge`) into a
    forward record. -/
def backRecT (P : Program) (RB : Obj → Prop) (m : MethodId) (jg : PFact × AFact) : Prop :=
  ∃ jb gb, RB (.edge m jb ((Reverse.Program.rev P).exit m) gb) ∧ jb ≠ zeroFact ∧
    gb.demand = false ∧ jb.kind.isAny = false ∧ gb.fact.kind.isAny = false ∧
    jg = ((revEdge jb gb.fact).1, ⟨(revEdge jb gb.fact).2, false⟩)

/-- The backward records of the spec are reversed normal backward summaries with a non-zero
    premise (`BExact.revRecs`): the normal backward edges that `BExact.edge_exactB` proves exact. -/
theorem backRecT_sub {P : Program} {RB : Obj → Prop} {m : MethodId} {jg : PFact × AFact}
    (h : backRecT P RB m jg) : BExact.revRecs P RB m jg := by
  obtain ⟨jb, gb, h1, h2, h3, _, _, h6⟩ := h
  exact ⟨jb, gb, h1, h2, h3, h6⟩

#print axioms backRecT_sub

/-- THE BACKWARD RECORDS OF THE SPEC ARE EXACT FORWARD RECORDS (`RExact.RecsExact P`; from
    `BExact.revRecs_exact`, which uses `BExact.rev_record_exact`): a forward run can persist and
    reuse them. Hypotheses: those of `BExact.revRecs_exact` (a mark-copying emission, concrete
    seeds, S7 `MarkWF`, `FiltUp`, `NoZeroBack`, `RevStmts`, `RevCalls`, `SatMark`, `RestrictSub`,
    the backward records exact off the zero base). -/
theorem backRec_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : Backward.NoZeroBack P)
    (hR : Reverse.RevStmts P) (hC : Reverse.RevCalls P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : BExact.RecsExactNZ (Reverse.Program.rev P) recs) :
    RExact.RecsExact P (backRecT P
      (Backward.DB (Reverse.Program.rev P) counted L demand emit sat restrict recs sinks roots seeds
        zbind)) :=
  RExact.recs_mono (fun _ _ h => backRecT_sub h)
    (BExact.revRecs_exact hem hsd hmw hup hNZB hR hC hsat hsub hrecs)

#print axioms backRec_exact

/-- The same for the spec rules (`emitM`, `satI`, `restrictU`) with concrete seeds. -/
theorem backRec_exactM {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : BExact.SeedsConc seeds) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hNZB : Backward.NoZeroBack P) (hR : Reverse.RevStmts P) (hC : Reverse.RevCalls P)
    (hrecs : BExact.RecsExactNZ (Reverse.Program.rev P) recs) :
    RExact.RecsExact P (backRecT P
      (Backward.DB (Reverse.Program.rev P) counted L demand emitM satI restrictU recs sinks roots
        seeds zbind)) :=
  RExact.recs_mono (fun _ _ h => backRecT_sub h)
    (BExact.revRecs_exactM hsd hmw hup hNZB hR hC hrecs)

#print axioms backRec_exactM

/-- A spec backward record is a correct reversed record: its pairs are real forward flows from the
    forward entry to the forward exit (`BExact.rev_record_exact`). Hypotheses: as
    `backRec_exact`. -/
theorem backRec_flow {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : Backward.NoZeroBack P)
    (hR : Reverse.RevStmts P) (hC : Reverse.RevCalls P)
    (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : BExact.RecsExactNZ (Reverse.Program.rev P) recs)
    {m : MethodId} {j : PFact} {g : AFact}
    (h : backRecT P (Backward.DB (Reverse.Program.rev P) counted L demand emit sat restrict recs
      sinks roots seeds zbind) m (j, g)) {l1 l2 : Loc} (hd : den j g.fact l1 l2) :
    Flow P m l1 (P.exit m) l2 := by
  have hg : g.demand = false := by
    obtain ⟨_, _, _, _, _, _, _, he⟩ := h
    rw [(Prod.mk.inj he).2]
  exact backRec_exact hem hsd hmw hup hNZB hR hC hsat hsub hrecs m j g h hg l1 l2 hd

#print axioms backRec_flow

/-- The records without must flags (`liftRecs`) read back by `DR` are the records themselves: a
    forward restricted run `DRT` that reuses records `recs` without must flags (for example the
    backward records `backRecT`) has the facts of `DR` with `recs`. -/
theorem recsDR_liftRecs (recs : MethodId → PFact × AFact → Prop) :
    recsDR (liftRecs recs) = recs := by
  funext m jg
  apply propext
  constructor
  · rintro ⟨mj, _, h⟩
    exact h
  · intro h
    exact ⟨false, rfl, h⟩

#print axioms recsDR_liftRecs


end ApSpec.AnyTaintSim
