/-
  ApSpec.Coverage — the global soundness theorems of the analysis closure `D`.

  Contents:
    * the mark invariants of `D` (`edge_conc`, `req_initial_star`);
    * the coverage theorem (forward soundness): if the initial fact covers the
      entry location and the data flow exists, then an edge covers the pair, or
      the analysis raises the mark request on the initial fact;
    * the vulnerability theorem: a concrete source-to-sink flow through a chain
      of calls gives a `vuln` object;
    * each forward run is sound: the theorems hold for the closure with the
      abstraction `policy demand`, for every `demand`.

  The local lemmas come from `ApSpec.Core`.
-/
import ApSpec.Core

namespace ApSpec.Coverage
open ApSpec

/-! ## 0. Small facts about marks and denotations -/

/-- A mark is abstract or concrete. -/
theorem mark_cases (m : MarkA) : m = .star ∨ ∃ t, m = .conc t := by
  cases m with
  | star => exact .inl rfl
  | conc t => exact .inr ⟨t, rfl⟩

/-- An abstract final mark passes the entry mark through. -/
theorem den_mark_star {i a : PFact} {l0 l1 : Loc} (hd : den i a l0 l1)
    (h : a.mark = .star) : l1.mark = l0.mark := by
  have hm := hd.2.2.2.1
  rw [h] at hm
  exact hm

/-- A concrete final mark is the mark of the end location. -/
theorem den_mark_conc {i a : PFact} {l0 l1 : Loc} {t : Mark} (hd : den i a l0 l1)
    (h : a.mark = .conc t) : a.mark = .conc l1.mark := by
  have hm : l1.mark = t := by
    have hm0 := hd.2.2.2.1
    rw [h] at hm0
    exact hm0
  rw [h, hm]

theorem applySummary_reqs {a g : AFact} {j : PFact} :
    (applySummary a j g).reqs = (applyEdge a j g.fact).reqs := rfl

/-- The zero fact covers the zero location. -/
theorem zeroFact_covers : zeroFact.covers zeroLoc := by
  unfold PFact.covers
  exact ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

/-! ## 1. Call bindings and summaries (local steps of a call) -/

/-- The binding into the callee raises no request (WF: it is mark agnostic). -/
theorem bind_in {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he1 : e ∈ c.toCallee)
    {i : PFact} {f : AFact} {l0 l l1 : Loc}
    (hd : den i f.fact l0 l) (hd1 : den e.1 e.2 l l1) :
    ∃ a, a ∈ (applyEdge f e.1 e.2).facts ∧ den i a.fact l0 l1 := by
  rcases applyEdge_sound hd hd1 with h | ⟨_, hq⟩
  · exact h
  · rw [applyEdge_reqs_of_star (hwf.toStar M n c n' he e he1)] at hq
    cases hq

/-- The binding back from the callee raises no request (WF: it is mark agnostic). -/
theorem bind_out {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he2 : e ∈ c.fromCallee)
    {i : PFact} {r : AFact} {l0 l l1 : Loc}
    (hd : den i r.fact l0 l) (hd2 : den e.1 e.2 l l1) :
    ∃ r', r' ∈ (applyEdge r e.1 e.2).facts ∧ den i r'.fact l0 l1 := by
  rcases applyEdge_sound hd hd2 with h | ⟨_, hq⟩
  · exact h
  · rw [applyEdge_reqs_of_star (hwf.fromStar M n c n' he e he2)] at hq
    cases hq

/-- An applicable summary raises no request: a concrete premise mark forces the
    same concrete mark on the added fact. -/
theorem summary_step {i j : PFact} {a g : AFact} {l0 l1 l2 : Loc}
    (hap : applicable j a.fact = true) (hda : den i a.fact l0 l1) (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    rcases mark_cases j.mark with hj | ⟨t, hj⟩
    · rw [applySummary_reqs, applyEdge_reqs_of_star hj] at hq
      cases hq
    · have hm := applicable_mark hap hj
      rw [hst] at hm
      cases hm

/-! ## 2. Mark invariants of `D` -/

/-- The edge invariant: a concrete-mark initial fact has concrete-mark final facts. -/
def EdgeInv : Obj → Prop
  | .edge _ i _ f => ∀ t, i.mark = .conc t → ∃ t', f.fact.mark = .conc t'
  | _ => True

/-- The request invariant: a request is on a mark-abstract initial fact. -/
def ReqInv : Obj → Prop
  | .req _ i _ => i.mark = .star
  | _ => True

section Closure
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

theorem edgeInv_all {o : Obj} (h : D P counted L α sinks roots o) : EdgeInv o := by
  induction h with
  | start _ =>
    intro t ht
    exact ⟨t, by rw [startFact_mark]; exact ht⟩
  | step _ _ hf' ih =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    exact transfer_mark_conc h1 hf'
  | pass _ _ _ ih => exact ih
  | ret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    intro t ht
    obtain ⟨t1, h1⟩ := ih t ht
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
    obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
    exact ⟨t4, by rw [limitF_mark]; exact h4⟩
  | root _ => trivial
  | reqStmt _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial

/-- Invariant (b): an edge of a concrete-mark initial fact has a concrete-mark final fact. -/
theorem edge_conc {M : MethodId} {i : PFact} {n : Node} {f : AFact} {t : Mark}
    (h : D P counted L α sinks roots (.edge M i n f)) (ht : i.mark = .conc t) :
    ∃ t', f.fact.mark = .conc t' :=
  edgeInv_all P counted L α sinks roots h t ht

#print axioms edge_conc

theorem reqInv_all {o : Obj} (h : D P counted L α sinks roots o) : ReqInv o := by
  induction h with
  | @reqStmt _ i _ _ _ _ _ hf _ hq _ =>
    rcases mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_conc P counted L α sinks roots hf hm
      rw [transfer_reqs_of_conc h1] at hq
      cases hq
  | reqSink _ _ hc _ => exact check_request_star hc
  | @reqUp _ _ _ _ ic _ _ _ _ _ _ _ hf _ _ _ ha ham _ _ _ =>
    rcases mark_cases ic.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_conc P counted L α sinks roots hf hm
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      rw [ham] at h2
      cases h2
  | root _ => trivial
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial

/-- Invariant (a): every request is on a mark-abstract initial fact. -/
theorem req_initial_star {M : MethodId} {i : PFact} {t : Mark}
    (h : D P counted L α sinks roots (.req M i t)) : i.mark = .star :=
  reqInv_all P counted L α sinks roots h

#print axioms req_initial_star

/-! ## 3. The return step of a call -/

/-- A covered callee pair, applied as a summary and bound back, gives a caller edge.
    The caller subscribes to every applicable initial fact `j` of the callee. -/
theorem ret_step (hwf : P.WF) {M : MethodId} {i : PFact} {n n' : Node} {f : AFact}
    {c : Call} {e1 e2 : MicroEdge} {a g : AFact} {j : PFact} {l0 l1 l2 l3 : Loc}
    (hf : D P counted L α sinks roots (.edge M i n f))
    (he : (M, n, Instr.call c, n') ∈ P.edges)
    (he1 : e1 ∈ c.toCallee) (ha : a ∈ (applyEdge f e1.1 e1.2).facts)
    (hda : den i a.fact l0 l1)
    (hj : D P counted L α sinks roots (.init c.callee j))
    (hap : applicable j a.fact = true)
    (hg : D P counted L α sinks roots (.edge c.callee j (P.exit c.callee) g))
    (hdg : den j g.fact l1 l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    ∃ f', D P counted L α sinks roots (.edge M i n' f') ∧ den i f'.fact l0 l3 := by
  obtain ⟨r, hr, hdr⟩ := summary_step hap hda hdg
  obtain ⟨r', hr', hdr'⟩ := bind_out hwf he he2 hdr hd2
  exact ⟨_, D.ret hf he he1 ha hj hap hg hr he2 hr', limitF_sound hdr'⟩

/-! ## 4. The coverage theorem -/

/-- THE COVERAGE THEOREM (forward soundness). If the initial fact `i` of `M`
    is in `D` and covers the entry location `l0`, and the value at `l0` flows
    to `l` at node `n`, then an edge of `i` at `n` covers the pair, or `D`
    has the request for the entry mark on `i`. -/
theorem coverage (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, D P counted L α sinks roots (.init M i) → i.covers l0 →
      (∃ f, D P counted L α sinks roots (.edge M i n f) ∧ den i f.fact l0 l) ∨
      D P counted L α sinks roots (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, D.start hi, startFact_sound hc⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr
    · rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D.step hf he hr, hdr⟩
      · exact .inr (D.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, D.pass hf he hb, hd⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd⟩ | hr
    · -- The caller fact reaches the call. Bind it into the callee.
      obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
      have hadd := D.added hf he he1 ha
      have hac : a.fact.covers l1 := den_covers_final hda
      have hapj := hα c.callee a.fact
      have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
      have hov : overlapB a.fact (α c.callee a.fact) = true := overlapB_of_common hac hjc
      rcases ihc _ (D.initA hadd) hjc with ⟨g, hg, hdg⟩ | hreq
      · -- The callee summary covers the pair.
        exact .inl (ret_step P counted L α sinks roots hwf hf he he1 ha hda (D.initA hadd)
          hapj hg hdg he2 hd2)
      · -- The callee raises the request on its initial fact.
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- The added fact is mark-abstract: the request climbs to the caller.
          have hup := D.reqUp hreq hf he rfl he1 ha ham hov
          rw [den_mark_star hda ham] at hup
          exact .inr hup
        · -- The added fact is concrete: it answers the request.
          have hmk := den_mark_conc hda ham
          have hans := D.answer hreq hadd hmk hov
          have hap' := answerInit_applicable hapj hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg⟩ | hreq'
          · exact .inl (ret_step P counted L α sinks roots hwf hf he he1 ha hda
              hans hap' hg hdg he2 hd2)
          · exfalso
            have hst := req_initial_star P counted L α sinks roots hreq'
            rw [answerInit_mark] at hst
            cases hst
    · exact .inr hr

#print axioms coverage

/-- Coverage for a concrete-mark initial fact: it has no request, so an edge covers the pair. -/
theorem coverage_conc (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l)
    {i : PFact} {t : Mark}
    (hi : D P counted L α sinks roots (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, D P counted L α sinks roots (.edge M i n f) ∧ den i f.fact l0 l := by
  rcases coverage P counted L α sinks roots hwf hα hfl i hi hc with h | hr
  · exact h
  · exfalso
    have hst := req_initial_star P counted L α sinks roots hr
    rw [ht] at hst
    cases hst

#print axioms coverage_conc

/-- Coverage at a root: the zero fact covers every flow from the zero location. -/
theorem coverage_root (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hM : M ∈ roots) (hfl : Flow P M zeroLoc n l) :
    ∃ f, D P counted L α sinks roots (.edge M zeroFact n f) ∧ den zeroFact f.fact zeroLoc l :=
  coverage_conc P counted L α sinks roots hwf hα hfl (t := zeroMark) (D.root hM)
    zeroFact_covers rfl

#print axioms coverage_root

/-! ## 5. The vulnerability theorem -/

/-- The strengthened reach statement. An edge covers the pair at `(M, n, l)`. Its
    initial fact has a concrete mark, or it is mark-abstract and a request for
    the entry mark on it gives a concrete-mark edge that covers the same pair. -/
theorem reach_strong (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hR : Reach P roots M n l) :
    ∃ l0 i f, D P counted L α sinks roots (.edge M i n f) ∧ den i f.fact l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       (i.mark = .star ∧ (D P counted L α sinks roots (.req M i l0.mark) →
          ∃ i' f', D P counted L α sinks roots (.edge M i' n f') ∧ den i' f'.fact l0 l ∧
            ∃ t, i'.mark = .conc t))) := by
  induction hR with
  | root hM hfl =>
    obtain ⟨f, hf, hd⟩ := coverage_root P counted L α sinks roots hwf hα hM hfl
    exact ⟨zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨l0, i, f, hf, hd, hdisj⟩ := ih
    -- Bind the caller fact into the callee.
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := D.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    have hapj := hα c.callee a.fact
    have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
    -- A request on the callee initial fact gets a concrete-mark answer that covers `l1`.
    have key : D P counted L α sinks roots (.req c.callee (α c.callee a.fact) l1.mark) →
        ∃ j', D P counted L α sinks roots (.init c.callee j') ∧ j'.covers l1 ∧
          ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', D P counted L α sinks roots (.added c.callee a') ∧ a'.covers l1 ∧
          a'.mark = .conc l1.mark := by
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · -- The request climbs to the caller. The caller IH gives a concrete-mark
          -- caller edge, and its binding is a concrete added fact.
          have hup := D.reqUp hreq hf he rfl he1 ha ham (overlapB_of_common hac hjc)
          rw [den_mark_star hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exfalso
            have hst := req_initial_star P counted L α sinks roots hup
            rw [ht] at hst
            cases hst
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_conc P counted L α sinks roots hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, D.added hf' he he1 ha', den_covers_final hda', den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := D.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    rcases coverage P counted L α sinks roots hwf hα hfc _ (D.initA hadd) hjc with
      ⟨g, hg, hdg⟩ | hreq
    · refine ⟨l1, _, g, hg, hdg, ?_⟩
      rcases mark_cases (α c.callee a.fact).mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg'⟩ :=
          coverage_conc P counted L α sinks roots hwf hα hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg'⟩ := coverage_conc P counted L α sinks roots hwf hα hfc hj' hjc' ht
      exact ⟨l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strong

/-- THE VULNERABILITY THEOREM. A concrete flow from the zero location of a root,
    through a chain of calls, to a location `l` at a sink node with a covering
    sink pattern gives a `vuln` object. -/
theorem vuln_found (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D P counted L α sinks roots (.vuln M n s b) := by
  obtain ⟨l0, i, f, hf, hd, hdisj⟩ := reach_strong P counted L α sinks roots hwf hα hR
  rcases check_sound hT hd hsc with htr | ⟨hrq, hist⟩
  · exact ⟨_, D.vuln hf hs htr⟩
  · have hreq := D.reqSink hf hs hrq
    rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
    · exfalso
      rw [ht] at hist
      cases hist
    · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hreq
      rcases check_sound hT hd' hsc with htr' | ⟨_, hist'⟩
      · exact ⟨_, D.vuln hf' hs htr'⟩
      · exfalso
        rw [ht] at hist'
        cases hist'

#print axioms vuln_found

/-! ## 6. Each forward run is sound

A run is the closure `D` with its own abstraction `policy demand`. The policy
satisfies (A1) for every `demand` (`policy_applicable`), so the theorems above
hold for every run. -/

/-- Coverage for one run: the closure with the abstraction `policy demand`. -/
theorem coverage_policy (hwf : P.WF) (demand : MethodId → List PFact)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, D P counted L (policy demand) sinks roots (.init M i) → i.covers l0 →
      (∃ f, D P counted L (policy demand) sinks roots (.edge M i n f) ∧ den i f.fact l0 l) ∨
      D P counted L (policy demand) sinks roots (.req M i l0.mark) :=
  coverage P counted L (policy demand) sinks roots hwf (policy_applicable demand) hfl

#print axioms coverage_policy

/-- The vulnerability theorem for one run: the run reports every concrete
    source-to-sink flow, for every `demand`. -/
theorem vuln_found_policy (hwf : P.WF) (demand : MethodId → List PFact)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D P counted L (policy demand) sinks roots (.vuln M n s b) :=
  vuln_found P counted L (policy demand) sinks roots hwf (policy_applicable demand) hR hs hT hsc

#print axioms vuln_found_policy

/-- Two runs with different demands both report a concrete vulnerability. So the
    intersection of the reported sets of the two runs is sound. -/
theorem vuln_sound_each_run (hwf : P.WF) (demand1 demand2 : MethodId → List PFact)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D P counted L (policy demand1) sinks roots (.vuln M n s b)) ∧
    (∃ b, D P counted L (policy demand2) sinks roots (.vuln M n s b)) :=
  ⟨vuln_found_policy P counted L sinks roots hwf demand1 hR hs hT hsc,
   vuln_found_policy P counted L sinks roots hwf demand2 hR hs hT hsc⟩

#print axioms vuln_sound_each_run

/-- The same for any list of runs: every run in the list reports the vulnerability. -/
theorem vuln_sound_all_runs (hwf : P.WF) (runs : List (MethodId → List PFact))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ demand, demand ∈ runs → ∃ b, D P counted L (policy demand) sinks roots (.vuln M n s b) :=
  fun demand _ => vuln_found_policy P counted L sinks roots hwf demand hR hs hT hsc

#print axioms vuln_sound_all_runs

end Closure

/-- Two runs with different demands AND different field limits both report every
    concrete vulnerability. So stopping at any run is sound, and the intersection of
    the reports of several runs is sound too. -/
theorem vuln_sound_two_runs {P : Program} {counted : Acc → Bool} {L1 L2 : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (d1 d2 : MethodId → List PFact)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D P counted L1 (policy d1) sinks roots (.vuln M n s b)) ∧
    (∃ b, D P counted L2 (policy d2) sinks roots (.vuln M n s b)) :=
  ⟨vuln_found_policy P counted L1 sinks roots hwf d1 hR hs hT hsc,
   vuln_found_policy P counted L2 sinks roots hwf d2 hR hs hT hsc⟩

#print axioms vuln_sound_two_runs

end ApSpec.Coverage
