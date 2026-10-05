/-
  ApSpec.Confirmed — a CONFIRMED vulnerability is a real vulnerability.

  A vulnerability on a complete edge is not enough: a demand caller edge can feed
  an added fact, the callee can answer the request with an exact initial fact
  (normal layer), and the callee sink edge is then complete (review 2).

  The fix: confirmation needs a normal-layer SUPPORT chain from a root (`Sup`).
  Only the zero fact and exact concrete-mark request answers are supported, and
  only through normal-layer caller edges of supported initial facts.

  Main results:
    * `sup_entry`        a supported initial fact is exact with a concrete mark, and
                         its unique location is entry-reachable.
                         (`sup_entry_valid`: the same for a valid entry location.)
    * `confirmed_real`   a confirmed vulnerability has a concrete witness:
                         `∃ l, Reach P roots M n l ∧ s.covers l`.
                         (`confirmed_real_of`: the same without `P.WF`, which the
                         proof does not use.)
    * `confirmed_real_valid` the same for prefix-closed type filters, if every location
                         of the sink pattern is valid (`confirmed_real_valid_of`: a
                         location of the sink pattern that is reached if it is valid).
    * `CexConfFilt.cex_conf_filt`, `CexConfMark.cex_conf_mark`: the version-4 statement of
                         `confirmed_real` (only `P.WF`) is FALSE. Each hypothesis is
                         necessary.
    * `rev2_vuln_derived`, `rev2_not_confirmed`: the false positive of review 2 is
                         derived in the normal layer, but it is not confirmed.
    * `weak_support_gap` the proposed weak side condition admits a false positive.

  ROUND 5 (type filters, cleaners, marks `*∖x`). The proof uses `Exact.edge_exact`, and that
  theorem now needs hypotheses (see `Exact.CexMark`, `Exact.CexFilt`). So `sup_entry` and
  `confirmed_real*` have new hypotheses. Two forms:
    * `Exact.MarkWF P` and `Exact.FiltUp P` (`sup_entry`, `confirmed_real_of`,
      `confirmed_real`). With `WF.filtPrefix`, `FiltUp` makes each filter constant
      (`Exact.filtUp_const`), so this form is for a program without a real type filter.
    * `Exact.MarkWF P`, `Exact.FiltValid P ok`, `Exact.BackOK P ok` and the validity of the
      sink locations (`sup_entry_valid`, `confirmed_real_valid_of`, `confirmed_real_valid`).
      This is the form for a real program with prefix-closed type filters.
  The two counterexamples show that the theorem is false without the hypotheses:
    * `CexConfFilt`: a normal `[any]` fact passes a filter; a read below it gives an exact
      complete sink fact, but the filter rejects the location that the read uses.
    * `CexConfMark`: the callee cleans the mark `5` and then a `*` to `9` edge gives a normal
      `9` fact (`markComp` forgets `*∖{5}`); the caller passes a `5` location.
  The sink check on a fact `*∖x` (`check_triggered_passes`) gives the new `passes` conjunct
  of `den`: a triggered mark is not in `x`.

  Lemma used at the sink: under a non-`*` initial fact every final fact is non-`*`
  (`D_NS`). So a complete final fact under a supported (exact) initial fact is exact,
  and the sink overlap gives a location inside the sink pattern.

  Side condition (correction of the proposed form): the support needs `j = a.fact`.
  The form `j = answerInit k a.fact t ∧ j.kind = .exact` is too weak: the request
  `k` can be on a different base or on a shorter path than the added fact `a`, and
  then `j` denotes a location that `a` does not reach (see `weak_support_gap`).
  For an answer made by the rule `answer` from the same added fact (`overlapB a k`)
  with an exact match, `j = a.fact` is true, so the condition loses no real answer.
-/
import ApSpec.Exact
import ApSpec.Core
import ApSpec.Invariant

namespace ApSpec.Confirmed
open ApSpec

/-! ## 1. Under a non-`*` initial fact every final fact is non-`*` -/

theorem norm_nonstar {x : AFact} (h : x.fact.kind.isStar = false) : x.norm = x := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  cases k with
  | star e => cases h
  | any => rfl
  | exact => rfl

theorem applyEdge_nonstar {c r : AFact} {fr to : PFact} (hc : c.fact.kind.isStar = false)
    (hr : r ∈ (applyEdge c fr to).facts) : r.fact.kind.isStar = false := by
  obtain ⟨p, k, ap, _, hg, _, rfl⟩ := Invariant.applyEdge_shape hr
  have hk : k.isStar = false := Invariant.geo_nonstar hc hg
  rw [norm_nonstar hk]
  exact hk

theorem limitF_nonstar {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : f.fact.kind.isStar = false) : (limitF counted L f).fact.kind.isStar = false := by
  rcases Invariant.limitF_cases counted L f with e | ⟨hany, _⟩
  · rw [e]; exact h
  · rw [hany]; rfl

theorem startFact_nonstar {i : PFact} (h : i.kind.isStar = false) :
    (startFact i).fact.kind.isStar = false := by
  obtain ⟨b, p, k, m⟩ := i
  cases k with
  | star e => cases h
  | any => cases m <;> rfl
  | exact => rfl

theorem transfer_nonstar {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hc : c.fact.kind.isStar = false) (hr : r ∈ (transfer counted L s c).facts) :
    r.fact.kind.isStar = false := by
  rcases Invariant.transfer_mem hr with rfl | ⟨x, e, _, hx, rfl⟩
  · exact hc
  · exact limitF_nonstar (applyEdge_nonstar hc hx)

/-- The cleaner keeps a non-`*` fact non-`*`: its results keep the tail, or (`concPart`)
    give the tail `$`. -/
theorem cleanRes_nonstar {cl : Cleaner} {c r : AFact} (hc : c.fact.kind.isStar = false)
    (hr : r ∈ (cleanRes cl c).facts) : r.fact.kind.isStar = false := by
  rcases Invariant.cleanRes_facts_cases hr with rfl | ⟨t, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
  · exact hc
  · exact hc
  · rw [norm_nonstar (x := ⟨c.fact, true⟩) hc]; exact hc
  · rcases Invariant.concPart_cases cl c with h1 | ⟨_, h1⟩
    · rw [h1]; exact hc
    · rw [h1]; rfl

/-- The motive: under a non-`*` initial fact the final fact is non-`*`. -/
def NS : Obj → Prop
  | .edge _ i _ f => i.kind.isStar = false → f.fact.kind.isStar = false
  | _ => True

theorem D_NS {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj} (h : D P counted L α sinks roots o) : NS o := by
  induction h with
  | root => trivial
  | @start M i _ _ => exact fun hi => startFact_nonstar hi
  | @step M i n f n' s f' _ _ hf' ih => exact fun hi => transfer_nonstar (ih hi) hf'
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ _ hr _ hr' ihF _ _ =>
    intro hi
    have h1 := applyEdge_nonstar (ihF hi) ha
    obtain ⟨x, hx, rfl⟩ := Invariant.applySummary_shape hr
    have h2 := applyEdge_nonstar h1 hx
    have h3 : (AFact.norm ⟨x.fact, x.demand || g.demand⟩).fact.kind.isStar = false := by
      rw [norm_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) h2]
      exact h2
    exact limitF_nonstar (applyEdge_nonstar h3 hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf' ih => exact fun hi => cleanRes_nonstar (ih hi) hf'
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms D_NS

/-! ## 2. The sink check on an exact initial fact -/

/-- The sink check with a concrete initial mark `t0`. ROUND 5: a triggered check also gives
    `f.fact.mark.passes t0` (for a fact `*∖x`, the mark `t0` is not in `x`). -/
theorem check_triggered_passes {i s : PFact} {f : AFact} {t0 : Mark} (him : i.mark = .conc t0)
    (h : check i f s = .triggered) :
    ∃ T, s.mark = .conc T ∧ overlapB f.fact s = true ∧ f.fact.mark.out t0 = T ∧
      f.fact.mark.passes t0 := by
  unfold check at h
  cases hsm : s.mark with
  | star => rw [hsm] at h; cases h
  | starEx _ => rw [hsm] at h; cases h
  | conc T =>
    rw [hsm] at h
    cases ho : overlapB f.fact s with
    | false => rw [ho] at h; cases h
    | true =>
      rw [ho] at h
      cases hfm : f.fact.mark with
      | conc t =>
        rw [hfm] at h
        dsimp only at h
        cases hb : Nat.beq t T with
        | false => rw [hb] at h; cases h
        | true => exact ⟨T, rfl, rfl, Nat.eq_of_beq_eq_true hb, trivial⟩
      | star =>
        rw [hfm, him] at h
        dsimp only at h
        cases hb : Nat.beq t0 T with
        | false => rw [hb] at h; cases h
        | true => exact ⟨T, rfl, rfl, Nat.eq_of_beq_eq_true hb, trivial⟩
      | starEx x =>
        rw [hfm, him] at h
        dsimp only at h
        cases hx : memB T x with
        | true => rw [hx] at h; cases h
        | false =>
          rw [hx] at h
          cases hb : Nat.beq t0 T with
          | false => rw [hb] at h; cases h
          | true =>
            have e : t0 = T := Nat.eq_of_beq_eq_true hb
            subst e
            exact ⟨_, rfl, rfl, rfl, hx⟩

#print axioms check_triggered_passes

theorem check_triggered {i s : PFact} {f : AFact} {t0 : Mark} (him : i.mark = .conc t0)
    (h : check i f s = .triggered) :
    ∃ T, s.mark = .conc T ∧ overlapB f.fact s = true ∧ f.fact.mark.out t0 = T := by
  obtain ⟨T, h1, h2, h3, _⟩ := check_triggered_passes him h
  exact ⟨T, h1, h2, h3⟩

#print axioms check_triggered

/-- An exact fact that overlaps a sink pattern lies in the sink pattern. -/
theorem overlap_exact_covers {a s : PFact} (hk : a.kind = .exact) (h : overlapB a s = true)
    (m : Mark) (hm : s.mark.admits m) : s.covers ⟨a.base, a.path, m⟩ := by
  unfold overlapB at h
  cases hb : Nat.beq a.base s.base with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_, hm⟩
    cases hrel : relate a.path s.path with
    | below r =>
      rw [hrel] at h
      have hr : admitsTailB a.kind r = true := h
      rw [hk] at hr
      cases r with
      | nil =>
        have e := Exact.relate_below hrel
        refine ⟨[], ?_, Exact.tailI_nil _⟩
        show a.path = s.path ++ []
        rw [e, List.append_nil, List.append_nil]
      | cons x r => cases hr
    | above r =>
      rw [hrel] at h
      have hr : admitsTailB s.kind r = true := h
      exact ⟨r, Exact.relate_above hrel, Exact.admitsTailB_tailI hr⟩
    | apart => rw [hrel] at h; cases h

#print axioms overlap_exact_covers

theorem complete_nonstar_exact {f : AFact} (hc : f.complete = true)
    (hs : f.fact.kind.isStar = false) : f.fact.kind = .exact := by
  unfold AFact.complete at hc
  cases hk : f.fact.kind with
  | star e => rw [hk] at hs; cases hs
  | any =>
    rw [hk] at hc
    cases hd : f.demand <;> rw [hd] at hc <;> cases hc
  | exact => rfl

/-- The pair of an initial fact at its own location (`σ = []`) and an exact final fact.
    ROUND 5: the new hypothesis `hp` is the `passes` conjunct of `den`. -/
theorem den_exact_exact {i a : PFact} {t0 : Mark} (him : i.mark = .conc t0)
    (hak : a.kind = .exact) (hp : a.mark.passes t0) :
    den i a ⟨i.base, i.path, t0⟩ ⟨a.base, a.path, a.mark.out t0⟩ := by
  refine ⟨rfl, rfl, ?_, rfl, hp, [], [], (List.append_nil _).symm, (List.append_nil _).symm,
    Exact.tailI_nil _, ?_⟩
  · rw [him]; exact rfl
  · rw [hak]; exact rfl

/-! ## 3. Entry reachability -/

section
variable (P : Program) (roots : List MethodId)

/-- `EntryReach M l0`: the location `l0` is real at the entry of `M`: the zero
    location of a root, or the binding of a real caller location. -/
def EntryReach (M : MethodId) (l0 : Loc) : Prop :=
  (M ∈ roots ∧ l0 = zeroLoc) ∨
  (∃ M' n l n' c e, Reach P roots M' n l ∧ (M', n, Instr.call c, n') ∈ P.edges ∧
    c.callee = M ∧ e ∈ c.toCallee ∧ den e.1 e.2 l l0)

theorem entry_reach {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (he : EntryReach P roots M l0) (hf : Flow P M l0 n l) : Reach P roots M n l := by
  rcases he with ⟨hM, rfl⟩ | ⟨M', n0, l', n', c, e, hR, hE, rfl, hc, hd⟩
  · exact Reach.root hM hf
  · exact Reach.down hR hE hc hd hf

end

/-! ## 4. Support and confirmation -/

section
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The normal-layer SUPPORT of initial facts. -/
inductive Sup : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → Sup M zeroFact
  | call {M i n f n' c e a j} :
      Sup M i → D P counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D P counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D P counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j = a.fact)) →
      Sup c.callee j

/-- A CONFIRMED vulnerability: a complete sink edge under a supported initial fact. -/
def Confirmed (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D P counted L α sinks roots (.edge M i n f) ∧ Sup P counted L α sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end

/-- The facts of one step of the support chain: the added fact `a` is exact with the mark `t`
    and it is the supported initial fact `j`. -/
theorem sup_step {a : AFact} {j : PFact} {P' : PFact → Mark → Prop}
    (hj : (j = zeroFact ∧ a.fact = zeroFact) ∨
      (∃ k t, P' k t ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧
        j = a.fact)) :
    ∃ t, a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧ j = a.fact := by
  rcases hj with ⟨hj0, hz⟩ | ⟨k, t, _, hak, ham, _, hja⟩
  · exact ⟨zeroMark, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hj0, hz]⟩
  · exact ⟨t, hak, ham, hja⟩

/-- A supported initial fact is exact with a concrete mark, and its unique location is
    entry-reachable. ROUND 5: the new hypotheses `MarkWF P` and `FiltUp P` are the hypotheses
    of `Exact.edge_exact`. -/
theorem sup_entry {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (h : Sup P counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧ EntryReach P roots M ⟨i.base, i.path, t⟩ := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := sup_step hj
    have hden := den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hR := entry_reach P roots hent (Exact.edge_exact hmw hup hD hfd hd1)
    exact ⟨t, hak, ham, Or.inr ⟨M, n, l, n', c, e, hR, hE, rfl, he, hd2⟩⟩

#print axioms sup_entry

/-- A supported initial fact is exact with a concrete mark, and its unique location is
    entry-reachable if it is valid (the hypotheses of `Exact.edge_exact_valid`: prefix-closed
    type filters, no `FiltUp`). -/
theorem sup_entry_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (h : Sup P counted L α sinks roots M i) :
    ∃ t, i.kind = .exact ∧ i.mark = .conc t ∧
      (ok ⟨i.base, i.path, t⟩ → EntryReach P roots M ⟨i.base, i.path, t⟩) := by
  induction h with
  | root hM => exact ⟨zeroMark, rfl, rfl, fun _ => Or.inl ⟨hM, rfl⟩⟩
  | @call M i n f n' c e a j _ hD hfd hE he ha had _ hj ih =>
    obtain ⟨t0, hik, him, hent⟩ := ih
    obtain ⟨t, hak, ham, rfl⟩ := sup_step hj
    refine ⟨t, hak, ham, fun hokj => ?_⟩
    have hden := den_exact_exact (a := a.fact) him hak (by rw [ham]; trivial)
    rw [ham] at hden
    obtain ⟨hp1, hc1⟩ := Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he) (Exact.applyEdge_mark ha).1
    obtain ⟨l, hd1, hd2⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had hden
    have hokl : ok l := hbo.toC _ _ _ _ hE e he _ _ hd2 hokj
    obtain ⟨hfl, hok0⟩ := Exact.edge_exact_valid hmw hv hbo hD hfd hd1 hokl
    exact Or.inr ⟨M, n, l, n', c, e, entry_reach P roots (hent hok0) hfl, hE, rfl, he, hd2⟩

#print axioms sup_entry_valid

/-- The sink location of a confirmed vulnerability: the exact complete sink fact `f` under the
    supported initial fact `i` (mark `t0`) gives the location `⟨f.base, f.path, f.mark.out t0⟩`.
    It is in the sink pattern, and the pair (entry location, sink location) is in `den`. -/
theorem confirmed_sink {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s i : PFact} {f : AFact} {t0 : Mark}
    (hD : D P counted L α sinks roots (.edge M i n f)) (hc : f.complete = true)
    (hch : check i f s = .triggered) (hik : i.kind = .exact) (him : i.mark = .conc t0) :
    den i f.fact ⟨i.base, i.path, t0⟩ ⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩ ∧
      s.covers ⟨f.fact.base, f.fact.path, f.fact.mark.out t0⟩ := by
  have hns : f.fact.kind.isStar = false := D_NS hD (by rw [hik]; rfl)
  have hfk := complete_nonstar_exact hc hns
  obtain ⟨T, hsm, ho, hmo, hps⟩ := check_triggered_passes him hch
  exact ⟨den_exact_exact him hfk hps, overlap_exact_covers hfk ho _ (by rw [hsm]; exact hmo)⟩

#print axioms confirmed_sink

/-- THE THEOREM (without the well-formedness hypothesis, which it does not need):
    a confirmed vulnerability is a real concrete vulnerability.
    ROUND 5: the new hypotheses `MarkWF P` and `FiltUp P`; without them the statement is
    false (`CexConfMark.cex_conf_mark`, `CexConfFilt.cex_conf_filt`). -/
theorem confirmed_real_of {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry hmw hup hS
  obtain ⟨hden, hcov⟩ := confirmed_sink hD hc hch hik him
  exact ⟨_, entry_reach P roots hent
    (Exact.edge_exact hmw hup hD (Exact.complete_demand hc) hden), hcov⟩

#print axioms confirmed_real_of

/-- THE THEOREM: a confirmed vulnerability is a real concrete vulnerability
    (no false positive). ROUND 5: the new hypotheses `MarkWF P` and `FiltUp P`. -/
theorem confirmed_real {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact}
    (_hwf : P.WF) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  confirmed_real_of hmw hup h

#print axioms confirmed_real

/-- THE THEOREM FOR VALID LOCATIONS (prefix-closed type filters, no `FiltUp`): a confirmed
    vulnerability has a location in the sink pattern, and this location is reached if it is
    valid. -/
theorem confirmed_real_valid_of {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, s.covers l ∧ (ok l → Reach P roots M n l) := by
  obtain ⟨i, f, hD, hS, hc, _, hch⟩ := h
  obtain ⟨t0, hik, him, hent⟩ := sup_entry_valid hmw hv hbo hS
  obtain ⟨hden, hcov⟩ := confirmed_sink hD hc hch hik him
  refine ⟨_, hcov, fun hok => ?_⟩
  obtain ⟨hfl, hok0⟩ := Exact.edge_exact_valid hmw hv hbo hD (Exact.complete_demand hc) hden hok
  exact entry_reach P roots (hent hok0) hfl

#print axioms confirmed_real_valid_of

/-- THE THEOREM FOR A REAL PROGRAM with prefix-closed type filters: if every location of the
    sink pattern is valid, a confirmed vulnerability is a real concrete vulnerability. -/
theorem confirmed_real_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {n : Node} {s : PFact} {ok : Loc → Prop}
    (_hwf : P.WF) (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hok : ∀ l, s.covers l → ok l)
    (h : Confirmed P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l := by
  obtain ⟨l, hcov, hR⟩ := confirmed_real_valid_of hmw hv hbo h
  exact ⟨l, hR (hok l hcov), hcov⟩

#print axioms confirmed_real_valid

/-! ## 5. The new hypotheses are necessary

  The version-4 statement of `confirmed_real` (only `P.WF`) is FALSE in round 5. Each program
  below is well formed, and it has a confirmed vulnerability that no concrete location
  reaches. The first program satisfies `MarkWF` but not `FiltUp`; the second program
  satisfies `FiltUp` but not `MarkWF`. -/

/-- A location with known components. -/
theorem loc_eq {l : Loc} {b : Base} {p : List Acc} {m : Mark} (hb : l.base = b)
    (hp : l.path = p) (hm : l.mark = m) : l = ⟨b, p, m⟩ := by
  obtain ⟨b', p', m'⟩ := l
  cases hb
  cases hp
  cases hm
  rfl

namespace CexConfFilt
open Exact

/-- The type filter of the base `1`: only the path `[]` exists. It is prefix-closed. -/
def may (p : List Acc) : Bool := p.isEmpty
/-- A source: the zero fact gives `(1,.,[any],{},5)` (a normal-layer fact). -/
def s1 : Stmt := ⟨[zeroBase], [(zeroFact, ⟨1, [], .any, .conc 5⟩)]⟩
/-- A read below the filtered path: `2 = 1.7`. -/
def rd : MicroEdge := (⟨1, [7], .exact, .star⟩, ⟨2, [], .exact, .star⟩)
def s2 : Stmt := ⟨[1], [rd]⟩
/-- One method `0` (a root): the source, the filter, the read. -/
def P : Program := ⟨fun _ => 0, fun _ => 3,
  [(0, 0, .stmt s1, 1), (0, 1, .filt 1 may, 2), (0, 2, .stmt s2, 3)]⟩
def sinkPat : PFact := ⟨2, [], .exact, .conc 5⟩
def sinks : List (MethodId × Node × PFact) := [(0, 3, sinkPat)]
def α : MethodId → PFact → PFact := fun _ a => a

abbrev DC := D P (fun _ => true) 3 α sinks [0]

theorem wf : P.WF where
  stmtTouched := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  filtPrefix := by
    intro M n b may' n' hE p q h
    cases hE with
    | tail _ h' =>
      cases h' with
      | head =>
        cases p with
        | nil => rfl
        | cons a p => cases h
      | tail _ h'' =>
        cases h'' with
        | tail _ h3 => cases h3

theorem markWF : MarkWF P where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_filtUp : ¬ FiltUp P := by
  intro h
  have h1 := h 0 1 1 may 2 (List.Mem.tail _ (List.Mem.head _)) [] [7] rfl
  exact absurd h1 (by decide)

/-- The analysis confirms the vulnerability: the read `2 = 1.7` of the normal `[any]` fact
    gives the complete fact `(2,.,$,{},5)` at the sink. -/
theorem confirmed : Confirmed P (fun _ => true) 3 α sinks [0] 0 3 sinkPat := by
  have h0 : DC (.init 0 zeroFact) := D.root (List.Mem.head _)
  have h1 : DC (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) := D.start h0
  have h2 : DC (.edge 0 zeroFact 1 ⟨⟨1, [], .any, .conc 5⟩, false⟩) :=
    D.step h1 (s := s1) (List.Mem.head _) (by decide)
  have h3 : DC (.edge 0 zeroFact 2 ⟨⟨1, [], .any, .conc 5⟩, false⟩) :=
    D.filt h2 (List.Mem.tail _ (List.Mem.head _)) (fun _ => rfl)
  have h4 : DC (.edge 0 zeroFact 3 ⟨⟨2, [], .exact, .conc 5⟩, false⟩) :=
    D.step h3 (s := s2) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  exact ⟨zeroFact, _, h4, Sup.root (List.Mem.head _), rfl, List.Mem.head _, by decide⟩

#print axioms confirmed

/-- The concrete locations from the zero location: at the node `2` only `1.[]`; no location
    at the node `3`. -/
def Inv (n : Node) (l : Loc) : Prop :=
  (n = 0 ∧ l = zeroLoc) ∨ (n = 1 ∧ l.base = 1) ∨ (n = 2 ∧ l.base = 1 ∧ l.path = [])

theorem flow_inv : ∀ {M l0 n l}, Flow P M l0 n l → l0 = zeroLoc → Inv n l := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro e; exact Or.inl ⟨rfl, e⟩
  | step _ hE hs ih =>
    intro e
    have hi := ih e
    cases hE with
    | head =>
      rcases hi with ⟨_, rfl⟩ | ⟨hn, _⟩ | ⟨hn, _⟩
      · rcases hs with ⟨ht, _⟩ | ⟨e', he', hd⟩
        · exact absurd ht (by decide)
        · cases he' with
          | head => exact Or.inr (Or.inl ⟨rfl, hd.2.1⟩)
          | tail _ h' => cases h'
      · exact absurd hn (by decide)
      · exact absurd hn (by decide)
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | head =>
          rcases hi with ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨_, hb, hp⟩
          · exact absurd hn (by decide)
          · exact absurd hn (by decide)
          · rcases hs with ⟨ht, _⟩ | ⟨e', he', hd⟩
            · rw [hb] at ht; exact absurd ht (by decide)
            · cases he' with
              | head =>
                obtain ⟨-, -, -, -, -, σ, τ, hp0, -, -, -⟩ := hd
                rw [hp] at hp0
                cases hp0
              | tail _ h' => cases h'
        | tail _ hE => cases hE
  | pass _ hE _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE => cases hE
  | call _ hE _ _ _ _ _ _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE => cases hE
  | clean _ hE _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE => cases hE
  | @filt _ _ _ l1 _ _ _ _ hE hb ih =>
    intro e
    cases hE with
    | tail _ hE =>
      cases hE with
      | head =>
        rcases ih e with ⟨hn, _⟩ | ⟨_, hb1⟩ | ⟨hn, _⟩
        · exact absurd hn (by decide)
        · have hm := hb hb1
          refine Or.inr (Or.inr ⟨rfl, hb1, ?_⟩)
          cases hlp : l1.path with
          | nil => rfl
          | cons a p => rw [hlp] at hm; cases hm
        · exact absurd hn (by decide)
      | tail _ hE =>
        cases hE with
        | tail _ hE => cases hE

theorem reach_inv : ∀ {M n l}, Reach P [0] M n l → Inv n l := by
  intro M n l h
  induction h with
  | root _ hf => exact flow_inv hf rfl
  | down _ hE _ _ _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE => cases hE

theorem not_real : ¬ ∃ l, Reach P [0] 0 3 l ∧ sinkPat.covers l := by
  rintro ⟨l, hR, _⟩
  rcases reach_inv hR with ⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact absurd hn (by decide)

/-- THE FILTER COUNTEREXAMPLE to the version-4 `confirmed_real`. The program is well formed
    and satisfies `MarkWF`, but not `FiltUp`. The vulnerability is confirmed, but no concrete
    location reaches the sink: the filter rejects the path `1.7` that the read uses. -/
theorem cex_conf_filt :
    P.WF ∧ MarkWF P ∧ ¬ FiltUp P ∧ Confirmed P (fun _ => true) 3 α sinks [0] 0 3 sinkPat ∧
      ¬ ∃ l, Reach P [0] 0 3 l ∧ sinkPat.covers l :=
  ⟨wf, markWF, not_filtUp, confirmed, not_real⟩

end CexConfFilt

#print axioms CexConfFilt.cex_conf_filt

namespace CexConfMark
open Exact

/-- The caller `1` (a root): `4 = source(5)`, then the call `0(4)`, the result to `3`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, ⟨4, [], .exact, .conc 5⟩)]⟩
def bnd : MicroEdge := (⟨4, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def back : MicroEdge := (⟨2, [], .exact, .star⟩, ⟨3, [], .exact, .star⟩)
def cc : Call := ⟨0, [4], [bnd], [back]⟩
/-- The callee `0`: the cleaner of the mark `5` on the base `1`, then `2 = convert9(1)`. -/
def cl : Cleaner := ⟨1, [], .atAndBelow, some 5⟩
def conv : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨2, [], .exact, .conc 9⟩)
def s : Stmt := ⟨[1], [conv]⟩
def P : Program := ⟨fun _ => 0, fun _ => 2,
  [(1, 0, .stmt src, 1), (1, 1, .call cc, 2), (0, 0, .clean cl, 1), (0, 1, .stmt s, 2)]⟩
def sinkPat : PFact := ⟨3, [], .exact, .conc 9⟩
def sinks : List (MethodId × Node × PFact) := [(1, 2, sinkPat)]
/-- The run-1 abstraction policy (the empty demand). -/
def α : MethodId → PFact → PFact := policy (fun _ => [])
def ic : PFact := ⟨1, [], .star (.set []), .star⟩
def a : AFact := ⟨⟨1, [], .exact, .conc 5⟩, false⟩

abbrev DC := D P (fun _ => true) 3 α sinks [1]

theorem wf : P.WF where
  stmtTouched := by
    intro M n s' n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | head =>
            cases he with
            | head => rfl
            | tail _ h => cases h
          | tail _ h => cases h
  toStar := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  fromStar := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  filtPrefix := by
    intro M n b may n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h

theorem filtUp : FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_markWF : ¬ MarkWF P := by
  intro h
  have h1 := h.stmt 0 1 s 2
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) conv
    (List.Mem.head _)
  exact absurd h1 (by decide)

/-- The analysis confirms the vulnerability: the callee summary `(1,.,*,{},*) → (2,.,$,{},9)`
    is in the normal layer (`markComp (conc 9) (starEx [5]) = some (conc 9)`), and the caller
    applies it to its fact `(1,.,$,{},5)`. -/
theorem confirmed : Confirmed P (fun _ => true) 3 α sinks [1] 1 2 sinkPat := by
  have h0 : DC (.init 1 zeroFact) := D.root (List.Mem.head _)
  have h1 : DC (.edge 1 zeroFact 0 ⟨zeroFact, false⟩) := D.start h0
  have hE1 : (1, 0, Instr.stmt src, 1) ∈ P.edges := List.Mem.head _
  have hE2 : (1, 1, Instr.call cc, 2) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
  have h2 : DC (.edge 1 zeroFact 1 ⟨⟨4, [], .exact, .conc 5⟩, false⟩) :=
    D.step h1 (s := src) hE1 (by decide)
  have h3 : DC (.added 0 a.fact) :=
    D.added (a := a) (c := cc) (e := bnd) h2 hE2 (List.Mem.head _) (by decide)
  have h4 : DC (.init 0 ic) := by
    have h := D.initA h3
    have e : α 0 a.fact = ic := by decide
    rw [e] at h
    exact h
  have h5 : DC (.edge 0 ic 0 ⟨ic, false⟩) := D.start h4
  have h6 : DC (.edge 0 ic 1 ⟨⟨1, [], .star (.set []), .starEx [5]⟩, false⟩) :=
    D.clean h5 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have h7 : DC (.edge 0 ic 2 ⟨⟨2, [], .exact, .conc 9⟩, false⟩) :=
    D.step h6 (s := s) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      (by decide)
  have h8 := D.ret (r := ⟨⟨2, [], .exact, .conc 9⟩, false⟩)
    (r' := ⟨⟨3, [], .exact, .conc 9⟩, false⟩) (e2 := back) h2 hE2 (List.Mem.head _)
    (a := a) (by decide) h4 (by decide) h7 (by decide) (List.Mem.head _) (by decide)
  have e8 : limitF (fun _ => true) 3 ⟨⟨3, [], .exact, .conc 9⟩, false⟩ =
      ⟨⟨3, [], .exact, .conc 9⟩, false⟩ := by decide
  rw [e8] at h8
  exact ⟨zeroFact, _, h8, Sup.root (List.Mem.head _), rfl, List.Mem.head _, by decide⟩

#print axioms confirmed

/-- In the callee `0`, the location `1` with the mark `5` flows nowhere: the cleaner
    removes it. -/
theorem flow0 : ∀ {M l0 n l}, Flow P M l0 n l → M = 0 → l0 = ⟨1, [], 5⟩ → n = 0 ∧ l = l0 := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro _ _; exact ⟨rfl, rfl⟩
  | step _ hE _ ih =>
    intro hM hl
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | head => exact absurd (ih rfl hl).1 (by decide)
          | tail _ h => cases h
  | pass _ hE _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | clean _ hE hcl ih =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          obtain ⟨-, rfl⟩ := ih rfl hl
          subst hl
          exact absurd hcl (by decide)
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h

/-- In the caller `1`, from the zero location: the zero location at the node `0`, the location
    `4` with the mark `5` at the node `1`, nothing at the node `2`. -/
theorem flow1 : ∀ {M l0 n l}, Flow P M l0 n l → M = 1 → l0 = zeroLoc →
    (n = 0 ∧ l = zeroLoc) ∨ (n = 1 ∧ l = ⟨4, [], 5⟩) := by
  intro M l0 n l h
  induction h with
  | start M l0 => intro _ hl; exact Or.inl ⟨rfl, hl⟩
  | step _ hE hs ih =>
    intro hM hl
    cases hE with
    | head =>
      rcases ih rfl hl with ⟨_, rfl⟩ | ⟨hn, _⟩
      · rcases hs with ⟨ht, _⟩ | ⟨e', he', hd⟩
        · exact absurd ht (by decide)
        · cases he' with
          | head =>
            obtain ⟨-, hb, -, hm, -, σ, τ, -, hp, -, hτ⟩ := hd
            have hτ' : τ = [] := hτ
            rw [hτ'] at hp
            exact Or.inr ⟨rfl, loc_eq hb hp hm⟩
          | tail _ h' => cases h'
      · exact absurd hn (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | head => exact absurd hM (by decide)
          | tail _ h => cases h
  | pass _ hE hm ih =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        rcases ih rfl hl with ⟨hn, _⟩ | ⟨_, rfl⟩
        · exact absurd hn (by decide)
        · exact absurd hm (by decide)
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | call _ hE he1 hd1 hfc _ _ ih _ =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        rcases ih rfl hl with ⟨hn, _⟩ | ⟨_, rfl⟩
        · exact absurd hn (by decide)
        · cases he1 with
          | head =>
            obtain ⟨-, hb, -, hm, -, σ, τ, hp0, hp, hσ, hτ⟩ := hd1
            have hσ' : σ = [] := hσ
            have hτ' : τ = [] := hτ
            rw [hτ'] at hp
            have hl1 := loc_eq hb hp hm
            exact absurd (flow0 hfc rfl hl1).1 (by decide)
          | tail _ h' => cases h'
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | clean _ hE _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head => exact absurd hM (by decide)
        | tail _ h =>
          cases h with
          | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h

theorem reach1 : ∀ {M n l}, Reach P [1] M n l → M = 1 →
    (n = 0 ∧ l = zeroLoc) ∨ (n = 1 ∧ l = ⟨4, [], 5⟩) := by
  intro M n l h
  induction h with
  | root hM hf =>
    intro e
    exact flow1 hf e rfl
  | down _ hE _ _ _ _ =>
    intro hM
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h

theorem not_real : ¬ ∃ l, Reach P [1] 1 2 l ∧ sinkPat.covers l := by
  rintro ⟨l, hR, _⟩
  rcases reach1 hR rfl with ⟨hn, _⟩ | ⟨hn, _⟩ <;> exact absurd hn (by decide)

/-- THE MARK COUNTEREXAMPLE to the version-4 `confirmed_real`. The program is well formed and
    satisfies `FiltUp` (it has no filter), but not `MarkWF` (the edge `conv` gives the
    concrete mark `9` from the premise mark `*`). The vulnerability is confirmed, but no
    concrete location reaches the sink: the caller passes the mark `5`, and the callee
    cleaner removes it. -/
theorem cex_conf_mark :
    P.WF ∧ FiltUp P ∧ ¬ MarkWF P ∧ Confirmed P (fun _ => true) 3 α sinks [1] 1 2 sinkPat ∧
      ¬ ∃ l, Reach P [1] 1 2 l ∧ sinkPat.covers l :=
  ⟨wf, filtUp, not_markWF, confirmed, not_real⟩

end CexConfMark

#print axioms CexConfMark.cex_conf_mark

/-! ## 6. The false positive of review 2 is not confirmed

  The program of review 2 (`review2/confirmed_fp.lean`). The analysis derives the
  vulnerability `D (.vuln 1 20 sinkPat false)` (normal layer). Its support chain
  goes through the caller edge `(w,.,$,T2)` at node 3, and that edge is in the
  demand layer. Here we prove the stronger fact: no confirmation is possible,
  because no concrete location reaches the sink.

  ROUND 5: the source edge of `s1` reads the zero fact (premise mark `conc 0`, not `*`), so
  that the program satisfies `MarkWF` (a concrete target mark needs a concrete premise mark).
  The zero base holds only the zero location, so the concrete flows do not change, and the
  derivation of `rev2_vuln_derived` does not change. -/

namespace Rev2

def f : Acc := 1
def g : Acc := 2
def T : Mark := 5
def T2 : Mark := 6
def h : Base := 10
def z : Base := 11
def w : Base := 12
def x : Base := 13
def st : Kind := .star Excl.empty
def cnt : Acc → Bool := fun _ => true

-- caller 0: h.f.g = source(T)  (cut to h.f.[any] under L = 1, demand layer)
def s1 : Stmt := ⟨[zeroBase, h], [ (zeroFact, zeroFact),
  (zeroFact, ⟨h, [f, g], .exact, .conc T⟩) ]⟩
-- z = h.f
def s2 : Stmt := ⟨[z, h], [ (⟨h, [], st, .star⟩, ⟨h, [], st, .star⟩),
  (⟨h, [f], st, .star⟩, ⟨z, [], st, .star⟩) ]⟩
-- conditional source: z carries T  =>  w gets T2
def s3 : Stmt := ⟨[z, w], [ (⟨z, [], st, .star⟩, ⟨z, [], st, .star⟩),
  (⟨z, [], .exact, .conc T⟩, ⟨w, [], .exact, .conc T2⟩) ]⟩
-- call m(w); callee 1 has sink(x) for T2 at its entry node
def c1 : Call := ⟨1, [w], [(⟨w, [], st, .star⟩, ⟨x, [], st, .star⟩)], []⟩
def P : Program := ⟨fun m => if m = 0 then 0 else 20, fun m => if m = 0 then 4 else 21,
  [(0, 0, .stmt s1, 1), (0, 1, .stmt s2, 2), (0, 2, .stmt s3, 3), (0, 3, .call c1, 4)]⟩
def sinkPat : PFact := ⟨x, [], .exact, .conc T2⟩
def sinks : List (MethodId × Node × PFact) := [(1, 20, sinkPat)]
def dem : MethodId → List PFact := fun _ => []

/-- The concrete invariant of method 0: no location on `w`; `h` holds only `h.f.g`;
    `z` holds only `z.g`. -/
def Good (l : Loc) : Prop :=
  l.base ≠ w ∧ (l.base = h → l.path = [f, g]) ∧ (l.base = z → l.path = [g])

theorem good_of_base {l : Loc} (hw : l.base ≠ w) (hh : l.base ≠ h) (hz : l.base ≠ z) : Good l :=
  ⟨hw, fun e => absurd e hh, fun e => absurd e hz⟩

theorem step_s1 {l l' : Loc} (hg : Good l) (hs : s1.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨_, hb, _⟩ := hd
      exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨_, hb, _, _, _, σ, τ, _, hp, _, hτ⟩ := hd
        have hτ' : τ = [] := hτ
        refine ⟨by rw [hb]; decide, fun _ => by rw [hp, hτ']; rfl,
          fun e => absurd (hb.symm.trans e) (by decide)⟩
      | tail _ he => cases he

theorem step_s2 {l l' : Loc} (hg : Good l) (hs : s2.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨hb0, hb, _, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
      have hpath : l.path = [f, g] := hg.2.1 hb0
      refine ⟨by rw [hb]; decide, fun _ => ?_, fun e => absurd (hb.symm.trans e) (by decide)⟩
      rw [hp, hτ, ← hpath, hp0]
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨hb0, hb, _, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
        have hpath : l.path = [f, g] := hg.2.1 hb0
        rw [hpath] at hp0
        have hσ : σ = [g] := by
          injection hp0 with _ h2
          exact h2.symm
        refine ⟨by rw [hb]; decide, fun e => absurd (hb.symm.trans e) (by decide), fun _ => ?_⟩
        rw [hp, hτ, hσ]; rfl
      | tail _ he => cases he

theorem step_s3 {l l' : Loc} (hg : Good l) (hs : s3.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨hb0, hb, _, _, _, σ, τ, hp0, hp, _, hτ, _⟩ := hd
      have hpath : l.path = [g] := hg.2.2 hb0
      refine ⟨by rw [hb]; decide, fun e => absurd (hb.symm.trans e) (by decide), fun _ => ?_⟩
      rw [hp, hτ, ← hpath, hp0]
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨hb0, _, _, _, _, σ, τ, hp0, _, hσ, _⟩ := hd
        have hpath : l.path = [g] := hg.2.2 hb0
        have hσ' : σ = [] := hσ
        rw [hpath, hσ'] at hp0
        cases hp0
      | tail _ he => cases he

theorem flow_good {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P M l0 n l) (h0 : Good l0) : Good l := by
  induction hf with
  | start => exact h0
  | step _ hE hs ih =>
    have ih := ih h0
    cases hE with
    | head => exact step_s1 ih hs
    | tail _ hE =>
      cases hE with
      | head => exact step_s2 ih hs
      | tail _ hE =>
        cases hE with
        | head => exact step_s3 ih hs
        | tail _ hE =>
          cases hE with
          | tail _ hE => cases hE
  | pass _ _ _ ih => exact ih h0
  | call _ hE _ _ _ he2 _ _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | head => cases he2
          | tail _ hE => cases hE
  | clean _ hE _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | tail _ hE => cases hE
  | filt _ hE _ _ =>
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | tail _ hE => cases hE

theorem reach_good {M : MethodId} {n : Node} {l : Loc} (hr : Reach P [0] M n l) :
    M = 0 ∧ Good l := by
  induction hr with
  | root hM hf =>
    cases hM with
    | head => exact ⟨rfl, flow_good hf (good_of_base (by decide) (by decide) (by decide))⟩
    | tail _ hM => cases hM
  | down _ hE he hd _ ih =>
    obtain ⟨rfl, hg⟩ := ih
    cases hE with
    | tail _ hE =>
      cases hE with
      | tail _ hE =>
        cases hE with
        | tail _ hE =>
          cases hE with
          | head =>
            cases he with
            | head => exact absurd hd.1 hg.1
            | tail _ he => cases he
          | tail _ hE => cases hE

/-- The analysis derives the vulnerability in the normal layer (`demand = false`)
    (the derivation of review 2). -/
theorem rev2_vuln_derived : D P cnt 1 (policy dem) sinks [0] (.vuln 1 20 sinkPat false) := by
  have r0 : D P cnt 1 (policy dem) sinks [0] (.init 0 zeroFact) := D.root (by decide)
  have e0 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) :=
    D.start (P := P) (counted := cnt) (L := 1) (α := policy dem) (sinks := sinks) (roots := [0]) r0
  have e1 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 1 ⟨⟨h, [f], .any, .conc T⟩, true⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e2 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 2 ⟨⟨z, [], .any, .conc T⟩, true⟩) :=
    D.step e1 (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e3 : D P cnt 1 (policy dem) sinks [0] (.edge 0 zeroFact 3 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e2 (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have ad : D P cnt 1 (policy dem) sinks [0] (.added 1 ⟨x, [], .exact, .conc T2⟩) :=
    D.added (a := ⟨⟨x, [], .exact, .conc T2⟩, true⟩) (c := c1) (n' := 4)
      (e := (⟨w, [], st, .star⟩, ⟨x, [], st, .star⟩)) e3
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      (List.Mem.head _) (by decide)
  have i0 : D P cnt 1 (policy dem) sinks [0] (.init 1 ⟨x, [], st, .star⟩) := by
    have := D.initA ad
    have hp : policy dem 1 ⟨x, [], .exact, .conc T2⟩ = ⟨x, [], st, .star⟩ := by decide
    rw [hp] at this; exact this
  have s0 : D P cnt 1 (policy dem) sinks [0]
      (.edge 1 ⟨x, [], st, .star⟩ 20 ⟨⟨x, [], st, .star⟩, false⟩) := D.start i0
  have rq : D P cnt 1 (policy dem) sinks [0] (.req 1 ⟨x, [], st, .star⟩ T2) :=
    D.reqSink s0 (s := sinkPat) (List.Mem.head _) (by decide)
  have ia : D P cnt 1 (policy dem) sinks [0] (.init 1 ⟨x, [], .exact, .conc T2⟩) :=
    D.answer rq ad rfl (by decide)
  have sa : D P cnt 1 (policy dem) sinks [0]
      (.edge 1 ⟨x, [], .exact, .conc T2⟩ 20 ⟨⟨x, [], .exact, .conc T2⟩, false⟩) := D.start ia
  exact D.vuln sa (s := sinkPat) (List.Mem.head _) (by decide)

#print axioms rev2_vuln_derived

/-- The program of review 2 satisfies the mark condition of `Exact.MarkWF`. -/
theorem markWF : Exact.MarkWF P where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head => cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | head => cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he with
            | head => rfl
            | tail _ he => cases he
          | tail _ hE => cases hE
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he
          | tail _ hE => cases hE

#print axioms markWF

/-- The program of review 2 has no type filter, so `Exact.FiltUp` holds. -/
theorem filtUp : Exact.FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

/-- The false positive of review 2 is NOT confirmed. -/
theorem rev2_not_confirmed : ¬ Confirmed P cnt 1 (policy dem) sinks [0] 1 20 sinkPat := by
  intro hc
  obtain ⟨l, hR, _⟩ := confirmed_real_of markWF filtUp hc
  exact absurd (reach_good hR).1 (by decide)

#print axioms rev2_not_confirmed

end Rev2

/-! ## 7. The side condition `j = a.fact` is necessary

  The proposed support condition was `j = answerInit k a.fact t ∧ j.kind = .exact`
  (`WeakSup`). It is too weak: the answer `j` of a request `k` on a DIFFERENT base
  is exact, but it does not denote the location that the real added fact `a`
  reaches. Counterexample (a well-formed program): the caller passes a real
  `v/T2` to the parameter `y` and the spurious demand fact `w/T2~` (review 2) to
  the parameter `y2`. The callee has `sink(y2)` for `T2`. The demand fact gives the
  request on `(y2,.,*,*)` and its exact answer `j = (y2,.,$,T2)`. `WeakSup` accepts
  `j` through the real normal fact `a = (y,.,$,T2)` (`answerInit k a T2 = j`,
  `j.kind = $`), so the vulnerability is "confirmed", but `y2` never holds `T2`. -/

section Weak
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The support with the proposed (weak) side condition `j.kind = .exact`. -/
inductive WeakSup : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → WeakSup M zeroFact
  | call {M i n f n' c e a j} :
      WeakSup M i → D P counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D P counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D P counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j.kind = .exact)) →
      WeakSup c.callee j

def WeakConfirmed (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D P counted L α sinks roots (.edge M i n f) ∧ WeakSup P counted L α sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end Weak

namespace Weak
open Rev2

def v : Base := 14
def y : Base := 15
def y2 : Base := 16

-- v = source(T2)  (a real normal fact; ROUND 5: the source reads the zero fact, for `MarkWF`)
def s4 : Stmt := ⟨[zeroBase, v], [ (zeroFact, zeroFact),
  (zeroFact, ⟨v, [], .exact, .conc T2⟩) ]⟩
-- call m(y2 := w, y := v); callee 1 has sink(y2) for T2 at its entry node
def c2 : Call := ⟨1, [w, v], [(⟨w, [], st, .star⟩, ⟨y2, [], st, .star⟩),
  (⟨v, [], st, .star⟩, ⟨y, [], st, .star⟩)], []⟩
def P2 : Program := ⟨fun m => if m = 0 then 0 else 20, fun m => if m = 0 then 5 else 21,
  [(0, 0, .stmt s1, 1), (0, 1, .stmt s2, 2), (0, 2, .stmt s3, 3), (0, 3, .stmt s4, 4),
   (0, 4, .call c2, 5)]⟩
def sinkPat2 : PFact := ⟨y2, [], .exact, .conc T2⟩
def sinks2 : List (MethodId × Node × PFact) := [(1, 20, sinkPat2)]

/-- The answer `j` and the request `k`. -/
def kReq : PFact := ⟨y2, [], st, .star⟩
def jAns : PFact := ⟨y2, [], .exact, .conc T2⟩

theorem P2_wf : P2.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n s n' hE e he
    cases hE with
    | head => cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | head => cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE with
          | head => cases he with
            | head => rfl
            | tail _ he => cases he with
              | head => rfl
              | tail _ he => cases he
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he with
              | head => rfl
              | tail _ he => cases he with
                | head => rfl
                | tail _ he => cases he
            | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he
            | tail _ hE => cases hE
  · intro M n b may n' hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE

#print axioms P2_wf

/-- The program `P2` satisfies the mark condition of `Exact.MarkWF`. -/
theorem P2_markWF : Exact.MarkWF P2 where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head => cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | head => cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE with
          | head => cases he with
            | head => rfl
            | tail _ he => cases he with
              | head => rfl
              | tail _ he => cases he
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he with
              | head => rfl
              | tail _ he => cases he with
                | head => rfl
                | tail _ he => cases he
            | tail _ hE => cases hE
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he
            | tail _ hE => cases hE

#print axioms P2_markWF

/-- The program `P2` has no type filter, so `Exact.FiltUp` holds. -/
theorem P2_filtUp : Exact.FiltUp P2 := by
  intro M n b may n' hE
  cases hE with
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE

abbrev D2 := D P2 cnt 1 (policy dem) sinks2 [0]

/-- The weak support confirms the vulnerability at `sink(y2)`. -/
theorem weak_confirmed : WeakConfirmed P2 cnt 1 (policy dem) sinks2 [0] 1 20 sinkPat2 := by
  have r0 : D2 (.init 0 zeroFact) := D.root (by decide)
  have e0 : D2 (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) := D.start r0
  have e1 : D2 (.edge 0 zeroFact 1 ⟨⟨h, [f], .any, .conc T⟩, true⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e1z : D2 (.edge 0 zeroFact 1 ⟨zeroFact, false⟩) :=
    D.step e0 (s := s1) (List.Mem.head _) (by decide)
  have e2 : D2 (.edge 0 zeroFact 2 ⟨⟨z, [], .any, .conc T⟩, true⟩) :=
    D.step e1 (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e2z : D2 (.edge 0 zeroFact 2 ⟨zeroFact, false⟩) :=
    D.step e1z (s := s2) (List.Mem.tail _ (List.Mem.head _)) (by decide)
  have e3 : D2 (.edge 0 zeroFact 3 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e2 (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have e3z : D2 (.edge 0 zeroFact 3 ⟨zeroFact, false⟩) :=
    D.step e2z (s := s3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)
  have hE4 : (0, 3, Instr.stmt s4, 4) ∈ P2.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hE5 : (0, 4, Instr.call c2, 5) ∈ P2.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have e4 : D2 (.edge 0 zeroFact 4 ⟨⟨w, [], .exact, .conc T2⟩, true⟩) :=
    D.step e3 (s := s4) hE4 (by decide)
  have e4v : D2 (.edge 0 zeroFact 4 ⟨⟨v, [], .exact, .conc T2⟩, false⟩) :=
    D.step e3z (s := s4) hE4 (by decide)
  -- the spurious added fact y2/T2 (demand) and its request answer j
  have ad : D2 (.added 1 jAns) :=
    D.added (a := ⟨jAns, true⟩) (c := c2) (n' := 5)
      (e := (⟨w, [], st, .star⟩, ⟨y2, [], st, .star⟩)) e4 hE5 (List.Mem.head _) (by decide)
  have i0 : D2 (.init 1 kReq) := by
    have := D.initA ad
    have hp : policy dem 1 jAns = kReq := by decide
    rw [hp] at this; exact this
  have s0 : D2 (.edge 1 kReq 20 ⟨kReq, false⟩) := D.start i0
  have rq : D2 (.req 1 kReq T2) := D.reqSink s0 (s := sinkPat2) (List.Mem.head _) (by decide)
  have ia : D2 (.init 1 jAns) := D.answer rq ad rfl (by decide)
  have sa : D2 (.edge 1 jAns 20 ⟨jAns, false⟩) := D.start ia
  -- the weak support through the REAL normal fact y/T2
  have sup : WeakSup P2 cnt 1 (policy dem) sinks2 [0] 1 jAns := by
    refine WeakSup.call (WeakSup.root (by decide)) e4v rfl hE5
      (e := (⟨v, [], st, .star⟩, ⟨y, [], st, .star⟩))
      (List.Mem.tail _ (List.Mem.head _))
      (a := ⟨⟨y, [], .exact, .conc T2⟩, false⟩) (by decide) rfl ia
      (Or.inr ⟨kReq, T2, rq, rfl, rfl, by decide, rfl⟩)
  exact ⟨jAns, ⟨jAns, false⟩, sa, sup, rfl, List.Mem.head _, by decide⟩

#print axioms weak_confirmed

theorem step_s4 {l l' : Loc} (hg : Good l) (hs : s4.step l l') : Good l' := by
  rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
  · exact hg
  · cases he with
    | head =>
      obtain ⟨_, hb, _⟩ := hd
      exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
    | tail _ he =>
      cases he with
      | head =>
        obtain ⟨_, hb, _⟩ := hd
        exact good_of_base (by rw [hb]; decide) (by rw [hb]; decide) (by rw [hb]; decide)
      | tail _ he => cases he

theorem flow_good2 {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P2 M l0 n l) (h0 : Good l0) : Good l := by
  induction hf with
  | start => exact h0
  | step _ hE hs ih =>
    have ih := ih h0
    cases hE with
    | head => exact step_s1 ih hs
    | tail _ hE =>
      cases hE with
      | head => exact step_s2 ih hs
      | tail _ hE =>
        cases hE with
        | head => exact step_s3 ih hs
        | tail _ hE =>
          cases hE with
          | head => exact step_s4 ih hs
          | tail _ hE =>
            cases hE with
            | tail _ hE => cases hE
  | pass _ _ _ ih => exact ih h0
  | call _ hE _ _ _ he2 _ _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => cases he2
            | tail _ hE => cases hE
  | clean _ hE _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | filt _ hE _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE

/-- Method 1 has no instruction: a flow in it stays at the entry location. -/
theorem flow_callee {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : Flow P2 M l0 n l) (hM : M = 1) : l = l0 := by
  induction hf with
  | start => rfl
  | step _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | pass _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | call _ hE _ _ _ _ _ _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | clean _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | filt _ hE _ _ =>
    subst hM
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE

theorem reach2 {M : MethodId} {n : Node} {l : Loc} (hr : Reach P2 [0] M n l) :
    (M = 0 ∧ Good l) ∨ (M = 1 ∧ l.base = y) := by
  induction hr with
  | root hM hf =>
    cases hM with
    | head => exact Or.inl ⟨rfl, flow_good2 hf (good_of_base (by decide) (by decide) (by decide))⟩
    | tail _ hM => cases hM
  | down _ hE he hd hf ih =>
    rcases ih with ⟨rfl, hg⟩ | ⟨rfl, _⟩
    · cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE with
              | head =>
                cases he with
                | head => exact absurd hd.1 hg.1
                | tail _ he =>
                  cases he with
                  | head =>
                    right
                    refine ⟨rfl, ?_⟩
                    rw [flow_callee hf rfl]
                    exact hd.2.1
                  | tail _ he => cases he
              | tail _ hE => cases hE
    · cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE with
              | tail _ hE => cases hE

/-- The weakly confirmed vulnerability is NOT real: no location reaches `sink(y2)`. -/
theorem weak_not_real : ¬ ∃ l, Reach P2 [0] 1 20 l ∧ sinkPat2.covers l := by
  rintro ⟨l, hR, hc⟩
  rcases reach2 hR with ⟨h1, _⟩ | ⟨_, hb⟩
  · exact absurd h1 (by decide)
  · have hb2 : l.base = y2 := hc.1
    rw [hb] at hb2
    exact absurd hb2 (by decide)

/-- THE GAP: with the weak side condition, `confirmed_real` is false. -/
theorem weak_support_gap :
    P2.WF ∧ WeakConfirmed P2 cnt 1 (policy dem) sinks2 [0] 1 20 sinkPat2 ∧
      ¬ ∃ l, Reach P2 [0] 1 20 l ∧ sinkPat2.covers l :=
  ⟨P2_wf, weak_confirmed, weak_not_real⟩

#print axioms weak_support_gap

/-- THE GAP under the round-5 hypotheses: `P2` also satisfies `MarkWF` and `FiltUp`, so the
    weak side condition breaks `confirmed_real` in its round-5 form too. -/
theorem weak_support_gap_exact :
    P2.WF ∧ Exact.MarkWF P2 ∧ Exact.FiltUp P2 ∧
      WeakConfirmed P2 cnt 1 (policy dem) sinks2 [0] 1 20 sinkPat2 ∧
      ¬ ∃ l, Reach P2 [0] 1 20 l ∧ sinkPat2.covers l :=
  ⟨P2_wf, P2_markWF, P2_filtUp, weak_confirmed, weak_not_real⟩

#print axioms weak_support_gap_exact

end Weak

end ApSpec.Confirmed
