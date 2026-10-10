/-
  General F75 normal-edge exactness. This module proves the closure rules
  directly with BaseCleaner.cleanRes. No historical closure embedding is used.
  The program mark, filter, validity, record and zero-binding hypotheses remain
  explicit. Reversal additionally requires reversible statements/calls and an
  empty premise exclusion; CurrentHandoff derives that exclusion from demands.
-/
import ApSpec.CurrentDefs
import ApSpec.AbsExact

namespace ApSpec.Current
open ApSpec ApSpec.Handoff ApSpec.Reverse

/-- Abstract cleaner outputs keep abstract marks. -/
theorem cleanRes_abs {cl : Cleaner} {c r : AFact}
    (hc : Exact.absB c.fact.mark = true)
    (hr : r ∈ (BaseCleaner.cleanRes cl c).facts) : Exact.absB r.fact.mark = true := by
  rcases BaseCleaner.result_cases hr with ⟨t, hm, _, _, rfl⟩ | hold
  · cases h : c.fact.mark with
    | conc m => simp [Exact.absB, h] at hm
    | star => simp [BaseCleaner.residual, h, addEx, Exact.absB]
    | starEx xs => simp [BaseCleaner.residual, h, addEx, Exact.absB]
  · exact Exact.cleanRes_abs hc hold

/-- Cleaner outputs preserve W2, including their layer. -/
theorem cleanRes_Legal {cl : Cleaner} {c r : AFact} (hc : Invariant.Legal c)
    (hr : r ∈ (BaseCleaner.cleanRes cl c).facts) : Invariant.Legal r := by
  rcases BaseCleaner.result_cases hr with ⟨t, _, _, _, rfl⟩ | hold
  · intro e hk
    exact ⟨Invariant.addEx_abs (hc e hk).1 t, (hc e hk).2⟩
  · exact Invariant.cleanRes_Legal hc hold

/-- Mark exclusion does not change the field-tail invariant. -/
theorem cleanRes_Q {ei : Excl} {cl : Cleaner} {c r : AFact} (hc : Invariant.Q ei c)
    (hr : r ∈ (BaseCleaner.cleanRes cl c).facts) : Invariant.Q ei r := by
  rcases BaseCleaner.result_cases hr with ⟨_, _, _, _, rfl⟩ | hold
  · exact hc
  · exact Invariant.cleanRes_Q hc hold

/-- A concrete input still has a concrete output, when an output exists. -/
theorem cleanRes_mark_conc {cl : Cleaner} {c r : AFact} {t : Mark}
    (hc : c.fact.mark = .conc t)
    (hr : r ∈ (BaseCleaner.cleanRes cl c).facts) : ∃ u, r.fact.mark = .conc u := by
  rw [BaseCleaner.concrete_unchanged hc] at hr
  exact ApSpec.cleanRes_mark_conc hc hr

end ApSpec.Current

namespace ApSpec.Exact
open ApSpec ApSpec.Current ApSpec.Handoff ApSpec.Reverse
theorem RC_edgeOK {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {ok : Loc → Prop} (hmw : MarkWF P) (hfo : FiltOK P ok)
    (hbo : BackOK P ok) {o : Obj} (h : Current.RC P counted L α sinks roots o) : EdgeOK P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, ?_⟩
    intro ha l0 l hd hok
    have e := startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    refine ⟨fun hi => transfer_abs (hmw.stmt _ _ _ _ hE) (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := transfer_demand hf ha
    obtain ⟨l1, hd1, hs⟩ := transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    refine ⟨fun hi => ?_, ?_⟩
    · -- the mark invariant
      have hA := applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD.1 hi) ha
      obtain ⟨x, hx, hxm⟩ := applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := applyEdge_mark hx
      have hG := ihG.1 (gate_abs hgx hA)
      have hR : absB r.fact.mark = true := by rw [hxm]; exact comp_abs hG hA hcx
      rw [limitF_mark]
      exact applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · intro hla l0 l hd hok
      have e := limitF_exact hla
      rw [e] at hd hla
      have hra := applyEdge_demand hr' hla
      -- the binding back to the caller
      obtain ⟨hp3, hc3⟩ := markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      -- the summary edge
      obtain ⟨x, hx, rfl⟩ := applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := or_eq_false hra
      have haa := applyEdge_demand hx hxa
      have hfa := applyEdge_demand ha haa
      have hp2 : premOKB j.mark a.fact.mark = true := premOK_of_sub (applicable_markSub happ)
      have hc2 : concOKB g.fact.mark a.fact.mark = true :=
        concOK_of (fun hA => ihG.1 (gate_abs (applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      -- the binding into the callee
      obtain ⟨hp1, hc1⟩ := markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihD.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨fun hi => Current.cleanRes_abs (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := BaseCleaner.normal_input hf ha
    obtain ⟨hd1, hcl⟩ := BaseCleaner.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

end ApSpec.Exact

namespace ApSpec.RExact
open ApSpec ApSpec.Current ApSpec.Handoff ApSpec.Reverse
variable {P Pb : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
theorem FC_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hfo : Exact.FiltOK P ok)
    (hbo : Exact.BackOK P ok) (hsat : SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RecsExactV P ok recs) {o : Obj}
    (h : Current.FC P counted L demand emit sat restrict recs sinks roots o) : EdgeOKR P ok o := by
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
    -- `RecsExactV`: the motive holds on the record. The record applies by `sat` (`SatMark`) or
    -- by `applicable` (the premise covers the caller fact): both give the sub-mark
    -- `markSubB j.mark a.fact.mark` that `summary_ok` needs (as in the rule `ret` of `D`)
    exact summary_ok hmw hbo hE he1 ha (recApp_markSub hsat hs) hr he2 hr' ihD
      (hrecs c.callee j g hrec)
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    intro ha
    have hfa := BaseCleaner.normal_input hf ha
    obtain ⟨ih1, ih2⟩ := ih hfa
    refine ⟨fun hi => Current.cleanRes_abs (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨hd1, hcl⟩ := BaseCleaner.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | @filt M i n f n' b may _ hE hp ih =>
    intro ha
    obtain ⟨ih1, ih2⟩ := ih ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

end ApSpec.RExact

namespace ApSpec.BExact
open ApSpec ApSpec.Current ApSpec.Handoff ApSpec.Reverse ApSpec.Backward
variable {P Pb : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
theorem BC_edgeOK {ok : Loc → Prop} (hmw : Exact.MarkWF Pb) (hfo : Exact.FiltOK Pb ok)
    (hbo : Exact.BackOK Pb ok) (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hnz : NoZeroIn Pb) (hrecs : RecsExactVNZ Pb ok recs) {o : Obj}
    (h : Current.BC Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    EdgeOKNZ Pb ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro _ ha
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, fun l0 l hd hok => ?_⟩
    have e := Exact.startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    intro hz ha
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨ih1, ih2⟩ := ih hz hfa
    refine ⟨fun hi => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih2 l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE hs, hok0⟩
  | @pass M i n f n' c _ hE hm ih =>
    intro hz ha
    obtain ⟨ih1, ih2⟩ := ih hz ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ hres hs hr he2 hr' ihD _ ihG =>
    intro hz
    -- the callee premise is off the zero base: its edges have a non-zero premise
    have hjz : j ≠ zeroFact := ne_zero_of_base (no_zero_summary hnz hE he1 ha hr)
    obtain ⟨hgd, hgsub⟩ := hsub j g d g' hres
    have ihG' : RExact.EdgeOKR Pb ok (.edge c.callee j (Pb.exit c.callee) g') := by
      intro hg'
      obtain ⟨h1, h2⟩ := ihG hjz (hgd.symm.trans hg')
      exact ⟨fun hJ => RExact.abs_of_sub hJ (h1 hJ) hgsub,
        fun l1 l2 hd hok => h2 l1 l2 (hgsub l1 l2 hd) hok⟩
    exact RExact.summary_ok hmw hbo hE he1 ha (hsat j a.fact hs) hr he2 hr' (ihD hz) ihG'
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hs hr he2 hr' ihD =>
    intro hz
    exact RExact.summary_ok hmw hbo hE he1 ha (RExact.recApp_markSub hsat hs) hr he2 hr' (ihD hz)
      (hrecs c.callee j g hrec (no_zero_summary hnz hE he1 ha hr))
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    intro hz ha
    have hfa := BaseCleaner.normal_input hf ha
    obtain ⟨ih1, ih2⟩ := ih hz hfa
    refine ⟨fun hi => Current.cleanRes_abs (ih1 hi) hf, fun l0 l hd hok => ?_⟩
    obtain ⟨hd1, hcl⟩ := BaseCleaner.cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | @filt M i n f n' b may _ hE hp ih =>
    intro hz ha
    obtain ⟨ih1, ih2⟩ := ih hz ha
    refine ⟨ih1, fun l0 l hd hok => ?_⟩
    obtain ⟨hfl, hok0⟩ := ih2 l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb
  -- the zero rules make edges of the zero premise only
  | zpass => exact fun hz => absurd rfl hz
  | zin => trivial
  | seed => exact fun hz => absurd rfl hz
  | zret => exact fun hz => absurd rfl hz

end ApSpec.BExact

namespace ApSpec.Current
open ApSpec ApSpec.Abs ApSpec.Handoff ApSpec.Reverse

/-- Executable concrete-mark witness for a cleaner output. -/
def cleanRes_concrete_witness {cl : Cleaner} {c r : AFact} {t : Mark}
    (hc : c.fact.mark = .conc t)
    (hr : r ∈ (BaseCleaner.cleanRes cl c).facts) :
    { u : Mark // r.fact.mark = .conc u } :=
  match hm : r.fact.mark with
  | .conc u => ⟨u, rfl⟩
  | .star => False.elim (by
      obtain ⟨u, hu⟩ := cleanRes_mark_conc hc hr
      rw [hm] at hu
      cases hu)
  | .starEx xs => False.elim (by
      obtain ⟨u, hu⟩ := cleanRes_mark_conc hc hr
      rw [hm] at hu
      cases hu)

section Run1
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

theorem RC_edge_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : RC P counted L α sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow P M l0 n l ∧ ok l0 :=
  (Exact.RC_edgeOK hmw (Exact.filtValid_ok hv) hbo h).2 hn l0 l hd hok

theorem RC_edge_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : RC P counted L α sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  ((Exact.RC_edgeOK hmw (Exact.filtUp_ok hup) (Exact.backOK_true P) h).2
    hn l0 l hd trivial).1

theorem RC_records_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) :
    RExact.RecsExact P (RExact.exitRecs P (RC P counted L α sinks roots)) :=
  fun _ _ _ h hn _ _ hd => RC_edge_exact hmw hup h hn hd

end Run1

section Forward
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

theorem FW_edge_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : FW P counted L dem rc sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  ((RExact.FC_edgeOK hmw (Exact.filtUp_ok hup) (Exact.backOK_true P)
    satW_SatMark restrictI_sub (hrecs.toV hmw) h hn).2 l0 l hd trivial).1

theorem FW_edge_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : FW P counted L dem rc sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow P M l0 n l ∧ ok l0 :=
  (RExact.FC_edgeOK hmw (Exact.filtValid_ok hv) hbo
    satW_SatMark restrictI_sub hrecs h hn).2 l0 l hd hok

theorem FW_records_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P rc) :
    RExact.RecsExact P (RExact.exitRecs P (FW P counted L dem rc sinks roots)) :=
  fun _ _ _ h hn _ _ hd => FW_edge_exact hmw hup hrecs h hn hd

theorem FW_records_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok rc) :
    RExact.RecsExactV P ok (RExact.exitRecs P (FW P counted L dem rc sinks roots)) :=
  fun _ _ _ h => RExact.FC_edgeOK hmw (Exact.filtValid_ok hv) hbo
    satW_SatMark restrictI_sub hrecs h

end Forward

section Backward
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {roots : List MethodId} {seeds : List (MethodId × Node × PFact)}

theorem BW_edge_exact (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactNZ Pb rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : BW Pb counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) (hd : den i f.fact l0 l) :
    Flow Pb M l0 n l :=
  ((BExact.BC_edgeOK hmw (Exact.filtUp_ok hup) (Exact.backOK_true Pb)
    satW_SatMark restrictI_sub hnz (hrecs.toV hmw) h hi hn).2 l0 l hd trivial).1

theorem BW_edge_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF Pb)
    (hv : Exact.FiltValid Pb ok) (hbo : Exact.BackOK Pb ok)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactVNZ Pb ok rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : BW Pb counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow Pb M l0 n l ∧ ok l0 :=
  (BExact.BC_edgeOK hmw (Exact.filtValid_ok hv) hbo satW_SatMark
    restrictI_sub hnz hrecs h hi hn).2 l0 l hd hok

theorem BW_records_exact (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactNZ Pb rc) :
    BExact.RecsExactNZ Pb (RExact.exitRecs Pb (BW Pb counted L dem rc roots seeds)) :=
  fun _ _ _ h hi hn _ _ hd =>
    BW_edge_exact hmw hup hnz hrecs h (BExact.ne_zero_of_base hi) hn hd

end Backward

section Reversal
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {roots : List MethodId} {seeds : List (MethodId × Node × PFact)}

theorem BW_normal_markRev (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hnz : Backward.NoZeroBack P) (hrecs : BExact.RecsExactNZ (Program.rev P) rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : BW (Program.rev P) counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) : MarkRev i f.fact := by
  rcases RAux.mark_conc_or_abs i.mark with hc | ha
  · exact Or.inr hc
  · have hmwB := BExact.markWF_rev hmw
    have hf := BExact.BC_edgeOK hmwB (Exact.filtUp_ok (BExact.filtUp_rev hup))
      (Exact.backOK_true (Program.rev P)) satW_SatMark restrictI_sub
      (BExact.noZeroIn_rev hnz) (hrecs.toV hmwB) h
    exact Or.inl (Kinds.absB_iff.mp ((hf hi hn).1 (Kinds.absB_iff.mpr ha)))

/-- Every pair of the reversed normal record is a real forward callee flow. -/
theorem BW_rev_record_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hnz : Backward.NoZeroBack P) (hR : RevStmts P) (hC : RevCalls P)
    (hrecs : BExact.RecsExactNZ (Program.rev P) rc)
    {M : MethodId} {jb : PFact} {gb : AFact} {l l0 : Loc}
    (h : BW (Program.rev P) counted L dem rc roots seeds
      (.edge M jb ((Program.rev P).exit M) gb))
    (hi : jb ≠ zeroFact) (hn : gb.demand = false) (hpe : PremEmpty jb.kind)
    (hd : den (revEdge jb gb.fact).1 (revEdge jb gb.fact).2 l l0) :
    Flow P M l (P.exit M) l0 := by
  have hb : den jb gb.fact l0 l :=
    (rev_exact_of_empty_premise hpe (BW_normal_markRev hmw hup hnz hrecs h hi hn)).mpr hd
  exact (flow_rev_iff_calls hR hC).mpr
    (BW_edge_exact (BExact.markWF_rev hmw) (BExact.filtUp_rev hup)
      (BExact.noZeroIn_rev hnz) hrecs h hi hn hb)

end Reversal

#print axioms RC_edge_exact
#print axioms FW_edge_exact
#print axioms BW_edge_exact
#print axioms BW_rev_record_exact
#print axioms cleanRes_concrete_witness
end ApSpec.Current

namespace ApSpec.Current
open ApSpec ApSpec.Handoff ApSpec.Reverse

theorem crossK_premEmpty {k : Kind} (h : CrossK k) : PremEmpty k := by
  cases k with
  | exact => trivial
  | any => exact h.elim
  | star e => exact h

/-- Crossable stored native records, read through the actual reversal. -/
def crossRevRecs (rc : Recs) : Recs := fun M rec =>
  ∃ j g,rc M (j,g) ∧ Cross j g ∧ rec = revRec (j,g)

/-- Exact native records give exact reverse reads. This applies to every
    eligible raw forward exit record before summary reduction. -/
theorem crossRevRecs_exact {P : Program} {rc : Recs}
    (hR : RevStmts P) (hC : RevCalls P) (hr : RExact.RecsExact P rc) :
    RExact.RecsExact (Program.rev P) (crossRevRecs rc) := by
  intro M j g hrec _ l0 l hd
  obtain ⟨j0,g0,hg,hcross,he⟩ := hrec
  cases he
  have hd0 : den j0 g0.fact l l0 :=
    (rev_exact_of_empty_premise (crossK_premEmpty hcross.2.1) hcross.2.2.1).mpr hd
  exact (flow_rev_iff_calls hR hC).mp (hr M j0 g0 hg hcross.1 l l0 hd0)

#print axioms crossRevRecs_exact
end ApSpec.Current

namespace ApSpec.Current
open ApSpec ApSpec.Handoff ApSpec.Abs

/-- Run-1 native records also preserve the validity-aware exactness contract. -/
theorem RC_records_exact_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok) :
    RExact.RecsExactV P ok (RExact.exitRecs P (RC P counted L α sinks roots)) := by
  intro M j g hg hn
  have hk := Exact.RC_edgeOK hmw (Exact.filtValid_ok hv) hbo hg
  exact ⟨hk.1,hk.2 hn⟩

/-- Backward native records preserve validity-aware exactness off zero. -/
theorem BW_records_exact_valid {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {ok : Loc → Prop}
    (hmw : Exact.MarkWF Pb) (hv : Exact.FiltValid Pb ok) (hbo : Exact.BackOK Pb ok)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactVNZ Pb ok rc) :
    BExact.RecsExactVNZ Pb ok (RExact.exitRecs Pb (BW Pb counted L dem rc roots seeds)) := by
  intro M j g hg hj
  exact BExact.BC_edgeOK hmw (Exact.filtValid_ok hv) hbo satW_SatMark restrictI_sub
    hnz hrecs hg (BExact.ne_zero_of_base hj)

end ApSpec.Current
