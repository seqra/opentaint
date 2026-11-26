import ApSpec.BackMustRun
import ApSpec.CurrentMustReverse
import ApSpec.FieldQuant

/-!
# Record reversal, case 4: a backward `$`-premise record with an `[any-taint]` conclusion

Spec `backward-condition-progress.md` §I.8, case 4 (NEW with B1 and B2): the backward record
`backward: ret.$(T) → arg.[any-taint]/E(U)` (a reversed unary conditional source, row S3) is read by
the forward run as the view `arg.*/E(U) → ret.$(T)` in the NORMAL layer.

`backExactView_forward`: every pair of that view is a flow of the forward program. It composes
`CurrentMustReverse.exact_converse` (the view relation is the converse of the record relation) with
`BackMust.backPair_forward` (every pair of a NORMAL non-must backward edge with a non-zero premise is
a forward flow).
-/

namespace ApSpec.BackView

open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.AnyTaintExExact ApSpec.Reverse ApSpec.Backward
  ApSpec.BExact ApSpec.BackMust

variable {P : Program} {bmay : BMay} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact × Bool)}

/-- Case 4: the forward view `xb.xp.*/gex(t) → pb.pp.$(u)` of a NORMAL backward record
    `pb.pp.$(u) → xb.xp.[any-taint]/gex(t)` relates only forward flows of `P`. -/
theorem backExactView_forward (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {pb xb : Base} {pp xp : List Acc} {u t : Mark} {jex gex : Excl}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M ⟨pb, pp, .exact, .conc u⟩ false jex ((Program.rev P).exit M)
        ⟨⟨⟨xb, xp, .any, .conc t⟩, false⟩, gex⟩))
    (hjb : (⟨pb, pp, .exact, .conc u⟩ : PFact) ≠ zeroFact) :
    ∀ l1 l0, den ⟨xb, xp, .star gex, .conc t⟩ ⟨pb, pp, .exact, .conc u⟩ l1 l0 →
      Flow P M l1 (P.exit M) l0 := by
  intro l1 l0 hd
  exact backPair_forward hmw hup hNZB hR hC hin hsub hem hsd hrecs hrc hrw h hjb rfl l0 l1
    (CurrentMustReverse.exact_converse.mpr hd)

/-! ## Record ends as field quantifiers (spec §N.6, §I.7, §I.8)

The NORMAL records of both runs are valid edges of `FieldQuant` for the forward flow relation of the
method. A forward record reads its `[any-taint]` ends as `[all-fields]`, a backward record as
`[any-field]`. Then `FieldQuant.fwd_apply` and `FieldQuant.bwd_apply` apply each record in each run. -/

/-- The forward flows of method `M`: entry location `a` to exit location `r`. -/
def fwdFlow (P : Program) (M : MethodId) (a r : Loc) : Prop := Flow P M a (P.exit M) r

/-- An exact premise location relates to each location of an `.any` conclusion. -/
theorem denX_exact_any {pb xb : Base} {pp xp : List Acc} {u t : Mark} {iex fex : Excl} {l : Loc}
    (hl : coversFX ⟨xb, xp, .any, .conc t⟩ fex l) :
    denX ⟨pb, pp, .exact, .conc u⟩ iex ⟨xb, xp, .any, .conc t⟩ fex ⟨pb, pp, u⟩ l := by
  obtain ⟨hb, ⟨τ, hp, _, he⟩, t', ht, hm⟩ := hl
  cases ht
  exact ⟨rfl, hb, rfl, hm, trivial, [], τ, (List.append_nil pp).symm, hp, rfl, trivial,
    by cases iex <;> rfl, he⟩

/-- Forward `arg.$(u) → ret.[all-fields]/fex(t)` NORMAL (pair-exact) is the valid edge
    `$ → [all-fields]`. -/
theorem fwd_pair_valid {P : Program} {M : MethodId} {pb xb : Base} {pp xp : List Acc} {u t : Mark}
    {iex fex : Excl}
    (h : EdgeOKX P (fun _ => True)
      (.edge M ⟨pb, pp, .exact, .conc u⟩ false iex (P.exit M) ⟨⟨⟨xb, xp, .any, .conc t⟩, false⟩, fex⟩)) :
    FieldQuant.Valid (fwdFlow P M) (.one ⟨pb, pp, u⟩) (.allFields (coversFX ⟨xb, xp, .any, .conc t⟩ fex)) :=
  (FieldQuant.valid_one _ _ _).mpr fun _ hr => ((h rfl).2 _ _ (denX_exact_any hr) trivial).1

/-- Forward `arg.[all-fields] →must ret.…` NORMAL (end-exact) is the valid edge
    `[all-fields] → [all-fields]` (a `$` conclusion covers one location). -/
theorem fwd_must_valid {P : Program} {M : MethodId} {i : PFact} {iex : Excl} {f : XFact}
    (h : EdgeOKX P (fun _ => True) (.edge M i true iex (P.exit M) f)) (hg : f.af.demand = false) :
    FieldQuant.Valid (fwdFlow P M) (.allFields (coversX i iex)) (.allFields (coversFX f.af.fact f.ex)) :=
  (FieldQuant.valid_all _ _ _).mpr fun r hr =>
    let ⟨a, ha, hf, _⟩ := (h hg).2 r hr trivial
    ⟨a, ha, hf⟩

/-- Backward `ret.$(u) → arg.[any-field]/gex(t)` NORMAL (§I.8 case 4) is the valid edge
    `[any-field] → $` in the forward orientation. -/
theorem bwd_pair_valid (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {pb xb : Base} {pp xp : List Acc} {u t : Mark} {jex gex : Excl}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M ⟨pb, pp, .exact, .conc u⟩ false jex ((Program.rev P).exit M)
        ⟨⟨⟨xb, xp, .any, .conc t⟩, false⟩, gex⟩))
    (hjb : (⟨pb, pp, .exact, .conc u⟩ : PFact) ≠ zeroFact) :
    FieldQuant.Valid (fwdFlow P M) (.anyField (coversFX ⟨xb, xp, .any, .conc t⟩ gex)) (.one ⟨pb, pp, u⟩) :=
  (FieldQuant.valid_any _ _ _).mpr fun _ ha =>
    backPair_forward hmw hup hNZB hR hC hin hsub hem hsd hrecs hrc hrw h hjb rfl _ _ (denX_exact_any ha)

/-- Backward `ret.[any-field] →must arg.…` NORMAL (§I.8 cases 3, 3') is the valid edge
    `[any-field] → [any-field]` in the forward orientation (a `$` end covers one location). -/
theorem bwd_must_valid (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M jb true jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false) :
    FieldQuant.Valid (fwdFlow P M) (.anyField (coversFX gb.af.fact gb.ex)) (.anyField (coversX jb jex)) :=
  (FieldQuant.valid_any _ _ _).mpr fun a ha =>
    let ⟨r, hr, hf⟩ := backMust_forward hmw hup hNZB hR hC hin hsub hem hsd hrecs hrc hrw h hjb hg a ha
    ⟨r, hr, hf⟩

/-- §I.8 case 2 with the new application: a backward requirement `R` at the forward exit that the
    forward must record's conclusion implies gives the NORMAL requirement `[all-fields]` on the
    record premise. -/
theorem fwdMust_backward_normal {P : Program} {M : MethodId} {i : PFact} {iex : Excl} {f : XFact}
    {R : FieldQuant.End Loc} {G : (Loc → Prop) → Prop}
    (h : EdgeOKX P (fun _ => True) (.edge M i true iex (P.exit M) f)) (hg : f.af.demand = false)
    (hi : FieldQuant.Impl (.allFields (coversFX f.af.fact f.ex)) R) (hr : FieldQuant.Req G R) :
    FieldQuant.Req (fun σ => G (FieldQuant.post (fwdFlow P M) σ)) (.allFields (coversX i iex)) :=
  FieldQuant.bwd_apply (fwd_must_valid h hg) hi hr

/-- §I.8 case 3 with the new application: a forward claim `A` at the forward entry that implies the
    backward must record's conclusion gives the NORMAL forward claim `[any-field]` on the record
    premise. -/
theorem backMust_forward_normal (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hNZB : NoZeroBack P)
    (hR : RevStmts P) (hC : RevCalls P) (hin : SatInsideX sat) (hsub : RestrictOKX restrict)
    (hem : EmitCopiesMarkX emit) (hsd : SeedsConcB seeds)
    (hrecs : RecsExactXNZ (Program.rev P) (fun _ => True) recs) (hrc : RecsConcXNZ recs)
    (hrw : RecsWFXNZ recs)
    {M : MethodId} {jb : PFact} {jex : Excl} {gb : XFact}
    (h : DBX (Program.rev P) bmay counted L demand emit sat restrict recs sinks roots seeds
      (.edge M jb true jex ((Program.rev P).exit M) gb))
    (hjb : jb ≠ zeroFact) (hg : gb.af.demand = false)
    {A : FieldQuant.End Loc} {σ : Loc → Prop}
    (hi : FieldQuant.Impl A (.anyField (coversFX gb.af.fact gb.ex))) (ha : FieldQuant.holds σ A) :
    FieldQuant.holds (FieldQuant.post (fwdFlow P M) σ) (.anyField (coversX jb jex)) :=
  FieldQuant.fwd_apply
    (bwd_must_valid hmw hup hNZB hR hC hin hsub hem hsd hrecs hrc hrw h hjb hg) hi ha

end ApSpec.BackView

#print axioms ApSpec.BackView.backExactView_forward
#print axioms ApSpec.BackView.fwd_pair_valid
#print axioms ApSpec.BackView.fwd_must_valid
#print axioms ApSpec.BackView.bwd_pair_valid
#print axioms ApSpec.BackView.bwd_must_valid
#print axioms ApSpec.BackView.fwdMust_backward_normal
#print axioms ApSpec.BackView.backMust_forward_normal
