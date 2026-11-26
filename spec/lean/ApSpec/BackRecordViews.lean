import ApSpec.BackMustRun
import ApSpec.CurrentMustReverse

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

end ApSpec.BackView

#print axioms ApSpec.BackView.backExactView_forward
