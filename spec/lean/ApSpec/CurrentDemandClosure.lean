/-
  Data-producing demand contracts for the F75 closures.

  CurrentHandoff derives the tail guard from the canonical base sequence.
  The concrete-added guard is required only for a concrete demand pattern;
  an abstract added fact deliberately cannot satisfy that demand. These local
  certificates do not assert global witness coverage or iteration preservation.
-/
import ApSpec.CurrentDemand
import ApSpec.CurrentHandoff

namespace ApSpec.CurrentDemand
open ApSpec ApSpec.Abs ApSpec.Handoff

/-- The supported-tail guard follows from the current handoff entry shape. -/
def emitUnderShape {dem : MethodId → DemandEdge → Prop} {M : MethodId}
    {d : DemandEdge} (shape : ApSpec.Current.EntryShape dem) (hd : dem M d)
    (a : PFact) (l : Loc)
    (concrete : d.din.mark ≠ .star → ∃ t, a.mark = .conc t)
    (demanded : d.din.covers l) (added : a.covers l) : Emission d.din a l :=
  emitCertificate d.din a l
    (fun _ => AbsHandoff.entryShape_PatTail shape hd) concrete demanded added

/-- A computed forward premise is an actual initial fact of the F75 closure. -/
def forwardEmission {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {d : DemandEdge} {a : PFact} {l : Loc}
    (shape : ApSpec.Current.EntryShape dem) (hd : dem M d)
    (ha : ApSpec.Current.FW P counted L dem rc sinks roots (.added M a))
    (concrete : d.din.mark ≠ .star → ∃ t, a.mark = .conc t)
    (demanded : d.din.covers l) (added : a.covers l) :
    {e : Emission d.din a l //
      ApSpec.Current.FW P counted L dem rc sinks roots (.init M e.premise)} :=
  let e := emitUnderShape shape hd a l concrete demanded added
  ⟨e, ApSpec.Current.FC.initR ha hd e.emitted⟩

/-- The same witness and guards apply in the current request-free backward run. -/
def backwardEmission {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)}
    {M : MethodId} {d : DemandEdge} {a : PFact} {l : Loc}
    (shape : ApSpec.Current.EntryShape dem) (hd : dem M d)
    (ha : ApSpec.Current.BW Pb counted L dem rc roots seeds (.added M a))
    (concrete : d.din.mark ≠ .star → ∃ t, a.mark = .conc t)
    (demanded : d.din.covers l) (added : a.covers l) :
    {e : Emission d.din a l //
      ApSpec.Current.BW Pb counted L dem rc roots seeds (.init M e.premise)} :=
  let e := emitUnderShape shape hd a l concrete demanded added
  ⟨e, ApSpec.Current.BC.initR ha hd e.emitted⟩

/-- A reduced actual exit edge is published by the same demand that emitted it. -/
def publishedReduction {P : Program} {R : Obj → Prop}
    {dem : MethodId → DemandEdge → Prop} {M : MethodId} {d : DemandEdge}
    {a : PFact} {l1 l2 : Loc} (hd : dem M d)
    (e : Emission d.din a l1) (g : AFact) (p : PFact)
    (actual : R (.edge M e.premise (P.exit M) g))
    (pair : den e.premise g.fact l1 l2) (exit : d.dout = some p)
    (demanded : p.covers l2) :
    {r : Reduction e.premise g d l1 l2 //
      R (.edge M e.premise (P.exit M) g) ∧
      pubR dem M e.premise g r.conclusion} :=
  let r := reduceEmission e g p pair exit demanded
  ⟨r, actual, d, hd, r.reduced⟩

/-- A paired exit with `$` came from a concrete premise in the preceding run. -/
def PairedExactExit (d : DemandEdge) : Prop :=
  ∀ p, d.dout = some p → p.kind = .exact → ∃ t, d.din.mark = .conc t

/-- The paired entry mark is selected by computation of `d.din.mark`. -/
def exactExitMarkWitness (d : DemandEdge) (p : PFact) (paired : PairedExactExit d)
    (exit : d.dout = some p) (exactTail : p.kind = .exact) :
    {t : Mark // d.din.mark = .conc t} :=
  match he : d.din.mark with
  | .conc t => ⟨t, rfl⟩
  | .star => False.elim (by
      obtain ⟨t, ht⟩ := paired p exit exactTail
      rw [he] at ht
      cases ht)
  | .starEx xs => False.elim (by
      obtain ⟨t, ht⟩ := paired p exit exactTail
      rw [he] at ht
      cases ht)

theorem inside_concrete_mark {j d : PFact} {t : Mark}
    (hi : insideB j d = true) (hd : d.mark = .conc t) : j.mark = .conc t := by
  have hm := insideB_mark hi
  rw [hd] at hm
  cases hj : j.mark with
  | star => rw [hj] at hm; cases hm
  | starEx xs => rw [hj] at hm; cases hm
  | conc u =>
    rw [hj] at hm
    have he : t = u := CoreAux.beq_iff.mp hm
    rw [he]

/-- The paired guard prevents reduction from creating an abstract `$` leaf.
    Raw FLOW shape and concrete-premise preservation are separate obligations. -/
theorem restriction_no_abstract_exact {j : PFact} {g g' : AFact} {d : DemandEdge}
    (paired : PairedExactExit d)
    (raw : Exact.absB g.fact.mark = true → g.fact.kind ≠ .exact)
    (concrete : (∃ t, j.mark = .conc t) → ∃ t, g.fact.mark = .conc t)
    (hr : restrictI j g d = some g') (hm : Exact.absB g'.fact.mark = true) :
    g'.fact.kind ≠ .exact := by
  obtain ⟨p, hp, hin, _, hc⟩ := restrictI_someM hr
  have hmark := restrictConcI_mark hc
  have hab : Exact.absB g.fact.mark = true := by rw [← hmark]; exact hm
  have hn := raw hab
  have noExitExact : p.kind ≠ .exact := by
    intro he
    obtain ⟨t, ht⟩ := paired p hp he
    have hj := inside_concrete_mark hin ht
    obtain ⟨u, hu⟩ := concrete ⟨t, hj⟩
    rw [hu] at hab
    cases hab
  obtain ⟨_, ⟨_, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, he⟩⟩ :=
    restrictConcI_cases hc
  · rw [he]
    cases hk : g.fact.kind with
    | star e => intro h; cases h
    | exact => exact (hn hk).elim
    | any => cases hpk : p.kind with
      | exact => exact (noExitExact hpk).elim
      | any => intro h; cases h
      | star e => intro h; cases h
  · rw [he]; exact hn
  · rw [he]
    cases hpk : p.kind with
    | exact => exact (noExitExact hpk).elim
    | any => intro h; cases h
    | star e => intro h; cases h
  · rw [he]; exact hn

/-- The conditional representation theorem for a reached current forward edge. -/
theorem forward_restriction_no_abstract_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {rc : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {n : Node} {g g' : AFact} {d : DemandEdge}
    (actual : ApSpec.Current.FC P counted L dem emitW sat restrict rc sinks roots (.edge M j n g))
    (paired : PairedExactExit d)
    (raw : Exact.absB g.fact.mark = true → g.fact.kind ≠ .exact)
    (hr : restrictI j g d = some g') (hm : Exact.absB g'.fact.mark = true) :
    g'.fact.kind ≠ .exact :=
  restriction_no_abstract_exact paired raw (ApSpec.Current.forward_concrete_premise actual) hr hm

/-- The same conditional theorem for reached current backward edges. -/
theorem backward_restriction_no_abstract_exact {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {rc : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    {M : MethodId} {j : PFact} {n : Node} {g g' : AFact} {d : DemandEdge}
    (seedsConcrete : ∀ M n s, (M, n, s) ∈ seeds → ∃ t, s.mark = .conc t)
    (actual : ApSpec.Current.BC Pb counted L dem emit sat restrict rc sinks roots seeds zbind
      (.edge M j n g))
    (paired : PairedExactExit d)
    (raw : Exact.absB g.fact.mark = true → g.fact.kind ≠ .exact)
    (hr : restrictI j g d = some g') (hm : Exact.absB g'.fact.mark = true) :
    g'.fact.kind ≠ .exact :=
  restriction_no_abstract_exact paired raw
    (ApSpec.Current.backward_concrete_premise seedsConcrete actual) hr hm

#print axioms emitUnderShape
#print axioms forwardEmission
#print axioms backwardEmission
#print axioms publishedReduction
#print axioms exactExitMarkWitness
#print axioms restriction_no_abstract_exact
#print axioms forward_restriction_no_abstract_exact
#print axioms backward_restriction_no_abstract_exact

end ApSpec.CurrentDemand
