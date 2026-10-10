/-
  Normal edges of the F72 closures are exact on valid locations.

  These results use the generic exactness proofs through the embeddings of DRA into DR and
  DBA into DB. They do not assume that emission copies the added mark. They apply to FLOW
  premises as well as concrete premises. The input records must satisfy the stated exactness
  contract. Reversal also needs an empty premise exclusion. This file does not prove that
  premise condition for the full iteration, the X-tail form, or coverage.
  The embeddings retain the pre-F75 spatial cleaner. The F75 closure exactness
  migration is pending; BaseCleaner proves its local normal-output exactness.
-/
import ApSpec.AbsDefs
import ApSpec.RestrictedExact
import ApSpec.BackwardExact
import ApSpec.Kinds

namespace ApSpec.Abs
open ApSpec ApSpec.Handoff ApSpec.Reverse

theorem satW_SatMark : RExact.SatMark satW :=
  fun _ _ h => satW_markSub h

#print axioms satW_SatMark

section Forward
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- L5, forward: every normal edge, including an edge of a FLOW premise, denotes real flows. -/
theorem DRW_edge_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DRW P counted L dem rc sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  RExact.edge_exactR hmw hup satW_SatMark restrictI_sub hrecs (DRA_sub_DR P counted L dem emitW satW restrictI rc sinks roots h) hn hd

#print axioms DRW_edge_exact

/-- L5, forward with type filters: exactness is restricted to valid end locations. -/
theorem DRW_edge_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DRW P counted L dem rc sinks roots (.edge M i n f))
    (hn : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow P M l0 n l ∧ ok l0 :=
  RExact.edge_exactR_valid hmw hv hbo satW_SatMark restrictI_sub hrecs
    (DRA_sub_DR P counted L dem emitW satW restrictI rc sinks roots h) hn hd hok

#print axioms DRW_edge_exact_valid

/-- The normal exit edges of a forward F72 run satisfy the same record contract. -/
theorem DRW_records_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P rc) :
    RExact.RecsExact P (RExact.exitRecs P (DRW P counted L dem rc sinks roots)) :=
  fun _ _ _ h hn _ _ hd => DRW_edge_exact hmw hup hrecs h hn hd

#print axioms DRW_records_exact

/-- A forward F72 run also preserves the record contract with type filters. -/
theorem DRW_records_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok rc) :
    RExact.RecsExactV P ok (RExact.exitRecs P (DRW P counted L dem rc sinks roots)) :=
  fun _ _ _ h => RExact.DR_edgeOK hmw (Exact.filtValid_ok hv) hbo satW_SatMark
    restrictI_sub hrecs (DRA_sub_DR P counted L dem emitW satW restrictI rc sinks roots h)

#print axioms DRW_records_exact_valid

end Forward

section Backward
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {roots : List MethodId} {seeds : List (MethodId × Node × PFact)}

/-- L5, backward: normal edges with a nonzero premise are exact in the backward program. -/
theorem DBW_edge_exact (hmw : Exact.MarkWF Pb) (hup : Exact.FiltUp Pb)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactNZ Pb rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DBW Pb counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) (hd : den i f.fact l0 l) :
    Flow Pb M l0 n l :=
  BExact.edge_exactB hmw hup satW_SatMark restrictI_sub hnz hrecs (DBA_sub_DB Pb counted L dem emitW satW restrictI rc [] roots seeds true h) hi hn hd

#print axioms DBW_edge_exact

/-- The backward exactness contract with type filters has the same validity conditions. -/
theorem DBW_edge_exact_valid {ok : Loc → Prop} (hmw : Exact.MarkWF Pb)
    (hv : Exact.FiltValid Pb ok) (hbo : Exact.BackOK Pb ok)
    (hnz : BExact.NoZeroIn Pb) (hrecs : BExact.RecsExactVNZ Pb ok rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DBW Pb counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) :
    Flow Pb M l0 n l ∧ ok l0 :=
  BExact.edge_exactB_valid hmw hv hbo satW_SatMark restrictI_sub hnz hrecs
    (DBA_sub_DB Pb counted L dem emitW satW restrictI rc [] roots seeds true h) hi hn hd hok

#print axioms DBW_edge_exact_valid

end Backward

section Reversal
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {rc : Recs}
  {roots : List MethodId} {seeds : List (MethodId × Node × PFact)}

/-- A normal nonzero backward edge is mark-reversible, also for a FLOW premise. -/
theorem DBW_normal_markRev (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hnz : Backward.NoZeroBack P) (hrecs : BExact.RecsExactNZ (Program.rev P) rc)
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DBW (Program.rev P) counted L dem rc roots seeds (.edge M i n f))
    (hi : i ≠ zeroFact) (hn : f.demand = false) : MarkRev i f.fact := by
  rcases RAux.mark_conc_or_abs i.mark with hc | ha
  · exact Or.inr hc
  · have hmwB := BExact.markWF_rev hmw
    have hf := BExact.DB_edgeOK hmwB (Exact.filtUp_ok (BExact.filtUp_rev hup))
      (Exact.backOK_true (Program.rev P)) satW_SatMark restrictI_sub
      (BExact.noZeroIn_rev hnz) (hrecs.toV hmwB)
      (DBA_sub_DB (Program.rev P) counted L dem emitW satW restrictI rc [] roots seeds true h)
    exact Or.inl (Kinds.absB_iff.mp ((hf hi hn).1 (Kinds.absB_iff.mpr ha)))

#print axioms DBW_normal_markRev

/-- A normal backward summary with an empty premise exclusion reverses to a real forward record.
    The shape premise is explicit; no mark-copying assumption is used. -/
theorem DBW_rev_record_exact (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hnz : Backward.NoZeroBack P) (hR : RevStmts P) (hC : RevCalls P)
    (hrecs : BExact.RecsExactNZ (Program.rev P) rc)
    {M : MethodId} {jb : PFact} {gb : AFact} {l l0 : Loc}
    (h : DBW (Program.rev P) counted L dem rc roots seeds
      (.edge M jb ((Program.rev P).exit M) gb))
    (hi : jb ≠ zeroFact) (hn : gb.demand = false) (hpe : PremEmpty jb.kind)
    (hd : den (revEdge jb gb.fact).1 (revEdge jb gb.fact).2 l l0) :
    Flow P M l (P.exit M) l0 :=
  BExact.summary_rev_flow hmw hup hnz hR hC satW_SatMark restrictI_sub hrecs
    (DBA_sub_DB (Program.rev P) counted L dem emitW satW restrictI rc [] roots seeds true h)
    hi hn ((rev_exact_of_empty_premise hpe (DBW_normal_markRev hmw hup hnz hrecs h hi hn)).mpr hd)

#print axioms DBW_rev_record_exact

end Reversal
end ApSpec.Abs
