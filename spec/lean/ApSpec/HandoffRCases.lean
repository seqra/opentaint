/-
  ApSpec.HandoffRCases — the worked programs 1 and 2 of `ap.md` §6.3, §6.4 (`RCases.P1`,
  `RCases.P2`; the backward runs of `Backward.lean` Part 5 and Part 6) with the INTERSECTION
  restriction `Handoff.restrictI` and the hand-off of the DEMAND EDGES only (decision F70).

  Up to now the spec checked these two programs with `restrictU` (and `restrictS`). This file
  checks the steps that the spec cites with `restrictI`:

  Program 1 (`c(x) { y = x.g.h; m(y) }`, the sink in `m`). Every demand edge has no `D-p`, so every
  restriction gives no result, with `restrictI` as with `restrictU` (`p1_no_exit`). Only the
  emission matters, and it does not change. The backward run with the new hand-off gives the same
  two demand edges (`p1_handoff`, for every backward demand, restriction and record set: the
  zero-premise backward edges do not read them), and forward run 3 with `restrictI` reports the
  vulnerability (`p1_found_I`, `p1_chain`).

  Program 2 (`c(arg) { ret = arg.h.i; return ret }`, the sink in the root on `r.f.k.z`).
    * Backward run 2: the run-1 summary of `c` is in the demand layer, so it is not crossable and
      `handF` gives the old backward demand edge `((ret,.[any],*), D-p = (arg,.*,*))`
      (`b2_handF`). The emitted backward premise `(ret,.f.k,[any],T)` lies inside `D-c`
      (`b2_inside`), and `restrictI` keeps the backward summary `(arg,.h.i,[any],T)` as `restrictU`
      does (`b2_restrictI`, `b2_restrictI_eq_U`). The backward summary is in the demand layer, so it
      is not `CrossB`, and `demOfN` hands off its piece: the demand edge `dem2c` of `c`
      (`p2_handoff`).
    * Forward run 3: the added fact `(arg,.h.i.f,[any],T)` emitted under `D-c = (arg,.h.i,[any],T)`
      is the initial fact itself and lies inside `D-c` (`f3_emit`, `f3_inside`); the exit fact
      `(ret,.f,[any],T)` restricted by `D-p = (ret,.f.k,[any],T)` gives `(ret,.f.k,[any],T)` with
      `restrictI` as with `restrictU` (`f3_restrictI`, `f3_restrictI_eq_U`); the run reports the
      vulnerability (`p2_found_I`, and the chain run 1 → backward run 2 → run 3 with the new
      hand-off, `p2_chain`).

  THE MARK-AWARE RESTRICTION (F71, 2026-10-10): `restrictI` tests the marks too (`insideB`,
  `concMarkB`). Both programs have one concrete mark `T` (the demand patterns have `T` or `*`), so
  every mark test passes and every result above is the same (`b2_insideB`, `b2_concMark`,
  `f3_insideB`, `f3_concMark`; the `decide` facts are computed with the new definition).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffDefs

namespace ApSpec.HandoffRCases
open ApSpec ApSpec.Reverse ApSpec.Handoff

/-! ## Program 1 -/

/-- PROGRAM 1: the demand edges of `c` and `m` have no `D-p`, so the restriction gives no result,
    with `restrictI` as with `restrictU`. Only the emission (unchanged) matters. -/
theorem p1_no_exit (j : PFact) (g : AFact) :
    restrictI j g RCases.Prog1.d1M = none ∧ restrictI j g RCases.Prog1.d2M = none ∧
    restrictU j g RCases.Prog1.d1M = none ∧ restrictU j g RCases.Prog1.d2M = none :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms p1_no_exit

open RCases RCases.Prog1 in
/-- PROGRAM 1, FORWARD RUN 3 WITH `restrictI`: for every demand that contains the two demand edges
    of `dem1M` and every record set, the run reports the vulnerability (in the demand layer). The
    proof is `RCases.p1_found_M`: it uses no summary return. -/
theorem p1_found_I (dem : MethodId → DemandEdge → Prop) (h1 : dem 1 d1M) (h2 : dem 2 d2M)
    (rc : Recs) :
    DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.vuln 2 0 sink1 true) := by
  have r0 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.init 0 zeroFact) :=
    DR.root (List.Mem.head _)
  have e0 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.edge 0 zeroFact 0 Z) := DR.start r0
  have e1 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.edge 0 zeroFact 1 X) :=
    DR.step e0 (s := src) hE00 (by decide)
  have ad1 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.added 1 X.fact) :=
    DR.added (c := callC) (e := bx) (a := X) e1 hE01 (List.Mem.head _) (by decide)
  have iX : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.init 1 X.fact) :=
    DR.initR (d := d1M) ad1 h1 (by decide)
  have eX0 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.edge 1 X.fact 0 X) := DR.start iX
  have eX1 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.edge 1 X.fact 1 Yc) :=
    DR.step eX0 (s := rd) hE10 (by decide)
  have ad2 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.added 2 A2M.fact) :=
    DR.added (c := callM) (e := bym) (a := A2M) eX1 hE11 (List.Mem.head _) (by decide)
  have iJ2 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.init 2 J2M) :=
    DR.initR (d := d2M) ad2 h2 (by decide)
  have eJ2 : DR P1 cnt 3 dem emitM satI restrictI rc sinks1 [0] (.edge 2 J2M 0 ⟨J2M, true⟩) :=
    DR.start iJ2
  exact DR.vuln eJ2 (s := sink1) (List.Mem.head _) (by decide)

#print axioms p1_found_I

section P1Back
variable (demB : MethodId → DemandEdge → Prop)
  (restrict : PFact → AFact → DemandEdge → Option AFact) (recsB : Recs)

local notation "B1N" => Backward.DB Backward.Pb1 RCases.cnt 2 demB emitM satI restrict recsB [] [0]
  RCases.sinks1 true

/-- The seed at the sink of `m` (`Backward.b1_s20`, for every demand, restriction and record
    set). -/
theorem b1n_s20 : B1N (.edge 2 zeroFact 0 Backward.Sd1) := by
  have r0 : B1N (.init 0 zeroFact) := Backward.DB.root (List.Mem.head _)
  have e02 : B1N (.edge 0 zeroFact 2 Backward.zeroAF) := Backward.DB.start r0
  have i1 : B1N (.init 1 zeroFact) :=
    Backward.DB.zin (c := Call.rev RCases.callC) rfl e02 Backward.hb1_c
  have e12 : B1N (.edge 1 zeroFact 2 Backward.zeroAF) := Backward.DB.start i1
  have i2 : B1N (.init 2 zeroFact) :=
    Backward.DB.zin (c := Call.rev RCases.callM) rfl e12 Backward.hb1_m
  have e20 : B1N (.edge 2 zeroFact 0 Backward.zeroAF) := Backward.DB.start i2
  exact Backward.DB.seed (s := RCases.sink1) (List.Mem.head _) e20

/-- The requirement `(x,.g.h,[any],T)` at the forward entry of `c` (`Backward.b1_x10`). -/
theorem b1n_x10 : B1N (.edge 1 zeroFact 0 Backward.Xg) := by
  have r0 : B1N (.init 0 zeroFact) := Backward.DB.root (List.Mem.head _)
  have e02 : B1N (.edge 0 zeroFact 2 Backward.zeroAF) := Backward.DB.start r0
  have i1 : B1N (.init 1 zeroFact) :=
    Backward.DB.zin (c := Call.rev RCases.callC) rfl e02 Backward.hb1_c
  have e12 : B1N (.edge 1 zeroFact 2 Backward.zeroAF) := Backward.DB.start i1
  have y11 : B1N (.edge 1 zeroFact 1 Backward.Yb1) :=
    Backward.DB.zret (c := Call.rev RCases.callM) (r := Backward.Sd1) (r' := Backward.Yb1) rfl e12
      Backward.hb1_m (b1n_s20 demB restrict recsB) (by decide) (List.Mem.head _) (by decide)
  exact Backward.DB.step y11 Backward.hb1_rd (by decide)

/-- PROGRAM 1, THE NEW HAND-OFF: the backward run gives the two demand edges of `dem1M`
    (zero-premise backward edges, `demOfN` case 2), for every backward demand, restriction,
    record set and publication. -/
theorem p1_handoff (pub : Pub) :
    demOfN Backward.Pb1 B1N pub 1 RCases.Prog1.d1M ∧
      demOfN Backward.Pb1 B1N pub 2 RCases.Prog1.d2M :=
  ⟨Or.inr (Or.inl ⟨Backward.Xg, b1n_x10 demB restrict recsB, rfl⟩),
   Or.inr (Or.inl ⟨Backward.Sd1, b1n_s20 demB restrict recsB, rfl⟩)⟩

/-- PROGRAM 1, THE CHAIN WITH THE NEW HAND-OFF: forward run 3 with the demand `demOfN` of the
    backward run and `restrictI` reports the vulnerability, for every record set. -/
theorem p1_chain (pub : Pub) (rc : Recs) :
    DR RCases.P1 RCases.cnt 3 (demOfN Backward.Pb1 B1N pub) emitM satI restrictI rc
      RCases.sinks1 [0]
      (.vuln 2 0 RCases.sink1 true) :=
  p1_found_I _ (p1_handoff demB restrict recsB pub).1 (p1_handoff demB restrict recsB pub).2 rc

end P1Back

#print axioms b1n_s20
#print axioms b1n_x10
#print axioms p1_handoff
#print axioms p1_chain

/-! ## Program 2: backward run 2 -/

/-- The run-1 summary of `c` (`(arg,.*,*) → (ret,.[any],*)`, demand layer) is not crossable. -/
theorem r1_c_not_cross : ¬ Cross Backward.Jc Backward.Gc :=
  fun h => absurd h.1 (by decide)

/-- THE BACKWARD DEMAND EDGE OF `c` WITH THE NEW HAND-OFF: `handF` gives the old edge
    `((ret,.[any],*), D-p = (arg,.*,*))` (run 1 publishes every exit edge as it is). -/
theorem b2_handF :
    handF RCases.P2 Backward.R1p pubD 1 ⟨Backward.Gc.fact, some Backward.Jc⟩ :=
  ⟨Backward.Jc, Backward.Gc, Backward.Gc, Backward.r1_init_c, Backward.r1_exit_c, r1_c_not_cross,
    rfl, rfl⟩

/-- The emission of the backward premise `(ret,.f.k,[any],T)` (unchanged). -/
theorem b2_emit : emitM Backward.Gc.fact Backward.Jb2 = some Backward.Jb2 := by decide

/-- The emitted backward premise lies inside `D-c = (ret,.[any],*)`. -/
theorem b2_inside : insideLocB Backward.Jb2 Backward.Gc.fact = true := by decide

/-- THE MARK TESTS (F71, the mark-aware restriction): the emitted backward premise lies inside
    `D-c` with its mark too (`insideB`: the `D-c` mark `*` admits `T`), and the conclusion mark
    `T` meets the `D-p` mark `*` (`concMarkB`). So `restrictI` gives the same result as before
    F71. -/
theorem b2_insideB : insideB Backward.Jb2 Backward.Gc.fact = true := by decide

theorem b2_concMark : concMarkB Backward.Jc.mark Backward.Gb2.fact.mark = true := by decide

/-- `restrictI` keeps the backward summary `(arg,.h.i,[any],T)` (below `D-p = (arg,.*,*)`). -/
theorem b2_restrictI :
    restrictI Backward.Jb2 Backward.Gb2 ⟨Backward.Gc.fact, some Backward.Jc⟩ =
      some Backward.Gb2 := by
  decide

/-- On this step `restrictI` and `restrictU` give the same result. -/
theorem b2_restrictI_eq_U :
    restrictI Backward.Jb2 Backward.Gb2 ⟨Backward.Gc.fact, some Backward.Jc⟩ =
      restrictU Backward.Jb2 Backward.Gb2 ⟨Backward.Gc.fact, some Backward.Jc⟩ := by
  decide

/-- The backward summary of `c` is in the demand layer: it is not `CrossB`, so it is handed off. -/
theorem b2_not_crossB : ¬ CrossB Backward.Jb2 Backward.Gb2 :=
  fun h => absurd h.1 (by decide)

#print axioms r1_c_not_cross
#print axioms b2_handF
#print axioms b2_emit
#print axioms b2_inside
#print axioms b2_insideB
#print axioms b2_concMark
#print axioms b2_restrictI
#print axioms b2_restrictI_eq_U
#print axioms b2_not_crossB

section P2Back
variable (recsB : Recs)

/-- Backward run 2 of program 2 with the NEW hand-off: the demand `handF` of forward run 1, the
    restriction `restrictI`, any backward record set. -/
local notation "B2N" => Backward.DB Backward.Pb2 RCases.cnt 2 (handF RCases.P2 Backward.R1p pubD)
  emitM satI restrictI recsB [] [0] RCases.sinks2 true

/-- The backward premise of `c` (`Backward.b2_i1`, with `handF`). -/
theorem b2n_i1 : B2N (.init 1 Backward.Jb2) := by
  have e02 : B2N (.edge 0 zeroFact 2 Backward.zeroAF) :=
    Backward.DB.start (Backward.DB.root (List.Mem.head _))
  have s02 : B2N (.edge 0 zeroFact 2 Backward.Sd2) :=
    Backward.DB.seed (s := RCases.sink2) (List.Mem.head _) e02
  have ad : B2N (.added 1 Backward.Jb2) :=
    Backward.DB.added (c := Call.rev RCases.callC2)
      (e := revEdge RCases.Prog2.br.1 RCases.Prog2.br.2)
      (a := Backward.Jb2t) s02 Backward.hb2_c (List.Mem.head _) (by decide)
  exact Backward.DB.initR ad b2_handF b2_emit

/-- The backward summary of `c`: `(ret,.f.k,[any],T) → (arg,.h.i,[any],T)` (`Backward.b2_g1`). -/
theorem b2n_g1 : B2N (.edge 1 Backward.Jb2 0 Backward.Gb2) :=
  Backward.DB.step (Backward.DB.start (b2n_i1 recsB)) Backward.hb2_rd (by decide)

/-- PROGRAM 2, THE NEW HAND-OFF: the backward run hands off the demand edge `dem2c` of `c`
    (`demOfN` case 3, the piece of `restrictI`). -/
theorem p2_handoff :
    demOfN Backward.Pb2 B2N (pubR (handF RCases.P2 Backward.R1p pubD)) 1 Backward.dem2c :=
  Or.inr (Or.inr ⟨Backward.Jb2, Backward.Gb2, Backward.Gb2, b2n_i1 recsB, by decide, b2n_g1 recsB,
    b2_not_crossB, ⟨_, b2_handF, b2_restrictI⟩, rfl⟩)

end P2Back

#print axioms b2n_i1
#print axioms b2n_g1
#print axioms p2_handoff

/-! ## Program 2: forward run 3 -/

/-- The demand edge of `c` in forward run 3 is the hand-off `dem2c` of backward run 2. -/
theorem ddM_eq : RCases.Prog2.ddM = Backward.dem2c := rfl

/-- The emission under `D-c = (arg,.h.i,[any],T)` gives the added fact `(arg,.h.i.f,[any],T)`
    itself (unchanged). -/
theorem f3_emit : emitM RCases.Prog2.ddM.din RCases.Prog2.A.fact = some RCases.Prog2.JM := by
  decide

/-- The initial fact lies inside `D-c`. -/
theorem f3_inside : insideLocB RCases.Prog2.JM RCases.Prog2.ddM.din = true := by decide

/-- THE MARK TESTS (F71): the initial fact `(arg,.h.i.f,[any],T)` lies inside
    `D-c = (arg,.h.i,[any],T)` with its mark too, and the conclusion mark `T` is the mark `T` of
    `D-p = (ret,.f.k,[any],T)`. So `restrictI` gives the same result as before F71. -/
theorem f3_insideB : insideB RCases.Prog2.JM RCases.Prog2.ddM.din = true := by decide

theorem f3_concMark :
    (∃ p, RCases.Prog2.ddM.dout = some p ∧ concMarkB p.mark RCases.Prog2.GM.fact.mark = true) :=
  ⟨_, rfl, by decide⟩

/-- `restrictI` restricts the exit fact `(ret,.f,[any],T)` by `D-p = (ret,.f.k,[any],T)` to
    `(ret,.f.k,[any],T)` (the case above `D-p`: the chain of `D-p`). -/
theorem f3_restrictI :
    restrictI RCases.Prog2.JM RCases.Prog2.GM RCases.Prog2.ddM = some RCases.Prog2.GM' := by
  decide

/-- On this step `restrictI` and `restrictU` give the same result. -/
theorem f3_restrictI_eq_U :
    restrictI RCases.Prog2.JM RCases.Prog2.GM RCases.Prog2.ddM =
      restrictU RCases.Prog2.JM RCases.Prog2.GM RCases.Prog2.ddM := by
  decide

#print axioms ddM_eq
#print axioms f3_emit
#print axioms f3_insideB
#print axioms f3_concMark
#print axioms f3_inside
#print axioms f3_restrictI
#print axioms f3_restrictI_eq_U

open RCases RCases.Prog2 in
/-- PROGRAM 2, FORWARD RUN 3 WITH `restrictI` (as `RCases.p2_found_M`): for every demand that
    contains the demand edge `ddM` of `c` and every record set, the run reports the vulnerability
    (in the demand layer). -/
theorem p2_found_I (dem : MethodId → DemandEdge → Prop) (h : dem 1 ddM) (rc : Recs) :
    DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.vuln 0 2 sink2 true) := by
  have r0 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.init 0 zeroFact) :=
    DR.root (List.Mem.head _)
  have e0 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.edge 0 zeroFact 0 Z) := DR.start r0
  have e1 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.edge 0 zeroFact 1 X) :=
    DR.step e0 (s := src2) hE00 (by decide)
  have ad : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.added 1 A.fact) :=
    DR.added (c := callC2) (e := bx) (a := A) e1 hE01 (List.Mem.head _) (by decide)
  have iJ : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.init 1 JM) :=
    DR.initR (d := ddM) ad h f3_emit
  have eJ0 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.edge 1 JM 0 A) := DR.start iJ
  have eJ1 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.edge 1 JM 1 GM) :=
    DR.step eJ0 (s := rd2) hE10 (by decide)
  -- the intersection restricts the exit fact to `(ret,.f.k,[any],T)`; the caller fact satisfies
  -- the premise; the result is `(r,.f.k,[any],T)`
  have e2 : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0]
      (.edge 0 zeroFact 2 (limitF cnt 3 RrM')) :=
    DR.ret (c := callC2) (e1 := bx) (a := A) (j := JM) (g := GM) (d := ddM) (g' := GM') (r := RrM)
      (e2 := br) e1 hE01 (List.Mem.head _) (by decide) iJ eJ1 h f3_restrictI (by decide)
      (by decide) (List.Mem.head _) (by decide)
  have e2' : DR P2 cnt 3 dem emitM satI restrictI rc sinks2 [0] (.edge 0 zeroFact 2 RrM') := e2
  exact DR.vuln e2' (s := sink2) (List.Mem.head _) (by decide)

#print axioms p2_found_I

/-- PROGRAM 2, THE CHAIN WITH THE NEW HAND-OFF: forward run 1 → backward run 2 (demand `handF`,
    `restrictI`, any record set) → forward run 3 (demand `demOfN`, `restrictI`, any record set)
    reports the vulnerability. -/
theorem p2_chain (recsB rc : Recs) :
    DR RCases.P2 RCases.cnt 3
      (demOfN Backward.Pb2
        (Backward.DB Backward.Pb2 RCases.cnt 2 (handF RCases.P2 Backward.R1p pubD) emitM satI
          restrictI recsB [] [0] RCases.sinks2 true)
        (pubR (handF RCases.P2 Backward.R1p pubD)))
      emitM satI restrictI rc RCases.sinks2 [0] (.vuln 0 2 RCases.sink2 true) :=
  p2_found_I _ (p2_handoff recsB) rc

#print axioms p2_chain

end ApSpec.HandoffRCases
