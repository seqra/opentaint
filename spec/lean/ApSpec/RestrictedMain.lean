/-
  ApSpec.RestrictedMain — the theorems of the restricted runs for the spec rules.

  The coverage, iteration and exactness theorems are generic over the emission, the
  satisfaction and the restriction (`RestrictedCoverage.lean`, `RestrictedExact.lean`).
  `RestrictedCore.lean` proves that the rules satisfy the contracts. This file joins them.
  The spec rules are `emitM` (since version 4), `satI` (since version 5) and `restrictU` (section
  "The spec rules": `vuln_found_M`,
  `iteration_sound_M`, `iteration_sound_M_identity`, `closed_records_exactM`, `confirmed_real_M`,
  `no_request_M`). The version-3 rules `emitS`, `satS`, `restrictS` come first, as the record of the
  review:
    * `vuln_found_S`        a restricted run with the version-3 rules reports every demanded vulnerability;
    * `iteration_sound_S`   with the backward contract B, every run reports every real vulnerability;
    * `iteration_sound_S_identity`  the same with the identity backward step (no hypothesis B);
    * `closed_records_exactR`  the records of a request-free initial fact of a restricted run: with no request and only normal exits,
                            the records of an initial fact cover every demanded flow from it and
                            denote only real flows;
    * `confirmed_real_S`    a confirmed vulnerability of a restricted run is real.
  Record reuse (the rule `retRec` applies a persisted record by `sat` OR `applicable`): on program 3
  of `RestrictedCases` the run-1 record is exact (`p3_recs_exact`) and the edge that its reuse
  gives by `applicable` denotes only real flows (`p3_reuse_exact`).
-/
import ApSpec.RestrictedCore
import ApSpec.RestrictedCoverage
import ApSpec.RestrictedExact
import ApSpec.RestrictedCases

namespace ApSpec.RMain
open ApSpec

/-- A restricted run with the spec rules reports every real vulnerability whose witness is
    demanded, and its own summaries demand the witness again. -/
theorem vuln_found_S {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DR P counted L demand emitS satS restrictS recs sinks roots (.vuln M n s b)) ∧
    ReachR P (summaryDemand P (DR P counted L demand emitS satS restrictS recs sinks roots))
      roots M n l :=
  RCov.vuln_foundR P counted L demand emitS satS restrictS recs sinks roots hwf
    (RCore.emitS_contract.on _) RCore.satS_contract RCore.restrictS_contract hRe hs hT hsc

#print axioms vuln_found_S

/-- THE ITERATION THEOREM for the spec rules. Run 1 is `D` with `policy1`; run k+1 is `DR`
    with the demand `dem k`. If every backward step keeps the witnesses that the summaries of
    the previous forward run demand (contract B), every run reports every real vulnerability. -/
theorem iteration_sound_S {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF)
    (hB : ∀ k, BackwardContract P roots sinks
      (RCov.runSeq P counted Ls dem emitS satS restrictS recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitS satS restrictS recs sinks roots k (.vuln M n s b) :=
  RCov.iteration_sound_full (P := P) (counted := counted) (Ls := Ls) (dem := dem) (recs := recs)
    (sinks := sinks) (roots := roots) hwf RCore.emitS_contract RCore.satS_contract
    RCore.restrictS_contract hB hRe hs hT hsc

#print axioms iteration_sound_S

/-- The iteration theorem with the identity backward step: no hypothesis on the backward run. -/
theorem iteration_sound_S_identity {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeqId P counted Ls emitS satS restrictS recs sinks roots k (.vuln M n s b) :=
  RCov.iteration_sound_identity hwf (fun _ => RCore.emitS_contract.on _) RCore.satS_contract
    RCore.restrictS_contract hRe hs hT hsc

#print axioms iteration_sound_S_identity

/-- The records of a request-free initial fact of a restricted run (the analogue of `Closed.closed_records_exact`). If the run raised
    no request on the initial fact `i` and every exit edge of `i` is in the normal layer, then
    every DEMANDED flow from the location set of `i` to the exit has a record, and every record
    pair is a real flow. -/
theorem closed_records_exactR {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hrecs : RExact.RecsExact P recs)
    {M : MethodId} {i : PFact}
    (hi : DR P counted L demand emitS satS restrictS recs sinks roots (.init M i))
    (hnoreq : ∀ t, ¬ DR P counted L demand emitS satS restrictS recs sinks roots (.req M i t))
    (hcomp : ∀ g, DR P counted L demand emitS satS restrictS recs sinks roots
      (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    (FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emitS satS restrictS recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) ∧
    ((∃ g, DR P counted L demand emitS satS restrictS recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) → Flow P M l0 (P.exit M) l) := by
  have hcov : ∀ l0 l, i.covers l0 → FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emitS satS restrictS recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l := by
    intro l0 l hc hfl
    rcases RCov.coverageR P counted L demand emitS satS restrictS recs sinks roots hwf
      (RCore.emitS_contract.on _) RCore.satS_contract RCore.restrictS_contract hfl i hi hc with
      ⟨g, hg, hd, _⟩ | hrq
    · exact ⟨g, hg, hd⟩
    · exact absurd hrq (hnoreq _)
  exact RExact.closed_exactR hmw hup RExact.satS_mark RCore.restrictS_sub hrecs hcov hcomp h0 l

#print axioms closed_records_exactR

/-- A confirmed vulnerability of a restricted run with the spec rules is real. -/
theorem confirmed_real_S {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : RExact.ConfirmedR P counted L demand emitS satS restrictS recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RExact.confirmed_realR hmw hup RExact.satS_mark RCore.restrictS_sub hrecs h

#print axioms confirmed_real_S

/-! ## The spec rules `emitM`, `satI`, `restrictU` (versions 4 and 5)

  A restricted run of the spec rules is concrete (`RExact.DR_concrete`), so the agreed restriction `restrictU` gives the
  same closure as `restrictS` (`RExact.restrict_U_eq_S_M`), whose contract holds. The emission
  contract holds for the concrete added facts (`RCore.emitM_contract_I`), and every added fact of the
  run is concrete (`RCov.emitOn_of_conc`). -/

/-- The same run with `restrictU` and with `restrictS` (the spec rules). -/
theorem runU_eq_S {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} :
    DR P counted L demand emitM satI restrictU recs sinks roots =
      DR P counted L demand emitM satI restrictS recs sinks roots :=
  RExact.restrict_U_eq_S_M

/-- A restricted run of the spec rules reports every real vulnerability whose witness is demanded, and its
    own summaries demand the witness again. -/
theorem vuln_found_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DR P counted L demand emitM satI restrictU recs sinks roots (.vuln M n s b)) ∧
    ReachR P (summaryDemand P (DR P counted L demand emitM satI restrictU recs sinks roots))
      roots M n l := by
  rw [runU_eq_S]
  exact RCov.vuln_foundR P counted L demand emitM satI restrictS recs sinks roots hwf
    (RCov.emitOn_of_conc P counted L demand emitM satI restrictS recs sinks roots
      RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract hRe hs hT hsc

#print axioms vuln_found_M

/-- The run sequence of the spec rules is the same with `restrictU` and with `restrictS`. -/
theorem runSeqU_eq_S {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (k : Nat) :
    RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k =
      RCov.runSeq P counted Ls dem emitM satI restrictS recs sinks roots k := by
  cases k with
  | zero => rfl
  | succ k => exact runU_eq_S

/-- THE ITERATION THEOREM for the spec rules. If every backward step keeps the
    vulnerability witnesses that the summaries of the previous forward run demand (contract B),
    every forward run reports every real vulnerability. -/
theorem iteration_sound_M {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF)
    (hB : ∀ k, BackwardContract P roots sinks
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [runSeqU_eq_S k]
  refine RCov.iteration_sound_conc (P := P) (counted := counted) (Ls := Ls) (dem := dem)
    (recs := recs) (sinks := sinks) (roots := roots) hwf RCore.emitM_contract_I RCore.emitM_copies
    RCore.satI_contract RCore.restrictS_contract ?_ hRe hs hT hsc k
  intro k'
  rw [← runSeqU_eq_S k']
  exact hB k'

#print axioms iteration_sound_M

/-- The identity run sequence of the spec rules is the same with `restrictU` and with `restrictS`. -/
theorem runSeqIdU_eq_S {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} :
    ∀ k, RCov.runSeqId P counted Ls emitM satI restrictU recs sinks roots k =
      RCov.runSeqId P counted Ls emitM satI restrictS recs sinks roots k
  | 0 => rfl
  | k + 1 => by
    show DR P counted (Ls (k + 1))
        (summaryDemand P (RCov.runSeqId P counted Ls emitM satI restrictU recs sinks roots k))
        emitM satI restrictU (recs k) sinks roots =
      DR P counted (Ls (k + 1))
        (summaryDemand P (RCov.runSeqId P counted Ls emitM satI restrictS recs sinks roots k))
        emitM satI restrictS (recs k) sinks roots
    rw [runSeqIdU_eq_S k]
    exact runU_eq_S

/-- The iteration theorem of the spec rules with the identity backward step: no hypothesis on the
    backward run. -/
theorem iteration_sound_M_identity {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeqId P counted Ls emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [runSeqIdU_eq_S k]
  exact RCov.iteration_sound_identity hwf
    (fun k => RCov.emitOn_of_conc P counted (Ls (k + 1))
      (summaryDemand P (RCov.runSeqId P counted Ls emitM satI restrictS recs sinks roots k))
      emitM satI restrictS (recs k) sinks roots RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract hRe hs hT hsc k

#print axioms iteration_sound_M_identity

/-- The records of a request-free initial fact of a restricted run of the spec rules: if every exit edge of the initial fact `i` is in the normal layer, every
    DEMANDED flow from the location set of `i` to the exit has a record, and every record pair is a
    real flow. No hypothesis on requests: such a run has none. -/
theorem closed_records_exactM {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hrecs : RExact.RecsExact P recs)
    {M : MethodId} {i : PFact}
    (hi : DR P counted L demand emitM satI restrictU recs sinks roots (.init M i))
    (hcomp : ∀ g, DR P counted L demand emitM satI restrictU recs sinks roots
      (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    (FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emitM satI restrictU recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) ∧
    ((∃ g, DR P counted L demand emitM satI restrictU recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l) → Flow P M l0 (P.exit M) l) := by
  rw [runU_eq_S] at hi hcomp ⊢
  have hcov : ∀ l0 l, i.covers l0 → FlowR P demand M l0 (P.exit M) l →
      ∃ g, DR P counted L demand emitM satI restrictS recs sinks roots (.edge M i (P.exit M) g) ∧
        den i g.fact l0 l := by
    intro l0 l hc hfl
    rcases RCov.coverageR P counted L demand emitM satI restrictS recs sinks roots hwf
      (RCov.emitOn_of_conc P counted L demand emitM satI restrictS recs sinks roots
        RCore.emitM_contract_I RCore.emitM_copies)
      RCore.satI_contract RCore.restrictS_contract hfl i hi hc with
      ⟨g, hg, hd, _⟩ | hrq
    · exact ⟨g, hg, hd⟩
    · exact absurd hrq (RExact.DR_no_requestM _ _ _)
  exact RExact.closed_exactR hmw hup RExact.satI_mark RCore.restrictS_sub hrecs hcov hcomp h0 l

#print axioms closed_records_exactM

/-- A confirmed vulnerability of a restricted run of the spec rules is real. -/
theorem confirmed_real_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : RExact.ConfirmedM P counted L demand emitM satI restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RExact.confirmed_realM_gen hmw hup RExact.satI_mark RCore.restrictU_sub hrecs h

#print axioms confirmed_real_M

/-- The same for a real program with type filters: the valid form (the locations that every
    filter accepts; the sink pattern covers only valid locations). -/
theorem confirmed_real_M_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok recs) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l)
    (h : RExact.ConfirmedM P counted L demand emitM satI restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RExact.confirmed_realM_gen_valid hmw hv hbo RExact.satI_mark RCore.restrictU_sub hrecs hok h

#print axioms confirmed_real_M_valid

/-- A restricted run of the spec rules raises no mark request: requests are needed only in run 1. -/
theorem no_request_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact} :
    ∀ M i t, ¬ DR P counted L demand emitM sat restrict recs sinks roots (.req M i t) :=
  RExact.DR_no_requestM

#print axioms no_request_M

/-! ## Why the backward contract is about sink witnesses only

  A program with no sink: root 0 calls method 1 with the zero binding. The backward run starts
  at the sinks, so for this program it gives the EMPTY demand. The empty demand satisfies the
  contract (there is no sink witness). A contract over EVERY witness would be false here: the
  summaries of run 1 demand the witness "zero location at the entry of method 1", and the empty
  demand does not. (Found by the review of version 3.) -/

def zb : MicroEdge := (zeroFact, zeroFact)
def call1 : Call := ⟨1, [0], [zb], []⟩
def Pq : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .call call1, 1)]⟩
def noSinks : List (MethodId × Node × PFact) := []

abbrev R0 := D Pq (fun _ => true) 3 policy1 noSinks [0]

theorem r0_init1 : R0 (.init 1 zeroFact) := by
  have h0 : R0 (.init 0 zeroFact) := D.root (List.Mem.head _)
  have e0 : R0 (.edge 0 zeroFact 0 (startFact zeroFact)) := D.start h0
  have ad : R0 (.added 1 zeroFact) :=
    D.added (c := call1) (e := zb) (a := ⟨zeroFact, false⟩) e0 (List.Mem.head _)
      (List.Mem.head _) (by decide)
  have : policy1 1 zeroFact = zeroFact := by decide
  rw [← this]
  exact D.initA ad

/-- The empty demand satisfies the contract for a program without sinks. -/
theorem noSink_contract : BackwardContract Pq [0] noSinks R0 (fun _ _ => False) := by
  intro M n l s T hs
  cases hs

#print axioms noSink_contract

/-- A contract over every witness (not only sink witnesses) fails for the same demand. -/
theorem everyWitness_contract_fails :
    ¬ (∀ M n l, ReachR Pq (summaryDemand Pq R0) [0] M n l →
        ReachR Pq (fun _ _ => False) [0] M n l) := by
  intro hB
  have hw : ReachR Pq (summaryDemand Pq R0) [0] 1 0 zeroLoc := by
    refine ReachR.down (d := ⟨zeroFact, none⟩) (c := call1) (e := zb) (l1 := zeroLoc)
      (ReachR.root (List.Mem.head _) (FlowR.start 0 zeroLoc)) (List.Mem.head _)
      (List.Mem.head _) ?_ ⟨r0_init1, Or.inl rfl⟩ ?_ (FlowR.start 1 zeroLoc)
    · exact ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  have key : ∀ M n l, ReachR Pq (fun _ _ => False) [0] M n l → M = 0 := by
    intro M n l h
    induction h with
    | root hM _ =>
      cases hM with
      | head => rfl
      | tail _ h => cases h
    | down _ _ _ _ hd _ _ _ => exact absurd hd id
  have := key 1 0 zeroLoc (hB 1 0 zeroLoc hw)
  cases this

#print axioms everyWitness_contract_fails

/-! ## Record reuse by `applicable` stays exact (program 3 of `RestrictedCases`)

  The rule `retRec` applies a persisted record when the caller fact satisfies its premise OR when
  its premise covers the caller fact (`applicable`, the user's decision). Program 3
  (`RCases.p3_reuse`): the run-1 record `(arg0,.,*,{},*) → (ret,.,*,{},*)` applies to the caller
  fact `(arg0,.f,$,T)` and gives `(r,.f,$,T)` in the normal layer. The record is an exit edge of
  run 1 (`RCases.recs3_run1`), so it is exact (`RExact.recs_of_D`), and the edge that the reuse
  gives denotes only real flows (`RExact.edge_exactR`, unchanged statement). -/

/-- Program 3 has the mark condition of `Exact.MarkWF`. -/
theorem p3_markWF : Exact.MarkWF RCases.P3 where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head => cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms p3_markWF

/-- Program 3 has no type filter. -/
theorem p3_filtUp : Exact.FiltUp RCases.P3 := by
  intro M n b may n' hE
  cases hE with
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

#print axioms p3_filtUp

/-- The record set of program 3 (the run-1 record of `id`) is exact. -/
theorem p3_recs_exact : RExact.RecsExact RCases.P3 RCases.recs3 :=
  RExact.recs_mono RCases.recs3_run1 (RExact.recs_of_D p3_markWF p3_filtUp)

#print axioms p3_recs_exact

/-- The edge that the record reuse gives (`RCases.p3_reuse`, applied by `applicable`) denotes only
    real flows: every pair of `zero → (r,.f,$,T)` at the node after the call is a real flow. -/
theorem p3_reuse_exact {l0 l : Loc} (hd : den zeroFact RCases.Prog3.Rr'.fact l0 l) :
    Flow RCases.P3 0 l0 2 l :=
  RExact.edge_exactR p3_markWF p3_filtUp RExact.satI_mark RExact.restrictU_sub p3_recs_exact
    RCases.p3_reuse rfl hd

#print axioms p3_reuse_exact

end ApSpec.RMain
