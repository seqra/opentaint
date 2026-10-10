/-
  ApSpec.HandoffDefs — the hand-off of the DEMAND EDGES only (decision F70), the definitions.

  The user's rule (2026-10-09): after run 1, every summary edge of a run (forward or backward) is
  the INTERSECTION with a demand edge of the previous run. A demand edge of the previous run is a
  summary edge that the next run cannot reuse: a demand-layer edge, or a normal edge with no record
  that both directions can cross. A COMPLETE edge never goes into the demand: the next run reuses it
  as a record (applied in its own direction, reversed in the other). So the demand of a run lies
  inside the demand of the run before it, and a method key with no demand gets no initial fact
  except the zero fact.

  The earlier hand-off (`Backward.revSummaryDemand`, `Backward.demOf`) reads EVERY summary edge, in
  every layer, before the restriction: a complete callee is analysed again in every run (the program
  WRAP of `HandoffCases.lean`).

  This file has only definitions (the interface of `HandoffRestrict.lean`, `HandoffCoverage.lean`,
  `HandoffBackward.lean`, `HandoffIter.lean`, `HandoffExclusion.lean`, `HandoffCases.lean`):
    1. `restrictI`: the restriction of `ap.md` §6.4 as an INTERSECTION: the premise must lie inside
       `D-c` (not only overlap it), and at the path of `D-p` the conclusion is met with the tail of
       `D-p` (`meetConcK`; today's `restrictU` keeps the whole conclusion there);
    2. `CrossK`, `Cross`, `revRec`: a record that both directions cross with no analysis;
    3. `pubD`, `pubR`: the published summary pieces of a run (run 1: the exit edges; a restricted
       run: the results of `restrictI`);
    4. `handF`, `demOfN`: the two hand-offs (only the pieces of the edges that are not crossable);
    5. `FlowRR`, `ReachRR`: a witness whose every call that returns is DEMANDED or crossed by a
       RECORD (the input of a forward run); `FlowRDN`, `ReachRDN`: a witness that a run JUSTIFIES by
       a published summary piece or by a record (the output of a forward run);
    6. `CoversN`, `BackwardContractN`: the two contracts that the iteration composes.

  All definitions are constructive.
-/
import ApSpec.Backward

namespace ApSpec.Handoff
open ApSpec ApSpec.Reverse

/-! ## 1. The restriction as an intersection (`ap.md` §6.4, revised) -/

/-- The location set of `j` lies inside the location set of `d`; the marks are ignored. It is the
    location part of `insideB` (the restriction tests the marks separately, F71) and the form of the
    narrowing theorems on locations. -/
def insideLocB (j d : PFact) : Bool :=
  coversB ⟨d.base, d.path, d.kind, .star⟩ ⟨j.base, j.path, j.kind, .star⟩

/-- The meet of a conclusion tail with the tail of `D-p` at the same path. Only `[any] ∩ $ = $`
    narrows. Every other cell keeps the conclusion tail: `$` is inside every pattern at its path;
    `[any] ∩ */E` has no form without the `*` tail on a concrete mark (W2); a correlated `*`
    conclusion cut to `$` would relate MORE pairs (`tailF .exact` relates every continuation), so it
    stays as it is (a restricted run has no `*` conclusion). -/
def meetConcK : Kind → Kind → Kind
  | .any, .exact => .exact
  | k,    _      => k

/-- The conclusion `sc` restricted by the exit pattern `dout` (the intersection, with the cells of
    `meetConcK`). Below `D-p`: all of `sc` if the tail of `D-p` admits the step (then `sc` lies
    inside `D-p`). At `D-p`: the meet. Above `D-p`: an `[any]` conclusion gives the chain of `D-p`
    (with `$` if `D-p` is `$`), a `*` conclusion stays if its exclusion admits the step (as
    `restrictS`; it never occurs in a restricted run), a `$` conclusion gives nothing. -/
def restrictConcI (sc : AFact) (dout : PFact) : Option AFact :=
  if Nat.beq sc.fact.base dout.base then
    match relate dout.path sc.fact.path with
    | .below []       => some ⟨⟨sc.fact.base, sc.fact.path, meetConcK sc.fact.kind dout.kind,
                          sc.fact.mark⟩, sc.demand⟩
    | .below (x :: r) => if admitsTailB dout.kind (x :: r) then some sc else none
    | .above r =>
      match sc.fact.kind with
      | .any    => some ⟨⟨sc.fact.base, dout.path,
                    (match dout.kind with | .exact => .exact | _ => .any), sc.fact.mark⟩, sc.demand⟩
      | .star e => if e.admits r then some sc else none
      | .exact  => none
    | .apart => none
  else none

/-- The premise `j` lies INSIDE the entry pattern `d`, in its locations AND in its marks: the
    marks of `j` are a subset of the marks of `d` (`markSubB`: a `*` pattern admits every mark, a
    concrete `T` only `T`, a `*∖x` pattern every mark that is not in `x`). An emitted premise has
    the mark of its concrete added fact, which the entry pattern admits, so it passes (F71, the
    mark-aware restriction). -/
def insideB (j d : PFact) : Bool :=
  insideLocB j d && markSubB d.mark j.mark

/-- The marks of the conclusion meet the marks of the exit pattern (`p` is `D-p`, `m` the
    conclusion mark): two concrete marks must be the same; a `*∖x` side does not admit a concrete
    mark in `x`; a `*` side meets every mark. A `*` or `*∖x` conclusion (it never occurs in a
    restricted run) is kept when it can pass a mark of `D-p`: the intersection of a pass-through
    mark with `T` has no form, so the edge stays as it is (an over-approximation, no lost pair). -/
def concMarkB : MarkA → MarkA → Bool
  | .conc t,   .conc u   => Nat.beq t u
  | .conc t,   .starEx x => !(memB t x)
  | .conc _,   .star     => true
  | .star,     _         => true
  | .starEx x, .conc u   => !(memB u x)
  | .starEx _, _         => true

/-- THE RESTRICTION OF `ap.md` §6.4 AS AN INTERSECTION, MARK-AWARE (F71). No `D-p`: no result. The
    premise `j` must lie INSIDE `D-c`, in its locations and in its marks (`insideB`; so
    `j ∩ D-c = j`; an emitted premise lies inside the entry pattern that emitted it). The marks of
    the conclusion must meet the marks of `D-p` (`concMarkB`; in a restricted run both are concrete,
    so the test is "the same mark"). The conclusion is `restrictConcI`. The layer stays. -/
def restrictI (j : PFact) (g : AFact) (d : DemandEdge) : Option AFact :=
  match d.dout with
  | none   => none
  | some p => if insideB j d.din && concMarkB p.mark g.fact.mark then restrictConcI g p else none

/-! ## 2. Crossable records -/

/-- A premise tail that a record application accepts for EVERY added fact that covers one of its
    locations: `$` (by `inside`) or `*` with the Empty exclusion (by `inside` or `applicable`). An
    `[any]` premise (a must-premise in the base model) is not crossable. -/
def CrossK : Kind → Prop
  | .exact  => True
  | .star e => e = Excl.empty
  | .any    => False

/-- A record `j → g` that BOTH directions cross with no analysis: normal, a crossable premise,
    mark-reversible, and its reversal has a crossable premise too (so `g` has no `[any]` tail: the
    reversed premise of an `[any]` conclusion is `[any]`). Such an edge is not handed off: the next
    run crosses it by the record (in its direction) or by `revRec` (in the other direction). -/
def Cross (j : PFact) (g : AFact) : Prop :=
  g.demand = false ∧ CrossK j.kind ∧ MarkRev j g.fact ∧ CrossK (revEdge j g.fact).1.kind

/-- The reversal of a record, as a record of the other direction (normal layer, `ap.md` §8.7 R3;
    the shape of `BExact.revRecs`). -/
def revRec (x : PFact × AFact) : PFact × AFact :=
  ((revEdge x.1 x.2.fact).1, ⟨(revEdge x.1 x.2.fact).2, false⟩)

/-- A backward summary leaf `jb → gb` that the next forward run crosses by its reversal: it is
    NORMAL, and its reversal is crossable. `revRec` always gives the normal layer, so the layer of
    `gb` must be tested here: the reversal of a demand-layer backward edge is not an exact record
    (`ap.md` §8.7 R1 persists only normal edges), so such a leaf is handed off. -/
def CrossB (jb : PFact) (gb : AFact) : Prop :=
  gb.demand = false ∧ Cross (revRec (jb, gb)).1 (revRec (jb, gb)).2

/-! ## 3. The published summary pieces -/

/-- The publication relation of a run: `pub m j g g'` — the exit edge `j → g` of the method `m`
    is published as the piece `j → g'`. -/
abbrev Pub := MethodId → PFact → AFact → AFact → Prop

/-- Run 1 publishes every exit edge as it is (no restriction). -/
def pubD : Pub := fun _ _ g g' => g' = g

/-- A restricted run (forward or backward) publishes the intersections with its demand edges. -/
def pubR (dem : MethodId → DemandEdge → Prop) : Pub :=
  fun m j g g' => ∃ d, dem m d ∧ restrictI j g d = some g'

/-! ## 4. The two hand-offs -/

/-- FORWARD TO BACKWARD (`ap.md` §9.2, revised). For every exit edge `j → g` of the forward run `R`
    that is NOT crossable, every published piece `j → g'` gives the backward demand edge
    `(D-c = g', D-p = j)`. A crossable exit edge gives no demand edge: the backward run crosses it
    by `revRec`. -/
def handF (P : Program) (R : Obj → Prop) (pub : Pub) (m : MethodId) (d : DemandEdge) : Prop :=
  ∃ j g g', R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ ¬ Cross j g ∧ pub m j g g' ∧
    d = ⟨g'.fact, some j⟩

/-- BACKWARD TO FORWARD (`ap.md` §9.2, revised; `Backward.demOf` with the filter). The zero demand,
    every zero-premise backward edge at the forward entry (never a record: the seed paths), and for
    every backward exit edge `jb → gb` with a non-zero premise whose reversal is NOT crossable,
    every published piece `jb → gb'` gives `(D-c = gb', D-p = jb)`. A NORMAL backward exit edge
    whose reversal is crossable (`CrossB`) gives no demand edge: the next forward run crosses it by
    `revRec`. A demand-layer backward exit edge is always handed off. -/
def demOfN (Pb : Program) (R : Obj → Prop) (pub : Pub) (M : MethodId) (d : DemandEdge) : Prop :=
  d = ⟨zeroFact, none⟩ ∨
  (∃ g, R (.edge M zeroFact (Pb.exit M) g) ∧ d = ⟨g.fact, none⟩) ∨
  (∃ jb gb gb', R (.init M jb) ∧ jb ≠ zeroFact ∧ R (.edge M jb (Pb.exit M) gb) ∧
    ¬ CrossB jb gb ∧ pub M jb gb gb' ∧ d = ⟨gb'.fact, some jb⟩)

/-! ## 5. Witnesses: demanded or recorded (input), justified (output) -/

/-- A record set: the records of a method. -/
abbrev Recs := MethodId → PFact × AFact → Prop

/-- A concrete flow whose every call that returns is DEMANDED (one demand edge covers the entry
    location and the exit location, each with its mark: the restriction is mark-aware, F71) or
    crossed by a crossable RECORD of `rc` whose
    premise covers the entry location and whose pair relation has the pair. A recorded call has no
    inner flow: the record replaces the analysis of the callee. -/
inductive FlowRR (P : Program) (demand : MethodId → DemandEdge → Prop) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRR P demand rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRR P demand rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRR P demand rc M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3 d p} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRR P demand rc c.callee l1 (P.exit c.callee) l2 →
      demand c.callee d → d.din.covers l1 → d.dout = some p → p.covers l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRR P demand rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRR P demand rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRR P demand rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRR P demand rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRR P demand rc M l0 n' l

/-- A concrete vulnerability witness for a forward run with the demand `demand` and the records
    `rc`: its calls down are demanded (a demand edge covers the entry location with its mark), its
    flows are `FlowRR`. -/
inductive ReachRR (P : Program) (demand : MethodId → DemandEdge → Prop) (rc : Recs)
    (roots : List MethodId) : MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRR P demand rc M zeroLoc n l → ReachRR P demand rc roots M n l
  | down {M n l n' c e l1 n2 l2 d} :
      ReachRR P demand rc roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      demand c.callee d → d.din.covers l1 →
      FlowRR P demand rc c.callee l1 n2 l2 → ReachRR P demand rc roots c.callee n2 l2

/-- A concrete flow that the run `R` JUSTIFIES: every call that returns is justified by a published
    piece `j → g'` (of an exit edge `j → g` of `R`) whose premise covers the entry location and
    whose pair relation has the pair, or by a crossable record of `rc` (the records that `R` read).
    `Backward.FlowRD` with the publication and the records. -/
inductive FlowRDN (P : Program) (R : Obj → Prop) (pub : Pub) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRDN P R pub rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRDN P R pub rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRDN P R pub rc M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3 j g g'} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRDN P R pub rc c.callee l1 (P.exit c.callee) l2 →
      R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) → pub c.callee j g g' →
      j.covers l1 → den j g'.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDN P R pub rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDN P R pub rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRDN P R pub rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRDN P R pub rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRDN P R pub rc M l0 n' l

/-- A vulnerability witness that the run `R` justifies: its calls down enter an initial fact of
    `R` that covers the entry location, its flows are `FlowRDN`. -/
inductive ReachRDN (P : Program) (R : Obj → Prop) (pub : Pub) (rc : Recs) (roots : List MethodId) :
    MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRDN P R pub rc M zeroLoc n l → ReachRDN P R pub rc roots M n l
  | down {M n l n' c e l1 n2 l2 j} :
      ReachRDN P R pub rc roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      R (.init c.callee j) → j.covers l1 →
      FlowRDN P R pub rc c.callee l1 n2 l2 → ReachRDN P R pub rc roots c.callee n2 l2

/-! ## 6. The two contracts -/

/-- THE FORWARD CONTRACT of a run `R` with the demand `demand`, the publication `pub` and the
    records `rc`: every demanded-or-recorded witness of a sink pattern with a concrete mark is
    justified by `R`, and `R` reports its vulnerability. `HandoffCoverage.lean` proves it for the
    restricted forward run with `restrictI`. -/
def CoversN (P : Program) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (demand : MethodId → DemandEdge → Prop) (rc : Recs) (R : Obj → Prop) (pub : Pub) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRR P demand rc roots M n l →
    ReachRDN P R pub rc roots M n l ∧ ∃ b, R (.vuln M n s b)

/-- THE BACKWARD CONTRACT (`Backward.BackwardContractD` with the new hand-off): every witness that
    forward run `Rk` justifies (with its publication `pub` and its records `rc`), of a sink that the
    backward run SEEDS, is demanded or recorded in the next forward run (its demand `dnext`, its
    records `rcnext`). `HandoffBackward.lean` proves it for the backward run of the user's design
    with the demand `handF` and the reversed crossable records. -/
def BackwardContractN (P : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (seeds : List (MethodId × Node × PFact))
    (Rk : Obj → Prop) (pub : Pub) (rc : Recs)
    (dnext : MethodId → DemandEdge → Prop) (rcnext : Recs) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRDN P Rk pub rc roots M n l → (M, n, s) ∈ seeds →
    ReachRR P dnext rcnext roots M n l

end ApSpec.Handoff
