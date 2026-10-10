/-
  ApSpec.HandoffXMain — THE EXCLUSION and THE NARROWING OVER ONE ROUND of the hand-off of the DEMAND
  EDGES only (decision F70), on the spec closures WITH THE `[any-taint]` EXCLUSION (decision F69):
  the canonical X run sequence `HandoffXIter.canonStateX` (review item PROOF-3).

  The sequence (`HandoffXIter.lean`): run 0 is `forget6 (D6X … policy1 …)`; forward run `k + 1` is
  `forgetX (DRX … (dem k) emitX satX restrictIX (embedRecs (rc (k + 1))) …)` with the publication
  `pubRX`; the backward run after forward run `k` is the BASE run
  `DB (Program.rev P) … (handF P (R k) (pub k)) emitM satI restrictI (recsBOf …) [] roots (seeds k)
  true`, and it reads forward run `k` on the forgotten view (the exclusions dropped). So the
  backward half of each theorem is the base theorem; only the forward half is new.

  Part 1. THE ZERO PATTERN IN AN X RUN (`emitTX_zero`, `forward_zero_initX`, `forward_zero_edgesX`):
    the emission `emitX` from the entry pattern `zeroFact` gives only the zero fact, not must, with
    no exclusion. So an X run whose demand gives the method `M` only the zero pattern has only the
    initial fact `(zeroFact, not must, no exclusion)` in `M`, and every edge of `M` has this
    premise. The forgotten view has the same property (`forward_zero_init_forgetX`,
    `forward_zero_edges_forgetX`).
  Part 2. THE EXCLUSION OVER ONE ROUND (`exclusion_roundX`, generic in the forward run that the
    hand-off reads) and ON THE CANONICAL X SEQUENCE (`exclusion_canonX`): a method key whose exit
    edges of forward run `k` (on the forgotten view) are all crossable, and with no seed in its call
    subtree, has only the zero fact as an initial fact (and as the premise of every edge) in forward
    run `k + 1`.
  Part 3. THE NARROWING ON THE CANONICAL X SEQUENCE:
    * `narrowing_canonX_fwd` (from `HandoffX.handF_narrowX`): a demand edge that forward run `k + 1`
      hands off lies inside the reversal of a demand edge of its demand, WITH THE EXCLUSIONS of the
      X run (`insideLocXB`); the only exception is the cell (a) of `RExcX` on a DEMAND-LAYER `[any]`
      piece (`FwdExc`);
    * `narrowing_canonX_back` (from `Handoff.demOfN_narrow`): the base theorem on the backward run;
    * the mark-aware forms (F71): `narrowing_canonX_fwdM`, `narrowing_canonX_backM`,
      `narrowing_canonXM` (the marks narrow in every cell: the runs are concrete);
    * `narrowing_canonX`: the two steps composed (every demand edge of forward run `k + 2`);
    * `narrowing_canonX_loc`: the composed location form. The hand-off DROPS the exclusions of the
      X run (DESIGN A2), so a location of the new demand edge lies inside the old demand edge, OR the
      dropped exclusion excluded it (`Dropped`). With no exclusion there is no such location
      (`not_dropped_empty`), and the form is the base form `HandoffMain.narrowing_canon_loc`.
      With concrete seeds with no `*` tail the demand patterns have no `*` tail, the exit side is
      exact, and the entry side drops a location only for the premise exclusion Universe
      (`HandoffNoStar.narrowing_canonX_loc_exact`).
    THE PATTERNS THAT THE NARROWING COVERS: the third case of `demOfN` (a backward exit edge with a
    non-zero premise). The zero demand `(zeroFact, none)` and the seed-path patterns `(gb, none)` of
    the zero-premise backward edges are NOT narrowed (as in the base theorem; decision F70 item 5).
  Part 4. CEGAR (`XMVec`): the `Dropped` disjunct is necessary for the composed step. Each step is
    a real cell of the operations (`decide`): a forward piece inside `D-p` only with its exclusion,
    a backward premise inside that piece on the forgotten view, at a location that `D-p` excludes;
    the same at the entry side for a premise exclusion. (These are vectors of the operations, not a
    program run.)

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffXIter
import ApSpec.HandoffExclusion

namespace ApSpec.HandoffXMain
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffIter
  ApSpec.HandoffExclusion ApSpec.HandoffX ApSpec.HandoffXIter ApSpec.AnyTaint ApSpec.AnyTaintEx
open ApSpec.AnyTaintExCov (forgetX forget6 CovLocX)

/-! ## 0. The forgotten view -/

/-- An initial fact of the forgotten view is an initial fact of the X run (with some must flag and
    some exclusion). -/
theorem forgetX_init {R : XObj → Prop} {M : MethodId} {i : PFact} (h : forgetX R (.init M i)) :
    ∃ mi iex, R (.init M i mi iex) := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | init M' i' mi iex => cases he; exact ⟨mi, iex, hx⟩
  | edge => cases he
  | added => cases he
  | req => cases he
  | vuln => cases he

/-- An edge of the forgotten view is an edge of the X run (with some must flag, some premise
    exclusion and an annotated conclusion with the same base fact). -/
theorem forgetX_edge {R : XObj → Prop} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : forgetX R (.edge M i n f)) : ∃ mi iex fx, R (.edge M i mi iex n fx) ∧ fx.af = f := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | edge M' i' mi iex n' fx => cases he; exact ⟨mi, iex, fx, hx, rfl⟩
  | init => cases he
  | added => cases he
  | req => cases he
  | vuln => cases he

#print axioms forgetX_init
#print axioms forgetX_edge

/-! ## 1. The zero pattern in an X run -/

/-- An emitted premise with the tail `$` has no exclusion (`normJ`, or the chain case). -/
theorem emitX_exact_ex {d a j : PFact} {aex jex : Excl} (h : emitX d a aex = some (j, jex))
    (hk : j.kind = .exact) : jex = Excl.empty := by
  unfold emitX at h
  cases he : emitM d a with
  | none => rw [he] at h; cases h
  | some j0 =>
    rw [he] at h
    dsimp only at h
    cases hr : relate d.path a.path with
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases ha : aex.admits r with
      | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
      | true =>
        rw [ha, if_pos rfl] at h
        exact (congrArg Prod.snd (Option.some.inj h)).symm
    | below r =>
      rw [hr] at h
      have h' := Option.some.inj h
      have e1 : j0 = j := congrArg Prod.fst h'
      have e2 : normJ j0 aex = jex := congrArg Prod.snd h'
      rw [← e2, e1]
      unfold normJ
      rw [hk]
    | apart =>
      rw [hr] at h
      have h' := Option.some.inj h
      have e1 : j0 = j := congrArg Prod.fst h'
      have e2 : normJ j0 aex = jex := congrArg Prod.snd h'
      rw [← e2, e1]
      unfold normJ
      rw [hk]

#print axioms emitX_exact_ex

/-- THE EMISSION FROM THE ZERO PATTERN (`emitX`, with the must flag): only the zero fact, not must,
    with no exclusion. -/
theorem emitTX_zero {a : PFact} {am : Bool} {aex : Excl} {j : PFact} {mj : Bool} {jex : Excl}
    (h : emitTX emitX zeroFact a am aex = some (j, mj, jex)) :
    j = zeroFact ∧ mj = false ∧ jex = Excl.empty := by
  unfold emitTX at h
  cases he : emitX zeroFact a aex with
  | none => rw [he] at h; cases h
  | some p =>
    obtain ⟨j0, jex0⟩ := p
    rw [he] at h
    have h' : ((j0, am && j0.kind.isAny, jex0) : PFact × Bool × Excl) = (j, mj, jex) :=
      Option.some.inj h
    have hj0 : j0 = zeroFact := emitM_zero_din (emitX_emitM he)
    have e1 : j0 = j := congrArg Prod.fst h'
    have e2 : (am && j0.kind.isAny) = mj := congrArg (fun x => x.2.1) h'
    have e3 : jex0 = jex := congrArg (fun x => x.2.2) h'
    have hk : j0.kind = .exact := by rw [hj0]; rfl
    refine ⟨e1 ▸ hj0, ?_, ?_⟩
    · rw [← e2, hj0]
      cases am <;> rfl
    · rw [← e3]
      exact emitX_exact_ex he hk

#print axioms emitTX_zero

/-- Every edge of an X run has its premise (with its must flag and its exclusion) as an initial
    fact. -/
def EdgeInitX (R : XObj → Prop) : XObj → Prop
  | .edge M i mi iex _ _ => R (.init M i mi iex)
  | _ => True

section ForwardX
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Excl → Option (PFact × Excl)}
  {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

theorem DRX_edgeInitX {o : XObj}
    (h : DRX P taint counted L dem emit sat restrict recs sinks roots o) :
    EdgeInitX (DRX P taint counted L dem emit sat restrict recs sinks roots) o := by
  induction h with
  | root => trivial
  | start h0 _ => exact h0
  | step _ _ _ ih => exact ih
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | retRec _ _ _ _ _ _ _ _ _ ih => exact ih
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- An edge of an X run has its premise as an initial fact. -/
theorem DRX_edge_init {M : MethodId} {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L dem emit sat restrict recs sinks roots (.edge M i mi iex n f)) :
    DRX P taint counted L dem emit sat restrict recs sinks roots (.init M i mi iex) :=
  DRX_edgeInitX h

#print axioms DRX_edgeInitX
#print axioms DRX_edge_init

/-- THE X FORM OF `HandoffExclusion.forward_zero_init`. An X run with the emission `emitX` whose
    demand gives `M` only the zero pattern has only the initial fact `(zeroFact, not must, no
    exclusion)` in `M` (rules `root`, `initR`; `answer` needs a request, and the run has none,
    `AnyTaintExCov.concX_all`). Every satisfaction, restriction, record set, sink and root. -/
theorem forward_zero_initX {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact} {mi : Bool} {iex : Excl}
    (h : DRX P taint counted L dem emitX sat restrict recs sinks roots (.init M i mi iex)) :
    i = zeroFact ∧ mi = false ∧ iex = Excl.empty := by
  cases h with
  | root _ => exact ⟨rfl, rfl, rfl⟩
  | initR _ hd he =>
    rw [hdem _ hd] at he
    exact emitTX_zero he
  | answer hq _ _ _ =>
    exact False.elim (AnyTaintExCov.concX_all P taint counted L dem emitX sat restrict recs sinks
      roots emitX_copies hq)

#print axioms forward_zero_initX

/-- In such an X run every edge of `M` has the premise `(zeroFact, not must, no exclusion)`. -/
theorem forward_zero_edgesX {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact} {mi : Bool} {iex : Excl} {n : Node} {f : XFact}
    (h : DRX P taint counted L dem emitX sat restrict recs sinks roots (.edge M i mi iex n f)) :
    i = zeroFact ∧ mi = false ∧ iex = Excl.empty :=
  forward_zero_initX hdem (DRX_edge_init h)

#print axioms forward_zero_edgesX

/-- The same on the forgotten view (the view that the hand-off and the reports read). -/
theorem forward_zero_init_forgetX {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact}
    (h : forgetX (DRX P taint counted L dem emitX sat restrict recs sinks roots) (.init M i)) :
    i = zeroFact := by
  obtain ⟨_, _, hx⟩ := forgetX_init h
  exact (forward_zero_initX hdem hx).1

theorem forward_zero_edges_forgetX {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact} {n : Node} {f : AFact}
    (h : forgetX (DRX P taint counted L dem emitX sat restrict recs sinks roots) (.edge M i n f)) :
    i = zeroFact := by
  obtain ⟨_, _, _, hx, _⟩ := forgetX_edge h
  exact (forward_zero_edgesX hdem hx).1

#print axioms forward_zero_init_forgetX
#print axioms forward_zero_edges_forgetX

end ForwardX

/-! ## 2. The exclusion over one round -/

/-- THE EXCLUSION OVER ONE ROUND, X FORM (the form of `HandoffExclusion.exclusion_round`). Forward
    run `Rk` (any run, read as the hand-off reads it) with the publication `pub`; the backward
    demand lies inside the forward hand-off `handF P Rk pub`; the backward run is the base run
    `DB (Program.rev P) …` with a mark-copying emission and concrete seeds. A method key `M` whose
    exit edges in `Rk` are all crossable, with no seed in its call subtree:
      (1) every backward edge of `M` is the zero-premise edge with the zero fact;
      (2) the hand-off `demOfN` gives `M` only the zero pattern `(zeroFact, none)`;
      (3) the next forward X run (`DRX … emitX …`, every satisfaction, restriction, record set,
          sink and root) has only the initial fact `(zeroFact, not must, no exclusion)` in `M`;
      (4) every edge of `M` there has this premise;
      (5), (6) the same on the forgotten view. -/
theorem exclusion_roundX {P : Program} (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    {Rk : Obj → Prop} {pub : Pub}
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, demB m d → handF P Rk pub m d)
    {emit : PFact → PFact → Option PFact} (hem : EmitCopiesMark emit)
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : BExact.SeedsConc seeds)
    {M : MethodId}
    (hcross : ∀ j g, Rk (.init M j) → Rk (.edge M j (P.exit M) g) → Cross j g)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ Reaches P M N) (pubB : Pub)
    {taint : TaintEdges} {counted' : Acc → Bool} {L' : Nat}
    {sat' : PFact → Excl → PFact → Excl → Bool}
    {restrict' : PFact → Excl → XFact → DemandEdge → Option XFact}
    {recs' : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks' : List (MethodId × Node × PFact)} {roots' : List MethodId} :
    (∀ i n f, DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind
        (.edge M i n f) → i = zeroFact ∧ f = zeroAF) ∧
    (∀ d, demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB
        M d → d = ⟨zeroFact, none⟩) ∧
    (∀ i mi iex, DRX P taint counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB)
        emitX sat' restrict' recs' sinks' roots' (.init M i mi iex) →
        i = zeroFact ∧ mi = false ∧ iex = Excl.empty) ∧
    (∀ i mi iex n f, DRX P taint counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB)
        emitX sat' restrict' recs' sinks' roots' (.edge M i mi iex n f) →
        i = zeroFact ∧ mi = false ∧ iex = Excl.empty) ∧
    (∀ i, forgetX (DRX P taint counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB)
        emitX sat' restrict' recs' sinks' roots') (.init M i) → i = zeroFact) ∧
    (∀ i n f, forgetX (DRX P taint counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB)
        emitX sat' restrict' recs' sinks' roots') (.edge M i n f) → i = zeroFact) := by
  have hdem : ∀ d, ¬ demB M d := by
    intro d hd
    obtain ⟨j, g, _, hj, hg, hnc, _, _⟩ := hdemB M d hd
    exact hnc (hcross j g hj hg)
  have hB := exclusion_backward_nodem (counted := counted) (L := L) (sat := sat)
    (restrict := restrict) (recsB := recsB) (sinksB := sinksB) (rootsB := rootsB) (zbind := zbind)
    hG hcl hem hsd hdem hseed
  have hD := exclusion_demand hB pubB
  have hZ : ∀ d, demOfN (Program.rev P)
      (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pubB
      M d → d.din = zeroFact := fun d h => by rw [hD d h]
  exact ⟨hB, hD, fun _ _ _ h => forward_zero_initX hZ h, fun _ _ _ _ _ h => forward_zero_edgesX hZ h,
    fun _ h => forward_zero_init_forgetX hZ h, fun _ _ _ h => forward_zero_edges_forgetX hZ h⟩

#print axioms exclusion_roundX

/-! ## 3. The canonical X sequence: the exclusion and the narrowing -/

/-- THE FORWARD EXCEPTION OF THE NARROWING IN AN X RUN: the cell (a) of `RExcX` (a DEMAND-LAYER
    `[any]` conclusion `gx` at or above a `*/E` exit pattern `p`): the piece is the chain of `p` with
    the tail `[any]`, in the demand layer, with no exclusion. -/
def FwdExc (gx : XFact) (p : PFact) (g' : AFact) (gex' : Excl) : Prop :=
  gx.af.fact.kind = .any ∧ gx.af.demand = true ∧ (∃ E, p.kind = .star E) ∧
    g'.fact = ⟨gx.af.fact.base, p.path, .any, gx.af.fact.mark⟩ ∧ g'.demand = true ∧
    gex' = Excl.empty

/-- `FwdExc` is the cell (a) of `RExcX`. -/
theorem fwdExc_rExcX {gx : XFact} {p : PFact} {g' : AFact} {gex' : Excl}
    (h : FwdExc gx p g' gex') : RExcX gx p ⟨g', gex'⟩ := by
  obtain ⟨hk, hd, hE, hf, hd', hex⟩ := h
  exact Or.inl ⟨hk, carriesB_demand hd, hE, hf, hd'.trans hd.symm, hex⟩

#print axioms fwdExc_rExcX

/-- A location that the dropped exclusion `e` of the pattern `q` excludes: it lies below the path
    of `q`, and `e` rejects the step down (its first accessor). -/
def Dropped (q : PFact) (e : Excl) (l : Loc) : Prop :=
  ∃ σ, l.path = q.path ++ σ ∧ e.admits σ = false

/-- A location of `q` lies in `p` if every location of `q` that the exclusion `e` admits lies in
    `p`, or the exclusion excludes it. -/
theorem covLoc_split {q p : PFact} {e : Excl} (hin : ∀ l, CovLocX q e l → p.coversLoc l)
    {l : Loc} (hl : q.coversLoc l) : p.coversLoc l ∨ Dropped q e l := by
  obtain ⟨hb, σ, hp, ht⟩ := hl
  cases ha : e.admits σ with
  | true => exact Or.inl (hin l ⟨hb, σ, hp, ht, ha⟩)
  | false => exact Or.inr ⟨σ, hp, ha⟩

/-- No exclusion: no dropped location. -/
theorem not_dropped_empty {q : PFact} {l : Loc} : ¬ Dropped q Excl.empty l := by
  intro ⟨σ, _, h⟩
  rw [admits_empty] at h
  exact Bool.noConfusion h

#print axioms covLoc_split
#print axioms not_dropped_empty

section Canon
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CS" => canonStateX P taint counted Ls LB sinks roots seeds
local notation "DBk" k => backOfX P counted (LB k) roots (seeds k) (CS k)
local notation "DEMk" k => demOfX P counted (LB k) roots (seeds k) (CS k)
local notation "RXk" k => runX P taint counted (Ls (k + 1)) (DEMk k) (RunStateX.rc (CS (k + 1))) sinks
  roots

/-- THE EXCLUSION ON THE CANONICAL X SEQUENCE. A method key `M` whose exit edges in forward run `k`
    (read on the forgotten view, as the hand-off reads them) are all crossable, and with no seed of
    the backward run after run `k` in its call subtree:
      (1) every edge of `M` in the backward run is the zero-premise edge with the zero fact (the
          base theorem: the backward run is the base run);
      (2) the demand of forward run `k + 1` gives `M` only the zero pattern `(zeroFact, none)`;
      (3) the X run `k + 1` (`DRX … emitX satX restrictIX …`) has only the initial fact
          `(zeroFact, not must, no exclusion)` in `M`, and (4) every edge of `M` there has this
          premise;
      (5), (6) on the forgotten view `(CS (k + 1)).R`: every initial fact of `M` is `zeroFact`, and
          every edge of `M` has the premise `zeroFact`.
    Program hypotheses: `NoZeroGenP` and no cleaner on the zero base; the seeds have concrete
    marks. Run 0 (`D6X`) needs no hypothesis: the hand-off reads only its forgotten view. -/
theorem exclusion_canonX (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    (k : Nat) (hsd : BExact.SeedsConc (seeds k)) {M : MethodId}
    (hcross : ∀ j g, (CS k).R (.init M j) → (CS k).R (.edge M j (P.exit M) g) → Cross j g)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds k → ¬ Reaches P M N) :
    (∀ i n f, (DBk k) (.edge M i n f) → i = zeroFact ∧ f = zeroAF) ∧
    (∀ d, (DEMk k) M d → d = ⟨zeroFact, none⟩) ∧
    (∀ i mi iex, (RXk k) (.init M i mi iex) → i = zeroFact ∧ mi = false ∧ iex = Excl.empty) ∧
    (∀ i mi iex n f, (RXk k) (.edge M i mi iex n f) →
      i = zeroFact ∧ mi = false ∧ iex = Excl.empty) ∧
    (∀ i, (CS (k + 1)).R (.init M i) → i = zeroFact) ∧
    (∀ i n f, (CS (k + 1)).R (.edge M i n f) → i = zeroFact) :=
  exclusion_roundX (Rk := (CS k).R) (pub := (CS k).pub) (counted := counted) (L := LB k)
    (demB := handF P (CS k).R (CS k).pub) (emit := emitM) (sat := satI) (restrict := restrictI)
    (recsB := recsBOf P (CS k).R (CS k).rc) (sinksB := []) (rootsB := roots) (zbind := true)
    (taint := taint) (counted' := counted) (L' := Ls (k + 1)) (sat' := satX)
    (restrict' := restrictIX) (recs' := embedRecs (CS (k + 1)).rc) (sinks' := sinks)
    (roots' := roots) hG hcl (fun _ _ h => h) RCov.emitM_copies hsd hcross hseed
    (pubR (handF P (CS k).R (CS k).pub))

#print axioms exclusion_canonX

/-- THE NARROWING, FORWARD TO BACKWARD, ON THE CANONICAL X SEQUENCE (`HandoffX.handF_narrowX` on
    the sequence, with the exceptions of a concrete run). Every demand edge `d'` that forward run
    `k + 1` hands off is `⟨g', some j⟩` for an annotated exit edge `(j, mj, jex) → gx` of the X run
    `k + 1` and a demand edge `d` of its demand that restricts it to `(g', gex')`: the premise `j`
    WITH ITS EXCLUSION `jex` lies inside `D-c` of `d`, and the piece `g'` WITH ITS EXCLUSION `gex'`
    lies inside `D-p` of `d`, except the cell `FwdExc` (the cell (a) of `RExcX` on a demand-layer
    `[any]` conclusion; the cell (b), a `*` conclusion, does not occur: the run is concrete,
    `AnyTaintExCov.concX_all`). -/
theorem narrowing_canonX_fwd (k : Nat) {m : MethodId} {d' : DemandEdge}
    (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ j mj jex gx g' gex' d p, (RXk k) (.edge m j mj jex (P.exit m) gx) ∧
      (DEMk k) m d ∧ d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideLocXB j jex d.din = true ∧
      (insideLocXB g'.fact gex' p = true ∨ FwdExc gx p g' gex') := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, hcon⟩ :=
    handF_narrowX (R := RXk k) (dem := DEMk k) h
  refine ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, ?_⟩
  obtain ⟨_, ⟨t, ht⟩, hns, _⟩ :=
    AnyTaintExCov.concX_all P taint counted (Ls (k + 1)) (DEMk k) emitX satX restrictIX
      (embedRecs (CS (k + 1)).rc) sinks roots emitX_copies hR
  rcases hcon with hc | hc
  · exact Or.inl hc
  · right
    rcases hc with ⟨hk, hcar, hE, hf, hdm, hex⟩ | ⟨⟨e, hk⟩, _⟩
    · have hgd : gx.af.demand = true := by
        unfold carriesB at hcar
        rw [hk, ht] at hcar
        cases hdm' : gx.af.demand with
        | true => rfl
        | false => rw [hdm'] at hcar; exact absurd hcar (fun h' => Bool.noConfusion h')
      exact ⟨hk, hgd, hE, hf, hdm.trans hgd, hex⟩
    · rw [hk] at hns
      exact absurd hns (fun h' => Bool.noConfusion h')

#print axioms narrowing_canonX_fwd

/-- THE NARROWING, BACKWARD TO FORWARD, ON THE CANONICAL X SEQUENCE (`Handoff.demOfN_narrow`: the
    backward run is the base run). Every demand edge `d'` of forward run `k + 1` is the zero demand,
    a zero-premise backward edge (a seed path), or lies inside the reversal of the backward demand
    edge `d` (a hand-off of forward run `k`, read on the forgotten view) that published it, except
    in the cells of `RExc`. -/
theorem narrowing_canonX_back (k : Nat) {M : MethodId} {d' : DemandEdge} (h : (DEMk k) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk k) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, (DBk k) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk k) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      handF P (CS k).R (CS k).pub M d ∧ d.dout = some p ∧ restrictI jb gb d = some gb' ∧
      d' = ⟨gb'.fact, some jb⟩ ∧ insideLocB jb d.din = true ∧
      (insideLocB gb'.fact p = true ∨ RExc gb p gb') :=
  demOfN_narrow h

#print axioms narrowing_canonX_back

/-- THE NARROWING OVER ONE ROUND ON THE CANONICAL X SEQUENCE. Every demand edge `d''` of forward run
    `k + 2` is the zero demand, a zero-premise backward edge (a seed path; not narrowed), or comes
    from a demand edge `d` of forward run `k + 1` (same method) through the annotated forward exit
    edge `(j, mj, jex) → gx` of the X run `k + 1` (piece `(g', gex')`, handed off as
    `⟨g', some j⟩` with the exclusions dropped) and the backward exit edge `jb → gb` (piece `gb'`):
      * its exit pattern `jb` lies inside `g'` (base locations), and `g'` WITH ITS EXCLUSION `gex'`
        lies inside `D-p` of `d`, except the cell `FwdExc`;
      * its entry pattern `gb'` lies inside `j` (base locations), except `RExc gb j gb'`, and `j`
        WITH ITS EXCLUSION `jex` lies inside `D-c` of `d`. -/
theorem narrowing_canonX (k : Nat) {M : MethodId} {d'' : DemandEdge}
    (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ j mj jex gx g' gex' d p jb gb gb',
      (RXk k) (.edge M j mj jex (P.exit M) gx) ∧
      (DEMk k) M d ∧ d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧
      (DBk (k + 1)) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk (k + 1)) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      restrictI jb gb ⟨g'.fact, some j⟩ = some gb' ∧ d'' = ⟨gb'.fact, some jb⟩ ∧
      (∀ l, jb.coversLoc l → g'.fact.coversLoc l) ∧
      ((∀ l, CovLocX g'.fact gex' l → p.coversLoc l) ∨ FwdExc gx p g' gex') ∧
      ((∀ l, gb'.fact.coversLoc l → j.coversLoc l) ∨ RExc gb j gb') ∧
      (∀ l, CovLocX j jex l → d.din.coversLoc l) := by
  rcases narrowing_canonX_back (k + 1) h with h1 | h2 | ⟨jb, gb, gb', dB, pB, hjb, hne, hgb, hncb,
    hdB, hdo, hres, hd'', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdop, hresF, hdB', hinF, hconF⟩ :=
      narrowing_canonX_fwd k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    refine Or.inr (Or.inr ⟨pB, mj, jex, gx, g', gex', d, p, jb, gb, gb', hR, hdem, hdop, hresF,
      hjb, hne, hgb, hncb, hres, hd'', fun l hl => insideLoc_coversLoc hin hl, ?_, ?_,
      fun l hl => insideLocXB_sound hinF hl⟩)
    · rcases hconF with hc | hc
      · exact Or.inl (fun l hl => insideLocXB_sound hc hl)
      · exact Or.inr hc
    · rcases hcon with hc | hc
      · exact Or.inl (fun l hl => insideLoc_coversLoc hc hl)
      · exact Or.inr hc

#print axioms narrowing_canonX

/-- THE COMPOSED LOCATION FORM ON THE CANONICAL X SEQUENCE. A demand edge `d''` of forward run
    `k + 2` with a non-zero premise comes from a demand edge `d` of forward run `k + 1` (through the
    annotated exit edge `(j, mj, jex) → gx` of the X run `k + 1` and its piece `(g', gex')`), and:
      * every exit location of `d''` is an exit location of `d`, OR the dropped exclusion `gex'` of
        the forward piece excludes it (`Dropped g'.fact gex'`); except the cell `FwdExc`;
      * every entry location of `d''` is an entry location of `d`, OR the dropped exclusion `jex` of
        the forward premise excludes it (`Dropped j jex`); except a cell of `RExc`.
    With no exclusion (`gex' = {}`, `jex = {}`) no location is dropped (`not_dropped_empty`), and
    this is the base form `HandoffMain.narrowing_canon_loc`. The zero demand and the seed-path
    patterns `(g, none)` are not narrowed. -/
theorem narrowing_canonX_loc (k : Nat) {M : MethodId} {d'' : DemandEdge}
    (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ j mj jex gx g' gex' d p jb gb',
      (RXk k) (.edge M j mj jex (P.exit M) gx) ∧ (DEMk k) M d ∧ d.dout = some p ∧
      restrictIX j jex gx d = some ⟨g', gex'⟩ ∧ d'' = ⟨gb'.fact, some jb⟩ ∧
      ((∀ l, jb.coversLoc l → p.coversLoc l ∨ Dropped g'.fact gex' l) ∨ FwdExc gx p g' gex') ∧
      ((∀ l, gb'.fact.coversLoc l → d.din.coversLoc l ∨ Dropped j jex l) ∨
        ∃ gb, RExc gb j gb') := by
  rcases narrowing_canonX k h with h1 | h2 | ⟨j, mj, jex, gx, g', gex', d, p, jb, gb, gb', hR, hdem,
    hdop, hresF, _, _, _, _, _, hd'', hjb, hF, hB, hj⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨j, mj, jex, gx, g', gex', d, p, jb, gb', hR, hdem, hdop, hresF, hd'', ?_,
      ?_⟩)
    · rcases hF with hc | hc
      · exact Or.inl (fun l hl => covLoc_split hc (hjb l hl))
      · exact Or.inr hc
    · rcases hB with hc | hc
      · exact Or.inl (fun l hl => covLoc_split hj (hc l hl))
      · exact Or.inr ⟨gb, hc⟩

#print axioms narrowing_canonX_loc

/-! ### The narrowing with the marks (F71, the mark-aware restriction)

  `restrictIX` has the mark tests of `restrictI` (`insideXB`, `concMarkB`). The X runs are concrete
  (`AnyTaintExCov.concX_all`) and the backward runs are concrete with seeds of concrete marks
  (`BExact.DB_edge_concrete`), so the marks narrow in every cell. -/

/-- THE NARROWING, FORWARD TO BACKWARD, ON THE CANONICAL X SEQUENCE, MARK-AWARE: as
    `narrowing_canonX_fwd`, with the marks (`insideXB`); in the cell `FwdExc` the mark of the piece
    is still a mark of `D-p`. -/
theorem narrowing_canonX_fwdM (k : Nat) {m : MethodId} {d' : DemandEdge}
    (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ j mj jex gx g' gex' d p, (RXk k) (.edge m j mj jex (P.exit m) gx) ∧
      (DEMk k) m d ∧ d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideXB j jex d.din = true ∧
      (insideXB g'.fact gex' p = true ∨
        (FwdExc gx p g' gex' ∧ markSubB p.mark g'.fact.mark = true)) := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', _, hcon⟩ :=
    narrowing_canonX_fwd k h
  obtain ⟨p0, hdo0, hin, hcm, hc⟩ := restrictIX_someM hres
  have hp0 : p0 = p := Option.some.inj (hdo0.symm.trans hdo)
  subst hp0
  obtain ⟨_, ⟨t, ht⟩, _, _⟩ :=
    AnyTaintExCov.concX_all P taint counted (Ls (k + 1)) (DEMk k) emitX satX restrictIX
      (embedRecs (CS (k + 1)).rc) sinks roots emitX_copies hR
  have hmk : markSubB p0.mark g'.fact.mark = true := by
    have hgm : g'.fact.mark = gx.af.fact.mark := restrictConcIX_mark hc
    rw [hgm, ht, ← RAux.concMarkB_conc, ← ht]
    exact hcm
  refine ⟨j, mj, jex, gx, g', gex', d, p0, hR, hdem, hdo, hres, hd', hin, ?_⟩
  rcases hcon with hc' | hc'
  · exact Or.inl (insideXB_intro hc' hmk)
  · exact Or.inr ⟨hc', hmk⟩

#print axioms narrowing_canonX_fwdM

/-- THE NARROWING, BACKWARD TO FORWARD, ON THE CANONICAL X SEQUENCE, MARK-AWARE (the backward run
    is the base run; its seeds have concrete marks). -/
theorem narrowing_canonX_backM (k : Nat) (hsd : BExact.SeedsConc (seeds k)) {M : MethodId}
    {d' : DemandEdge} (h : (DEMk k) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk k) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, (DBk k) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk k) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      handF P (CS k).R (CS k).pub M d ∧ d.dout = some p ∧ restrictI jb gb d = some gb' ∧
      d' = ⟨gb'.fact, some jb⟩ ∧ insideB jb d.din = true ∧
      (insideB gb'.fact p = true ∨ (RExc gb p gb' ∧ markSubB p.mark gb'.fact.mark = true)) := by
  rcases demOfN_narrow h with h1 | h2 | ⟨jb, gb, gb', d, p, hi, hz, he, hnc, hdem, hdo, hres,
    hd', _, _⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete RCov.emitM_copies hsd he
    obtain ⟨p', hdo', hin, hcon⟩ := restrictI_narrow_conc hres ht
    have hpp : p' = p := Option.some.inj (hdo'.symm.trans hdo)
    subst hpp
    exact Or.inr (Or.inr ⟨jb, gb, gb', d, p', hi, hz, he, hnc, hdem, hdo, hres, hd', hin, hcon⟩)

#print axioms narrowing_canonX_backM

/-- THE NARROWING OVER ONE ROUND ON THE CANONICAL X SEQUENCE, MARK-AWARE: `narrowing_canonX` in
    the locations AND the marks. The forward piece and premise are read with their exclusions and
    marks (`CovLocX` and the mark); in the exception cells the marks still narrow. -/
theorem narrowing_canonXM (k : Nat) (hsd : BExact.SeedsConc (seeds (k + 1))) {M : MethodId}
    {d'' : DemandEdge} (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ j mj jex gx g' gex' d p jb gb gb',
      (RXk k) (.edge M j mj jex (P.exit M) gx) ∧
      (DEMk k) M d ∧ d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧
      (DBk (k + 1)) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk (k + 1)) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      restrictI jb gb ⟨g'.fact, some j⟩ = some gb' ∧ d'' = ⟨gb'.fact, some jb⟩ ∧
      (∀ l, jb.covers l → g'.fact.covers l) ∧
      ((∀ l, CovLocX g'.fact gex' l → g'.fact.mark.admits l.mark → p.covers l) ∨
        (FwdExc gx p g' gex' ∧ ∀ x, g'.fact.mark.admits x → p.mark.admits x)) ∧
      ((∀ l, gb'.fact.covers l → j.covers l) ∨
        (RExc gb j gb' ∧ ∀ x, gb'.fact.mark.admits x → j.mark.admits x)) ∧
      (∀ l, CovLocX j jex l → j.mark.admits l.mark → d.din.covers l) := by
  rcases narrowing_canonX_backM (k + 1) hsd h with h1 | h2 | ⟨jb, gb, gb', dB, pB, hjb, hne, hgb,
    hncb, hdB, hdo, hres, hd'', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdop, hresF, hdB', hinF, hconF⟩ :=
      narrowing_canonX_fwdM k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    refine Or.inr (Or.inr ⟨pB, mj, jex, gx, g', gex', d, p, jb, gb, gb', hR, hdem, hdop, hresF,
      hjb, hne, hgb, hncb, hres, hd'', fun l hl => insideB_covers hin hl, ?_, ?_,
      fun l hl hm => insideXB_sound hinF hl hm⟩)
    · rcases hconF with hc | ⟨hc, hm⟩
      · exact Or.inl (fun l hl hlm => insideXB_sound hc hl hlm)
      · exact Or.inr ⟨hc, fun x hx => CoreAux.markSubB_sound hm hx⟩
    · rcases hcon with hc | ⟨hc, hm⟩
      · exact Or.inl (fun l hl => insideB_covers hc hl)
      · exact Or.inr ⟨hc, fun x hx => CoreAux.markSubB_sound hm hx⟩

#print axioms narrowing_canonXM

end Canon

/-! ## 4. CEGAR: the dropped exclusions are real cells of the operations -/

namespace XMVec

/-- The premise `1.$` (mark `1`) and the entry pattern `1.$`. -/
def j1 : PFact := ⟨1, [], .exact, .conc 1⟩
def dc1 : PFact := ⟨1, [], .exact, .star⟩
/-- An `[any-taint]/{4}` conclusion `2.[any-taint]/{4}` (normal, mark `1`). -/
def gTaint : XFact := ⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .set [4]⟩
/-- The exit pattern `2.*/{4}`. -/
def pS4 : PFact := ⟨2, [], .star (.set [4]), .star⟩
/-- The base fact of the forward piece: `2.[any]` (its exclusion `{4, 4}` is dropped). -/
def gPiece : PFact := ⟨2, [], .any, .conc 1⟩
/-- A backward premise `2.[4].$` and a backward conclusion `1.$`. -/
def jb4 : PFact := ⟨2, [4], .exact, .conc 1⟩
def gb1 : AFact := ⟨⟨1, [], .exact, .conc 1⟩, false⟩

/-- THE EXIT SIDE. The forward cell `[any-taint]/{4} ∩ */{4}` gives the piece `2.[any]` with the
    exclusion `{4, 4}`; the piece lies inside `D-p = 2.*/{4}` only with its exclusion. The hand-off
    `⟨2.[any], some 1.$⟩` drops it; a backward premise `2.[4].$` lies inside `2.[any]`, and the
    backward restriction keeps its edge `2.[4].$ → 1.$`. So the new demand edge has the exit pattern
    `2.[4].$`. -/
theorem exit_dropped :
    restrictIX j1 Excl.empty gTaint ⟨dc1, some pS4⟩ = some ⟨⟨gPiece, false⟩, .set [4, 4]⟩ ∧
    insideLocXB gPiece (.set [4, 4]) pS4 = true ∧ insideLocB gPiece pS4 = false ∧
    insideLocB jb4 gPiece = true ∧
    restrictI jb4 gb1 ⟨gPiece, some j1⟩ = some gb1 := by decide

/-- The exit location `2.[4]` of the new demand edge is not in `D-p = 2.*/{4}`; it is a dropped
    location of the piece. -/
theorem exit_dropped_loc :
    jb4.coversLoc ⟨2, [4], 1⟩ ∧ ¬ pS4.coversLoc ⟨2, [4], 1⟩ ∧
    Dropped gPiece (.set [4, 4]) ⟨2, [4], 1⟩ := by
  refine ⟨⟨rfl, [], rfl, rfl⟩, ?_, ⟨[4], rfl, rfl⟩⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [4] := by
    have h' : [4] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  rw [hσ] at ht
  exact Bool.noConfusion ht

/-- The premise `1.[any-taint]` emitted from the added fact `1.[any-taint]/{4}` by the entry
    pattern `1.[any]` (premise exclusion `{4}`); the entry pattern `1.*/{4}`; the conclusion `2.$`
    and the exit pattern `2.$`. -/
def jA : PFact := ⟨1, [], .any, .conc 1⟩
def dcA : PFact := ⟨1, [], .any, .star⟩
def dcS4 : PFact := ⟨1, [], .star (.set [4]), .star⟩
def gExact : XFact := ⟨⟨⟨2, [], .exact, .conc 1⟩, false⟩, Excl.empty⟩
def pE : PFact := ⟨2, [], .exact, .star⟩
/-- A backward premise `2.$` and a backward conclusion `1.[4].$`. -/
def jbE : PFact := ⟨2, [], .exact, .conc 1⟩
def gb4 : AFact := ⟨⟨1, [4], .exact, .conc 1⟩, false⟩

/-- THE ENTRY SIDE. `emitX` gives the premise `1.[any]` with the exclusion `{4}`; it lies inside
    `D-c = 1.*/{4}` only with its exclusion, and the restriction by `⟨1.*/{4}, some 2.$⟩` keeps the
    exit edge `2.$`. The hand-off `⟨2.$, some 1.[any]⟩` drops the exclusion; the backward
    restriction keeps the backward edge `2.$ → 1.[4].$`. So the new demand edge has the entry
    pattern `1.[4].$`. -/
theorem entry_dropped :
    emitX dcA jA (.set [4]) = some (jA, .set [4]) ∧
    insideLocXB jA (.set [4]) dcS4 = true ∧ insideLocB jA dcS4 = false ∧
    restrictIX jA (.set [4]) gExact ⟨dcS4, some pE⟩ = some gExact ∧
    insideLocB jbE gExact.af.fact = true ∧
    restrictI jbE gb4 ⟨gExact.af.fact, some jA⟩ = some gb4 := by decide

/-- The entry location `1.[4]` of the new demand edge is not in `D-c = 1.*/{4}`; it is a dropped
    location of the premise. -/
theorem entry_dropped_loc :
    gb4.fact.coversLoc ⟨1, [4], 1⟩ ∧ ¬ dcS4.coversLoc ⟨1, [4], 1⟩ ∧
    Dropped jA (.set [4]) ⟨1, [4], 1⟩ := by
  refine ⟨⟨rfl, [], rfl, rfl⟩, ?_, ⟨[4], rfl, rfl⟩⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [4] := by
    have h' : [4] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  rw [hσ] at ht
  exact Bool.noConfusion ht

#print axioms exit_dropped
#print axioms exit_dropped_loc
#print axioms entry_dropped
#print axioms entry_dropped_loc

end XMVec

end ApSpec.HandoffXMain
