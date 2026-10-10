/-
  ApSpec.HandoffMain — the end-to-end theorems of the hand-off of the DEMAND EDGES only
  (decision F70), on the run sequence of the spec rules.

  Part 1. THE CANONICAL RUN SEQUENCE (`canonState`), by recursion over the state of a forward
    run (its result, its publication, its record set):
      * run 0: `D P counted (Ls 0) policy1 sinks roots`, the publication `pubD`, no record;
      * the backward run after forward run `k` (`backOf`):
          `DB (Program.rev P) counted (LB k) (handF P (R k) (pub k)) emitM satI restrictI
             (recsBOf P (R k) (rc k)) [] roots (seeds k) true`;
      * the demand of run `k + 1` (`demOf`): `demOfN (Program.rev P) DBk (pubR (handF …))`;
      * the records of run `k + 1`: `rcNextOf P (R k) (rc k) DBk`;
      * run `k + 1`: `DR P counted (Ls (k + 1)) (dem k) emitM satI restrictI (rc (k + 1)) sinks
        roots`, the publication `pubR (dem k)`.
    The seeds `seeds k` are a parameter: every vulnerability that run `k` reports is confirmed
    (a predicate `C k`) or seeded.
  Part 2. THE ITERATION (`iteration_generalN`): every real vulnerability (a sink pattern with a
    concrete mark and the tail `$` or `[any]`) is, at every forward run `k`, reported by run `k`
    or confirmed by an earlier run. Corollary `iteration_generalN_all`: if every reported
    vulnerability is seeded, every forward run reports every real vulnerability.
    The inclusion form (`iteration_generalN_incl`): the driver may hand off MORE demand edges and
    MORE records than the canonical sets (`runSeqN`, `pubSeqN`).
  Part 3. THE EXCLUSION (`exclusion_canon`): a method key with only crossable exit edges in
    forward run `k` and no seed in its call subtree has only the zero fact as an initial fact (and
    as the premise of every edge) in forward run `k + 1`.
  Part 4. THE NARROWING (`narrowing_canon_fwd`, `narrowing_canon_back`, `narrowing_canon`): every
    demand edge that run `k + 1` hands off lies inside the reversal of a demand edge of its
    demand; every non-zero demand edge of run `k + 1` lies inside the reversal of a backward demand
    edge; so every non-zero demand edge of run `k + 2` lies inside a demand edge of run `k + 1`
    (with the exceptions `RExc` of `HandoffRestrict.lean`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffBackward
import ApSpec.HandoffIter
import ApSpec.HandoffExclusion
import ApSpec.HandoffCoverage

namespace ApSpec.HandoffMain
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward
  ApSpec.HandoffIter ApSpec.HandoffExclusion

/-! ## Part 1. The canonical run sequence -/

/-- The state of a forward run: its result, its publication and the records it read. -/
structure RunState where
  R : Obj → Prop
  pub : Pub
  rc : Recs

/-- The backward run after the forward run `s` (field limit `LB`, seeds `seeds`): demand
    `handF`, records `recsBOf`, no forward sink, started at the forward roots, the zero rules on. -/
abbrev backOf (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunState) : Obj → Prop :=
  DB (Program.rev P) counted LB (handF P s.R s.pub) emitM satI restrictI (recsBOf P s.R s.rc) []
    roots seeds true

/-- The demand that the backward run after `s` hands off to the next forward run. -/
abbrev demOf (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunState) : MethodId → DemandEdge → Prop :=
  demOfN (Program.rev P) (backOf P counted LB roots seeds s) (pubR (handF P s.R s.pub))

/-- The records of the next forward run. -/
abbrev rcOf (P : Program) (counted : Acc → Bool) (LB : Nat) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (s : RunState) : Recs :=
  rcNextOf P s.R s.rc (backOf P counted LB roots seeds s)

/-- One round: from forward run `k` (state `s`) to forward run `k + 1`. -/
def stepState (P : Program) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) (k : Nat) (s : RunState) : RunState where
  R := DR P counted (Ls (k + 1)) (demOf P counted (LB k) roots (seeds k) s) emitM satI restrictI
    (rcOf P counted (LB k) roots (seeds k) s) sinks roots
  pub := pubR (demOf P counted (LB k) roots (seeds k) s)
  rc := rcOf P counted (LB k) roots (seeds k) s

/-- Run 0: `D … policy1 …`, the publication `pubD`, no record. -/
def state0 (P : Program) (counted : Acc → Bool) (L0 : Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : RunState where
  R := D P counted L0 policy1 sinks roots
  pub := pubD
  rc := fun _ _ => False

/-- THE CANONICAL RUN SEQUENCE of the spec rules. -/
def canonState (P : Program) (counted : Acc → Bool) (Ls LB : Nat → Nat)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) : Nat → RunState
  | 0 => state0 P counted (Ls 0) sinks roots
  | k + 1 => stepState P counted Ls LB sinks roots seeds k
      (canonState P counted Ls LB sinks roots seeds k)

section Canon
variable {P : Program} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CS" => canonState P counted Ls LB sinks roots seeds
local notation "DBk" k => backOf P counted (LB k) roots (seeds k) (CS k)
local notation "DEMk" k => demOf P counted (LB k) roots (seeds k) (CS k)

theorem canon_zero : CS 0 = state0 P counted (Ls 0) sinks roots := rfl

theorem canon_succ (k : Nat) : CS (k + 1) = stepState P counted Ls LB sinks roots seeds k (CS k) :=
  rfl

#print axioms canon_zero
#print axioms canon_succ

/-- Every publication of the sequence only removes pairs. -/
theorem canon_pubSub (k : Nat) :
    ∀ m j g g', (CS k).pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubR_sub (DEMk k)

#print axioms canon_pubSub

/-- Run 0 justifies every real witness and reports it. -/
theorem canon_run0 (hW : P.WF) :
    Run0Contract P roots sinks (CS 0).R (CS 0).pub (CS 0).rc :=
  run1_justifies P counted (Ls 0) sinks roots hW

/-- The forward contract of every restricted run of the sequence. -/
theorem canon_covers (hW : P.WF) (k : Nat) :
    CoversN P roots sinks (DEMk k) (CS (k + 1)).rc (CS (k + 1)).R (CS (k + 1)).pub :=
  coversN_DR P counted (Ls (k + 1)) (DEMk k) (CS (k + 1)).rc sinks roots hW

/-- The backward contract of every backward run of the sequence. -/
theorem canon_backward (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any) (k : Nat) :
    BackwardContractN P roots sinks (seeds k) (CS k).R (CS k).pub (CS k).rc (DEMk k)
      (CS (k + 1)).rc :=
  B_generalN_canon (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
    (canon_pubSub k)

#print axioms canon_run0
#print axioms canon_covers
#print axioms canon_backward

/-! ## Part 2. The iteration -/

/-- THE GENERAL ITERATION THEOREM OF THE NEW HAND-OFF. On the canonical run sequence, every real
    vulnerability (a sink pattern with a concrete mark) is, at every forward run `k`, reported by
    run `k` or confirmed by an earlier run, if every reported vulnerability of a run is confirmed
    (`C`) or seeded. Program hypotheses as `Backward.iteration_general`: well-formed, mark-agnostic
    binding targets, mark-reversible statements, no zero binding back, the zero kept by every
    instruction, every node of a method reaches its exit; the sinks have the tail `$` or
    `[any]`. -/
theorem iteration_generalN (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {C : Nat → MethodId → Node → PFact → Prop}
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_abstract_or (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc) (dem := fun k => DEMk k) (seeds := seeds)
    (canon_run0 hW) (canon_covers hW) (canon_backward hW hT hmr hNZB hZ hX hk) hseeds
    hRe hs hT' hsc

#print axioms iteration_generalN

/-- THE COROLLARY: if the backward run after each forward run seeds every reported vulnerability,
    every forward run of the canonical sequence reports every real vulnerability. -/
theorem iteration_generalN_all (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (hseeds : ∀ k M n s b, (CS k).R (.vuln M n s b) → (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, (CS k).R (.vuln M n s b) :=
  iteration_all_seeded (R := fun k => (CS k).R) (pub := fun k => (CS k).pub)
    (rc := fun k => (CS k).rc) (dem := fun k => DEMk k) (seeds := seeds)
    (canon_run0 hW) (canon_covers hW) (canon_backward hW hT hmr hNZB hZ hX hk) hseeds
    hRe hs hT' hsc

#print axioms iteration_generalN_all

/-! ## Part 3. The exclusion on the canonical sequence -/

/-- THE EXCLUSION ON THE CANONICAL SEQUENCE. A method key `M` whose exit edges in forward run `k`
    are all crossable, and with no seed of the backward run after run `k` in its call subtree, has
    only the zero fact as an initial fact in forward run `k + 1`, and every edge of `M` there has
    the zero premise. Program hypotheses: `NoZeroGenP` and no cleaner on the zero base; the seeds
    have concrete marks. -/
theorem exclusion_canon (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    (k : Nat) (hsd : BExact.SeedsConc (seeds k)) {M : MethodId}
    (hcross : ∀ j g, (CS k).R (.init M j) → (CS k).R (.edge M j (P.exit M) g) → Cross j g)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds k → ¬ Reaches P M N) :
    (∀ i, (CS (k + 1)).R (.init M i) → i = zeroFact) ∧
    (∀ i n f, (CS (k + 1)).R (.edge M i n f) → i = zeroFact) :=
  exclusion_round (Rk := (CS k).R) (pub := (CS k).pub) (counted := counted) (L := LB k)
    (demB := handF P (CS k).R (CS k).pub) (recsB := recsBOf P (CS k).R (CS k).rc) (sinksB := [])
    (rootsB := roots) (zbind := true) (counted' := counted) (L' := Ls (k + 1)) (sat' := satI)
    (restrict' := restrictI) (rc' := (CS (k + 1)).rc) (sinks' := sinks) (roots' := roots)
    hG hcl (fun _ _ h => h) hsd hcross hseed

#print axioms exclusion_canon

/-! ## Part 4. The narrowing on the canonical sequence -/

/-- THE NARROWING, FORWARD TO BACKWARD (`handF_narrow_DR` on the sequence). Every demand edge `d'`
    that forward run `k + 1` hands off comes from a demand edge `d` of its demand that published
    it: the premise `j` (the exit pattern of `d'`) lies inside `D-c` of `d`, and the piece `g'`
    (the entry pattern of `d'`) lies inside `D-p` of `d`, except the `[any]` cell of `RExc`. -/
theorem narrowing_canon_fwd (k : Nat) {m : MethodId} {d' : DemandEdge}
    (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ j g g' d p, (CS (k + 1)).R (.init m j) ∧
      (DEMk k) m d ∧ d.dout = some p ∧ restrictI j g d = some g' ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideLocB j d.din = true ∧
      (insideLocB g'.fact p = true ∨
       (g.fact.kind = .any ∧ (∃ E, p.kind = .star E) ∧
         g'.fact = ⟨g.fact.base, p.path, .any, g.fact.mark⟩ ∧ g'.demand = g.demand)) :=
  handF_narrow_DR h

#print axioms narrowing_canon_fwd

/-- THE NARROWING, BACKWARD TO FORWARD (`demOfN_narrow` on the sequence). Every demand edge `d'` of
    forward run `k + 1` is the zero demand, a zero-premise backward edge, or lies inside the
    reversal of the backward demand edge `d` (a hand-off of forward run `k`) that published it,
    except in the cells of `RExc`. -/
theorem narrowing_canon_back (k : Nat) {M : MethodId} {d' : DemandEdge} (h : (DEMk k) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk k) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, (DBk k) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk k) (.edge M jb ((Program.rev P).exit M) gb) ∧
      ¬ CrossB jb gb ∧
      handF P (CS k).R (CS k).pub M d ∧ d.dout = some p ∧ restrictI jb gb d = some gb' ∧
      d' = ⟨gb'.fact, some jb⟩ ∧ insideLocB jb d.din = true ∧
      (insideLocB gb'.fact p = true ∨ RExc gb p gb') :=
  demOfN_narrow h

#print axioms narrowing_canon_back

/-- THE NARROWING OVER ONE ROUND (the user's rule: the demand of a run lies inside the demand of
    the run before it). Every demand edge `d''` of forward run `k + 2` is the zero demand, a
    zero-premise backward edge, or comes from a demand edge `d` of forward run `k + 1` (same
    method) through the forward exit edge `j → g` of run `k + 1` (piece `g'`) and the backward exit
    edge `jb → gb` (piece `gb'`):
      * its exit pattern `jb` lies inside `g'`, and `g'` lies inside `D-p` of `d` (except the
        `[any]` cell of `RExc`);
      * its entry pattern `gb'` lies inside `j` (except `RExc gb j gb'`), and `j` lies inside
        `D-c` of `d`.
    So, when no exception cell occurs, `d''` lies inside `d` (`narrowing_canon_loc`). -/
theorem narrowing_canon (k : Nat) {M : MethodId} {d'' : DemandEdge} (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ j g g' d p jb gb gb',
      (DEMk k) M d ∧ d.dout = some p ∧ restrictI j g d = some g' ∧
      restrictI jb gb ⟨g'.fact, some j⟩ = some gb' ∧ d'' = ⟨gb'.fact, some jb⟩ ∧
      (∀ l, jb.coversLoc l → g'.fact.coversLoc l) ∧
      ((∀ l, g'.fact.coversLoc l → p.coversLoc l) ∨
        (g.fact.kind = .any ∧ (∃ E, p.kind = .star E) ∧
          g'.fact = ⟨g.fact.base, p.path, .any, g.fact.mark⟩ ∧ g'.demand = g.demand)) ∧
      ((∀ l, gb'.fact.coversLoc l → j.coversLoc l) ∨ RExc gb j gb') ∧
      (∀ l, j.coversLoc l → d.din.coversLoc l) := by
  rcases narrowing_canon_back (k + 1) h with h1 | h2 | ⟨jb, gb, gb', dB, pB, _, _, _, _, hdB, hdo,
    hres, hd'', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, g, g', d, p, _, hdem, hdop, hresF, hdB', hinF, hconF⟩ := narrowing_canon_fwd k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    refine Or.inr (Or.inr ⟨pB, g, g', d, p, jb, gb, gb', hdem, hdop, hresF, hres, hd'',
      fun l hl => insideLoc_coversLoc hin hl, ?_, ?_, fun l hl => insideLoc_coversLoc hinF hl⟩)
    · rcases hconF with hc | hc
      · exact Or.inl (fun l hl => insideLoc_coversLoc hc hl)
      · exact Or.inr hc
    · rcases hcon with hc | hc
      · exact Or.inl (fun l hl => insideLoc_coversLoc hc hl)
      · exact Or.inr hc

#print axioms narrowing_canon

/-- The composed form: a non-zero demand edge of forward run `k + 2` whose two restrictions met no
    exception cell lies inside a demand edge of forward run `k + 1`: its entry locations are entry
    locations of that edge, and its exit locations are exit locations of that edge. -/
theorem narrowing_canon_loc (k : Nat) {M : MethodId} {d'' : DemandEdge}
    (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ jb gb' d p, (DEMk k) M d ∧ d.dout = some p ∧ d'' = ⟨gb'.fact, some jb⟩ ∧
      ((∀ l, jb.coversLoc l → p.coversLoc l) ∨ ∃ g g', RExc g p g') ∧
      ((∀ l, gb'.fact.coversLoc l → d.din.coversLoc l) ∨ ∃ gb j, RExc gb j gb') := by
  rcases narrowing_canon k h with h1 | h2 | ⟨j, g, g', d, p, jb, gb, gb', hdem, hdop, _, _, hd'',
    hjb, hF, hB, hj⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨jb, gb', d, p, hdem, hdop, hd'', ?_, ?_⟩)
    · rcases hF with hc | hc
      · exact Or.inl (fun l hl => hc l (hjb l hl))
      · exact Or.inr ⟨g, g', Or.inl hc⟩
    · rcases hB with hc | hc
      · exact Or.inl (fun l hl => hj l (hc l hl))
      · exact Or.inr ⟨gb, j, hc⟩

#print axioms narrowing_canon_loc

end Canon

/-! ## Part 2b. The inclusion form: the driver may hand off more -/

/-- A run sequence with given demands and records: run 0 is `D … policy1 …`, run `k + 1` is
    `DR … (dem k) emitM satI restrictI (rc (k + 1)) …`. -/
def runSeqN (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (rc : Nat → Recs)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Obj → Prop
  | 0 => D P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR P counted (Ls (k + 1)) (dem k) emitM satI restrictI (rc (k + 1)) sinks roots

/-- The publications of `runSeqN`. -/
def pubSeqN (dem : Nat → MethodId → DemandEdge → Prop) : Nat → Pub
  | 0 => pubD
  | k + 1 => pubR (dem k)

theorem pubSeqN_sub (dem : Nat → MethodId → DemandEdge → Prop) (k : Nat) :
    ∀ m j g g', pubSeqN dem k m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 := by
  cases k with
  | zero => exact pubD_sub
  | succ k => exact pubR_sub (dem k)

#print axioms pubSeqN_sub

/-- A larger demand keeps a demanded-or-recorded flow. -/
theorem flowRR_mono {P : Program} {d1 d2 : MethodId → DemandEdge → Prop} {rc : Recs}
    (h : ∀ m e, d1 m e → d2 m e) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowRR P d1 rc M l0 n l) : FlowRR P d2 rc M l0 n l := by
  induction hf with
  | start M l0 => exact FlowRR.start M l0
  | step _ he hs ih => exact FlowRR.step ih he hs
  | pass _ he hm ih => exact FlowRR.pass ih he hm
  | call _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    exact FlowRR.call ih he he1 hd1 ihc (h _ _ hdem) hdin hdout hp he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRR.rcall ih he he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRR.clean ih he hcl
  | filt _ he hl ih => exact FlowRR.filt ih he hl

/-- A larger demand keeps a demanded-or-recorded vulnerability witness. -/
theorem reachRR_mono {P : Program} {roots : List MethodId} {d1 d2 : MethodId → DemandEdge → Prop}
    {rc : Recs} (h : ∀ m e, d1 m e → d2 m e) {M : MethodId} {n : Node} {l : Loc}
    (hr : ReachRR P d1 rc roots M n l) : ReachRR P d2 rc roots M n l := by
  induction hr with
  | root hM hfl => exact ReachRR.root hM (flowRR_mono h hfl)
  | down _ he he1 hd1 hdem hdin hfc ih =>
    exact ReachRR.down ih he he1 hd1 (h _ _ hdem) hdin (flowRR_mono h hfc)

/-- More records keep a justified flow. -/
theorem flowRDN_mono_rc {P : Program} {R : Obj → Prop} {pub : Pub} {rc1 rc2 : Recs}
    (h : ∀ m x, rc1 m x → rc2 m x) {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (hf : FlowRDN P R pub rc1 M l0 n l) : FlowRDN P R pub rc2 M l0 n l := by
  induction hf with
  | start M l0 => exact FlowRDN.start M l0
  | step _ he hs ih => exact FlowRDN.step ih he hs
  | pass _ he hm ih => exact FlowRDN.pass ih he hm
  | call _ he he1 hd1 _ hj hg hpub hjc hdg he2 hd2 ih ihc =>
    exact FlowRDN.call ih he he1 hd1 ihc hj hg hpub hjc hdg he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRDN.rcall ih he he1 hd1 (h _ _ hrc) hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRDN.clean ih he hcl
  | filt _ he hl ih => exact FlowRDN.filt ih he hl

/-- More records keep a justified vulnerability witness. -/
theorem reachRDN_mono_rc {P : Program} {R : Obj → Prop} {pub : Pub} {rc1 rc2 : Recs}
    {roots : List MethodId} (h : ∀ m x, rc1 m x → rc2 m x) {M : MethodId} {n : Node} {l : Loc}
    (hr : ReachRDN P R pub rc1 roots M n l) : ReachRDN P R pub rc2 roots M n l := by
  induction hr with
  | root hM hfl => exact ReachRDN.root hM (flowRDN_mono_rc h hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachRDN.down ih he he1 hd1 hj hjc (flowRDN_mono_rc h hfc)

#print axioms flowRR_mono
#print axioms reachRR_mono
#print axioms flowRDN_mono_rc
#print axioms reachRDN_mono_rc

/-- THE GENERAL ITERATION THEOREM, INCLUSION FORM. The driver may hand off MORE than the canonical
    sets: the backward demand `demB k` contains `handF` of run `k`, the backward records `recsB k`
    contain the reversed crossable records of run `k`, the demand `dem k` of run `k + 1` contains
    the hand-off `demOfN` of the backward run, and the records `rc (k + 1)` of run `k + 1` contain
    `rcNextOf` (`NextRecs`). Then every real vulnerability is, at every forward run `k`, reported
    by run `k` or confirmed by an earlier run. -/
theorem iteration_generalN_incl {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls LB : Nat → Nat}
    {dem demB : Nat → MethodId → DemandEdge → Prop} {rc recsB : Nat → Recs}
    {seeds : Nat → List (MethodId × Node × PFact)} {C : Nat → MethodId → Node → PFact → Prop}
    (hdemB : ∀ k m d, handF P (runSeqN P counted Ls dem rc sinks roots k) (pubSeqN dem k) m d →
      demB k m d)
    (hrecB : ∀ k m x, (rc k m x ∨ (runSeqN P counted Ls dem rc sinks roots k (.init m x.1) ∧
        runSeqN P counted Ls dem rc sinks roots k (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB k m (revRec x))
    (hdem : ∀ k m d, demOfN (Program.rev P)
        (DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k) [] roots
          (seeds k) true) (pubR (demB k)) m d → dem k m d)
    (hrc : ∀ k, NextRecs P (runSeqN P counted Ls dem rc sinks roots k) (rc k)
      (DB (Program.rev P) counted (LB k) (demB k) emitM satI restrictI (recsB k) [] roots
        (seeds k) true) (rc (k + 1)))
    (hseeds : ∀ k M n s b, runSeqN P counted Ls dem rc sinks roots k (.vuln M n s b) →
      C k M n s ∨ (M, n, s) ∈ seeds k)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, (∃ k', k' < k ∧ C k' M n s) ∨ ∃ b, runSeqN P counted Ls dem rc sinks roots k
      (.vuln M n s b) := by
  refine iteration_abstract_or (R := runSeqN P counted Ls dem rc sinks roots)
    (pub := pubSeqN dem) (rc := rc) (dem := dem) (seeds := seeds) ?_ ?_ ?_ hseeds hRe hs hT' hsc
  · intro M' n' l' s' T' hs' hT'' hc' hRe'
    obtain ⟨hR, hv⟩ := run1_justifies P counted (Ls 0) sinks roots hW M' n' l' s' T' hs' hT'' hc'
      hRe'
    exact ⟨reachRDN_mono_rc (fun _ _ h => h.elim) hR, hv⟩
  · intro k
    exact coversN_DR P counted (Ls (k + 1)) (dem k) (rc (k + 1)) sinks roots hW
  · intro k M' n' l' s' T' hs' hT'' hc' hRR hsd
    exact reachRR_mono (hdem k)
      (B_generalN (counted := counted) (L := LB k) (sinksB := []) hW hT hmr hNZB hZ hX hk
        (hdemB k) (hrecB k) (pubSeqN_sub dem k) (hrc k) M' n' l' s' T' hs' hT'' hc' hRR hsd)

#print axioms iteration_generalN_incl

end ApSpec.HandoffMain
