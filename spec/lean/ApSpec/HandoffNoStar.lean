/-
  ApSpec.HandoffNoStar — the demand patterns of the hand-off of the DEMAND EDGES only (decision F70)
  have no `*` tail, so the narrowing is EXACT (design review item DES-4).

  With the new hand-off the exception (a) of the narrowing (an `[any]` conclusion at or above a
  `*/E` exit pattern, `E ≠ {}`) does not occur. The steps (base model first):
    1. RUN 1 (`D … policy1 …`). Every premise has the tail `$` or `*` with the Empty exclusion
       (`D_premK`: the zero fact, the policy premise, and the answers keep the tail). A `*`
       conclusion of run 1 is normal and has an abstract mark (W2, `Invariant.final_star_legal`:
       a demand-layer `*` conclusion is normalized to `[any]` or `$`, so it does not survive). So an
       exit edge with a `*` conclusion is crossable (`run1_exit_star_cross`), and the hand-off of
       run 1 has no `*` entry pattern `D-c` (`handF_run1_nonstar`); its exit patterns `D-p` (the
       premises of run 1) have the tail `$` or `*/{}`.
    2. THE BACKWARD RUN (`DB … emitM …`, concrete seeds). If the backward demand has no `*` entry
       pattern, no premise has a `*` tail (`DB_init_nonstar`). If the seeds have no `*` tail, no
       conclusion has a `*` tail (`DB_edge_nonstar`, from W2 and the concrete marks). So the
       hand-off `demOfN` has no `*` pattern at all (`demOfN_nonstar`).
    3. THE CANONICAL SEQUENCE (`HandoffMain.canonState`), seeds with concrete marks and no `*`
       tail: every demand pattern of every forward run `k + 1` has no `*` tail
       (`canon_dem_nonstar`), and every hand-off of a forward run has no `*` entry pattern
       (`canon_handF_nonstar`; its exit patterns have no `*` tail, except the `*/{}` premises of
       run 1). So:
       * THE FORWARD NARROWING IS EXACT at every forward run `k + 1` (spec run 3 on):
         `narrowing_canon_fwd_exact` (`Handoff.handF_narrow_DR_exact` applies);
       * THE BACKWARD NARROWING IS EXACT after every restricted forward run (`RExc` does not occur):
         `narrowing_canon_back_exact`; after run 1 the only cell is (a) with `D-p = */{}`, which
         adds no location (`narrowing_canon_back_loc`, for every `k`);
       * THE NARROWING OVER ONE ROUND IS EXACT: every demand edge of forward run `k + 2` with a
         non-zero premise lies inside a demand edge of forward run `k + 1` (entry locations and
         exit locations), with no exception: `narrowing_canon_loc_exact`.
    4. THE SAME ON THE X SEQUENCE (`HandoffXIter.canonStateX`): `handF_run1X_nonstar` (run 1
       `D6X`, W2 from `AnyTaintExKinds.D6X_legal_all`), `DRX_init_nonstar`, `handF_DRX_nonstar`,
       `canonX_dem_nonstar`; the forward narrowing of the X runs has no exception and the piece lies
       inside `D-p` ALSO WITHOUT ITS EXCLUSION (`narrowing_canonX_fwd_exact`); the backward
       narrowing as in the base (`narrowing_canonX_back_loc`); the composed form
       (`narrowing_canonX_loc_exact`): the exit side is exact; the entry side is exact, except when
       the premise exclusion `jex` is Universe (with no `*` tail, `insideLocXB` and `insideLocB`
       differ only there, `insideLocXB_nonstar`), and then only at a location that the dropped
       exclusion excludes (`HandoffXMain.Dropped`).
    5. CEGAR (`NSVec`): the cell with the exclusion Universe is real in the operations (a binding
       gives `[any-taint]/Universe`, `emitX` gives the premise `[any]/Universe`, which lies inside a
       `$` entry pattern only with its exclusion), and there the composed step has an entry
       location outside `D-c` (`entry_univ`, `entry_univ_loc`; vectors of the operations, not a
       program run).
  The zero demand and the seed-path patterns `(g, none)` are not narrowed (decision F70 item 5).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffMain
import ApSpec.HandoffXMain
import ApSpec.AnyTaintExKinds

namespace ApSpec.HandoffNoStar
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff ApSpec.HandoffBackward ApSpec.HandoffIter

/-! ## 1. Run 1: the premises, and the crossable `*` exit edges -/

/-- A premise tail of run 1: `$`, or `*` with the Empty exclusion. -/
def Run1K (k : Kind) : Prop := k = .exact ∨ k = .star Excl.empty

theorem run1K_crossK {k : Kind} (h : Run1K k) : CrossK k := by
  rcases h with h | h
  · rw [h]; trivial
  · rw [h]; rfl

/-- The premise motive of run 1: the premise of an initial fact, an edge and a request. -/
def PremK : Obj → Prop
  | .init _ i => Run1K i.kind
  | .edge _ i _ _ => Run1K i.kind
  | .req _ i _ => Run1K i.kind
  | _ => True

/-- An answer keeps the tail of the requesting premise, or gives `$`. -/
theorem answerInit_kind (i a : PFact) (t : Mark) :
    (answerInit i a t).kind = .exact ∨ (answerInit i a t).kind = i.kind := by
  unfold answerInit
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The policy of run 1 gives the zero fact or the policy premise `*/{}`. -/
theorem policy1_run1K (m : MethodId) (a : PFact) : Run1K (policy1 m a).kind := by
  unfold policy1 policy
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inr rfl

#print axioms run1K_crossK
#print axioms answerInit_kind
#print axioms policy1_run1K

section Run1
variable {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- THE PREMISES OF RUN 1. If the abstraction gives the tail `$` or `*/{}`, every premise of
    `D` has the tail `$` or `*/{}` (the zero fact, the abstraction, the answers). -/
theorem D_premK (hα : ∀ m a, Run1K (α m a).kind) {o : Obj}
    (h : D P counted L α sinks roots o) : PremK o := by
  induction h with
  | root => exact Or.inl rfl
  | start _ ih => exact ih
  | step _ _ _ ih => exact ih
  | reqStmt _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => exact hα _ _
  | ret _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | reqSink _ _ _ ih => exact ih
  | @answer M i t a _ _ _ _ ihR _ =>
    rcases answerInit_kind i a t with h | h
    · exact Or.inl h
    · show Run1K (answerInit i a t).kind
      rw [h]
      exact ihR
  | reqUp _ _ _ _ _ _ _ _ _ ihE => exact ihE
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih

#print axioms D_premK

end Run1

/-- The reversal of an edge with a `*` conclusion and a premise tail `$` or `*/{}` has a
    crossable premise. -/
theorem crossK_rev_star {j f : PFact} {E : Excl} (hj : Run1K j.kind) (hk : f.kind = .star E) :
    CrossK (revEdge j f).1.kind := by
  show CrossK (revKinds j.kind f.kind).1
  rw [hk]
  rcases hj with h | h
  · rw [h]; trivial
  · rw [h]; rfl

#print axioms crossK_rev_star

/-- A `*` EXIT EDGE OF RUN 1 IS CROSSABLE. Every exit edge of `D … policy1 …` with a `*`
    conclusion is normal, has an abstract conclusion mark (W2), and its premise has the tail `$` or
    `*/{}`: so `Cross`. -/
theorem run1_exit_star_cross {P : Program} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {M : MethodId}
    {j : PFact} {n : Node} {g : AFact} {E : Excl}
    (hj : D P counted L policy1 sinks roots (.init M j))
    (hg : D P counted L policy1 sinks roots (.edge M j n g)) (hk : g.fact.kind = .star E) :
    Cross j g := by
  have hpj : Run1K j.kind := D_premK policy1_run1K hj
  obtain ⟨habs, hdem⟩ := Invariant.final_star_legal P counted L policy1 sinks roots hg hk
  exact ⟨hdem, run1K_crossK hpj, Or.inl habs, crossK_rev_star hpj hk⟩

#print axioms run1_exit_star_cross

/-- THE HAND-OFF OF RUN 1 HAS NO `*` ENTRY PATTERN. Every demand edge `handF` gives for run 1 (the
    publication `pubD`) has an entry pattern `D-c` with no `*` tail; its exit pattern `D-p` (a
    premise of run 1) has the tail `$` or `*/{}`. -/
theorem handF_run1_nonstar {P : Program} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {m : MethodId}
    {d : DemandEdge} (h : handF P (D P counted L policy1 sinks roots) pubD m d) :
    NoStarK d.din.kind ∧ ∀ p, d.dout = some p → Run1K p.kind := by
  obtain ⟨j, g, g', hj, hg, hnc, hpub, rfl⟩ := h
  have hg' : g' = g := hpub
  subst hg'
  refine ⟨fun E hE => hnc (run1_exit_star_cross hj hg hE), fun p hp => ?_⟩
  have hjp : j = p := Option.some.inj hp
  subst hjp
  exact D_premK policy1_run1K hj

#print axioms handF_run1_nonstar

/-! ## 2. The backward run -/

section Back
variable {Pb : Program} {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
  {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

local notation "DBr" => DB Pb counted L demB emitM sat restrict recsB sinksB rootsB seeds zbind

/-- An added fact of the backward run has no `*` tail (it is concrete, and W2 gives a `*` tail
    only to an abstract mark). -/
theorem DB_added_nonstar (hsd : BExact.SeedsConc seeds) {m : MethodId} {a : PFact}
    (h : DBr (.added m a)) : NoStarK a.kind := by
  obtain ⟨t, ht⟩ := BExact.DB_added_concrete RCov.emitM_copies hsd m a h
  cases h with
  | added _ _ _ hx =>
    intro E hE
    exact Invariant.AbsMark.not_conc ((Invariant.applyEdge_Legal hx) E hE).1 t ht

#print axioms DB_added_nonstar

/-- THE BACKWARD PREMISES HAVE NO `*` TAIL if the backward demand has no `*` entry pattern (the
    zero fact, the emission `emitM`, no answer: the run has no request). -/
theorem DB_init_nonstar (hsd : BExact.SeedsConc seeds)
    (hdin : ∀ m d, demB m d → NoStarK d.din.kind) {M : MethodId} {i : PFact}
    (h : DBr (.init M i)) : NoStarK i.kind := by
  cases h with
  | root _ => intro E hE; cases hE
  | initR ha hd he => exact emitM_nonstar he (hdin _ _ hd) (DB_added_nonstar hsd ha)
  | answer hq _ _ _ => exact absurd hq (BExact.DB_no_request RCov.emitM_copies hsd _ _ _)
  | zin _ _ _ => intro E hE; cases hE

#print axioms DB_init_nonstar

/-- The W2 motive on the edges. -/
def LegalE : Obj → Prop
  | .edge _ _ _ f => Invariant.Legal f
  | _ => True

/-- W2 ON THE BACKWARD RUN, for seeds with no `*` tail. -/
theorem DB_legal (hsk : ∀ M n s, (M, n, s) ∈ seeds → NoStarK s.kind) {o : Obj} (h : DBr o) :
    LegalE o := by
  induction h with
  | root => trivial
  | start _ _ => exact fun _ hk => Invariant.startFact_legal hk
  | step _ _ hf ih =>
    rcases Invariant.transfer_mem hf with h1 | ⟨x, e, _, hx, h2⟩
    · rw [h1]; exact ih
    · rw [h2]; exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hx)
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')
  | retRec _ _ _ _ _ _ _ _ hr' _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ hf ih => exact Invariant.cleanRes_Legal ih hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | zpass => intro e hk; cases hk
  | zin => trivial
  | seed hs _ _ =>
    exact Invariant.limitF_Legal (fun e hk => absurd hk (hsk _ _ _ hs e))
  | zret _ _ _ _ _ _ hr' _ _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')

#print axioms DB_legal

/-- THE BACKWARD CONCLUSIONS HAVE NO `*` TAIL, for concrete seeds with no `*` tail. -/
theorem DB_edge_nonstar (hsd : BExact.SeedsConc seeds)
    (hsk : ∀ M n s, (M, n, s) ∈ seeds → NoStarK s.kind) {M : MethodId} {i : PFact} {n : Node}
    {f : AFact} (h : DBr (.edge M i n f)) : NoStarK f.fact.kind := by
  intro E hE
  obtain ⟨_, t, ht⟩ := BExact.DB_edge_concrete RCov.emitM_copies hsd h
  exact Invariant.AbsMark.not_conc ((DB_legal hsk h) E hE).1 t ht

#print axioms DB_edge_nonstar

/-- THE BACKWARD HAND-OFF HAS NO `*` PATTERN: with concrete seeds with no `*` tail and a backward
    demand with no `*` entry pattern, every demand edge that `demOfN` gives (the publication
    `pubR demB`) has no `*` entry pattern and no `*` exit pattern. -/
theorem demOfN_nonstar (hsd : BExact.SeedsConc seeds)
    (hsk : ∀ M n s, (M, n, s) ∈ seeds → NoStarK s.kind)
    (hdin : ∀ m d, demB m d → NoStarK d.din.kind) {M : MethodId} {d : DemandEdge}
    (h : demOfN Pb DBr (pubR demB) M d) :
    NoStarK d.din.kind ∧ ∀ p, d.dout = some p → NoStarK p.kind := by
  rcases h with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, _, hgb, _, ⟨d0, _, hres⟩, rfl⟩
  · exact ⟨fun E hE => (by cases hE), fun p hp => (by cases hp)⟩
  · exact ⟨DB_edge_nonstar hsd hsk hg, fun p hp => (by cases hp)⟩
  · obtain ⟨p0, _, _, hc⟩ := restrictI_some hres
    refine ⟨restrictConcI_nonstar hc (DB_edge_nonstar hsd hsk hgb), fun p hp => ?_⟩
    have hjp : jb = p := Option.some.inj hp
    rw [← hjp]
    exact DB_init_nonstar hsd hdin hjb

#print axioms demOfN_nonstar

end Back

/-! ## 3. The canonical sequence -/

/-- A seed with the tail `$` or `[any]` (the sink patterns of the iteration theorems) has no `*`
    tail. -/
theorem nonstar_of_sinkK {s : PFact} (h : s.kind = .exact ∨ s.kind = .any) : NoStarK s.kind := by
  intro E hE
  rcases h with h | h
  · rw [h] at hE; cases hE
  · rw [h] at hE; cases hE

#print axioms nonstar_of_sinkK

/-- A pattern tail with no `*`, or `*` with the Empty exclusion (the exit patterns of the hand-off
    of run 1). -/
def NoStarOrEmpty (k : Kind) : Prop := NoStarK k ∨ k = .star Excl.empty

/-- The cell (a) of `RExc` at an exit pattern `*/{}` adds no location: the result lies inside the
    exit pattern. -/
theorem rexc_empty_loc {gb gb' : AFact} {p : PFact} (hc : restrictConcI gb p = some gb')
    (hr : RExc gb p gb') (hp : NoStarOrEmpty p.kind) (hns : NoStarK gb.fact.kind) :
    ∀ l, gb'.fact.coversLoc l → p.coversLoc l := by
  intro l hl
  have hb : gb.fact.base = p.base := (restrictConcI_cases hc).1
  rcases hr with ⟨_, ⟨E, hE⟩, hf, _⟩ | ⟨⟨e, he⟩, _⟩
  · rcases hp with hp | hp
    · exact absurd hE (hp E)
    · obtain ⟨hlb, σ, hlp, _⟩ := hl
      rw [hf] at hlb hlp
      refine ⟨hlb.trans hb, σ, hlp, ?_⟩
      show tailI p.kind σ
      rw [hp]
      show Excl.empty.admits σ = true
      cases σ <;> rfl
  · exact absurd he (hns e)

#print axioms rexc_empty_loc

section Canon
variable {P : Program} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

open ApSpec.HandoffMain

local notation "CS" => canonState P counted Ls LB sinks roots seeds
local notation "DBk" k => backOf P counted (LB k) roots (seeds k) (CS k)
local notation "DEMk" k => demOf P counted (LB k) roots (seeds k) (CS k)

/-- THE DEMAND PATTERNS OF THE CANONICAL SEQUENCE HAVE NO `*` TAIL. With concrete seeds with no
    `*` tail, every demand edge of every forward run `k + 1` has no `*` entry pattern and no `*`
    exit pattern. -/
theorem canon_dem_nonstar (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) :
    ∀ k m d, (DEMk k) m d → NoStarK d.din.kind ∧ ∀ p, d.dout = some p → NoStarK p.kind := by
  intro k
  induction k with
  | zero =>
    intro m d h
    exact demOfN_nonstar (hsd 0) (hsk 0)
      (fun m' d' hd => (handF_run1_nonstar (P := P) (counted := counted) (L := Ls 0)
        (sinks := sinks) (roots := roots) hd).1) h
  | succ k ih =>
    intro m d h
    exact demOfN_nonstar (hsd (k + 1)) (hsk (k + 1))
      (fun m' d' hd => (handF_DR_nonstar (P := P) (counted := counted) (L := Ls (k + 1))
        (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
        (sinks := sinks) (roots := roots) (fun m1 d1 h1 => (ih m1 d1 h1).1) hd).1) h

#print axioms canon_dem_nonstar

/-- THE HAND-OFFS OF THE CANONICAL SEQUENCE HAVE NO `*` ENTRY PATTERN; their exit patterns have
    no `*` tail, or (only after run 1) the tail `*/{}`. -/
theorem canon_handF_nonstar (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {m : MethodId}
    {d : DemandEdge} (h : handF P (CS k).R (CS k).pub m d) :
    NoStarK d.din.kind ∧ ∀ p, d.dout = some p → NoStarOrEmpty p.kind := by
  cases k with
  | zero =>
    obtain ⟨h1, h2⟩ := handF_run1_nonstar (P := P) (counted := counted) (L := Ls 0)
      (sinks := sinks) (roots := roots) h
    refine ⟨h1, fun p hp => ?_⟩
    rcases h2 p hp with he | he
    · exact Or.inl (fun E hE => by rw [he] at hE; cases hE)
    · exact Or.inr he
  | succ k =>
    obtain ⟨h1, h2⟩ := handF_DR_nonstar (P := P) (counted := counted) (L := Ls (k + 1))
      (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
      (sinks := sinks) (roots := roots)
      (fun m1 d1 h1 => (canon_dem_nonstar hsd hsk k m1 d1 h1).1) h
    exact ⟨h1, fun p hp => Or.inl (h2 p hp)⟩

#print axioms canon_handF_nonstar

/-- THE FORWARD NARROWING IS EXACT ON THE CANONICAL SEQUENCE (every forward run `k + 1`: spec run
    3 on). Every demand edge `d'` that forward run `k + 1` hands off lies inside the reversal of a
    demand edge `d` of its demand, with NO exception: its exit pattern `j` lies inside `D-c` of
    `d`, and its entry pattern `g'` lies inside `D-p` of `d`. -/
theorem narrowing_canon_fwd_exact (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {m : MethodId}
    {d' : DemandEdge} (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ (j : PFact) (g' : AFact) (d : DemandEdge) (p : PFact), (DEMk k) m d ∧ d.dout = some p ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideLocB j d.din = true ∧ insideLocB g'.fact p = true :=
  handF_narrow_DR_exact (P := P) (counted := counted) (L := Ls (k + 1)) (demand := DEMk k)
    (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
    (sinks := sinks) (roots := roots)
    (fun m1 d1 p1 h1 hp1 => (canon_dem_nonstar hsd hsk k m1 d1 h1).2 p1 hp1) h

#print axioms narrowing_canon_fwd_exact

/-- THE BACKWARD NARROWING IS EXACT AFTER EVERY RESTRICTED FORWARD RUN: every non-zero demand edge
    of forward run `k + 2` lies inside the reversal of the backward demand edge (a hand-off of
    forward run `k + 1`) that published it, with NO exception (`RExc` does not occur: the exit
    patterns have no `*` tail and the backward conclusions have no `*` tail). -/
theorem narrowing_canon_back_exact (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d' : DemandEdge} (h : (DEMk (k + 1)) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, (DBk (k + 1)) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk (k + 1)) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      handF P (CS (k + 1)).R (CS (k + 1)).pub M d ∧ d.dout = some p ∧
      restrictI jb gb d = some gb' ∧ d' = ⟨gb'.fact, some jb⟩ ∧ insideLocB jb d.din = true ∧
      insideLocB gb'.fact p = true := by
  rcases narrowing_canon_back (k + 1) h with h1 | h2 | ⟨jb, gb, gb', d, p, hjb, hne, hgb, hncb,
    hdB, hdo, hres, hd', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨jb, gb, gb', d, p, hjb, hne, hgb, hncb, hdB, hdo, hres, hd', hin, ?_⟩)
    rcases hcon with hc | ⟨_, ⟨E, hE⟩, _, _⟩ | ⟨⟨e, he⟩, _⟩
    · exact hc
    · rcases (canon_handF_nonstar hsd hsk (k + 1) hdB).2 p hdo with hp | hp
      · exact absurd hE (hp E)
      · -- after a restricted run the exit pattern is not `*/{}`
        obtain ⟨_, h2'⟩ := handF_DR_nonstar (P := P) (counted := counted) (L := Ls (k + 1))
          (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
          (sinks := sinks) (roots := roots)
          (fun m1 d1 h1 => (canon_dem_nonstar hsd hsk k m1 d1 h1).1) hdB
        exact absurd hE (h2' p hdo E)
    · exact absurd he (DB_edge_nonstar (hsd (k + 1)) (hsk (k + 1)) hgb e)

#print axioms narrowing_canon_back_exact

/-- THE BACKWARD NARROWING IN LOCATION FORM, FOR EVERY BACKWARD RUN (also after run 1): every
    non-zero demand edge of forward run `k + 1` lies inside the reversal of the backward demand
    edge that published it (its exit locations are entry locations of that edge, its entry
    locations are exit locations of that edge). After run 1 the cell (a) of `RExc` can occur, but
    only at an exit pattern `*/{}`, where it adds no location. -/
theorem narrowing_canon_back_loc (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d' : DemandEdge} (h : (DEMk k) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk k) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ (jb : PFact) (gb' : AFact) (d : DemandEdge) (p : PFact),
      handF P (CS k).R (CS k).pub M d ∧ d.dout = some p ∧
      d' = ⟨gb'.fact, some jb⟩ ∧ (∀ l, jb.coversLoc l → d.din.coversLoc l) ∧
      (∀ l, gb'.fact.coversLoc l → p.coversLoc l) := by
  rcases narrowing_canon_back k h with h1 | h2 | ⟨jb, gb, gb', d, p, _, _, hgb, _,
    hdB, hdo, hres, hd', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨jb, gb', d, p, hdB, hdo, hd', fun l hl => insideLoc_coversLoc hin hl,
      ?_⟩)
    rcases hcon with hc | hc
    · exact fun l hl => insideLoc_coversLoc hc hl
    · obtain ⟨p0, hdo0, _, hc0⟩ := restrictI_some hres
      have hp0 : p0 = p := Option.some.inj (hdo0.symm.trans hdo)
      subst hp0
      exact rexc_empty_loc hc0 hc ((canon_handF_nonstar hsd hsk k hdB).2 p0 hdo)
        (DB_edge_nonstar (hsd k) (hsk k) hgb)

#print axioms narrowing_canon_back_loc

/-- THE NARROWING OVER ONE ROUND IS EXACT ON THE CANONICAL SEQUENCE (the user's rule with no
    exception). With concrete seeds with no `*` tail, every demand edge `d''` of forward run `k + 2`
    is the zero demand, a zero-premise backward edge (a seed path; not narrowed), or lies inside a
    demand edge `d` of forward run `k + 1` of the same method: every exit location of `d''` is an
    exit location of `d`, and every entry location of `d''` is an entry location of `d`. -/
theorem narrowing_canon_loc_exact (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d'' : DemandEdge} (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ (jb : PFact) (gb' : AFact) (d : DemandEdge) (p : PFact), (DEMk k) M d ∧ d.dout = some p ∧
      d'' = ⟨gb'.fact, some jb⟩ ∧ (∀ l, jb.coversLoc l → p.coversLoc l) ∧
      (∀ l, gb'.fact.coversLoc l → d.din.coversLoc l) := by
  rcases narrowing_canon_back_exact hsd hsk k h with h1 | h2 | ⟨jb, gb, gb', dB, pB, _, _, _, _,
    hdB, hdo, _, hd'', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, g', d, p, hdem, hdop, hdB', hinF, hconF⟩ := narrowing_canon_fwd_exact hsd hsk k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    exact Or.inr (Or.inr ⟨jb, gb', d, p, hdem, hdop, hd'',
      fun l hl => insideLoc_coversLoc hconF (insideLoc_coversLoc hin hl),
      fun l hl => insideLoc_coversLoc hinF (insideLoc_coversLoc hcon hl)⟩)

#print axioms narrowing_canon_loc_exact

/-! ### The exact narrowing with the marks (F71, the mark-aware restriction) -/

/-- THE FORWARD NARROWING IS EXACT, MARK-AWARE: as `narrowing_canon_fwd_exact`, in the locations
    AND the marks (`insideB`). -/
theorem narrowing_canon_fwd_exactM (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {m : MethodId}
    {d' : DemandEdge} (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ (j : PFact) (g' : AFact) (d : DemandEdge) (p : PFact), (DEMk k) m d ∧ d.dout = some p ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideB j d.din = true ∧ insideB g'.fact p = true :=
  handF_narrow_DR_exactM (P := P) (counted := counted) (L := Ls (k + 1)) (demand := DEMk k)
    (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
    (sinks := sinks) (roots := roots)
    (fun m1 d1 p1 h1 hp1 => (canon_dem_nonstar hsd hsk k m1 d1 h1).2 p1 hp1) h

#print axioms narrowing_canon_fwd_exactM

/-- THE BACKWARD NARROWING IS EXACT, MARK-AWARE: as `narrowing_canon_back_exact`, in the locations
    AND the marks (`insideB`; the backward run is concrete, `BExact.DB_edge_concrete`). -/
theorem narrowing_canon_back_exactM (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d' : DemandEdge} (h : (DEMk (k + 1)) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, (DBk (k + 1)) (.init M jb) ∧ jb ≠ zeroFact ∧
      (DBk (k + 1)) (.edge M jb ((Program.rev P).exit M) gb) ∧ ¬ CrossB jb gb ∧
      handF P (CS (k + 1)).R (CS (k + 1)).pub M d ∧ d.dout = some p ∧
      restrictI jb gb d = some gb' ∧ d' = ⟨gb'.fact, some jb⟩ ∧ insideB jb d.din = true ∧
      insideB gb'.fact p = true := by
  rcases narrowing_canon_backM (k + 1) (hsd (k + 1)) h with h1 | h2 | ⟨jb, gb, gb', d, p, hjb, hne,
    hgb, hncb, hdB, hdo, hres, hd', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨jb, gb, gb', d, p, hjb, hne, hgb, hncb, hdB, hdo, hres, hd', hin, ?_⟩)
    rcases hcon with hc | ⟨⟨_, ⟨E, hE⟩, _, _⟩ | ⟨⟨e, he⟩, _⟩, _⟩
    · exact hc
    · rcases (canon_handF_nonstar hsd hsk (k + 1) hdB).2 p hdo with hp | hp
      · exact absurd hE (hp E)
      · -- after a restricted run the exit pattern is not `*/{}`
        obtain ⟨_, h2'⟩ := handF_DR_nonstar (P := P) (counted := counted) (L := Ls (k + 1))
          (dem := DEMk k) (sat := satI) (restrict := restrictI) (recs := (CS (k + 1)).rc)
          (sinks := sinks) (roots := roots)
          (fun m1 d1 h1 => (canon_dem_nonstar hsd hsk k m1 d1 h1).1) hdB
        exact absurd hE (h2' p hdo E)
    · exact absurd he (DB_edge_nonstar (hsd (k + 1)) (hsk (k + 1)) hgb e)

#print axioms narrowing_canon_back_exactM

/-- THE NARROWING OVER ONE ROUND IS EXACT, MARK-AWARE (the user's rule with no exception, in the
    locations AND the marks). With concrete seeds with no `*` tail, every demand edge `d''` of
    forward run `k + 2` is the zero demand, a zero-premise backward edge (a seed path; not
    narrowed), or lies inside a demand edge `d` of forward run `k + 1` of the same method: every
    exit location of `d''` with its mark is an exit location of `d` with its mark, and every entry
    location of `d''` with its mark is an entry location of `d` with its mark. -/
theorem narrowing_canon_loc_exactM (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d'' : DemandEdge} (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ (jb : PFact) (gb' : AFact) (d : DemandEdge) (p : PFact), (DEMk k) M d ∧ d.dout = some p ∧
      d'' = ⟨gb'.fact, some jb⟩ ∧ (∀ l, jb.covers l → p.covers l) ∧
      (∀ l, gb'.fact.covers l → d.din.covers l) := by
  rcases narrowing_canon_back_exactM hsd hsk k h with h1 | h2 | ⟨jb, gb, gb', dB, pB, _, _, _, _,
    hdB, hdo, _, hd'', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, g', d, p, hdem, hdop, hdB', hinF, hconF⟩ := narrowing_canon_fwd_exactM hsd hsk k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    exact Or.inr (Or.inr ⟨jb, gb', d, p, hdem, hdop, hd'',
      fun l hl => insideB_covers hconF (insideB_covers hin hl),
      fun l hl => insideB_covers hinF (insideB_covers hcon hl)⟩)

#print axioms narrowing_canon_loc_exactM

end Canon

/-! ## 4. The X sequence (`HandoffXIter.canonStateX`) -/

section XSeq
open ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.HandoffX ApSpec.HandoffXIter ApSpec.HandoffXMain
open ApSpec.AnyTaintExCov (forgetX forget6 CovLocX)

/-- The premise motive of run 1 with the exclusion. -/
def PremK6 : XObj6 → Prop
  | .init _ i => Run1K i.kind
  | .edge _ i _ _ => Run1K i.kind
  | .req _ i _ => Run1K i.kind
  | _ => True

/-- THE PREMISES OF RUN 1 WITH THE EXCLUSION (`D6X`): as `D_premK`. -/
theorem D6X_premK {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hα : ∀ m a, Run1K (α m a).kind) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) : PremK6 o := by
  induction h with
  | root => exact Or.inl rfl
  | start _ ih => exact ih
  | step _ _ _ ih => exact ih
  | reqStmt _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => exact hα _ _
  | ret _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | reqSink _ _ _ ih => exact ih
  | @answer M i t a _ _ _ _ ihR _ =>
    rcases answerInit_kind i a t with h | h
    · exact Or.inl h
    · show Run1K (answerInit i a t).kind
      rw [h]
      exact ihR
  | reqUp _ _ _ _ _ _ _ _ _ ihE => exact ihE
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih

#print axioms D6X_premK

theorem forget6_init {R : XObj6 → Prop} {M : MethodId} {i : PFact} (h : forget6 R (.init M i)) :
    R (.init M i) := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | init M' i' => cases he; exact hx
  | edge => cases he
  | added => cases he
  | req => cases he
  | vuln => cases he

theorem forget6_edge {R : XObj6 → Prop} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : forget6 R (.edge M i n f)) : ∃ fx, R (.edge M i n fx) ∧ fx.af = f := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | edge M' i' n' fx => cases he; exact ⟨fx, hx, rfl⟩
  | init => cases he
  | added => cases he
  | req => cases he
  | vuln => cases he

#print axioms forget6_init
#print axioms forget6_edge

/-- A `*` EXIT EDGE OF RUN 1 WITH THE EXCLUSION IS CROSSABLE (on the forgotten view): W2 on `D6X`
    (`AnyTaintExKinds.D6X_legal_all`) and the premises `$` or `*/{}`. -/
theorem run1X_exit_star_cross {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {M : MethodId}
    {j : PFact} {n : Node} {g : AFact} {E : Excl}
    (hj : forget6 (D6X P taint counted L policy1 sinks roots) (.init M j))
    (hg : forget6 (D6X P taint counted L policy1 sinks roots) (.edge M j n g))
    (hk : g.fact.kind = .star E) : Cross j g := by
  have hpj : Run1K j.kind := D6X_premK policy1_run1K (forget6_init hj)
  obtain ⟨fx, hfx, rfl⟩ := forget6_edge hg
  have hl : Invariant.Legal fx.af := AnyTaintExKinds.D6X_legal_all hfx
  obtain ⟨habs, hdem⟩ := hl E hk
  exact ⟨hdem, run1K_crossK hpj, Or.inl habs, crossK_rev_star hpj hk⟩

#print axioms run1X_exit_star_cross

/-- THE HAND-OFF OF RUN 1 WITH THE EXCLUSION HAS NO `*` ENTRY PATTERN (as `handF_run1_nonstar`). -/
theorem handF_run1X_nonstar {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {m : MethodId}
    {d : DemandEdge}
    (h : handF P (forget6 (D6X P taint counted L policy1 sinks roots)) pubD m d) :
    NoStarK d.din.kind ∧ ∀ p, d.dout = some p → Run1K p.kind := by
  obtain ⟨j, g, g', hj, hg, hnc, hpub, rfl⟩ := h
  have hg' : g' = g := hpub
  subst hg'
  refine ⟨fun E hE => hnc (run1X_exit_star_cross hj hg hE), fun p hp => ?_⟩
  have hjp : j = p := Option.some.inj hp
  subst hjp
  exact D6X_premK policy1_run1K (forget6_init hj)

#print axioms handF_run1X_nonstar

/-- The emission with the must flag gives the premise of the emission. -/
theorem emitTX_emit {emit : PFact → PFact → Excl → Option (PFact × Excl)} {d a : PFact} {am : Bool}
    {aex : Excl} {j : PFact} {mj : Bool} {jex : Excl}
    (h : emitTX emit d a am aex = some (j, mj, jex)) : emit d a aex = some (j, jex) := by
  unfold emitTX at h
  cases he : emit d a aex with
  | none => rw [he] at h; cases h
  | some p =>
    obtain ⟨p1, p2⟩ := p
    rw [he] at h
    have h' : ((p1, am && p1.kind.isAny, p2) : PFact × Bool × Excl) = (j, mj, jex) :=
      Option.some.inj h
    have e1 : p1 = j := congrArg Prod.fst h'
    have e3 : p2 = jex := congrArg (fun x => x.2.2) h'
    rw [e1, e3]

#print axioms emitTX_emit

/-- A tail that is not `*` (Boolean form). -/
theorem nonstar_of_isStar {k : Kind} (h : k.isStar = false) : NoStarK k := by
  intro E hE
  rw [hE] at h
  cases h

#print axioms nonstar_of_isStar

section RunX
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {sat : PFact → Excl → PFact → Excl → Bool}
  {restrict : PFact → Excl → XFact → DemandEdge → Option XFact}
  {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- An added fact of an X run has no `*` tail (it is concrete, and its fact is a fact of the base
    binding, W2). -/
theorem DRX_added_nonstar {emit : PFact → PFact → Excl → Option (PFact × Excl)}
    (hem : EmitCopiesMarkX emit) {m : MethodId} {a : PFact} {am : Bool} {aex : Excl}
    (h : DRX P taint counted L dem emit sat restrict recs sinks roots (.added m a am aex)) :
    NoStarK a.kind := by
  obtain ⟨t, ht⟩ := AnyTaintExCov.concX_all P taint counted L dem emit sat restrict recs sinks
    roots hem h
  cases h with
  | added _ _ _ hx =>
    intro E hE
    obtain ⟨y, hy, hfy, _⟩ := bindX_base hx
    rw [hfy] at hE ht
    exact Invariant.AbsMark.not_conc ((Invariant.applyEdge_Legal hy) E hE).1 t ht

#print axioms DRX_added_nonstar

/-- THE PREMISES OF AN X RUN HAVE NO `*` TAIL if its demand has no `*` entry pattern (`emitX`
    emits by `emitM`; no answer: the run has no request). -/
theorem DRX_init_nonstar (hdin : ∀ m d, dem m d → NoStarK d.din.kind) {M : MethodId}
    {i : PFact} {mi : Bool} {iex : Excl}
    (h : DRX P taint counted L dem emitX sat restrict recs sinks roots (.init M i mi iex)) :
    NoStarK i.kind := by
  cases h with
  | root _ => intro E hE; cases hE
  | initR ha hd he =>
    exact emitM_nonstar (emitX_emitM (emitTX_emit he)) (hdin _ _ hd)
      (DRX_added_nonstar emitX_copies ha)
  | answer hq _ _ _ =>
    exact False.elim (AnyTaintExCov.concX_all P taint counted L dem emitX sat restrict recs sinks
      roots emitX_copies hq)

#print axioms DRX_init_nonstar

/-- THE HAND-OFF OF AN X RUN HAS NO `*` PATTERN (read on the forgotten view, publication `pubRX`),
    if its demand has no `*` entry pattern. -/
theorem handF_DRX_nonstar (hdin : ∀ m d, dem m d → NoStarK d.din.kind) {m : MethodId}
    {d' : DemandEdge}
    (h : handF P (forgetX (DRX P taint counted L dem emitX sat restrictIX recs sinks roots))
      (pubRX P (DRX P taint counted L dem emitX sat restrictIX recs sinks roots) dem) m d') :
    NoStarK d'.din.kind ∧ ∀ jp, d'.dout = some jp → NoStarK jp.kind := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, _, _, hres, hd', _, _⟩ := handF_narrowX h
  subst hd'
  obtain ⟨p0, _, _, hc⟩ := restrictIX_some hres
  have hcI : restrictConcI gx.af p0 = some g' := restrictConcIX_fact hc
  obtain ⟨_, _, hns, _⟩ := AnyTaintExCov.concX_all P taint counted L dem emitX sat restrictIX recs
    sinks roots emitX_copies hR
  refine ⟨restrictConcI_nonstar hcI (nonstar_of_isStar hns), fun jp hjp => ?_⟩
  have hjp' : j = jp := Option.some.inj hjp
  rw [← hjp']
  exact DRX_init_nonstar hdin (DRX_edge_init hR)

#print axioms handF_DRX_nonstar

end RunX

/-- With patterns with no `*` tail, `insideLocXB` (the premise exclusion read) and `insideLocB` (no
    exclusion read) differ only for the premise exclusion Universe (`[any]` with the exclusion
    Universe at the path of a `$` pattern). -/
theorem insideLocXB_nonstar {j d : PFact} {jex : Excl} (hd : NoStarK d.kind) (hj : NoStarK j.kind)
    (h : insideLocXB j jex d = true) : insideLocB j d = true ∨ jex = .univ := by
  unfold insideLocXB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hb, hm⟩ := h
  have hb' : Nat.beq d.base j.base = true := hb
  cases hdp : dropPrefix d.path j.path with
  | none => rw [hdp] at hm; cases hm
  | some r =>
    rw [hdp] at hm
    cases r with
    | cons x r =>
      left
      unfold insideLocB coversB
      dsimp only
      rw [hb', hdp]
      exact hm
    | nil =>
      dsimp only at hm
      cases hdk : d.kind with
      | star e => exact absurd hdk (hd e)
      | any =>
        left
        unfold insideLocB coversB
        dsimp only
        rw [hb', hdp, hdk]
        rfl
      | exact =>
        cases hjk : j.kind with
        | star e => exact absurd hjk (hj e)
        | exact =>
          left
          unfold insideLocB coversB
          dsimp only
          rw [hb', hdp, hdk, hjk]
          rfl
        | any =>
          right
          rw [hdk, hjk] at hm
          cases jex with
          | univ => rfl
          | set ys => cases hm

#print axioms insideLocXB_nonstar

section CanonX
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {Ls LB : Nat → Nat}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : Nat → List (MethodId × Node × PFact)}

local notation "CS" => canonStateX P taint counted Ls LB sinks roots seeds
local notation "DBk" k => backOfX P counted (LB k) roots (seeds k) (CS k)
local notation "DEMk" k => demOfX P counted (LB k) roots (seeds k) (CS k)
local notation "RXk" k => runX P taint counted (Ls (k + 1)) (DEMk k) (RunStateX.rc (CS (k + 1)))
  sinks roots

/-- THE DEMAND PATTERNS OF THE CANONICAL X SEQUENCE HAVE NO `*` TAIL (as `canon_dem_nonstar`). -/
theorem canonX_dem_nonstar (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) :
    ∀ k m d, (DEMk k) m d → NoStarK d.din.kind ∧ ∀ p, d.dout = some p → NoStarK p.kind := by
  intro k
  induction k with
  | zero =>
    intro m d h
    exact demOfN_nonstar (hsd 0) (hsk 0)
      (fun m' d' hd => (handF_run1X_nonstar (P := P) (taint := taint) (counted := counted)
        (L := Ls 0) (sinks := sinks) (roots := roots) hd).1) h
  | succ k ih =>
    intro m d h
    exact demOfN_nonstar (hsd (k + 1)) (hsk (k + 1))
      (fun m' d' hd => (handF_DRX_nonstar (P := P) (taint := taint) (counted := counted)
        (L := Ls (k + 1)) (dem := DEMk k) (sat := satX) (recs := embedRecs (CS (k + 1)).rc)
        (sinks := sinks) (roots := roots) (fun m1 d1 h1 => (ih m1 d1 h1).1) hd).1) h

#print axioms canonX_dem_nonstar

/-- THE HAND-OFFS OF THE CANONICAL X SEQUENCE HAVE NO `*` ENTRY PATTERN; their exit patterns have
    no `*` tail, or (only after run 1) the tail `*/{}`. -/
theorem canonX_handF_nonstar (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {m : MethodId}
    {d : DemandEdge} (h : handF P (CS k).R (CS k).pub m d) :
    NoStarK d.din.kind ∧ ∀ p, d.dout = some p → NoStarOrEmpty p.kind := by
  cases k with
  | zero =>
    obtain ⟨h1, h2⟩ := handF_run1X_nonstar (P := P) (taint := taint) (counted := counted)
      (L := Ls 0) (sinks := sinks) (roots := roots) h
    refine ⟨h1, fun p hp => ?_⟩
    rcases h2 p hp with he | he
    · exact Or.inl (fun E hE => by rw [he] at hE; cases hE)
    · exact Or.inr he
  | succ k =>
    obtain ⟨h1, h2⟩ := handF_DRX_nonstar (P := P) (taint := taint) (counted := counted)
      (L := Ls (k + 1)) (dem := DEMk k) (sat := satX) (recs := embedRecs (CS (k + 1)).rc)
      (sinks := sinks) (roots := roots)
      (fun m1 d1 h1 => (canonX_dem_nonstar hsd hsk k m1 d1 h1).1) h
    exact ⟨h1, fun p hp => Or.inl (h2 p hp)⟩

#print axioms canonX_handF_nonstar

/-- THE FORWARD NARROWING OF THE X RUNS IS EXACT ON THE CANONICAL X SEQUENCE (every forward run
    `k + 1`): every demand edge `d'` that forward run `k + 1` hands off is `⟨g', some j⟩` for an
    annotated exit edge `(j, mj, jex) → gx` and a demand edge `d` of its demand: the premise `j`
    with its exclusion `jex` lies inside `D-c` of `d`, and the piece `g'` lies inside `D-p` of `d`
    WITHOUT ITS EXCLUSION (no exception: `D-p` has no `*` tail, and the run has no `*`
    conclusion). -/
theorem narrowing_canonX_fwd_exact (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {m : MethodId}
    {d' : DemandEdge} (h : handF P (CS (k + 1)).R (CS (k + 1)).pub m d') :
    ∃ j mj jex gx g' gex' d p, (RXk k) (.edge m j mj jex (P.exit m) gx) ∧
      (DEMk k) m d ∧ d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideLocXB j jex d.din = true ∧ insideLocB g'.fact p = true := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, _⟩ :=
    narrowing_canonX_fwd k h
  refine ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, ?_⟩
  obtain ⟨p0, hdo0, _, hc⟩ := restrictIX_some hres
  have hp0 : p0 = p := Option.some.inj (hdo0.symm.trans hdo)
  subst hp0
  have hcI : restrictConcI gx.af p0 = some g' := restrictConcIX_fact hc
  obtain ⟨_, _, hns, _⟩ := AnyTaintExCov.concX_all P taint counted (Ls (k + 1)) (DEMk k) emitX satX
    restrictIX (embedRecs (CS (k + 1)).rc) sinks roots emitX_copies hR
  rcases restrictConcI_inside hcI with hc' | ⟨_, ⟨E, hE⟩, _, _⟩ | ⟨⟨e, he⟩, _⟩
  · exact hc'
  · exact absurd hE ((canonX_dem_nonstar hsd hsk k m d hdem).2 p0 hdo E)
  · exact absurd he (nonstar_of_isStar hns e)

#print axioms narrowing_canonX_fwd_exact

/-- THE BACKWARD NARROWING IN LOCATION FORM ON THE CANONICAL X SEQUENCE (as
    `narrowing_canon_back_loc`; the backward run is the base run). -/
theorem narrowing_canonX_back_loc (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d' : DemandEdge} (h : (DEMk k) M d') :
    d' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk k) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ (jb : PFact) (gb' : AFact) (d : DemandEdge) (p : PFact),
      handF P (CS k).R (CS k).pub M d ∧ d.dout = some p ∧
      d' = ⟨gb'.fact, some jb⟩ ∧ (∀ l, jb.coversLoc l → d.din.coversLoc l) ∧
      (∀ l, gb'.fact.coversLoc l → p.coversLoc l) := by
  rcases narrowing_canonX_back k h with h1 | h2 | ⟨jb, gb, gb', d, p, _, _, hgb, _,
    hdB, hdo, hres, hd', hin, hcon⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨jb, gb', d, p, hdB, hdo, hd', fun l hl => insideLoc_coversLoc hin hl,
      ?_⟩)
    rcases hcon with hc | hc
    · exact fun l hl => insideLoc_coversLoc hc hl
    · obtain ⟨p0, hdo0, _, hc0⟩ := restrictI_some hres
      have hp0 : p0 = p := Option.some.inj (hdo0.symm.trans hdo)
      subst hp0
      exact rexc_empty_loc hc0 hc ((canonX_handF_nonstar hsd hsk k hdB).2 p0 hdo)
        (DB_edge_nonstar (hsd k) (hsk k) hgb)

#print axioms narrowing_canonX_back_loc

/-- THE NARROWING OVER ONE ROUND ON THE CANONICAL X SEQUENCE, with no exception cell. With concrete
    seeds with no `*` tail, every demand edge `d''` of forward run `k + 2` is the zero demand, a
    zero-premise backward edge (a seed path; not narrowed), or comes from a demand edge `d` of
    forward run `k + 1` (same method) through the annotated exit edge `(j, mj, jex) → gx` of the X
    run `k + 1`, and:
      * every exit location of `d''` is an exit location of `d` (EXACT: the forward piece lies inside
        `D-p` also without its exclusion);
      * every entry location of `d''` is an entry location of `d`, OR the premise exclusion `jex`
        is Universe (an `[any]` premise read only at its own path) and the location is a dropped
        location of `j` (`Dropped j jex`: strictly below the path of `j`). -/
theorem narrowing_canonX_loc_exact (hsd : ∀ k, BExact.SeedsConc (seeds k))
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) {M : MethodId}
    {d'' : DemandEdge} (h : (DEMk (k + 1)) M d'') :
    d'' = ⟨zeroFact, none⟩ ∨
    (∃ g, (DBk (k + 1)) (.edge M zeroFact ((Program.rev P).exit M) g) ∧ d'' = ⟨g.fact, none⟩) ∨
    ∃ (j : PFact) (mj : Bool) (jex : Excl) (gx : XFact) (jb : PFact) (gb' : AFact)
      (d : DemandEdge) (p : PFact),
      (RXk k) (.edge M j mj jex (P.exit M) gx) ∧ (DEMk k) M d ∧ d.dout = some p ∧
      d'' = ⟨gb'.fact, some jb⟩ ∧ (∀ l, jb.coversLoc l → p.coversLoc l) ∧
      ((∀ l, gb'.fact.coversLoc l → d.din.coversLoc l) ∨
        (jex = .univ ∧ ∀ l, gb'.fact.coversLoc l → d.din.coversLoc l ∨ Dropped j jex l)) := by
  rcases narrowing_canonX_back_loc hsd hsk (k + 1) h with h1 | h2 | ⟨jb, gb', dB, pB, hdB, hdo,
    hd'', hjb, hgb⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdop, _, hdB', hinF, hconF⟩ :=
      narrowing_canonX_fwd_exact hsd hsk k hdB
    subst hdB'
    have hpB : pB = j := (Option.some.inj hdo).symm
    subst hpB
    refine Or.inr (Or.inr ⟨pB, mj, jex, gx, jb, gb', d, p, hR, hdem, hdop, hd'',
      fun l hl => insideLoc_coversLoc hconF (hjb l hl), ?_⟩)
    have hdn := (canonX_dem_nonstar hsd hsk k M d hdem).1
    have hjn : NoStarK pB.kind := DRX_init_nonstar
      (fun m1 d1 h1 => (canonX_dem_nonstar hsd hsk k m1 d1 h1).1) (DRX_edge_init hR)
    rcases insideLocXB_nonstar hdn hjn hinF with hb | hu
    · exact Or.inl (fun l hl => insideLoc_coversLoc hb (hgb l hl))
    · exact Or.inr ⟨hu, fun l hl => covLoc_split (fun l' hl' => insideLocXB_sound hinF hl')
        (hgb l hl)⟩

#print axioms narrowing_canonX_loc_exact

end CanonX

end XSeq

/-! ## 5. A remark on the base location form, and CEGAR on the X entry side -/

/-- REMARK on `HandoffMain.narrowing_canon_loc`: its exit exception `∃ g g', RExc g p g'` holds for
    EVERY exit pattern `p` with a `*` tail (the existentials do not tie the cell to the edge). So
    that form says nothing at a `*` exit pattern; `narrowing_canon_loc_exact` is the form with no
    exception. -/
theorem base_loc_exception_weak {p : PFact} (hp : ∃ E, p.kind = .star E) :
    ∃ g g', RExc g p g' :=
  ⟨⟨⟨0, [], .any, .star⟩, false⟩, ⟨⟨0, p.path, .any, .star⟩, false⟩, Or.inl ⟨rfl, hp, rfl, rfl⟩⟩

/-- The same for its entry exception `∃ gb j, RExc gb j gb'`: it holds for every piece `gb'` with
    the tail `[any]` or a `*` tail. -/
theorem base_loc_exception_weak_entry {gb' : AFact}
    (h : gb'.fact.kind = .any ∨ ∃ e, gb'.fact.kind = .star e) : ∃ gb j, RExc gb j gb' := by
  rcases h with hk | ⟨e, hk⟩
  · refine ⟨⟨⟨gb'.fact.base, [], .any, gb'.fact.mark⟩, gb'.demand⟩,
      ⟨0, gb'.fact.path, .star Excl.empty, .star⟩, Or.inl ⟨rfl, ⟨Excl.empty, rfl⟩, ?_, rfl⟩⟩
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := gb'
    dsimp only at hk ⊢
    rw [hk]
  · exact ⟨gb', ⟨0, [], .exact, .star⟩, Or.inr ⟨⟨e, hk⟩, rfl⟩⟩

#print axioms base_loc_exception_weak
#print axioms base_loc_exception_weak_entry

namespace NSVec
open ApSpec.AnyTaintEx ApSpec.HandoffX

/-- The added fact `1.[any-taint]`, a binding `1.[5].$ → 2.*`: the binding gives the normal
    `2.[any-taint]` with the exclusion Universe (the `above` row of `annX`: `tailExcl $`). -/
def aT : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
def eU : MicroEdge := (⟨1, [5], .exact, .star⟩, ⟨2, [], .star Excl.empty, .star⟩)
/-- The premise `1.[any]` (mark `1`), the entry patterns `1.[any]` (emission) and `1.$`
    (restriction), the conclusion `2.$`, the exit pattern `2.$`. -/
def jA : PFact := ⟨1, [], .any, .conc 1⟩
def dcA : PFact := ⟨1, [], .any, .star⟩
def dcE : PFact := ⟨1, [], .exact, .star⟩
def gExact : XFact := ⟨⟨⟨2, [], .exact, .conc 1⟩, false⟩, Excl.empty⟩
def pE : PFact := ⟨2, [], .exact, .star⟩
/-- A backward premise `2.$` and a backward conclusion `1.[4].$`. -/
def jbE : PFact := ⟨2, [], .exact, .conc 1⟩
def gb4 : AFact := ⟨⟨1, [4], .exact, .conc 1⟩, false⟩

/-- THE EXCLUSION UNIVERSE IS A REAL CELL, AND THE ENTRY SIDE LOSES A LOCATION THERE. The binding
    gives `2.[any-taint]/Universe`; the emission of an `[any-taint]/Universe` added fact by the entry
    pattern `1.[any]` gives the premise `1.[any]` with the exclusion Universe; it lies inside
    `D-c = 1.$` only with its exclusion (no `*` tail anywhere); the restriction keeps the exit edge
    `2.$`; the hand-off `⟨2.$, some 1.[any]⟩` drops the exclusion; the backward restriction keeps the
    backward edge `2.$ → 1.[4].$`. -/
theorem entry_univ :
    bindX aT eU = ⟨[⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .univ⟩], []⟩ ∧
    emitX dcA jA .univ = some (jA, .univ) ∧
    insideLocXB jA .univ dcE = true ∧ insideLocB jA dcE = false ∧
    restrictIX jA .univ gExact ⟨dcE, some pE⟩ = some gExact ∧
    insideLocB jbE gExact.af.fact = true ∧
    restrictI jbE gb4 ⟨gExact.af.fact, some jA⟩ = some gb4 := by decide

/-- The entry location `1.[4]` of the new demand edge is not in `D-c = 1.$`; it is a dropped
    location of the premise `1.[any]` with the exclusion Universe. -/
theorem entry_univ_loc :
    gb4.fact.coversLoc ⟨1, [4], 1⟩ ∧ ¬ dcE.coversLoc ⟨1, [4], 1⟩ ∧
    HandoffXMain.Dropped jA .univ ⟨1, [4], 1⟩ := by
  refine ⟨⟨rfl, [], rfl, rfl⟩, ?_, ⟨[4], rfl, rfl⟩⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [4] := by
    have h' : [4] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  have ht' : σ = [] := ht
  rw [hσ] at ht'
  exact List.cons_ne_nil 4 [] ht'

#print axioms entry_univ
#print axioms entry_univ_loc

end NSVec

end ApSpec.HandoffNoStar
