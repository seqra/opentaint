/-
  Entry-tail invariants for the request-free base runs of F72.
  The star-with-exclusion emission cell is total, but the canonical hand-offs do not produce it.
  This is a shape proof, not a coverage or iteration theorem.
-/
import ApSpec.AbsWitness
import ApSpec.AbsExact
import ApSpec.ReviewDemand

namespace ApSpec.AbsHandoff
open ApSpec ApSpec.Abs ApSpec.Handoff ApSpec.HandoffNoStar ApSpec.Reverse

/-- Normalized marks: a concrete mark or the unrestricted abstract mark. -/
def NormMark (m : MarkA) : Prop := match m with
  | .starEx _ => False
  | _ => True

theorem normFact_normMark (f : PFact) : NormMark (normFact f).mark := by
  change NormMark (markNorm f.mark)
  cases f.mark <;> trivial

/-- Incoming entry patterns have no star tail and no excluded abstract mark. -/
def EntryShape (dem : MethodId → DemandEdge → Prop) : Prop :=
  ∀ m d, dem m d → NoStarK d.din.kind ∧ NormMark d.din.mark

theorem emitW_cross_or_conc {d a j : PFact} (hk : NoStarK d.kind)
    (hm : NormMark d.mark) (he : emitW d a = some j) :
    CrossK j.kind ∨ ∃ t, j.mark = .conc t := by
  cases hd : d.mark with
  | star =>
    have hj := (emitW_star hd he).1
    subst j
    apply Or.inl
    cases hdk : d.kind with
    | star e => exact (hk e hdk).elim
    | any => simp [flowForm, flowK, hdk, CrossK]
    | exact => simp [flowForm, flowK, hdk, CrossK]
  | starEx x => rw [hd] at hm; exact hm.elim
  | conc t =>
    rw [emitW_nonstar (by rw [hd]; intro h; cases h)] at he
    have hmatch := (RCore.emitM_cases he).2.1
    have hj := RCore.emitM_mark he
    cases ham : a.mark with
    | star => rw [hd, ham] at hmatch; cases hmatch
    | starEx x => rw [hd, ham] at hmatch; cases hmatch
    | conc u => exact Or.inr ⟨u, hj.trans ham⟩

/-- Empty premise exclusions come from the entry shape and legality of the binding result. -/
theorem emitW_premEmpty {d a j : PFact} (hk : NoStarK d.kind) (hm : NormMark d.mark)
    (ha : ∀ t, a.mark = .conc t → NoStarK a.kind) (he : emitW d a = some j) :
    Reverse.PremEmpty j.kind := by
  cases hd : d.mark with
  | star =>
    have hj := (emitW_star hd he).1
    rw [hj]
    change Reverse.PremEmpty (flowK d.kind)
    cases hdk : d.kind with
    | star e => exact (hk e hdk).elim
    | any => rfl
    | exact => trivial
  | starEx x => rw [hd] at hm; exact hm.elim
  | conc t =>
    rw [emitW_nonstar (by rw [hd]; intro h; cases h)] at he
    have hmatch := (RCore.emitM_cases he).2.1
    have han : NoStarK a.kind := by
      cases ham : a.mark with
      | star => rw [hd, ham] at hmatch; cases hmatch
      | starEx x => rw [hd, ham] at hmatch; cases hmatch
      | conc u => exact ha u ham
    have hjn := emitM_nonstar he hk han
    cases hjk : j.kind with
    | star e => exact (hjn e hjk).elim
    | any => trivial
    | exact => trivial

section Forward
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact} {rc : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

local notation "FR" => DRA P counted L dem emitW sat restrict rc sinks roots

theorem forward_concrete_premise {o : Obj} (h : FR o) : ReviewDemand.ConcEdge o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro hc
    obtain ⟨t, ht⟩ := hc
    exact ⟨t, by rw [startFact_mark, ht]⟩
  | @step M i n f n' s f' _ _ hf ih =>
    intro hc
    obtain ⟨t, ht⟩ := ih hc
    exact transfer_mark_conc ht hf
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hc
    obtain ⟨t, ht⟩ := ihF hc
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨t3, by rw [limitF_mark, h3]⟩
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hc
    obtain ⟨t, ht⟩ := ihF hc
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨t3, by rw [limitF_mark, h3]⟩
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf ih =>
    intro hc
    obtain ⟨t, ht⟩ := ih hc
    exact cleanRes_mark_conc ht hf
  | filt _ _ _ ih => exact ih

theorem forward_init_shape (hd : EntryShape dem) {M : MethodId} {j : PFact}
    (h : FR (.init M j)) : CrossK j.kind ∨ ∃ t, j.mark = .conc t := by
  cases h with
  | root => exact Or.inl trivial
  | initR _ hdem he =>
    have hs := hd _ _ hdem
    exact emitW_cross_or_conc hs.1 hs.2 he

theorem forward_init_premEmpty (hd : EntryShape dem) {M : MethodId} {j : PFact}
    (h : FR (.init M j)) : Reverse.PremEmpty j.kind := by
  cases h with
  | root => trivial
  | initR ha hdem he =>
    have hs := hd _ _ hdem
    apply emitW_premEmpty hs.1 hs.2 _ he
    cases ha with
    | added _ _ _ hx =>
      intro t ht e hek
      exact Invariant.AbsMark.not_conc (Invariant.applyEdge_Legal hx e hek).1 t ht

/-- A raw star conclusion is crossable before summary restriction. -/
theorem forward_star_cross (hd : EntryShape dem) {M : MethodId} {j : PFact} {n : Node}
    {g : AFact} {e : Excl} (hj : FR (.init M j)) (hg : FR (.edge M j n g))
    (hk : g.fact.kind = .star e) : Cross j g := by
  have hl := RExact.final_star_legalR P counted L dem emitW sat restrict rc sinks roots
    (DRA_sub_DR _ _ _ _ _ _ _ _ _ _ hg) hk
  rcases forward_init_shape hd hj with hcross | hconc
  · exact cross_of_star_concl hl.2 hcross hk hl.1
  · obtain ⟨t, ht⟩ := forward_concrete_premise hg hconc
    exact (Invariant.AbsMark.not_conc hl.1 t ht).elim

theorem handFA_forward_entry_shape (hd : EntryShape dem) :
    EntryShape (handFA P FR (pubR dem)) := by
  intro M d h
  obtain ⟨d0, ⟨j, g, g', hj, hg, hnc, ⟨dp, _, hp⟩, rfl⟩, rfl⟩ := h
  obtain ⟨p, _, _, hc⟩ := restrictI_some hp
  refine ⟨?_, normFact_normMark _⟩
  change NoStarK g'.fact.kind
  apply restrictConcI_nonstar hc
  intro e hk
  exact hnc (forward_star_cross hd hj hg hk)

end Forward

section Backward
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {rc : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

local notation "BR" => DBA Pb counted L dem emit sat restrict rc sinks roots seeds zbind

theorem backward_legal (hsk : ∀ M n s, (M, n, s) ∈ seeds → NoStarK s.kind)
    {o : Obj} (h : BR o) : LegalE o := by
  induction h with
  | root => trivial
  | start _ _ => exact fun _ hk => Invariant.startFact_legal hk
  | step _ _ hf ih =>
    rcases Invariant.transfer_mem hf with rfl | ⟨x, e, _, hx, rfl⟩
    · exact ih
    · exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hx)
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ hr' _ _ _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')
  | retRec _ _ _ _ _ _ _ _ hr' _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')
  | vuln => trivial
  | clean _ _ hf ih => exact Invariant.cleanRes_Legal ih hf
  | filt _ _ _ ih => exact ih
  | zpass => intro e hk; cases hk
  | zin => trivial
  | seed hs _ _ =>
    exact Invariant.limitF_Legal (fun e hk => absurd hk (hsk _ _ _ hs e))
  | zret _ _ _ _ _ _ hr' _ _ =>
    exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')

/-- The backward hand-off has no star entry even if some backward premises are FLOW. -/
theorem demOfNA_backward_entry_shape
    (hsd : ∀ M n s, (M, n, s) ∈ seeds → ∃ t, s.mark = .conc t)
    (hsk : ∀ M n s, (M, n, s) ∈ seeds → NoStarK s.kind) :
    EntryShape (demOfNA Pb BR (pubR dem)) := by
  intro M d h
  obtain ⟨d0, h0, rfl⟩ := h
  refine ⟨?_, normFact_normMark _⟩
  change NoStarK d0.din.kind
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', _, _, hgb, hnc, ⟨dp, _, hp⟩, rfl⟩
  · intro e he; cases he
  · intro e he
    have hl := backward_legal hsk hg e he
    obtain ⟨t, ht⟩ := ReviewDemand.backward_zero_premise_concrete hsd hg
    exact Invariant.AbsMark.not_conc hl.1 t ht
  · obtain ⟨p, _, _, hc⟩ := restrictI_some hp
    apply restrictConcI_nonstar hc
    intro e he
    have hl := backward_legal hsk hgb e he
    exact hnc (crossB_of_star_concl hl.2 he hl.1)

end Backward

section BackwardPremises
variable {Pb : Program} {counted : Acc → Bool} {L : Nat}
  {dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact} {rc : Recs}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

theorem backward_init_premEmpty (hd : EntryShape dem) {M : MethodId} {j : PFact}
    (h : DBA Pb counted L dem emitW sat restrict rc sinks roots seeds zbind (.init M j)) :
    Reverse.PremEmpty j.kind := by
  cases h with
  | root => trivial
  | zin => trivial
  | initR ha hdem he =>
    have hs := hd _ _ hdem
    apply emitW_premEmpty hs.1 hs.2 _ he
    cases ha with
    | added _ _ _ hx =>
      intro t ht e hek
      exact Invariant.AbsMark.not_conc (Invariant.applyEdge_Legal hx e hek).1 t ht

/-- The same premise is retained along each edge, including the special zero paths. -/
def EmptyPrem : Obj → Prop
  | .init _ j => Reverse.PremEmpty j.kind
  | .edge _ j _ _ => Reverse.PremEmpty j.kind
  | _ => True

theorem backward_premEmpty (hd : EntryShape dem) {o : Obj}
    (h : DBA Pb counted L dem emitW sat restrict rc sinks roots seeds zbind o) :
    EmptyPrem o := by
  induction h with
  | root => trivial
  | start _ ih => exact ih
  | step _ _ _ ih => exact ih
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR ha hd0 he _ => exact backward_init_premEmpty hd (DBA.initR ha hd0 he)
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | retRec _ _ _ _ _ _ _ _ _ ih => exact ih
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | filt _ _ _ ih => exact ih
  | zpass => trivial
  | zin => trivial
  | seed => trivial
  | zret => trivial

end BackwardPremises

/-- Reversal exactness with the premise condition derived from the normalized entry shape. -/
theorem DBW_rev_record_exact_shape {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} (hshape : EntryShape dem)
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hnz : Backward.NoZeroBack P)
    (hR : Reverse.RevStmts P) (hC : Reverse.RevCalls P)
    (hrecs : BExact.RecsExactNZ (Program.rev P) rc) {M : MethodId}
    {jb : PFact} {gb : AFact} {l l0 : Loc}
    (h : DBW (Program.rev P) counted L dem rc roots seeds
      (.edge M jb ((Program.rev P).exit M) gb))
    (hi : jb ≠ zeroFact) (hn : gb.demand = false)
    (hd : den (revEdge jb gb.fact).1 (revEdge jb gb.fact).2 l l0) :
    Flow P M l (P.exit M) l0 :=
  DBW_rev_record_exact hmw hup hnz hR hC hrecs h hi hn (backward_premEmpty hshape h) hd

theorem entryShape_PatTail {dem : MethodId → DemandEdge → Prop} (hd : EntryShape dem)
    {M : MethodId} {d : DemandEdge} (h : dem M d) : PatTailB d.din.kind = true := by
  have hk := (hd _ _ h).1
  cases he : d.din.kind with
  | exact => rfl
  | any => rfl
  | star e => exact (hk e he).elim

/-- The shape state records the actual forward closure and its publication rule. -/
structure ShapeState where
  run : Obj → Prop
  pub : Pub

def shapeNext (P Pb : Program) (counted : Acc → Bool) (lf lb : Nat) (rcf rcb : Recs)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : List (MethodId × Node × PFact)) (prev : ShapeState) : ShapeState :=
  let db := handFA P prev.run prev.pub
  let br := DBW Pb counted lb db rcb roots seeds
  let df := demOfNA Pb br (pubR db)
  ⟨DRW P counted lf df rcf sinks roots, pubR df⟩

def shapeSeq (P Pb : Program) (counted : Acc → Bool) (lf lb : Nat → Nat)
    (rcf rcb : Nat → Recs) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact)) : Nat → ShapeState
  | 0 => ⟨D P counted (lf 0) policy1 sinks roots, pubD⟩
  | k + 1 => shapeNext P Pb counted (lf (k + 1)) (lb k) (rcf (k + 1)) (rcb k)
      sinks roots (seeds k) (shapeSeq P Pb counted lf lb rcf rcb sinks roots seeds k)

/-- Every backward entry demand of the explicit alternating base sequence has a non-star tail.
    Records can be arbitrary here: their exactness is a separate obligation. -/
theorem shapeSeq_entry_shape (P Pb : Program) (counted : Acc → Bool) (lf lb : Nat → Nat)
    (rcf rcb : Nat → Recs) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact))
    (hsd : ∀ k M n s, (M, n, s) ∈ seeds k → ∃ t, s.mark = .conc t)
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) (k : Nat) :
    EntryShape (handFA P (shapeSeq P Pb counted lf lb rcf rcb sinks roots seeds k).run
      (shapeSeq P Pb counted lf lb rcf rcb sinks roots seeds k).pub) := by
  cases k with
  | zero =>
    intro M d h
    obtain ⟨d0, h0, rfl⟩ := h
    exact ⟨(handF_run1_nonstar h0).1, normFact_normMark _⟩
  | succ k =>
    dsimp only [shapeSeq, shapeNext]
    apply handFA_forward_entry_shape
    exact demOfNA_backward_entry_shape (hsd k) (hsk k)

/-- L6's tail guard holds in every backward demand of the base sequence. -/
theorem shapeSeq_PatTail (P Pb : Program) (counted : Acc → Bool) (lf lb : Nat → Nat)
    (rcf rcb : Nat → Recs) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
    (seeds : Nat → List (MethodId × Node × PFact))
    (hsd : ∀ k M n s, (M, n, s) ∈ seeds k → ∃ t, s.mark = .conc t)
    (hsk : ∀ k M n s, (M, n, s) ∈ seeds k → NoStarK s.kind) {k M d}
    (h : handFA P (shapeSeq P Pb counted lf lb rcf rcb sinks roots seeds k).run
      (shapeSeq P Pb counted lf lb rcf rcb sinks roots seeds k).pub M d) :
    PatTailB d.din.kind = true :=
  entryShape_PatTail (shapeSeq_entry_shape P Pb counted lf lb rcf rcb sinks roots seeds hsd hsk k) h

#print axioms emitW_cross_or_conc
#print axioms emitW_premEmpty
#print axioms forward_init_premEmpty
#print axioms backward_init_premEmpty
#print axioms backward_premEmpty
#print axioms DBW_rev_record_exact_shape
#print axioms forward_star_cross
#print axioms handFA_forward_entry_shape
#print axioms demOfNA_backward_entry_shape
#print axioms shapeSeq_entry_shape
#print axioms shapeSeq_PatTail

end ApSpec.AbsHandoff
