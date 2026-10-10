/-
  ApSpec.HandoffRestrict — the restriction `restrictI` of `HandoffDefs.lean` (decision F70): the
  restriction of `ap.md` §6.4 as an INTERSECTION.

  Results (constructive; see the `#print axioms` lines):
    R1 `restrictI_sub`        the restriction only removes pairs, and keeps the layer.
    R2 `restrictI_contract`   the contract C5 for a premise INSIDE `D-c`: a pair of the edge whose
                              exit location is in `D-p` stays, in the same layer. Every cell holds,
                              also the `*` conclusions (`restrictConcI_cases` lists the cells).
                              `restrictI_not_RestrictContract`: the earlier contract form (entry
                              location in `D-c`, premise only overlapping it) is FALSE for
                              `restrictI`, so the coverage proof needs `emitM_inside`.
    R3 `emitM_inside`         an emitted premise lies inside its entry pattern (locations, marks
                              ignored). `insideLoc_coversLoc`: the location form of `insideLocB`.
    R4 `restrictI_inter`      every pair of a result has its entry in `D-c`, and its exit in
                              `D-p`, except in two cells (`RExc`): an `[any]` conclusion at or
                              above a `*/E` exit pattern (the result is the chain of `D-p` with the
                              tail `[any]`), and a `*` conclusion (the result is the edge itself).
                              `RVec.inter_exc_any`, `RVec.inter_exc_star`: each exception is real.
    R5 `handF_narrow`         THE NARROWING THEOREM: a demand edge that a restricted run hands off
                              lies inside the reversal of the demand edge that published it
                              (except `RExc`). `demOfN_narrow`: the same for the backward hand-off
                              (case 3). `handF_narrow_loc`: the location form. `handF_narrow_DR`:
                              for a restricted forward run with `emitM` the `*` exception does not
                              occur. `handF_narrow_DR_exact`: if also no exit pattern of the demand
                              has a `*` tail, the narrowing is exact. `handF_DR_nonstar`: if no
                              entry pattern of the demand has a `*` tail, the hand-off has no `*`
                              pattern (so the exception does not come back in the next round).
    R6 vectors (`decide`, namespace `RVec`)   every row of `restrictConcI`; the §6.4 example
                              (`[any]` against `$` gives `$`, `restrictU` keeps `[any]`); a premise
                              that only overlaps `D-c` (`restrictI` gives nothing, `restrictU` gives
                              a result).
    Also: `pubD_sub`, `pubR_sub` (a published piece only removes pairs: the hypothesis `hpubSub` of
    `HandoffBackward.lean`); `emitM_nonstar`, `DR_nonstar`, `DR_exit_not_star`,
    `restrictConcI_nonstar` (the `*`-free invariants of a restricted run with `emitM`).
  Helpers are in the namespace `RAux`.
-/
import ApSpec.HandoffDefs

namespace ApSpec.Handoff
open ApSpec ApSpec.Reverse

/-! ## 0. Helpers (namespace `RAux`) -/

namespace RAux

theorem dropPrefix_self' (p : List Acc) : dropPrefix p p = some [] :=
  CoreAux.dropPrefix_some.mpr (List.append_nil p).symm

/-- The second exclusion of a union is a part of it. -/
theorem subB_union_left' (e1 e2 : Excl) : e2.subB (e1.union e2) = true := by
  cases e1 with
  | univ => exact Invariant.subB_univ e2
  | set xs =>
    cases e2 with
    | univ => rfl
    | set ys =>
      show ys.all (fun a => memB a (xs ++ ys)) = true
      apply List.all_eq_true.mpr
      intro a ha
      rw [CoreAux.memB_append, CoreAux.memB_iff.mpr ha, Bool.or_true]

/-- The meet of the emission lies inside the tail of the demand pattern. -/
theorem tailSubB_meetK_right (a d : Kind) : tailSubB d (meetK a d) = true := by
  cases a with
  | any => exact tailSubB_refl d
  | exact =>
    cases d with
    | any => rfl
    | exact => rfl
    | star e => rfl
  | star e1 =>
    cases d with
    | any => rfl
    | exact => rfl
    | star e2 => exact subB_union_left' e1 e2

/-- The meet of a conclusion tail relates only pairs of the conclusion tail. -/
theorem meetConcK_tailF {k1 k2 : Kind} {σ τ : List Acc} (h : tailF (meetConcK k1 k2) σ τ) :
    tailF k1 σ τ := by
  cases k1 with
  | any => trivial
  | star e => cases k2 <;> exact h
  | exact => cases k2 <;> exact h

/-- A pair of the conclusion tail whose continuation the tail of `D-p` admits is a pair of the
    meet. -/
theorem meetConcK_tailF_of {k1 k2 : Kind} {σ τ : List Acc} (h1 : tailF k1 σ τ)
    (h2 : tailI k2 τ) : tailF (meetConcK k1 k2) σ τ := by
  cases k1 with
  | any =>
    cases k2 with
    | exact => exact h2
    | any => exact h1
    | star e => exact h1
  | star e => cases k2 <;> exact h1
  | exact => cases k2 <;> exact h1

/-- Every tail admits the empty continuation (the `Prop` form). -/
theorem tailI_nil (k : Kind) : tailI k [] := by
  cases k with
  | star e => exact CoreAux.admits_nil e
  | any => trivial
  | exact => rfl

#print axioms dropPrefix_self'
#print axioms subB_union_left'
#print axioms tailSubB_meetK_right
#print axioms meetConcK_tailF
#print axioms meetConcK_tailF_of
#print axioms tailI_nil

end RAux
open RAux

/-! ## 1. The cells of `restrictConcI` and `restrictI` -/

/-- The four cells of `restrictConcI` that give a result: AT `D-p` (the meet), BELOW `D-p` (the
    edge, if the tail of `D-p` admits the step), ABOVE `D-p` with an `[any]` conclusion (the chain
    of `D-p`), ABOVE `D-p` with a `*` conclusion (the edge, if its exclusion admits the step). -/
theorem restrictConcI_cases {sc g' : AFact} {p : PFact} (h : restrictConcI sc p = some g') :
    sc.fact.base = p.base ∧
    ((sc.fact.path = p.path ∧
        g' = ⟨⟨sc.fact.base, sc.fact.path, meetConcK sc.fact.kind p.kind, sc.fact.mark⟩,
          sc.demand⟩) ∨
     (∃ x r, sc.fact.path = p.path ++ x :: r ∧ admitsTailB p.kind (x :: r) = true ∧ g' = sc) ∨
     (∃ r, p.path = sc.fact.path ++ r ∧ r ≠ [] ∧ sc.fact.kind = .any ∧
        g' = ⟨⟨sc.fact.base, p.path, RCore.outKind p.kind, sc.fact.mark⟩, sc.demand⟩) ∨
     (∃ r e, p.path = sc.fact.path ++ r ∧ r ≠ [] ∧ sc.fact.kind = .star e ∧ e.admits r = true ∧
        g' = sc)) := by
  unfold restrictConcI at h
  cases hb : Nat.beq sc.fact.base p.base with
  | false => rw [hb, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hb, if_pos rfl] at h
    refine ⟨CoreAux.beq_iff.mp hb, ?_⟩
    cases hr : relate p.path sc.fact.path with
    | apart => rw [hr] at h; cases h
    | below r =>
      have hq := CoreAux.relate_below_inv hr
      rw [hr] at h
      cases r with
      | nil =>
        exact Or.inl ⟨by rw [hq, List.append_nil], (Option.some.inj h).symm⟩
      | cons x r =>
        dsimp only at h
        cases ha : admitsTailB p.kind (x :: r) with
        | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [ha, if_pos rfl] at h
          exact Or.inr (Or.inl ⟨x, r, hq, ha, (Option.some.inj h).symm⟩)
    | above r =>
      obtain ⟨hP, hr0⟩ := CoreAux.relate_above_inv hr
      rw [hr] at h
      dsimp only at h
      cases hk : sc.fact.kind with
      | any =>
        rw [hk] at h
        refine Or.inr (Or.inr (Or.inl ⟨r, hP, hr0, rfl, ?_⟩))
        rw [← Option.some.inj h]
        cases p.kind <;> rfl
      | star e =>
        rw [hk] at h
        dsimp only at h
        cases he : e.admits r with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [he, if_pos rfl] at h
          exact Or.inr (Or.inr (Or.inr ⟨r, e, hP, hr0, rfl, he, (Option.some.inj h).symm⟩))
      | exact => rw [hk] at h; cases h

#print axioms restrictConcI_cases

/-- A result of `restrictI`: the demand edge has an exit pattern, the premise lies inside the
    entry pattern, and the conclusion is the result of `restrictConcI`. -/
theorem restrictI_some {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictI j g d = some g') :
    ∃ p, d.dout = some p ∧ insideLocB j d.din = true ∧ restrictConcI g p = some g' := by
  unfold restrictI at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases hi : insideLocB j d.din with
    | false => rw [hi, if_neg Bool.false_ne_true] at h; cases h
    | true => rw [hi, if_pos rfl] at h; exact ⟨p, rfl, rfl, h⟩

theorem restrictI_of {j : PFact} {g : AFact} {d : DemandEdge} {p : PFact}
    (hd : d.dout = some p) (hi : insideLocB j d.din = true) :
    restrictI j g d = restrictConcI g p := by
  unfold restrictI
  rw [hd]
  dsimp only
  rw [if_pos hi]

/-- A `*` conclusion is never changed: the result is the edge itself. -/
theorem restrictConcI_star {sc g' : AFact} {p : PFact} {e : Excl} (hk : sc.fact.kind = .star e)
    (h : restrictConcI sc p = some g') : g' = sc := by
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, hk', _⟩ | ⟨_, _, _, _, _, _, h4⟩⟩ :=
    restrictConcI_cases h
  · rw [h1]
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
    dsimp only at hk ⊢
    subst hk
    cases p.kind <;> rfl
  · exact h2
  · rw [hk] at hk'; cases hk'
  · exact h4

#print axioms restrictI_some
#print axioms restrictI_of
#print axioms restrictConcI_star

/-! ## 2. R1: the restriction only removes pairs -/

theorem restrictConcI_sub {sc g' : AFact} {p : PFact} (h : restrictConcI sc p = some g') :
    g'.demand = sc.demand ∧ ∀ (j : PFact) l1 l2, den j g'.fact l1 l2 → den j sc.fact l1 l2 := by
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, hP, _, hk, h3⟩ | ⟨_, _, _, _, _, _, h4⟩⟩ :=
    restrictConcI_cases h
  · subst h1
    refine ⟨rfl, fun j l1 l2 hd => ?_⟩
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf⟩ := hd
    exact ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, meetConcK_tailF htf⟩
  · subst h2
    exact ⟨rfl, fun _ _ _ hd => hd⟩
  · subst h3
    refine ⟨rfl, fun j l1 l2 hd => ?_⟩
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, _⟩ := hd
    refine ⟨hb1, hb2, hm1, hm2, hps, σ, r ++ τ, hp1, ?_, hti, ?_⟩
    · rw [hp2]
      show p.path ++ τ = sc.fact.path ++ (r ++ τ)
      rw [hP, List.append_assoc]
    · rw [hk]
      trivial
  · subst h4
    exact ⟨rfl, fun _ _ _ hd => hd⟩

/-- R1. THE RESTRICTION ONLY REMOVES PAIRS, and keeps the layer. -/
theorem restrictI_sub : RestrictSub restrictI := by
  intro j g d g' h
  obtain ⟨p, _, _, hc⟩ := restrictI_some h
  obtain ⟨hdem, hsub⟩ := restrictConcI_sub hc
  exact ⟨hdem, fun l1 l2 hd => hsub j l1 l2 hd⟩

/-- Run 1 publishes each edge as it is: a published piece has the pairs of its edge. -/
theorem pubD_sub : ∀ m j g g', pubD m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 :=
  fun _ _ _ _ h _ _ hd => by
    have h' : _ = _ := h
    rw [h'] at hd
    exact hd

/-- A restricted run publishes intersections: a published piece has only pairs of its edge. -/
theorem pubR_sub (dem : MethodId → DemandEdge → Prop) :
    ∀ m j g g', pubR dem m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 :=
  fun _ j g g' ⟨d, _, hr⟩ l1 l2 hd => (restrictI_sub j g d g' hr).2 l1 l2 hd

#print axioms restrictConcI_sub
#print axioms restrictI_sub
#print axioms pubD_sub
#print axioms pubR_sub

/-! ## 3. R2: the contract C5 for a premise inside `D-c` -/

/-- R2. THE CONTRACT C5 of the intersection: if the premise lies inside `D-c`, a pair of the edge
    whose exit location is in `D-p` stays, in the same layer. The cells: at `D-p` the meet keeps
    the pair (the `D-p` tail admits the exit continuation; `[any] ∩ $ = $` keeps the pairs with
    the empty continuation, and the other cells keep the conclusion tail); below `D-p` the edge
    stays; above `D-p` an `[any]` conclusion gives the chain of `D-p`, a `*` conclusion stays (its
    exclusion admits the step: the continuation is the initial one), a `$` conclusion has no
    pair there. -/
theorem restrictI_contract {j : PFact} {g : AFact} {d : DemandEdge} {p : PFact} {l1 l2 : Loc}
    (hin : insideLocB j d.din = true) (hden : den j g.fact l1 l2) (hdout : d.dout = some p)
    (hp : p.coversLoc l2) :
    ∃ g', restrictI j g d = some g' ∧ den j g'.fact l1 l2 ∧ g'.demand = g.demand := by
  rw [restrictI_of hdout hin]
  have hden0 := hden
  obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf⟩ := hden
  obtain ⟨hbp, σ', hpp, htp⟩ := hp
  have hb : Nat.beq g.fact.base p.base = true := by rw [← hb2, ← hbp]; exact Nat.beq_refl _
  have hpath : p.path ++ σ' = g.fact.path ++ τ := by rw [← hpp, ← hp2]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, hr, hτ⟩
  · cases r with
    | nil =>
      -- at the path of `D-p`: the meet
      have hτp : tailI p.kind τ := by rw [hσ] at htp; exact htp
      refine ⟨⟨⟨g.fact.base, g.fact.path, meetConcK g.fact.kind p.kind, g.fact.mark⟩, g.demand⟩,
        ?_, ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, meetConcK_tailF_of htf hτp⟩, rfl⟩
      unfold restrictConcI
      rw [if_pos hb, hrel]
    | cons x r =>
      -- below `D-p`: keep the edge
      have ha : admitsTailB p.kind (x :: r) = true := by
        rw [hσ] at htp
        exact CoreAux.tailI_append_admits htp
      refine ⟨g, ?_, hden0, rfl⟩
      unfold restrictConcI
      rw [if_pos hb, hrel]
      show (if admitsTailB p.kind (x :: r) = true then _ else _) = _
      rw [if_pos ha]
  · -- above `D-p`
    cases hk : g.fact.kind with
    | star e =>
      -- correlated: the continuation is the initial one, so `e` admits the step
      rw [hk] at htf
      obtain ⟨hτσ, he⟩ := htf
      have her : e.admits r = true := by
        rw [← hτσ, hτ] at he
        exact CoreAux.tailI_append_admits (k := .star e) he
      refine ⟨g, ?_, hden0, rfl⟩
      unfold restrictConcI
      rw [if_pos hb, hrel, hk]
      show (if e.admits r = true then _ else _) = _
      rw [if_pos her]
    | any =>
      -- uncorrelated: the new conclusion is the chain of `D-p`
      refine ⟨⟨⟨g.fact.base, p.path, RCore.outKind p.kind, g.fact.mark⟩, g.demand⟩, ?_, ?_, rfl⟩
      · unfold restrictConcI
        rw [if_pos hb, hrel, hk]
        dsimp only
        cases p.kind <;> rfl
      · refine ⟨hb1, hb2, hm1, hm2, hps, σ, σ', hp1, hpp, hti, ?_⟩
        cases hpk : p.kind with
        | exact => rw [hpk] at htp; exact htp
        | any => trivial
        | star e => trivial
    | exact =>
      rw [hk] at htf
      have hτ0 : τ = [] := htf
      rw [hτ0] at hτ
      cases r with
      | nil => exact absurd rfl hr
      | cons x r' => exact absurd hτ.symm (List.cons_ne_nil x (r' ++ σ'))

#print axioms restrictI_contract

/-! ## 4. R3: an emitted premise lies inside its entry pattern -/

/-- R3. An emitted premise lies inside the entry pattern that emitted it (locations, marks
    ignored). At the demand chain: the meet of the tails lies inside the demand tail; below the
    chain: the added fact, whose step the demand tail admits; above the chain: the demand chain
    itself. -/
theorem emitM_inside {d a j : PFact} (h : emitM d a = some j) : insideLocB j d = true := by
  obtain ⟨hb, _, ⟨hq, h1⟩ | ⟨x, r, hq, hx, h2⟩ | ⟨r, _, _, _, _, h3⟩⟩ := RCore.emitM_cases h
  · subst h1
    unfold insideLocB coversB
    dsimp only
    rw [hb, hq, dropPrefix_self']
    exact tailSubB_meetK_right a.kind d.kind
  · subst h2
    unfold insideLocB coversB
    dsimp only
    rw [hb, hq, Store.dropPrefix_append]
    exact hx
  · subst h3
    unfold insideLocB coversB
    dsimp only
    rw [Nat.beq_refl, dropPrefix_self']
    exact tailSubB_refl d.kind

/-- The location form of `insideLocB`: every location of `j` is a location of `d`. -/
theorem insideLoc_coversLoc {j d : PFact} {l : Loc} (h : insideLocB j d = true)
    (hj : j.coversLoc l) : d.coversLoc l := by
  have hc : (⟨j.base, j.path, j.kind, .star⟩ : PFact).covers l := ⟨hj.1, hj.2, trivial⟩
  have hd := coversB_sound h hc
  exact ⟨hd.1, hd.2.1⟩

/-- An emitted premise covers only locations of its entry pattern. -/
theorem emitM_coversLoc {d a j : PFact} {l : Loc} (h : emitM d a = some j) (hj : j.coversLoc l) :
    d.coversLoc l :=
  insideLoc_coversLoc (emitM_inside h) hj

#print axioms emitM_inside
#print axioms insideLoc_coversLoc
#print axioms emitM_coversLoc

/-! ## 5. R4: the intersection property, with its exact exceptions -/

/-- THE TWO EXCEPTIONS of the intersection (the cells that `meetConcK` and `restrictConcI` keep
    whole), for the edge conclusion `g`, the exit pattern `p` and the result `g'`:
    * an `[any]` conclusion at or above a `*/E` exit pattern: the result is the chain of `D-p`
      with the tail `[any]` (W2: a concrete mark has no `*` tail, so the exclusion `E` is not
      applied);
    * a `*` conclusion: the result is the edge itself (a cut to `$` would add pairs). -/
def RExc (g : AFact) (p : PFact) (g' : AFact) : Prop :=
  (g.fact.kind = .any ∧ (∃ E, p.kind = .star E) ∧
    g'.fact = ⟨g.fact.base, p.path, .any, g.fact.mark⟩ ∧ g'.demand = g.demand) ∨
  ((∃ e, g.fact.kind = .star e) ∧ g' = g)

/-- The exit part of R4, for the conclusion restriction. -/
theorem restrictConcI_exit {sc g' : AFact} {p : PFact} (h : restrictConcI sc p = some g')
    {j : PFact} {l1 l2 : Loc} (hd : den j g'.fact l1 l2) :
    p.coversLoc l2 ∨ RExc sc p g' := by
  obtain ⟨hbp, ⟨hq, h1⟩ | ⟨x, r, hq, ha, h2⟩ | ⟨r, _, _, hk, h3⟩ | ⟨r, e, _, _, hk, _, h4⟩⟩ :=
    restrictConcI_cases h
  · -- at `D-p`: the meet
    subst h1
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hq hd
    subst hbp hq
    obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, htf⟩ := hd
    cases k with
    | exact =>
      -- the exit continuation is empty
      have hτ : τ = [] := by cases pk <;> exact htf
      left
      exact ⟨hb2, [], by rw [hp2, hτ], tailI_nil pk⟩
    | star e =>
      right; right
      exact ⟨⟨e, rfl⟩, by cases pk <;> rfl⟩
    | any =>
      cases pk with
      | exact =>
        have hτ : τ = [] := htf
        left
        exact ⟨hb2, [], by rw [hp2, hτ], rfl⟩
      | any =>
        left
        exact ⟨hb2, τ, hp2, trivial⟩
      | star E =>
        right; left
        exact ⟨rfl, ⟨E, rfl⟩, rfl, rfl⟩
  · -- below `D-p`: the edge, and the tail of `D-p` admits the step
    subst h2
    obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _⟩ := hd
    left
    refine ⟨by rw [hb2]; exact hbp, x :: r ++ τ, ?_, CoreAux.tailI_cons_append ha⟩
    rw [hp2, hq, List.append_assoc]
  · -- above `D-p`, an `[any]` conclusion: the chain of `D-p`
    subst h3
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hk hd
    subst hbp hk
    obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, htf⟩ := hd
    cases pk with
    | exact =>
      have hτ : τ = [] := htf
      left
      exact ⟨hb2, [], by rw [hp2, hτ], rfl⟩
    | any =>
      left
      exact ⟨hb2, τ, hp2, trivial⟩
    | star E =>
      right; left
      exact ⟨rfl, ⟨E, rfl⟩, rfl, rfl⟩
  · -- above `D-p`, a `*` conclusion: the edge
    exact Or.inr (Or.inr ⟨⟨e, hk⟩, h4⟩)

/-- R4. THE INTERSECTION PROPERTY. Every pair of a result of `restrictI` has its entry location
    in `D-c` (the premise lies inside `D-c`) and its exit location in `D-p`, except in the two
    cells of `RExc`. -/
theorem restrictI_inter {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictI j g d = some g') {l1 l2 : Loc} (hd : den j g'.fact l1 l2) :
    d.din.coversLoc l1 ∧ ∃ p, d.dout = some p ∧ (p.coversLoc l2 ∨ RExc g p g') := by
  obtain ⟨p, hdo, hin, hc⟩ := restrictI_some h
  exact ⟨insideLoc_coversLoc hin (RCore.coversLoc_of_den hd), p, hdo, restrictConcI_exit hc hd⟩

/-- In the `[any]` exception the exit location is still on the chain of `D-p` (at or below its
    path): only the tail exclusion of `D-p` is not applied. -/
theorem rexc_any_chain {g g' : AFact} {p : PFact} {j : PFact} {l1 l2 : Loc}
    (hx : g'.fact = ⟨g.fact.base, p.path, .any, g.fact.mark⟩) (hbp : g.fact.base = p.base)
    (hd : den j g'.fact l1 l2) : l2.base = p.base ∧ ∃ τ, l2.path = p.path ++ τ := by
  obtain ⟨_, hb2, _, _, _, _, τ, _, hp2, _, _⟩ := hd
  rw [hx] at hb2 hp2
  exact ⟨by rw [hb2]; exact hbp, τ, hp2⟩

#print axioms restrictConcI_exit
#print axioms restrictI_inter
#print axioms rexc_any_chain

/-! ### Remark: the `*` cell at `D-p` has an exact form

  `meetConcK` keeps a correlated `*/e` conclusion at the path of `D-p` as it is (a cut to `$` would
  add pairs). The exact meet is representable: the correlated `*/(e ∪ tailExcl k)` relates exactly
  the pairs of `*/e` whose exit continuation the `D-p` tail `k` admits (`star_meet_exact`). For
  `k = $` it is `*/Universe` (only the empty continuation). It is a legal final fact (the mark of
  a `*` conclusion is abstract). A restricted run with `emitM` has no `*` conclusion
  (`DR_exit_not_star`), so this cell does not change a restricted run. The proposal is in the
  log (`meetConcK (.star e) k = .star (e.union (tailExcl k))`). -/

theorem tailExcl_admits_iff (k : Kind) (σ : List Acc) :
    (tailExcl k).admits σ = true ↔ tailI k σ := by
  cases k with
  | star e => exact Iff.rfl
  | any => exact ⟨fun _ => trivial, fun _ => CoreAux.empty_admits σ⟩
  | exact =>
    refine ⟨CoreAux.univ_admits, fun h => ?_⟩
    have h' : σ = [] := h
    subst h'
    rfl

theorem star_meet_exact (e : Excl) (k : Kind) (σ τ : List Acc) :
    tailF (.star (e.union (tailExcl k))) σ τ ↔ tailF (.star e) σ τ ∧ tailI k τ := by
  constructor
  · intro ⟨hτ, hX⟩
    rw [CoreAux.Excl.admits_union, Bool.and_eq_true] at hX
    refine ⟨⟨hτ, hX.1⟩, ?_⟩
    rw [hτ]
    exact (tailExcl_admits_iff k σ).mp hX.2
  · intro ⟨⟨hτ, he⟩, hk⟩
    refine ⟨hτ, ?_⟩
    rw [hτ] at hk
    rw [CoreAux.Excl.admits_union, he, (tailExcl_admits_iff k σ).mpr hk]
    rfl

#print axioms tailExcl_admits_iff
#print axioms star_meet_exact

/-- The proposed meet (not in `HandoffDefs.lean`): as `meetConcK`, and the exact correlated meet
    for a `*` conclusion. -/
def meetConcKX : Kind → Kind → Kind
  | .any,    .exact => .exact
  | .star e, k      => .star (e.union (tailExcl k))
  | k,       _      => k

/-- The two tail properties that `restrictI_sub` and `restrictI_contract` use in the meet cell
    hold for the proposed meet. The other cells do not change, so both theorems hold for it with
    the same proofs. -/
theorem meetConcKX_tailF {k1 k2 : Kind} {σ τ : List Acc} (h : tailF (meetConcKX k1 k2) σ τ) :
    tailF k1 σ τ := by
  cases k1 with
  | any => trivial
  | star e => exact ((star_meet_exact e k2 σ τ).mp h).1
  | exact => cases k2 <;> exact h

theorem meetConcKX_tailF_of {k1 k2 : Kind} {σ τ : List Acc} (h1 : tailF k1 σ τ)
    (h2 : tailI k2 τ) : tailF (meetConcKX k1 k2) σ τ := by
  cases k1 with
  | any =>
    cases k2 with
    | exact => exact h2
    | any => exact h1
    | star e => exact h1
  | star e => exact (star_meet_exact e k2 σ τ).mpr ⟨h1, h2⟩
  | exact => cases k2 <;> exact h1

/-- The proposed meet is exact except in the `[any] ∩ */E` cell: every pair of the meet has its
    exit continuation in the `D-p` tail. -/
theorem meetConcKX_exact {k1 k2 : Kind} {σ τ : List Acc} (h : tailF (meetConcKX k1 k2) σ τ) :
    tailI k2 τ ∨ (k1 = .any ∧ ∃ E, k2 = .star E) := by
  cases k1 with
  | any =>
    cases k2 with
    | exact => exact Or.inl h
    | any => exact Or.inl trivial
    | star E => exact Or.inr ⟨rfl, E, rfl⟩
  | star e => exact Or.inl ((star_meet_exact e k2 σ τ).mp h).2
  | exact =>
    have hτ : τ = [] := by cases k2 <;> exact h
    rw [hτ]
    exact Or.inl (tailI_nil k2)

#print axioms meetConcKX_tailF
#print axioms meetConcKX_tailF_of
#print axioms meetConcKX_exact

/-! ### Each exception is real (namespace `RVec`) -/

namespace RVec

/-- The `[any]` exception: the edge `1.$ → 2.[any]` (mark `1`), the demand edge
    `(1.$, 2.*/{4})`. The result is `2.[any]`; the pair `1 → 2.[4]` is in the result, but not in
    `D-p`. -/
def xaJ : PFact := ⟨1, [], .exact, .conc 1⟩
def xaG : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩
def xaP : PFact := ⟨2, [], .star (.set [4]), .star⟩
def xaD : DemandEdge := ⟨⟨1, [], .exact, .star⟩, some xaP⟩

theorem xa_vector : restrictI xaJ xaG xaD = some xaG := by decide

theorem inter_exc_any :
    restrictI xaJ xaG xaD = some xaG ∧ den xaJ xaG.fact ⟨1, [], 1⟩ ⟨2, [4], 1⟩ ∧
      ¬ xaP.coversLoc ⟨2, [4], 1⟩ := by
  refine ⟨xa_vector, ⟨rfl, rfl, rfl, rfl, trivial, [], [4], rfl, rfl, rfl, trivial⟩, ?_⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [4] := by
    have h' : [4] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  rw [hσ] at ht
  exact Bool.noConfusion ht

/-- The `*` exception: the edge `1.* → 2.*` (correlated, mark `*`), the demand edge
    `(1.*, 2.[5].$)`. The result is the edge; the pair `1.[] → 2.[]` is in the result, but not in
    `D-p` (it is above `D-p`). -/
def xsJ : PFact := ⟨1, [], .star Excl.empty, .star⟩
def xsG : AFact := ⟨⟨2, [], .star Excl.empty, .star⟩, false⟩
def xsP : PFact := ⟨2, [5], .exact, .star⟩
def xsD : DemandEdge := ⟨⟨1, [], .star Excl.empty, .star⟩, some xsP⟩

theorem xs_vector : restrictI xsJ xsG xsD = some xsG := by decide

theorem inter_exc_star :
    restrictI xsJ xsG xsD = some xsG ∧ den xsJ xsG.fact ⟨1, [], 3⟩ ⟨2, [], 3⟩ ∧
      ¬ xsP.coversLoc ⟨2, [], 3⟩ := by
  refine ⟨xs_vector, ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨_, σ, hp, _⟩
  have h' : ([] : List Acc) = [5] ++ σ := hp
  exact List.cons_ne_nil 5 σ h'.symm

#print axioms xa_vector
#print axioms inter_exc_any
#print axioms xs_vector
#print axioms inter_exc_star

/-- The `*` exception also occurs AT `D-p`: the same edge and the demand edge `(1.*, 2.$)`. The
    result is the edge; the pair `1.[5] → 2.[5]` is in the result, but not in `D-p`. (The exact
    meet `*/Universe` of `star_meet_exact` removes it.) -/
def xtD : DemandEdge := ⟨⟨1, [], .star Excl.empty, .star⟩, some ⟨2, [], .exact, .star⟩⟩

theorem xt_vector : restrictI xsJ xsG xtD = some xsG := by decide

theorem inter_exc_star_at :
    restrictI xsJ xsG xtD = some xsG ∧ den xsJ xsG.fact ⟨1, [5], 3⟩ ⟨2, [5], 3⟩ ∧
      ¬ (⟨2, [], .exact, .star⟩ : PFact).coversLoc ⟨2, [5], 3⟩ := by
  refine ⟨xt_vector, ⟨rfl, rfl, trivial, rfl, trivial, [5], [5], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [5] := by
    have h' : [5] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  have h0 : σ = [] := ht
  rw [hσ] at h0
  exact List.cons_ne_nil 5 [] h0

#print axioms xt_vector
#print axioms inter_exc_star_at

end RVec

/-! ## 6. R5: THE NARROWING THEOREM -/

/-- The conclusion part of the narrowing: the result of `restrictConcI`, read as a pattern, lies
    inside `D-p`, except in the two cells of `RExc`. -/
theorem restrictConcI_inside {sc g' : AFact} {p : PFact} (h : restrictConcI sc p = some g') :
    insideLocB g'.fact p = true ∨ RExc sc p g' := by
  obtain ⟨hbp, ⟨hq, h1⟩ | ⟨x, r, hq, ha, h2⟩ | ⟨r, _, _, hk, h3⟩ | ⟨r, e, _, _, hk, _, h4⟩⟩ :=
    restrictConcI_cases h
  · -- at `D-p`: the meet
    subst h1
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hq
    subst hbp hq
    cases k with
    | exact =>
      left
      unfold insideLocB coversB
      dsimp only
      rw [Nat.beq_refl, dropPrefix_self']
      cases pk <;> rfl
    | star e =>
      right; right
      exact ⟨⟨e, rfl⟩, by cases pk <;> rfl⟩
    | any =>
      cases pk with
      | exact =>
        left
        unfold insideLocB coversB
        dsimp only
        rw [Nat.beq_refl, dropPrefix_self']
        rfl
      | any =>
        left
        unfold insideLocB coversB
        dsimp only
        rw [Nat.beq_refl, dropPrefix_self']
        rfl
      | star E =>
        right; left
        exact ⟨rfl, ⟨E, rfl⟩, rfl, rfl⟩
  · -- below `D-p`: the edge, and the tail of `D-p` admits the step
    rw [h2]
    left
    have hb : Nat.beq p.base sc.fact.base = true := by rw [hbp]; exact Nat.beq_refl _
    unfold insideLocB coversB
    dsimp only
    rw [hb, hq, Store.dropPrefix_append]
    exact ha
  · -- above `D-p`, an `[any]` conclusion: the chain of `D-p`
    subst h3
    obtain ⟨⟨b, q, k, m⟩, dm⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hk
    subst hbp hk
    cases pk with
    | exact =>
      left
      unfold insideLocB coversB
      dsimp only
      rw [Nat.beq_refl, dropPrefix_self']
      rfl
    | any =>
      left
      unfold insideLocB coversB
      dsimp only
      rw [Nat.beq_refl, dropPrefix_self']
      rfl
    | star E =>
      right; left
      exact ⟨rfl, ⟨E, rfl⟩, rfl, rfl⟩
  · -- above `D-p`, a `*` conclusion: the edge
    exact Or.inr (Or.inr ⟨⟨e, hk⟩, h4⟩)

/-- The narrowing of one restriction: the premise lies inside `D-c`, and the result conclusion
    lies inside `D-p` (except `RExc`). -/
theorem restrictI_narrow {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictI j g d = some g') :
    ∃ p, d.dout = some p ∧ insideLocB j d.din = true ∧
      (insideLocB g'.fact p = true ∨ RExc g p g') := by
  obtain ⟨p, hdo, hin, hc⟩ := restrictI_some h
  exact ⟨p, hdo, hin, restrictConcI_inside hc⟩

#print axioms restrictConcI_inside
#print axioms restrictI_narrow

/-- R5. THE NARROWING THEOREM (forward to backward). Every demand edge `d'` that a restricted run
    (publication `pubR dem`) hands off comes from a demand edge `d` of `dem` that published it,
    and lies inside the reversal of `d`: the exit pattern of `d'` (the premise `j`) lies inside
    the entry pattern of `d`, and the entry pattern of `d'` (the piece `g'`) lies inside the exit
    pattern `p` of `d`, except in the two cells of `RExc`. So the search space only shrinks. -/
theorem handF_narrow {P : Program} {R : Obj → Prop} {dem : MethodId → DemandEdge → Prop}
    {m : MethodId} {d' : DemandEdge} (h : handF P R (pubR dem) m d') :
    ∃ j g g' d p, R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ ¬ Cross j g ∧
      dem m d ∧ d.dout = some p ∧ restrictI j g d = some g' ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideLocB j d.din = true ∧ (insideLocB g'.fact p = true ∨ RExc g p g') := by
  obtain ⟨j, g, g', hi, he, hnc, ⟨d, hdem, hres⟩, rfl⟩ := h
  obtain ⟨p, hdo, hin, hcon⟩ := restrictI_narrow hres
  exact ⟨j, g, g', d, p, hi, he, hnc, hdem, hdo, hres, rfl, hin, hcon⟩

/-- R5, the location form: the exit locations of `d'` are entry locations of `d`, and the entry
    locations of `d'` are exit locations of `d` (except `RExc`). -/
theorem handF_narrow_loc {P : Program} {R : Obj → Prop} {dem : MethodId → DemandEdge → Prop}
    {m : MethodId} {d' : DemandEdge} (h : handF P R (pubR dem) m d') :
    ∃ j g g' d p, dem m d ∧ d.dout = some p ∧ d' = ⟨g'.fact, some j⟩ ∧
      (∀ l, j.coversLoc l → d.din.coversLoc l) ∧
      ((∀ l, g'.fact.coversLoc l → p.coversLoc l) ∨ RExc g p g') := by
  obtain ⟨j, g, g', d, p, _, _, _, hdem, hdo, _, hd', hin, hcon⟩ := handF_narrow h
  refine ⟨j, g, g', d, p, hdem, hdo, hd', fun l hl => insideLoc_coversLoc hin hl, ?_⟩
  rcases hcon with hc | hc
  · exact Or.inl (fun l hl => insideLoc_coversLoc hc hl)
  · exact Or.inr hc

/-- R5 (backward to forward). The same for the backward hand-off `demOfN` with the publication
    `pubR demB` of a restricted backward run: case 3 lies inside the reversal of the backward
    demand edge that published it. Cases 1 and 2 are the zero demand and the zero-premise edges
    (their localization is later, decision F70 item 5). -/
theorem demOfN_narrow {Pb : Program} {R : Obj → Prop} {demB : MethodId → DemandEdge → Prop}
    {M : MethodId} {d' : DemandEdge} (h : demOfN Pb R (pubR demB) M d') :
    d' = ⟨zeroFact, none⟩ ∨ (∃ g, R (.edge M zeroFact (Pb.exit M) g) ∧ d' = ⟨g.fact, none⟩) ∨
    ∃ jb gb gb' d p, R (.init M jb) ∧ jb ≠ zeroFact ∧ R (.edge M jb (Pb.exit M) gb) ∧
      ¬ CrossB jb gb ∧
      demB M d ∧ d.dout = some p ∧ restrictI jb gb d = some gb' ∧ d' = ⟨gb'.fact, some jb⟩ ∧
      insideLocB jb d.din = true ∧ (insideLocB gb'.fact p = true ∨ RExc gb p gb') := by
  rcases h with h1 | h2 | ⟨jb, gb, gb', hi, hz, he, hnc, ⟨d, hdem, hres⟩, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨p, hdo, hin, hcon⟩ := restrictI_narrow hres
    exact Or.inr (Or.inr ⟨jb, gb, gb', d, p, hi, hz, he, hnc, hdem, hdo, hres, rfl, hin, hcon⟩)

#print axioms handF_narrow
#print axioms handF_narrow_loc
#print axioms demOfN_narrow

/-- In a restricted forward run with the mark-copying emission `emitM`, no exit edge has a `*`
    conclusion (every final fact has a concrete mark, and W2 gives a `*` tail only to an abstract
    mark). So only the `[any]` exception of the narrowing remains. -/
theorem DR_exit_not_star {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR P counted L demand emitM sat restrict recs sinks roots (.edge M i n f)) :
    ∀ e, f.fact.kind ≠ .star e := by
  intro e hk
  have hc := RExact.DR_concrete RCore.emitM_copies h
  obtain ⟨_, t, ht⟩ := hc
  have hab := (RExact.final_star_legalR P counted L demand emitM sat restrict recs sinks roots h
    hk).1
  exact Invariant.AbsMark.not_conc hab t ht

/-- R5 for a restricted forward run with `emitM` (the run of the spec): only the `[any]` exception
    remains. -/
theorem handF_narrow_DR {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {m : MethodId} {d' : DemandEdge}
    (h : handF P (DR P counted L demand emitM sat restrict recs sinks roots) (pubR dem) m d') :
    ∃ j g g' d p, DR P counted L demand emitM sat restrict recs sinks roots (.init m j) ∧
      dem m d ∧ d.dout = some p ∧ restrictI j g d = some g' ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideLocB j d.din = true ∧
      (insideLocB g'.fact p = true ∨
       (g.fact.kind = .any ∧ (∃ E, p.kind = .star E) ∧
         g'.fact = ⟨g.fact.base, p.path, .any, g.fact.mark⟩ ∧ g'.demand = g.demand)) := by
  obtain ⟨j, g, g', d, p, hi, he, _, hdem, hdo, hres, hd', hin, hcon⟩ := handF_narrow h
  refine ⟨j, g, g', d, p, hi, hdem, hdo, hres, hd', hin, ?_⟩
  rcases hcon with hc | hc | ⟨⟨e, hk⟩, _⟩
  · exact Or.inl hc
  · exact Or.inr hc
  · exact absurd hk (DR_exit_not_star he e)

#print axioms DR_exit_not_star
#print axioms handF_narrow_DR

/-! ### When the narrowing is exact

  The `[any]` exception needs an exit pattern `D-p` with a `*` tail, and the `*` exception needs a
  `*` conclusion. A restricted run with `emitM` has no `*` conclusion and no `*` added fact (it is
  concrete, and W2 gives a `*` tail only to an abstract mark), so its premises have a `*` tail only
  if a demand pattern has one. Run 1 is not concrete: its conclusions can have `*` tails, so the
  first hand-offs can carry `*` patterns. When the demand of a restricted forward run has no `*`
  pattern, its hand-off has no `*` pattern and the narrowing is exact. -/

/-- A tail with no `*`. -/
def NoStarK (k : Kind) : Prop := ∀ E, k ≠ .star E

/-- The emission of a fact with no `*` tail, by a pattern with no `*` tail, has no `*` tail. -/
theorem emitM_nonstar {d a j : PFact} (h : emitM d a = some j) (hd : NoStarK d.kind)
    (ha : NoStarK a.kind) : NoStarK j.kind := by
  intro E hE
  obtain ⟨_, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩⟩ := RCore.emitM_cases h
  · subst h1
    dsimp only at hE
    cases hak : a.kind with
    | star e => exact ha e hak
    | any =>
      rw [hak] at hE
      cases hdk : d.kind with
      | star e => exact hd e hdk
      | any => rw [hdk] at hE; cases hE
      | exact => rw [hdk] at hE; cases hE
    | exact =>
      rw [hak] at hE
      cases hdk : d.kind with
      | star e => exact hd e hdk
      | any => rw [hdk] at hE; cases hE
      | exact => rw [hdk] at hE; cases hE
  · subst h2
    exact ha E hE
  · subst h3
    exact hd E hE

#print axioms emitM_nonstar

/-- The motive: initial facts and added facts with no `*` tail. -/
def NoStarObj : Obj → Prop
  | .init _ j  => NoStarK j.kind
  | .added _ a => NoStarK a.kind
  | _          => True

/-- In a restricted run with `emitM` whose demand entry patterns have no `*` tail, no initial fact
    and no added fact has a `*` tail. -/
theorem DR_nonstar {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hdin : ∀ m d, dem m d → NoStarK d.din.kind) {o : Obj}
    (h : DR P counted L dem emitM sat restrict recs sinks roots o) : NoStarObj o := by
  induction h with
  | root _ => intro E hE; cases hE
  | @added M i n f n' c e a hf _ _ ha _ =>
    intro E hE
    obtain ⟨_, t, ht⟩ := RExact.DR_concrete RCore.emitM_copies hf
    obtain ⟨t', ht'⟩ := applyEdge_mark_conc ht ha
    exact Invariant.AbsMark.not_conc ((Invariant.applyEdge_Legal ha) E hE).1 t' ht'
  | @initR m a d j _ hdem hemit ih => exact emitM_nonstar hemit (hdin m d hdem) ih
  | answer hreq _ _ _ _ _ =>
    exact absurd hreq (RCov.no_reqR _ _ _ _ _ _ _ _ _ _ RCov.emitM_copies)
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | reqStmt _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | retRec _ _ _ _ _ _ _ _ _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | clean _ _ _ _ => trivial
  | reqClean _ _ _ _ => trivial
  | filt _ _ _ _ => trivial

#print axioms DR_nonstar

/-- The result of `restrictConcI` on a conclusion with no `*` tail has no `*` tail. -/
theorem restrictConcI_nonstar {sc g' : AFact} {p : PFact} (h : restrictConcI sc p = some g')
    (hk : NoStarK sc.fact.kind) : NoStarK g'.fact.kind := by
  intro E hE
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, h3⟩ | ⟨_, e, _, _, he, _, _⟩⟩ :=
    restrictConcI_cases h
  · subst h1
    dsimp only at hE
    cases hsk : sc.fact.kind with
    | star e => exact hk e hsk
    | any =>
      rw [hsk] at hE
      cases hpk : p.kind with
      | exact => rw [hpk] at hE; cases hE
      | any => rw [hpk] at hE; cases hE
      | star e => rw [hpk] at hE; cases hE
    | exact =>
      rw [hsk] at hE
      cases hpk : p.kind with
      | exact => rw [hpk] at hE; cases hE
      | any => rw [hpk] at hE; cases hE
      | star e => rw [hpk] at hE; cases hE
  · subst h2
    exact hk E hE
  · subst h3
    dsimp only at hE
    cases hpk : p.kind with
    | exact => rw [hpk] at hE; cases hE
    | any => rw [hpk] at hE; cases hE
    | star e => rw [hpk] at hE; cases hE
  · exact hk e he

#print axioms restrictConcI_nonstar

/-- A restricted forward run with `emitM` whose demand entry patterns have no `*` tail hands off
    demand edges with no `*` pattern (both `D-c` and `D-p`). So the backward restriction of the
    next run never meets the `[any]` exception at these exit patterns. -/
theorem handF_DR_nonstar {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hdin : ∀ m d, dem m d → NoStarK d.din.kind) {m : MethodId} {d' : DemandEdge}
    (h : handF P (DR P counted L dem emitM sat restrict recs sinks roots) (pubR dem) m d') :
    NoStarK d'.din.kind ∧ ∀ jp, d'.dout = some jp → NoStarK jp.kind := by
  obtain ⟨j, g, g', hi, he, _, ⟨d, _, hres⟩, rfl⟩ := h
  obtain ⟨p, _, _, hc⟩ := restrictI_some hres
  refine ⟨restrictConcI_nonstar hc (DR_exit_not_star he), ?_⟩
  intro jp hjp
  have hj : j = jp := Option.some.inj hjp
  rw [← hj]
  exact DR_nonstar hdin hi

/-- THE EXACT NARROWING: for a restricted forward run with `emitM` whose demand exit patterns have
    no `*` tail, every handed-off demand edge lies inside the reversal of the demand edge that
    published it, with no exception. -/
theorem handF_narrow_DR_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand dem : MethodId → DemandEdge → Prop} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact} {recs : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hdout : ∀ m d p, dem m d → d.dout = some p → NoStarK p.kind)
    {m : MethodId} {d' : DemandEdge}
    (h : handF P (DR P counted L demand emitM sat restrict recs sinks roots) (pubR dem) m d') :
    ∃ (j : PFact) (g' : AFact) (d : DemandEdge) (p : PFact), dem m d ∧ d.dout = some p ∧
      d' = ⟨g'.fact, some j⟩ ∧ insideLocB j d.din = true ∧ insideLocB g'.fact p = true := by
  obtain ⟨j, g, g', d, p, _, hdem, hdo, _, hd', hin, hcon⟩ := handF_narrow_DR h
  refine ⟨j, g', d, p, hdem, hdo, hd', hin, ?_⟩
  rcases hcon with hc | ⟨_, ⟨E, hE⟩, _, _⟩
  · exact hc
  · exact absurd hE (hdout m d p hdem hdo E)

#print axioms handF_DR_nonstar
#print axioms handF_narrow_DR_exact

/-! ## 7. R6: vectors (namespace `RVec`) -/

namespace RVec

/-! ### The §6.4 example and the two contrasts with `restrictU` -/

/-- The §6.4 example: the edge `(x,.,$) → (y,.,[any])` and the demand edge with `D-p = (y,.,$)`.
    The intersection gives `(y,.,$)`; `restrictU` keeps the whole `[any]` conclusion. -/
def vJ : PFact := ⟨1, [], .exact, .conc 1⟩
def vG : AFact := ⟨⟨2, [], .any, .conc 1⟩, false⟩
def vD : DemandEdge := ⟨⟨1, [], .exact, .star⟩, some ⟨2, [], .exact, .star⟩⟩

theorem v64_restrictI : restrictI vJ vG vD = some ⟨⟨2, [], .exact, .conc 1⟩, false⟩ := by decide
theorem v64_restrictU : restrictU vJ vG vD = some vG := by decide

/-- A premise that only OVERLAPS `D-c`: the premise `(x,.,[any])` and `D-c = (x,.f,$)`. The
    intersection gives nothing; `restrictU` gives a result. -/
def vJo : PFact := ⟨1, [], .any, .conc 1⟩
def vDo : DemandEdge := ⟨⟨1, [5], .exact, .star⟩, some ⟨2, [], .any, .star⟩⟩

theorem vOverlap_overlapB : overlapB vJo vDo.din = true := by decide
theorem vOverlap_inside : insideLocB vJo vDo.din = false := by decide
theorem vOverlap_restrictI : restrictI vJo vG vDo = none := by decide
theorem vOverlap_restrictU : restrictU vJo vG vDo = some vG := by decide

/-- No exit pattern: no result. -/
theorem vNoExit : restrictI vJ vG ⟨⟨1, [], .exact, .star⟩, none⟩ = none := by decide

#print axioms v64_restrictI
#print axioms v64_restrictU
#print axioms vOverlap_overlapB
#print axioms vOverlap_inside
#print axioms vOverlap_restrictI
#print axioms vOverlap_restrictU
#print axioms vNoExit

/-! ### Every row of `restrictConcI`

  The conclusions have the base `2`, the mark `1` (`[any]`, `$`) or `*` (`*`); the exit patterns
  have the mark `*` (marks are ignored). -/

def cA (q : List Acc) : AFact := ⟨⟨2, q, .any, .conc 1⟩, true⟩
def cE (q : List Acc) : AFact := ⟨⟨2, q, .exact, .conc 1⟩, false⟩
def cS (q : List Acc) (e : Excl) : AFact := ⟨⟨2, q, .star e, .star⟩, false⟩
def pE (q : List Acc) : PFact := ⟨2, q, .exact, .star⟩
def pA (q : List Acc) : PFact := ⟨2, q, .any, .star⟩
def pS (q : List Acc) (e : Excl) : PFact := ⟨2, q, .star e, .star⟩

/-- Row 0: another base gives nothing. -/
theorem row_base : restrictConcI (cA [1]) ⟨3, [1], .any, .star⟩ = none := by decide

/-- Row 1: AT `D-p`, the meet `meetConcK` (nine cells). Only `[any] ∩ $` narrows. -/
theorem row_at_any_exact : restrictConcI (cA [1]) (pE [1]) = some ⟨⟨2, [1], .exact, .conc 1⟩, true⟩ :=
  by decide
theorem row_at_any_any : restrictConcI (cA [1]) (pA [1]) = some (cA [1]) := by decide
theorem row_at_any_star : restrictConcI (cA [1]) (pS [1] (.set [7])) = some (cA [1]) := by decide
theorem row_at_exact_exact : restrictConcI (cE [1]) (pE [1]) = some (cE [1]) := by decide
theorem row_at_exact_any : restrictConcI (cE [1]) (pA [1]) = some (cE [1]) := by decide
theorem row_at_exact_star : restrictConcI (cE [1]) (pS [1] (.set [7])) = some (cE [1]) := by decide
theorem row_at_star_exact : restrictConcI (cS [1] (.set [3])) (pE [1]) = some (cS [1] (.set [3])) :=
  by decide
theorem row_at_star_any : restrictConcI (cS [1] (.set [3])) (pA [1]) = some (cS [1] (.set [3])) :=
  by decide
theorem row_at_star_star :
    restrictConcI (cS [1] (.set [3])) (pS [1] (.set [7])) = some (cS [1] (.set [3])) := by decide

/-- Row 2: BELOW `D-p`, the tail of `D-p` admits the step: the edge stays (every conclusion
    kind). -/
theorem row_below_any : restrictConcI (cA [1, 4]) (pA [1]) = some (cA [1, 4]) := by decide
theorem row_below_star_adm : restrictConcI (cE [1, 4]) (pS [1] (.set [5])) = some (cE [1, 4]) := by
  decide
theorem row_below_starc : restrictConcI (cS [1, 4] Excl.empty) (pA [1]) =
    some (cS [1, 4] Excl.empty) := by decide

/-- Row 3: BELOW `D-p`, the tail of `D-p` does not admit the step: nothing. -/
theorem row_below_exact : restrictConcI (cA [1, 4]) (pE [1]) = none := by decide
theorem row_below_star_excl : restrictConcI (cA [1, 4]) (pS [1] (.set [4])) = none := by decide

/-- Row 4: ABOVE `D-p`, an `[any]` conclusion: the chain of `D-p`, with `$` for a `$` exit
    pattern and `[any]` otherwise. -/
theorem row_above_any_exact : restrictConcI (cA [1]) (pE [1, 4]) =
    some ⟨⟨2, [1, 4], .exact, .conc 1⟩, true⟩ := by decide
theorem row_above_any_any : restrictConcI (cA [1]) (pA [1, 4]) = some (cA [1, 4]) := by decide
theorem row_above_any_star : restrictConcI (cA [1]) (pS [1, 4] (.set [7])) = some (cA [1, 4]) := by
  decide

/-- Row 5: ABOVE `D-p`, a `*` conclusion: the edge if its exclusion admits the step, else
    nothing. -/
theorem row_above_star_adm : restrictConcI (cS [1] Excl.empty) (pE [1, 4]) =
    some (cS [1] Excl.empty) := by decide
theorem row_above_star_excl : restrictConcI (cS [1] (.set [4])) (pE [1, 4]) = none := by decide

/-- Row 6: ABOVE `D-p`, a `$` conclusion: nothing. -/
theorem row_above_exact : restrictConcI (cE [1]) (pA [1, 4]) = none := by decide

/-- Row 7: APART: nothing. -/
theorem row_apart : restrictConcI (cA [1]) (pA [2]) = none := by decide

#print axioms row_base
#print axioms row_at_any_exact
#print axioms row_at_any_any
#print axioms row_at_any_star
#print axioms row_at_exact_exact
#print axioms row_at_exact_any
#print axioms row_at_exact_star
#print axioms row_at_star_exact
#print axioms row_at_star_any
#print axioms row_at_star_star
#print axioms row_below_any
#print axioms row_below_star_adm
#print axioms row_below_starc
#print axioms row_below_exact
#print axioms row_below_star_excl
#print axioms row_above_any_exact
#print axioms row_above_any_any
#print axioms row_above_any_star
#print axioms row_above_star_adm
#print axioms row_above_star_excl
#print axioms row_above_exact
#print axioms row_apart

end RVec

/-- So the contract of the earlier restrictions (`RestrictContract`: the entry location only in
    `D-c`) is FALSE for the intersection: the overlap-only premise has a demanded pair and no
    result. The coverage proof of a restricted run with `restrictI` therefore needs the premise
    inside `D-c` (`restrictI_contract`), and `emitM` gives it (`emitM_inside`); `RCov.coverageR`
    does not apply as it is. -/
theorem restrictI_not_RestrictContract : ¬ RestrictContract restrictI := by
  intro h
  have hden : den RVec.vJo RVec.vG.fact ⟨1, [5], 1⟩ ⟨2, [], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [5], [], rfl, rfl, trivial, trivial⟩
  have hdin : RVec.vDo.din.coversLoc ⟨1, [5], 1⟩ := ⟨rfl, [], rfl, rfl⟩
  have hp : (⟨2, [], .any, .star⟩ : PFact).coversLoc ⟨2, [], 1⟩ := ⟨rfl, [], rfl, trivial⟩
  obtain ⟨g', hg', _, _⟩ := h RVec.vJo RVec.vG RVec.vDo _ _ _ hden hdin rfl hp
  rw [RVec.vOverlap_restrictI] at hg'
  cases hg'

#print axioms restrictI_not_RestrictContract

end ApSpec.Handoff
