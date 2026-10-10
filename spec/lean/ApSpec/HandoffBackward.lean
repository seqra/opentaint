/-
  ApSpec.HandoffBackward — the backward run of the hand-off of the DEMAND EDGES only (decision
  F70) satisfies the backward contract `BackwardContractN`.

  The backward run is the closure `Backward.DB` on the reversed program, with the spec rules
  `emitM`, `satI` and the INTERSECTION restriction `restrictI`:
    `DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true`.
  Its demand `demB` contains the forward hand-off `handF P Rk pub` (the published pieces of the
  exit edges of the forward run `Rk` that are NOT crossable). Its records `recsB` contain the
  reversal `revRec x` of every crossable record `x` of `Rk` (a record that `Rk` read, or an exit
  edge of `Rk`). The next forward run gets the hand-off `demOfN` (only the pieces of the backward
  exit edges that are not `CrossB`: a demand-layer edge, or an edge whose reversal is not
  crossable) and a record set `rcnext` that contains the records of `Rk`, the crossable exit edges
  of `Rk`, and the reversals of the NORMAL backward exit edges with a crossable reversal (`CrossB`).
  A demand-layer backward summary is never a record (ap.md R1).

  The proof copies `Backward.seg_gen`, `reach_of_db_gen`, `demanded_gen` and `B_general`. At a call
  of a justified witness (`FlowRDN`) there are three cases:
    * a published piece `j → g'` of an exit edge `j → g` that is NOT crossable: the backward run
      enters the callee by the demand edge `(g', j)` of `handF`, the emitted premise lies inside
      `g'` with its mark (`emitM_insideB_B`: the requirement is concrete), and the exit location
      of the backward pair has its mark in `D-p = j` (the forward pair), so the mark-aware
      intersection restriction keeps the pair (`restrictI_contract_B`, F70). The demanded call of
      `FlowRR` gets the exit location with its mark in `D-p = jb` (`jb` covers it). After the
      callee, the backward summary `jb → gb` is NORMAL with a
      crossable reversal (`CrossB`, decided by its layer and `cross_em`: `crossB_em`) and it is a
      RECORDED call of `FlowRR` with the record `revRec (jb, gb)`, or its piece is handed off (a
      DEMANDED call of `FlowRR`, `demOfN` case 3);
    * a CROSSABLE exit edge `j → g`, or a crossable record of `rc`: the backward run crosses the
      call by the record `revRec (j, g)` (rule `retRec`; the requirement satisfies the reversed
      premise or the reversed premise is applicable to it, `cross_applies_B`); in `FlowRR` it is
      a RECORDED call with the record `(j, g)` itself.

  Agent R proves `emitM_inside`, `cross_applies` and `restrictI_contract` in
  `HandoffRestrict.lean` / `HandoffCoverage.lean`. This file has local copies under other names
  (`emitM_inside_B`, `emitM_insideB_B`, `concMarkB_of_den_B`, `cross_applies_B`,
  `restrictI_contract_B`), so it does not import them. They follow the mark-aware restriction of
  F71 (`insideB`, `concMarkB`).

  Main results:
    * `seg_genN`: the backward segment of a justified flow; the flow is demanded or recorded in the
      next forward run.
    * `reach_of_db_genN`, `demanded_genN`: the induction over the calls down; every justified
      witness of a seeded sink is demanded or recorded in the next forward run.
    * `B_generalN`: THE BACKWARD CONTRACT `BackwardContractN` of the backward run of the user's
      design, under the hypotheses of `Backward.B_general`.
    * `recsBOf`, `rcNextOf` (the canonical record sets, `recsBOf_spec`, `rcNextOf_spec`,
      `rcNextOf_cross`) and `B_generalN_canon`: the contract for the canonical backward run
      (demand `handF P Rk pub`, records `recsBOf`), for the join `HandoffMain.lean`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffDefs

namespace ApSpec.HandoffBackward
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff

/-! ## 0. Local copies of the lemmas of agent R -/

/-- The union keeps the exclusions of its right part. -/
theorem subB_union_left (e1 e2 : Excl) : e2.subB (e1.union e2) = true := by
  cases e1 with
  | univ => cases e2 <;> rfl
  | set xs =>
    cases e2 with
    | univ => rfl
    | set ys =>
      show ys.all (fun a => memB a (xs ++ ys)) = true
      refine List.all_eq_true.mpr (fun a ha => ?_)
      rw [Reverse.memB_append]
      rw [Reverse.memB_of_mem ha, Bool.or_true]

/-- The meet of two premise tails lies inside its right part. -/
theorem tailSub_meet_right (k d : Kind) : tailSubB d (meetK k d) = true := by
  cases k with
  | any => exact tailSubB_refl d
  | exact => cases d with
    | star e => rfl
    | any => rfl
    | exact => rfl
  | star e1 =>
    cases d with
    | any => rfl
    | exact => rfl
    | star e2 => exact subB_union_left e1 e2

#print axioms tailSub_meet_right

/-- `emitM_inside` (agent R), local copy: an emitted premise lies inside the entry pattern that
    emitted it (locations, marks ignored). -/
theorem emitM_inside_B {d a j : PFact} (h : emitM d a = some j) : insideLocB j d = true := by
  obtain ⟨hb, _, ⟨hq, h1⟩ | ⟨x, r, hq, hx, h2⟩ | ⟨r, _, _, _, _, h3⟩⟩ := RCore.emitM_cases h
  · subst h1
    have hbd : d.base = a.base := Nat.eq_of_beq_eq_true hb
    unfold insideLocB coversB
    simp only
    rw [hbd, Nat.beq_refl, hq, show dropPrefix d.path d.path = some [] by
      have := Store.dropPrefix_append d.path []; rwa [List.append_nil] at this]
    exact tailSub_meet_right _ _
  · subst h2
    have hbd : d.base = j.base := Nat.eq_of_beq_eq_true hb
    unfold insideLocB coversB
    simp only
    rw [hbd, Nat.beq_refl, hq, Store.dropPrefix_append]
    exact hx
  · subst h3
    unfold insideLocB coversB
    simp only
    rw [Nat.beq_refl, show dropPrefix d.path d.path = some [] by
      have := Store.dropPrefix_append d.path []; rwa [List.append_nil] at this]
    exact tailSubB_refl _

#print axioms emitM_inside_B

/-- A mark that admits the concrete mark `t` contains the concrete mark `t`. -/
theorem markSub_conc_of_admits {m : MarkA} {t : Mark} (h : m.admits t) :
    markSubB m (.conc t) = true := by
  cases m with
  | star => rfl
  | conc t' =>
    have e : t = t' := h
    subst e
    exact Nat.beq_refl t
  | starEx x =>
    have e : memB t x = false := h
    show (!memB t x) = true
    rw [e]
    rfl

/-- A fact covers the start location of each of its pairs (with the mark). -/
theorem den_covers_init {i f : PFact} {l0 l1 : Loc} (h : den i f l0 l1) : i.covers l0 := by
  obtain ⟨hb0, _, hm0, _, _, σ, _, hp0, _, hti, _⟩ := h
  exact ⟨hb0, ⟨σ, hp0, hti⟩, hm0⟩

/-- `cross_applies` (agent R), local copy: a crossable premise (`$`, or `*` with the Empty
    exclusion) is satisfied by, or applicable to, every concrete fact that covers one of its
    locations. -/
theorem cross_applies_B {j a : PFact} {l : Loc} (hk : CrossK j.kind) (hj : j.covers l)
    (ha : a.covers l) (hc : ∃ t, a.mark = .conc t) :
    satI j a = true ∨ applicable j a = true := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨hbj, ⟨σ, hpj, htj⟩, hmj⟩ := hj
  obtain ⟨hba, ⟨τ, hpa, hta⟩, hma⟩ := ha
  have hlt : l.mark = t := by rw [ht] at hma; exact hma
  have hms : markSubB j.mark a.mark = true := by
    rw [ht]
    rw [hlt] at hmj
    exact markSub_conc_of_admits hmj
  have hpath : j.path ++ σ = a.path ++ τ := by rw [← hpj, ← hpa]
  cases hjk : j.kind with
  | any => rw [hjk] at hk; exact hk.elim
  | exact =>
    -- `j` is one location: the fact `a` covers it, so `a` satisfies `j`
    rw [hjk] at htj
    have hσ : σ = [] := htj
    rw [hσ, List.append_nil] at hpath
    left
    unfold satI coversB
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨by rw [← hba, ← hbj]; exact Nat.beq_refl _, rfl⟩, ?_⟩, hms⟩
    simp only
    rw [hpath, Store.dropPrefix_append]
    cases τ with
    | nil =>
      rw [hjk]
      cases a.kind <;> rfl
    | cons x r => exact CoreAux.admitsTailB_iff.mpr hta
  | star e =>
    rw [hjk] at hk
    have he : e = Excl.empty := hk
    subst he
    rcases CoreAux.relate_common hpath with ⟨r, _, hq, _⟩ | ⟨r, _, hP, hr, hτ⟩
    · -- the fact is at or below the premise chain: the premise is applicable
      right
      unfold applicable coversB
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨⟨by rw [← hba, ← hbj]; exact Nat.beq_refl _, hms⟩, ?_⟩, by rw [hjk]; rfl⟩
      rw [hq, Store.dropPrefix_append, hjk]
      cases r with
      | nil => exact RCore.tailSubB_starEmpty a.kind
      | cons x r => exact Reverse.empty_admits (x :: r)
    · -- the fact is above the premise chain: it covers the premise, so it satisfies it
      left
      unfold satI coversB
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨⟨by rw [← hba, ← hbj]; exact Nat.beq_refl _, rfl⟩, ?_⟩, hms⟩
      simp only
      rw [hP, Store.dropPrefix_append]
      cases r with
      | nil => exact absurd rfl hr
      | cons x r' =>
        rw [hτ] at hta
        exact CoreAux.tailI_append_admits hta

#print axioms cross_applies_B
#print axioms subB_union_left
#print axioms markSub_conc_of_admits
#print axioms den_covers_init

/-- `emitM_insideB` (HandoffRestrict), local copy (F71, the mark-aware restriction): an emitted
    premise of a CONCRETE added fact lies inside its entry pattern in its locations AND its marks
    (`insideB`). On a concrete mark, the emission test `markMatchB` is `markSubB`. -/
theorem emitM_insideB_B {d a j : PFact} {t : Mark} (h : emitM d a = some j)
    (ha : a.mark = .conc t) : insideB j d = true := by
  have hm := RCore.emitM_mark h
  obtain ⟨_, hmm, _⟩ := RCore.emitM_cases h
  have hsub : markSubB d.mark j.mark = true := by
    rw [hm, ha]
    rw [ha] at hmm
    have he : markMatchB d.mark (.conc t) = markSubB d.mark (.conc t) := by
      cases d.mark <;> rfl
    rw [← he]
    exact hmm
  unfold insideB
  rw [emitM_inside_B h, hsub]
  rfl

#print axioms emitM_insideB_B

/-- `concMarkB_of_den` (HandoffRestrict), local copy: a pair of the edge whose exit location has a
    mark of `D-p` passes the mark test of the conclusion (every mark cell). -/
theorem concMarkB_of_den_B {j f p : PFact} {l1 l2 : Loc} (hd : den j f l1 l2)
    (hp : p.mark.admits l2.mark) : concMarkB p.mark f.mark = true := by
  obtain ⟨_, _, _, hm2, hps, _⟩ := hd
  cases hf : f.mark with
  | conc u =>
    rw [hf] at hm2
    have h2 : l2.mark = u := hm2
    cases hpm : p.mark with
    | star => rfl
    | conc t =>
      rw [hpm] at hp
      have h3 : l2.mark = t := hp
      show Nat.beq t u = true
      rw [← h3, ← h2]
      exact Nat.beq_refl _
    | starEx x =>
      rw [hpm] at hp
      have h3 : memB l2.mark x = false := hp
      rw [h2] at h3
      show (!(memB u x)) = true
      rw [h3]
      rfl
  | star => cases p.mark <;> rfl
  | starEx x =>
    rw [hf] at hm2 hps
    have h2 : l2.mark = l1.mark := hm2
    have h3 : memB l1.mark x = false := hps
    cases hpm : p.mark with
    | star => rfl
    | conc u =>
      rw [hpm] at hp
      have h4 : l2.mark = u := hp
      show (!(memB u x)) = true
      rw [← h4, h2, h3]
      rfl
    | starEx _ => rfl

#print axioms concMarkB_of_den_B

/-- `restrictI_contract` (HandoffRestrict), local copy, MARK-AWARE (F71): if the premise lies
    inside `D-c` in its locations and marks (`insideB`), the intersection restriction keeps every
    pair of the edge whose exit location (with its mark) `D-p` covers, in the same layer. Every
    cell of `restrictConcI`, also a `*` conclusion; the mark test by `concMarkB_of_den_B`. -/
theorem restrictI_contract_B {j : PFact} {g : AFact} {d : DemandEdge} {p : PFact} {l1 l2 : Loc}
    (hin : insideB j d.din = true) (hden : den j g.fact l1 l2) (hdout : d.dout = some p)
    (hp : p.covers l2) :
    ∃ g', restrictI j g d = some g' ∧ den j g'.fact l1 l2 ∧ g'.demand = g.demand := by
  have hR : restrictI j g d = restrictConcI g p := by
    unfold restrictI
    rw [hdout]
    dsimp only
    rw [hin, concMarkB_of_den_B hden hp.2.2]
    rfl
  rw [hR]
  have hden0 := hden
  obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf⟩ := hden
  obtain ⟨hbp, ⟨σ', hpp, htp⟩, _⟩ := hp
  have hb : Nat.beq g.fact.base p.base = true := by rw [← hb2, ← hbp]; exact Nat.beq_refl _
  have hpath : p.path ++ σ' = g.fact.path ++ τ := by rw [← hpp, ← hp2]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, hq, hσ⟩ | ⟨r, hrel, _, hr, hτ⟩
  · cases r with
    | nil =>
      -- the conclusion is at the exit pattern: the meet of the tails
      rw [List.nil_append] at hσ
      refine ⟨⟨⟨g.fact.base, g.fact.path, meetConcK g.fact.kind p.kind, g.fact.mark⟩, g.demand⟩,
        ?_, ?_, rfl⟩
      · unfold restrictConcI
        rw [if_pos hb, hrel]
      · refine ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, ?_⟩
        cases hgk : g.fact.kind with
        | any =>
          cases hpk : p.kind with
          | exact =>
            show τ = []
            rw [hpk] at htp
            rw [← hσ]
            exact htp
          | any => trivial
          | star e => trivial
        | exact => rw [hgk] at htf; exact htf
        | star e => rw [hgk] at htf; exact htf
    | cons x r =>
      -- the conclusion is below the exit pattern: keep the edge
      have ha : admitsTailB p.kind (x :: r) = true := by
        rw [hσ] at htp
        exact CoreAux.tailI_append_admits htp
      refine ⟨g, ?_, hden0, rfl⟩
      unfold restrictConcI
      rw [if_pos hb, hrel]
      show (if admitsTailB p.kind (x :: r) = true then _ else _) = _
      rw [if_pos ha]
  · -- the conclusion is above the exit pattern
    cases hk : g.fact.kind with
    | star e =>
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
      refine ⟨⟨⟨g.fact.base, p.path, RCore.outKind p.kind, g.fact.mark⟩, g.demand⟩, ?_, ?_, rfl⟩
      · unfold restrictConcI
        rw [if_pos hb, hrel, hk]
        dsimp only
        cases p.kind <;> rfl
      · refine ⟨hb1, hb2, hm1, hm2, hps, σ, σ', hp1, hpp, hti, ?_⟩
        cases hpk : p.kind with
        | exact =>
          rw [hpk] at htp
          exact htp
        | any => trivial
        | star e => trivial
    | exact =>
      rw [hk] at htf
      have hτ0 : τ = [] := htf
      rw [hτ0] at hτ
      cases r with
      | nil => exact absurd rfl hr
      | cons x r' => exact absurd hτ.symm (List.cons_ne_nil x (r' ++ σ'))

#print axioms restrictI_contract_B

/-! ## 1. Small lemmas -/

/-- `CrossK` is decidable (constructive case split). -/
theorem crossK_em (k : Kind) : CrossK k ∨ ¬ CrossK k := by
  cases k with
  | exact => exact Or.inl trivial
  | any => exact Or.inr id
  | star e =>
    cases decEq e Excl.empty with
    | isTrue h => exact Or.inl h
    | isFalse h => exact Or.inr h

/-- `MarkRev` is decidable (constructive case split). -/
theorem markRev_em (i f : PFact) : MarkRev i f ∨ ¬ MarkRev i f := by
  cases hf : f.mark with
  | star => exact Or.inl (markRev_star hf)
  | starEx x => exact Or.inl (markRev_starEx hf)
  | conc t =>
    cases hi : i.mark with
    | conc s => exact Or.inl (Or.inr ⟨s, hi⟩)
    | star =>
      refine Or.inr ?_
      rintro ((h | ⟨_, h⟩) | ⟨_, h⟩)
      · rw [hf] at h; cases h
      · rw [hf] at h; cases h
      · rw [hi] at h; cases h
    | starEx y =>
      refine Or.inr ?_
      rintro ((h | ⟨_, h⟩) | ⟨_, h⟩)
      · rw [hf] at h; cases h
      · rw [hf] at h; cases h
      · rw [hi] at h; cases h

/-- `Cross` is decidable (constructive case split). -/
theorem cross_em (j : PFact) (g : AFact) : Cross j g ∨ ¬ Cross j g := by
  have hd : g.demand = false ∨ ¬ g.demand = false := by
    cases g.demand with
    | false => exact Or.inl rfl
    | true => exact Or.inr Bool.noConfusion
  rcases hd with h1 | h1
  · rcases crossK_em j.kind with h2 | h2
    · rcases markRev_em j g.fact with h3 | h3
      · rcases crossK_em (revEdge j g.fact).1.kind with h4 | h4
        · exact Or.inl ⟨h1, h2, h3, h4⟩
        · exact Or.inr (fun h => h4 h.2.2.2)
      · exact Or.inr (fun h => h3 h.2.2.1)
    · exact Or.inr (fun h => h2 h.2.1)
  · exact Or.inr (fun h => h1 h.1)

#print axioms crossK_em
#print axioms markRev_em
#print axioms cross_em

/-- `CrossB` is decidable (the layer is a `Bool`, `Cross` by `cross_em`). -/
theorem crossB_em (jb : PFact) (gb : AFact) : CrossB jb gb ∨ ¬ CrossB jb gb := by
  cases hd : gb.demand with
  | true =>
    refine Or.inr (fun h => ?_)
    have h1 : gb.demand = false := h.1
    rw [hd] at h1
    exact Bool.noConfusion h1
  | false =>
    rcases cross_em (revRec (jb, gb)).1 (revRec (jb, gb)).2 with hc | hc
    · exact Or.inl ⟨hd, hc⟩
    · exact Or.inr (fun h => hc h.2)

#print axioms crossB_em

/-- A justified flow reaches its node along a CFG path from the entry. -/
theorem flowRDN_cfg {P : Program} {R : Obj → Prop} {pub : Pub} {rc : Recs} {M : MethodId}
    {l0 : Loc} {n : Node} {l : Loc} (h : FlowRDN P R pub rc M l0 n l) :
    CfgPath P M (P.entry M) n := by
  induction h with
  | start => exact CfgPath.refl
  | step _ he _ ih => exact CfgPath.step ih he
  | pass _ he _ ih => exact CfgPath.step ih he
  | call _ he _ _ _ _ _ _ _ _ _ _ ih _ => exact CfgPath.step ih he
  | rcall _ he _ _ _ _ _ _ _ _ ih => exact CfgPath.step ih he
  | clean _ he _ ih => exact CfgPath.step ih he
  | filt _ he _ ih => exact CfgPath.step ih he

/-- The node of a justified witness is reachable from the entry of its method. -/
theorem reachRDN_cfg {P : Program} {R : Obj → Prop} {pub : Pub} {rc : Recs}
    {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRDN P R pub rc roots M n l) : CfgPath P M (P.entry M) n := by
  cases h with
  | root _ hfl => exact flowRDN_cfg hfl
  | down _ _ _ _ _ _ hfl => exact flowRDN_cfg hfl

/-- The method of a justified witness is a method of the program. -/
theorem reachRDN_called {P : Program} {R : Obj → Prop} {pub : Pub} {rc : Recs}
    {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRDN P R pub rc roots M n l) : Called P roots M := by
  cases h with
  | root hM _ => exact Or.inl hM
  | @down M0 n0 _ n0' c _ _ _ _ _ _ hE _ _ _ _ _ => exact Or.inr ⟨M0, n0, c, n0', hE, rfl⟩

#print axioms flowRDN_cfg
#print axioms reachRDN_cfg
#print axioms reachRDN_called

/-! ## 2. The hypotheses on the records of the next forward run -/

/-- The record set `rcnext` of the next forward run (brief §2.3, `hrcN`): it contains the
    records that `Rk` read, the crossable exit edges of `Rk`, and the reversals of the NORMAL
    backward exit edges with a non-zero premise and a crossable reversal (`CrossB`) of the
    backward run `DBk`. A demand-layer backward exit edge is never a record (ap.md R1). -/
structure NextRecs (P : Program) (Rk : Obj → Prop) (rc : Recs) (DBk : Obj → Prop)
    (rcnext : Recs) : Prop where
  old : ∀ m x, rc m x → rcnext m x
  fwd : ∀ m j g, Rk (.init m j) → Rk (.edge m j (P.exit m) g) → Cross j g → rcnext m (j, g)
  back : ∀ m jb gb, DBk (.init m jb) → jb ≠ zeroFact →
    DBk (.edge m jb ((Program.rev P).exit m) gb) →
    CrossB jb gb → rcnext m (revRec (jb, gb))

section General
variable {P : Program} {Rk : Obj → Prop} {pub : Pub} {rc rcnext : Recs} {counted : Acc → Bool}
  {L : Nat} {demB : MethodId → DemandEdge → Prop} {recsB : MethodId → PFact × AFact → Prop}
  {sinksB : List (MethodId × Node × PFact)} {rootsB : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

local notation "DBr" =>
  DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB rootsB seeds zbind

/-! ## 3. The backward run crosses a call by a reversed crossable record -/

/-- THE RECORD CROSSING. A crossable record `j → g` of the callee that has the concrete pair
    `(l1, l2)`, with its reversal `revRec (j, g)` in the backward records: a concrete backward edge
    at the forward post-call node that covers `l3` gives a concrete legal backward edge at the
    forward pre-call node that covers `l` (rule `retRec`). The reversed requirement satisfies the
    reversed premise, or the reversed premise is applicable to it (`cross_applies_B`). -/
theorem cross_step (hW : P.WF) (hT : BindTargetsStar P)
    {M : MethodId} {n n' : Node} {c : Call} {e1 e2 : MicroEdge} {l l1 l2 l3 lX : Loc}
    {i : PFact} {f : AFact} {j : PFact} {g : AFact}
    (he : (M, n, Instr.call c, n') ∈ P.edges) (he1 : e1 ∈ c.toCallee) (hd1 : den e1.1 e1.2 l l1)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3)
    (hrec : recsB c.callee (revRec (j, g))) (hcr : Cross j g) (hdg : den j g.fact l1 l2)
    (h : DBr (.edge M i n' f)) (hd : den i f.fact lX l3) (hc : ∃ t, f.fact.mark = .conc t) :
    ∃ f', DBr (.edge M i n f') ∧ den i f'.fact lX l ∧ (∃ t, f'.fact.mark = .conc t) ∧
      Invariant.Legal f' := by
  obtain ⟨t, ht⟩ := hc
  have hEr : (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges := mem_rev_call he
  have hWr := rev_WF hW hT
  -- the reversed binding back takes the requirement into the callee's forward exit
  have her2 : revEdge e2.1 e2.2 ∈ (Call.rev c).toCallee := List.mem_map.mpr ⟨e2, he2, rfl⟩
  have hdr2 : den (revEdge e2.1 e2.2).1 (revEdge e2.1 e2.2).2 l3 l2 :=
    revEdge_sound (markRev_star ((hT M n c n' he).2 e2 he2)) hd2
  obtain ⟨a, ha, hda⟩ := Coverage.bind_in hWr hEr her2 hd hdr2
  obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
  -- the reversed record has the converse pair, and the requirement meets its premise
  have hdr : den (revRec (j, g)).1 (revRec (j, g)).2.fact l2 l1 := revEdge_sound hcr.2.2.1 hdg
  have happ := cross_applies_B hcr.2.2.2 (den_covers_init hdr) (den_covers_final hda) ⟨ta, hta⟩
  obtain ⟨r, hr, hdr'⟩ : ∃ r, r ∈ (applySummary a (revRec (j, g)).1 (revRec (j, g)).2).facts ∧
      den i r.fact lX l1 := by
    rcases happ with hs | hap
    · exact RCov.sat_step RCore.satI_contract hs hda hdr
    · exact Coverage.summary_step hap hda hdr
  -- the reversed binding into the callee, back to the caller
  have her1 : revEdge e1.1 e1.2 ∈ (Call.rev c).fromCallee := List.mem_map.mpr ⟨e1, he1, rfl⟩
  have hdr1 : den (revEdge e1.1 e1.2).1 (revEdge e1.1 e1.2).2 l1 l :=
    revEdge_sound (markRev_star ((hT M n c n' he).1 e1 he1)) hd1
  obtain ⟨r', hr', hdr''⟩ := Coverage.bind_out hWr hEr her1 hdr' hdr1
  have hret := DB.retRec (c := Call.rev c) h hEr her2 ha hrec happ hr her1 hr'
  obtain ⟨t1, h1⟩ := applySummary_mark_conc hta hr
  obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 hr'
  exact ⟨_, hret, limitF_sound hdr'', ⟨t2, by rw [limitF_mark]; exact h2⟩,
    Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')⟩

#print axioms cross_step

/-! ## 4. The backward segment of a justified flow -/

/-- BACKWARD SEGMENT COVERAGE FOR A JUSTIFIED FLOW (`Backward.seg_gen` with the new hand-off). A
    justified forward flow of `M` from the entry location `l0` to `(n, l)`, and a concrete legal
    backward edge of any premise `i` at `n` that covers `l`, give a concrete legal backward edge of
    `i` at the forward entry that covers `l0`; and the flow is demanded or recorded in the next
    forward run (its demand `demOfN`, its records `rcnext`). -/
theorem seg_genN (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowRDN P Rk pub rc M l0 n l) :
    ∀ i f lX, DBr (.edge M i n f) →
      den i f.fact lX l → (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      (∃ f', DBr (.edge M i (P.entry M) f') ∧ den i f'.fact lX l0 ∧
          (∃ t, f'.fact.mark = .conc t) ∧ Invariant.Legal f') ∧
      FlowRR P (demOfN (Program.rev P) DBr (pubR demB)) rcnext M l0 n l := by
  induction hfl with
  | start M l0 =>
    intro i f lX h hd hc hl
    exact ⟨⟨f, h, hd, hc, hl⟩, FlowRR.start M l0⟩
  | @step M l0 n1 l1 n' l' s _ he hst ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.stmt (Stmt.rev s), n1) ∈ (Program.rev P).edges := mem_rev_stmt he
    have hrs : (Stmt.rev s).step l' l1 := Stmt.rev_step_sound (hmr M n1 s n' he) hst
    obtain ⟨t, ht⟩ := hc
    rcases transfer_sound (counted := counted) (L := L) (rev_touched s) hd hrs with
      ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.step h hEr hr) hdr (transfer_mark_conc ht hr)
        (legal_transfer hl hr)
      exact ⟨res, FlowRR.step hfr he hst⟩
    · exact absurd ht (habs t)
  | @pass M l0 n1 l1 n' c _ he hb ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.call (Call.rev c), n1) ∈ (Program.rev P).edges := mem_rev_call he
    have hb' : memB f.fact.base (Call.rev c).touched = false := by
      show memB f.fact.base c.touched = false
      rw [← hd.2.1]
      exact hb
    obtain ⟨res, hfr⟩ := ih i f lX (DB.pass h hEr hb') hd hc hl
    exact ⟨res, FlowRR.pass hfr he hb⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 j g g' _ he he1 hd1 _ hj hg hpub hjc hdg he2 hd2 ih ihc =>
    intro i f lX h hd hc hl
    rcases cross_em j g with hcr | hncr
    · -- a crossable exit edge: the backward run crosses it by its reversal
      have hdgf : den j g.fact l1 l2 := hpubSub _ _ _ _ hpub _ _ hdg
      obtain ⟨f1, h1, hd1', hc1, hl1⟩ := cross_step hW hT he he1 hd1 he2 hd2
        (hrecB _ (j, g) (Or.inr ⟨hj, hg⟩) hcr) hcr hdgf h hd hc
      obtain ⟨res, hfr⟩ := ih i f1 lX h1 hd1' hc1 hl1
      exact ⟨res, FlowRR.rcall hfr he he1 hd1 (hrcN.fwd _ _ _ hj hg hcr) hcr hjc hdgf he2 hd2⟩
    · -- not crossable: the backward run enters the callee by the demand edge `(g', j)`
      obtain ⟨t, ht⟩ := hc
      have hEr : (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges := mem_rev_call he
      have hWr := rev_WF hW hT
      have her2 : revEdge e2.1 e2.2 ∈ (Call.rev c).toCallee := List.mem_map.mpr ⟨e2, he2, rfl⟩
      have hdr2 : den (revEdge e2.1 e2.2).1 (revEdge e2.1 e2.2).2 l3 l2 :=
        revEdge_sound (markRev_star ((hT M n c n' he).2 e2 he2)) hd2
      obtain ⟨a, ha, hda⟩ := Coverage.bind_in hWr hEr her2 hd hdr2
      have hadd : DBr (.added c.callee a.fact) := DB.added (c := Call.rev c) h hEr her2 ha
      obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
      have hdB : demB c.callee ⟨g'.fact, some j⟩ :=
        hdemB _ _ ⟨j, g, g', hj, hg, hncr, hpub, rfl⟩
      obtain ⟨jb, hemit, hjbc, hsat⟩ := RCore.emitM_contract_I g'.fact a.fact l2 ta hta
        (den_covers_final hdg) (den_covers_final hda)
      have hjb : DBr (.init c.callee jb) := DB.initR (m := c.callee) hadd hdB hemit
      have hjbm : jb.mark = .conc ta := by rw [RCov.emitM_copies _ _ _ hemit]; exact hta
      -- the reversed callee flow: from the backward premise at the forward exit to the entry
      obtain ⟨⟨gb, hgb, hdgb, _, _⟩, hfrc⟩ := ihc jb (startFact jb) l2 (DB.start hjb)
        (startFact_sound hjbc) ⟨ta, by rw [startFact_mark]; exact hjbm⟩
        (fun _ hk => Invariant.startFact_legal hk)
      -- the intersection restriction by the demand edge keeps the pair: the emitted premise
      -- lies inside `g'` with its mark, and the exit location `l1` of the backward pair has its
      -- mark in `D-p = j` (the forward pair: `j` covers `l1`; F71)
      obtain ⟨gb', hres, hdgb', _⟩ := restrictI_contract_B (d := ⟨g'.fact, some j⟩)
        (emitM_insideB_B hemit hta) hdgb rfl hjc
      -- the backward summary piece applied, and the reversed binding into the callee
      obtain ⟨r, hr, hdr⟩ := RCov.sat_step RCore.satI_contract hsat hda hdgb'
      have her1 : revEdge e1.1 e1.2 ∈ (Call.rev c).fromCallee := List.mem_map.mpr ⟨e1, he1, rfl⟩
      have hdr1 : den (revEdge e1.1 e1.2).1 (revEdge e1.1 e1.2).2 l1 l :=
        revEdge_sound (markRev_star ((hT M n c n' he).1 e1 he1)) hd1
      obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hWr hEr her1 hdr hdr1
      have hret := DB.ret (c := Call.rev c) h hEr her2 ha hjb hgb hdB hres hsat hr her1 hr'
      obtain ⟨t1, h1⟩ := applySummary_mark_conc hta hr
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 hr'
      obtain ⟨res, hfr⟩ := ih i _ lX hret (limitF_sound hdr') ⟨t2, by rw [limitF_mark]; exact h2⟩
        (Invariant.limitF_Legal (Invariant.applyEdge_Legal hr'))
      -- the backward premise is not the zero fact (no zero binding back)
      have hne : jb ≠ zeroFact := by
        intro hz
        have hb1 : l2.base = jb.base := hjbc.1
        have hb2 : l2.base = e2.1.base := hd2.1
        rw [hz] at hb1
        exact hNZB M n c n' he e2 he2 (hb2.symm.trans hb1)
      -- the layer of `gb` (a `Bool`) and `cross_em` decide `CrossB jb gb`
      rcases crossB_em jb gb with hcb | hncb
      · -- a normal backward summary with a crossable reversal: a RECORDED call of the next
        -- forward run
        have hrv : den (revRec (jb, gb)).1 (revRec (jb, gb)).2.fact l1 l2 :=
          revEdge_sound (Or.inr ⟨ta, hjbm⟩) hdgb
        exact ⟨res, FlowRR.rcall hfr he he1 hd1 (hrcN.back _ _ _ hjb hne hgb hcb) hcb.2
          (den_covers_init hrv) hrv he2 hd2⟩
      · -- a demand-layer backward summary, or a reversal that is not crossable: a DEMANDED
        -- call (`demOfN`, case 3)
        have hdem : demOfN (Program.rev P) DBr (pubR demB) c.callee ⟨gb'.fact, some jb⟩ :=
          Or.inr (Or.inr ⟨jb, gb, gb', hjb, hne, hgb, hncb, ⟨_, hdB, hres⟩, rfl⟩)
        exact ⟨res, FlowRR.call hfr he he1 hd1 hfrc hdem (den_covers_final hdgb') rfl
          hjbc he2 hd2⟩
  | @rcall M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 hrcj hcr hjc hdg he2 hd2 ih =>
    intro i f lX h hd hc hl
    -- a crossable record of `rc`: the backward run crosses it by its reversal
    obtain ⟨f1, h1, hd1', hc1, hl1⟩ := cross_step hW hT he he1 hd1 he2 hd2
      (hrecB _ (j, g) (Or.inl hrcj) hcr) hcr hdg h hd hc
    obtain ⟨res, hfr⟩ := ih i f1 lX h1 hd1' hc1 hl1
    exact ⟨res, FlowRR.rcall hfr he he1 hd1 (hrcN.old _ _ hrcj) hcr hjc hdg he2 hd2⟩
  | @clean M l0 n1 l1 n' cl _ he hcl ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.clean cl, n1) ∈ (Program.rev P).edges := mem_rev_clean he
    obtain ⟨t, ht⟩ := hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.clean h hEr hr) hdr (cleanRes_mark_conc ht hr)
        (Invariant.cleanRes_Legal hl hr)
      exact ⟨res, FlowRR.clean hfr he hcl⟩
    · exact absurd ht (habs t)
  | @filt M l0 n1 l1 n' b may _ he hmay ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.filt b may, n1) ∈ (Program.rev P).edges := mem_rev_filt he
    have hff : f.fact.base = b → may f.fact.path = true := by
      intro hfb
      obtain ⟨_, hb1, _, _, _, σ, τ, _, hp1, _, _⟩ := hd
      have hm := hmay (hb1.trans hfb)
      rw [hp1] at hm
      exact hW.filtPrefix _ _ _ _ _ he _ _ hm
    obtain ⟨res, hfr⟩ := ih i f lX (DB.filt h hEr hff) hd hc hl
    exact ⟨res, FlowRR.filt hfr he hmay⟩

#print axioms seg_genN

/-! ## 5. The zero fact reaches every node of a justified witness -/

/-- Every method of a justified witness has the zero premise in the backward run
    (`Backward.zero_init` for `ReachRDN`). -/
theorem zero_initN (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRDN P Rk pub rc roots M n l) :
    DBr (.init M zeroFact) := by
  induction hRe with
  | root hM _ => exact DB.root (hroots _ hM)
  | @down M n l n' c e l1 n2 l2 j hRe0 hE _ _ _ _ _ ih =>
    have hz := zero_path (counted := counted) (L := L) (demand := demB) (emit := emitM)
      (sat := satI) (restrict := restrictI) (recs := recsB) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ
      (hX M n' (reachRDN_called hRe0) (CfgPath.step (reachRDN_cfg hRe0) hE)) (zero_exit ih)
    exact DB.zin (c := Call.rev c) hzb hz (mem_rev_call hE)

#print axioms zero_initN

/-- The zero fact is at every node of a justified witness. -/
theorem zero_atN (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRDN P Rk pub rc roots M n l) :
    DBr (.edge M zeroFact n zeroAF) :=
  zero_path hZ (hX M n (reachRDN_called hRe) (reachRDN_cfg hRe))
    (zero_exit (zero_initN hZ hX hzb hroots hRe))

#print axioms zero_atN

/-! ## 6. The induction over the calls down -/

/-- The induction over the calls down (`Backward.reach_of_db_gen` with the new hand-off): a
    concrete legal zero-premise backward edge at `(M, n)` that covers the end location of a
    justified witness gives the witness demanded or recorded in the next forward run. -/
theorem reach_of_db_genN (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRDN P Rk pub rc roots M n l) :
    ∀ f, DBr (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l →
      (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      ReachRR P (demOfN (Program.rev P) DBr (pubR demB)) rcnext roots M n l := by
  induction hRe with
  | root hM hfl =>
    intro f h hd hc hl
    exact ReachRR.root hM
      (seg_genN hW hT hmr hNZB hdemB hrecB hpubSub hrcN hfl zeroFact f zeroLoc h hd hc hl).2
  | @down M n l n' c e l1 n2 l2 j hRe0 hE he hd1 _ _ hfl ih =>
    intro f h hd hc hl
    obtain ⟨⟨f', h', hd', hc', _⟩, hfr⟩ :=
      seg_genN hW hT hmr hNZB hdemB hrecB hpubSub hrcN hfl zeroFact f zeroLoc h hd hc hl
    have hz := zero_path (counted := counted) (L := L) (demand := demB) (emit := emitM)
      (sat := satI) (restrict := restrictI) (recs := recsB) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ
      (hX M n' (reachRDN_called hRe0) (CfgPath.step (reachRDN_cfg hRe0) hE))
      (zero_exit (zero_initN hZ hX hzb hroots hRe0))
    obtain ⟨g, hg, hdg, hcg, hlg⟩ := zret_descent hW hT hzb hE he hd1 hz h' hd' hc'
    have hdem : demOfN (Program.rev P) DBr (pubR demB) c.callee ⟨f'.fact, none⟩ :=
      Or.inr (Or.inl ⟨f', h', rfl⟩)
    exact ReachRR.down (ih g hg hdg hcg hlg) hE he hd1 hdem (den_covers_final hd') hfr

#print axioms reach_of_db_genN

/-- Every justified witness whose sink is seeded is demanded or recorded in the next forward
    run (`Backward.demanded_gen` with the new hand-off). -/
theorem demanded_genN (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc DBr rcnext)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachRDN P Rk pub rc roots M n l) (hseed : (M, n, s) ∈ seeds)
    (hT' : s.mark = .conc T) (hk : s.kind = .exact ∨ s.kind = .any) (hsc : s.covers l) :
    ReachRR P (demOfN (Program.rev P) DBr (pubR demB)) rcnext roots M n l :=
  reach_of_db_genN hW hT hmr hNZB hZ hX hzb hroots hdemB hrecB hpubSub hrcN hRe _
    (DB.seed hseed (zero_atN hZ hX hzb hroots hRe))
    (limitF_sound (seed_den hT' hk hsc)) ⟨T, by rw [limitF_mark]; exact hT'⟩ (legal_seed hk)

#print axioms demanded_genN

end General

/-! ## 7. The backward contract -/

/-- THE BACKWARD CONTRACT OF THE NEW HAND-OFF (`Backward.B_general` with `handF`, `demOfN`,
    `restrictI` and the records). The backward run of the user's design
    `DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true`, whose
    demand contains the forward hand-off `handF P Rk pub` and whose records contain the reversed
    crossable records, satisfies `BackwardContractN` for the next forward run with the demand
    `demOfN … (pubR demB)` and every record set `rcnext` that contains the records of `Rk`, the
    crossable exit edges of `Rk` and the reversed `CrossB` backward exit edges. Program
    hypotheses: well-formed, mark-agnostic binding targets, mark-reversible statements, no zero
    binding back, the zero kept by every instruction, every node of a method reaches its exit;
    the sinks have the tail `$` or `[any]`. The publication `pub` only removes pairs
    (`hpubSub`). -/
theorem B_generalN {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {pub : Pub} {rc rcnext : Recs} {seeds : List (MethodId × Node × PFact)}
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    (hdemB : ∀ m d, handF P Rk pub m d → demB m d)
    (hrecB : ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsB m (revRec x))
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2)
    (hrcN : NextRecs P Rk rc
      (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true) rcnext) :
    BackwardContractN P roots sinks seeds Rk pub rc
      (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB roots seeds true)
        (pubR demB))
      rcnext := by
  intro M n l s T hs hT' hsc hRR hseed
  exact demanded_genN hW hT hmr hNZB hZ hX rfl (fun _ h => h) hdemB hrecB hpubSub hrcN hRR hseed
    hT' (hk M n s hs) hsc

#print axioms B_generalN

/-! ## 8. The canonical record sets and the canonical backward run -/

/-- The canonical backward records: the reversals `revRec x` of the crossable records `x` of the
    forward run `Rk` (a record that `Rk` read, or an exit edge of `Rk`). -/
def recsBOf (P : Program) (Rk : Obj → Prop) (rc : Recs) : Recs :=
  fun m y => ∃ x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) ∧
    Cross x.1 x.2 ∧ y = revRec x

theorem recsBOf_spec {P : Program} {Rk : Obj → Prop} {rc : Recs} :
    ∀ m x, (rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2))) →
      Cross x.1 x.2 → recsBOf P Rk rc m (revRec x) :=
  fun _ x h hc => ⟨x, h, hc, rfl⟩

/-- The canonical record set of the next forward run: the records that `Rk` read, the crossable
    exit edges of `Rk`, and the reversals of the NORMAL backward exit edges with a non-zero premise
    and a crossable reversal (`CrossB`) of the backward run `DBk`. -/
def rcNextOf (P : Program) (Rk : Obj → Prop) (rc : Recs) (DBk : Obj → Prop) : Recs :=
  fun m y => rc m y ∨ (Rk (.init m y.1) ∧ Rk (.edge m y.1 (P.exit m) y.2) ∧ Cross y.1 y.2) ∨
    ∃ jb gb, DBk (.init m jb) ∧ jb ≠ zeroFact ∧ DBk (.edge m jb ((Program.rev P).exit m) gb) ∧
      CrossB jb gb ∧ y = revRec (jb, gb)

theorem rcNextOf_spec {P : Program} {Rk : Obj → Prop} {rc : Recs} {DBk : Obj → Prop} :
    NextRecs P Rk rc DBk (rcNextOf P Rk rc DBk) where
  old _ _ h := Or.inl h
  fwd _ _ _ hj hg hc := Or.inr (Or.inl ⟨hj, hg, hc⟩)
  back _ jb gb hjb hne hgb hc := Or.inr (Or.inr ⟨jb, gb, hjb, hne, hgb, hc, rfl⟩)

/-- Every record of `rcNextOf` is crossable, if every record of `rc` is crossable. -/
theorem rcNextOf_cross {P : Program} {Rk : Obj → Prop} {rc : Recs} {DBk : Obj → Prop}
    (hrc : ∀ m x, rc m x → Cross x.1 x.2) :
    ∀ m x, rcNextOf P Rk rc DBk m x → Cross x.1 x.2 := by
  intro m x h
  rcases h with h | ⟨_, _, hc⟩ | ⟨jb, gb, _, _, _, hc, rfl⟩
  · exact hrc m x h
  · exact hc
  · exact hc.2

/-- A record of `rcNextOf` that comes from the backward run is the reversal of a NORMAL backward
    exit edge: a demand-layer backward summary is never a record. -/
theorem rcNextOf_back_normal {P : Program} {Rk : Obj → Prop} {rc : Recs} {DBk : Obj → Prop}
    {m : MethodId} {x : PFact × AFact} (h : rcNextOf P Rk rc DBk m x) :
    rc m x ∨ (Rk (.init m x.1) ∧ Rk (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2) ∨
    ∃ jb gb, DBk (.init m jb) ∧ DBk (.edge m jb ((Program.rev P).exit m) gb) ∧
      gb.demand = false ∧ x = revRec (jb, gb) := by
  rcases h with h | h | ⟨jb, gb, hjb, _, hgb, hc, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨jb, gb, hjb, hgb, hc.1, rfl⟩)

#print axioms recsBOf_spec
#print axioms rcNextOf_spec
#print axioms rcNextOf_cross
#print axioms rcNextOf_back_normal

/-- THE BACKWARD CONTRACT FOR THE CANONICAL BACKWARD RUN: the backward demand is the forward
    hand-off `handF P Rk pub`, the backward records are `recsBOf P Rk rc`, the next forward run
    gets the demand `demOfN … (pubR (handF P Rk pub))` and the records `rcNextOf`. -/
theorem B_generalN_canon {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {pub : Pub} {rc : Recs} {seeds : List (MethodId × Node × PFact)}
    {counted : Acc → Bool} {L : Nat} {sinksB : List (MethodId × Node × PFact)}
    (hpubSub : ∀ m j g g', pub m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2) :
    BackwardContractN P roots sinks seeds Rk pub rc
      (demOfN (Program.rev P)
        (DB (Program.rev P) counted L (handF P Rk pub) emitM satI restrictI (recsBOf P Rk rc)
          sinksB roots seeds true)
        (pubR (handF P Rk pub)))
      (rcNextOf P Rk rc
        (DB (Program.rev P) counted L (handF P Rk pub) emitM satI restrictI (recsBOf P Rk rc)
          sinksB roots seeds true)) :=
  B_generalN hW hT hmr hNZB hZ hX hk (fun _ _ h => h) recsBOf_spec hpubSub rcNextOf_spec

#print axioms B_generalN_canon

end ApSpec.HandoffBackward
