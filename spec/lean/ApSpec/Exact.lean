/-
  ApSpec.Exact — the PRECISION side of the analysis.

  Soundness (over-approximation) is proved in other modules. This module proves
  the converse for the NORMAL layer: an edge is in the normal layer when its final
  fact has `demand = false`. Such an edge contains no approximation that the AP
  made: every pair in its denotation is a real concrete flow (`Flow`).
  A COMPLETE edge (`AFact.complete`: normal layer and no `[any]` conclusion) is in
  the normal layer, so the same result applies to it (`complete_exact`).

  This justifies to persist complete edges and to use them again across runs
  and across directions.

  Main results:
    1. `applyEdge_exact`  (with the executable witness `wit`, `applyEdge_exact_wit`)
    2. `limitF_exact`, `limitF_complete`
    3. `startFact_exact`
    4. `transfer_exact`
    5. `edge_exact`       THE EXACTNESS THEOREM for the closure `D`
    5'. `complete_exact`  the same for a complete edge (`AFact.complete`)
    6. `closed_exact`     a closed initial fact: its exit edges are EXACTLY the real flows
    7. witness examples at the end of the file

  Result of the audit of `applyEdge`: every branch of `belowCase` and `aboveCase`
  that returns `demand = false` is exact. There is no design bug in the demand bit.
  The proof goes through every branch (`below_geo`, `above_geo`). This includes the
  `lostCorr` branches (a correlated `*` fact with an uncorrelated `[any]` or `$`
  result, `lostCorr_star_exact`): there the middle location takes the initial
  continuation `σ` of `l0`, so the witness `wit` reads `ic` and `l0.path`.
  `AFact.norm` changes a fact only when it sets `demand` (`norm_id_of_demand`).

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.Basic

namespace ApSpec.Exact
open ApSpec

/-! ## Path and exclusion helpers -/

theorem dropPrefix_some : ∀ {p q r : List Acc}, dropPrefix p q = some r → q = p ++ r
  | [], q, r, h => by
    simp only [dropPrefix, Option.some.injEq] at h
    subst h; rfl
  | a :: p, [], r, h => by
    simp only [dropPrefix] at h
    cases h
  | a :: p, b :: q, r, h => by
    simp only [dropPrefix] at h
    split at h
    next hab =>
      have e : a = b := Nat.eq_of_beq_eq_true hab
      subst e
      rw [dropPrefix_some h]; rfl
    next => cases h

theorem dropPrefix_append : ∀ (p τ : List Acc), dropPrefix p (p ++ τ) = some τ
  | [], τ => rfl
  | a :: p, τ => by
    simp only [List.cons_append, dropPrefix, Nat.beq_refl]
    exact dropPrefix_append p τ

theorem relate_below {p q r : List Acc} (h : relate p q = .below r) : q = p ++ r := by
  unfold relate at h
  split at h
  next r' hr => cases h; exact dropPrefix_some hr
  next => split at h <;> cases h

theorem relate_above {p q r : List Acc} (h : relate p q = .above r) : p = q ++ r := by
  unfold relate at h
  split at h
  next => cases h
  next =>
    split at h
    next r' hr => cases h; exact dropPrefix_some hr
    next => cases h

theorem memB_append (a : Acc) : ∀ (xs ys : List Acc), memB a (xs ++ ys) = (memB a xs || memB a ys)
  | [], ys => rfl
  | b :: xs, ys => by
    simp only [List.cons_append, memB, memB_append a xs ys, Bool.or_assoc]

theorem admits_nil (e : Excl) : e.admits [] = true := by cases e <;> rfl

theorem setNil_admits (σ : List Acc) : (Excl.set []).admits σ = true := by
  cases σ <;> rfl

theorem union_admits {e1 e2 : Excl} {σ : List Acc} (h : (e1.union e2).admits σ = true) :
    e1.admits σ = true ∧ e2.admits σ = true := by
  cases σ with
  | nil => exact ⟨admits_nil _, admits_nil _⟩
  | cons a σ =>
    cases e1 with
    | univ => cases h
    | set xs =>
      cases e2 with
      | univ => cases h
      | set ys =>
        revert h
        show (!(memB a (xs ++ ys))) = true → (!(memB a xs)) = true ∧ (!(memB a ys)) = true
        rw [memB_append]
        cases memB a xs <;> cases memB a ys <;> decide

theorem tailExcl_tailI {k : Kind} {σ : List Acc} (h : (tailExcl k).admits σ = true) : tailI k σ := by
  cases k with
  | star e => exact h
  | any => trivial
  | exact =>
    cases σ with
    | nil => rfl
    | cons a σ => cases h

theorem admitsTailB_tailI {k : Kind} {r : List Acc} (h : admitsTailB k r = true) : tailI k r := by
  cases k with
  | star e => exact h
  | any => trivial
  | exact =>
    cases r with
    | nil => rfl
    | cons a r => cases h

theorem tailI_nil (k : Kind) : tailI k [] := by
  cases k with
  | star e => exact admits_nil e
  | any => trivial
  | exact => rfl

theorem admits_cons_append {e : Excl} {a : Acc} {r : List Acc} (τ : List Acc)
    (h : e.admits (a :: r) = true) : e.admits (a :: r ++ τ) = true := by
  cases e <;> exact h

theorem tailI_cons_append {k : Kind} {a : Acc} {r : List Acc} (τ : List Acc)
    (h : admitsTailB k (a :: r) = true) : tailI k (a :: r ++ τ) := by
  cases k with
  | star e => exact admits_cons_append τ h
  | any => trivial
  | exact => cases h

theorem isEmpty_union {e1 e2 : Excl} (h : (e1.union e2).isEmptyB = true) :
    e1 = .set [] ∧ e2 = .set [] := by
  cases e1 with
  | univ => cases h
  | set xs =>
    cases e2 with
    | univ => cases h
    | set ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil => exact ⟨rfl, rfl⟩
        | cons => cases h
      | cons => cases h

theorem tailExcl_setNil {k : Kind} (h : tailExcl k = .set []) (σ : List Acc) : tailI k σ := by
  cases k with
  | star e =>
    simp only [tailExcl] at h
    subst h; exact setNil_admits σ
  | any => trivial
  | exact => cases h

/-! ## Geometry of `belowCase` and `aboveCase`

  For a complete result, the lemmas give the middle location explicitly.
  The continuation of the middle location below the premise path `fr.path` is
  `contOf tk dflt tp q`: for a `*` target it is the part of the end path `q` below
  the target path `tp` (the correlated tail), else it is `dflt`. -/

/-- The continuation of the witness location below the premise path of the edge. -/
def contOf (tk : Kind) (dflt tp q : List Acc) : List Acc :=
  match tk with
  | .star _ => (dropPrefix tp q).getD []
  | _       => dflt

theorem contOf_star {et : Excl} {dflt tp s : List Acc} (τ : List Acc) :
    contOf (.star et) dflt tp (tp ++ s ++ τ) = s ++ τ := by
  simp only [contOf, List.append_assoc, dropPrefix_append, Option.getD_some]

theorem contOf_star_nil {et : Excl} {dflt tp : List Acc} (q : List Acc) :
    contOf (.star et) dflt tp (tp ++ q) = q := by
  simp only [contOf, dropPrefix_append, Option.getD_some]

/-- The continuation of the middle location below the premise path when the target
    tail is not `*`: a correlated `*` fact keeps the initial continuation `σ`. -/
def midOf (ck : Kind) (r σ : List Acc) : List Acc :=
  match ck with
  | .star _ => r ++ σ
  | _       => r

theorem not_eq_false_true {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · cases h
  · rfl

theorem isEmptyB_true {e : Excl} (h : e.isEmptyB = true) : e = .set [] := by
  cases e with
  | univ => cases h
  | set xs =>
    cases xs with
    | nil => rfl
    | cons => cases h

/-- `lostCorr` is exact: if it is `false` for a `*` fact, then the fact admits every
    initial continuation `σ`, and the premise admits the middle continuation `r ++ σ`. -/
theorem lostCorr_star_exact {ec : Excl} {fk : Kind} {r : List Acc}
    (hA : admitsTailB fk r = true) (hs : lostCorr (.star ec) fk r = false) (σ : List Acc) :
    ec.admits σ = true ∧ tailI fk (r ++ σ) := by
  cases r with
  | nil =>
    have he := isEmpty_union (not_eq_false_true hs)
    refine ⟨?_, tailExcl_setNil he.2 σ⟩
    rw [he.1]
    exact setNil_admits σ
  | cons a r =>
    have he := isEmptyB_true (not_eq_false_true hs)
    refine ⟨?_, tailI_cons_append σ hA⟩
    rw [he]
    exact setNil_admits σ

/-- Case `below r` (fact path = premise path ++ r). Every branch with
    `demand = false` is exact: the result pair `(σ, τ)` comes from a middle
    location with continuation `r ++ τ1` below the premise path. -/
theorem below_geo {ck fk tk k : Kind} {r tp p σ τ : List Acc}
    (hb : belowCase ck fk r tp tk = some (p, k, false)) (hF : tailF k σ τ) :
    ∃ τ1, r ++ τ1 = contOf tk (midOf ck r σ) tp (p ++ τ) ∧ tailF ck σ τ1 ∧
      tailI fk (contOf tk (midOf ck r σ) tp (p ++ τ)) ∧
      ∃ τ', p ++ τ = tp ++ τ' ∧ tailF tk (contOf tk (midOf ck r σ) tp (p ++ τ)) τ' := by
  unfold belowCase at hb
  split at hb
  next hA =>
    split at hb
    next et =>
      split at hb
      next a r' =>
        split at hb
        next hE =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, -⟩ := hb
          rw [contOf_star]
          exact ⟨τ, rfl, hF, tailI_cons_append τ hA, a :: r' ++ τ, List.append_assoc _ _ _, rfl,
            admits_cons_append τ hE⟩
        next => cases hb
      next =>
        cases ck with
        | exact =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, -⟩ := hb
          have hτ : τ = [] := hF
          subst hτ
          rw [contOf_star_nil]
          exact ⟨[], rfl, rfl, tailI_nil fk, [], rfl, rfl, admits_nil et⟩
        | star ec =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, -⟩ := hb
          obtain ⟨hτ, hE⟩ := hF
          subst hτ
          rw [contOf_star_nil]
          have u := union_admits hE
          have v := union_admits u.2
          exact ⟨_, rfl, ⟨rfl, u.1⟩, tailExcl_tailI v.1, _, rfl, rfl, v.2⟩
        | any =>
          cases hex : (tailExcl fk).union et with
          | univ =>
            simp only [hex, Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, -⟩ := hb
            have hτ : τ = [] := hF
            subst hτ
            rw [contOf_star_nil]
            exact ⟨[], rfl, trivial, tailI_nil fk, [], rfl, rfl, admits_nil et⟩
          | set xs =>
            cases xs with
            | cons x xs =>
              simp only [hex, Option.some.injEq, Prod.mk.injEq, Excl.isEmptyB] at hb
              obtain ⟨-, -, h⟩ := hb
              cases h
            | nil =>
              simp only [hex, Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl, -⟩ := hb
              have he := isEmpty_union (e1 := tailExcl fk) (e2 := et) (by rw [hex]; rfl)
              rw [contOf_star_nil]
              exact ⟨τ, rfl, trivial, tailExcl_setNil he.1 τ, τ, rfl, rfl,
                by rw [he.2]; exact setNil_admits τ⟩
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, hs⟩ := hb
      cases ck with
      | star ec =>
        have h := lostCorr_star_exact hA hs σ
        exact ⟨σ, rfl, ⟨rfl, h.1⟩, h.2, τ, rfl, trivial⟩
      | any => exact ⟨[], List.append_nil r, trivial, admitsTailB_tailI hA, τ, rfl, trivial⟩
      | exact => exact ⟨[], List.append_nil r, rfl, admitsTailB_tailI hA, τ, rfl, trivial⟩
    next =>
      cases ck with
      | star ec =>
        cases fk with
        | exact =>
          cases r with
          | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, -⟩ := hb
            obtain ⟨hτ, hE⟩ := hF
            cases σ with
            | cons a σ => cases hE
            | nil =>
              subst hτ
              exact ⟨[], rfl, ⟨rfl, admits_nil ec⟩, rfl, [], rfl, rfl⟩
          | cons a r => cases hA
        | star ef =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, hs⟩ := hb
          have hτ : τ = [] := hF
          subst hτ
          have h := lostCorr_star_exact hA hs σ
          exact ⟨σ, rfl, ⟨rfl, h.1⟩, h.2, [], rfl, rfl⟩
        | any =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, hs⟩ := hb
          have hτ : τ = [] := hF
          subst hτ
          have h := lostCorr_star_exact hA hs σ
          exact ⟨σ, rfl, ⟨rfl, h.1⟩, h.2, [], rfl, rfl⟩
      | any =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl, -⟩ := hb
        have hτ : τ = [] := hF
        subst hτ
        exact ⟨[], List.append_nil r, trivial, admitsTailB_tailI hA, [], rfl, rfl⟩
      | exact =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl, -⟩ := hb
        have hτ : τ = [] := hF
        subst hτ
        exact ⟨[], List.append_nil r, rfl, admitsTailB_tailI hA, [], rfl, rfl⟩
  next => cases hb

#print axioms below_geo

/-- Case `above r` (premise path = fact path ++ r). A complete result needs an
    `[any]` fact (`ck = any`), so the middle location is free below the fact path. -/
theorem above_geo {ck fk tk k : Kind} {r tp p σ τ : List Acc}
    (hb : aboveCase ck fk r tp tk = some (p, k, false)) (hF : tailF k σ τ) :
    tailF ck σ (r ++ contOf tk [] tp (p ++ τ)) ∧
      tailI fk (contOf tk [] tp (p ++ τ)) ∧
      ∃ τ', p ++ τ = tp ++ τ' ∧ tailF tk (contOf tk [] tp (p ++ τ)) τ' := by
  unfold aboveCase at hb
  split at hb
  next hA =>
    split at hb
    next et =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, hs⟩ := hb
      cases ck with
      | any =>
        have hE : ((tailExcl fk).union et).isEmptyB = true := by
          revert hs
          cases ((tailExcl fk).union et).isEmptyB <;> decide
        have he := isEmpty_union hE
        rw [contOf_star_nil]
        exact ⟨trivial, tailExcl_setNil he.1 τ, τ, rfl, rfl, by rw [he.2]; exact setNil_admits τ⟩
      | star e => cases hs
      | exact => cases hs
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, hs⟩ := hb
      cases ck with
      | any => exact ⟨trivial, tailI_nil fk, τ, rfl, trivial⟩
      | star e => cases hs
      | exact => cases hs
    next =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, hs⟩ := hb
      cases ck with
      | any =>
        have hτ : τ = [] := hF
        subst hτ
        exact ⟨trivial, tailI_nil fk, [], rfl, rfl⟩
      | star e => cases hs
      | exact => cases hs
  next => cases hb

#print axioms above_geo

/-! ## 1. The core operation -/

/-- The geometric part of `applyEdge`. -/
def geo (c : AFact) (fr to : PFact) : Option (List Acc × Kind × Bool) :=
  match relate fr.path c.fact.path with
  | .below r => belowCase c.fact.kind fr.kind r to.path to.kind
  | .above r => aboveCase c.fact.kind fr.kind r to.path to.kind
  | .apart   => none

/-- A normal form that is complete is the fact itself (the normal form changes a
    fact only when it sets `demand`). -/
theorem norm_id_of_demand {x : AFact} (h : x.norm.demand = false) : x.norm = x := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := x
  cases k with
  | star e =>
    cases m with
    | star =>
      cases ap with
      | false => cases e <;> rfl
      | true => cases e <;> cases h
    | conc t => cases e <;> cases h
  | any => rfl
  | exact => rfl

theorem applyEdge_mem {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts)
    (hra : r.demand = false) :
    ∃ p k ap, c.fact.base = fr.base ∧ geo c fr to = some (p, k, ap) ∧
      markGate fr.mark c.fact.mark = .ok ∧
      r = ⟨⟨to.base, p, k, markOutA to.mark c.fact.mark⟩, c.demand || ap⟩ := by
  unfold applyEdge at h
  split at h
  next hb =>
    dsimp only at h
    split at h
    next => cases h
    next p k ap hg =>
      split at h
      next => cases h
      next => cases h
      next hm =>
        refine ⟨p, k, ap, Nat.eq_of_beq_eq_true hb, hg, hm, ?_⟩
        cases h with
        | head => exact norm_id_of_demand hra
        | tail _ h => cases h
  next => cases h

theorem markOut_out (tm cm : MarkA) (m0 : Mark) :
    (markOutA tm cm).out m0 = tm.out (cm.out m0) := by
  cases tm <;> rfl

theorem gate_admits {fm cm : MarkA} (h : markGate fm cm = .ok) (m0 : Mark) :
    fm.admits (cm.out m0) := by
  cases fm with
  | star => trivial
  | conc t =>
    cases cm with
    | star => cases h
    | conc t' =>
      simp only [markGate] at h
      split at h
      next he => exact (Nat.eq_of_beq_eq_true he).symm
      next => cases h

/-- The relative continuation of the witness location (below the premise path `fr.path`).
    The initial continuation `σ` of `l0` below `ic.path` is necessary: a correlated `*`
    fact with an uncorrelated result takes its middle location from `σ`. -/
def witCont (ic : PFact) (c : AFact) (fr to : PFact) (l0 l2 : Loc) : List Acc :=
  contOf to.kind (match relate fr.path c.fact.path with
    | .below r => midOf c.fact.kind r ((dropPrefix ic.path l0.path).getD [])
    | _        => []) to.path l2.path

/-- THE WITNESS of `applyEdge_exact`: the middle location `l1`. It is computed from
    the initial fact, the fact, the edge, the start location `l0` and the end
    location `l2`. -/
def wit (ic : PFact) (c : AFact) (fr to : PFact) (l0 l2 : Loc) : Loc :=
  ⟨c.fact.base, fr.path ++ witCont ic c fr to l0 l2, c.fact.mark.out l0.mark⟩

/-- 1 (with the witness). The witness `wit` is the middle location of the composition. -/
theorem applyEdge_exact_wit {ic fr to : PFact} {c r : AFact} {l0 l2 : Loc}
    (hc : c.demand = false) (hr : r ∈ (applyEdge c fr to).facts) (hra : r.demand = false)
    (hd : den ic r.fact l0 l2) :
    den ic c.fact l0 (wit ic c fr to l0 l2) ∧ den fr to (wit ic c fr to l0 l2) l2 := by
  obtain ⟨p, k, ap, hbase, hg, hm, rfl⟩ := applyEdge_mem hr hra
  have hap : ap = false := by
    rw [hc] at hra
    exact hra
  subst hap
  obtain ⟨h0b, h2b, h0m, h2m, σ, τ, h0p, h2p, hI, hF⟩ := hd
  have hmA := gate_admits hm l0.mark
  have h2m' : l2.mark = to.mark.out (c.fact.mark.out l0.mark) := by
    rw [h2m]; exact markOut_out _ _ _
  unfold geo at hg
  cases hrel : relate fr.path c.fact.path with
  | below rr =>
    rw [hrel] at hg
    obtain ⟨τ1, hτ1, hF1, hI', τ', hp', hF'⟩ := below_geo hg hF
    have hcp := relate_below hrel
    have hw : witCont ic c fr to l0 l2 = contOf to.kind (midOf c.fact.kind rr σ) to.path (p ++ τ) := by
      unfold witCont; rw [hrel, h2p, h0p, dropPrefix_append, Option.getD_some]
    refine ⟨⟨h0b, rfl, h0m, rfl, σ, τ1, h0p, ?_, hI, hF1⟩,
      ⟨hbase, h2b, hmA, h2m', witCont ic c fr to l0 l2, τ', rfl, ?_, ?_, ?_⟩⟩
    · show fr.path ++ witCont ic c fr to l0 l2 = c.fact.path ++ τ1
      rw [hw, ← hτ1, hcp, List.append_assoc]
    · rw [h2p, hp']
    · rw [hw]; exact hI'
    · rw [hw]; exact hF'
  | above rr =>
    rw [hrel] at hg
    obtain ⟨hF1, hI', τ', hp', hF'⟩ := above_geo hg hF
    have hfp := relate_above hrel
    have hw : witCont ic c fr to l0 l2 = contOf to.kind [] to.path (p ++ τ) := by
      unfold witCont; rw [hrel, h2p]
    refine ⟨⟨h0b, rfl, h0m, rfl, σ, rr ++ witCont ic c fr to l0 l2, h0p, ?_, hI, ?_⟩,
      ⟨hbase, h2b, hmA, h2m', witCont ic c fr to l0 l2, τ', rfl, ?_, ?_, ?_⟩⟩
    · show fr.path ++ witCont ic c fr to l0 l2 = c.fact.path ++ (rr ++ witCont ic c fr to l0 l2)
      rw [hfp, List.append_assoc]
    · rw [hw]; exact hF1
    · rw [h2p, hp']
    · rw [hw]; exact hI'
    · rw [hw]; exact hF'
  | apart =>
    rw [hrel] at hg
    cases hg

#print axioms applyEdge_exact_wit

/-- 1. A complete result of `applyEdge` on a complete fact is a real composition. -/
theorem applyEdge_exact {ic fr to : PFact} {c r : AFact} {l0 l2 : Loc}
    (hc : c.demand = false) (hr : r ∈ (applyEdge c fr to).facts) (hra : r.demand = false)
    (hd : den ic r.fact l0 l2) :
    ∃ l1, den ic c.fact l0 l1 ∧ den fr to l1 l2 :=
  ⟨wit ic c fr to l0 l2, applyEdge_exact_wit hc hr hra hd⟩

#print axioms applyEdge_exact

/-! ## Provenance bit propagation -/

theorem applyEdge_demand {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts)
    (hra : r.demand = false) : c.demand = false := by
  obtain ⟨p, k, ap, -, -, -, rfl⟩ := applyEdge_mem hr hra
  cases hca : c.demand with
  | false => rfl
  | true =>
    rw [hca] at hra
    cases hra

theorem or_eq_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem applySummary_mem {a r g : AFact} {j : PFact} (hr : r ∈ (applySummary a j g).facts)
    (hra : r.demand = false) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ r = ⟨x.fact, x.demand || g.demand⟩ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp hr
  subst e
  exact ⟨x, hx, norm_id_of_demand hra⟩

/-! ## 2. Field limit -/

/-- 2. A complete result of the field limit is the fact itself: the limit did not cut. -/
theorem limitF_exact {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : (limitF counted L f).demand = false) : limitF counted L f = f := by
  unfold limitF at h ⊢
  cases hc : cutPath counted L f.fact.path with
  | none => rfl
  | some p =>
    rw [hc] at h
    cases h

#print axioms limitF_exact

/-- 2'. The converse: if the fact is complete and the limit does not change it, the
    result is complete. -/
theorem limitF_complete {counted : Acc → Bool} {L : Nat} {f : AFact}
    (hf : f.demand = false) (h : limitF counted L f = f) : (limitF counted L f).demand = false := by
  rw [h]; exact hf

#print axioms limitF_complete

theorem limitF_demand {counted : Acc → Bool} {L : Nat} {f : AFact}
    (h : (limitF counted L f).demand = false) : f.demand = false := by
  have e := limitF_exact h
  rw [e] at h
  exact h

/-! ## 3. Start fact -/

theorem loc_ext {l l0 : Loc} (hb : l.base = l0.base) (hp : l.path = l0.path)
    (hm : l.mark = l0.mark) : l = l0 := by
  obtain ⟨b, p, m⟩ := l
  obtain ⟨b0, p0, m0⟩ := l0
  simp only at hb hp hm
  subst hb hp hm
  rfl

/-- 3. A complete start fact is the identity on the initial location set. -/
theorem startFact_exact {i : PFact} {l0 l : Loc} (h : (startFact i).demand = false)
    (hd : den i (startFact i).fact l0 l) : l = l0 := by
  obtain ⟨ib, ip, ik, im⟩ := i
  cases ik with
  | star e =>
    cases im with
    | star =>
      obtain ⟨h0b, hlb, -, hlm, σ, τ, h0p, hlp, -, hτ, -⟩ := hd
      exact loc_ext (hlb.trans h0b.symm) (by rw [hlp, h0p, hτ]; rfl) hlm
    | conc t => cases h
  | any => cases h
  | exact =>
    obtain ⟨h0b, hlb, h0m, hlm, σ, τ, h0p, hlp, hσ, hτ⟩ := hd
    refine loc_ext (hlb.trans h0b.symm) ?_ ?_
    · have hσ' : σ = [] := hσ
      have hτ' : τ = [] := hτ
      rw [hlp, h0p, hσ', hτ']
      rfl
    · cases im with
      | star => exact hlm
      | conc t =>
        have h0 : l0.mark = t := h0m
        rw [hlm, h0]
        rfl

#print axioms startFact_exact

/-! ## 4. Statement transfer -/

theorem applyAll_mem {c x : AFact} :
    ∀ {es : List MicroEdge}, x ∈ (applyAll c es).facts →
      ∃ e, e ∈ es ∧ x ∈ (applyEdge c e.1 e.2).facts
  | [], h => by cases h
  | e :: es, h => by
    have h' : x ∈ (applyEdge c e.1 e.2).facts ++ (applyAll c es).facts := h
    rcases List.mem_append.mp h' with h1 | h1
    · exact ⟨e, List.Mem.head _, h1⟩
    · obtain ⟨e', he', h2⟩ := applyAll_mem h1
      exact ⟨e', List.Mem.tail _ he', h2⟩

theorem transfer_mem {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : AFact}
    (h : x ∈ (transfer counted L s c).facts) :
    (memB c.fact.base s.touched = true ∧
      ∃ y, y ∈ (applyAll c s.edges).facts ∧ x = limitF counted L y) ∨
    (memB c.fact.base s.touched = false ∧ x = c) := by
  unfold transfer at h
  cases ht : memB c.fact.base s.touched with
  | true =>
    rw [ht] at h
    have h' : x ∈ (applyAll c s.edges).facts.map (limitF counted L) := h
    obtain ⟨y, hy, e⟩ := List.mem_map.mp h'
    exact Or.inl ⟨rfl, y, hy, e.symm⟩
  | false =>
    rw [ht] at h
    have h' : x ∈ [c] := h
    cases h' with
    | head => exact Or.inr ⟨rfl, rfl⟩
    | tail _ h2 => cases h2

theorem transfer_demand {counted : Acc → Bool} {L : Nat} {s : Stmt} {c r : AFact}
    (hr : r ∈ (transfer counted L s c).facts) (hra : r.demand = false) : c.demand = false := by
  rcases transfer_mem hr with ⟨-, y, hy, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨e, -, hye⟩ := applyAll_mem hy
    exact applyEdge_demand hye (limitF_demand hra)
  · exact hra

/-- 4. A complete result of the statement transfer is a real statement step. -/
theorem transfer_exact {counted : Acc → Bool} {L : Nat} {s : Stmt} {ic : PFact} {c r : AFact}
    {l0 l' : Loc} (hc : c.demand = false) (hr : r ∈ (transfer counted L s c).facts)
    (hra : r.demand = false) (hd : den ic r.fact l0 l') :
    ∃ l, den ic c.fact l0 l ∧ s.step l l' := by
  rcases transfer_mem hr with ⟨-, y, hy, rfl⟩ | ⟨hu, rfl⟩
  · have e := limitF_exact hra
    rw [e] at hd hra
    obtain ⟨me, hme, hye⟩ := applyAll_mem hy
    obtain ⟨l1, hd1, hd2⟩ := applyEdge_exact hc hye hra hd
    exact ⟨l1, hd1, Or.inr ⟨me, hme, hd2⟩⟩
  · refine ⟨l', hd, Or.inl ⟨?_, rfl⟩⟩
    rw [hd.2.1]
    exact hu

#print axioms transfer_exact

/-! ## 5. THE EXACTNESS THEOREM -/

/-- The motive: a complete edge denotes only real flows. `True` for other objects. -/
def EdgeOK (P : Program) : Obj → Prop
  | .edge M i n f => f.demand = false → ∀ l0 l, den i f.fact l0 l → Flow P M l0 n l
  | _ => True

theorem D_edgeOK {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj} (h : D P counted L α sinks roots o) : EdgeOK P o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro ha l0 l hd
    have e := startFact_exact ha hd
    rw [e]
    exact Flow.start M l0
  | @step M i n f n' s f' _ hE hf ih =>
    intro ha l0 l hd
    have hfa := transfer_demand hf ha
    obtain ⟨l1, hd1, hs⟩ := transfer_exact hfa hf ha hd
    exact Flow.step (ih hfa l0 l1 hd1) hE hs
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    intro ha l0 l hd
    refine Flow.pass (ih ha l0 l hd) hE ?_
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihD _ ihG =>
    intro hla l0 l hd
    have e := limitF_exact hla
    rw [e] at hd hla
    have hra := applyEdge_demand hr' hla
    obtain ⟨l2, hd2, hde2⟩ := applyEdge_exact hra hr' hla hd
    obtain ⟨x, hx, rfl⟩ := applySummary_mem hr hra
    obtain ⟨hxa, hga⟩ := or_eq_false hra
    have haa := applyEdge_demand hx hxa
    have hfa := applyEdge_demand ha haa
    obtain ⟨l1', hd1', hdg⟩ := applyEdge_exact haa hx hxa hd2
    obtain ⟨l1, hd1, hde1⟩ := applyEdge_exact hfa ha haa hd1'
    exact Flow.call (ihD hfa l0 l1 hd1) hE he1 hde1 (ihG hga l1' l2 hdg) he2 hde2
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial

#print axioms D_edgeOK

/-- 5. THE EXACTNESS THEOREM. A complete edge of the closure denotes only real flows. -/
theorem edge_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D P counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  D_edgeOK h ha l0 l hd

#print axioms edge_exact

/-- A complete fact is in the normal layer. -/
theorem complete_demand {f : AFact} (h : f.complete = true) : f.demand = false := by
  unfold AFact.complete at h
  cases hd : f.demand with
  | false => rfl
  | true =>
    rw [hd] at h
    cases h

#print axioms complete_demand

/-- 5'. A complete edge of the closure denotes only real flows. -/
theorem complete_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D P counted L α sinks roots (.edge M i n f)) (hc : f.complete = true)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  edge_exact h (complete_demand hc) hd

#print axioms complete_exact

/-! ## 6. Closed initial fact -/

/-- 6. A closed initial fact: if the exit edges of `i` cover every real flow and every
    exit edge of `i` is complete, then the exit edges of `i` are EXACTLY the real flows
    from the location set of `i`. This is the licence to reuse the persisted summaries
    of `i`. -/
theorem closed_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact}
    (hcov : ∀ l0 l, i.covers l0 → Flow P M l0 (P.exit M) l →
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l)
    (hcomp : ∀ g, D P counted L α sinks roots (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    Flow P M l0 (P.exit M) l ↔
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l :=
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ => edge_exact hg (hcomp g hg) hd⟩

#print axioms closed_exact

/-! ## 7. Witness examples

  The examples use the statement `a.f = b` of `ApSpec.Cases` (accessor f = 1,
  g = 2, h = 3; base a = 11, b = 12; mark T = 5). -/

/-- The initial fact `(x,.,*,{},*)` of the method (x = 10). -/
def exIc : PFact := ⟨10, [], .star (.set []), .star⟩
/-- The complete final fact `(b,.g,*,{h},*)`. -/
def exC : AFact := ⟨⟨12, [2], .star (.set [3]), .star⟩, false⟩
/-- The micro edge `(b,.,*,{},*) → (a,.f,*,{},*)` of `a.f = b`. -/
def exFr : PFact := ⟨12, [], .star (.set []), .star⟩
def exTo : PFact := ⟨11, [1], .star (.set []), .star⟩
/-- The complete result `(a,.f.g,*,{h},*)`. -/
def exR : AFact := ⟨⟨11, [1, 2], .star (.set [3]), .star⟩, false⟩
def exL0 : Loc := ⟨10, [1], 5⟩
def exL2 : Loc := ⟨11, [1, 2, 1], 5⟩

-- 1. The witness: the middle location is `b.g.f` with mark 5.
#eval wit exIc exC exFr exTo exL0 exL2
theorem ex_applyEdge_mem : exR ∈ (applyEdge exC exFr exTo).facts := by decide
theorem ex_wit : wit exIc exC exFr exTo exL0 exL2 = ⟨12, [2, 1], 5⟩ := by decide
theorem ex_applyEdge_exact :
    den exIc exC.fact exL0 ⟨12, [2, 1], 5⟩ ∧ den exFr exTo ⟨12, [2, 1], 5⟩ exL2 := by
  rw [← ex_wit]
  exact applyEdge_exact_wit rfl ex_applyEdge_mem rfl
    ⟨rfl, rfl, trivial, rfl, [1], [1], rfl, rfl, rfl, rfl, rfl⟩
#print axioms ex_applyEdge_exact

-- 1b. A correlated `*` fact through an uncorrelated edge `(b,.,*,{},*) → (a,.,[any],{},*)`.
--     `lostCorr` is false, so the result is complete. The middle location comes from
--     the initial continuation: the start location `x.7` gives the middle location `b.7`.
def exC2 : AFact := ⟨⟨12, [], .star (.set []), .star⟩, false⟩
def exTo2 : PFact := ⟨11, [], .any, .star⟩
def exR2 : AFact := ⟨⟨11, [], .any, .star⟩, false⟩
def exL0b : Loc := ⟨10, [7], 5⟩
def exL2b : Loc := ⟨11, [9, 9], 5⟩
#eval applyEdge exC2 exFr exTo2
#eval wit exIc exC2 exFr exTo2 exL0b exL2b
theorem ex2_applyEdge_mem : exR2 ∈ (applyEdge exC2 exFr exTo2).facts := by decide
theorem ex2_wit : wit exIc exC2 exFr exTo2 exL0b exL2b = ⟨12, [7], 5⟩ := by decide
theorem ex2_applyEdge_exact :
    den exIc exC2.fact exL0b ⟨12, [7], 5⟩ ∧ den exFr exTo2 ⟨12, [7], 5⟩ exL2b := by
  rw [← ex2_wit]
  exact applyEdge_exact_wit rfl ex2_applyEdge_mem rfl
    ⟨rfl, rfl, trivial, rfl, [7], [9, 9], rfl, rfl, rfl, trivial⟩
#print axioms ex2_applyEdge_exact
-- With the exclusion {h} on the fact, `lostCorr` is true: the result is a demand fact.
theorem ex2_lostCorr :
    (applyEdge ⟨⟨12, [], .star (.set [3]), .star⟩, false⟩ exFr exTo2).facts
      = [⟨⟨11, [], .any, .star⟩, true⟩] := by decide

-- 2. Under the limit 2 the fact is complete and the limit is the identity.
--    Under the limit 0 the limit cuts: the result is a demand fact (`demand = true`).
#eval limitF (fun _ => true) 0 exC
theorem ex_limitF_exact : limitF (fun _ => true) 2 exC = exC := limitF_exact (by decide)
#print axioms ex_limitF_exact

-- 3. The start fact of `(x,.f,$,{},T)` is complete. Its only pair from `x.f` is `x.f`.
def exI3 : PFact := ⟨10, [1], .exact, .conc 5⟩
#eval startFact exI3
theorem ex_startFact_den : den exI3 (startFact exI3).fact ⟨10, [1], 5⟩ ⟨10, [1], 5⟩ :=
  ⟨rfl, rfl, rfl, rfl, [], [], rfl, rfl, rfl, rfl⟩
theorem ex_startFact_exact (l : Loc) (h : den exI3 (startFact exI3).fact ⟨10, [1], 5⟩ l) :
    l = ⟨10, [1], 5⟩ :=
  startFact_exact rfl h
#print axioms ex_startFact_exact

end ApSpec.Exact
