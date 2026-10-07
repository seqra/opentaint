/-
  ApSpec.Exact — the PRECISION side of the analysis.

  Soundness (over-approximation) is proved in other modules. This module proves
  the converse for the NORMAL layer: an edge is in the normal layer when its final
  fact has `demand = false`. Such an edge contains no approximation that the AP
  made: every pair in its denotation is a real concrete flow (`Flow`).
  A COMPLETE edge (`AFact.complete`: normal layer and no `[any]` conclusion) is in
  the normal layer, so the same result applies to it (`complete_exact`).

  This justifies to persist complete edges and to use them again across runs.
  Across directions: a backward record with a non-zero premise reverses into an exact forward
  record (`BExact.rev_record_exact`, under `NoZeroBack`).

  Main results:
    1. `applyEdge_exact`  (with the executable witness `wit`, `applyEdge_exact_wit`)
    2. `limitF_exact`, `limitF_complete`
    3. `startFact_exact`
    4. `transfer_exact`
    4'. `cleanRes_exact`  the cleaner (round 5)
    5. `edge_exact`       THE EXACTNESS THEOREM for the closure `D`
    5v. `edge_exact_valid` the same for valid locations (prefix-closed type filters)
    5'. `complete_exact`  the same for a complete edge (`AFact.complete`)
    6. `closed_exact`     a closed initial fact: its exit edges are EXACTLY the real flows
    7. witness examples
    8. `CexMark.cex_mark`, `CexFilt.cex_filt`: the version-4 statement of `edge_exact` is FALSE

  Result of the audit of `applyEdge`: every branch of `belowCase` and `aboveCase`
  that returns `demand = false` is exact. There is no design bug in the demand bit.
  The proof goes through every branch (`below_geo`, `above_geo`). This includes the
  `lostCorr` branches (a correlated `*` fact with an uncorrelated `[any]` or `$`
  result, `lostCorr_star_exact`): there the middle location takes the initial
  continuation `σ` of `l0`, so the witness `wit` reads `ic` and `l0.path`.
  `AFact.norm` changes a fact only when it sets `demand` (`norm_id_of_demand`).

  Result of the round-5 audit (marks `*∖x`, cleaners, type filters):
  * The cleaner is exact (`cleanRes_exact`). A normal-layer result denotes only pairs of the
    input whose end location the cleaner does not clean: `disjoint` is exact, `addEx` removes
    the cleaned mark, and the `$` result of `concPart` keeps only the position itself.
  * `markComp` is NOT exact for a concrete target mark on a fact `*∖x`: the result `conc t`
    forgets the exclusion `x` (`cex_concOK`, and in the closure `CexMark.cex_mark`). A premise
    mark `*∖x` on a micro edge passes the gate but does not admit every mark (`cex_premOK`).
    The theorems therefore need `MarkWF`: on the micro edges of the program, no premise mark
    `*∖x`, and a concrete target mark needs a concrete premise mark. At a summary edge the
    conditions follow from `applicable` and from the invariant "an abstract initial mark gives
    an abstract final mark" (part of the motive `EdgeOK`).
  * The type filter is NOT exact for all locations: a passing `*` or `[any]` fact also denotes
    locations below its path that the filter rejects (`CexFilt.cex_filt`). Two true forms:
    `edge_exact` with `FiltUp` (a filter accepts every extension of an accepted path; with
    `WF.filtPrefix` such a filter is constant, `filtUp_const`), and `edge_exact_valid` for
    valid end locations (every filter accepts a valid location, and validity goes back along
    the micro edges).
  * Possible fixes in `Basic.lean` (not done: the file is frozen): `markComp (conc t) (starEx x)`
    sets `demand`, and the filter rule moves a passing fact with a `*` or `[any]` tail to the
    demand layer unless the filter accepts every extension of its path.

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


/-! ## Mark helpers (round 5: `starEx`, `passes`, `markComp`) -/

theorem or_eq_false {a b : Bool} (h : (a || b) = false) : a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem bool_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- An abstract mark: `*` or `*∖x`. -/
def absB : MarkA → Bool
  | .conc _ => false
  | _       => true

/-- The premise mark of an edge admits every mark that a fact with the mark `cm` gives:
    a premise `*∖x` must be a sub-mark of the fact mark. Other premise marks are always good
    (the gate checks them). -/
def premOKB (fm cm : MarkA) : Bool :=
  match fm with
  | .starEx _ => markSubB fm cm
  | _         => true

/-- A concrete target mark does not meet a fact mark `*∖x`. If it does, `markComp` gives the
    concrete mark and forgets the exclusion `x` of the fact: the result covers initial marks
    that the cleaner removed. -/
def concOKB (tm cm : MarkA) : Bool :=
  match tm, cm with
  | .conc _, .starEx _ => false
  | _,       _         => true

/-- The mark condition of a micro edge (a statement edge or a call binding): its premise mark
    is not `*∖x`, and a concrete target mark has a concrete premise mark (a source reads the
    zero fact). -/
def markEdgeB (fm tm : MarkA) : Bool :=
  match fm, tm with
  | .starEx _, _       => false
  | .star,     .conc _ => false
  | _,         _       => true

theorem memB_all {p : Acc → Bool} {m : Acc} :
    ∀ {x : List Acc}, x.all p = true → memB m x = true → p m = true
  | [], _, h => by cases h
  | a :: x, hall, hm => by
    rw [List.all_cons] at hall
    simp only [memB] at hm
    cases hma : Nat.beq m a with
    | true =>
      have e : m = a := Nat.eq_of_beq_eq_true hma
      subst e
      cases hpa : p m with
      | true => rfl
      | false => rw [hpa] at hall; cases hall
    | false =>
      rw [hma, Bool.false_or] at hm
      cases hpa : p a with
      | true => rw [hpa, Bool.true_and] at hall; exact memB_all hall hm
      | false => rw [hpa] at hall; cases hall

theorem markOut_out (tm cm : MarkA) (m0 : Mark) :
    (markOutA tm cm).out m0 = tm.out (cm.out m0) := by
  cases tm <;> rfl

/-- The gate and the premise condition give the admission of the middle mark. -/
theorem gate_admits {fm cm : MarkA} (h : markGate fm cm = .ok) (hp : premOKB fm cm = true)
    {m0 : Mark} (hc : cm.passes m0) : fm.admits (cm.out m0) := by
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
    | starEx x =>
      simp only [markGate] at h
      split at h <;> cases h
  | starEx x =>
    cases cm with
    | star =>
      have hx : x.isEmpty = true := hp
      cases x with
      | nil => rfl
      | cons => cases hx
    | conc t =>
      have ht : (!memB t x) = true := hp
      show memB t x = false
      revert ht
      cases memB t x <;> decide
    | starEx y =>
      show memB m0 x = false
      have hall : x.all (fun t => memB t y) = true := hp
      have hy : memB m0 y = false := hc
      cases hmx : memB m0 x with
      | false => rfl
      | true =>
        have h1 := memB_all hall hmx
        rw [hy] at h1
        cases h1

#print axioms gate_admits

/-- `markComp` is exact when `concOKB` holds: the result mark is the composition of the two
    marks, and it passes a mark only if the fact mark and the target mark both pass it. -/
theorem markComp_out {tm cm m : MarkA} (h : markComp tm cm = some m) (hc : concOKB tm cm = true)
    {m0 : Mark} (hp : m.passes m0) :
    m.out m0 = tm.out (cm.out m0) ∧ cm.passes m0 ∧ tm.passes (cm.out m0) := by
  cases tm with
  | star =>
    simp only [markComp, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hp, trivial⟩
  | conc t =>
    simp only [markComp, Option.some.injEq] at h
    subst h
    cases cm with
    | star => exact ⟨rfl, trivial, trivial⟩
    | conc t' => exact ⟨rfl, trivial, trivial⟩
    | starEx y => cases hc
  | starEx x =>
    cases cm with
    | star =>
      simp only [markComp, Option.some.injEq] at h
      subst h
      exact ⟨rfl, trivial, hp⟩
    | starEx y =>
      simp only [markComp, Option.some.injEq] at h
      subst h
      have hp' : memB m0 (x ++ y) = false := hp
      rw [memB_append] at hp'
      obtain ⟨hx, hy⟩ := or_eq_false hp'
      exact ⟨rfl, hy, hx⟩
    | conc t =>
      simp only [markComp] at h
      split at h
      next => cases h
      next hn =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, trivial, bool_false_of_not hn⟩

#print axioms markComp_out

/-- A micro edge with `markEdgeB` that passes the gate satisfies both mark conditions. -/
theorem markEdge_ok {fm tm cm : MarkA} (he : markEdgeB fm tm = true) (hg : markGate fm cm = .ok) :
    premOKB fm cm = true ∧ concOKB tm cm = true := by
  cases fm with
  | starEx x => cases he
  | star =>
    cases tm with
    | conc t => cases he
    | star => exact ⟨rfl, rfl⟩
    | starEx x => exact ⟨rfl, rfl⟩
  | conc t =>
    cases cm with
    | star => cases hg
    | starEx y => simp only [markGate] at hg; split at hg <;> cases hg
    | conc t' => exact ⟨rfl, by cases tm <;> rfl⟩

theorem premOK_of_sub {fm cm : MarkA} (h : markSubB fm cm = true) : premOKB fm cm = true := by
  cases fm with
  | starEx x => exact h
  | star => rfl
  | conc t => rfl

theorem gate_abs {fm cm : MarkA} (hg : markGate fm cm = .ok) (hc : absB cm = true) :
    absB fm = true := by
  cases fm with
  | star => rfl
  | starEx x => rfl
  | conc t =>
    cases cm with
    | conc t' => cases hc
    | star => cases hg
    | starEx y => simp only [markGate] at hg; split at hg <;> cases hg

theorem comp_abs {tm cm m : MarkA} (ht : absB tm = true) (hc : absB cm = true)
    (h : markComp tm cm = some m) : absB m = true := by
  cases tm with
  | conc t => cases ht
  | star => simp only [markComp, Option.some.injEq] at h; subst h; exact hc
  | starEx x =>
    cases cm with
    | conc t => cases hc
    | star => simp only [markComp, Option.some.injEq] at h; subst h; rfl
    | starEx y => simp only [markComp, Option.some.injEq] at h; subst h; rfl

theorem concOK_of {tm cm : MarkA} (h : absB cm = true → absB tm = true) : concOKB tm cm = true := by
  cases cm with
  | starEx y =>
    cases tm with
    | conc t => have h1 := h rfl; cases h1
    | star => rfl
    | starEx x => rfl
  | star => cases tm <;> rfl
  | conc t => cases tm <;> rfl

theorem markEdge_abs {fm tm : MarkA} (he : markEdgeB fm tm = true) (hf : absB fm = true) :
    absB tm = true := by
  cases fm with
  | conc t => cases hf
  | starEx x => cases he
  | star =>
    cases tm with
    | conc t => cases he
    | star => rfl
    | starEx x => rfl

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
    | starEx x =>
      cases ap with
      | false => cases e <;> rfl
      | true => cases e <;> cases h
    | conc t => cases e <;> cases h
  | any => rfl
  | exact => rfl

#print axioms norm_id_of_demand

/-- The normal form keeps the mark. -/
theorem norm_mark (x : AFact) : x.norm.fact.mark = x.fact.mark := by
  obtain ⟨⟨b, p, k, m⟩, ap⟩ := x
  cases k with
  | star e => cases m <;> cases ap <;> cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- Every result of `applyEdge` passed the gate, and its mark is the `markComp` result. -/
theorem applyEdge_mark {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    markGate fr.mark c.fact.mark = .ok ∧ markComp to.mark c.fact.mark = some r.fact.mark := by
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
        split at h
        next => cases h
        next m hc =>
          refine ⟨hm, ?_⟩
          cases h with
          | head => rw [norm_mark]; exact hc
          | tail _ h => cases h
  next => cases h

theorem applyEdge_mem {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts)
    (hra : r.demand = false) :
    ∃ p k ap m, c.fact.base = fr.base ∧ geo c fr to = some (p, k, ap) ∧
      markGate fr.mark c.fact.mark = .ok ∧ markComp to.mark c.fact.mark = some m ∧
      r = ⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ := by
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
        split at h
        next => cases h
        next m hc =>
          refine ⟨p, k, ap, m, Nat.eq_of_beq_eq_true hb, hg, hm, hc, ?_⟩
          cases h with
          | head => exact norm_id_of_demand hra
          | tail _ h => cases h
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
    location `l2`. Its mark is the mark of the fact applied to the mark of `l0`. -/
def wit (ic : PFact) (c : AFact) (fr to : PFact) (l0 l2 : Loc) : Loc :=
  ⟨c.fact.base, fr.path ++ witCont ic c fr to l0 l2, c.fact.mark.out l0.mark⟩

/-- 1 (with the witness). The witness `wit` is the middle location of the composition.
    ROUND 5: two mark conditions are necessary (see `cex_premOK` and `cex_concOK`):
    `premOKB` (a premise `*∖x` is a sub-mark of the fact mark) and `concOKB` (a concrete
    target mark does not meet a fact mark `*∖x`). The witness gives the new `passes`
    conjuncts from `markComp_out`. -/
theorem applyEdge_exact_wit {ic fr to : PFact} {c r : AFact} {l0 l2 : Loc}
    (hpm : premOKB fr.mark c.fact.mark = true) (hcm : concOKB to.mark c.fact.mark = true)
    (hc : c.demand = false) (hr : r ∈ (applyEdge c fr to).facts) (hra : r.demand = false)
    (hd : den ic r.fact l0 l2) :
    den ic c.fact l0 (wit ic c fr to l0 l2) ∧ den fr to (wit ic c fr to l0 l2) l2 := by
  obtain ⟨p, k, ap, m, hbase, hg, hm, hmc, rfl⟩ := applyEdge_mem hr hra
  have hap : ap = false := by
    rw [hc] at hra
    exact hra
  subst hap
  obtain ⟨h0b, h2b, h0m, h2m, h2s, σ, τ, h0p, h2p, hI, hF⟩ := hd
  obtain ⟨hout, hcs, hts⟩ := markComp_out hmc hcm h2s
  have hmA := gate_admits hm hpm hcs
  have h2m' : l2.mark = to.mark.out (c.fact.mark.out l0.mark) := by
    rw [h2m]; exact hout
  unfold geo at hg
  cases hrel : relate fr.path c.fact.path with
  | below rr =>
    rw [hrel] at hg
    obtain ⟨τ1, hτ1, hF1, hI', τ', hp', hF'⟩ := below_geo hg hF
    have hcp := relate_below hrel
    have hw : witCont ic c fr to l0 l2 = contOf to.kind (midOf c.fact.kind rr σ) to.path (p ++ τ) := by
      unfold witCont; rw [hrel, h2p, h0p, dropPrefix_append, Option.getD_some]
    refine ⟨⟨h0b, rfl, h0m, rfl, hcs, σ, τ1, h0p, ?_, hI, hF1⟩,
      ⟨hbase, h2b, hmA, h2m', hts, witCont ic c fr to l0 l2, τ', rfl, ?_, ?_, ?_⟩⟩
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
    refine ⟨⟨h0b, rfl, h0m, rfl, hcs, σ, rr ++ witCont ic c fr to l0 l2, h0p, ?_, hI, ?_⟩,
      ⟨hbase, h2b, hmA, h2m', hts, witCont ic c fr to l0 l2, τ', rfl, ?_, ?_, ?_⟩⟩
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

/-- 1. A complete result of `applyEdge` on a complete fact is a real composition
    (under the two mark conditions of `applyEdge_exact_wit`). -/
theorem applyEdge_exact {ic fr to : PFact} {c r : AFact} {l0 l2 : Loc}
    (hpm : premOKB fr.mark c.fact.mark = true) (hcm : concOKB to.mark c.fact.mark = true)
    (hc : c.demand = false) (hr : r ∈ (applyEdge c fr to).facts) (hra : r.demand = false)
    (hd : den ic r.fact l0 l2) :
    ∃ l1, den ic c.fact l0 l1 ∧ den fr to l1 l2 :=
  ⟨wit ic c fr to l0 l2, applyEdge_exact_wit hpm hcm hc hr hra hd⟩

#print axioms applyEdge_exact

/-! ### The two mark conditions are necessary

  Without `premOKB`: the premise `*∖{5}` of an edge passes the gate for a fact with the mark
  `5`, but the edge does not admit the mark `5`. Without `concOKB`: the target `5 → 9`
  (`conc 9`) applied to a fact `*∖{5}` gives `conc 9`, which forgets the exclusion. The
  initial location with the mark `5` is in the pair relation of the result, but not in the
  pair relation of the fact. -/

def cxC1 : AFact := ⟨⟨1, [], .exact, .conc 5⟩, false⟩
def cxFr1 : PFact := ⟨1, [], .exact, .starEx [5]⟩
def cxTo1 : PFact := ⟨2, [], .exact, .star⟩
def cxIc : PFact := ⟨3, [], .exact, .star⟩
def cxR1 : AFact := ⟨⟨2, [], .exact, .conc 5⟩, false⟩

theorem cex_premOK :
    premOKB cxFr1.mark cxC1.fact.mark = false ∧ cxR1 ∈ (applyEdge cxC1 cxFr1 cxTo1).facts ∧
    den cxIc cxR1.fact ⟨3, [], 7⟩ ⟨2, [], 5⟩ ∧
    ¬ ∃ l1, den cxIc cxC1.fact ⟨3, [], 7⟩ l1 ∧ den cxFr1 cxTo1 l1 ⟨2, [], 5⟩ := by
  refine ⟨by decide, by decide, ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨l1, _, h⟩
  obtain ⟨_, _, hadm, hmk, _⟩ := h
  have hadm' : memB l1.mark [5] = false := hadm
  have hmk' : (5 : Nat) = l1.mark := hmk
  rw [← hmk'] at hadm'
  exact absurd hadm' (by decide)

#print axioms cex_premOK

def cxC2 : AFact := ⟨⟨1, [], .exact, .starEx [5]⟩, false⟩
def cxFr2 : PFact := ⟨1, [], .exact, .star⟩
def cxTo2 : PFact := ⟨2, [], .exact, .conc 9⟩
def cxR2 : AFact := ⟨⟨2, [], .exact, .conc 9⟩, false⟩

theorem cex_concOK :
    concOKB cxTo2.mark cxC2.fact.mark = false ∧ cxR2 ∈ (applyEdge cxC2 cxFr2 cxTo2).facts ∧
    den cxIc cxR2.fact ⟨3, [], 5⟩ ⟨2, [], 9⟩ ∧
    ¬ ∃ l1, den cxIc cxC2.fact ⟨3, [], 5⟩ l1 ∧ den cxFr2 cxTo2 l1 ⟨2, [], 9⟩ := by
  refine ⟨by decide, by decide, ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨l1, h, _⟩
  obtain ⟨_, _, _, _, hps, _⟩ := h
  have hps' : memB 5 [5] = false := hps
  exact absurd hps' (by decide)

#print axioms cex_concOK

/-! ## Provenance bit propagation -/

theorem applyEdge_demand {c r : AFact} {fr to : PFact} (hr : r ∈ (applyEdge c fr to).facts)
    (hra : r.demand = false) : c.demand = false := by
  obtain ⟨p, k, ap, m, -, -, -, -, rfl⟩ := applyEdge_mem hr hra
  cases hca : c.demand with
  | false => rfl
  | true =>
    rw [hca] at hra
    cases hra

theorem applySummary_mem {a r g : AFact} {j : PFact} (hr : r ∈ (applySummary a j g).facts)
    (hra : r.demand = false) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ r = ⟨x.fact, x.demand || g.demand⟩ := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp hr
  subst e
  exact ⟨x, hx, norm_id_of_demand hra⟩

theorem applySummary_mark {a r g : AFact} {j : PFact} (hr : r ∈ (applySummary a j g).facts) :
    ∃ x, x ∈ (applyEdge a j g.fact).facts ∧ r.fact.mark = x.fact.mark := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp hr
  subst e
  exact ⟨x, hx, norm_mark _⟩

/-- A micro edge with `markEdgeB` keeps an abstract fact mark abstract. -/
theorem applyEdge_abs {c r : AFact} {fr to : PFact} (he : markEdgeB fr.mark to.mark = true)
    (hc : absB c.fact.mark = true) (hr : r ∈ (applyEdge c fr to).facts) :
    absB r.fact.mark = true := by
  obtain ⟨hg, hm⟩ := applyEdge_mark hr
  exact comp_abs (markEdge_abs he (gate_abs hg hc)) hc hm

theorem applicable_markSub {j a : PFact} (h : applicable j a = true) :
    markSubB j.mark a.mark = true := by
  unfold applicable coversB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

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

theorem limitF_mark {counted : Acc → Bool} {L : Nat} (f : AFact) :
    (limitF counted L f).fact.mark = f.fact.mark := by
  unfold limitF
  cases cutPath counted L f.fact.path <;> rfl

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
      obtain ⟨h0b, hlb, -, hlm, -, σ, τ, h0p, hlp, -, hτ, -⟩ := hd
      exact loc_ext (hlb.trans h0b.symm) (by rw [hlp, h0p, hτ]; rfl) hlm
    | starEx x =>
      obtain ⟨h0b, hlb, -, hlm, -, σ, τ, h0p, hlp, -, hτ, -⟩ := hd
      exact loc_ext (hlb.trans h0b.symm) (by rw [hlp, h0p, hτ]; rfl) hlm
    | conc t => cases h
  | any => cases h
  | exact =>
    obtain ⟨h0b, hlb, h0m, hlm, -, σ, τ, h0p, hlp, hσ, hτ⟩ := hd
    refine loc_ext (hlb.trans h0b.symm) ?_ ?_
    · have hσ' : σ = [] := hσ
      have hτ' : τ = [] := hτ
      rw [hlp, h0p, hσ', hτ']
      rfl
    · cases im with
      | star => exact hlm
      | starEx x => exact hlm
      | conc t =>
        have h0 : l0.mark = t := h0m
        rw [hlm, h0]
        rfl

#print axioms startFact_exact

/-- The start fact keeps the mark of the initial fact. -/
theorem startFact_mark (i : PFact) : (startFact i).fact.mark = i.mark := by
  obtain ⟨ib, ip, ik, im⟩ := i
  cases ik <;> cases im <;> rfl

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

/-- The statement transfer keeps an abstract fact mark abstract. -/
theorem transfer_abs {counted : Acc → Bool} {L : Nat} {s : Stmt} {c x : AFact}
    (hmk : ∀ e, e ∈ s.edges → markEdgeB e.1.mark e.2.mark = true)
    (hc : absB c.fact.mark = true) (hx : x ∈ (transfer counted L s c).facts) :
    absB x.fact.mark = true := by
  rcases transfer_mem hx with ⟨-, y, hy, rfl⟩ | ⟨-, rfl⟩
  · rw [limitF_mark]
    obtain ⟨me, hme, hye⟩ := applyAll_mem hy
    exact applyEdge_abs (hmk me hme) hc hye
  · exact hc

/-- 4. A complete result of the statement transfer is a real statement step.
    ROUND 5: the micro edges of the statement satisfy `markEdgeB`. -/
theorem transfer_exact {counted : Acc → Bool} {L : Nat} {s : Stmt} {ic : PFact} {c r : AFact}
    {l0 l' : Loc} (hmk : ∀ e, e ∈ s.edges → markEdgeB e.1.mark e.2.mark = true)
    (hc : c.demand = false) (hr : r ∈ (transfer counted L s c).facts)
    (hra : r.demand = false) (hd : den ic r.fact l0 l') :
    ∃ l, den ic c.fact l0 l ∧ s.step l l' := by
  rcases transfer_mem hr with ⟨-, y, hy, rfl⟩ | ⟨hu, rfl⟩
  · have e := limitF_exact hra
    rw [e] at hd hra
    obtain ⟨me, hme, hye⟩ := applyAll_mem hy
    obtain ⟨hpm, hcm⟩ := markEdge_ok (hmk me hme) (applyEdge_mark hye).1
    obtain ⟨l1, hd1, hd2⟩ := applyEdge_exact hpm hcm hc hye hra hd
    exact ⟨l1, hd1, Or.inr ⟨me, hme, hd2⟩⟩
  · refine ⟨l', hd, Or.inl ⟨?_, rfl⟩⟩
    rw [hd.2.1]
    exact hu

#print axioms transfer_exact

/-! ## 4'. The cleaner (round 5)

  A normal-layer result of the cleaner denotes only pairs of the input whose end location
  the cleaner does not clean (`cleanRes_exact`). The proof has three parts: the position
  `disjoint` is exact (`cleanPos_disjoint`), the mark `addEx m t` removes the end marks `t`
  (`addEx_den`), and the `$` result of `concPart` keeps only the position itself, which a
  cleaner of everything strictly below does not clean. -/

theorem relate_above_none {p q r : List Acc} (h : relate p q = .above r) : dropPrefix p q = none := by
  unfold relate at h
  split at h
  next => cases h
  next hn => exact hn

theorem relate_apart {p q : List Acc} (h : relate p q = .apart) :
    dropPrefix p q = none ∧ dropPrefix q p = none := by
  unfold relate at h
  split at h
  next => cases h
  next hn =>
    split at h
    next => cases h
    next hn' => exact ⟨hn, hn'⟩

theorem dropPrefix_self (p : List Acc) : dropPrefix p p = some [] := by
  have h := dropPrefix_append p []
  rwa [List.append_nil] at h

/-- Two decompositions of one list: one of the two prefixes is a prefix of the other. -/
theorem prefix_comparable : ∀ (p q ρ τ : List Acc), p ++ ρ = q ++ τ →
    (∃ r, q = p ++ r) ∨ (∃ r, p = q ++ r)
  | [], q, _, _, _ => Or.inl ⟨q, rfl⟩
  | a :: p, [], _, _, _ => Or.inr ⟨a :: p, rfl⟩
  | a :: p, b :: q, ρ, τ, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rcases prefix_comparable p q ρ τ h with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr ⟨r, rfl⟩

theorem cleansB_base {cl : Cleaner} {l : Loc} (h : Nat.beq l.base cl.base = false) :
    cl.cleansB l = false := by
  unfold Cleaner.cleansB
  rw [h]
  rfl

theorem cleansB_mark {cl : Cleaner} {l : Loc} (h : cl.markB l.mark = false) :
    cl.cleansB l = false := by
  unfold Cleaner.cleansB
  rw [h, Bool.and_false, Bool.false_and]

theorem cleansB_none {cl : Cleaner} {l : Loc} (h : dropPrefix cl.path l.path = none) :
    cl.cleansB l = false := by
  unfold Cleaner.cleansB
  rw [h, Bool.and_false]

theorem cleansB_some {cl : Cleaner} {l : Loc} {σ : List Acc} (h : dropPrefix cl.path l.path = some σ)
    (hσ : cl.reach.inB σ = false) : cl.cleansB l = false := by
  unfold Cleaner.cleansB
  rw [h]
  dsimp only
  rw [hσ, Bool.and_false]

/-- The position `disjoint` is exact: the cleaner cleans no end location of the fact. -/
theorem cleanPos_disjoint {cl : Cleaner} {c i : PFact} {l0 l : Loc}
    (hp : cleanPos cl c = .disjoint) (hd : den i c l0 l) : cl.cleansB l = false := by
  obtain ⟨clb, clp, clr, clm⟩ := cl
  obtain ⟨cb, cp, ck, cm⟩ := c
  obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, hF⟩ := hd
  simp only at hlb hlp hF
  unfold cleanPos at hp
  simp only at hp
  split at hp
  next hb =>
    cases hrel : relate clp cp with
    | below r =>
      rw [hrel] at hp
      have hcp : cp = clp ++ r := relate_below hrel
      cases r with
      | nil =>
        cases clr <;> cases ck <;> simp only at hp <;> (try cases hp)
        -- the reach `below` on a `$` fact at the position
        have hτ : τ = [] := hF
        apply cleansB_some (σ := [])
        · show dropPrefix clp l.path = some []
          rw [hlp, hτ, hcp, List.append_nil, List.append_nil]
          exact dropPrefix_self clp
        · rfl
      | cons a r' =>
        cases clr <;> simp only at hp <;> (try cases hp)
        -- the reach `exact` on a fact strictly below the position
        apply cleansB_some (σ := a :: r' ++ τ)
        · show dropPrefix clp l.path = some (a :: r' ++ τ)
          rw [hlp, hcp, List.append_assoc]
          exact dropPrefix_append clp _
        · rfl
    | above r =>
      rw [hrel] at hp
      have hnone := relate_above_none hrel
      have hpc : clp = cp ++ r := relate_above hrel
      cases ck with
      | exact =>
        have hτ : τ = [] := hF
        apply cleansB_none
        show dropPrefix clp l.path = none
        rw [hlp, hτ, List.append_nil]
        exact hnone
      | any => simp only at hp; cases hp
      | star e =>
        simp only at hp
        split at hp
        next => cases hp
        next hne =>
          obtain ⟨hτσ, hE⟩ := hF
          cases hdp : dropPrefix clp l.path with
          | none => exact cleansB_none hdp
          | some ρ =>
            exfalso
            have hl := dropPrefix_some hdp
            rw [hlp, hpc, List.append_assoc] at hl
            have hτ : τ = r ++ ρ := List.append_cancel_left hl
            cases r with
            | nil =>
              rw [List.append_nil] at hpc
              rw [hpc, dropPrefix_self] at hnone
              cases hnone
            | cons a r' =>
              have h1 : e.admits (a :: r' ++ ρ) = true := by rw [← hτ, hτσ]; exact hE
              have h2 : e.admits (a :: r') = e.admits (a :: r' ++ ρ) := by cases e <;> rfl
              rw [← h2] at h1
              exact hne h1
    | apart =>
      have ⟨h1, h2⟩ := relate_apart hrel
      cases hdp : dropPrefix clp l.path with
      | none => exact cleansB_none hdp
      | some ρ =>
        exfalso
        have hl := dropPrefix_some hdp
        rw [hlp] at hl
        rcases prefix_comparable cp clp τ ρ hl with ⟨r, hr⟩ | ⟨r, hr⟩
        · rw [hr, dropPrefix_append] at h2
          cases h2
        · rw [hr, dropPrefix_append] at h1
          cases h1
  next hb =>
    apply cleansB_base
    show Nat.beq l.base clb = false
    rw [hlb]
    exact bool_false_of_not hb

#print axioms cleanPos_disjoint

/-- The mark `addEx m t` of an abstract mark `m`: its pairs are pairs of the mark `m` whose end
    location does not carry the mark `t`. -/
theorem addEx_den {i : PFact} {b : Base} {p : List Acc} {k : Kind} {m : MarkA} {t : Mark}
    {l0 l : Loc} (hm : absB m = true) (hd : den i ⟨b, p, k, addEx m t⟩ l0 l) :
    den i ⟨b, p, k, m⟩ l0 l ∧ Nat.beq l.mark t = false := by
  obtain ⟨h0b, hlb, h0m, hlm, hps, rest⟩ := hd
  cases m with
  | conc t' => cases hm
  | star =>
    have hps' : memB l0.mark [t] = false := hps
    have hlm' : l.mark = l0.mark := hlm
    simp only [memB, Bool.or_false] at hps'
    exact ⟨⟨h0b, hlb, h0m, hlm', trivial, rest⟩, by rw [hlm']; exact hps'⟩
  | starEx x =>
    have hps' : memB l0.mark (t :: x) = false := hps
    have hlm' : l.mark = l0.mark := hlm
    simp only [memB] at hps'
    obtain ⟨h1, h2⟩ := or_eq_false hps'
    exact ⟨⟨h0b, hlb, h0m, hlm', h2, rest⟩, by rw [hlm']; exact h1⟩

theorem addEx_abs {m : MarkA} (t : Mark) (hm : absB m = true) : absB (addEx m t) = true := by
  cases m with
  | conc t' => cases hm
  | star => rfl
  | starEx x => rfl

/-- The two results of `concPart`. -/
theorem concPart_cases (cl : Cleaner) (c : AFact) :
    (c.fact.kind = .any ∧ cl.reach = .below ∧ relate cl.path c.fact.path = .below [] ∧
      concPart cl c = ⟨⟨c.fact.base, c.fact.path, .exact, c.fact.mark⟩, c.demand⟩) ∨
    concPart cl c = ⟨c.fact, true⟩ := by
  unfold concPart
  split
  next h1 h2 h3 => exact Or.inl ⟨h1, h2, h3, rfl⟩
  next => exact Or.inr rfl

/-- The normal form of a demand-layer fact stays in the demand layer. -/
theorem norm_true_demand (g : PFact) : (AFact.norm ⟨g, true⟩).demand = true := by
  unfold AFact.norm
  split <;> rfl

/-- The normal form keeps the mark. -/
theorem norm_mark_eq (f : AFact) : f.norm.fact.mark = f.fact.mark := by
  unfold AFact.norm
  split <;> rfl

/-- The results of the cleaner on one fact. -/
theorem cleanRes_mem {cl : Cleaner} {c r : AFact} (hr : r ∈ (cleanRes cl c).facts) :
    (r = c ∧ (cleanPos cl c.fact = .disjoint ∨ ∃ t, c.fact.mark = .conc t ∧ cl.markB t = false)) ∨
    (∃ t, absB c.fact.mark = true ∧ cl.mark = some t ∧
      r = ⟨⟨c.fact.base, c.fact.path, c.fact.kind, addEx c.fact.mark t⟩, c.demand⟩) ∨
    (∃ t, c.fact.mark = .conc t ∧ cl.markB t = true ∧ r = concPart cl c) ∨
    r = AFact.norm ⟨c.fact, true⟩ := by
  unfold cleanRes at hr
  cases hpos : cleanPos cl c.fact with
  | disjoint =>
    rw [hpos] at hr
    cases hr with
    | head => exact Or.inl ⟨rfl, Or.inl rfl⟩
    | tail _ h => cases h
  | inside =>
    rw [hpos] at hr
    obtain ⟨⟨cb, cp, ck, cm⟩, cd⟩ := c
    obtain ⟨clb, clp, clr, clm⟩ := cl
    cases cm with
    | conc t =>
      dsimp only at hr
      split at hr
      next => cases hr
      next hn =>
        cases hr with
        | head => exact Or.inl ⟨rfl, Or.inr ⟨t, rfl, bool_false_of_not hn⟩⟩
        | tail _ h => cases h
    | star =>
      cases clm with
      | none => cases hr
      | some t =>
        cases hr with
        | head => exact Or.inr (Or.inl ⟨t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
    | starEx x =>
      cases clm with
      | none => cases hr
      | some t =>
        cases hr with
        | head => exact Or.inr (Or.inl ⟨t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
  | part =>
    rw [hpos] at hr
    obtain ⟨⟨cb, cp, ck, cm⟩, cd⟩ := c
    obtain ⟨clb, clp, clr, clm⟩ := cl
    cases cm with
    | conc t =>
      dsimp only at hr
      split at hr
      next hy =>
        cases hr with
        | head => exact Or.inr (Or.inr (Or.inl ⟨t, rfl, hy, rfl⟩))
        | tail _ h => cases h
      next hn =>
        cases hr with
        | head => exact Or.inl ⟨rfl, Or.inr ⟨t, rfl, bool_false_of_not hn⟩⟩
        | tail _ h => cases h
    | star =>
      cases clm with
      | none =>
        cases hr with
        | head => exact Or.inr (Or.inr (Or.inr rfl))
        | tail _ h => cases h
      | some t =>
        cases hr with
        | head => exact Or.inr (Or.inl ⟨t, rfl, rfl, rfl⟩)
        | tail _ h => cases h
    | starEx x =>
      cases clm with
      | none =>
        cases hr with
        | head => exact Or.inr (Or.inr (Or.inr rfl))
        | tail _ h => cases h
      | some t =>
        cases hr with
        | head => exact Or.inr (Or.inl ⟨t, rfl, rfl, rfl⟩)
        | tail _ h => cases h

theorem markB_some {cl : Cleaner} {t m : Mark} (h : cl.mark = some t) : cl.markB m = Nat.beq m t := by
  unfold Cleaner.markB
  rw [h]

/-- THE CLEANER IS EXACT. A normal-layer result of the cleaner denotes pairs of the input
    whose end location the cleaner does not clean. -/
theorem cleanRes_exact {cl : Cleaner} {c r : AFact} {i : PFact} {l0 l : Loc}
    (hr : r ∈ (cleanRes cl c).facts) (hra : r.demand = false) (hd : den i r.fact l0 l) :
    den i c.fact l0 l ∧ cl.cleansB l = false := by
  rcases cleanRes_mem hr with ⟨rfl, hpos | ⟨t, hm, ht⟩⟩ | ⟨t, hab, hcl, rfl⟩ | ⟨t, hm, ht, rfl⟩ | rfl
  · exact ⟨hd, cleanPos_disjoint hpos hd⟩
  · refine ⟨hd, cleansB_mark ?_⟩
    have hlm : l.mark = r.fact.mark.out l0.mark := hd.2.2.2.1
    rw [hm] at hlm
    rw [hlm]
    exact ht
  · obtain ⟨hd', hb⟩ := addEx_den hab hd
    refine ⟨hd', cleansB_mark ?_⟩
    rw [markB_some hcl]
    exact hb
  · rcases concPart_cases cl c with ⟨hk, hreach, hrel, he⟩ | he
    · rw [he] at hd
      obtain ⟨h0b, hlb, h0m, hlm, hps, σ, τ, h0p, hlp, hI, hF⟩ := hd
      have hτ : τ = [] := hF
      have hcp : c.fact.path = cl.path ++ [] := relate_below hrel
      refine ⟨⟨h0b, hlb, h0m, hlm, hps, σ, τ, h0p, hlp, hI, ?_⟩, ?_⟩
      · rw [hk]; trivial
      · apply cleansB_some (σ := [])
        · show dropPrefix cl.path l.path = some []
          rw [hlp, hτ, List.append_nil, hcp, List.append_nil]
          exact dropPrefix_self _
        · rw [hreach]; rfl
    · rw [he] at hra
      cases hra
  · rw [norm_true_demand] at hra
    cases hra

#print axioms cleanRes_exact

/-- A normal-layer result of the cleaner comes from a normal-layer fact. -/
theorem cleanRes_demand {cl : Cleaner} {c r : AFact} (hr : r ∈ (cleanRes cl c).facts)
    (hra : r.demand = false) : c.demand = false := by
  rcases cleanRes_mem hr with ⟨rfl, -⟩ | ⟨t, -, -, rfl⟩ | ⟨t, -, -, rfl⟩ | rfl
  · exact hra
  · exact hra
  · rcases concPart_cases cl c with ⟨-, -, -, he⟩ | he
    · rw [he] at hra; exact hra
    · rw [he] at hra; cases hra
  · rw [norm_true_demand] at hra
    cases hra

/-- The cleaner keeps an abstract fact mark abstract. -/
theorem cleanRes_abs {cl : Cleaner} {c r : AFact} (hc : absB c.fact.mark = true)
    (hr : r ∈ (cleanRes cl c).facts) : absB r.fact.mark = true := by
  rcases cleanRes_mem hr with ⟨rfl, -⟩ | ⟨t, hab, -, rfl⟩ | ⟨t, hm, -, rfl⟩ | rfl
  · exact hc
  · exact addEx_abs t hab
  · rw [hm] at hc; cases hc
  · rw [norm_mark_eq]; exact hc

/-! ## 5. THE EXACTNESS THEOREM

  ROUND 5. The version-4 statement (no hypotheses) is FALSE. Two counterexamples are in §8:
  * `CexMark`: a cleaner gives `*∖{5}`; then a statement edge with the premise mark `*` and
    the target mark `9` (`conc 9`) gives `conc 9` in the normal layer. `markComp` forgets the
    exclusion, so the edge also denotes the initial location with the mark `5`, which the
    cleaner removed. Condition: `MarkWF` (a concrete target mark needs a concrete premise
    mark; no premise mark `*∖x`).
  * `CexFilt`: a type filter keeps a fact whose path passes; the fact `[any]` also denotes
    locations below the path that the filter rejects. Condition: `FiltUp` (a filter that
    accepts a path accepts every extension), or exactness for VALID locations only
    (`edge_exact_valid`).
  The program of each counterexample satisfies `Program.WF`. -/

/-- The mark condition on the micro edges of the program (statement edges and call bindings). -/
structure MarkWF (P : Program) : Prop where
  stmt  : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    ∀ e, e ∈ s.edges → markEdgeB e.1.mark e.2.mark = true
  toC   : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e, e ∈ c.toCallee → markEdgeB e.1.mark e.2.mark = true
  fromC : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e, e ∈ c.fromCallee → markEdgeB e.1.mark e.2.mark = true

/-- A filter accepts every extension of a path that it accepts (an Accept keeps the whole
    subtree). -/
def FiltUp (P : Program) : Prop :=
  ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges →
    ∀ p q, may p = true → may (p ++ q) = true

/-- Every filter accepts every valid location of its base. -/
def FiltValid (P : Program) (ok : Loc → Prop) : Prop :=
  ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges →
    ∀ l, ok l → l.base = b → may l.path = true

/-- The filter condition that the proof uses, relative to the valid locations `ok`: a filter
    that accepts a path accepts every valid location below it. -/
def FiltOK (P : Program) (ok : Loc → Prop) : Prop :=
  ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges →
    ∀ (p τ : List Acc) (l : Loc), may p = true → l.path = p ++ τ → ok l → l.base = b →
      may l.path = true

/-- The valid locations are closed backwards along the micro edges: the source location of a
    valid location is valid. -/
structure BackOK (P : Program) (ok : Loc → Prop) : Prop where
  stmt  : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → ∀ e, e ∈ s.edges →
    ∀ l1 l2, den e.1 e.2 l1 l2 → ok l2 → ok l1
  toC   : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → ∀ e, e ∈ c.toCallee →
    ∀ l1 l2, den e.1 e.2 l1 l2 → ok l2 → ok l1
  fromC : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → ∀ e, e ∈ c.fromCallee →
    ∀ l1 l2, den e.1 e.2 l1 l2 → ok l2 → ok l1

theorem filtUp_ok {P : Program} (h : FiltUp P) : FiltOK P (fun _ => True) := by
  intro M n b may n' hE p τ l hp hlp _ _
  rw [hlp]
  exact h M n b may n' hE p τ hp

theorem filtValid_ok {P : Program} {ok : Loc → Prop} (h : FiltValid P ok) : FiltOK P ok := by
  intro M n b may n' hE _ _ l _ _ hok hb
  exact h M n b may n' hE l hok hb

theorem backOK_true (P : Program) : BackOK P (fun _ => True) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-- `FiltUp` and `Program.WF.filtPrefix` together make a filter CONSTANT on paths: it accepts
    every path or no path. So `FiltUp` is a strong condition; `edge_exact_valid` is the form
    for a real type filter (prefix-closed, not extension-closed). -/
theorem filtUp_const {may : List Acc → Bool} (hup : ∀ p q, may p = true → may (p ++ q) = true)
    (hpre : ∀ p q, may (p ++ q) = true → may p = true) (p : List Acc) : may p = may [] := by
  cases h : may [] with
  | true => exact hup [] p h
  | false =>
    cases hp : may p with
    | false => rfl
    | true =>
      have h1 := hpre [] p hp
      rw [h] at h1
      cases h1

#print axioms filtUp_const

/-- The motive. For an edge: an abstract initial mark gives an abstract final mark (the
    invariant that excludes the `CexMark` case at a summary), and a normal-layer edge denotes
    only real flows for valid end locations; the start location is then valid too. `True` for
    other objects. -/
def EdgeOK (P : Program) (ok : Loc → Prop) : Obj → Prop
  | .edge M i n f => (absB i.mark = true → absB f.fact.mark = true) ∧
      (f.demand = false → ∀ l0 l, den i f.fact l0 l → ok l → Flow P M l0 n l ∧ ok l0)
  | _ => True

theorem D_edgeOK {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {ok : Loc → Prop} (hmw : MarkWF P) (hfo : FiltOK P ok)
    (hbo : BackOK P ok) {o : Obj} (h : D P counted L α sinks roots o) : EdgeOK P ok o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    refine ⟨fun hi => by rw [startFact_mark]; exact hi, ?_⟩
    intro ha l0 l hd hok
    have e := startFact_exact ha hd
    subst e
    exact ⟨Flow.start M l, hok⟩
  | @step M i n f n' s f' _ hE hf ih =>
    refine ⟨fun hi => transfer_abs (hmw.stmt _ _ _ _ hE) (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := transfer_demand hf ha
    obtain ⟨l1, hd1, hs⟩ := transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l1 hd1 hok1
    exact ⟨Flow.step hfl hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M i n f n' c _ hE hm ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.pass hfl hE ?_, hok0⟩
    rw [hd.2.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    refine ⟨fun hi => ?_, ?_⟩
    · -- the mark invariant
      have hA := applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (ihD.1 hi) ha
      obtain ⟨x, hx, hxm⟩ := applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := applyEdge_mark hx
      have hG := ihG.1 (gate_abs hgx hA)
      have hR : absB r.fact.mark = true := by rw [hxm]; exact comp_abs hG hA hcx
      rw [limitF_mark]
      exact applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · intro hla l0 l hd hok
      have e := limitF_exact hla
      rw [e] at hd hla
      have hra := applyEdge_demand hr' hla
      -- the binding back to the caller
      obtain ⟨hp3, hc3⟩ := markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      -- the summary edge
      obtain ⟨x, hx, rfl⟩ := applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := or_eq_false hra
      have haa := applyEdge_demand hx hxa
      have hfa := applyEdge_demand ha haa
      have hp2 : premOKB j.mark a.fact.mark = true := premOK_of_sub (applicable_markSub happ)
      have hc2 : concOKB g.fact.mark a.fact.mark = true :=
        concOK_of (fun hA => ihG.1 (gate_abs (applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hflG, hok1'⟩ := ihG.2 hga l1' l2 hdg hok2
      -- the binding into the callee
      obtain ⟨hp1, hc1⟩ := markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 hok1'
      obtain ⟨hflD, hok0⟩ := ihD.2 hfa l0 l1 hd1 hok1
      exact ⟨Flow.call hflD hE he1 hde1 hflG he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨fun hi => cleanRes_abs (ih.1 hi) hf, ?_⟩
    intro ha l0 l hd hok
    have hfa := cleanRes_demand hf ha
    obtain ⟨hd1, hcl⟩ := cleanRes_exact hf ha hd
    obtain ⟨hfl, hok0⟩ := ih.2 hfa l0 l hd1 hok
    exact ⟨Flow.clean hfl hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M i n f n' b may _ hE hp ih =>
    refine ⟨ih.1, ?_⟩
    intro ha l0 l hd hok
    obtain ⟨hfl, hok0⟩ := ih.2 ha l0 l hd hok
    refine ⟨Flow.filt hfl hE ?_, hok0⟩
    intro hb
    obtain ⟨-, hlb, -, -, -, σ, τ, -, hlp, -, -⟩ := hd
    exact hfo _ _ _ _ _ hE f.fact.path τ l (hp (hlb.symm.trans hb)) hlp hok hb

#print axioms D_edgeOK

/-- 5. THE EXACTNESS THEOREM. A normal-layer edge of the closure denotes only real flows.
    ROUND 5: the hypotheses `MarkWF P` and `FiltUp P` are new; without them the theorem is
    false (`cex_mark`, `cex_filt`). -/
theorem edge_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (hmw : MarkWF P) (hup : FiltUp P)
    (h : D P counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  ((D_edgeOK (ok := fun _ => True) hmw (filtUp_ok hup) (backOK_true P) h).2 ha l0 l hd trivial).1

#print axioms edge_exact

/-- 5v. THE EXACTNESS THEOREM FOR VALID LOCATIONS. The filters are prefix-closed type filters
    (no `FiltUp`). A location is valid (`ok`) if every filter accepts it, and the source of a
    valid location along a micro edge is valid. Then a normal-layer edge denotes only real
    flows to valid locations, and the start location is valid. -/
theorem edge_exact_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    {ok : Loc → Prop} (hmw : MarkWF P) (hv : FiltValid P ok) (hbo : BackOK P ok)
    (h : D P counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  (D_edgeOK hmw (filtValid_ok hv) hbo h).2 ha l0 l hd hok

#print axioms edge_exact_valid

/-- A complete fact is in the normal layer. -/
theorem complete_demand {f : AFact} (h : f.complete = true) : f.demand = false := by
  unfold AFact.complete at h
  cases hd : f.demand with
  | false => rfl
  | true =>
    rw [hd] at h
    cases h

#print axioms complete_demand

/-- 5'. A complete edge of the closure denotes only real flows (the hypotheses of
    `edge_exact`). -/
theorem complete_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (hmw : MarkWF P) (hup : FiltUp P)
    (h : D P counted L α sinks roots (.edge M i n f)) (hc : f.complete = true)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  edge_exact hmw hup h (complete_demand hc) hd

#print axioms complete_exact

/-! ## 6. Closed initial fact -/

/-- 6. A closed initial fact: if the exit edges of `i` cover every real flow and every
    exit edge of `i` is complete, then the exit edges of `i` are EXACTLY the real flows
    from the location set of `i`. This is the licence to reuse the persisted summaries
    of `i`. (The hypotheses of `edge_exact`.) -/
theorem closed_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact}
    (hmw : MarkWF P) (hup : FiltUp P)
    (hcov : ∀ l0 l, i.covers l0 → Flow P M l0 (P.exit M) l →
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l)
    (hcomp : ∀ g, D P counted L α sinks roots (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    Flow P M l0 (P.exit M) l ↔
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l :=
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ => edge_exact hmw hup hg (hcomp g hg) hd⟩

#print axioms closed_exact

/-- 6v. The closed initial fact for valid end locations (the hypotheses of `edge_exact_valid`). -/
theorem closed_exact_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {ok : Loc → Prop}
    (hmw : MarkWF P) (hv : FiltValid P ok) (hbo : BackOK P ok)
    (hcov : ∀ l0 l, i.covers l0 → Flow P M l0 (P.exit M) l →
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l)
    (hcomp : ∀ g, D P counted L α sinks roots (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) (hok : ok l) :
    Flow P M l0 (P.exit M) l ↔
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l :=
  ⟨hcov l0 l h0, fun ⟨g, hg, hd⟩ => (edge_exact_valid hmw hv hbo hg (hcomp g hg) hd hok).1⟩

#print axioms closed_exact_valid

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
  exact applyEdge_exact_wit rfl rfl rfl ex_applyEdge_mem rfl
    ⟨rfl, rfl, trivial, rfl, trivial, [1], [1], rfl, rfl, rfl, rfl, rfl⟩
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
  exact applyEdge_exact_wit rfl rfl rfl ex2_applyEdge_mem rfl
    ⟨rfl, rfl, trivial, rfl, trivial, [7], [9, 9], rfl, rfl, rfl, trivial⟩
#print axioms ex2_applyEdge_exact
-- With the exclusion {h} on the fact, `lostCorr` is true: the result is a demand fact.
theorem ex2_lostCorr :
    (applyEdge ⟨⟨12, [], .star (.set [3]), .star⟩, false⟩ exFr exTo2).facts
      = [⟨⟨11, [], .any, .star⟩, true⟩] := by decide

-- 1c. ROUND 5: the edge `a.f = b` on the cleaned fact `(b,.g,*,{h},*∖{5})`. The result
--     `(a,.f.g,*,{h},*∖{5})` keeps the exclusion; the witness gives `passes` for the mark 7.
def exC3 : AFact := ⟨⟨12, [2], .star (.set [3]), .starEx [5]⟩, false⟩
def exR3 : AFact := ⟨⟨11, [1, 2], .star (.set [3]), .starEx [5]⟩, false⟩
theorem ex3_applyEdge_mem : exR3 ∈ (applyEdge exC3 exFr exTo).facts := by decide
theorem ex3_applyEdge_exact :
    den exIc exC3.fact ⟨10, [1], 7⟩ (wit exIc exC3 exFr exTo ⟨10, [1], 7⟩ ⟨11, [1, 2, 1], 7⟩) ∧
      den exFr exTo (wit exIc exC3 exFr exTo ⟨10, [1], 7⟩ ⟨11, [1, 2, 1], 7⟩) ⟨11, [1, 2, 1], 7⟩ :=
  applyEdge_exact_wit rfl rfl rfl ex3_applyEdge_mem rfl
    ⟨rfl, rfl, trivial, rfl, (rfl : memB 7 [5] = false), [1], [1], rfl, rfl, rfl, rfl, rfl⟩
#print axioms ex3_applyEdge_exact

-- 2. Under the limit 2 the fact is complete and the limit is the identity.
--    Under the limit 0 the limit cuts: the result is a demand fact (`demand = true`).
#eval limitF (fun _ => true) 0 exC
theorem ex_limitF_exact : limitF (fun _ => true) 2 exC = exC := limitF_exact (by decide)
#print axioms ex_limitF_exact

-- 3. The start fact of `(x,.f,$,{},T)` is complete. Its only pair from `x.f` is `x.f`.
def exI3 : PFact := ⟨10, [1], .exact, .conc 5⟩
#eval startFact exI3
theorem ex_startFact_den : den exI3 (startFact exI3).fact ⟨10, [1], 5⟩ ⟨10, [1], 5⟩ :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
theorem ex_startFact_exact (l : Loc) (h : den exI3 (startFact exI3).fact ⟨10, [1], 5⟩ l) :
    l = ⟨10, [1], 5⟩ :=
  startFact_exact rfl h
#print axioms ex_startFact_exact

-- 4. ROUND 5: the cleaner of the mark 5 at `b.f` and below on the fact `(b,.,*,{},*)`. The
--    position is `part`: the fact continues as `(b,.,*,{},*∖{5})` and the mark 5 is requested.
--    A pair with the end mark 7 is a pair of the input, and the cleaner does not clean its end.
--    The end mark 5 is not in the result.
def exCl : Cleaner := ⟨12, [1], .atAndBelow, some 5⟩
def exClR : AFact := ⟨⟨12, [], .star (.set []), .starEx [5]⟩, false⟩
#eval cleanRes exCl exC2
theorem ex_clean_res : (cleanRes exCl exC2).facts = [exClR] ∧ (cleanRes exCl exC2).reqs = [5] := by
  decide
theorem ex_clean_mem : exClR ∈ (cleanRes exCl exC2).facts := by decide
theorem ex_cleanRes_exact :
    den exIc exC2.fact ⟨10, [1, 2], 7⟩ ⟨12, [1, 2], 7⟩ ∧ exCl.cleansB ⟨12, [1, 2], 7⟩ = false :=
  cleanRes_exact ex_clean_mem rfl
    ⟨rfl, rfl, trivial, rfl, (rfl : memB 7 [5] = false), [1, 2], [1, 2], rfl, rfl, rfl, rfl, rfl⟩
#print axioms ex_cleanRes_exact
theorem ex_clean_excl : ¬ den exIc exClR.fact ⟨10, [1, 2], 5⟩ ⟨12, [1, 2], 5⟩ := by
  intro h
  have h1 : memB 5 [5] = false := h.2.2.2.2.1
  exact absurd h1 (by decide)
-- The real flow of the mark 5 is cleaned: `b.f.g` with the mark 5 is in the reach.
theorem ex_clean_cleans : exCl.cleansB ⟨12, [1, 2], 5⟩ = true := by decide

/-! ## 8. Counterexamples to the version-4 statement of `edge_exact`

  Each program satisfies `Program.WF`. Each derivation is a derivation of `D` with a
  normal-layer edge. Its pair relation contains a pair that is not a real flow. -/

namespace CexFilt

/-- The type filter of the base `1`: only the path `[]` exists. It is prefix-closed. -/
def may (p : List Acc) : Bool := p.isEmpty
/-- A source: the zero fact gives `(1,.,[any],{},5)`. -/
def src : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 5⟩)
def s : Stmt := ⟨[zeroBase], [src]⟩
/-- One method `0`: the source, then the filter. -/
def P : Program := ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt s, 1), (0, 1, .filt 1 may, 2)]⟩
def f : AFact := ⟨⟨1, [], .any, .conc 5⟩, false⟩
/-- The location `1.7`: the filter rejects it. -/
def lEnd : Loc := ⟨1, [7], 5⟩

theorem wf : P.WF where
  stmtTouched := by
    intro M n s' n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  toStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  fromStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  filtPrefix := by
    intro M n b may' n' hE p q h
    cases hE with
    | tail _ h' =>
      cases h' with
      | head =>
        cases p with
        | nil => rfl
        | cons a p => cases h
      | tail _ h'' => cases h''

theorem markWF : MarkWF P where
  stmt := by
    intro M n s' n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem not_filtUp : ¬ FiltUp P := by
  intro h
  have h1 := h 0 1 1 may 2 (List.Mem.tail _ (List.Mem.head _)) [] [7] rfl
  exact absurd h1 (by decide)

theorem d_edge : D P (fun _ => true) 3 (fun _ a => a) [] [0] (.edge 0 zeroFact 2 f) := by
  have h0 : D P (fun _ => true) 3 (fun _ a => a) [] [0] (.init 0 zeroFact) :=
    D.root (List.Mem.head _)
  have h1 := D.start h0
  have h2 : D P (fun _ => true) 3 (fun _ a => a) [] [0] (.edge 0 zeroFact 1 f) :=
    D.step h1 (List.Mem.head _) (by decide)
  exact D.filt h2 (List.Mem.tail _ (List.Mem.head _)) (fun _ => rfl)

/-- Every flow to the node `2` passed the filter. -/
theorem flow_filt : ∀ {M l0 n l}, Flow P M l0 n l → n = 2 → l.base = 1 → may l.path = true := by
  intro M l0 n l h
  induction h with
  | start M l0 =>
    intro hn
    have h' : (0 : Nat) = 2 := hn
    exact absurd h' (by decide)
  | step _ hE _ _ =>
    intro hn
    cases hE with
    | head => exact absurd hn (by decide)
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | pass _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | clean _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  | filt _ hE hb _ =>
    intro _ hb1
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact hb hb1
      | tail _ h => cases h

/-- THE FILTER COUNTEREXAMPLE. The program is well formed and satisfies `MarkWF`. The edge
    `zeroFact → (1,.,[any],{},5)` at the node `2` is in the normal layer and denotes the pair
    `(0, 1.7)`, but no real flow reaches `1.7`: the filter rejects the path `.7`. -/
theorem cex_filt :
    D P (fun _ => true) 3 (fun _ a => a) [] [0] (.edge 0 zeroFact 2 f) ∧ f.demand = false ∧
    den zeroFact f.fact zeroLoc lEnd ∧ ¬ Flow P 0 zeroLoc 2 lEnd := by
  refine ⟨d_edge, rfl, ⟨rfl, rfl, rfl, rfl, trivial, [], [7], rfl, rfl, rfl, trivial⟩, ?_⟩
  intro h
  have h1 := flow_filt h rfl rfl
  exact absurd h1 (by decide)

end CexFilt

#print axioms CexFilt.wf
#print axioms CexFilt.cex_filt

namespace CexMark

/-- The binding of the zero base of method `1` to the base `1` of method `0`. -/
def bnd : MicroEdge := (⟨0, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def cc : Call := ⟨0, [0], [bnd], []⟩
/-- The cleaner of the mark `5` on the base `1` and everything below it. -/
def cl : Cleaner := ⟨1, [], .atAndBelow, some 5⟩
/-- A statement edge that gives the mark `9` to the base `2` from any mark of the base `1`. -/
def conv : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨2, [], .exact, .conc 9⟩)
def s : Stmt := ⟨[1], [conv]⟩
/-- The method `1` (a root) calls the method `0`. The method `0` cleans, then converts. -/
def P : Program :=
  ⟨fun _ => 0, fun _ => 2, [(1, 0, .call cc, 1), (0, 0, .clean cl, 1), (0, 1, .stmt s, 2)]⟩
/-- The run-1 abstraction policy (the empty demand). -/
def α : MethodId → PFact → PFact := policy (fun _ => [])
def ic : PFact := ⟨1, [], .star (.set []), .star⟩
def c1 : AFact := ⟨⟨1, [], .star (.set []), .starEx [5]⟩, false⟩
def r : AFact := ⟨⟨2, [], .exact, .conc 9⟩, false⟩
/-- The initial location with the mark `5`: the cleaner removes it. -/
def l0 : Loc := ⟨1, [], 5⟩
def l2 : Loc := ⟨2, [], 9⟩

theorem wf : P.WF where
  stmtTouched := by
    intro M n s' n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toStar := by
    intro M n c n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromStar := by
    intro M n c n' hE e he
    cases hE with
    | head => cases he
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  filtPrefix := by
    intro M n b may n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem filtUp : FiltUp P := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem not_markWF : ¬ MarkWF P := by
  intro h
  have h1 := h.stmt 0 1 s 2 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) conv
    (List.Mem.head _)
  exact absurd h1 (by decide)

theorem d_edge : D P (fun _ => true) 3 α [] [1] (.edge 0 ic 2 r) := by
  have h0 : D P (fun _ => true) 3 α [] [1] (.init 1 zeroFact) := D.root (List.Mem.head _)
  have h1 := D.start h0
  have h2 : D P (fun _ => true) 3 α [] [1] (.added 0 ⟨1, [], .exact, .conc 0⟩) :=
    D.added (a := ⟨⟨1, [], .exact, .conc 0⟩, false⟩) h1 (List.Mem.head _) (List.Mem.head _)
      (by decide)
  have h3 := D.initA h2
  have e : α 0 ⟨1, [], .exact, .conc 0⟩ = ic := by decide
  rw [e] at h3
  have h4 := D.start h3
  have h5 : D P (fun _ => true) 3 α [] [1] (.edge 0 ic 1 c1) :=
    D.clean h4 (List.Mem.tail _ (List.Mem.head _)) (by decide)
  exact D.step h5 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (by decide)

/-- In the method `0`, the location `l0` flows nowhere: the cleaner removes it. -/
theorem flow_stays : ∀ {M l0' n l}, Flow P M l0' n l → M = 0 → l0' = l0 → n = 0 ∧ l = l0' := by
  intro M l0' n l h
  induction h with
  | start M l0' => intro _ _; exact ⟨rfl, rfl⟩
  | step _ hE _ ih =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head => exact absurd (ih rfl hl).1 (by decide)
        | tail _ h => cases h
  | pass _ hE _ _ =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    intro hM
    cases hE with
    | head => exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | clean _ hE hcl ih =>
    intro hM hl
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        obtain ⟨-, rfl⟩ := ih rfl hl
        subst hl
        exact absurd hcl (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

/-- THE MARK COUNTEREXAMPLE. The program is well formed and satisfies `FiltUp` (it has no
    filter). The run-1 policy gives the initial fact `(1,.,*,{},*)` to the method `0`. The
    cleaner gives `(1,.,*,{},*∖{5})`; the edge `conv` gives `(2,.,$,{},9)` in the normal layer
    (`markComp (conc 9) (starEx [5]) = some (conc 9)`). This edge denotes the pair
    `(1 with 5, 2 with 9)`, but the cleaner removed the location `1` with the mark `5`, so no
    real flow exists. -/
theorem cex_mark :
    D P (fun _ => true) 3 α [] [1] (.edge 0 ic 2 r) ∧ r.demand = false ∧
    den ic r.fact l0 l2 ∧ ¬ Flow P 0 l0 2 l2 := by
  refine ⟨d_edge, rfl, ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩, ?_⟩
  intro h
  exact absurd (flow_stays h rfl rfl).1 (by decide)

end CexMark

#print axioms CexMark.wf
#print axioms CexMark.cex_mark

end ApSpec.Exact
