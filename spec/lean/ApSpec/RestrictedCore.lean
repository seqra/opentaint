/-
  ApSpec.RestrictedCore — the local lemmas of the restricted-run rules
  (`Restricted.lean`): the emission table, the satisfaction of a premise and the
  restriction of a summary edge by a demand edge.

  Main results of version 4 (the spec rules `emitM`, `satO`, `restrictU`;
  constructive; see the `#print axioms` lines):
   V4.1 `meetK_tailI`         the meet of two tails admits what both tails admit.
   V4.2 `emitM_contract`      THE MAIN RESULT: the mark-aware emission serves every demanded
                              location of a CONCRETE added fact (`EmitContractConc`).
        `emitM_not_full`      the full contract (`EmitContract`, every added fact) is false for
                              `emitM`: a `*` added fact with a `T` demand gets nothing. So the
                              coverage proof needs the concreteness of the run.
   V4.3 `satO_contract`       the overlap satisfaction keeps the contract.
   V4.4 `emitM_mark`, `emitM_base`, `emitM_copies`   the emission keeps the mark and the base of
                              the added fact (`EmitCopiesMark emitM`).
   V4.5 `emitM_inter`         the emission is EXACTLY the intersection `a ∩ D-c` (as locations).
   V4.6 `emitM_complete`      the emission loses nothing when the marks match.
   V4.7 `emitM_shape`, `emitM_chain`, `emitM_chain_strong`   the emitted chain is the chain of
                              the added fact, or the demand chain below it.
   V4.8 `restrictU_eq_S_nonstar`   the two restrictions agree on a conclusion without `*`.
   Also: `emitM_sat` (the added fact satisfies its emission), `emitM_serves`, `emitM_cases`.

  Results of version 3 (kept as the record of the review):
    1. `emitS_contract`      the sound emission table serves every demanded location.
    2. `emitU_fails`         the agreed emission table does not (a `*` fact above the
                             demand chain). `emitS_vector` is the positive vector.
    3. `satS_contract`, `satU_contract`   both satisfaction rules keep the contract.
    4. `restrictS_contract`  the sound restriction keeps every demanded pair.
    5. `restrictU_fails`     the agreed restriction does not (a correlated `*`
                             conclusion above `D-p`). `restrictS_vector` is the vector.
    6. `restrictS_sub`, `restrictU_sub`   the restriction only removes pairs.
    7. `restrictS_shape`     a restricted conclusion is the edge or an uncorrelated one.
    8. `summary_stepR`       a satisfied premise raises no request.
    9. `emitS_shape`, `emitS_premEmpty`, `emitU_shape`, `emitU_premEmpty`, `emitU_emitS`.
   10. `satU_satS`, `applicable_satU`.
-/
import ApSpec.Restricted
import ApSpec.Core
import ApSpec.Reverse
import ApSpec.Store
import ApSpec.Invariant

namespace ApSpec.RCore
open ApSpec

/-! ## 0. Helpers -/

/-- `relate p q = .above r` gives `p = q ++ r`. -/
theorem relate_above_path {p q r : List Acc} : relate p q = .above r → p = q ++ r := by
  intro h
  unfold relate at h
  cases h1 : dropPrefix p q with
  | some r' =>
    rw [h1] at h
    exact Rel.noConfusion h
  | none =>
    rw [h1] at h
    cases h2 : dropPrefix q p with
    | some r' =>
      rw [h2] at h
      have hr : r' = r := Rel.above.inj h
      rw [← hr]
      exact CoreAux.dropPrefix_some.mp h2
    | none =>
      rw [h2] at h
      exact Rel.noConfusion h

/-- A tail with an empty exclusion contains every tail at the same position. -/
theorem tailSubB_starEmpty (k : Kind) : tailSubB (.star Excl.empty) k = true := by
  cases k with
  | star e => cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- The chain fact covers every location below its path. -/
theorem chain_covers {d : PFact} {l : Loc} {p s : List Acc}
    (hb : l.base = d.base) (hp : l.path = p ++ s) : (chainFact d p).covers l :=
  ⟨hb, ⟨s, hp, CoreAux.empty_admits s⟩, trivial⟩

/-- The chain fact is applicable to every fact at or below its path. -/
theorem applicable_chain {d a : PFact} {p r : List Acc} (hb : Nat.beq d.base a.base = true)
    (hd : dropPrefix p a.path = some r) : applicable (chainFact d p) a = true := by
  unfold applicable coversB chainFact
  dsimp only
  rw [hb, hd]
  cases r with
  | nil => rw [tailSubB_starEmpty]; rfl
  | cons x r => rfl

theorem satU_of_applicable {j a : PFact} (h : applicable j a = true) : satU j a = true := by
  unfold satU
  rw [h]
  rfl

theorem satS_of_satU {j a : PFact} (h : satU j a = true) : satS j a = true := by
  unfold satS
  rw [h]
  rfl

theorem satU_of_anyAbove {j a : PFact} (hb : Nat.beq j.base a.base = true)
    (hk : a.kind.isAny = true) (hm : markSubB j.mark a.mark = true) (hab : aboveB j a = true) :
    satU j a = true := by
  unfold satU
  rw [Bool.or_eq_true]
  right
  rw [hb, hk, hm, hab]
  rfl

theorem satS_of_starAbove {j a : PFact} {x : Acc} {r : List Acc}
    (hb : Nat.beq j.base a.base = true) (hk : a.kind.isStar = true)
    (hm : markSubB j.mark a.mark = true) (hd : dropPrefix a.path j.path = some (x :: r))
    (ht : admitsTailB a.kind (x :: r) = true) : satS j a = true := by
  unfold satS
  rw [Bool.or_eq_true]
  right
  rw [hb, hk, hm, hd]
  exact ht

/-! ## 1. The sound emission table serves every demanded location -/

/-- A pattern that covers a location (with its mark) covers it as a location. -/
theorem covers_coversLoc {d : PFact} {l : Loc} (h : d.covers l) : d.coversLoc l :=
  ⟨h.1, h.2.1⟩

theorem emitS_contract : EmitContract emitS satS := by
  intro d a l hd ha
  obtain ⟨hbd, ⟨σ, hpd, htd⟩, _⟩ := hd
  obtain ⟨hba, ⟨τ, hpa, hta⟩, _⟩ := ha
  have hb : Nat.beq d.base a.base = true := by rw [← hbd, ← hba]; exact Nat.beq_refl _
  have hpath : d.path ++ σ = a.path ++ τ := by rw [← hpd, ← hpa]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, hq, hσ⟩ | ⟨r, hrel, hP, hr, hτ⟩
  · -- the added fact is at or below the demand chain
    cases r with
    | cons g r' =>
      have hg : admitsTailB d.kind [g] = true := by
        rw [hσ] at htd
        exact CoreAux.tailI_append_admits (r := [g]) (s := r' ++ τ) htd
      have hdp : dropPrefix (d.path ++ [g]) a.path = some r' :=
        CoreAux.dropPrefix_some.mpr (by rw [hq, List.append_assoc]; rfl)
      refine ⟨chainFact d (d.path ++ [g]), ?_, ?_, ?_⟩
      · unfold emitS
        rw [if_pos hb, hrel]
        show (if admitsTailB d.kind [g] = true then _ else _) = _
        rw [if_pos hg]
      · exact chain_covers hbd (by rw [hpd, hσ, List.append_assoc]; rfl)
      · exact satS_of_satU (satU_of_applicable (applicable_chain hb hdp))
    | nil =>
      have hdp : dropPrefix d.path a.path = some [] := CoreAux.dropPrefix_some.mpr hq
      have hστ : σ = τ := hσ
      cases hk : a.kind with
      | exact =>
        rw [hk] at hta
        have hτ0 : τ = [] := hta
        refine ⟨⟨d.base, d.path, .exact, .star⟩, ?_, ?_, ?_⟩
        · unfold emitS
          rw [if_pos hb, hrel, hk]
        · refine ⟨hbd, ⟨σ, hpd, ?_⟩, trivial⟩
          show σ = []
          rw [hστ, hτ0]
        · apply satS_of_satU
          apply satU_of_applicable
          unfold applicable coversB
          dsimp only
          rw [hb, hdp, hk]
          rfl
      | any =>
        refine ⟨⟨d.base, d.path, .any, .star⟩, ?_, ?_, ?_⟩
        · unfold emitS
          rw [if_pos hb, hrel, hk]
        · exact ⟨hbd, ⟨σ, hpd, trivial⟩, trivial⟩
        · apply satS_of_satU
          apply satU_of_applicable
          unfold applicable coversB
          dsimp only
          rw [hb, hdp, hk]
          rfl
      | star e =>
        refine ⟨chainFact d d.path, ?_, ?_, ?_⟩
        · unfold emitS
          rw [if_pos hb, hrel, hk]
        · exact chain_covers hbd hpd
        · exact satS_of_satU (satU_of_applicable (applicable_chain hb hdp))
  · -- the added fact is above the demand chain
    cases r with
    | nil => exact absurd rfl hr
    | cons x r' =>
      have hdp : dropPrefix a.path d.path = some (x :: r') := CoreAux.dropPrefix_some.mpr hP
      cases hk : a.kind with
      | exact =>
        rw [hk] at hta
        have hτ0 : τ = [] := hta
        rw [hτ0] at hτ
        exact absurd hτ.symm (List.cons_ne_nil x (r' ++ σ))
      | any =>
        refine ⟨chainFact d d.path, ?_, chain_covers hbd hpd, ?_⟩
        · unfold emitS
          rw [if_pos hb, hrel, hk]
        · apply satS_of_satU
          apply satU_of_anyAbove (j := chainFact d d.path) hb (by rw [hk]; rfl) rfl
          show (match dropPrefix a.path d.path with
            | some (_ :: _) => true
            | _ => false) = true
          rw [hdp]
      | star e =>
        rw [hk, hτ] at hta
        have he : e.admits (x :: r') = true :=
          CoreAux.tailI_append_admits (k := .star e) (r := x :: r') (s := σ) hta
        refine ⟨chainFact d d.path, ?_, chain_covers hbd hpd, ?_⟩
        · unfold emitS
          rw [if_pos hb, hrel, hk]
          show (if e.admits (x :: r') = true then _ else _) = _
          rw [if_pos he]
        · exact satS_of_starAbove (j := chainFact d d.path) hb (by rw [hk]; rfl) rfl hdp (by rw [hk]; exact he)

#print axioms emitS_contract

/-! ## 2. The agreed emission table does not serve every demanded location -/

/-- The witness: the demand chain `[1,4]` with the `[any]` tail, and a `*` added fact
    `[1]` above it. The location `[1,4,5]` is demanded and the added fact carries it. -/
def wD : PFact := ⟨3, [1, 4], .any, .star⟩
def wA : PFact := ⟨3, [1], .star (.set []), .star⟩
def wL : Loc := ⟨3, [1, 4, 5], 1⟩

theorem emitU_witness_none : emitU wD wA = none := by decide

/-- The positive vector: the sound table emits the demand chain. -/
theorem emitS_vector : emitS wD wA = some ⟨3, [1, 4], .star (.set []), .star⟩ := by decide

/-- The demand mark of the witness is `*`, so the demand covers the location with its mark. -/
theorem emitU_fails : ∀ sat, ¬ EmitContract emitU sat := by
  intro sat h
  have hd : wD.covers wL := ⟨rfl, ⟨[5], rfl, trivial⟩, trivial⟩
  have ha : wA.covers wL := ⟨rfl, ⟨[4, 5], rfl, rfl⟩, trivial⟩
  obtain ⟨j, hj, _, _⟩ := h wD wA wL hd ha
  rw [emitU_witness_none] at hj
  cases hj

#print axioms emitS_vector
#print axioms emitU_fails

/-! ## 3. The satisfaction contracts -/

theorem answerInit_base {i a : PFact} {t : Mark} : (answerInit i a t).base = i.base := by
  unfold answerInit
  split <;> rfl

theorem answerInit_path {i a : PFact} {t : Mark} : (answerInit i a t).path = i.path := by
  unfold answerInit
  split <;> rfl

theorem applicable_markSub {j a : PFact} (h : applicable j a = true) :
    markSubB j.mark a.mark = true := by
  unfold applicable coversB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1.2

/-- The mark part of the answer: `conc t` admits the fact mark `conc t`. -/
theorem markSub_answer {j a : PFact} {t : Mark} (ham : a.mark = .conc t) :
    markSubB (answerInit j a t).mark a.mark = true := by
  rw [answerInit_mark, ham]
  exact Nat.beq_refl t

/-- The `[any]`-above disjunct of `satU`, as one boolean. -/
theorem satU_cases {j a : PFact} (h : satU j a = true) :
    applicable j a = true ∨
    (Nat.beq j.base a.base = true ∧ a.kind.isAny = true ∧ markSubB j.mark a.mark = true ∧
      aboveB j a = true) := by
  unfold satU at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hb, hk⟩, hm⟩, hab⟩ := h
    exact Or.inr ⟨hb, hk, hm, hab⟩

theorem satS_cases {j a : PFact} (h : satS j a = true) :
    satU j a = true ∨
    (Nat.beq j.base a.base = true ∧ a.kind.isStar = true ∧ markSubB j.mark a.mark = true ∧
      (match dropPrefix a.path j.path with
       | some (x :: r) => admitsTailB a.kind (x :: r)
       | _ => false) = true) := by
  unfold satS at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hb, hk⟩, hm⟩, hd⟩ := h
    exact Or.inr ⟨hb, hk, hm, hd⟩

theorem satU_contract : SatContract satU := by
  refine ⟨?_, ?_⟩
  · intro j a h
    rcases satU_cases h with h | ⟨_, _, hm, _⟩
    · exact applicable_markSub h
    · exact hm
  · intro j a t h ham
    rcases satU_cases h with h | ⟨hb, hk, _, hab⟩
    · exact satU_of_applicable (answerInit_applicable h ham)
    · apply satU_of_anyAbove _ hk (markSub_answer ham)
      · unfold aboveB
        rw [answerInit_path]
        exact hab
      · rw [answerInit_base]
        exact hb

theorem satS_contract : SatContract satS := by
  refine ⟨?_, ?_⟩
  · intro j a h
    rcases satS_cases h with h | ⟨_, _, hm, _⟩
    · exact satU_contract.1 j a h
    · exact hm
  · intro j a t h ham
    rcases satS_cases h with h | ⟨hb, hk, _, hd⟩
    · exact satS_of_satU (satU_contract.2 j a t h ham)
    · unfold satS
      rw [Bool.or_eq_true]
      right
      rw [answerInit_base, answerInit_path, hb, hk, markSub_answer ham]
      exact hd

#print axioms satU_contract
#print axioms satS_contract

/-! ## 4. The restriction: helpers -/

/-- The tail of an uncorrelated restricted conclusion: `$` for a `$` exit pattern,
    `[any]` otherwise. -/
def outKind (k : Kind) : Kind :=
  match k with
  | .exact => .exact
  | _ => .any

theorem outKind_cases (k : Kind) : outKind k = .any ∨ outKind k = .exact := by
  cases k with
  | star e => exact Or.inl rfl
  | any => exact Or.inl rfl
  | exact => exact Or.inr rfl

theorem coversLoc_of_den {i f : PFact} {l0 l1 : Loc} (h : den i f l0 l1) : i.coversLoc l0 := by
  obtain ⟨hb0, _, _, _, σ, _, hp0, _, hti, _⟩ := h
  exact ⟨hb0, σ, hp0, hti⟩

/-- Two patterns with a common location overlap (marks are ignored). -/
theorem overlapB_of_commonLoc {a b : PFact} {l : Loc} :
    a.coversLoc l → b.coversLoc l → overlapB a b = true := by
  intro ha hb
  obtain ⟨hba, σa, hpa, hta⟩ := ha
  obtain ⟨hbb, σb, hpb, htb⟩ := hb
  unfold overlapB
  rw [Bool.and_eq_true]
  refine ⟨by rw [← hba, ← hbb]; exact Nat.beq_refl _, ?_⟩
  have h : a.path ++ σa = b.path ++ σb := by rw [← hpa, ← hpb]
  rcases CoreAux.relate_common h with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, _, hτ⟩
  · rw [hrel]
    rw [hσ] at hta
    exact CoreAux.tailI_append_admits hta
  · rw [hrel]
    rw [hτ] at htb
    exact CoreAux.tailI_append_admits htb

theorem restrictWith_some {rc : AFact → PFact → Option AFact} {sp : PFact} {sc g' : AFact}
    {d : DemandEdge} (h : restrictWith rc sp sc d = some g') :
    ∃ p, d.dout = some p ∧ overlapB sp d.din = true ∧ rc sc p = some g' := by
  unfold restrictWith at h
  cases hd : d.dout with
  | none =>
    rw [hd] at h
    cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases ho : overlapB sp d.din with
    | false =>
      rw [ho, if_neg Bool.false_ne_true] at h
      cases h
    | true =>
      rw [ho, if_pos rfl] at h
      exact ⟨p, rfl, rfl, h⟩

theorem restrictWith_of {rc : AFact → PFact → Option AFact} {sp : PFact} {sc : AFact}
    {d : DemandEdge} {p : PFact} (hd : d.dout = some p) (ho : overlapB sp d.din = true) :
    restrictWith rc sp sc d = rc sc p := by
  unfold restrictWith
  rw [hd]
  dsimp only
  rw [if_pos ho]

/-- The sound conclusion restriction keeps the edge, or gives the uncorrelated
    conclusion at the exit pattern for an `[any]` conclusion above it. -/
theorem restrictConcS_cases {sc g' : AFact} {p : PFact} (h : restrictConcS sc p = some g') :
    g' = sc ∨ (∃ r, p.path = sc.fact.path ++ r ∧ sc.fact.kind = .any ∧
      g' = ⟨⟨sc.fact.base, p.path, outKind p.kind, sc.fact.mark⟩, sc.demand⟩) := by
  unfold restrictConcS at h
  cases hb : Nat.beq sc.fact.base p.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    cases h
  | true =>
    rw [hb, if_pos rfl] at h
    cases hr : relate p.path sc.fact.path with
    | below r =>
      rw [hr] at h
      dsimp only at h
      cases ha : admitsTailB p.kind r with
      | false =>
        rw [ha, if_neg Bool.false_ne_true] at h
        cases h
      | true =>
        rw [ha, if_pos rfl] at h
        exact Or.inl (Option.some.inj h).symm
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases hk : sc.fact.kind with
      | star e =>
        rw [hk] at h
        dsimp only at h
        cases he : e.admits r with
        | false =>
          rw [he, if_neg Bool.false_ne_true] at h
          cases h
        | true =>
          rw [he, if_pos rfl] at h
          exact Or.inl (Option.some.inj h).symm
      | any =>
        rw [hk] at h
        refine Or.inr ⟨r, relate_above_path hr, rfl, ?_⟩
        rw [← Option.some.inj h]
        cases p.kind <;> rfl
      | exact =>
        rw [hk] at h
        cases h
    | apart =>
      rw [hr] at h
      cases h

/-- The agreed conclusion restriction is a part of the sound one. -/
theorem restrictConcU_sub {sc g' : AFact} {p : PFact} (h : restrictConcU sc p = some g') :
    restrictConcS sc p = some g' := by
  unfold restrictConcU at h
  unfold restrictConcS
  cases hb : Nat.beq sc.fact.base p.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    cases h
  | true =>
    rw [hb, if_pos rfl] at h
    rw [if_pos rfl]
    cases hr : relate p.path sc.fact.path with
    | below r =>
      rw [hr] at h
      exact h
    | above r =>
      rw [hr] at h
      cases hk : sc.fact.kind with
      | star e =>
        rw [hk] at h
        cases h
      | any =>
        rw [hk] at h
        exact h
      | exact =>
        rw [hk] at h
        cases h
    | apart =>
      rw [hr] at h
      cases h

/-- The restriction only removes pairs, and keeps the layer (conclusion part). -/
theorem restrictConcS_sub {sc g' : AFact} {p : PFact} (h : restrictConcS sc p = some g') :
    g'.demand = sc.demand ∧ ∀ (j : PFact) l1 l2, den j g'.fact l1 l2 → den j sc.fact l1 l2 := by
  rcases restrictConcS_cases h with h | ⟨r, hP, hk, h⟩
  · subst h
    exact ⟨rfl, fun _ _ _ hd => hd⟩
  · subst h
    refine ⟨rfl, ?_⟩
    intro j l1 l2 hd
    obtain ⟨hb1, hb2, hm1, hm2, σ, τ, hp1, hp2, hti, _⟩ := hd
    refine ⟨hb1, hb2, hm1, hm2, σ, r ++ τ, hp1, ?_, hti, ?_⟩
    · rw [hp2]
      show p.path ++ τ = sc.fact.path ++ (r ++ τ)
      rw [hP, List.append_assoc]
    · rw [hk]
      trivial

/-! ## 4. The sound restriction keeps every demanded pair -/

theorem restrictS_contract : RestrictContract restrictS := by
  intro j g d p l1 l2 hden hdin hdout hp
  have hov : overlapB j d.din = true := overlapB_of_commonLoc (coversLoc_of_den hden) hdin
  have hR : restrictS j g d = restrictConcS g p := restrictWith_of hdout hov
  rw [hR]
  have hden0 := hden
  obtain ⟨hb1, hb2, hm1, hm2, σ, τ, hp1, hp2, hti, htf⟩ := hden
  obtain ⟨hbp, σ', hpp, htp⟩ := hp
  have hb : Nat.beq g.fact.base p.base = true := by rw [← hb2, ← hbp]; exact Nat.beq_refl _
  have hpath : p.path ++ σ' = g.fact.path ++ τ := by rw [← hpp, ← hp2]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, hr, hτ⟩
  · -- the conclusion is at or below the exit pattern: keep the edge
    have ha : admitsTailB p.kind r = true := by
      rw [hσ] at htp
      exact CoreAux.tailI_append_admits htp
    refine ⟨g, ?_, hden0, rfl⟩
    unfold restrictConcS
    rw [if_pos hb, hrel]
    show (if admitsTailB p.kind r = true then _ else _) = _
    rw [if_pos ha]
  · -- the conclusion is above the exit pattern
    cases hk : g.fact.kind with
    | star e =>
      -- correlated: the continuation is the initial one, so `e` admits `r`
      rw [hk] at htf
      obtain ⟨hτσ, he⟩ := htf
      have her : e.admits r = true := by
        rw [← hτσ, hτ] at he
        exact CoreAux.tailI_append_admits (k := .star e) he
      refine ⟨g, ?_, hden0, rfl⟩
      unfold restrictConcS
      rw [if_pos hb, hrel, hk]
      show (if e.admits r = true then _ else _) = _
      rw [if_pos her]
    | any =>
      -- uncorrelated: the new conclusion is the exit pattern
      refine ⟨⟨⟨g.fact.base, p.path, outKind p.kind, g.fact.mark⟩, g.demand⟩, ?_, ?_, rfl⟩
      · unfold restrictConcS
        rw [if_pos hb, hrel, hk]
        dsimp only
        cases p.kind <;> rfl
      · refine ⟨hb1, hb2, hm1, hm2, σ, σ', hp1, hpp, hti, ?_⟩
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

#print axioms restrictS_contract

/-! ## 5. The agreed restriction loses a demanded pair -/

/-- The witness: the summary edge `1.[2,3,1].* -> 2.[1].*` (correlated), the demand
    edge `1.[2,3].[any] -> 2.[1,4].[any]`, and the pair `1.[2,3,1,4,5] -> 2.[1,4,5]`.
    The conclusion `2.[1].*` is above the exit pattern `2.[1,4]`. -/
def wJ : PFact := ⟨1, [2, 3, 1], .star (.set []), .star⟩
def wG : AFact := ⟨⟨2, [1], .star (.set []), .star⟩, false⟩
def wP : PFact := ⟨2, [1, 4], .any, .star⟩
def wDE : DemandEdge := ⟨⟨1, [2, 3], .any, .star⟩, some wP⟩
def wL1 : Loc := ⟨1, [2, 3, 1, 4, 5], 7⟩
def wL2 : Loc := ⟨2, [1, 4, 5], 7⟩

theorem restrictU_witness_none : restrictU wJ wG wDE = none := by decide

/-- The positive vector: the sound restriction keeps the edge. -/
theorem restrictS_vector : restrictS wJ wG wDE = some wG := by decide

theorem wDen : den wJ wG.fact wL1 wL2 :=
  ⟨rfl, rfl, trivial, rfl, [4, 5], [4, 5], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

theorem restrictU_fails : ¬ RestrictContract restrictU := by
  intro h
  have hdin : wDE.din.coversLoc wL1 := ⟨rfl, [1, 4, 5], rfl, trivial⟩
  have hp : wP.coversLoc wL2 := ⟨rfl, [5], rfl, trivial⟩
  obtain ⟨g', hg', _, _⟩ := h wJ wG wDE wP wL1 wL2 wDen hdin rfl hp
  rw [restrictU_witness_none] at hg'
  cases hg'

#print axioms restrictS_vector
#print axioms restrictU_fails

/-! ## 6. The restriction only removes pairs -/

theorem restrictS_sub : RestrictSub restrictS := by
  intro j g d g' h
  obtain ⟨p, _, _, hc⟩ := restrictWith_some h
  obtain ⟨hdem, hsub⟩ := restrictConcS_sub hc
  exact ⟨hdem, fun l1 l2 hd => hsub j l1 l2 hd⟩

/-- The agreed restriction is a part of the sound one. -/
theorem restrictU_restrictS {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictU j g d = some g') : restrictS j g d = some g' := by
  obtain ⟨p, hd, ho, hc⟩ := restrictWith_some h
  show restrictWith restrictConcS j g d = some g'
  rw [restrictWith_of hd ho]
  exact restrictConcU_sub hc

theorem restrictU_sub : RestrictSub restrictU := by
  intro j g d g' h
  exact restrictS_sub j g d g' (restrictU_restrictS h)

#print axioms restrictS_sub
#print axioms restrictU_sub

/-! ## 7. The shape of a restricted conclusion -/

theorem restrictS_shape {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictS j g d = some g') :
    g' = g ∨ (g'.fact.kind = .any ∨ g'.fact.kind = .exact) := by
  obtain ⟨p, _, _, hc⟩ := restrictWith_some h
  rcases restrictConcS_cases hc with h | ⟨_, _, _, h⟩
  · exact Or.inl h
  · subst h
    exact Or.inr (outKind_cases p.kind)

theorem restrictU_shape {j : PFact} {g g' : AFact} {d : DemandEdge}
    (h : restrictU j g d = some g') :
    g' = g ∨ (g'.fact.kind = .any ∨ g'.fact.kind = .exact) :=
  restrictS_shape (restrictU_restrictS h)

#print axioms restrictS_shape
#print axioms restrictU_shape

/-! ## 8. A satisfied premise raises no request -/

/-- The application of a summary whose premise the fact satisfies covers the composed
    pair: the premise mark admits the fact mark, so the mark gate raises no request. -/
theorem summary_stepR {sat : PFact → PFact → Bool} (hsc : SatContract sat)
    {i j : PFact} {a g : AFact} {l0 l1 l2 : Loc}
    (hs : sat j a.fact = true) (hda : den i a.fact l0 l1) (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    have hm := hsc.1 j a.fact hs
    rw [hst] at hm
    have hreq : (applySummary a j g).reqs = (applyEdge a j g.fact).reqs := rfl
    cases hj : j.mark with
    | star =>
      rw [hreq, applyEdge_reqs_of_star hj] at hq
      cases hq
    | conc t =>
      rw [hj] at hm
      cases hm

#print axioms summary_stepR

/-! ## 9. The shape of an emitted initial fact -/

/-- The four rows of the sound emission table. -/
theorem emitS_cases {d a j : PFact} (h : emitS d a = some j) :
    j = chainFact d d.path ∨ (∃ x, j = chainFact d (d.path ++ [x])) ∨
    j = ⟨d.base, d.path, .exact, .star⟩ ∨ j = ⟨d.base, d.path, .any, .star⟩ := by
  unfold emitS at h
  cases hb : Nat.beq d.base a.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    cases h
  | true =>
    rw [hb, if_pos rfl] at h
    cases hr : relate d.path a.path with
    | below r =>
      rw [hr] at h
      cases r with
      | cons g r' =>
        dsimp only at h
        cases hg : admitsTailB d.kind [g] with
        | false =>
          rw [hg, if_neg Bool.false_ne_true] at h
          cases h
        | true =>
          rw [hg, if_pos rfl] at h
          exact Or.inr (Or.inl ⟨g, (Option.some.inj h).symm⟩)
      | nil =>
        dsimp only at h
        cases hk : a.kind with
        | exact =>
          rw [hk] at h
          exact Or.inr (Or.inr (Or.inl (Option.some.inj h).symm))
        | any =>
          rw [hk] at h
          exact Or.inr (Or.inr (Or.inr (Option.some.inj h).symm))
        | star e =>
          rw [hk] at h
          exact Or.inl (Option.some.inj h).symm
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases hk : a.kind with
      | exact =>
        rw [hk] at h
        cases h
      | any =>
        rw [hk] at h
        exact Or.inl (Option.some.inj h).symm
      | star e =>
        rw [hk] at h
        dsimp only at h
        cases he : e.admits r with
        | false =>
          rw [he, if_neg Bool.false_ne_true] at h
          cases h
        | true =>
          rw [he, if_pos rfl] at h
          exact Or.inl (Option.some.inj h).symm
    | apart =>
      rw [hr] at h
      cases h

/-- The agreed emission table is a part of the sound one. -/
theorem emitU_emitS {d a j : PFact} (h : emitU d a = some j) : emitS d a = some j := by
  unfold emitU at h
  unfold emitS
  cases hb : Nat.beq d.base a.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    cases h
  | true =>
    rw [hb, if_pos rfl] at h
    rw [if_pos rfl]
    cases hr : relate d.path a.path with
    | below r =>
      rw [hr] at h
      cases r with
      | cons g r' => exact h
      | nil => exact h
    | above r =>
      rw [hr] at h
      cases hk : a.kind with
      | exact =>
        rw [hk] at h
        cases h
      | any =>
        rw [hk] at h
        exact h
      | star e =>
        rw [hk] at h
        cases h
    | apart =>
      rw [hr] at h
      cases h

/-- An emitted initial fact is on the demand chain, or one accessor below it (no field
    chain without a demand). Its mark is `*` and its tail is `*{}`, `[any]` or `$`. -/
theorem emitS_shape {d a j : PFact} (h : emitS d a = some j) :
    j.base = d.base ∧ j.mark = .star ∧
      (j.path = d.path ∨ ∃ x, j.path = d.path ++ [x]) ∧
      (j.kind = .star Excl.empty ∨ j.kind = .any ∨ j.kind = .exact) := by
  rcases emitS_cases h with h | ⟨x, h⟩ | h | h <;> subst h
  · exact ⟨rfl, rfl, Or.inl rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, Or.inr ⟨x, rfl⟩, Or.inl rfl⟩
  · exact ⟨rfl, rfl, Or.inl rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨rfl, rfl, Or.inl rfl, Or.inr (Or.inl rfl)⟩

/-- An emitted initial fact has the empty premise exclusion (its records reverse exactly,
    `Reverse.rev_exact_of_empty_premise`). -/
theorem emitS_premEmpty {d a j : PFact} (h : emitS d a = some j) :
    Reverse.PremEmpty j.kind := by
  rcases (emitS_shape h).2.2.2 with hk | hk | hk <;> rw [hk]
  · rfl
  · trivial
  · trivial

theorem emitU_shape {d a j : PFact} (h : emitU d a = some j) :
    j.base = d.base ∧ j.mark = .star ∧
      (j.path = d.path ∨ ∃ x, j.path = d.path ++ [x]) ∧
      (j.kind = .star Excl.empty ∨ j.kind = .any ∨ j.kind = .exact) :=
  emitS_shape (emitU_emitS h)

theorem emitU_premEmpty {d a j : PFact} (h : emitU d a = some j) :
    Reverse.PremEmpty j.kind :=
  emitS_premEmpty (emitU_emitS h)

#print axioms emitS_cases
#print axioms emitU_emitS
#print axioms emitS_shape
#print axioms emitS_premEmpty
#print axioms emitU_shape
#print axioms emitU_premEmpty

/-! ## 10. The agreed satisfaction is a part of the sound one -/

theorem satU_satS {j a : PFact} (h : satU j a = true) : satS j a = true := satS_of_satU h

theorem applicable_satU {j a : PFact} (h : applicable j a = true) : satU j a = true :=
  satU_of_applicable h

#print axioms satU_satS
#print axioms applicable_satU

/-! # Version 4: the mark-aware emission `emitM`, the satisfaction `satO` -/

/-! ## 11. Helpers -/

/-- `relate p q = .below r` gives `q = p ++ r`. -/
theorem relate_below_path {p q r : List Acc} : relate p q = .below r → q = p ++ r := by
  intro h
  unfold relate at h
  cases h1 : dropPrefix p q with
  | some r' =>
    rw [h1] at h
    have hr : r' = r := Rel.below.inj h
    rw [← hr]
    exact CoreAux.dropPrefix_some.mp h1
  | none =>
    rw [h1] at h
    cases h2 : dropPrefix q p with
    | some r' =>
      rw [h2] at h
      exact Rel.noConfusion h
    | none =>
      rw [h2] at h
      exact Rel.noConfusion h

/-- `relate p q = .above r` gives `p = q ++ r` with a non-empty `r`. -/
theorem relate_above_ne {p q r : List Acc} : relate p q = .above r → r ≠ [] := by
  intro h hr0
  have hP := relate_above_path h
  unfold relate at h
  cases h1 : dropPrefix p q with
  | some r' =>
    rw [h1] at h
    exact Rel.noConfusion h
  | none =>
    have h0 : dropPrefix p q = some [] :=
      CoreAux.dropPrefix_some.mpr (by rw [hP, hr0, List.append_nil, List.append_nil])
    rw [h1] at h0
    cases h0

theorem relate_self (p : List Acc) : relate p p = .below [] :=
  CoreAux.relate_below (CoreAux.dropPrefix_some.mpr (List.append_nil p).symm)

/-- Every tail admits the empty continuation. -/
theorem admitsTailB_nil (k : Kind) : admitsTailB k [] = true := by
  cases k with
  | star e => exact CoreAux.admits_nil e
  | any => rfl
  | exact => rfl

theorem markSubB_refl (m : MarkA) : markSubB m m = true := by
  cases m with
  | star => rfl
  | conc t => exact Nat.beq_refl t

/-- The mark match of the emission is the mark inclusion of the premise. -/
theorem markMatchB_eq_markSubB (m1 m2 : MarkA) : markMatchB m1 m2 = markSubB m1 m2 := by
  cases m1 <;> cases m2 <;> rfl

/-! ## 12. The meet of two tails -/

theorem meetK_tailI (k1 k2 : Kind) (σ : List Acc) :
    tailI (meetK k1 k2) σ ↔ tailI k1 σ ∧ tailI k2 σ := by
  cases k1 with
  | any => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | star e1 =>
    cases k2 with
    | any => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    | star e2 =>
      show (e1.union e2).admits σ = true ↔ e1.admits σ = true ∧ e2.admits σ = true
      rw [CoreAux.Excl.admits_union, Bool.and_eq_true]
    | exact =>
      show σ = [] ↔ e1.admits σ = true ∧ σ = []
      refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
      rw [h]
      exact CoreAux.admits_nil e1
  | exact =>
    cases k2 with
    | any => exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
    | star e2 =>
      show σ = [] ↔ σ = [] ∧ e2.admits σ = true
      refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
      rw [h]
      exact CoreAux.admits_nil e2
    | exact => exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

#print axioms meetK_tailI

/-! ## 13. The three rows of `emitM` -/

/-- The three rows of the mark-aware emission: at the demand chain (the meet of the tails),
    below it (the added fact as it is), above it (the demand chain with the mark of `a`). -/
theorem emitM_cases {d a j : PFact} (h : emitM d a = some j) :
    Nat.beq d.base a.base = true ∧ markMatchB d.mark a.mark = true ∧
    ((a.path = d.path ∧ j = ⟨a.base, a.path, meetK a.kind d.kind, a.mark⟩) ∨
     (∃ x r, a.path = d.path ++ x :: r ∧ admitsTailB d.kind (x :: r) = true ∧ j = a) ∨
     (∃ r, relate d.path a.path = .above r ∧ d.path = a.path ++ r ∧ r ≠ [] ∧
        admitsTailB a.kind r = true ∧ j = ⟨d.base, d.path, d.kind, a.mark⟩)) := by
  unfold emitM at h
  cases hc : (Nat.beq d.base a.base && markMatchB d.mark a.mark) with
  | false =>
    rw [hc, if_neg Bool.false_ne_true] at h
    cases h
  | true =>
    rw [hc, if_pos rfl] at h
    have hc' := hc
    rw [Bool.and_eq_true] at hc'
    refine ⟨hc'.1, hc'.2, ?_⟩
    cases hr : relate d.path a.path with
    | below r =>
      rw [hr] at h
      have hq := relate_below_path hr
      cases r with
      | nil =>
        refine Or.inl ⟨by rw [hq, List.append_nil], (Option.some.inj h).symm⟩
      | cons x r =>
        dsimp only at h
        cases hx : admitsTailB d.kind (x :: r) with
        | false =>
          rw [hx, if_neg Bool.false_ne_true] at h
          cases h
        | true =>
          rw [hx, if_pos rfl] at h
          exact Or.inr (Or.inl ⟨x, r, hq, hx, (Option.some.inj h).symm⟩)
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases hx : admitsTailB a.kind r with
      | false =>
        rw [hx, if_neg Bool.false_ne_true] at h
        cases h
      | true =>
        rw [hx, if_pos rfl] at h
        exact Or.inr (Or.inr ⟨r, rfl, relate_above_path hr, relate_above_ne hr, hx,
          (Option.some.inj h).symm⟩)
    | apart =>
      rw [hr] at h
      cases h

#print axioms emitM_cases

/-! ## 14. Mark, base and shape of an emitted fact -/

theorem emitM_mark {d a j : PFact} (h : emitM d a = some j) : j.mark = a.mark := by
  obtain ⟨_, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩⟩ := emitM_cases h
  · rw [h1]
  · rw [h2]
  · rw [h3]

theorem emitM_base {d a j : PFact} (h : emitM d a = some j) : j.base = a.base := by
  obtain ⟨hb, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩⟩ := emitM_cases h
  · rw [h1]
  · rw [h2]
  · rw [h3]
    exact CoreAux.beq_iff.mp hb

/-- `emitM` is a mark-copying emission. -/
theorem emitM_copies : EmitCopiesMark emitM :=
  fun _ _ _ h => emitM_mark h

/-- The emitted chain is the chain of the added fact or the demand chain. -/
theorem emitM_shape {d a j : PFact} (h : emitM d a = some j) :
    j.path = a.path ∨ j.path = d.path := by
  obtain ⟨_, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩⟩ := emitM_cases h
  · rw [h1]
    exact Or.inl rfl
  · rw [h2]
    exact Or.inl rfl
  · rw [h3]
    exact Or.inr rfl

/-- The chain bound, strong form: the emitted chain is the chain of the added fact, or the
    demand chain strictly below the added fact. So a field chain longer than the chain of the
    added fact comes only from the demand. -/
theorem emitM_chain_strong {d a j : PFact} (h : emitM d a = some j) :
    j.path = a.path ∨ (j.path = d.path ∧ ∃ r, r ≠ [] ∧ d.path = a.path ++ r) := by
  obtain ⟨_, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, _, hP, hr, _, h3⟩⟩ := emitM_cases h
  · rw [h1]
    exact Or.inl rfl
  · rw [h2]
    exact Or.inl rfl
  · rw [h3]
    exact Or.inr ⟨rfl, r, hr, hP⟩

/-- The chain bound, as stated in the task. -/
theorem emitM_chain {d a j : PFact} (h : emitM d a = some j) :
    j.path = a.path ∨ (∃ r, d.path = a.path ++ r) := by
  rcases emitM_chain_strong h with h1 | ⟨_, r, _, hP⟩
  · exact Or.inl h1
  · exact Or.inr ⟨r, hP⟩

#print axioms emitM_mark
#print axioms emitM_base
#print axioms emitM_copies
#print axioms emitM_shape
#print axioms emitM_chain_strong
#print axioms emitM_chain

/-! ## 15. The emitted fact is exactly the intersection -/

theorem emitM_inter {d a j : PFact} (h : emitM d a = some j) :
    ∀ l, (j.covers l ↔ a.covers l ∧ d.coversLoc l) := by
  intro l
  obtain ⟨hb, _, ⟨hq, h1⟩ | ⟨x, r, hq, hx, h2⟩ | ⟨r, _, hP, hr, hx, h3⟩⟩ := emitM_cases h
  · -- at the demand chain: the meet of the two tails
    have hbd : d.base = a.base := CoreAux.beq_iff.mp hb
    subst h1
    constructor
    · intro hj
      obtain ⟨hlb, ⟨σ, hp, ht⟩, hm⟩ := hj
      have ht' := (meetK_tailI a.kind d.kind σ).mp ht
      refine ⟨⟨hlb, ⟨σ, hp, ht'.1⟩, hm⟩, ⟨?_, σ, ?_, ht'.2⟩⟩
      · show l.base = d.base
        rw [hbd]
        exact hlb
      · show l.path = d.path ++ σ
        rw [← hq]
        exact hp
    · intro ⟨⟨hlb, ⟨σ, hp, ht1⟩, hm⟩, ⟨_, σ', hp', ht2⟩⟩
      have hσ : σ = σ' := by
        rw [hp, hq] at hp'
        exact List.append_cancel_left hp'
      rw [← hσ] at ht2
      exact ⟨hlb, ⟨σ, hp, (meetK_tailI a.kind d.kind σ).mpr ⟨ht1, ht2⟩⟩, hm⟩
  · -- below the demand chain: the added fact as it is
    have hbd : d.base = a.base := CoreAux.beq_iff.mp hb
    subst h2
    constructor
    · intro hj
      refine ⟨hj, ?_⟩
      obtain ⟨hlb, ⟨τ, hp, _⟩, _⟩ := hj
      refine ⟨by rw [hbd]; exact hlb, x :: r ++ τ, ?_, CoreAux.tailI_cons_append hx⟩
      rw [hp, hq, List.append_assoc]
    · exact fun h => h.1
  · -- above the demand chain: the demand chain with the mark of `a`
    have hbd : d.base = a.base := CoreAux.beq_iff.mp hb
    subst h3
    constructor
    · intro hj
      obtain ⟨hlb, ⟨σ, hp, ht⟩, hm⟩ := hj
      refine ⟨⟨?_, ⟨r ++ σ, ?_, ?_⟩, hm⟩, ⟨hlb, σ, hp, ht⟩⟩
      · rw [← hbd]
        exact hlb
      · rw [hp, hP, List.append_assoc]
      · cases r with
        | nil => exact absurd rfl hr
        | cons y r' => exact CoreAux.tailI_cons_append hx
    · intro ⟨⟨_, _, hm⟩, ⟨hlb, σ, hp, ht⟩⟩
      exact ⟨hlb, ⟨σ, hp, ht⟩, hm⟩

#print axioms emitM_inter

/-! ## 16. Nothing is lost when the marks match -/

theorem emitM_complete {d a : PFact} {l : Loc} (hm : markMatchB d.mark a.mark = true)
    (ha : a.covers l) (hd : d.coversLoc l) : ∃ j, emitM d a = some j := by
  obtain ⟨hba, ⟨τ, hpa, hta⟩, _⟩ := ha
  obtain ⟨hbd, σ, hpd, htd⟩ := hd
  have hb : Nat.beq d.base a.base = true := by rw [← hbd, ← hba]; exact Nat.beq_refl _
  have hpath : d.path ++ σ = a.path ++ τ := by rw [← hpd, ← hpa]
  have hc : (Nat.beq d.base a.base && markMatchB d.mark a.mark) = true := by rw [hb, hm]; rfl
  unfold emitM
  rw [if_pos hc]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, _, hτ⟩
  · rw [hrel]
    cases r with
    | nil => exact ⟨_, rfl⟩
    | cons x r' =>
      have hx : admitsTailB d.kind (x :: r') = true := by
        rw [hσ] at htd
        exact CoreAux.tailI_append_admits htd
      refine ⟨a, ?_⟩
      show (if admitsTailB d.kind (x :: r') = true then some a else none) = some a
      rw [if_pos hx]
  · rw [hrel]
    have hx : admitsTailB a.kind r = true := by
      rw [hτ] at hta
      exact CoreAux.tailI_append_admits hta
    refine ⟨⟨d.base, d.path, d.kind, a.mark⟩, ?_⟩
    show (if admitsTailB a.kind r = true then some (⟨d.base, d.path, d.kind, a.mark⟩ : PFact)
      else none) = _
    rw [if_pos hx]

#print axioms emitM_complete

/-! ## 17. The added fact satisfies its emission -/

/-- Every emission is satisfied by its added fact (`satO`): the emission overlaps the added
    fact, and it has the mark of the added fact. -/
theorem emitM_sat {d a j : PFact} (h : emitM d a = some j) : satO j a = true := by
  unfold satO
  rw [Bool.and_eq_true]
  refine ⟨?_, by rw [emitM_mark h]; exact markSubB_refl a.mark⟩
  obtain ⟨hb, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, hrel, _, _, hx, h3⟩⟩ := emitM_cases h
  · subst h1
    unfold overlapB
    dsimp only
    rw [Nat.beq_refl, relate_self]
    exact admitsTailB_nil _
  · subst h2
    unfold overlapB
    rw [Nat.beq_refl, relate_self]
    exact admitsTailB_nil _
  · subst h3
    unfold overlapB
    dsimp only
    rw [hb, hrel]
    exact hx

#print axioms emitM_sat

/-! ## 18. The emission contract (THE MAIN RESULT) -/

/-- For a demanded location `l` (with its mark) that the added fact carries, the emission gives
    an initial fact that covers `l` and that the added fact satisfies, when the marks match. -/
theorem emitM_serves {d a : PFact} {l : Loc} (hm : markMatchB d.mark a.mark = true)
    (ha : a.covers l) (hd : d.coversLoc l) :
    ∃ j, emitM d a = some j ∧ j.covers l ∧ satO j a = true := by
  obtain ⟨j, hj⟩ := emitM_complete hm ha hd
  exact ⟨j, hj, (emitM_inter hj l).mpr ⟨ha, hd⟩, emitM_sat hj⟩

theorem emitM_contract : EmitContractConc emitM satO := by
  intro d a l t ham hd ha
  refine emitM_serves ?_ ha (covers_coversLoc hd)
  have hdm := hd.2.2
  have hla : l.mark = t := by
    have h' := ha.2.2
    rw [ham] at h'
    exact h'
  cases hmd : d.mark with
  | star => rfl
  | conc T =>
    rw [hmd] at hdm
    have hlT : l.mark = T := hdm
    rw [ham]
    show Nat.beq T t = true
    rw [← hlT, ← hla]
    exact Nat.beq_refl _

#print axioms emitM_serves
#print axioms emitM_contract

/-- The full contract (for every added fact) is FALSE for `emitM`: a `*`-mark added fact
    meets a demand with the concrete mark `5` and gets nothing. So the coverage proof needs the
    concreteness of the run (`EmitContractConc.on`). -/
def nfD : PFact := ⟨1, [], .exact, .conc 5⟩
def nfA : PFact := ⟨1, [], .exact, .star⟩
def nfL : Loc := ⟨1, [], 5⟩

theorem emitM_nf_none : emitM nfD nfA = none := by decide

theorem emitM_not_full : ¬ EmitContract emitM satO := by
  intro h
  have hd : nfD.covers nfL := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  have ha : nfA.covers nfL := ⟨rfl, ⟨[], rfl, rfl⟩, trivial⟩
  obtain ⟨j, hj, _, _⟩ := h nfD nfA nfL hd ha
  rw [emitM_nf_none] at hj
  cases hj

#print axioms emitM_nf_none
#print axioms emitM_not_full

/-! ## 19. The overlap satisfaction keeps the contract -/

theorem satO_contract : SatContract satO := by
  refine ⟨?_, ?_⟩
  · intro j a h
    unfold satO at h
    rw [Bool.and_eq_true] at h
    exact h.2
  · intro j a t h ham
    unfold satO at h
    rw [Bool.and_eq_true] at h
    unfold satO
    rw [Bool.and_eq_true]
    refine ⟨?_, markSub_answer ham⟩
    have h1 := h.1
    unfold answerInit
    split
    · rename_i hdp
      unfold overlapB at h1
      rw [Bool.and_eq_true] at h1
      unfold overlapB
      dsimp only
      rw [h1.1, CoreAux.relate_below hdp]
      rfl
    · exact h1

#print axioms satO_contract

/-! ## 20. The two restrictions agree on a conclusion without `*` -/

theorem restrictConcU_eq_S {sc : AFact} {p : PFact} (hk : sc.fact.kind.isStar = false) :
    restrictConcU sc p = restrictConcS sc p := by
  unfold restrictConcU restrictConcS
  cases Nat.beq sc.fact.base p.base with
  | false => rfl
  | true =>
    cases relate p.path sc.fact.path with
    | below r => rfl
    | above r =>
      cases hk' : sc.fact.kind with
      | star e =>
        rw [hk'] at hk
        cases hk
      | any => rfl
      | exact => rfl
    | apart => rfl

theorem restrictU_eq_S_nonstar {j : PFact} {g : AFact} {d : DemandEdge}
    (hk : g.fact.kind.isStar = false) : restrictU j g d = restrictS j g d := by
  show restrictWith restrictConcU j g d = restrictWith restrictConcS j g d
  unfold restrictWith
  cases d.dout with
  | none => rfl
  | some p =>
    dsimp only
    rw [restrictConcU_eq_S hk]

#print axioms restrictU_eq_S_nonstar


/-! ## Version 4: the satisfaction `satI` (the premise lies inside the fact)

  From the review of version 4 (M2): `satI` suffices for the emission contract and the
  satisfaction contract, and it rejects the cross-context reads that `satO` admits. -/

theorem tailSub_meet (k d : Kind) : tailSubB k (meetK k d) = true := by
  cases k with
  | any => cases d <;> rfl
  | exact => cases d <;> rfl
  | star e1 =>
    cases d with
    | any => exact tailSubB_refl _
    | exact => rfl
    | star e2 => exact Invariant.subB_union_right e2 (subB_refl e1)

theorem emitM_satI {d a j : PFact} (h : emitM d a = some j) : satI j a = true := by
  have hm : j.mark = a.mark := emitM_mark h
  unfold satI
  rw [Bool.and_eq_true]
  refine ⟨?_, by rw [hm]; exact markSubB_refl _⟩
  obtain ⟨hb, _, ⟨hq, h1⟩ | ⟨x, r, hq, _, h2⟩ | ⟨r, _, hP, hr, hx, h3⟩⟩ := emitM_cases h
  · subst h1
    unfold coversB
    simp only [Nat.beq_refl, markSubB_refl, Bool.true_and]
    rw [show dropPrefix a.path a.path = some [] by
      have := Store.dropPrefix_append a.path []; rwa [List.append_nil] at this]
    exact tailSub_meet _ _
  · subst h2
    unfold coversB
    simp only [Nat.beq_refl, markSubB_refl, Bool.true_and]
    rw [show dropPrefix j.path j.path = some [] by
      have := Store.dropPrefix_append j.path []; rwa [List.append_nil] at this]
    exact tailSubB_refl _
  · subst h3
    have hbd : d.base = a.base := Nat.eq_of_beq_eq_true hb
    unfold coversB
    simp only
    rw [hbd, Nat.beq_refl, markSubB_refl, Bool.true_and, hP, Store.dropPrefix_append]
    cases r with
    | nil => exact absurd rfl hr
    | cons y r' => exact hx

/-- The spec emission satisfies the emission contract for concrete facts with `satI`. -/
theorem emitM_contract_I : EmitContractConc emitM satI := by
  intro d a l t ham hd ha
  obtain ⟨j, hj, hc, _⟩ := emitM_contract d a l t ham hd ha
  exact ⟨j, hj, hc, emitM_satI hj⟩

theorem satI_contract : SatContract satI := by
  refine ⟨fun j a h => ?_, fun j a t h ham => ?_⟩
  · unfold satI at h; rw [Bool.and_eq_true] at h; exact h.2
  · -- no answer exists in a concrete run; the clause still holds
    unfold satI at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    obtain ⟨hc, _⟩ := h
    refine ⟨?_, markSub_answer ham⟩
    unfold coversB at hc ⊢
    unfold answerInit
    split
    · rename_i hk hdp
      rw [Bool.and_eq_true, Bool.and_eq_true] at hc ⊢
      obtain ⟨⟨hb, _⟩, _⟩ := hc
      refine ⟨⟨hb, by rw [ham]; exact Nat.beq_refl t⟩, ?_⟩
      have hpe : a.path = j.path := by
        have := Store.dropPrefix_some hdp; rwa [List.append_nil] at this
      simp only
      rw [hpe, show dropPrefix j.path j.path = some [] by
        have := Store.dropPrefix_append j.path []; rwa [List.append_nil] at this]
      show tailSubB a.kind .exact = true
      rw [hk]; rfl
    · rw [Bool.and_eq_true, Bool.and_eq_true] at hc ⊢
      obtain ⟨⟨hb, _⟩, hp⟩ := hc
      exact ⟨⟨hb, by rw [ham]; exact Nat.beq_refl t⟩, hp⟩

#print axioms emitM_satI
#print axioms emitM_contract_I
#print axioms satI_contract

end ApSpec.RCore
