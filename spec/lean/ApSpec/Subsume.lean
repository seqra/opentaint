/-
  ApSpec.Subsume — subsumption of FINAL facts and of RECORDS (edge store, spec §8.1).

  Part 1 (final facts): `subsumesB`, `subsumes_sound`. Version 5: the marks of the
  two facts are compared with their exclusions (`markSubsB`): a stored `*∖Xs`
  subsumes a new `*∖Xn` if `Xs ⊆ Xn`, and a stored `*` subsumes every abstract mark.
  Part 2 (edges, v2): the conclusion exclusion `*/E` is the exclusion of the edge.
    * Merge rule 2 (same premise, same conclusion, exclusions E1 and E2) is EXACT:
      the pairs of `*/(E1 ∩ E2)` are the pairs of `*/E1` and the pairs of `*/E2`
      (`merge_inter`).
    * A union of exclusions across conclusions loses pairs (`union_loses_pairs`).
    * Record subsumption: `(a, p, *) → (b, q, */E1)` subsumes
      `(a, p ++ r, *) → (b, q ++ r, */E2)` when `r ≠ []` and `E1` admits `r`, or
      `r = []` and `E1.subB E2` (`record_subsumes`). `recordSubsumesB` is the
      decidable test, `recordSubsumesB_sound` its soundness.
    * Subsumption keeps the layer: a demand record never subsumes a complete record
      (`recordSubsumesLB`, `recordSubsumesLB_layer`, the examples at the end).
  Part 3 (mark exclusions, v5): the same two rules for the mark `*∖x`.
    * Two conclusions that differ only in the mark exclusions `x1` and `x2` merge
      EXACTLY into the mark `*∖(x1 ∩ x2)` (`merge_mark_inter`).
    * A union of mark exclusions loses pairs (`union_marks_loses_pairs`).

  The premise reading `coversB` is NOT a subsumption test for final facts: a final
  `[any]` fact with the mark `*` does not cover a final `$` fact with the mark `T`
  (the marks mean different things), and as finals `*/Universe` is smaller than
  `$`. `subsumesB f1 f2` is the syntactic test; `subsumes_sound` proves that every
  pair of `f2` is a pair of `f1`, for every initial fact.
-/
import ApSpec.Core

namespace ApSpec.Subsume
open ApSpec

def markEqB : MarkA → MarkA → Bool
  | .star,     .star     => true
  | .conc a,   .conc b   => Nat.beq a b
  | .starEx x, .starEx y => decide (x = y)
  | _,         _         => false

/-- `markSubsB m1 m2`: the FINAL mark `m1` lets through every pair that the final
    mark `m2` lets through, with the same output mark. Equal concrete marks; for
    abstract marks (`*` is `*∖[]`), `*∖Xs` subsumes `*∖Xn` if `Xs ⊆ Xn`. A concrete
    mark and an abstract mark never subsume each other. -/
def markSubsB : MarkA → MarkA → Bool
  | .conc a,    .conc b    => Nat.beq a b
  | .star,      .star      => true
  | .star,      .starEx _  => true
  | .starEx xs, .star      => xs.isEmpty
  | .starEx xs, .starEx xn => xs.all (fun a => memB a xn)
  | _,          _          => false

def samePathB (p q : List Acc) : Bool :=
  match dropPrefix p q with
  | some [] => true
  | _       => false

/-- `subsumesB f1 f2`: the final fact `f1` covers every pair of the final fact `f2`
    (same base, a mark that subsumes (`markSubsB`); `[any]` covers everything at or below its path; a `*`
    leaf covers a `*` leaf with more exclusions at the same path; `$` covers `$`
    and `*/Universe` at the same path). -/
def subsumesB (f1 f2 : PFact) : Bool :=
  Nat.beq f1.base f2.base && markSubsB f1.mark f2.mark &&
  match f1.kind, f2.kind with
  | .any,     _                => (dropPrefix f1.path f2.path).isSome
  | .star e1, .star e2         => e1.subB e2 && samePathB f1.path f2.path
  | .exact,   .exact           => samePathB f1.path f2.path
  | .exact,   .star .univ      => samePathB f1.path f2.path
  | _,        _                => false

theorem markEqB_eq {a b : MarkA} (h : markEqB a b = true) : a = b := by
  cases a with
  | star =>
    cases b with
    | star => rfl
    | conc _ => cases h
    | starEx _ => cases h
  | conc x =>
    cases b with
    | star => cases h
    | conc y =>
      have h' : Nat.beq x y = true := h
      rw [CoreAux.beq_iff.mp h']
    | starEx _ => cases h
  | starEx x =>
    cases b with
    | star => cases h
    | conc _ => cases h
    | starEx y =>
      have h' : decide (x = y) = true := h
      rw [of_decide_eq_true h']

/-- SOUNDNESS of the mark test: if `m2` lets the initial mark `x` through, then `m1`
    lets it through too, with the same output mark. -/
theorem markSubsB_sound {m1 m2 : MarkA} {x : Mark} (h : markSubsB m1 m2 = true)
    (hp : m2.passes x) : m1.out x = m2.out x ∧ m1.passes x := by
  cases m1 with
  | conc a =>
    cases m2 with
    | conc b =>
      have h' : Nat.beq a b = true := h
      rw [CoreAux.beq_iff.mp h']
      exact ⟨rfl, trivial⟩
    | star => cases h
    | starEx _ => cases h
  | star =>
    cases m2 with
    | star => exact ⟨rfl, trivial⟩
    | starEx _ => exact ⟨rfl, trivial⟩
    | conc _ => cases h
  | starEx xs =>
    cases m2 with
    | conc _ => cases h
    | star =>
      cases xs with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => cases h
    | starEx xn =>
      refine ⟨rfl, ?_⟩
      have hp' : memB x xn = false := hp
      show memB x xs = false
      cases hx : memB x xs with
      | false => rfl
      | true =>
        have h' : xs.all (fun a => memB a xn) = true := h
        rw [CoreAux.memB_of_all hx h'] at hp'
        cases hp'

#print axioms markSubsB_sound

theorem samePathB_eq {p q : List Acc} (h : samePathB p q = true) : q = p := by
  unfold samePathB at h
  cases hd : dropPrefix p q with
  | none => rw [hd] at h; cases h
  | some r =>
    rw [hd] at h
    cases r with
    | nil => rw [CoreAux.dropPrefix_some.mp hd, List.append_nil]
    | cons a r => cases h

theorem subsumes_sound {i f1 f2 : PFact} {l0 l1 : Loc} (h : subsumesB f1 f2 = true)
    (hd : den i f2 l0 l1) : den i f1 l0 l1 := by
  unfold subsumesB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hb, hm⟩, hk⟩ := h
  have hbase : f1.base = f2.base := CoreAux.beq_iff.mp hb
  obtain ⟨hb0, hb1, hm0, hm1, hps, σ, τ, hp0, hp1, hti, htf⟩ := hd
  have ⟨hout, hps'⟩ := markSubsB_sound hm hps
  have hb1' : l1.base = f1.base := by rw [hb1, hbase]
  have hm1' : l1.mark = f1.mark.out l0.mark := by rw [hm1, hout]
  cases hk1 : f1.kind with
  | any =>
    rw [hk1] at hk
    cases hdp : dropPrefix f1.path f2.path with
    | none => rw [hdp] at hk; cases hk
    | some r =>
      have hq := CoreAux.dropPrefix_some.mp hdp
      refine ⟨hb0, hb1', hm0, hm1', hps', σ, r ++ τ, hp0, ?_, hti, ?_⟩
      · rw [hp1, hq, List.append_assoc]
      · rw [hk1]; trivial
  | star e1 =>
    cases hk2 : f2.kind with
    | star e2 =>
      rw [hk1, hk2, Bool.and_eq_true] at hk
      obtain ⟨hsub, hsp⟩ := hk
      have hpe := samePathB_eq hsp
      rw [hk2] at htf
      obtain ⟨hτ, ha2⟩ := htf
      refine ⟨hb0, hb1', hm0, hm1', hps', σ, τ, hp0, by rw [hp1, hpe], hti, ?_⟩
      rw [hk1]
      exact ⟨hτ, CoreAux.Excl.subB_sound hsub ha2⟩
    | any => rw [hk1, hk2] at hk; cases hk
    | exact => rw [hk1, hk2] at hk; cases hk
  | exact =>
    cases hk2 : f2.kind with
    | exact =>
      rw [hk1, hk2] at hk
      have hpe := samePathB_eq hk
      rw [hk2] at htf
      refine ⟨hb0, hb1', hm0, hm1', hps', σ, τ, hp0, by rw [hp1, hpe], hti, ?_⟩
      rw [hk1]; exact htf
    | star e2 =>
      cases e2 with
      | univ =>
        rw [hk1, hk2] at hk
        have hpe := samePathB_eq hk
        rw [hk2] at htf
        obtain ⟨hτ, hu⟩ := htf
        have hσ : σ = [] := CoreAux.univ_admits hu
        refine ⟨hb0, hb1', hm0, hm1', hps', σ, τ, hp0, by rw [hp1, hpe], hti, ?_⟩
        rw [hk1]
        show τ = []
        rw [hτ, hσ]
      | set xs => rw [hk1, hk2] at hk; cases hk
    | any => rw [hk1, hk2] at hk; cases hk

#print axioms subsumes_sound

-- The premise test is not a final subsumption test (review finding):
-- coversB says (y,.,[any],*) covers (y,.,$,T), but subsumesB refuses it.
example : coversB ⟨1, [], .any, .star⟩ ⟨1, [], .exact, .conc 5⟩ = true := by decide
example : subsumesB ⟨1, [], .any, .star⟩ ⟨1, [], .exact, .conc 5⟩ = false := by decide
-- the same mark: [any] subsumes a fact below it
example : subsumesB ⟨1, [], .any, .conc 5⟩ ⟨1, [2, 3], .exact, .conc 5⟩ = true := by decide
-- intersection join direction: fewer exclusions subsume more exclusions
example : subsumesB ⟨1, [], .star (.set []), .star⟩ ⟨1, [], .star (.set [2]), .star⟩ = true := by decide
example : subsumesB ⟨1, [], .star (.set [2]), .star⟩ ⟨1, [], .star (.set []), .star⟩ = false := by decide
-- version 5, mark exclusions: fewer excluded marks subsume more excluded marks
example : subsumesB ⟨1, [], .star (.set []), .starEx [5]⟩ ⟨1, [], .star (.set []), .starEx [6, 5]⟩ = true := by
  decide
example : subsumesB ⟨1, [], .star (.set []), .starEx [6, 5]⟩ ⟨1, [], .star (.set []), .starEx [5]⟩ = false := by
  decide
-- a stored `*` subsumes every abstract mark; a stored `*∖{5}` does not subsume `*`
example : subsumesB ⟨1, [], .any, .star⟩ ⟨1, [2], .exact, .starEx [5]⟩ = true := by decide
example : subsumesB ⟨1, [], .any, .starEx [5]⟩ ⟨1, [2], .exact, .star⟩ = false := by decide
-- an abstract mark never subsumes a concrete mark (the output marks differ)
example : subsumesB ⟨1, [], .any, .starEx []⟩ ⟨1, [], .exact, .conc 5⟩ = false := by decide

/-! ## Part 2. Edges: merge and record subsumption -/

/-! ### 2.1 The intersection of exclusions -/

theorem memB_filter {a : Acc} {ys : List Acc} : ∀ {xs : List Acc},
    memB a (xs.filter (fun b => memB b ys)) = (memB a xs && memB a ys)
  | [] => rfl
  | b :: bs => by
    cases hb : memB b ys
    · have hf : (b :: bs).filter (fun b => memB b ys) = bs.filter (fun b => memB b ys) := by
        simp only [List.filter, hb]
      rw [hf, memB_filter]
      show (memB a bs && memB a ys) = ((Nat.beq a b || memB a bs) && memB a ys)
      cases hab : Nat.beq a b
      · rfl
      · have hab' := CoreAux.beq_iff.mp hab
        subst hab'
        rw [hb, Bool.and_false, Bool.and_false]
    · have hf : (b :: bs).filter (fun b => memB b ys) = b :: bs.filter (fun b => memB b ys) := by
        simp only [List.filter, hb]
      rw [hf]
      show (Nat.beq a b || memB a (bs.filter (fun b => memB b ys))) =
        ((Nat.beq a b || memB a bs) && memB a ys)
      rw [memB_filter]
      cases hab : Nat.beq a b
      · rfl
      · have hab' := CoreAux.beq_iff.mp hab
        subst hab'
        rw [hb]; rfl

/-- `E1 ∩ E2` admits what `E1` admits or what `E2` admits. -/
theorem admits_inter (e1 e2 : Excl) (σ : List Acc) :
    (e1.inter e2).admits σ = (e1.admits σ || e2.admits σ) := by
  cases σ with
  | nil => rw [CoreAux.admits_nil, CoreAux.admits_nil, CoreAux.admits_nil]; rfl
  | cons a s =>
    cases e1 with
    | univ => rfl
    | set xs =>
      cases e2 with
      | univ => show (!(memB a xs)) = (!(memB a xs) || false); rw [Bool.or_false]
      | set ys =>
        show (!(memB a (xs.filter (fun b => memB b ys)))) = (!(memB a xs) || !(memB a ys))
        rw [memB_filter]
        cases memB a xs <;> cases memB a ys <;> rfl

#print axioms admits_inter

/-! ### 2.2 Merge rule 2 is exact -/

/-- MERGE RULE 2. Two edges with the same premise and the same conclusion
    `(b, q, */E1, m)` and `(b, q, */E2, m)` merge into `(b, q, */(E1 ∩ E2), m)`.
    The merge is exact: it has the same pairs as the two edges. -/
theorem merge_inter {i : PFact} {b : Base} {q : List Acc} {E1 E2 : Excl} {m : MarkA}
    {l0 l1 : Loc} :
    den i ⟨b, q, .star (E1.inter E2), m⟩ l0 l1 ↔
      den i ⟨b, q, .star E1, m⟩ l0 l1 ∨ den i ⟨b, q, .star E2, m⟩ l0 l1 := by
  constructor
  · intro ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ha⟩
    have ha' : (E1.admits σ || E2.admits σ) = true := by rw [← admits_inter]; exact ha
    rw [Bool.or_eq_true] at ha'
    rcases ha' with ha' | ha'
    · exact Or.inl ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ha'⟩
    · exact Or.inr ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ha'⟩
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ha⟩ |
                  ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ha⟩
    · refine ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ?_⟩
      show (E1.inter E2).admits σ = true
      rw [admits_inter, ha]; rfl
    · refine ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, hτ, ?_⟩
      show (E1.inter E2).admits σ = true
      rw [admits_inter, ha, Bool.or_true]

#print axioms merge_inter

/-- A union of exclusions across different conclusions is FORBIDDEN: it loses
    pairs. The edge `(10, ., *) → (11, ., */{})` has the pair
    `(10, .2) ↦ (11, .2)`; the merge with an exclusion `{2}` of another
    conclusion removes it. -/
theorem union_loses_pairs :
    den ⟨10, [], .star Excl.empty, .star⟩ ⟨11, [], .star Excl.empty, .star⟩ ⟨10, [2], 0⟩ ⟨11, [2], 0⟩ ∧
    ¬ den ⟨10, [], .star Excl.empty, .star⟩ ⟨11, [], .star (Excl.empty.union (.set [2])), .star⟩
        ⟨10, [2], 0⟩ ⟨11, [2], 0⟩ := by
  refine ⟨⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨_, _, _, _, _, σ, τ, hp0, _, _, _, ha⟩
  have hs : σ = [2] := hp0.symm
  subst hs
  exact absurd ha (by decide)

#print axioms union_loses_pairs

/-! ### 2.3 Record subsumption -/

/-- The condition on the common suffix `r` of the two records. -/
def suffixOkB (r : List Acc) (P1 P2 E1 E2 : Excl) : Bool :=
  match r with
  | []     => P1.subB P2 && E1.subB E2
  | _ :: _ => P1.admits r && E1.admits r

/-- The general form: the record `i2 → f2` is the record `i1 → f1` extended by
    the same suffix `r` on both sides. Then every pair of `i2 → f2` is a pair of
    `i1 → f1`. -/
theorem record_subsumes_gen {i1 f1 i2 f2 : PFact} {P1 P2 E1 E2 : Excl} {r : List Acc}
    {l0 l1 : Loc}
    (hib : i2.base = i1.base) (hfb : f2.base = f1.base)
    (him : i2.mark = i1.mark) (hfm : f2.mark = f1.mark)
    (hk1 : i1.kind = .star P1) (hk2 : i2.kind = .star P2)
    (hf1 : f1.kind = .star E1) (hf2 : f2.kind = .star E2)
    (hip : i2.path = i1.path ++ r) (hfp : f2.path = f1.path ++ r)
    (hc : suffixOkB r P1 P2 E1 E2 = true) :
    den i2 f2 l0 l1 → den i1 f1 l0 l1 := by
  intro ⟨h0, h1, h2, h3, h4, σ, τ, hp0, hp1, hti, htf⟩
  rw [hk2] at hti
  rw [hf2] at htf
  obtain ⟨hτ, ha⟩ := htf
  have hP : P1.admits (r ++ σ) = true ∧ E1.admits (r ++ σ) = true := by
    cases r with
    | nil =>
      have ⟨hs1, hs2⟩ := (Bool.and_eq_true _ _).mp hc
      exact ⟨CoreAux.Excl.subB_sound hs1 hti, CoreAux.Excl.subB_sound hs2 ha⟩
    | cons x r' =>
      have ⟨hs1, hs2⟩ := (Bool.and_eq_true _ _).mp hc
      rw [CoreAux.admits_append_cons, CoreAux.admits_append_cons]
      exact ⟨hs1, hs2⟩
  refine ⟨by rw [h0, hib], by rw [h1, hfb], by rw [← him]; exact h2, by rw [h3, hfm],
    by rw [← hfm]; exact h4, r ++ σ, r ++ σ, ?_, ?_, ?_, ?_⟩
  · rw [hp0, hip, List.append_assoc]
  · rw [hp1, hfp, hτ, List.append_assoc]
  · rw [hk1]; exact hP.1
  · rw [hf1]; exact ⟨rfl, hP.2⟩

#print axioms record_subsumes_gen

/-- RECORD SUBSUMPTION (the form of the spec). `(a, p, *) → (b, q, */E1)`
    subsumes `(a, p ++ r, *) → (b, q ++ r, */E2)` when `r ≠ []` and `E1` admits
    `r`, or when `r = []` and `E1.subB E2`: every pair of the second record is a
    pair of the first record. -/
theorem record_subsumes {a b : Base} {p q r : List Acc} {E1 E2 : Excl} {m mo : MarkA}
    {l0 l1 : Loc}
    (h : (r ≠ [] ∧ E1.admits r = true) ∨ (r = [] ∧ E1.subB E2 = true)) :
    den ⟨a, p ++ r, .star Excl.empty, m⟩ ⟨b, q ++ r, .star E2, mo⟩ l0 l1 →
    den ⟨a, p, .star Excl.empty, m⟩ ⟨b, q, .star E1, mo⟩ l0 l1 := by
  refine record_subsumes_gen (P1 := Excl.empty) (P2 := Excl.empty) (r := r)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
  rcases h with ⟨hne, ha⟩ | ⟨he, hs⟩
  · cases r with
    | nil => exact absurd rfl hne
    | cons x r' =>
      show (Excl.empty.admits (x :: r') && E1.admits (x :: r')) = true
      rw [CoreAux.empty_admits, ha]; rfl
  · subst he
    show (Excl.empty.subB Excl.empty && E1.subB E2) = true
    rw [hs]; rfl

#print axioms record_subsumes

/-- The decidable test: `recordSubsumesB g s` — the record `g` (general)
    subsumes the record `s` (specific). Both records are `* → *` records with
    the same bases and marks, and `s` extends `g` by the same suffix on both
    sides. -/
def recordSubsumesB (g s : PFact × PFact) : Bool :=
  Nat.beq g.1.base s.1.base && Nat.beq g.2.base s.2.base &&
  markEqB g.1.mark s.1.mark && markEqB g.2.mark s.2.mark &&
  match g.1.kind, s.1.kind, g.2.kind, s.2.kind,
        dropPrefix g.1.path s.1.path, dropPrefix g.2.path s.2.path with
  | .star P1, .star P2, .star E1, .star E2, some r, some r' =>
    samePathB r r' && suffixOkB r P1 P2 E1 E2
  | _, _, _, _, _, _ => false

/-- SOUNDNESS of the test: every pair of the subsumed record is a pair of the
    subsuming record. -/
theorem recordSubsumesB_sound {g s : PFact × PFact} {l0 l1 : Loc}
    (h : recordSubsumesB g s = true) : den s.1 s.2 l0 l1 → den g.1 g.2 l0 l1 := by
  unfold recordSubsumesB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb1, hb2⟩, hm1⟩, hm2⟩, hk⟩ := h
  split at hk
  · rename_i P1 P2 E1 E2 r r' hk1 hk2 hf1 hf2 hd1 hd2
    rw [Bool.and_eq_true] at hk
    obtain ⟨hsp, hc⟩ := hk
    have hr : r' = r := samePathB_eq hsp
    rw [hr] at hd2
    exact record_subsumes_gen (CoreAux.beq_iff.mp hb1).symm (CoreAux.beq_iff.mp hb2).symm
      (markEqB_eq hm1).symm (markEqB_eq hm2).symm hk1 hk2 hf1 hf2
      (CoreAux.dropPrefix_some.mp hd1) (CoreAux.dropPrefix_some.mp hd2) hc
  · cases hk

#print axioms recordSubsumesB_sound

/-! ### 2.4 Subsumption keeps the layer -/

/-- The test on records with the layer of the conclusion: geometric subsumption
    AND the same classification `complete`. -/
def recordSubsumesLB (g s : PFact × AFact) : Bool :=
  recordSubsumesB (g.1, g.2.fact) (s.1, s.2.fact) && decide (g.2.complete = s.2.complete)

theorem recordSubsumesLB_sound {g s : PFact × AFact} {l0 l1 : Loc}
    (h : recordSubsumesLB g s = true) : den s.1 s.2.fact l0 l1 → den g.1 g.2.fact l0 l1 :=
  recordSubsumesB_sound ((Bool.and_eq_true _ _).mp h).1

/-- A record that subsumes a record keeps its classification: a demand (or an
    `[any]`) record never removes a complete record. -/
theorem recordSubsumesLB_layer {g s : PFact × AFact} (h : recordSubsumesLB g s = true) :
    g.2.complete = s.2.complete :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp h).2

#print axioms recordSubsumesLB_sound
#print axioms recordSubsumesLB_layer

/-! ### 2.5 Examples -/

namespace Examples

-- accessors f, g, h; bases a, b
def f : Acc := 1
def g : Acc := 2
def h : Acc := 3
def a : Base := 10
def b : Base := 11
def st : Kind := .star Excl.empty
def pf (base : Base) (p : List Acc) (k : Kind) : PFact := ⟨base, p, k, .star⟩

/-- The general record `(a, .f, *) → (b, .h, *)`. -/
def gen : PFact × PFact := (pf a [f] st, pf b [h] st)
/-- The specific record `(a, .f.g, *) → (b, .h.g, *)`. -/
def spec : PFact × PFact := (pf a [f, g] st, pf b [h, g] st)

-- The user's case: the general record subsumes the specific record.
example : recordSubsumesB gen spec = true := by decide

-- The reverse does NOT hold.
example : recordSubsumesB spec gen = false := by decide

-- An exclusion of `g` on the general conclusion blocks the subsumption.
example : recordSubsumesB (pf a [f] st, pf b [h] (.star (.set [g]))) spec = false := by decide

-- The same paths: fewer exclusions subsume more exclusions, not the reverse.
example : recordSubsumesB (pf a [f] st, pf b [h] st) (pf a [f] st, pf b [h] (.star (.set [g]))) = true := by
  decide
example : recordSubsumesB (pf a [f] st, pf b [h] (.star (.set [g]))) (pf a [f] st, pf b [h] st) = false := by
  decide

-- Different suffixes on the two sides: no subsumption.
example : recordSubsumesB gen (pf a [f, g] st, pf b [h, f] st) = false := by decide

/-- The reverse fails on the pairs too: `(a, .f) ↦ (b, .h)` is a pair of the
    general record and not a pair of the specific record. -/
theorem reverse_fails :
    den gen.1 gen.2 ⟨a, [f], 0⟩ ⟨b, [h], 0⟩ ∧ ¬ den spec.1 spec.2 ⟨a, [f], 0⟩ ⟨b, [h], 0⟩ := by
  refine ⟨⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨_, _, _, _, _, σ, τ, hp0, _⟩
  have hp0' : [f] = [f, g] ++ σ := hp0
  have hl := congrArg List.length hp0'
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

#print axioms reverse_fails

-- Merge rule 2 on concrete exclusions: {g, h} ∩ {h, f} = {h}.
example : (Excl.inter (.set [g, h]) (.set [h, f])) = .set [h] := by decide

/-- A demand record `(a, .f, *) → (b, .h, *)~` and a complete record
    `(a, .f.g, *) → (b, .h.g, *)`: the geometry subsumes, but the classification
    `complete` differs, so the layered test refuses. -/
def genDemand : PFact × AFact := (gen.1, ⟨gen.2, true⟩)
def specComplete : PFact × AFact := (spec.1, ⟨spec.2, false⟩)

example : recordSubsumesB (genDemand.1, genDemand.2.fact) (specComplete.1, specComplete.2.fact) = true ∧
    genDemand.2.complete = false ∧ specComplete.2.complete = true ∧
    recordSubsumesLB genDemand specComplete = false := by decide

-- In the same layer the layered test accepts.
example : recordSubsumesLB (gen.1, ⟨gen.2, false⟩) specComplete = true := by decide

end Examples

/-! ## Part 3. Mark exclusions: merge and union -/

/-- The intersection of two mark exclusion lists. -/
def markInter (x1 x2 : List Mark) : List Mark := x1.filter (fun m => memB m x2)

/-- MERGE RULE 2 FOR MARKS. Two conclusions `(b, q, k, *∖x1)` and `(b, q, k, *∖x2)` of the
    same premise merge into `(b, q, k, *∖(x1 ∩ x2))`. The merge is exact: it has the same
    pairs as the two conclusions. -/
theorem merge_mark_inter {i : PFact} {b : Base} {q : List Acc} {k : Kind} {x1 x2 : List Mark}
    {l0 l1 : Loc} :
    den i ⟨b, q, k, .starEx (markInter x1 x2)⟩ l0 l1 ↔
      den i ⟨b, q, k, .starEx x1⟩ l0 l1 ∨ den i ⟨b, q, k, .starEx x2⟩ l0 l1 := by
  constructor
  · intro ⟨h0, h1, h2, h3, h4, hr⟩
    have h4' : memB l0.mark (markInter x1 x2) = false := h4
    unfold markInter at h4'
    rw [memB_filter] at h4'
    cases hx1 : memB l0.mark x1 with
    | false => exact Or.inl ⟨h0, h1, h2, h3, hx1, hr⟩
    | true =>
      rw [hx1, Bool.true_and] at h4'
      exact Or.inr ⟨h0, h1, h2, h3, h4', hr⟩
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, hr⟩ | ⟨h0, h1, h2, h3, h4, hr⟩
    · refine ⟨h0, h1, h2, h3, ?_, hr⟩
      have h4' : memB l0.mark x1 = false := h4
      show memB l0.mark (markInter x1 x2) = false
      unfold markInter
      rw [memB_filter, h4', Bool.false_and]
    · refine ⟨h0, h1, h2, h3, ?_, hr⟩
      have h4' : memB l0.mark x2 = false := h4
      show memB l0.mark (markInter x1 x2) = false
      unfold markInter
      rw [memB_filter, h4', Bool.and_false]

#print axioms merge_mark_inter

/-- The mark `*∖[]` has the same pairs as the mark `*`. So the merge of a `*` conclusion
    with a `*∖x` conclusion is the `*` conclusion (`markInter [] x = []`). -/
theorem den_starEx_nil {i : PFact} {b : Base} {q : List Acc} {k : Kind} {l0 l1 : Loc} :
    den i ⟨b, q, k, .starEx []⟩ l0 l1 ↔ den i ⟨b, q, k, .star⟩ l0 l1 :=
  ⟨fun ⟨h0, h1, h2, h3, _, hr⟩ => ⟨h0, h1, h2, h3, trivial, hr⟩,
   fun ⟨h0, h1, h2, h3, _, hr⟩ => ⟨h0, h1, h2, h3, rfl, hr⟩⟩

#print axioms den_starEx_nil

/-- A union of mark exclusions is FORBIDDEN: it loses pairs. The edge
    `(10, ., *, *) → (11, ., *, *∖{5})` has the pair `(10, ., 6) ↦ (11, ., 6)`; the merge
    with the exclusion `{6}` of another conclusion (the mark `*∖{5, 6}`) removes it. -/
theorem union_marks_loses_pairs :
    den ⟨10, [], .star Excl.empty, .star⟩ ⟨11, [], .star Excl.empty, .starEx [5]⟩
        ⟨10, [], 6⟩ ⟨11, [], 6⟩ ∧
    ¬ den ⟨10, [], .star Excl.empty, .star⟩ ⟨11, [], .star Excl.empty, .starEx ([5] ++ [6])⟩
        ⟨10, [], 6⟩ ⟨11, [], 6⟩ := by
  refine ⟨⟨rfl, rfl, trivial, rfl, rfl, [], [], rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro ⟨_, _, _, _, hp, _⟩
  have hp' : memB 6 ([5] ++ [6]) = false := hp
  exact absurd hp' (by decide)

#print axioms union_marks_loses_pairs

-- Merge rule 2 on concrete mark exclusions: {5, 6} ∩ {6, 7} = {6}.
example : markInter [5, 6] [6, 7] = [6] := by decide

end ApSpec.Subsume
