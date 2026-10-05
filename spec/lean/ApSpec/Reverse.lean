/-
  ApSpec.Reverse — reversal of records, statements and programs (model v5).

  The forward and the backward runs share the complete records. A forward record
  `i → f` (entry fact → exit fact) read in the backward direction is `revEdge i f`
  (Basic §13): the exit fact becomes the premise. The tails come from the exact
  table `revKinds`; the exclusion goes to the NEW conclusion, so the new premise
  has the empty exclusion. The backward run also applies the reversed statement
  summaries and the reversed call bindings.

  Version 5 (cleaners and type filters):
    * A record with the conclusion mark `*∖x` (`MarkA.starEx x`, put there by a cleaner)
      passes the mark of the initial fact through, except the marks of `x`. Its mark
      relation is a partial identity (`markRel_starEx_iff`), so it is its own converse.
      `revEdge` keeps `*∖x` on the NEW conclusion and puts the old premise mark on the
      new premise. RESULT: such a record is mark-reversible for EVERY premise mark, and
      it reverses exactly (`rev_starEx_exact`). `MarkRev` has a new disjunct for it.
    * `den` has the conjunct `f.mark.passes l0.mark`; `MarkRel` carries it.
    * `Program.rev` maps `Instr.clean cl` and `Instr.filt b may` to THEMSELVES: both
      concrete steps keep the location (partial identities), so the converse of the
      step is the same step. `SegC` and `RevSim` have the two new cases, and `rev_WF`
      has the new field `filtPrefix`.

  Main results (constructive; see the `#print axioms` lines):
    1. `revEdge_sound`        the reversed record covers the converse relation
                              (condition: the record is mark-reversible).
    2. `revEdge_exact`        the reversal is exact on `ExactShape` (all shapes but
                              `*e → $` and `*e → [any]` with `e ≠ {}`).
       `rev_starEx_exact`     a record with the conclusion mark `*∖x` and an empty
                              premise exclusion reverses exactly, for every premise mark.
       `no_rev_of_two_marks`  two premise marks to one conclusion location: no fact pair
                              covers the converse (so `MarkRev` is necessary).
       `rev_exact_of_empty_premise` THE SPEC ASSERTION: a premise with the empty
                              exclusion (every initial fact that the abstraction
                              emits: `policy_premEmpty`, `answerInit_premEmpty`)
                              gives an exact reversal for all nine shapes.
       `star_exact_no_exact_rev` NO fact pair reverses `(*{1} → $)` exactly: the
                              condition on the premise exclusion is necessary.
       `no_rev_of_star_conc`  NO fact pair reverses a mark-producing record under
                              a `*`-mark premise, not even soundly.
    3. `revEdge_involutive`   reversal twice gives the same relation.
       `revEdge_revEdge`      on canonical records it gives the same syntax.
    4. `applicable_rev_premise` a reversed `*` premise has the empty exclusion and
                              is applicable to every fact at or below its chain.
    5. `Stmt.rev_step_iff`    the backward step is the converse of the forward step.
       `revNoId_breaks`       without the identity edges the iff fails.
    6. `Program.rev` (statements, calls and bindings reversed; cleaners and type
       filters kept as they are):
       `flow_iff_segC`, `flow_rev_iff_calls`, `segC_rev_iff`, `flow_iff_backSegC`,
       `rev_WF`, `backward_of_forward_calls`: the backward run is the closure `D`
       on `Program.rev P`, and the forward soundness theorem applied to it covers
       every converse flow.
    7. `backward_reuse`, `backward_reuse_rev`, `backward_reuse_precise`:
       reversed forward records cover the converse flows of the covered entry set
       (the closed-method condition), and exact records stay exact.
       `backward_reuse_needs_cover`: the cover condition is necessary.
    8. `Vec`: `revEdge` on the cases of `ApSpec/Cases.lean`.
-/
import ApSpec.Basic

namespace ApSpec.Reverse
open ApSpec

/-! ## 0. List and exclusion helpers -/

theorem memB_append (a : Acc) (xs ys : List Acc) :
    memB a (xs ++ ys) = (memB a xs || memB a ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    show (Nat.beq a b || memB a (bs ++ ys)) = ((Nat.beq a b || memB a bs) || memB a ys)
    rw [ih, Bool.or_assoc]

theorem memB_of_mem {a : Acc} {xs : List Acc} (h : a ∈ xs) : memB a xs = true := by
  induction h with
  | head bs => show (Nat.beq a a || memB a bs) = true; rw [Nat.beq_refl]; rfl
  | tail b _ ih => show (Nat.beq a b || memB a _) = true; rw [ih, Bool.or_true]

theorem mem_of_memB {a : Acc} : ∀ {xs : List Acc}, memB a xs = true → a ∈ xs
  | [], h => by cases h
  | b :: bs, h => by
    cases hb : Nat.beq a b with
    | true => rw [Nat.eq_of_beq_eq_true hb]; exact List.Mem.head bs
    | false =>
      have e : memB a (b :: bs) = memB a bs := by
        show (Nat.beq a b || memB a bs) = memB a bs
        rw [hb]; rfl
      rw [e] at h
      exact List.Mem.tail b (mem_of_memB h)

theorem empty_admits (σ : List Acc) : Excl.empty.admits σ = true := by
  cases σ <;> rfl

theorem admits_nil (e : Excl) : e.admits [] = true := by cases e <;> rfl

theorem admits_union (e1 e2 : Excl) (σ : List Acc) :
    (e1.union e2).admits σ = (e1.admits σ && e2.admits σ) := by
  cases σ with
  | nil => cases e1 <;> cases e2 <;> rfl
  | cons a σ =>
    cases e1 with
    | univ => rfl
    | set xs =>
      cases e2 with
      | univ => show false = (!memB a xs && false); rw [Bool.and_false]
      | set ys =>
        show (!memB a (xs ++ ys)) = (!memB a xs && !memB a ys)
        rw [memB_append]
        cases memB a xs <;> rfl

theorem nil_eq_append {p q : List Acc} (h : [] = p ++ q) : p = [] ∧ q = [] := by
  cases p with
  | nil => exact ⟨rfl, h.symm⟩
  | cons x xs => cases h

theorem dropPrefix_append : ∀ (p τ : List Acc), dropPrefix p (p ++ τ) = some τ
  | [], τ => rfl
  | a :: p, τ => by
    show (if Nat.beq a a then dropPrefix p (p ++ τ) else none) = some τ
    rw [Nat.beq_refl]; exact dropPrefix_append p τ

/-! ## 1. Conditions and the shape of `revEdge` -/

/-- The record is mark-reversible: it passes the mark through (`f.mark = *`, or
    `f.mark = *∖x`: the mark passes unless it is in `x`), or its premise has a concrete
    mark. (Version 5: the disjunct `*∖x` is new. The order of the disjuncts keeps
    `Or.inr ⟨t, h⟩` for a concrete premise mark.) -/
def MarkRev (i f : PFact) : Prop :=
  (f.mark = .star ∨ ∃ x, f.mark = .starEx x) ∨ ∃ t, i.mark = .conc t

/-- A record with the conclusion mark `*∖x` is mark-reversible, for every premise mark. -/
theorem markRev_starEx {i f : PFact} {x : List Mark} (h : f.mark = .starEx x) : MarkRev i f :=
  Or.inl (Or.inr ⟨x, h⟩)

/-- A record with the conclusion mark `*` is mark-reversible, for every premise mark. -/
theorem markRev_star {i f : PFact} (h : f.mark = .star) : MarkRev i f :=
  Or.inl (Or.inl h)

/-- The tail shapes that `revEdge` reverses exactly: all but `*e → $` and
    `*e → [any]` with a non-empty premise exclusion `e`. -/
def ExactShape : Kind → Kind → Prop
  | .star e, .exact => e = Excl.empty
  | .star e, .any   => e = Excl.empty
  | _,       _      => True

/-- The premise exclusion is empty (`$` and `[any]` premises have none). -/
def PremEmpty : Kind → Prop
  | .star e => e = Excl.empty
  | _       => True

/-- The mark of the new premise. -/
def pmOf (i f : PFact) : MarkA :=
  match f.mark with
  | .star     => i.mark
  | .conc t   => .conc t
  | .starEx _ => i.mark

/-- The mark of the new conclusion. -/
def fmOf (i f : PFact) : MarkA :=
  match f.mark with
  | .star     => .star
  | .conc _   => i.mark
  | .starEx x => .starEx x

theorem revEdge_eq (i f : PFact) : revEdge i f =
    (⟨f.base, f.path, (revKinds i.kind f.kind).1, pmOf i f⟩,
     ⟨i.base, i.path, (revKinds i.kind f.kind).2, fmOf i f⟩) := by
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases fm <;> rfl

/-- The path part of `den`. -/
def PathRel (ip : List Acc) (ik : Kind) (fp : List Acc) (fk : Kind) (p0 p1 : List Acc) : Prop :=
  ∃ σ τ, p0 = ip ++ σ ∧ p1 = fp ++ τ ∧ tailI ik σ ∧ tailF fk σ τ

/-- The mark part of `den` (version 5: with the conjunct `passes`). -/
def MarkRel (im fm : MarkA) (m0 m1 : Mark) : Prop :=
  im.admits m0 ∧ m1 = fm.out m0 ∧ fm.passes m0

theorem den_split {i f : PFact} {l0 l1 : Loc} : den i f l0 l1 ↔
    (l0.base = i.base ∧ l1.base = f.base) ∧ MarkRel i.mark f.mark l0.mark l1.mark ∧
    PathRel i.path i.kind f.path f.kind l0.path l1.path := by
  unfold den MarkRel PathRel
  exact ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨⟨h1, h2⟩, ⟨h3, h4, h5⟩, h6⟩,
         fun ⟨⟨h1, h2⟩, ⟨h3, h4, h5⟩, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- The mark relation of a `*∖x` conclusion is a partial identity: the mark stays, the
    premise admits it, and `x` does not contain it. So it is its own converse. -/
theorem markRel_starEx_iff {im : MarkA} {x : List Mark} {m0 m1 : Mark} :
    MarkRel im (.starEx x) m0 m1 ↔ m1 = m0 ∧ im.admits m0 ∧ memB m0 x = false :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩

#print axioms markRel_starEx_iff

theorem markRel_rev {i f : PFact} {m0 m1 : Mark} (hm : MarkRev i f)
    (h : MarkRel i.mark f.mark m0 m1) : MarkRel (pmOf i f) (fmOf i f) m1 m0 := by
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  unfold MarkRel at h ⊢
  unfold MarkRev at hm
  obtain ⟨h1, h2, h3⟩ := h
  cases fm with
  | star =>
    have e : m1 = m0 := h2
    subst e
    exact ⟨h1, rfl, trivial⟩
  | conc t =>
    rcases hm with (hm | ⟨_, hm⟩) | ⟨s, hs⟩
    · cases hm
    · cases hm
    · have e : im = .conc s := hs
      subst e
      exact ⟨h2, h1, trivial⟩
  | starEx x =>
    have e : m1 = m0 := h2
    subst e
    exact ⟨h1, rfl, h3⟩

theorem markRel_unrev {i f : PFact} {m0 m1 : Mark} (hm : MarkRev i f)
    (h : MarkRel (pmOf i f) (fmOf i f) m1 m0) : MarkRel i.mark f.mark m0 m1 := by
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  unfold MarkRel at h ⊢
  unfold MarkRev at hm
  obtain ⟨h1, h2, h3⟩ := h
  cases fm with
  | star =>
    have e : m0 = m1 := h2
    subst e
    exact ⟨h1, rfl, trivial⟩
  | conc t =>
    rcases hm with (hm | ⟨_, hm⟩) | ⟨s, hs⟩
    · cases hm
    · cases hm
    · have e : im = .conc s := hs
      subst e
      exact ⟨h2, h1, trivial⟩
  | starEx x =>
    have e : m0 = m1 := h2
    subst e
    exact ⟨h1, rfl, h3⟩

/-- The tails of `revKinds` cover the converse, for all nine shapes. -/
theorem pathRel_rev {ip fp : List Acc} {ik fk : Kind} {p0 p1 : List Acc}
    (h : PathRel ip ik fp fk p0 p1) :
    PathRel fp (revKinds ik fk).1 ip (revKinds ik fk).2 p1 p0 := by
  obtain ⟨σ, τ, h0, h1, hi, hf⟩ := h
  cases ik <;> cases fk
  case star.star ei ef =>
    obtain ⟨hτ, hef⟩ := hf
    subst hτ
    refine ⟨τ, τ, h1, h0, empty_admits τ, rfl, ?_⟩
    have hei : ei.admits τ = true := hi
    rw [admits_union, hei, hef]; rfl
  case any.star ef =>
    obtain ⟨hτ, hef⟩ := hf
    subst hτ
    exact ⟨τ, τ, h1, h0, empty_admits τ, rfl, hef⟩
  case exact.star ef =>
    obtain ⟨hτ, _⟩ := hf
    subst hτ
    exact ⟨τ, τ, h1, h0, hi, hi⟩
  case exact.exact => exact ⟨τ, σ, h1, h0, hf, hi⟩
  case star.exact => exact ⟨τ, σ, h1, h0, hf, trivial⟩
  case any.exact => exact ⟨τ, σ, h1, h0, hf, trivial⟩
  case exact.any => exact ⟨τ, σ, h1, h0, trivial, hi⟩
  case star.any => exact ⟨τ, σ, h1, h0, trivial, trivial⟩
  case any.any => exact ⟨τ, σ, h1, h0, trivial, trivial⟩

/-- On `ExactShape` the tails of `revKinds` give nothing more than the converse. -/
theorem pathRel_unrev {ip fp : List Acc} {ik fk : Kind} {p0 p1 : List Acc}
    (hk : ExactShape ik fk) (h : PathRel fp (revKinds ik fk).1 ip (revKinds ik fk).2 p1 p0) :
    PathRel ip ik fp fk p0 p1 := by
  obtain ⟨σ, τ, h1, h0, hi, hf⟩ := h
  cases ik <;> cases fk
  case star.star ei ef =>
    obtain ⟨hτ, hu⟩ := hf
    subst hτ
    have hu' : (ei.union ef).admits τ = true := hu
    rw [admits_union] at hu'
    cases hei : ei.admits τ
    · rw [hei] at hu'; cases hu'
    · rw [hei] at hu'
      exact ⟨τ, τ, h0, h1, hei, rfl, hu'⟩
  case any.star ef =>
    obtain ⟨hτ, hef⟩ := hf
    subst hτ
    exact ⟨τ, τ, h0, h1, trivial, rfl, hef⟩
  case exact.star ef =>
    have e1 : σ = [] := hi
    have e2 : τ = [] := hf
    subst e1 e2
    exact ⟨[], [], h0, h1, rfl, rfl, admits_nil ef⟩
  case exact.exact => exact ⟨τ, σ, h0, h1, hf, hi⟩
  case star.exact e =>
    have he : e = Excl.empty := hk
    subst he
    exact ⟨τ, σ, h0, h1, empty_admits τ, hi⟩
  case any.exact => exact ⟨τ, σ, h0, h1, trivial, hi⟩
  case exact.any => exact ⟨τ, σ, h0, h1, hf, trivial⟩
  case star.any e =>
    have he : e = Excl.empty := hk
    subst he
    exact ⟨τ, σ, h0, h1, empty_admits τ, trivial⟩
  case any.any => exact ⟨τ, σ, h0, h1, trivial, trivial⟩

/-! ## 2. Soundness and exactness of `revEdge` -/

/-- THEOREM 1. The reversed record covers the converse of the record relation.
    The tail shape can be any; only the marks need the condition. -/
theorem revEdge_sound {i f : PFact} {l0 l1 : Loc} (hm : MarkRev i f) :
    den i f l0 l1 → den (revEdge i f).1 (revEdge i f).2 l1 l0 := by
  intro h
  obtain ⟨⟨hb0, hb1⟩, hk, hp⟩ := den_split.mp h
  rw [revEdge_eq]
  exact den_split.mpr ⟨⟨hb1, hb0⟩, markRel_rev hm hk, pathRel_rev hp⟩

#print axioms revEdge_sound

/-- THEOREM 2. On `ExactShape`, a mark-reversible record has an exact reversal. -/
theorem revEdge_exact {i f : PFact} {l0 l1 : Loc} (hk : ExactShape i.kind f.kind)
    (hm : MarkRev i f) :
    den i f l0 l1 ↔ den (revEdge i f).1 (revEdge i f).2 l1 l0 := by
  refine ⟨revEdge_sound hm, fun h => ?_⟩
  rw [revEdge_eq] at h
  obtain ⟨⟨hb1, hb0⟩, hmk, hp⟩ := den_split.mp h
  exact den_split.mpr ⟨⟨hb0, hb1⟩, markRel_unrev hm hmk, pathRel_unrev hk hp⟩

#print axioms revEdge_exact

/-- An empty premise exclusion makes every shape exact (all nine cases). -/
theorem exactShape_of_premEmpty {ik fk : Kind} (h : PremEmpty ik) : ExactShape ik fk := by
  cases ik <;> cases fk
  case star.exact e => exact h
  case star.any e => exact h
  all_goals exact True.intro

/-- THEOREM 2'. THE SPEC ASSERTION (replaces finding F8). If the premise
    exclusion is empty and the record is mark-reversible, the reversal is exact
    for every tail shape. The exclusion of the record lives in its conclusion
    `*/E`, and `revKinds` moves it to the new conclusion. -/
theorem rev_exact_of_empty_premise {i f : PFact} {l0 l1 : Loc} (he : PremEmpty i.kind)
    (hm : MarkRev i f) :
    den i f l0 l1 ↔ den (revEdge i f).1 (revEdge i f).2 l1 l0 :=
  revEdge_exact (exactShape_of_premEmpty he) hm

#print axioms rev_exact_of_empty_premise

/-! ### Records with the conclusion mark `*∖x` (version 5, question 3)

A cleaner puts the mark `*∖x` on a final fact, so a record `i → f` can have
`f.mark = starEx x`. ANSWER: such a record IS mark-reversible, for EVERY premise mark,
and it reverses EXACTLY (with the tail condition of THEOREM 2 / 2'). Reason: its mark
relation is a partial identity (`markRel_starEx_iff`): the mark `m` goes to `m` if the
premise admits `m` and `m ∉ x`. `revEdge` gives the new premise mark `i.mark` and the new
conclusion mark `*∖x`, which is the same partial identity read in the other direction.
The new premise never has `starEx` (`revEdge_premise_mark`), so the reversed record obeys
the premise invariant again. -/

/-- THEOREM 2a. The reversal of a `*∖x` record is exact on `ExactShape`, for every premise
    mark. -/
theorem revEdge_starEx_exact {i f : PFact} {x : List Mark} {l0 l1 : Loc}
    (hk : ExactShape i.kind f.kind) (hf : f.mark = .starEx x) :
    den i f l0 l1 ↔ den (revEdge i f).1 (revEdge i f).2 l1 l0 :=
  revEdge_exact hk (markRev_starEx hf)

#print axioms revEdge_starEx_exact

/-- THEOREM 2a'. A `*∖x` record with an empty premise exclusion (every emitted premise)
    reverses exactly, for every tail shape and every premise mark. -/
theorem rev_starEx_exact {i f : PFact} {x : List Mark} {l0 l1 : Loc}
    (he : PremEmpty i.kind) (hf : f.mark = .starEx x) :
    den i f l0 l1 ↔ den (revEdge i f).1 (revEdge i f).2 l1 l0 :=
  rev_exact_of_empty_premise he (markRev_starEx hf)

#print axioms rev_starEx_exact

/-- The reversed record of a `*∖x` record keeps `*∖x` on its conclusion and the old
    premise mark on its premise. -/
theorem revEdge_starEx_marks {i f : PFact} {x : List Mark} (hf : f.mark = .starEx x) :
    (revEdge i f).1.mark = i.mark ∧ (revEdge i f).2.mark = .starEx x := by
  rw [revEdge_eq]
  obtain ⟨fb, fp, fk, fm⟩ := f
  have e : fm = .starEx x := hf
  subst e
  exact ⟨rfl, rfl⟩

#print axioms revEdge_starEx_marks

/-- A reversed record keeps the premise invariant: if the premise mark is `*` or concrete
    (never `*∖x`), the new premise mark is `*` or concrete too. -/
theorem revEdge_premise_mark {i f : PFact} (hi : i.mark = .star ∨ ∃ t, i.mark = .conc t) :
    (revEdge i f).1.mark = .star ∨ ∃ t, (revEdge i f).1.mark = .conc t := by
  rw [revEdge_eq]
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases fm with
  | star => exact hi
  | conc t => exact Or.inr ⟨t, rfl⟩
  | starEx _ => exact hi

#print axioms revEdge_premise_mark

/-- Every initial fact that the abstraction policy emits has the empty premise
    exclusion. -/
theorem policy_premEmpty (demand : MethodId → List PFact) (m : MethodId) (a : PFact) :
    PremEmpty (policy demand m a).kind := by
  unfold policy
  split
  · exact True.intro
  · split <;> rfl

/-- An answer of a request keeps an empty premise exclusion. -/
theorem answerInit_premEmpty {i a : PFact} {t : Mark} (h : PremEmpty i.kind) :
    PremEmpty (answerInit i a t).kind := by
  unfold answerInit
  split
  · exact True.intro
  · exact h

/-- An answer of a request has a concrete premise mark, so its records are
    mark-reversible. -/
theorem answerInit_markRev {i a f : PFact} {t : Mark} : MarkRev (answerInit i a t) f := by
  unfold answerInit
  split
  · exact Or.inr ⟨t, rfl⟩
  · exact Or.inr ⟨t, rfl⟩

#print axioms policy_premEmpty
#print axioms answerInit_premEmpty
#print axioms answerInit_markRev

/-! ### Counterexample A: a non-empty premise exclusion with a `$` conclusion

The record `(0,.,*,{1},*) → (0,.,$,{},*)` maps `0.σ` (σ does not start with `1`)
to `0`. Its converse maps `0` to every `0.σ` with σ not starting with `1`. This
needs a conclusion tail that is NOT correlated (the premise `0` is exact) and
that HAS an exclusion. `[any]` has no exclusion and `*` is correlated, so no fact
pair gives this relation. `revEdge` gives `$ → [any]`: sound, and the exclusion is
lost. So the condition `PremEmpty` of THEOREM 2' is necessary. The abstraction
never emits such a premise (`policy_premEmpty`). -/

def cxI : PFact := ⟨0, [], .star (.set [1]), .star⟩
def cxF : PFact := ⟨0, [], .exact, .star⟩
def cxL0 : Loc := ⟨0, [1], 0⟩
def cxL1 : Loc := ⟨0, [], 0⟩

example : revEdge cxI cxF = (⟨0, [], .exact, .star⟩, ⟨0, [], .any, .star⟩) := by decide

/-- The reversed record relates `0` to `0.1` ... -/
theorem cx_rev_holds : den (revEdge cxI cxF).1 (revEdge cxI cxF).2 cxL1 cxL0 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [1], rfl, rfl, rfl, trivial⟩

/-- ... but the forward record does not relate `0.1` to `0` (`1` is excluded). -/
theorem cx_fwd_fails : ¬ den cxI cxF cxL0 cxL1 := by
  rintro ⟨_, _, _, _, _, σ, τ, h0, _, hi, _⟩
  have e : σ = [1] := h0.symm
  subst e
  have hi' : (Excl.set [1]).admits [1] = true := hi
  exact absurd hi' (by decide)

theorem star_exact_not_exact :
    ¬ ∀ l0 l1, den (revEdge cxI cxF).1 (revEdge cxI cxF).2 l1 l0 → den cxI cxF l0 l1 :=
  fun H => cx_fwd_fails (H _ _ cx_rev_holds)

#print axioms star_exact_not_exact

/-- No fact pair at all reverses `(0,.,*,{1},*) → (0,.,$,{},*)` exactly. -/
theorem star_exact_no_exact_rev :
    ¬ ∃ i' f' : PFact, ∀ l0 l1, den cxI cxF l0 l1 ↔ den i' f' l1 l0 := by
  rintro ⟨⟨ib, ip, ik, im⟩, ⟨fb, fp, fk, fm⟩, H⟩
  -- 0 ↦ 0 and 0.2 ↦ 0 are forward pairs; 0.1 ↦ 0 is not.
  have ha : den cxI cxF ⟨0, [], 0⟩ ⟨0, [], 0⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
  have hb : den cxI cxF ⟨0, [2], 0⟩ ⟨0, [], 0⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [2], [], rfl, rfl, rfl, rfl⟩
  obtain ⟨a1, a2, a3, a4, a4', σa, τa, a5, a6, a7, _⟩ := (H _ _).mp ha
  obtain ⟨_, _, _, _, _, σb, τb, b5, b6, _, b8⟩ := (H _ _).mp hb
  obtain ⟨hip, hσa⟩ := nil_eq_append a5
  obtain ⟨hfp, _⟩ := nil_eq_append a6
  subst hip hfp hσa
  have hσb : σb = [] := (nil_eq_append b5).2
  have hτb : τb = [2] := b6.symm
  subst hσb hτb
  -- the conclusion tail relates the empty continuation to `[2]`: it is `[any]`
  cases fk with
  | star e => have e' : ([2] : List Acc) = [] := b8.1; cases e'
  | exact => have e' : ([2] : List Acc) = [] := b8; cases e'
  | any =>
    -- so the pair also relates `0` to `0.1`, which is not a forward pair
    apply cx_fwd_fails
    exact (H cxL0 cxL1).mpr ⟨a1, a2, a3, a4, a4', [], [1], rfl, rfl, a7, trivial⟩

#print axioms star_exact_no_exact_rev

/-! ### Counterexample B: a mark-producing record under a `*`-mark premise

A record with `i.mark = *` and `f.mark = conc t` maps a location with ANY mark to
a location with mark `t`. Its converse must map the mark `t` to EVERY mark. In
`den` the conclusion mark is a function of the premise mark (`f.mark.out`), so no
fact pair covers this converse, not even as an over-approximation. -/

/-- No fact pair covers the converse of a non-empty mark-producing record under
    a `*`-mark premise. -/
theorem no_rev_of_star_conc {i f : PFact} {t : Mark} (hi : i.mark = .star)
    (hf : f.mark = .conc t) {l0 l1 : Loc} (h : den i f l0 l1) :
    ¬ ∃ i' f' : PFact, ∀ l0 l1, den i f l0 l1 → den i' f' l1 l0 := by
  rintro ⟨i', f', H⟩
  have h' : den i f ⟨l0.base, l0.path, l0.mark + 1⟩ l1 := by
    obtain ⟨h1, h2, _, h4, _, σ, τ, h5, h6, h7, h8⟩ := h
    refine ⟨h1, h2, ?_, ?_, ?_, σ, τ, h5, h6, h7, h8⟩
    · rw [hi]; trivial
    · rw [h4, hf]; rfl
    · rw [hf]; trivial
  obtain ⟨_, _, _, e1, _⟩ := H _ _ h
  obtain ⟨_, _, _, e2, _⟩ := H _ _ h'
  have e : l0.mark + 1 = l0.mark := e2.trans e1.symm
  exact absurd e (Nat.succ_ne_self _)

#print axioms no_rev_of_star_conc

/-- The general form: if two entry locations with DIFFERENT marks go to the same exit
    location, no fact pair covers the converse (in `den` the conclusion mark is a function
    of the premise mark). This is the only obstacle: `MarkRev` excludes exactly the
    records with a concrete conclusion mark and a premise mark that admits more than one
    mark. -/
theorem no_rev_of_two_marks {i f : PFact} {l0 l0' l1 : Loc} (h : den i f l0 l1)
    (h' : den i f l0' l1) (hne : l0.mark ≠ l0'.mark) :
    ¬ ∃ i' f' : PFact, ∀ l0 l1, den i f l0 l1 → den i' f' l1 l0 := by
  rintro ⟨i', f', H⟩
  obtain ⟨_, _, _, e1, _⟩ := H _ _ h
  obtain ⟨_, _, _, e2, _⟩ := H _ _ h'
  exact hne (e1.trans e2.symm)

#print axioms no_rev_of_two_marks

-- A `*∖{1}` PREMISE (never emitted) with a concrete conclusion mark: the marks 0 and 2 both
-- go to the mark 5, so no fact pair covers the converse. `MarkRev` is false for it.
def mxI : PFact := ⟨0, [], .exact, .starEx [1]⟩
def mxF : PFact := ⟨0, [], .exact, .conc 5⟩

example : ¬ ∃ i' f' : PFact, ∀ l0 l1, den mxI mxF l0 l1 → den i' f' l1 l0 :=
  no_rev_of_two_marks (l0 := ⟨0, [], 0⟩) (l0' := ⟨0, [], 2⟩) (l1 := ⟨0, [], 5⟩)
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩ (by decide)

example : ¬ MarkRev mxI mxF := by
  rintro ((h | ⟨_, h⟩) | ⟨_, h⟩) <;> cases h

-- A witness: `(0,.,$,{},*) → (0,.,$,{},T=5)` (a mark conversion rule).
def mpI : PFact := ⟨0, [], .exact, .star⟩
def mpF : PFact := ⟨0, [], .exact, .conc 5⟩
def mpL0 : Loc := ⟨0, [], 0⟩
def mpL1 : Loc := ⟨0, [], 5⟩

theorem mp_fwd : den mpI mpF mpL0 mpL1 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

example : ¬ ∃ i' f' : PFact, ∀ l0 l1, den mpI mpF l0 l1 → den i' f' l1 l0 :=
  no_rev_of_star_conc rfl rfl mp_fwd

-- `revEdge` gives `(0,.,$,{},5) → (0,.,$,{},*)`: it maps 5 to 5 only, so it is unsound here.
example : revEdge mpI mpF = (⟨0, [], .exact, .conc 5⟩, ⟨0, [], .exact, .star⟩) := by decide
example : ¬ den (revEdge mpI mpF).1 (revEdge mpI mpF).2 mpL1 mpL0 := by
  rintro ⟨_, _, _, h, _⟩
  exact absurd h (by decide)

/-! ## 3. Involution -/

/-- Every reversed record is mark-reversible. -/
theorem revEdge_markRev (i f : PFact) : MarkRev (revEdge i f).1 (revEdge i f).2 := by
  rw [revEdge_eq]
  unfold MarkRev
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases fm with
  | star => exact Or.inl (Or.inl rfl)
  | conc t => exact Or.inr ⟨t, rfl⟩
  | starEx x => exact Or.inl (Or.inr ⟨x, rfl⟩)

#print axioms revEdge_markRev

/-- Every reversed record has an exact shape (a reversed `*` premise has `{}`). -/
theorem revEdge_exactShape (i f : PFact) :
    ExactShape (revEdge i f).1.kind (revEdge i f).2.kind := by
  rw [revEdge_eq]
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases ik <;> cases fk <;> exact True.intro

/-- THEOREM 3. Reversal twice gives the same relation. -/
theorem revEdge_involutive {i f : PFact} {l0 l1 : Loc} (hk : ExactShape i.kind f.kind)
    (hm : MarkRev i f) :
    den (revEdge (revEdge i f).1 (revEdge i f).2).1 (revEdge (revEdge i f).1 (revEdge i f).2).2 l0 l1
      ↔ den i f l0 l1 :=
  (revEdge_exact (revEdge_exactShape i f) (revEdge_markRev i f)).symm.trans (revEdge_exact hk hm).symm

#print axioms revEdge_involutive

/-- A canonical record: a `*` premise has the empty exclusion, and the shape is
    one that `revKinds` produces. Every reversed record is canonical. -/
def CanonK : Kind → Kind → Prop
  | .star e, .star _ => e = Excl.empty
  | .exact,  .exact  => True
  | .exact,  .any    => True
  | .any,    .exact  => True
  | .any,    .any    => True
  | _,       _       => False

theorem revEdge_canon (i f : PFact) : CanonK (revEdge i f).1.kind (revEdge i f).2.kind := by
  rw [revEdge_eq]
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases ik <;> cases fk
  all_goals first | exact True.intro | rfl

/-- On a canonical mark-reversible record, reversal twice gives the same syntax. -/
theorem revEdge_revEdge {i f : PFact} (hc : CanonK i.kind f.kind) (hm : MarkRev i f) :
    revEdge (revEdge i f).1 (revEdge i f).2 = (i, f) := by
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  have hmk : (fm = .star ∨ ∃ x, fm = .starEx x) ∨ ∃ t s, fm = .conc t ∧ im = .conc s := by
    rcases hm with h | ⟨s, hs⟩
    · exact Or.inl h
    · cases fm with
      | star => exact Or.inl (Or.inl rfl)
      | conc t => exact Or.inr ⟨t, s, rfl, hs⟩
      | starEx x => exact Or.inl (Or.inr ⟨x, rfl⟩)
  rcases hmk with (hfm | ⟨x, hfm⟩) | ⟨t, s, hfm, him⟩
  · subst hfm
    cases ik <;> cases fk
    case star.star e ef =>
      have he : e = Excl.empty := hc
      subst he
      cases ef <;> rfl
    all_goals first | rfl | exact hc.elim
  · subst hfm
    cases ik <;> cases fk
    case star.star e ef =>
      have he : e = Excl.empty := hc
      subst he
      cases ef <;> rfl
    all_goals first | rfl | exact hc.elim
  · subst hfm him
    cases ik <;> cases fk
    case star.star e ef =>
      have he : e = Excl.empty := hc
      subst he
      cases ef <;> rfl
    all_goals first | rfl | exact hc.elim

#print axioms revEdge_revEdge

/-! ## 4. The reversed premise serves the facts below its chain -/

theorem tailSubB_empty (k : Kind) : tailSubB (.star Excl.empty) k = true := by
  cases k with
  | star e => cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- A reversed `*` premise has the empty exclusion. -/
theorem rev_premise_star {i f : PFact} {e : Excl} (h : (revEdge i f).1.kind = .star e) :
    e = Excl.empty := by
  rw [revEdge_eq] at h
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases ik <;> cases fk <;> first | (injection h with h'; exact h'.symm) | cases h

/-- THEOREM 4. A reversed `*` premise is applicable to EVERY fact at or below
    its chain (same base, compatible mark), whatever its tail: the exclusion of
    the record is in the new conclusion, not in the new premise. -/
theorem applicable_rev_premise {i f c : PFact} {r : List Acc}
    (hs : (revEdge i f).1.kind.isStar = true) (hb : c.base = f.base)
    (hp : c.path = f.path ++ r) (hm : markSubB (revEdge i f).1.mark c.mark = true) :
    applicable (revEdge i f).1 c = true := by
  have hk : ∃ e, (revEdge i f).1.kind = .star e := by
    cases h : (revEdge i f).1.kind with
    | star e => exact ⟨e, rfl⟩
    | any => rw [h] at hs; cases hs
    | exact => rw [h] at hs; cases hs
  obtain ⟨e, he⟩ := hk
  have he0 := rev_premise_star he
  subst he0
  have hbase : (revEdge i f).1.base = f.base := by rw [revEdge_eq]
  have hpath : (revEdge i f).1.path = f.path := by rw [revEdge_eq]
  unfold applicable coversB
  rw [he, hbase, hpath, hm, hb, hp, Nat.beq_refl, dropPrefix_append]
  cases r with
  | nil =>
    show (tailSubB (Kind.star Excl.empty) c.kind && (!(Kind.star Excl.empty).isAny || c.kind.isAny)) = true
    rw [tailSubB_empty]; rfl
  | cons a r => exact empty_admits (a :: r)

#print axioms applicable_rev_premise

/-! ## 5. Statement reversal

`s.step l l'` keeps an untouched base and regenerates a touched base only by
the micro edges. The reversed statement must keep this form. Two points:

  * A reversed micro edge reads from the TARGET base of the forward edge. The
    WF condition needs that base in `touched`. So `touched := s.touched ++ targets`.
  * A target base `b` that is NOT in `s.touched` keeps its old value in the
    forward step (a weak update: `l ↦ l` for base `b`). In the reversed
    statement `b` is touched, so this identity pair must come from an edge:
    the identity micro edge `(b,.,*,{},*) → (b,.,*,{},*)`.

`revNoId_breaks` shows that without the identity edges the iff fails. -/

def targets (s : Stmt) : List Base := s.edges.map (fun e => e.2.base)

/-- The identity micro edge on base `b`. -/
def idEdge (b : Base) : MicroEdge :=
  (⟨b, [], .star Excl.empty, .star⟩, ⟨b, [], .star Excl.empty, .star⟩)

/-- The reversed statement summary. -/
def Stmt.rev (s : Stmt) : Stmt :=
  { touched := s.touched ++ targets s
    edges   := s.edges.map (fun e => revEdge e.1 e.2) ++
               ((targets s).filter (fun b => !memB b s.touched)).map idEdge }

theorem den_idEdge {b : Base} {l l' : Loc} :
    den (idEdge b).1 (idEdge b).2 l l' ↔ l.base = b ∧ l' = l := by
  constructor
  · rintro ⟨h1, h2, _, h4, _, σ, τ, h5, h6, _, h7, _⟩
    refine ⟨h1, ?_⟩
    obtain ⟨lb, lp, lm⟩ := l
    obtain ⟨lb', lp', lm'⟩ := l'
    have e5 : lp = σ := h5
    have e6 : lp' = τ := h6
    have e4 : lm' = lm := h4
    have e2 : lb' = lb := h2.trans h1.symm
    rw [e2, e6, h7, ← e5, e4]
  · rintro ⟨h1, h2⟩
    rw [h2]
    exact ⟨h1, h1, trivial, rfl, trivial, l.path, l.path, rfl, rfl, empty_admits _, rfl,
      empty_admits _⟩

/-- Every edge of a reversed statement reads from a touched base (WF holds for
    every reversed statement, with no condition). -/
theorem rev_touched (s : Stmt) :
    ∀ e, e ∈ (Stmt.rev s).edges → memB e.1.base (Stmt.rev s).touched = true := by
  intro e he
  show memB e.1.base (s.touched ++ targets s) = true
  rw [memB_append]
  have ht : memB e.1.base (targets s) = true := by
    rcases List.mem_append.mp he with h1 | h2
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp h1
      exact memB_of_mem (List.mem_map.mpr ⟨e0, he0, rfl⟩)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h2
      exact memB_of_mem (List.mem_filter.mp hb).1
  rw [ht, Bool.or_true]

/-- Forward step ⇒ reversed step, for mark-reversible edges of any shape. -/
theorem Stmt.rev_step_sound {s : Stmt} (hrv : ∀ e, e ∈ s.edges → MarkRev e.1 e.2)
    {l l' : Loc} : s.step l l' → (Stmt.rev s).step l' l := by
  intro h
  rcases h with ⟨hb, hl⟩ | ⟨e, he, hd⟩
  · rw [hl]
    cases ht : memB l.base (targets s) with
    | false =>
      refine Or.inl ⟨?_, rfl⟩
      show memB l.base (s.touched ++ targets s) = false
      rw [memB_append, hb, ht]; rfl
    | true =>
      refine Or.inr ⟨idEdge l.base, ?_, den_idEdge.mpr ⟨rfl, rfl⟩⟩
      show idEdge l.base ∈ s.edges.map (fun e => revEdge e.1 e.2) ++
        ((targets s).filter (fun b => !memB b s.touched)).map idEdge
      refine List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨l.base, ?_, rfl⟩))
      exact List.mem_filter.mpr ⟨mem_of_memB ht, by rw [hb]; rfl⟩
  · refine Or.inr ⟨revEdge e.1 e.2, ?_, revEdge_sound (hrv e he) hd⟩
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨e, he, rfl⟩))

#print axioms Stmt.rev_step_sound

/-- The edges of `s` are exactly reversible. -/
def RevEdges (s : Stmt) : Prop :=
  ∀ e, e ∈ s.edges → ExactShape e.1.kind e.2.kind ∧ MarkRev e.1 e.2

/-- Reversed step ⇒ forward step, for exactly reversible edges. -/
theorem Stmt.rev_step_complete {s : Stmt} (hrv : RevEdges s) {l l' : Loc} :
    (Stmt.rev s).step l' l → s.step l l' := by
  intro h
  rcases h with ⟨hb, rfl⟩ | ⟨e', he', hd⟩
  · refine Or.inl ⟨?_, rfl⟩
    have hb' : (memB l.base s.touched || memB l.base (targets s)) = false := by
      rw [← memB_append]; exact hb
    cases ht : memB l.base s.touched
    · rfl
    · rw [ht] at hb'; cases hb'
  · rcases List.mem_append.mp he' with h1 | h2
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h1
      exact Or.inr ⟨e, he, (revEdge_exact (hrv e he).1 (hrv e he).2).mpr hd⟩
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp h2
      have hnb := (List.mem_filter.mp hbm).2
      obtain ⟨hlb, rfl⟩ := den_idEdge.mp hd
      refine Or.inl ⟨?_, rfl⟩
      rw [hlb]
      cases ht : memB b s.touched
      · rfl
      · rw [ht] at hnb; cases hnb

/-- THEOREM 5. The backward step is the converse of the forward step. -/
theorem Stmt.rev_step_iff {s : Stmt} (h : RevEdges s) {l l' : Loc} :
    s.step l l' ↔ (Stmt.rev s).step l' l :=
  ⟨Stmt.rev_step_sound (fun e he => (h e he).2), Stmt.rev_step_complete h⟩

#print axioms Stmt.rev_step_iff

/-- The reversed statement has exactly reversible edges again. -/
theorem rev_revEdges (s : Stmt) : RevEdges (Stmt.rev s) := by
  intro e he
  rcases List.mem_append.mp he with h1 | h2
  · obtain ⟨e0, _, rfl⟩ := List.mem_map.mp h1
    exact ⟨revEdge_exactShape _ _, revEdge_markRev _ _⟩
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h2
    exact ⟨True.intro, Or.inl (Or.inl rfl)⟩

/-! ### Counterexample C: the identity edges are necessary -/

/-- Reversal without the identity edges. -/
def Stmt.revNoId (s : Stmt) : Stmt :=
  { touched := s.touched ++ targets s, edges := s.edges.map (fun e => revEdge e.1 e.2) }

/-- `b := b ∪ a` as a weak update: base 11 is touched, base 12 is a target and
    is NOT touched (it keeps its old value). -/
def sWeak : Stmt :=
  { touched := [11],
    edges := [(⟨11, [], .star Excl.empty, .star⟩, ⟨12, [], .star Excl.empty, .star⟩)] }

def lB : Loc := ⟨12, [], 0⟩

theorem revNoId_breaks : sWeak.step lB lB ∧ ¬ (Stmt.revNoId sWeak).step lB lB := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
  rintro (⟨hb, _⟩ | ⟨e, he, hd⟩)
  · exact absurd hb (by decide)
  · have e1 : e = revEdge (⟨11, [], .star Excl.empty, .star⟩ : PFact) ⟨12, [], .star Excl.empty, .star⟩ :=
      List.mem_singleton.mp he
    subst e1
    obtain ⟨_, h2, _⟩ := hd
    exact absurd h2 (by decide)

#print axioms revNoId_breaks

/-- With the identity edges the pair is there (an instance of `Stmt.rev_step_iff`). -/
example : (Stmt.rev sWeak).step lB lB := by
  refine (Stmt.rev_step_iff ?_).mp (Or.inl ⟨rfl, rfl⟩)
  intro e he
  have e1 := List.mem_singleton.mp he
  subst e1
  exact ⟨True.intro, Or.inl (Or.inl rfl)⟩

/-! ## 6. Program reversal (with calls)

`Program.rev` swaps entry and exit of every method, reverses every CFG edge,
reverses every statement (`Stmt.rev`) and every call:
  * `c'.callee = c.callee`, `c'.touched = c.touched`;
  * `c'.toCallee   := reversed c.fromCallee` (caller post-location → callee EXIT
    location, for example `r.* → return.*`, `ai.* → argi.*`);
  * `c'.fromCallee := reversed c.toCallee` (callee ENTRY location → caller
    pre-location).
The bindings are reversed by `revEdge`. Their shape is `* → *` with mark `*`, so
the reversal is exact on them (`bindRev_of_star`).

A cleaner `Instr.clean cl` and a type filter `Instr.filt b may` stay as they are
(only the CFG edge turns round). Each concrete step keeps the location and has a
condition on that location only (`cl.cleansB l = false`; `l.base = b → may l.path`):
it is a partial identity, so its converse is the same step.

Proof route. `RevSim P Q` says that `Q` simulates the converse of every
instruction of `P`. One induction on `Flow P` (the nested callee flow is a
sub-derivation, so its induction hypothesis is there) gives a backward segment
in `Q`. `Program.rev` gives `RevSim P (rev P)` (soundness of the reversal) and
`RevSim (rev P) P` (exactness), so the theorem is an iff. -/

def Call.rev (c : Call) : Call :=
  { callee     := c.callee
    touched    := c.touched
    toCallee   := c.fromCallee.map (fun e => revEdge e.1 e.2)
    fromCallee := c.toCallee.map (fun e => revEdge e.1 e.2) }

/-- The reversed instruction. A cleaner and a type filter are partial identities on the
    locations, so they are their own converse. -/
def revInstr : Instr → Instr
  | .stmt s      => .stmt (Stmt.rev s)
  | .call c      => .call (Call.rev c)
  | .clean cl    => .clean cl
  | .filt b may  => .filt b may

def revE (e : MethodId × Node × Instr × Node) : MethodId × Node × Instr × Node :=
  (e.1, e.2.2.2, revInstr e.2.2.1, e.2.1)

/-- The reversed program: entry and exit swapped in every method, every CFG
    edge reversed, every statement and every call reversed. -/
def Program.rev (P : Program) : Program :=
  { entry := P.exit, exit := P.entry, edges := P.edges.map revE }

/-- Every statement of `P` has exactly reversible micro edges. -/
def RevStmts (P : Program) : Prop :=
  ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → RevEdges s

/-- A binding edge is exactly reversible. -/
def BindRev (e : MicroEdge) : Prop := ExactShape e.1.kind e.2.kind ∧ MarkRev e.1 e.2

def RevCalls (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    (∀ e, e ∈ c.toCallee → BindRev e) ∧ (∀ e, e ∈ c.fromCallee → BindRev e)

/-- The binding targets are mark-agnostic too (needed for WF of the reversed
    program: a reversed binding reads from the forward target). -/
def BindTargetsStar (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    (∀ e, e ∈ c.toCallee → e.2.mark = .star) ∧ (∀ e, e ∈ c.fromCallee → e.2.mark = .star)

/-- The binding shape `* → *` with the mark `*` is exactly reversible. -/
theorem bindRev_of_star {e : MicroEdge} {e1 e2 : Excl} (h1 : e.1.kind = .star e1)
    (h2 : e.2.kind = .star e2) (hm : e.2.mark = .star) : BindRev e := by
  refine ⟨?_, markRev_star hm⟩
  rw [h1, h2]; exact True.intro

/-! ### Segments with calls -/

/-- A segment flow in `M` from `(n, l)`: statement steps, call-to-return passes,
    and call steps that contain a FULL callee flow (entry to exit). -/
inductive SegC (P : Program) (M : MethodId) (n : Node) (l : Loc) : Node → Loc → Prop where
  | refl : SegC P M n l n l
  | step {n1 l1 s n2 l2} : SegC P M n l n1 l1 → (M, n1, Instr.stmt s, n2) ∈ P.edges →
      s.step l1 l2 → SegC P M n l n2 l2
  | pass {n1 l1 c n2} : SegC P M n l n1 l1 → (M, n1, Instr.call c, n2) ∈ P.edges →
      memB l1.base c.touched = false → SegC P M n l n2 l1
  | call {n1 l1 c n2 e1 e2 la lb l2} : SegC P M n l n1 l1 → (M, n1, Instr.call c, n2) ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l1 la →
      Flow P c.callee la (P.exit c.callee) lb →
      e2 ∈ c.fromCallee → den e2.1 e2.2 lb l2 → SegC P M n l n2 l2
  -- a cleaner: the location stays unless the cleaner cleans it (as `Flow.clean`)
  | clean {n1 l1 cl n2} : SegC P M n l n1 l1 → (M, n1, Instr.clean cl, n2) ∈ P.edges →
      cl.cleansB l1 = false → SegC P M n l n2 l1
  -- a type filter: the location stays if its path may exist (as `Flow.filt`)
  | filt {n1 l1 b may n2} : SegC P M n l n1 l1 → (M, n1, Instr.filt b may, n2) ∈ P.edges →
      (l1.base = b → may l1.path = true) → SegC P M n l n2 l1

theorem SegC.trans {P : Program} {M : MethodId} {n n1 n2 : Node} {l l1 l2 : Loc}
    (h1 : SegC P M n l n1 l1) (h2 : SegC P M n1 l1 n2 l2) : SegC P M n l n2 l2 := by
  induction h2 with
  | refl => exact h1
  | step _ he hs ih => exact SegC.step ih he hs
  | pass _ he hb ih => exact SegC.pass ih he hb
  | call _ he he1 hd1 hf he2 hd2 ih => exact SegC.call ih he he1 hd1 hf he2 hd2
  | clean _ he hc ih => exact SegC.clean ih he hc
  | filt _ he hf ih => exact SegC.filt ih he hf

theorem flow_of_segC {P : Program} {M : MethodId} {l0 l : Loc} {n : Node}
    (h : SegC P M (P.entry M) l0 n l) : Flow P M l0 n l := by
  induction h with
  | refl => exact Flow.start M l0
  | step _ he hs ih => exact Flow.step ih he hs
  | pass _ he hb ih => exact Flow.pass ih he hb
  | call _ he he1 hd1 hf he2 hd2 ih => exact Flow.call ih he he1 hd1 hf he2 hd2
  | clean _ he hc ih => exact Flow.clean ih he hc
  | filt _ he hf ih => exact Flow.filt ih he hf

theorem segC_of_flow {P : Program} {M : MethodId} {l0 l : Loc} {n : Node}
    (h : Flow P M l0 n l) : SegC P M (P.entry M) l0 n l := by
  induction h with
  | start M l0 => exact SegC.refl
  | step _ he hs ih => exact SegC.step ih he hs
  | pass _ he hb ih => exact SegC.pass ih he hb
  | call _ he he1 hd1 hf he2 hd2 ih _ => exact SegC.call ih he he1 hd1 hf he2 hd2
  | clean _ he hc ih => exact SegC.clean ih he hc
  | filt _ he hf ih => exact SegC.filt ih he hf

/-- THEOREM 6a. The flow (with calls) is the segment flow from the entry. -/
theorem flow_iff_segC {P : Program} {M : MethodId} {l0 l : Loc} {n : Node} :
    Flow P M l0 n l ↔ SegC P M (P.entry M) l0 n l :=
  ⟨segC_of_flow, flow_of_segC⟩

#print axioms flow_iff_segC

/-! ### The simulation of the converse -/

/-- `Q` simulates the converse of every instruction of `P`. -/
structure RevSim (P Q : Program) : Prop where
  entry : ∀ M, Q.entry M = P.exit M
  exit  : ∀ M, Q.exit M = P.entry M
  stmt  : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    ∃ s', (M, n', Instr.stmt s', n) ∈ Q.edges ∧ ∀ l l', s.step l l' → s'.step l' l
  call  : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∃ c', (M, n', Instr.call c', n) ∈ Q.edges ∧ c'.callee = c.callee ∧ c'.touched = c.touched ∧
      (∀ e, e ∈ c.toCallee → ∃ e', e' ∈ c'.fromCallee ∧
        ∀ l l', den e.1 e.2 l l' → den e'.1 e'.2 l' l) ∧
      (∀ e, e ∈ c.fromCallee → ∃ e', e' ∈ c'.toCallee ∧
        ∀ l l', den e.1 e.2 l l' → den e'.1 e'.2 l' l)
  /-- a cleaner is its own converse: `Q` has the same cleaner on the turned CFG edge -/
  clean : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → (M, n', Instr.clean cl, n) ∈ Q.edges
  /-- a type filter is its own converse: `Q` has the same filter on the turned CFG edge -/
  filt  : ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges →
    (M, n', Instr.filt b may, n) ∈ Q.edges

/-- A forward flow to `(n, l)` is a backward segment from `(n, l)` to the exit
    of `Q` (the forward entry). The callee flow inside a call step is reversed
    by its own induction hypothesis. -/
theorem backSeg_of_flow {P Q : Program} (hs : RevSim P Q) {M : MethodId} {l0 l : Loc} {n : Node}
    (h : Flow P M l0 n l) : SegC Q M n l (Q.exit M) l0 := by
  induction h with
  | start M l0 => rw [hs.exit M]; exact SegC.refl
  | step _ he hst ih =>
    obtain ⟨s', he', hs'⟩ := hs.stmt _ _ _ _ he
    exact SegC.trans (SegC.step SegC.refl he' (hs' _ _ hst)) ih
  | pass _ he hb ih =>
    obtain ⟨c', he', _, ht, _, _⟩ := hs.call _ _ _ _ he
    exact SegC.trans (SegC.pass SegC.refl he' (by rw [ht]; exact hb)) ih
  | clean _ he hc ih => exact SegC.trans (SegC.clean SegC.refl (hs.clean _ _ _ _ he) hc) ih
  | filt _ he hf ih => exact SegC.trans (SegC.filt SegC.refl (hs.filt _ _ _ _ _ he) hf) ih
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    obtain ⟨c', he', hcal, _, hto, hfrom⟩ := hs.call _ _ _ _ he
    obtain ⟨e1', he1', hd1'⟩ := hto e1 he1
    obtain ⟨e2', he2', hd2'⟩ := hfrom e2 he2
    -- the reversed callee flow: from the forward exit `l2` back to the forward entry `l1`
    have hseg : SegC Q c.callee (Q.entry c.callee) l2 (Q.exit c.callee) l1 := by
      rw [hs.entry c.callee]; exact ihc
    have hcf : Flow Q c'.callee l2 (Q.exit c'.callee) l1 := by
      rw [hcal]; exact flow_of_segC hseg
    exact SegC.trans (SegC.call SegC.refl he' he2' (hd2' _ _ hd2) hcf he1' (hd1' _ _ hd1)) ih

/-- Entry-to-exit flows of `P` give converse entry-to-exit flows of `Q`. -/
theorem flow_rev_sim {P Q : Program} (hs : RevSim P Q) {M : MethodId} {l0 l1 : Loc}
    (h : Flow P M l0 (P.exit M) l1) : Flow Q M l1 (Q.exit M) l0 := by
  have hseg := backSeg_of_flow hs h
  rw [← hs.entry M] at hseg
  exact flow_of_segC hseg

/-- Segments of `P` (with calls) give converse segments of `Q`. -/
theorem segC_rev_sim {P Q : Program} (hs : RevSim P Q) {M : MethodId} {n n' : Node} {l l' : Loc}
    (h : SegC P M n l n' l') : SegC Q M n' l' n l := by
  induction h with
  | refl => exact SegC.refl
  | step _ he hst ih =>
    obtain ⟨s', he', hs'⟩ := hs.stmt _ _ _ _ he
    exact SegC.trans (SegC.step SegC.refl he' (hs' _ _ hst)) ih
  | pass _ he hb ih =>
    obtain ⟨c', he', _, ht, _, _⟩ := hs.call _ _ _ _ he
    exact SegC.trans (SegC.pass SegC.refl he' (by rw [ht]; exact hb)) ih
  | @call n1 l1 c n2 e1 e2 la lb l2 _ he he1 hd1 hf he2 hd2 ih =>
    obtain ⟨c', he', hcal, _, hto, hfrom⟩ := hs.call _ _ _ _ he
    obtain ⟨e1', he1', hd1'⟩ := hto e1 he1
    obtain ⟨e2', he2', hd2'⟩ := hfrom e2 he2
    have hcf : Flow Q c'.callee lb (Q.exit c'.callee) la := by
      rw [hcal]; exact flow_rev_sim hs hf
    exact SegC.trans (SegC.call SegC.refl he' he2' (hd2' _ _ hd2) hcf he1' (hd1' _ _ hd1)) ih
  | clean _ he hc ih => exact SegC.trans (SegC.clean SegC.refl (hs.clean _ _ _ _ he) hc) ih
  | filt _ he hf ih => exact SegC.trans (SegC.filt SegC.refl (hs.filt _ _ _ _ _ he) hf) ih

/-! ### `Program.rev` simulates in both directions -/

theorem mem_rev_stmt {P : Program} {M : MethodId} {n n' : Node} {s : Stmt}
    (h : (M, n, Instr.stmt s, n') ∈ P.edges) :
    (M, n', Instr.stmt (Stmt.rev s), n) ∈ (Program.rev P).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_rev_call {P : Program} {M : MethodId} {n n' : Node} {c : Call}
    (h : (M, n, Instr.call c, n') ∈ P.edges) :
    (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_rev_clean {P : Program} {M : MethodId} {n n' : Node} {cl : Cleaner}
    (h : (M, n, Instr.clean cl, n') ∈ P.edges) :
    (M, n', Instr.clean cl, n) ∈ (Program.rev P).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_rev_filt {P : Program} {M : MethodId} {n n' : Node} {b : Base}
    {may : List Acc → Bool} (h : (M, n, Instr.filt b may, n') ∈ P.edges) :
    (M, n', Instr.filt b may, n) ∈ (Program.rev P).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

/-- Every edge of the reversed program comes from a turned edge of `P`. -/
theorem mem_rev_inv {P : Program} {M : MethodId} {n n' : Node} {ins' : Instr}
    (h : (M, n', ins', n) ∈ (Program.rev P).edges) :
    ∃ ins, (M, n, ins, n') ∈ P.edges ∧ ins' = revInstr ins := by
  obtain ⟨⟨M0, a, ins, b⟩, hm, he⟩ := List.mem_map.mp h
  injection he with h1 h2
  injection h2 with h3 h4
  injection h4 with h5 h6
  subst h1 h3 h6
  exact ⟨ins, hm, h5.symm⟩

theorem rev_stmt_inv {P : Program} {M : MethodId} {n n' : Node} {s' : Stmt}
    (h : (M, n', Instr.stmt s', n) ∈ (Program.rev P).edges) :
    ∃ s, (M, n, Instr.stmt s, n') ∈ P.edges ∧ s' = Stmt.rev s := by
  obtain ⟨ins, hm, he⟩ := mem_rev_inv h
  cases ins with
  | stmt s =>
    injection he with he'
    exact ⟨s, hm, he'⟩
  | call c => cases he
  | clean cl => cases he
  | filt b may => cases he

theorem rev_call_inv {P : Program} {M : MethodId} {n n' : Node} {c' : Call}
    (h : (M, n', Instr.call c', n) ∈ (Program.rev P).edges) :
    ∃ c, (M, n, Instr.call c, n') ∈ P.edges ∧ c' = Call.rev c := by
  obtain ⟨ins, hm, he⟩ := mem_rev_inv h
  cases ins with
  | stmt s => cases he
  | call c =>
    injection he with he'
    exact ⟨c, hm, he'⟩
  | clean cl => cases he
  | filt b may => cases he

theorem rev_clean_inv {P : Program} {M : MethodId} {n n' : Node} {cl : Cleaner}
    (h : (M, n', Instr.clean cl, n) ∈ (Program.rev P).edges) :
    (M, n, Instr.clean cl, n') ∈ P.edges := by
  obtain ⟨ins, hm, he⟩ := mem_rev_inv h
  cases ins with
  | stmt s => cases he
  | call c => cases he
  | clean cl0 =>
    injection he with he'
    subst he'
    exact hm
  | filt b may => cases he

theorem rev_filt_inv {P : Program} {M : MethodId} {n n' : Node} {b : Base}
    {may : List Acc → Bool} (h : (M, n', Instr.filt b may, n) ∈ (Program.rev P).edges) :
    (M, n, Instr.filt b may, n') ∈ P.edges := by
  obtain ⟨ins, hm, he⟩ := mem_rev_inv h
  cases ins with
  | stmt s => cases he
  | call c => cases he
  | clean cl => cases he
  | filt b0 may0 =>
    injection he with hb hmay
    subst hb hmay
    exact hm

/-- `Program.rev P` simulates the converse of `P` (soundness of the reversal). -/
theorem revSim_rev {P : Program} (hR : RevStmts P) (hC : RevCalls P) :
    RevSim P (Program.rev P) where
  entry := fun _ => rfl
  exit := fun _ => rfl
  stmt := fun M n s n' h =>
    ⟨Stmt.rev s, mem_rev_stmt h, fun _ _ hst => (Stmt.rev_step_iff (hR M n s n' h)).mp hst⟩
  call := fun M n c n' h =>
    ⟨Call.rev c, mem_rev_call h, rfl, rfl,
     fun e he => ⟨revEdge e.1 e.2, List.mem_map.mpr ⟨e, he, rfl⟩,
       fun _ _ hd => revEdge_sound ((hC M n c n' h).1 e he).2 hd⟩,
     fun e he => ⟨revEdge e.1 e.2, List.mem_map.mpr ⟨e, he, rfl⟩,
       fun _ _ hd => revEdge_sound ((hC M n c n' h).2 e he).2 hd⟩⟩
  clean := fun _ _ _ _ h => mem_rev_clean h
  filt := fun _ _ _ _ _ h => mem_rev_filt h

/-- `P` simulates the converse of `Program.rev P` (exactness of the reversal). -/
theorem revSim_back {P : Program} (hR : RevStmts P) (hC : RevCalls P) :
    RevSim (Program.rev P) P where
  entry := fun _ => rfl
  exit := fun _ => rfl
  stmt := by
    intro M n s' n' h
    obtain ⟨s, hm, rfl⟩ := rev_stmt_inv h
    exact ⟨s, hm, fun _ _ hst => (Stmt.rev_step_iff (hR _ _ _ _ hm)).mpr hst⟩
  call := by
    intro M n c' n' h
    obtain ⟨c, hm, rfl⟩ := rev_call_inv h
    refine ⟨c, hm, rfl, rfl, ?_, ?_⟩
    · -- a reversed `fromCallee` edge: its converse is the forward `fromCallee` edge
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have hb := (hC _ _ _ _ hm).2 e0 he0
      exact ⟨e0, he0, fun _ _ hd => (revEdge_exact hb.1 hb.2).mpr hd⟩
    · intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have hb := (hC _ _ _ _ hm).1 e0 he0
      exact ⟨e0, he0, fun _ _ hd => (revEdge_exact hb.1 hb.2).mpr hd⟩
  clean := fun _ _ _ _ h => rev_clean_inv h
  filt := fun _ _ _ _ _ h => rev_filt_inv h

/-- THEOREM 6b. Entry-to-exit flows WITH calls: the reversed program has
    exactly the converse flows. -/
theorem flow_rev_iff_calls {P : Program} (hR : RevStmts P) (hC : RevCalls P)
    {M : MethodId} {l0 l1 : Loc} :
    Flow P M l0 (P.exit M) l1 ↔ Flow (Program.rev P) M l1 ((Program.rev P).exit M) l0 :=
  ⟨flow_rev_sim (revSim_rev hR hC), flow_rev_sim (revSim_back hR hC)⟩

#print axioms flow_rev_iff_calls

/-- THEOREM 6c. Segments WITH calls: a segment of `P` is a reversed segment of
    `Program.rev P`, and back. -/
theorem segC_rev_iff {P : Program} (hR : RevStmts P) (hC : RevCalls P)
    {M : MethodId} {n n' : Node} {l l' : Loc} :
    SegC P M n l n' l' ↔ SegC (Program.rev P) M n' l' n l :=
  ⟨segC_rev_sim (revSim_rev hR hC), segC_rev_sim (revSim_back hR hC)⟩

#print axioms segC_rev_iff

/-- THEOREM 6d. A forward flow to `(n, l)` (with calls) is a backward segment
    from `(n, l)` to the exit of the reversed program, and back. -/
theorem flow_iff_backSegC {P : Program} (hR : RevStmts P) (hC : RevCalls P)
    {M : MethodId} {l0 l : Loc} {n : Node} :
    Flow P M l0 n l ↔ SegC (Program.rev P) M n l ((Program.rev P).exit M) l0 :=
  flow_iff_segC.trans (segC_rev_iff hR hC)

#print axioms flow_iff_backSegC

/-- The reversed program satisfies the reversal conditions again. -/
theorem rev_revStmts (P : Program) : RevStmts (Program.rev P) := by
  intro M n s' n' h
  obtain ⟨s, _, rfl⟩ := rev_stmt_inv h
  exact rev_revEdges s

theorem rev_revCalls (P : Program) : RevCalls (Program.rev P) := by
  intro M n c' n' h
  obtain ⟨c, _, rfl⟩ := rev_call_inv h
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨e0, _, rfl⟩ := List.mem_map.mp he
    exact ⟨revEdge_exactShape _ _, revEdge_markRev _ _⟩
  · obtain ⟨e0, _, rfl⟩ := List.mem_map.mp he
    exact ⟨revEdge_exactShape _ _, revEdge_markRev _ _⟩

#print axioms rev_revCalls

/-- Program reversal twice gives the same segment relation. -/
theorem segC_revrev_iff {P : Program} (hR : RevStmts P) (hC : RevCalls P)
    {M : MethodId} {n n' : Node} {l l' : Loc} :
    SegC P M n l n' l' ↔ SegC (Program.rev (Program.rev P)) M n l n' l' :=
  (segC_rev_iff hR hC).trans (segC_rev_iff (rev_revStmts P) (rev_revCalls P))

#print axioms segC_revrev_iff

/-! ### WF of the reversed program and backward soundness -/

theorem pmOf_star {i f : PFact} (hi : i.mark = .star) (hf : f.mark = .star) : pmOf i f = .star := by
  unfold pmOf; rw [hf]; exact hi

/-- The reversed program is WF when `P` is WF and the binding targets have the
    mark `*` (a reversed binding reads from the forward target). -/
theorem rev_WF {P : Program} (hW : P.WF) (hT : BindTargetsStar P) : (Program.rev P).WF where
  stmtTouched := by
    intro M n s n' h e he
    obtain ⟨s0, _, rfl⟩ := rev_stmt_inv h
    exact rev_touched s0 e he
  toStar := by
    intro M n c' n' h e he
    obtain ⟨c, hm, rfl⟩ := rev_call_inv h
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    show (revEdge e0.1 e0.2).1.mark = .star
    rw [revEdge_eq]
    exact pmOf_star (hW.fromStar _ _ _ _ hm e0 he0) ((hT _ _ _ _ hm).2 e0 he0)
  fromStar := by
    intro M n c' n' h e he
    obtain ⟨c, hm, rfl⟩ := rev_call_inv h
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    show (revEdge e0.1 e0.2).1.mark = .star
    rw [revEdge_eq]
    exact pmOf_star (hW.toStar _ _ _ _ hm e0 he0) ((hT _ _ _ _ hm).1 e0 he0)
  filtPrefix := by
    -- a reversed filter is the same filter of `P`
    intro M n b may n' h
    exact hW.filtPrefix _ _ _ _ _ (rev_filt_inv h)

#print axioms rev_WF

/-- The backward run: the closure `D` on `Program.rev P` (the SAME rules). -/
abbrev DBack (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Obj → Prop :=
  D (Program.rev P) counted L α sinks roots

/-- THEOREM 6e. Backward soundness from forward soundness, WITH calls. Let the
    forward soundness theorem have the form `fwd`, for example
    `Cov Q M l0 n l := ∀ i, D Q … (.init M i) → i.covers l0 →
       (∃ f, D Q … (.edge M i n f) ∧ den i f.fact l0 l) ∨ (∃ t, …)`.
    Then the same theorem for `Program.rev P` covers every converse segment of
    `P`: a forward segment from `(n, l)` to the exit location `l1` (it can
    contain full callee flows) is found by the backward run that starts at `l1`. -/
theorem backward_of_forward_calls (Cov : Program → MethodId → Loc → Node → Loc → Prop)
    (fwd : ∀ Q : Program, Q.WF → ∀ M l0 n l, Flow Q M l0 n l → Cov Q M l0 n l)
    {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hR : RevStmts P) (hC : RevCalls P) :
    ∀ M n l l1, SegC P M n l (P.exit M) l1 → Cov (Program.rev P) M l1 n l := by
  intro M n l l1 h
  exact fwd _ (rev_WF hW hT) M l1 n l (flow_of_segC ((segC_rev_iff hR hC).mp h))

#print axioms backward_of_forward_calls

/-- The entry-to-exit form: every forward flow `l0 ↦ l1` of `M` is a flow of
    the backward run from `l1` back to `l0`, and the forward theorem on
    `Program.rev P` covers it. -/
theorem backward_of_forward_calls_exit (Cov : Program → MethodId → Loc → Node → Loc → Prop)
    (fwd : ∀ Q : Program, Q.WF → ∀ M l0 n l, Flow Q M l0 n l → Cov Q M l0 n l)
    {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hR : RevStmts P) (hC : RevCalls P) :
    ∀ M l0 l1, Flow P M l0 (P.exit M) l1 → Cov (Program.rev P) M l1 (P.entry M) l0 :=
  fun M l0 l1 h => fwd _ (rev_WF hW hT) M l1 _ l0 ((flow_rev_iff_calls hR hC).mp h)

#print axioms backward_of_forward_calls_exit

/-! ## 7. Backward reuse of persisted forward records

Condition (the "closed method" condition of the spec): the forward run must
COVER the entry set `X`. That is, for every entry location `l0 ∈ X`, every
concrete flow of `M` from `l0` to the exit has a record in `S`. The forward
closure gives this for `X = ⋃ {i.covers | D (.init M i)}` (forward soundness).
A backward query that ends at an entry location outside `X` can need a flow
that no forward record holds: `backward_reuse_needs_cover`. -/

/-- THEOREM 7. Reversed forward records cover every converse flow from `X`. -/
theorem backward_reuse {P : Program} {M : MethodId} (S : List (PFact × PFact)) (X : Loc → Prop)
    (hcov : ∀ l0, X l0 → ∀ l1, Flow P M l0 (P.exit M) l1 → ∃ r, r ∈ S ∧ den r.1 r.2 l0 l1)
    (hS : ∀ r, r ∈ S → MarkRev r.1 r.2) :
    ∀ l0, X l0 → ∀ l1, Flow P M l0 (P.exit M) l1 →
      ∃ r, r ∈ S ∧ den (revEdge r.1 r.2).1 (revEdge r.1 r.2).2 l1 l0 := by
  intro l0 hx l1 hf
  obtain ⟨r, hr, hd⟩ := hcov l0 hx l1 hf
  exact ⟨r, hr, revEdge_sound (hS r hr) hd⟩

#print axioms backward_reuse

/-- With calls: the reversed records cover every flow of the BACKWARD program
    from the exit location `l1` to a covered entry location `l0 ∈ X`. -/
theorem backward_reuse_rev {P : Program} {M : MethodId} (hR : RevStmts P) (hC : RevCalls P)
    (S : List (PFact × PFact)) (X : Loc → Prop)
    (hcov : ∀ l0, X l0 → ∀ l1, Flow P M l0 (P.exit M) l1 → ∃ r, r ∈ S ∧ den r.1 r.2 l0 l1)
    (hS : ∀ r, r ∈ S → MarkRev r.1 r.2) :
    ∀ l1 l0, X l0 → Flow (Program.rev P) M l1 ((Program.rev P).exit M) l0 →
      ∃ r, r ∈ S ∧ den (revEdge r.1 r.2).1 (revEdge r.1 r.2).2 l1 l0 :=
  fun l1 l0 hx hb => backward_reuse S X hcov hS l0 hx l1 ((flow_rev_iff_calls hR hC).mpr hb)

#print axioms backward_reuse_rev

/-- Precision of the reuse: if every pair of a record is a real flow (a complete
    record, `ApSpec.Exact`), and the record has an empty premise exclusion and is
    mark-reversible, then every pair of the reversed record is a real flow of the
    backward program. -/
theorem backward_reuse_precise {P : Program} {M : MethodId} (hR : RevStmts P) (hC : RevCalls P)
    {i f : PFact} (he : PremEmpty i.kind) (hm : MarkRev i f)
    (hex : ∀ l0 l1, den i f l0 l1 → Flow P M l0 (P.exit M) l1) :
    ∀ l1 l0, den (revEdge i f).1 (revEdge i f).2 l1 l0 →
      Flow (Program.rev P) M l1 ((Program.rev P).exit M) l0 :=
  fun l1 l0 hd => (flow_rev_iff_calls hR hC).mp (hex l0 l1 ((rev_exact_of_empty_premise he hm).mpr hd))

#print axioms backward_reuse_precise

/-! ### Counterexample D: the cover condition is necessary

`P0` has one method with no instructions (entry = exit). The forward run
analysed only base 10, so `S0 = [10.* → 10.*]` and `X = base 10`. A backward
query on base 11 has the real flow `11 ↦ 11`, and no reversed record covers it. -/

def P0 : Program := { entry := fun _ => 0, exit := fun _ => 0, edges := [] }
def S0 : List (PFact × PFact) := [idEdge 10]

theorem P0_flow {M : MethodId} {l0 l : Loc} {n : Node} (h : Flow P0 M l0 n l) : l = l0 := by
  induction h with
  | start => rfl
  | step _ he _ _ => cases he
  | pass _ he _ _ => cases he
  | call _ he _ _ _ _ _ _ _ => cases he
  | clean _ he _ _ => cases he
  | filt _ he _ _ => cases he

theorem backward_reuse_needs_cover :
    (∀ l0 : Loc, l0.base = 10 → ∀ l1, Flow P0 0 l0 (P0.exit 0) l1 →
        ∃ r, r ∈ S0 ∧ den r.1 r.2 l0 l1) ∧
    ¬ (∀ l0 l1 : Loc, Flow P0 0 l0 (P0.exit 0) l1 →
        ∃ r, r ∈ S0 ∧ den (revEdge r.1 r.2).1 (revEdge r.1 r.2).2 l1 l0) := by
  refine ⟨fun l0 hx l1 hf => ?_, fun H => ?_⟩
  · have e := P0_flow hf
    subst e
    exact ⟨idEdge 10, List.Mem.head _, den_idEdge.mpr ⟨hx, rfl⟩⟩
  · obtain ⟨r, hr, hd⟩ := H ⟨11, [], 0⟩ ⟨11, [], 0⟩ (Flow.start 0 _)
    have e := List.mem_singleton.mp hr
    subst e
    obtain ⟨h1, _⟩ := hd
    exact absurd h1 (by decide)

#print axioms backward_reuse_needs_cover

/-! ## 8. `revEdge` on the cases of `ApSpec/Cases.lean`

The definitions below copy the vectors of `ApSpec.Cases` (this file imports
`ApSpec.Basic` only). -/

namespace Vec

def fA : Acc := 1
def gA : Acc := 2
def hA : Acc := 3
def x : Base := 10
def a : Base := 11
def b : Base := 12
def r0 : Base := 20
def T : Mark := 5
def E1 : Excl := .set [hA]

def pf (base : Base) (path : List Acc) (k : Kind) (m : MarkA) : PFact := ⟨base, path, k, m⟩

/-- `a = b.f` (as in `Cases.loadF`). -/
def loadF : Stmt :=
  { touched := [a, b]
    edges := [ (pf b [] (.star (.set [fA])) .star, pf b [] (.star Excl.empty) .star),
               (pf b [fA] (.star Excl.empty) .star, pf b [fA] (.star Excl.empty) .star),
               (pf b [fA] (.star Excl.empty) .star, pf a [] (.star Excl.empty) .star) ] }

/-- `a.f = b` (as in `Cases.storeF`). -/
def storeF : Stmt :=
  { touched := [a, b]
    edges := [ (pf a [] (.star (.set [fA])) .star, pf a [] (.star Excl.empty) .star),
               (pf b [] (.star Excl.empty) .star, pf b [] (.star Excl.empty) .star),
               (pf b [] (.star Excl.empty) .star, pf a [fA] (.star Excl.empty) .star) ] }

-- `a = b.f` reversed: `a.* → b.f.*` reads `a` and writes `b.f`; the premise
-- exclusion `{f}` of the first micro edge moves to the new conclusion.
#eval loadF.edges.map (fun e => revEdge e.1 e.2)
#eval (Stmt.rev loadF).touched        -- [11, 12, 12, 12, 11]: every target is touched
#eval (Stmt.rev loadF).edges.length   -- 3: no identity edge (every target is touched)

example : revEdge (pf b [] (.star (.set [fA])) .star) (pf b [] (.star Excl.empty) .star)
    = (pf b [] (.star Excl.empty) .star, pf b [] (.star (.set [fA])) .star) := by decide
example : revEdge (pf b [fA] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) .star)
    = (pf a [] (.star Excl.empty) .star, pf b [fA] (.star Excl.empty) .star) := by decide
example : RevEdges loadF := by
  intro e he
  simp only [loadF, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl <;> exact ⟨True.intro, Or.inl (Or.inl rfl)⟩

-- `a.f = b` reversed: `a.f.* → b.*` and `a.* → a.*{f}`.
#eval storeF.edges.map (fun e => revEdge e.1 e.2)
example : revEdge (pf b [] (.star Excl.empty) .star) (pf a [fA] (.star Excl.empty) .star)
    = (pf a [fA] (.star Excl.empty) .star, pf b [] (.star Excl.empty) .star) := by decide

-- A weak update `b ⊇ a` (target 12 is not touched) gets the identity edge on 12.
#eval (Stmt.rev sWeak).touched                          -- [11, 12]
#eval (Stmt.rev sWeak).edges                            -- reversed edge + idEdge 12

-- Summary `(x,.f,*,{},*) → (r,.,*,{},*)` reversed: `(r,.,*,{},*) → (x,.f,*,{},*)`.
example : revEdge (pf x [fA] (.star Excl.empty) .star) (pf r0 [] (.star Excl.empty) .star)
    = (pf r0 [] (.star Excl.empty) .star, pf x [fA] (.star Excl.empty) .star) := by decide

-- The source `x = source()`: `0 → (x,.,$,{},T)` reversed: `(x,.,$,{},T) → (0,.,$,{},0)`.
#eval revEdge zeroFact (pf x [] .exact (.conc T))
example : MarkRev zeroFact (pf x [] .exact (.conc T)) := Or.inr ⟨zeroMark, rfl⟩

-- The answered request `(x,.f,$,{},T) → (r,.,$,{},T)` reversed: `(r,.,$,T) → (x,.f,$,T)`.
example : revEdge (pf x [fA] .exact (.conc T)) (pf r0 [] .exact (.conc T))
    = (pf r0 [] .exact (.conc T), pf x [fA] .exact (.conc T)) := by decide

-- `a.f = b`, case 3, as a record from the emitted premise `(a,.,*,{},*)`:
-- `(a,.,*,{},*) → (a,.,*,{f},*)` reverses to `(a,.,*,{},*) → (a,.,*,{f},*)`.
example : revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star (.set [fA])) .star)
    = (pf a [] (.star Excl.empty) .star, pf a [] (.star (.set [fA])) .star) := by decide

-- `a = b.f`, case 2 (a demand record): `(x,.,*,E,*) → (a,.,[any],{},*)` reverses
-- to `[any] → [any]`: sound. With the emitted premise `(x,.,*,{},*)` the same
-- shape is exact (THEOREM 2'); with `E = {h}` it is not.
#eval revEdge (pf x [] (.star E1) .star) (pf a [] .any .star)
example : ExactShape (pf x [] (.star Excl.empty) .star).kind (pf a [] .any .star).kind := rfl

-- The reversed premise of a `* → *` record serves every fact below its chain.
example : applicable (revEdge (pf x [] (.star Excl.empty) .star) (pf b [] (.star (.set [fA])) .star)).1
    (pf b [gA] (.star Excl.empty) .star) = true := by decide
example : applicable (revEdge (pf x [] (.star Excl.empty) .star) (pf b [] (.star (.set [fA])) .star)).1
    (pf b [] (.star Excl.empty) .star) = true := by decide

/-- `r = foo(a)`: the caller binds `a.* → arg0.*` into the callee and
    `return.* → r.*` back (bases: a = 11, arg0 = 30, return = 31, r = 20). -/
def callFoo : Call :=
  { callee := 7, touched := [r0]
    toCallee := [(pf a [] (.star Excl.empty) .star, pf 30 [] (.star Excl.empty) .star)]
    fromCallee := [(pf 31 [] (.star Excl.empty) .star, pf r0 [] (.star Excl.empty) .star)] }

-- Reversed: `toCallee = [r.* → return.*]` (caller post-location → callee exit),
-- `fromCallee = [arg0.* → a.*]` (callee entry → caller pre-location).
#eval (Call.rev callFoo).toCallee
#eval (Call.rev callFoo).fromCallee
example : (Call.rev callFoo).toCallee
    = [(pf r0 [] (.star Excl.empty) .star, pf 31 [] (.star (Excl.empty.union Excl.empty)) .star)] := by
  decide

/-! ### Version 5: cleaner records and the reversed cleaner -/

-- A cleaner of the mark `T` on `a.*` gives the record `(a,.,*,{},*) → (a,.,*,{},*∖{T})`.
-- Its reversal is the same record: the mark relation is a partial identity.
example : revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T]))
    = (pf a [] (.star Excl.empty) .star, pf a [] (.star Excl.empty) (.starEx [T])) := by decide

-- It reverses exactly (THEOREM 2a'), for every pair of locations.
example {l0 l1 : Loc} :
    den (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T])) l0 l1 ↔
    den (revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T]))).1
      (revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T]))).2
      l1 l0 :=
  rev_starEx_exact rfl rfl

-- The reversed record stops the cleaned mark `T` (the `passes` conjunct), as the forward one.
example : ¬ den (revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T]))).1
    (revEdge (pf a [] (.star Excl.empty) .star) (pf a [] (.star Excl.empty) (.starEx [T]))).2
    ⟨a, [], T⟩ ⟨a, [], T⟩ := by
  rintro ⟨_, _, _, _, h, _⟩
  have h' : memB T [T] = false := h
  exact absurd h' (by decide)

-- A concrete premise mark with a `*∖x` conclusion: the new premise gets the concrete mark.
example : revEdge (pf x [fA] .exact (.conc T)) (pf r0 [] .exact (.starEx [6]))
    = (pf r0 [] .exact (.conc T), pf x [fA] .exact (.starEx [6])) := by decide

-- A cleaner and a type filter of a program stay as they are; only the CFG edge turns round.
def clA : Cleaner := ⟨a, [], .atAndBelow, some T⟩
def mayA : List Acc → Bool := fun p => p.length ≤ 1
def Pcf : Program :=
  { entry := fun _ => 0, exit := fun _ => 2,
    edges := [(0, 0, .clean clA, 1), (0, 1, .filt a mayA, 2)] }

example : (Program.rev Pcf).edges = [(0, 1, .clean clA, 0), (0, 2, .filt a mayA, 1)] := rfl

end Vec

end ApSpec.Reverse
