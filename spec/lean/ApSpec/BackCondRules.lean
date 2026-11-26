/-
  ApSpec.BackCondRules — the rule-level reference semantics of rule B1: the layer of a backward
  SEED and of a REVERSED SOURCE LITERAL (spec interpreter.md §4.1, §4.2, §4.9 RULE ROLES;
  ap.md §9.2).

  A backward fact is a REQUIREMENT: taint at a covered location reaches a sink. A requirement in
  the normal layer is a MUST: EVERY covered location is sufficient by itself. A requirement in the
  demand layer is a MAY: it covers every location that can take part, but a covered location need
  not be sufficient. Rule B1: the seed of a sink literal, and the reversal of a conditional source
  literal, of an alternative with exactly ONE positive literal is a MUST, also with the `[any]`
  tail (`ContainsMarkOnAnyField`). The literals of an alternative with two or more positive
  literals (a conjunctive sink, an ND source) and the reversal of a pass rule with an `AnyField`
  target stay MAY. This module justifies the MUST case and shows by executable counterexamples
  that the MAY cases cannot be MUST.

  The model.
    * `covB p l`: the Boolean coverage test, `covB_iff : covB p l = true ↔ p.covers l` for EVERY
      `PFact` (every tail kind and mark), so the results below need no shape hypothesis on the
      literal; the spec literals are the `$` and `[any]` patterns with a concrete mark.
    * `State := List Loc`: the tainted locations. `holds st p`: some location of `st` is covered.
    * `Cond := List (List PFact)`: the condition in DNF, alternatives of positive literals;
      `fires c st`: some alternative has all its literals held. `fires_mono`: monotone in `st`.
    * `Suff c l`: the location `l` alone is sufficient, `∀ st, l ∈ st → fires c st`.
      `suff_iff : Suff c l ↔ fires c [l] = true`, so `Suff` is decidable.
    * A statement with a source rule: `post c targets st = if fires c st then st ++ targets else
      st` (the source never kills). `targets` lists the locations that the action taints: the
      `$` target is one location, the `[any-taint]` target (a MUST, I14) any finite list of
      locations under `P`. `ReqSuff D t`: the location `t` alone is sufficient for the
      downstream property `D` (the requirement on the target).
    * A pass rule with an `AnyField` target in its real semantics: the program writes the taint
      of each location under `P` to ONE location under `Q`, chosen by `choose`:
      `postPass P choose st = st ++ (st.filter (covB P)).map choose`. The model edge
      `(P.$, Q.[any])` (`den`) relates the source to EVERY location under `Q`.
    * `litReqs` / `reqs`: the B1 requirements of the positive literals of an alternative / of a
      condition, as `AFact`s: a single literal gives its pattern in the normal layer, two or more
      give one demand-layer pattern per literal, none gives none (the zero demand covers it).

  Main results.
    * `unary_seed_must` (1): a literal that is a whole alternative is MUST: every covered location
      is sufficient.
    * `unary_cond_exact` (2): if every alternative is a single literal, the union of the seeds is
      EXACTLY the sufficient set.
    * `nd_suff_iff`, `nd_seed_not_must_of_base`, `nd_seed_not_must` (3): for a two-literal
      alternative on different bases a location covered by one literal is not sufficient
      (executable counterexample).
    * `seed_may_cover` (4), `core_spec`: the per-literal seeds are a sound MAY cover. Every
      location of a minimal firing state is covered by a literal of a firing alternative; every
      firing state has a firing sub-state (`core`, computed) of literal-covered locations.
    * `rev_unary_source_must` (5): the reversed single literal of a source is MUST, for every
      literal tail and every target list; `rev_unary_source_must_exact` (the `$` target).
      `rev_source_may_cover`: the reversed literals of any source are a sound MAY cover.
    * `rev_nd_source_not_must_gen`, `rev_nd_source_not_must` (6): the reversed literal of an ND
      source is not MUST (witness state `[q]`).
    * `rev_pass_any_not_must_gen`, `rev_pass_any_not_must` (7): the reversal of a pass rule with
      an `AnyField` target is not MUST, also its `$` result; `rev_pass_may_sound`: it is a sound
      MAY cover.
    * The AP form (8): `reqs_normal_must`, `reqs_normal_rev_must` (every NORMAL B1 requirement is
      MUST, for the seed and for the reversed source), `reqs_may_cover` (all B1 requirements
      together are a sound MAY cover), `reqs_unary_exact` (all-unary condition: the normal seeds
      cover EXACTLY the sufficient set), `reqs_nd_demand`, `any_seed_exact` (the seed of
      `ContainsMarkOnAnyField(P,T)` is `P.[any](T)` in the normal layer and covers exactly the
      sufficient locations).
    * Precision note: `nd_overlap_suff`: B1 is a sound under-approximation of MUST, not the exact
      MUST set: a two-literal alternative can have a sufficient location (both literals cover it);
      B1 seeds it as MAY.
    * `empty_alt_suff`, `suff_covered`: an alternative with no positive literal makes every
      location sufficient (TRUE: no seed, the zero demand covers it); otherwise a sufficient
      location is covered by a literal.
    * `firesS_proj`, `signed_not_must`: the negated-literal projection (below).

  Hypotheses. None beyond the statements: the minimal state in (4) is given by
  `fires c (st.erase l) = false`; (5) needs `t ∈ targets` and `ReqSuff D t` (the requirement on
  the target is itself MUST: a MAY requirement on the target gives a MAY result, the ordinary
  layer OR). `suff_covered` needs `fires c [] = false`: a condition that is true without taint
  (an alternative with no positive literal) needs no requirement, the zero demand covers it.

  Differences between the model and production.
    * DNF against the NNF DAG: production keeps one positive NNF DAG per bound occurrence and
      never expands it to cubes (interpreter.md §4.2). Its truth function on locations is a
      monotone Boolean function; `Cond` is its DNF. "An alternative with one positive literal" is
      a DNF cube of size one: a leaf with an AND-free path to the root gives one. The converse
      needs absorption (`(A ∨ B) ∧ (A ∨ C)` has the cube `[A, A]`), which production does not
      do; B1 then gives MAY, which is sound (MAY is always sound, `reqs_may_cover`; see the
      precision note). The model does not model the DAG walk that finds the leaves.
    * Negated literals: production projects residual negated mark literals to true before it
      evaluates the condition, as the forward run does. `Cond` is the condition AFTER this
      projection (`proj`, `firesS_proj`). B1's MUST is relative to the projected condition, the
      condition that the forward run reports with. Against the signed condition, a single positive
      literal next to a negated one is NOT sufficient (`signed_not_must`): the MUST claim does not
      hold for the unprojected semantics, which is also not monotone.
    * Finite targets: the `[any-taint]` target taints every location under `P` (unboundedly
      many); the model takes any finite list. The theorems hold for every list that contains the
      requirement location.
    * The module is rule-level: it does not model the propagation of a normal `[any]`
      requirement through later reversed edges, the field limit, the cleaners, the mark modes of
      the backward run (F72) or the end-fact trigger.

  All proofs are constructive (`propext`, `Quot.sound` only; audit with `#print axioms`).
-/
import ApSpec.Basic

namespace ApSpec.BackCond
open ApSpec

/-! ## 1. Coverage as a Boolean test -/

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem dropPrefix_iff : ∀ {p q r : List Acc}, dropPrefix p q = some r ↔ q = p ++ r
  | [], q, r => by
    show some q = some r ↔ q = r
    exact ⟨Option.some.inj, fun h => h ▸ rfl⟩
  | a :: p, [], r => by
    show (none : Option (List Acc)) = some r ↔ [] = a :: (p ++ r)
    exact ⟨(fun h => nomatch h), (fun h => (List.cons_ne_nil a (p ++ r) h.symm).elim)⟩
  | a :: p, b :: q, r => by
    show (if Nat.beq a b = true then dropPrefix p q else none) = some r ↔ b :: q = a :: (p ++ r)
    cases hab : Nat.beq a b with
    | true =>
      rw [if_pos rfl, dropPrefix_iff, beq_iff.mp hab]
      exact ⟨fun h => h ▸ rfl, fun h => List.cons.inj h |>.2⟩
    | false =>
      rw [if_neg Bool.false_ne_true]
      refine ⟨(fun h => nomatch h), (fun h => ?_)⟩
      have hba : b = a := (List.cons.inj h).1
      rw [hba, Nat.beq_refl] at hab
      exact Bool.noConfusion hab

theorem admitsTailB_iff {k : Kind} {r : List Acc} : admitsTailB k r = true ↔ tailI k r := by
  cases k with
  | star e => exact Iff.rfl
  | any => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | exact =>
    cases r with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons a r => exact ⟨fun h => Bool.noConfusion h, fun h => (List.cons_ne_nil a r h).elim⟩

/-- The Boolean form of `MarkA.admits`. -/
def markAdmB : MarkA → Mark → Bool
  | .star,     _ => true
  | .conc t,   m => Nat.beq m t
  | .starEx x, m => !memB m x

theorem markAdmB_iff {a : MarkA} {m : Mark} : markAdmB a m = true ↔ a.admits m := by
  cases a with
  | star => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | conc t => exact beq_iff
  | starEx x =>
    show (!memB m x) = true ↔ memB m x = false
    cases memB m x <;> decide

/-- The Boolean coverage test of a literal (a premise pattern) on a location. -/
def covB (p : PFact) (l : Loc) : Bool :=
  Nat.beq l.base p.base && markAdmB p.mark l.mark &&
    (match dropPrefix p.path l.path with
     | some σ => admitsTailB p.kind σ
     | none   => false)

/-- `covB` decides `PFact.covers`, for every tail kind and every mark. -/
theorem covB_iff {p : PFact} {l : Loc} : covB p l = true ↔ p.covers l := by
  unfold covB PFact.covers
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff, markAdmB_iff]
  constructor
  · rintro ⟨⟨hb, hm⟩, hp⟩
    refine ⟨hb, ?_, hm⟩
    cases hd : dropPrefix p.path l.path with
    | none => rw [hd] at hp; exact Bool.noConfusion hp
    | some σ =>
      rw [hd] at hp
      exact ⟨σ, dropPrefix_iff.mp hd, admitsTailB_iff.mp hp⟩
  · rintro ⟨hb, ⟨σ, hσ, ht⟩, hm⟩
    refine ⟨⟨hb, hm⟩, ?_⟩
    rw [dropPrefix_iff.mpr hσ]
    exact admitsTailB_iff.mpr ht
#print axioms covB_iff

instance (p : PFact) : DecidablePred p.covers :=
  fun _ => decidable_of_iff _ covB_iff

/-! ## 2. States and conditions -/

/-- The tainted locations. -/
abbrev State := List Loc

/-- The positive literal `p` holds in `st`: some tainted location is covered. -/
def holds (st : State) (p : PFact) : Bool := st.any (covB p)

/-- The reference condition after the projection of negated literals to true: alternatives
    (DNF cubes) of positive literals. -/
abbrev Cond := List (List PFact)

def fires (c : Cond) (st : State) : Bool := c.any (fun alt => alt.all (holds st))

theorem holds_iff {st : State} {p : PFact} : holds st p = true ↔ ∃ l ∈ st, p.covers l := by
  unfold holds
  rw [List.any_eq_true]
  exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, covB_iff.mp h⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, covB_iff.mpr h⟩⟩

theorem fires_iff {c : Cond} {st : State} :
    fires c st = true ↔ ∃ alt ∈ c, ∀ p ∈ alt, holds st p = true := by
  unfold fires
  rw [List.any_eq_true]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, List.all_eq_true.mp h⟩,
    fun ⟨a, ha, h⟩ => ⟨a, ha, List.all_eq_true.mpr h⟩⟩

theorem holds_mono {st st' : State} {p : PFact} (h : ∀ l, l ∈ st → l ∈ st') :
    holds st p = true → holds st' p = true := by
  intro hp
  obtain ⟨l, hl, hc⟩ := holds_iff.mp hp
  exact holds_iff.mpr ⟨l, h l hl, hc⟩

/-- The condition is monotone in the tainted locations. -/
theorem fires_mono {c : Cond} {st st' : State} (h : ∀ l, l ∈ st → l ∈ st') :
    fires c st = true → fires c st' = true := by
  intro hf
  obtain ⟨alt, ha, hall⟩ := fires_iff.mp hf
  exact fires_iff.mpr ⟨alt, ha, fun p hp => holds_mono h (hall p hp)⟩
#print axioms fires_mono

/-! ## 3. Sufficiency of one location -/

/-- The location `l` alone is sufficient: every state that contains it fires the condition. -/
def Suff (c : Cond) (l : Loc) : Prop := ∀ st : State, l ∈ st → fires c st = true

theorem suff_iff {c : Cond} {l : Loc} : Suff c l ↔ fires c [l] = true := by
  constructor
  · intro h; exact h [l] (List.mem_singleton.mpr rfl)
  · intro h st hl
    exact fires_mono (fun x hx => by rw [List.mem_singleton] at hx; exact hx ▸ hl) h
#print axioms suff_iff

instance (c : Cond) : DecidablePred (Suff c) :=
  fun _ => decidable_of_iff _ suff_iff.symm

/-- (1) A literal that is a whole alternative is a MUST: every location it covers is
    sufficient. No hypothesis on its tail or mark (`$`, `[any]` and the others). -/
theorem unary_seed_must {c : Cond} {lit : PFact} {l : Loc}
    (hc : [lit] ∈ c) (hl : lit.covers l) : Suff c l := by
  rw [suff_iff, fires_iff]
  refine ⟨[lit], hc, fun p hp => ?_⟩
  rw [List.mem_singleton] at hp
  subst hp
  exact holds_iff.mpr ⟨l, List.mem_singleton.mpr rfl, hl⟩
#print axioms unary_seed_must

/-- (2) If every alternative is a single literal, the union of the seeds is EXACTLY the set of
    sufficient locations. -/
theorem unary_cond_exact {c : Cond} {lits : List PFact} {l : Loc}
    (hc : c = lits.map (fun p => [p])) : Suff c l ↔ ∃ p ∈ lits, p.covers l := by
  subst hc
  constructor
  · intro h
    obtain ⟨alt, halt, hall⟩ := fires_iff.mp (suff_iff.mp h)
    rw [List.mem_map] at halt
    obtain ⟨p, hp, rfl⟩ := halt
    obtain ⟨l', hl', hcov⟩ := holds_iff.mp (hall p (List.mem_singleton.mpr rfl))
    rw [List.mem_singleton] at hl'
    subst hl'
    exact ⟨p, hp, hcov⟩
  · rintro ⟨p, hp, hcov⟩
    exact unary_seed_must (List.mem_map.mpr ⟨p, hp, rfl⟩) hcov
#print axioms unary_cond_exact

/-- A condition that is false without taint: a sufficient location is covered by a literal.
    (A condition true without taint, an alternative with no positive literal, makes every
    location sufficient; it needs no requirement: the zero demand covers it.) -/
theorem empty_alt_suff {c : Cond} (h : [] ∈ c) (l : Loc) : Suff c l :=
  fun _ _ => fires_iff.mpr ⟨[], h, fun _ hp => nomatch hp⟩
#print axioms empty_alt_suff

/-! ## 4. Two positive literals: not a MUST -/

/-- A two-literal alternative: one location is sufficient iff it is covered by both. -/
theorem nd_suff_iff {a b : PFact} {l : Loc} : Suff [[a, b]] l ↔ a.covers l ∧ b.covers l := by
  rw [suff_iff, ← covB_iff, ← covB_iff]
  show ((covB a l || false) && ((covB b l || false) && true) || false) = true ↔ _
  cases covB a l <;> cases covB b l <;> decide
#print axioms nd_suff_iff

/-- (3) Literals on different bases: a location covered by one literal is not sufficient. -/
theorem nd_seed_not_must_of_base {a b : PFact} {l : Loc} (hab : a.base ≠ b.base)
    (ha : a.covers l) : ¬ Suff [[a, b]] l := by
  intro h
  have hb := (nd_suff_iff.mp h).2
  exact hab (ha.1.symm.trans hb.1)
#print axioms nd_seed_not_must_of_base

/-- The executable counterexample: `x.[any](7) ∧ y.$(7)`; the location `x.f` with the mark 7 is
    covered by the first literal, but alone it does not fire the condition. -/
def ndA : PFact := ⟨1, [], .any, .conc 7⟩
def ndB : PFact := ⟨2, [], .exact, .conc 7⟩
def ndL : Loc := ⟨1, [3], 7⟩

theorem nd_seed_not_must : ndA.covers ndL ∧ ¬ Suff [[ndA, ndB]] ndL := by decide
#print axioms nd_seed_not_must

/-- Precision note: B1 is a sound under-approximation of MUST, not the exact MUST set. The two
    literals `x.[any](7)` and `x.f.$(7)` share the location `x.f`, which alone fires the
    two-literal alternative; B1 seeds it as MAY. -/
def ovA : PFact := ⟨1, [], .any, .conc 7⟩
def ovB : PFact := ⟨1, [3], .exact, .conc 7⟩

theorem nd_overlap_suff : Suff [[ovA, ovB]] ndL := by decide
#print axioms nd_overlap_suff

/-! ## 5. The per-literal seeds are a sound MAY cover -/

/-- Constructive replacement of `List.all_eq_false` (which uses `Classical.choice`). -/
theorem all_false_exists {α : Type} {f : α → Bool} :
    ∀ {l : List α}, l.all f = false → ∃ x ∈ l, f x = false
  | [], h => Bool.noConfusion h
  | x :: xs, h => by
    cases hx : f x with
    | false => exact ⟨x, List.mem_cons_self, hx⟩
    | true =>
      have h1 : (f x && xs.all f) = false := h
      rw [hx, Bool.true_and] at h1
      obtain ⟨y, hy, hfy⟩ := all_false_exists h1
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- Constructive replacement of `List.mem_erase_of_ne` (which uses `Classical.choice`). -/
theorem mem_erase_of_ne' {a b : Loc} : ∀ {l : List Loc}, a ∈ l → a ≠ b → a ∈ l.erase b
  | [], h, _ => nomatch h
  | x :: xs, h, hne => by
    match decEq x b with
    | isTrue hxb =>
      subst hxb
      rw [List.erase_cons_head]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h' hne
      · exact h'
    | isFalse hxb =>
      have hb : ¬ (x == b) = true := fun h' => hxb (of_decide_eq_true h')
      rw [List.erase_cons_tail hb]
      rcases List.mem_cons.mp h with h' | h'
      · exact h' ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_erase_of_ne' h' hne)

/-- (4) A location of a minimal firing state is covered by a literal of a firing alternative. -/
theorem seed_may_cover {c : Cond} {st : State} {l : Loc}
    (hf : fires c st = true) (_hl : l ∈ st) (hmin : fires c (st.erase l) = false) :
    ∃ alt ∈ c, alt.all (holds st) = true ∧ ∃ p ∈ alt, p.covers l := by
  obtain ⟨alt, halt, hall⟩ := fires_iff.mp hf
  refine ⟨alt, halt, List.all_eq_true.mpr hall, ?_⟩
  have hne : alt.all (holds (st.erase l)) = false := by
    cases h : alt.all (holds (st.erase l)) with
    | false => rfl
    | true =>
      have h' : fires c (st.erase l) = true := List.any_eq_true.mpr ⟨alt, halt, h⟩
      rw [hmin] at h'
      exact Bool.noConfusion h'
  obtain ⟨p, hp, hnp⟩ := all_false_exists hne
  obtain ⟨l', hl', hcov⟩ := holds_iff.mp (hall p hp)
  refine ⟨p, hp, ?_⟩
  match decEq l' l with
  | isTrue he => exact he ▸ hcov
  | isFalse hne' =>
    have h1 := holds_iff.mpr ⟨l', mem_erase_of_ne' hl' hne', hcov⟩
    rw [hnp] at h1
    exact Bool.noConfusion h1
#print axioms seed_may_cover

/-- A sufficient location of a condition that is false without taint is covered by a literal. -/
theorem suff_covered {c : Cond} {l : Loc} (h0 : fires c [] = false) (h : Suff c l) :
    ∃ alt ∈ c, ∃ p ∈ alt, p.covers l := by
  have hmin : fires c ([l].erase l) = false := by
    rw [List.erase_cons_head]; exact h0
  obtain ⟨alt, halt, _, p, hp, hc⟩ := seed_may_cover (suff_iff.mp h) (List.mem_singleton.mpr rfl) hmin
  exact ⟨alt, halt, p, hp, hc⟩
#print axioms suff_covered

/-- The first location of `st` that the literal covers. -/
def pick (st : State) (p : PFact) : Option Loc := st.find? (covB p)

/-- One witness location per literal of the alternative. -/
def wit (st : State) (alt : List PFact) : State := alt.filterMap (pick st)

/-- The firing core: the witnesses of the first firing alternative. -/
def core (c : Cond) (st : State) : State :=
  match c.find? (fun alt => alt.all (holds st)) with
  | some alt => wit st alt
  | none     => []

theorem pick_some {st : State} {p : PFact} {l : Loc} (h : pick st p = some l) :
    l ∈ st ∧ p.covers l :=
  ⟨List.mem_of_find?_eq_some h, covB_iff.mp (List.find?_some h)⟩

theorem pick_of_holds {st : State} {p : PFact} (h : holds st p = true) :
    ∃ l, pick st p = some l := by
  cases hp : pick st p with
  | some l => exact ⟨l, rfl⟩
  | none =>
    obtain ⟨l, hl, hc⟩ := holds_iff.mp h
    have := List.find?_eq_none.mp hp l hl
    exact absurd (covB_iff.mpr hc) this

theorem wit_spec {st : State} {alt : List PFact} (hall : ∀ p ∈ alt, holds st p = true) :
    (∀ l ∈ wit st alt, l ∈ st ∧ ∃ p ∈ alt, p.covers l) ∧
    (∀ p ∈ alt, holds (wit st alt) p = true) ∧ (wit st alt).length ≤ alt.length := by
  refine ⟨fun l hl => ?_, fun p hp => ?_, List.length_filterMap_le _ _⟩
  · obtain ⟨p, hp, hpk⟩ := List.mem_filterMap.mp hl
    exact ⟨(pick_some hpk).1, p, hp, (pick_some hpk).2⟩
  · obtain ⟨l, hpk⟩ := pick_of_holds (hall p hp)
    exact holds_iff.mpr ⟨l, List.mem_filterMap.mpr ⟨p, hp, hpk⟩, (pick_some hpk).2⟩

/-- (4, constructive form) Every firing state has a computed firing sub-state, `core c st`, of at
    most one location per literal of one firing alternative, each covered by a literal of that
    alternative. So the analysis needs requirements only at literal-covered locations. -/
theorem core_spec {c : Cond} {st : State} (hf : fires c st = true) :
    (∀ l ∈ core c st, l ∈ st) ∧ fires c (core c st) = true ∧
    ∃ alt ∈ c, (core c st).length ≤ alt.length ∧ ∀ l ∈ core c st, ∃ p ∈ alt, p.covers l := by
  unfold core
  cases hfind : c.find? (fun alt => alt.all (holds st)) with
  | none =>
    obtain ⟨alt, halt, hall⟩ := fires_iff.mp hf
    exact absurd (List.all_eq_true.mpr hall) (List.find?_eq_none.mp hfind alt halt)
  | some alt =>
    have halt : alt ∈ c := List.mem_of_find?_eq_some hfind
    have hall0 : alt.all (holds st) = true :=
      List.find?_some (p := fun (a : List PFact) => a.all (holds st)) hfind
    have hall : ∀ p ∈ alt, holds st p = true := List.all_eq_true.mp hall0
    obtain ⟨h1, h2, h3⟩ := wit_spec hall
    exact ⟨fun l hl => (h1 l hl).1, fires_iff.mpr ⟨alt, halt, h2⟩,
      alt, halt, h3, fun l hl => (h1 l hl).2⟩
#print axioms core_spec

/-! ## 6. The reversal of a source: requirement transfer -/

/-- A statement with one source rule: if the condition fires, the action taints `targets`;
    the source never removes taint. -/
def post (c : Cond) (targets : List Loc) (st : State) : State :=
  if fires c st then st ++ targets else st

/-- The location `t` alone is sufficient for the downstream property `D`. -/
def ReqSuff (D : State → Prop) (t : Loc) : Prop := ∀ st : State, t ∈ st → D st

/-- (5) The reversed single literal of a source is a MUST: a requirement location `t` among the
    targets that is sufficient downstream makes every location covered by the literal sufficient
    upstream. Every literal tail (`$`, `[any]`), every target list (`$`, `[any-taint]`). -/
theorem rev_unary_source_must {c : Cond} {lit : PFact} {q t : Loc} {targets : List Loc}
    {D : State → Prop} (hc : [lit] ∈ c) (hq : lit.covers q) (ht : t ∈ targets)
    (hD : ReqSuff D t) : ReqSuff (D ∘ post c targets) q := by
  intro st hst
  have hf : fires c st = true := unary_seed_must hc hq st hst
  show D (post c targets st)
  unfold post
  rw [if_pos hf]
  exact hD _ (List.mem_append_right _ ht)
#print axioms rev_unary_source_must

/-- The `$` target `P.$ (T)`: the action taints the one location `P` with the mark `T`. -/
theorem rev_unary_source_must_exact {c : Cond} {lit : PFact} {q : Loc} {b : Base}
    {π : List Acc} {T : Mark} {D : State → Prop} (hc : [lit] ∈ c) (hq : lit.covers q)
    (hD : ReqSuff D ⟨b, π, T⟩) : ReqSuff (D ∘ post c [⟨b, π, T⟩]) q :=
  rev_unary_source_must hc hq (List.mem_singleton.mpr rfl) hD
#print axioms rev_unary_source_must_exact

/-- The reversed literals of ANY source are a sound MAY cover: a requirement location `t` that
    the statement newly taints comes from a firing state, whose computed core is made of
    literal-covered locations. -/
theorem rev_source_may_cover {c : Cond} {st : State} {t : Loc} {targets : List Loc}
    (hnt : t ∉ st) (ht : t ∈ post c targets st) :
    t ∈ targets ∧ fires c st = true ∧ (∀ l ∈ core c st, l ∈ st) ∧
    fires c (core c st) = true ∧ ∃ alt ∈ c, ∀ l ∈ core c st, ∃ p ∈ alt, p.covers l := by
  unfold post at ht
  cases hf : fires c st with
  | false => rw [if_neg (by rw [hf]; exact Bool.false_ne_true)] at ht; exact absurd ht hnt
  | true =>
    rw [if_pos hf] at ht
    have htt : t ∈ targets := by
      rcases List.mem_append.mp ht with h | h
      · exact absurd h hnt
      · exact h
    obtain ⟨h1, h2, alt, halt, _, h4⟩ := core_spec hf
    exact ⟨htt, rfl, h1, h2, alt, halt, h4⟩
#print axioms rev_source_may_cover

/-- The requirement "the location `t` is tainted". -/
def at_ (t : Loc) : State → Prop := fun st => t ∈ st

theorem at_reqSuff (t : Loc) : ReqSuff (at_ t) t := fun _ h => h

/-- (6) The reversed literal of a two-literal source is not a MUST: a location `q` that the
    other literal does not cover is not sufficient (witness state `[q]`). -/
theorem rev_nd_source_not_must_gen {a b : PFact} {q t : Loc} {targets : List Loc}
    (hb : ¬ b.covers q) (htq : t ≠ q) : ¬ ReqSuff (at_ t ∘ post [[a, b]] targets) q := by
  intro h
  have hnf : fires [[a, b]] [q] = false := by
    cases hf : fires [[a, b]] [q] with
    | false => rfl
    | true => exact absurd (nd_suff_iff.mp (suff_iff.mpr hf)).2 hb
  have := h [q] (List.mem_singleton.mpr rfl)
  change t ∈ post [[a, b]] targets [q] at this
  unfold post at this
  rw [if_neg (by rw [hnf]; exact Bool.false_ne_true)] at this
  exact htq (List.mem_singleton.mp this)
#print axioms rev_nd_source_not_must_gen

/-- (6, executable) `x.[any](7) ∧ y.$(7)` gives the target `z.$(4)`; the requirement "`z.$(4)`
    is tainted" is a MUST at `z`, but `x.f` (covered by the first literal) is not sufficient:
    from the state `[x.f]` the statement does not taint `z`. -/
def ndT : Loc := ⟨9, [], 4⟩

theorem rev_nd_source_not_must :
    ndA.covers ndL ∧ ReqSuff (at_ ndT) ndT ∧ ¬ ReqSuff (at_ ndT ∘ post [[ndA, ndB]] [ndT]) ndL ∧
    ndT ∉ post [[ndA, ndB]] [ndT] [ndL] :=
  ⟨by decide, at_reqSuff ndT,
    rev_nd_source_not_must_gen (by decide) (by decide), by decide⟩
#print axioms rev_nd_source_not_must

/-! ## 7. The reversal of a pass rule with an `AnyField` target -/

/-- The real semantics of `CopyAllMarks(P → Q.AnyField)` / `CopyMark(T, P → Q.AnyField)`: the
    program writes the taint of each location under `P` to ONE location under `Q`, chosen by
    `choose`; the analysis does not know which. -/
def postPass (P : PFact) (choose : Loc → Loc) (st : State) : State :=
  st ++ (st.filter (covB P)).map choose

/-- The reversal of the may edge is a sound MAY cover: if the program respects the rule (each
    choice is related by the model edge `i → f`), a requirement location `x` that the call newly
    taints has a source in the state related to it by the model edge. -/
theorem rev_pass_may_sound {i f : PFact} {choose : Loc → Loc} {st : State} {x : Loc}
    (hch : ∀ p, i.covers p → den i f p (choose p)) (hx : x ∈ postPass i choose st) :
    x ∈ st ∨ ∃ p ∈ st, den i f p x := by
  rcases List.mem_append.mp hx with h | h
  · exact Or.inl h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    obtain ⟨hps, hpc⟩ := List.mem_filter.mp hp
    exact Or.inr ⟨p, hps, hch p (covB_iff.mp hpc)⟩
#print axioms rev_pass_may_sound

/-- (7) The reversal of the may edge is not a MUST: a source location `p` is not sufficient for
    the requirement location `x` under `Q` if the program chose another location. -/
theorem rev_pass_any_not_must_gen {P : PFact} {choose : Loc → Loc} {p x : Loc}
    (hxp : x ≠ p) (hch : choose p ≠ x) : ¬ ReqSuff (at_ x ∘ postPass P choose) p := by
  intro h
  have hx := h [p] (List.mem_singleton.mpr rfl)
  change x ∈ postPass P choose [p] at hx
  unfold postPass at hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact hxp (List.mem_singleton.mp h1)
  · obtain ⟨p', hp', he⟩ := List.mem_map.mp h1
    have : p' = p := List.mem_singleton.mp (List.mem_filter.mp hp').1
    subst this
    exact hch he
#print axioms rev_pass_any_not_must_gen

/-- The executable counterexample. `CopyMark(5, a → b.AnyField)`: the model edge
    `a.$(5) → b.[any](5)` relates `a` to both `b.f0` and `b.f1`; the program writes `b.f0`.
    The requirement "`b.f1` is tainted" is a MUST at `b.f1`, but `a` is not sufficient. -/
def pcI : PFact := ⟨1, [], .exact, .conc 5⟩
def pcF : PFact := ⟨2, [], .any, .conc 5⟩
def pcP : Loc := ⟨1, [], 5⟩
def pcY : Loc := ⟨2, [0], 5⟩
def pcX : Loc := ⟨2, [1], 5⟩

theorem pc_den (y : List Acc) : den pcI pcF pcP ⟨2, y, 5⟩ :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], y, rfl, rfl, rfl, trivial⟩

theorem rev_pass_any_not_must :
    den pcI pcF pcP pcX ∧ den pcI pcF pcP pcY ∧ pcX ≠ pcY ∧
    ReqSuff (at_ pcX) pcX ∧ ¬ ReqSuff (at_ pcX ∘ postPass pcI (fun _ => pcY)) pcP ∧
    postPass pcI (fun _ => pcY) [pcP] = [pcP, pcY] :=
  ⟨pc_den [1], pc_den [0], by decide, at_reqSuff pcX,
    rev_pass_any_not_must_gen (by decide) (by decide), by decide⟩
#print axioms rev_pass_any_not_must

/-! ## 8. The AP form of the B1 requirements -/

/-- The B1 requirements of the positive literals of one alternative (the sink seeds, and the
    reversed literals of a source): one literal gives its pattern in the NORMAL layer (MUST); two
    or more give one DEMAND-layer pattern per literal (MAY); none gives none. -/
def litReqs : List PFact → List AFact
  | []             => []
  | [p]            => [⟨p, false⟩]
  | p :: q :: rest => (p :: q :: rest).map (fun r => ⟨r, true⟩)

/-- The B1 requirements of a condition. -/
def reqs (c : Cond) : List AFact := c.flatMap litReqs

theorem litReqs_normal {alt : List PFact} {s : AFact} (hs : s ∈ litReqs alt)
    (hd : s.demand = false) : alt = [s.fact] := by
  match alt, hs with
  | [p], hs =>
    rw [List.mem_singleton.mp hs]
  | p :: q :: rest, hs =>
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hs
    exact Bool.noConfusion hd

theorem mem_litReqs {alt : List PFact} {p : PFact} (hp : p ∈ alt) :
    ∃ s ∈ litReqs alt, s.fact = p := by
  match alt, hp with
  | [r], hp =>
    exact ⟨⟨r, false⟩, List.mem_singleton.mpr rfl, (List.mem_singleton.mp hp).symm⟩
  | r :: r' :: rest, hp =>
    exact ⟨⟨p, true⟩, List.mem_map.mpr ⟨p, hp, rfl⟩, rfl⟩

/-- A two-or-more literal alternative gives only demand-layer requirements. -/
theorem reqs_nd_demand {alt : List PFact} (h : 2 ≤ alt.length) :
    ∀ s ∈ litReqs alt, s.demand = true := by
  match alt, h with
  | p :: q :: rest, _ =>
    intro s hs
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hs
    rfl
#print axioms reqs_nd_demand

/-- (8) Every NORMAL B1 seed is a MUST: each location it covers is sufficient. -/
theorem reqs_normal_must {c : Cond} {s : AFact} {l : Loc} (hs : s ∈ reqs c)
    (hd : s.demand = false) (hl : s.fact.covers l) : Suff c l := by
  obtain ⟨alt, halt, hs'⟩ := List.mem_flatMap.mp hs
  have := litReqs_normal hs' hd
  subst this
  exact unary_seed_must halt hl
#print axioms reqs_normal_must

/-- (8) Every NORMAL B1 reversed source literal is a MUST. -/
theorem reqs_normal_rev_must {c : Cond} {s : AFact} {q t : Loc} {targets : List Loc}
    {D : State → Prop} (hs : s ∈ reqs c) (hd : s.demand = false) (hq : s.fact.covers q)
    (ht : t ∈ targets) (hD : ReqSuff D t) : ReqSuff (D ∘ post c targets) q := by
  obtain ⟨alt, halt, hs'⟩ := List.mem_flatMap.mp hs
  have := litReqs_normal hs' hd
  subst this
  exact rev_unary_source_must halt hq ht hD
#print axioms reqs_normal_rev_must

/-- (8) All B1 requirements together (both layers) are a sound MAY cover. -/
theorem reqs_may_cover {c : Cond} {st : State} {l : Loc}
    (hf : fires c st = true) (hl : l ∈ st) (hmin : fires c (st.erase l) = false) :
    ∃ s ∈ reqs c, s.fact.covers l := by
  obtain ⟨alt, halt, _, p, hp, hc⟩ := seed_may_cover hf hl hmin
  obtain ⟨s, hs, rfl⟩ := mem_litReqs hp
  exact ⟨s, List.mem_flatMap.mpr ⟨alt, halt, hs⟩, hc⟩
#print axioms reqs_may_cover

/-- (8) An all-unary condition: every B1 requirement is normal, and together they cover EXACTLY
    the sufficient locations. -/
theorem reqs_unary_exact {lits : List PFact} {l : Loc} :
    (∀ s ∈ reqs (lits.map (fun p => [p])), s.demand = false) ∧
    ((∃ s ∈ reqs (lits.map (fun p => [p])), s.fact.covers l) ↔
      Suff (lits.map (fun p => [p])) l) := by
  refine ⟨fun s hs => ?_, ⟨fun ⟨s, hs, hc⟩ => ?_, fun h => ?_⟩⟩
  · obtain ⟨alt, halt, hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp halt
    rw [List.mem_singleton.mp hs']
  · obtain ⟨alt, halt, hs'⟩ := List.mem_flatMap.mp hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp halt
    rw [List.mem_singleton.mp hs'] at hc
    exact unary_seed_must (List.mem_map.mpr ⟨p, hp, rfl⟩) hc
  · obtain ⟨p, hp, hc⟩ := (unary_cond_exact rfl).mp h
    refine ⟨⟨p, false⟩, List.mem_flatMap.mpr ⟨[p], List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩, hc⟩
    exact List.mem_singleton.mpr rfl
#print axioms reqs_unary_exact

/-- The pattern of `ContainsMarkOnAnyField(P, T)`: `P.[any] (T)`. -/
def anyLit (b : Base) (π : List Acc) (T : Mark) : PFact := ⟨b, π, .any, .conc T⟩

theorem anyLit_covers_iff {b : Base} {π : List Acc} {T : Mark} {l : Loc} :
    (anyLit b π T).covers l ↔ l.base = b ∧ (∃ σ, l.path = π ++ σ) ∧ l.mark = T :=
  ⟨fun ⟨hb, ⟨σ, hσ, _⟩, hm⟩ => ⟨hb, ⟨σ, hσ⟩, hm⟩,
   fun ⟨hb, ⟨σ, hσ⟩, hm⟩ => ⟨hb, ⟨σ, hσ, trivial⟩, hm⟩⟩
#print axioms anyLit_covers_iff

/-- (8) The seed of a single `ContainsMarkOnAnyField(P, T)` literal is `P.[any] (T)` in the
    NORMAL layer, and it covers EXACTLY the sufficient locations: every location at or below `P`
    with the mark `T`. The same holds for it as one unary alternative among others (`c` any
    condition with `[anyLit b π T] ∈ c`: `unary_seed_must`). -/
theorem any_seed_exact (b : Base) (π : List Acc) (T : Mark) :
    reqs [[anyLit b π T]] = [⟨anyLit b π T, false⟩] ∧
    ∀ l, ((anyLit b π T).covers l ↔ Suff [[anyLit b π T]] l) ∧
      (Suff [[anyLit b π T]] l ↔ l.base = b ∧ (∃ σ, l.path = π ++ σ) ∧ l.mark = T) := by
  refine ⟨rfl, fun l => ?_⟩
  have hu := unary_cond_exact (c := [[anyLit b π T]]) (lits := [anyLit b π T]) (l := l) rfl
  have h : (anyLit b π T).covers l ↔ Suff [[anyLit b π T]] l :=
    ⟨fun h => hu.mpr ⟨_, List.mem_singleton.mpr rfl, h⟩,
      fun hs => by
        obtain ⟨p, hp, h⟩ := hu.mp hs
        exact List.mem_singleton.mp hp ▸ h⟩
  exact ⟨h, h.symm.trans anyLit_covers_iff⟩
#print axioms any_seed_exact

/-! ## 9. Negated literals: B1 is MUST for the projected condition -/

/-- A signed literal: `(p, true)` is `p`, `(p, false)` is `NOT p`. -/
abbrev SLit := PFact × Bool

/-- A signed condition (DNF of signed literals). -/
abbrev SCond := List (List SLit)

def sholds (st : State) (s : SLit) : Bool := if s.2 then holds st s.1 else !holds st s.1

def firesS (c : SCond) (st : State) : Bool := c.any (fun alt => alt.all (sholds st))

/-- The projection of the negated literals to true (interpreter.md §4.2). -/
def proj (c : SCond) : Cond := c.map (fun alt => (alt.filter (fun s => s.2)).map (fun s => s.1))

/-- The projection is an over-approximation. -/
theorem firesS_proj {c : SCond} {st : State} (h : firesS c st = true) :
    fires (proj c) st = true := by
  unfold firesS at h
  obtain ⟨alt, halt, hall⟩ := List.any_eq_true.mp h
  refine fires_iff.mpr ⟨_, List.mem_map.mpr ⟨alt, halt, rfl⟩, fun p hp => ?_⟩
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp hs
  have := List.all_eq_true.mp hall s hs1
  unfold sholds at this
  rw [if_pos hs2] at this
  exact this
#print axioms firesS_proj

/-- `x.[any](7) ∧ NOT y.$(7)`: after the projection the alternative has one positive literal,
    so B1 makes `x.f` a MUST, and it is sufficient for the projected condition. Against the
    signed condition `x.f` is not sufficient: the state `[x.f, y]` does not fire it. -/
def sgC : SCond := [[(ndA, true), (ndB, false)]]
def ndLB : Loc := ⟨2, [], 7⟩

theorem signed_not_must :
    proj sgC = [[ndA]] ∧ Suff (proj sgC) ndL ∧
    firesS sgC [ndL] = true ∧ firesS sgC [ndL, ndLB] = false := by decide
#print axioms signed_not_must

end ApSpec.BackCond
