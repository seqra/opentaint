/-!
# Field quantifiers: `[all-fields]`, `[any-field]` and the summary application table

Spec `backward-condition-progress.md` §N.1, §N.5, §N.6, §I.7. A field tail reads its location set
with a quantifier: `[all-fields]` (every covered location) and `[any-field]` (some covered location).
`$` is one location. A forward fact CLAIMS its end on the taint state at its node. A backward
requirement says that its end on the taint state at its node makes the sink fire (`Req`). A summary
edge relates the end at the forward ENTRY of the method to the end at the forward EXIT (`Valid`), for
both directions: the direction only tells which end is the premise.

* `impl_*`: the implication table between ends (`Impl`); each row is exact (both directions).
* `valid_one`, `valid_all`, `valid_some`: what a valid edge means for each entry kind (nine shapes).
* `fwd_apply`, `bwd_apply`: the application rule of each run is sound.
  `fwd_apply_exact`, `bwd_apply_exact`: no weaker condition is sound for every edge.
* `all_sub`, `all_kill`, `req_any_sub`: the native kinds survive narrowing. `Cex.*`: the foreign kinds
  (a forward `[any-field]` claim, a backward `[all-fields]` requirement) do not.

Constructive: no classical axioms; every existence proof gives its witness.
-/

namespace ApSpec.FieldQuant

universe u

/-- An end of a fact, a requirement or a summary edge: one location (`$`), or a location set read
    with a quantifier. -/
inductive End (α : Type u) where
  | one       (l : α)
  | allFields (S : α → Prop)
  | anyField  (S : α → Prop)

variable {α : Type u}

/-- The end holds on the taint state `σ` (the set of tainted locations). -/
def holds (σ : α → Prop) : End α → Prop
  | .one l       => σ l
  | .allFields S => ∀ l, S l → σ l
  | .anyField S  => ∃ l, S l ∧ σ l

theorem holds_mono {σ σ' : α → Prop} (h : ∀ l, σ l → σ' l) : ∀ e : End α, holds σ e → holds σ' e
  | .one _,       hx => h _ hx
  | .allFields _, hx => fun l hl => h l (hx l hl)
  | .anyField _,  hx => let ⟨l, hl, hσ⟩ := hx; ⟨l, hl, h l hσ⟩

/-! ## 1. The implication table (spec §N.5) -/

/-- `e1` implies `e2` on every taint state. -/
def Impl (e1 e2 : End α) : Prop := ∀ σ, holds σ e1 → holds σ e2

theorem impl_one (a : α) (e : End α) : Impl (.one a) e ↔ holds (· = a) e := by
  constructor
  · intro h; exact h _ rfl
  · intro h σ ha; exact holds_mono (fun l hl => by subst hl; exact ha) e h

theorem impl_all_one (S : α → Prop) (r : α) : Impl (.allFields S) (.one r) ↔ S r := by
  constructor
  · intro h; exact h S (fun _ hl => hl)
  · intro h σ hs; exact hs r h

/-- `[all-fields] S ⇒ [all-fields] Y` ⇔ `Y ⊆ S` (inside). -/
theorem impl_all_all (S Y : α → Prop) : Impl (.allFields S) (.allFields Y) ↔ ∀ l, Y l → S l := by
  constructor
  · intro h; exact h S (fun _ hl => hl)
  · intro h σ hs l hl; exact hs l (h l hl)

/-- `[all-fields] S ⇒ [any-field] Y` ⇔ `S ∩ Y ≠ ∅` (overlap), with a witness. -/
theorem impl_all_any (S Y : α → Prop) : Impl (.allFields S) (.anyField Y) ↔ ∃ l, S l ∧ Y l := by
  constructor
  · intro h; obtain ⟨l, hy, hs⟩ := h S (fun _ hl => hl); exact ⟨l, hs, hy⟩
  · intro ⟨l, hs, hy⟩ σ hσ; exact ⟨l, hy, hσ l hs⟩

theorem impl_any_one (S : α → Prop) (r : α) : Impl (.anyField S) (.one r) ↔ ∀ l, S l → l = r := by
  constructor
  · intro h l hl; exact (h (· = l) ⟨l, hl, rfl⟩).symm
  · intro h σ ⟨l, hl, hσ⟩; exact (h l hl) ▸ hσ

theorem impl_any_all (S Y : α → Prop) :
    Impl (.anyField S) (.allFields Y) ↔ ∀ l, S l → ∀ l', Y l' → l' = l := by
  constructor
  · intro h l hl l' hl'; exact h (· = l) ⟨l, hl, rfl⟩ l' hl'
  · intro h σ ⟨l, hl, hσ⟩ l' hl'; exact (h l hl l' hl') ▸ hσ

/-- `[any-field] S ⇒ [any-field] Y` ⇔ `S ⊆ Y` (inside, the other way). -/
theorem impl_any_any (S Y : α → Prop) : Impl (.anyField S) (.anyField Y) ↔ ∀ l, S l → Y l := by
  constructor
  · intro h l hl; obtain ⟨l', hy, he⟩ := h (· = l) ⟨l, hl, rfl⟩; exact he ▸ hy
  · intro h σ ⟨l, hl, hσ⟩; exact ⟨l, h l hl, hσ⟩

/-- The "never" cells: a field tail covers two different locations. -/
theorem not_impl_one_all {a l1 l2 : α} {Y : α → Prop} (h1 : Y l1) (h2 : Y l2) (hne : l1 ≠ l2) :
    ¬ Impl (.one a) (.allFields Y) := by
  intro h
  have e1 : l1 = a := h (· = a) rfl l1 h1
  have e2 : l2 = a := h (· = a) rfl l2 h2
  exact hne (e1.trans e2.symm)

theorem not_impl_any_one {r l1 l2 : α} {S : α → Prop} (h1 : S l1) (h2 : S l2) (hne : l1 ≠ l2) :
    ¬ Impl (.anyField S) (.one r) := by
  intro h
  have e1 := (impl_any_one S r).mp h l1 h1
  have e2 := (impl_any_one S r).mp h l2 h2
  exact hne (e1.trans e2.symm)

theorem not_impl_any_all {l1 l2 : α} {S Y : α → Prop} (hs : S l1) (h2 : Y l2)
    (hne : l1 ≠ l2) : ¬ Impl (.anyField S) (.allFields Y) := by
  intro h
  have e2 := (impl_any_all S Y).mp h l1 hs l2 h2
  exact hne e2.symm

/-! ## 2. Summary edges (spec §N.6) -/

/-- The taint at the forward exit that the taint `σ` at the forward entry gives through the flows
    `F` (entry location, exit location) of the method. -/
def post (F : α → α → Prop) (σ : α → Prop) (r : α) : Prop := ∃ a, σ a ∧ F a r

theorem post_mono (F : α → α → Prop) {σ σ' : α → Prop} (h : ∀ l, σ l → σ' l) :
    ∀ r, post F σ r → post F σ' r := fun _ ⟨a, ha, hf⟩ => ⟨a, h a ha, hf⟩

/-- A valid edge with the end `Y` at the forward entry and the end `X` at the forward exit: the entry
    end on the entry state gives the exit end on the exit state. One meaning for both directions. -/
def Valid (F : α → α → Prop) (Y X : End α) : Prop := ∀ σ, holds σ Y → holds (post F σ) X

/-- Entry `$ a`: the flows from `a` give `X` (`$`: `F a r`; `[all-fields]`: each `r`; `[any-field]`:
    some `r`). -/
theorem valid_one (F : α → α → Prop) (a : α) (X : End α) :
    Valid F (.one a) X ↔ holds (F a) X := by
  constructor
  · intro h
    exact holds_mono (fun _ ⟨a', ha', hf⟩ => by subst ha'; exact hf) X (h (· = a) rfl)
  · intro h σ ha; exact holds_mono (fun _ hf => ⟨a, ha, hf⟩) X h

/-- Entry `[all-fields] Y`: the flows from the whole of `Y` give `X` (with `X = [all-fields]`: every
    exit location has a source in `Y`, END-EXACT; with `X = [any-field]`: some flow from `Y` into `X`). -/
theorem valid_all (F : α → α → Prop) (Y : α → Prop) (X : End α) :
    Valid F (.allFields Y) X ↔ holds (post F Y) X := by
  constructor
  · intro h; exact h Y (fun _ hl => hl)
  · intro h σ hy; exact holds_mono (post_mono F (fun l hl => hy l hl)) X h

/-- Entry `[any-field] Y`: the flows from EACH location of `Y` give `X` (with `X = [any-field]`: every
    entry location reaches some exit location; with `X = $` or `[all-fields]`: pair-exact). -/
theorem valid_any (F : α → α → Prop) (Y : α → Prop) (X : End α) :
    Valid F (.anyField Y) X ↔ ∀ a, Y a → holds (F a) X := by
  constructor
  · intro h a ha
    exact holds_mono (fun _ ⟨a', ha', hf⟩ => by subst ha'; exact hf) X (h (· = a) ⟨a, ha, rfl⟩)
  · intro h σ ⟨a, ha, hσ⟩; exact holds_mono (fun _ hf => ⟨a, hσ, hf⟩) X (h a ha)

/-- The four edges with field tails at both ends, spelled out. -/
theorem valid_all_all (F : α → α → Prop) (Y X : α → Prop) :
    Valid F (.allFields Y) (.allFields X) ↔ ∀ r, X r → ∃ a, Y a ∧ F a r :=
  valid_all F Y (.allFields X)
theorem valid_all_any (F : α → α → Prop) (Y X : α → Prop) :
    Valid F (.allFields Y) (.anyField X) ↔ ∃ r, X r ∧ ∃ a, Y a ∧ F a r :=
  valid_all F Y (.anyField X)
theorem valid_any_all (F : α → α → Prop) (Y X : α → Prop) :
    Valid F (.anyField Y) (.allFields X) ↔ ∀ a, Y a → ∀ r, X r → F a r :=
  valid_any F Y (.allFields X)
theorem valid_any_any (F : α → α → Prop) (Y X : α → Prop) :
    Valid F (.anyField Y) (.anyField X) ↔ ∀ a, Y a → ∃ r, X r ∧ F a r :=
  valid_any F Y (.anyField X)

/-! ## 3. Application (spec §I.7) -/

/-- FORWARD run: a claim `A` at the forward entry that implies the entry end gives the exit end. -/
theorem fwd_apply {F : α → α → Prop} {Y X A : End α} {σ : α → Prop} (hv : Valid F Y X)
    (hi : Impl A Y) (ha : holds σ A) : holds (post F σ) X :=
  hv σ (hi σ ha)

/-- A backward requirement: the end `R` on the taint state at its node makes the sink fire (`G`). -/
def Req (G : (α → Prop) → Prop) (R : End α) : Prop := ∀ σ, holds σ R → G σ

/-- BACKWARD run: a requirement `R` at the forward exit that the exit end implies gives the
    requirement "the entry end makes the sink fire". -/
theorem bwd_apply {F : α → α → Prop} {Y X R : End α} {G : (α → Prop) → Prop} (hv : Valid F Y X)
    (hi : Impl X R) (hr : Req G R) : Req (fun σ => G (post F σ)) Y :=
  fun σ hy => hr _ (hi _ (hv σ hy))

/-- The same with more taint at the exit than the flows give (other sources, other callers): the
    sink condition is monotone. -/
theorem bwd_apply_mono {F : α → α → Prop} {Y X R : End α} {G : (α → Prop) → Prop}
    (hm : ∀ σ₁ σ₂, (∀ l, σ₁ l → σ₂ l) → G σ₁ → G σ₂) (hv : Valid F Y X) (hi : Impl X R)
    (hr : Req G R) : Req (fun σ => ∀ σ', (∀ r, post F σ r → σ' r) → G σ') Y :=
  fun σ hy _ hsub => hm _ _ hsub (hr _ (hi _ (hv σ hy)))

theorem valid_id (Y : End α) : Valid (· = ·) Y Y :=
  fun _ hy => holds_mono (fun r hr => ⟨r, hr, rfl⟩) Y hy

theorem post_id {σ : α → Prop} : ∀ r, post (· = ·) σ r → σ r :=
  fun _ ⟨_, ha, he⟩ => by subst he; exact ha

/-- The forward rule is exact: a condition that is sound for every valid edge implies `Impl A Y`
    (take the identity edge `Y → Y`). -/
theorem fwd_apply_exact {A Y : End α}
    (h : ∀ (F : α → α → Prop) (X : End α), Valid F Y X → ∀ σ, holds σ A → holds (post F σ) X) :
    Impl A Y :=
  fun σ ha => holds_mono post_id Y (h (· = ·) Y (valid_id Y) σ ha)

/-- The backward rule is exact (take the identity edge `X → X` and the sink "`R` holds"). -/
theorem bwd_apply_exact {X R : End α}
    (h : ∀ (F : α → α → Prop) (Y : End α) (G : (α → Prop) → Prop), Valid F Y X → Req G R →
      Req (fun σ => G (post F σ)) Y) :
    Impl X R :=
  fun σ hx => h (· = ·) X (fun σ => holds σ R) (valid_id X) (fun _ hr => hr) σ hx
    |> holds_mono post_id R

/-! ## 4. Narrowing: native kinds survive it, foreign kinds do not (spec §D2) -/

/-- A forward `[all-fields]` claim gives the claim on each subset (restriction, a deeper emission). -/
theorem all_sub {σ : α → Prop} {S S' : α → Prop} (h : ∀ l, S' l → S l) :
    holds σ (.allFields S) → holds σ (.allFields S') :=
  fun hs l hl => hs l (h l hl)

/-- A forward `[all-fields]` claim survives a strong update that kills `K` (the exclusion grows). -/
theorem all_kill {σ K S : α → Prop} :
    holds σ (.allFields S) → holds (fun l => σ l ∧ ¬ K l) (.allFields (fun l => S l ∧ ¬ K l)) :=
  fun hs l ⟨hl, hk⟩ => ⟨hs l hl, hk⟩

/-- A backward `[any-field]` requirement gives the requirement on each subset. -/
theorem req_any_sub {G : (α → Prop) → Prop} {S S' : α → Prop} (h : ∀ l, S' l → S l) :
    Req G (.anyField S) → Req G (.anyField S') :=
  fun hr σ ⟨l, hl, hσ⟩ => hr σ ⟨l, h l hl, hσ⟩

namespace Cex

/-- Two locations `1`, `2` and the subset `{2}`. -/
def S12 (l : Nat) : Prop := l = 1 ∨ l = 2
def S2 (l : Nat) : Prop := l = 2

/-- A forward `[any-field]` claim does not give the claim on a subset: the tainted location can be
    the one that the subset leaves out. -/
theorem any_not_sub :
    holds (· = 1) (.anyField S12) ∧ ¬ holds (· = 1) (.anyField S2) :=
  ⟨⟨1, Or.inl rfl, rfl⟩, fun ⟨_, h2, h1⟩ => by unfold S2 at h2; subst h2; exact absurd h1 (by decide)⟩

/-- A forward `[any-field]` claim does not survive a strong update that kills the tainted location. -/
theorem any_not_kill :
    holds (· = 1) (.anyField S12) ∧
    ¬ holds (fun l => l = 1 ∧ ¬ l = 1) (.anyField (fun l => S12 l ∧ ¬ l = 1)) :=
  ⟨⟨1, Or.inl rfl, rfl⟩, fun ⟨_, _, h, hn⟩ => hn h⟩

/-- A backward `[all-fields]` requirement does not give the requirement on a subset: taint on the
    subset alone does not fire. -/
theorem all_req_not_sub :
    Req (fun σ => holds σ (.allFields S12)) (.allFields S12) ∧
    ¬ Req (fun σ => holds σ (.allFields S12)) (.allFields S2) := by
  refine ⟨fun _ h => h, fun h => ?_⟩
  have h1 := h (· = 2) (fun _ hl => hl) 1 (Or.inl rfl)
  exact absurd h1 (by decide)

/-! ### One code tail is not enough (spec §N.7, rule F)

With one field tail, the reading of a fact comes from the run direction. These cases show that the
kind must be part of the fact: the same tail bits on the same location sets mean different things. -/

/-- Locations `1`, `2` at the forward entry, `3`, `4` at the forward exit. -/
def Y12 (l : Nat) : Prop := l = 1 ∨ l = 2
def Y1 (l : Nat) : Prop := l = 1
def X3 (l : Nat) : Prop := l = 3
def X34 (l : Nat) : Prop := l = 3 ∨ l = 4
/-- One flow, `1 → 3`. -/
def F13 (a r : Nat) : Prop := a = 1 ∧ r = 3

/-- §I.8 case 2 in the backward run: the forward must record `[all-fields] Y12 → [all-fields] X3` is
    valid, and with the reader `$ 3` the result `[all-fields] Y12` is sound. Read with the backward
    native kind, `[any-field] Y12`, it is false: taint at `2` alone does not reach `3`. -/
theorem case2_needs_all_fields :
    Valid F13 (.allFields Y12) (.allFields X3) ∧
    Req (fun σ => post F13 σ 3) (.allFields Y12) ∧
    ¬ Req (fun σ => post F13 σ 3) (.anyField Y12) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (valid_all_all F13 Y12 X3).mpr fun r hr => ⟨1, Or.inl rfl, rfl, hr⟩
  · intro σ hy; exact ⟨1, hy 1 (Or.inl rfl), rfl, rfl⟩
  · intro h
    obtain ⟨a, ha, ha1, _⟩ := h (· = 2) ⟨2, Or.inr rfl, rfl⟩
    subst ha1; exact absurd ha (by decide)

/-- §I.8 case 3 in the forward run: the backward must record `[any-field] Y1 → [any-field] X34`
    (forward orientation) is valid, and with the claim `$ 1` the result `[any-field] X34` holds. Read
    with the forward native kind, `[all-fields] X34`, it is false: `4` is not tainted. -/
theorem case3_needs_any_field :
    Valid F13 (.anyField Y1) (.anyField X34) ∧
    holds (post F13 (· = 1)) (.anyField X34) ∧
    ¬ holds (post F13 (· = 1)) (.allFields X34) := by
  refine ⟨?_, ⟨3, Or.inl rfl, 1, rfl, rfl, rfl⟩, ?_⟩
  · exact (valid_any_any F13 Y1 X34).mpr fun a ha => ⟨3, Or.inl rfl, ha, rfl⟩
  · intro h
    obtain ⟨_, _, _, h4⟩ := h 4 (Or.inr rfl)
    exact absurd h4 (by decide)

/-- Two summaries of ONE direction with the same tail bits and the same ends have different
    meanings: under D2 a backward summary can start from a foreign `[all-fields]` requirement, so the
    direction cannot give the kind. `F13` validates `[all-fields] Y12 → [all-fields] X3` and not
    `[any-field] Y12 → [any-field] X3`. -/
theorem same_bits_two_meanings :
    Valid F13 (.allFields Y12) (.allFields X3) ∧ ¬ Valid F13 (.anyField Y12) (.anyField X3) := by
  refine ⟨case2_needs_all_fields.1, fun h => ?_⟩
  obtain ⟨_, _, ha, _⟩ := (valid_any_any F13 Y12 X3).mp h 2 (Or.inr rfl)
  exact absurd ha (by decide)

end Cex

end ApSpec.FieldQuant

#print axioms ApSpec.FieldQuant.impl_all_any
#print axioms ApSpec.FieldQuant.impl_any_any
#print axioms ApSpec.FieldQuant.valid_any
#print axioms ApSpec.FieldQuant.bwd_apply_exact
#print axioms ApSpec.FieldQuant.fwd_apply_exact
#print axioms ApSpec.FieldQuant.Cex.any_not_sub
#print axioms ApSpec.FieldQuant.Cex.all_req_not_sub
#print axioms ApSpec.FieldQuant.Cex.case2_needs_all_fields
#print axioms ApSpec.FieldQuant.Cex.case3_needs_any_field
#print axioms ApSpec.FieldQuant.Cex.same_bits_two_meanings
