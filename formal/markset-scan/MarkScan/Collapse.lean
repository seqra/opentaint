import MarkScan.Basic

/-!
# Collapse of the context-sensitive mark-set concept

The user's concept for the flow-insensitive scan reads literally as a
context-sensitive tabulation: every node `n` is analyzed per input set `IN`,
its `OUT` contains `IN`, is closed under the gens of the rules at `n` whose
mark-only condition is satisfied by `OUT`, and for every call `n → c` the
callee is analyzed with `IN := OUT(n)` and its `OUT` flows back into `OUT(n)`.

This module shows that, without flow sensitivity, the table collapses: the
least solution at `(n, I)` is the closure of `I` under all sites reachable
from `n`, and inside the call tree of a root `E` every context is the single
set `S_E = closure (reachSites p E) []`.
-/

namespace MarkScan

/-! ## 1. Local Dnf lemmas (reproved; `Cond.lean` is not imported) -/

namespace CollapseLemmas

theorem dnf_sat_iff (φ : Dnf) (S : List Mark) :
    φ.sat S = true ↔ ∃ c, c ∈ φ ∧ ∀ m, m ∈ c → m ∈ S := by
  unfold Dnf.sat
  simp only [List.any_eq_true, List.all_eq_true, List.contains_iff_mem]

theorem dnf_sat_mono {φ : Dnf} {S T : List Mark} (h : Subset S T) :
    φ.sat S = true → φ.sat T = true := by
  intro hs
  obtain ⟨c, hc, hall⟩ := (dnf_sat_iff φ S).1 hs
  exact (dnf_sat_iff φ T).2 ⟨c, hc, fun m hm => h m (hall m hm)⟩

theorem subset_refl (a : List Mark) : Subset a a := fun _ h => h

theorem subset_trans {a b c : List Mark} (h1 : Subset a b) (h2 : Subset b c) : Subset a c :=
  fun m hm => h2 m (h1 m hm)

theorem filter_length_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    have ih := filter_length_le_of_imp p q xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq]
    · exact ih
    · exact Nat.le_succ_of_le ih
    · have := h x List.mem_cons_self hp; rw [hq] at this; cases this
    · exact ih

theorem filter_length_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = true → q x = true) →
      (∃ x, x ∈ l ∧ q x = true ∧ p x = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hx, _⟩ => by cases hx
  | x :: xs, h, ⟨y, hy, hqy, hpy⟩ => by
    have hle := filter_length_le_of_imp p q xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    cases List.mem_cons.1 hy with
    | inl e =>
      subst e
      simp [hpy, hqy]
      exact Nat.lt_succ_of_le hle
    | inr hy' =>
      have ih := filter_length_lt_of_imp p q xs
        (fun z hz => h z (List.mem_cons_of_mem _ hz)) ⟨y, hy', hqy, hpy⟩
      cases hp : p x <;> cases hq : q x <;> simp [hp, hq]
      · exact ih
      · exact Nat.lt_succ_of_lt ih
      · have := h x List.mem_cons_self hp; rw [hq] at this; cases this
      · exact ih

end CollapseLemmas

open CollapseLemmas

/-! ## 2. The closure -/

/-- Gens of the sites whose condition holds on `S`. -/
def satGens (sites : List Site) (S : List Mark) : List Mark :=
  sites.flatMap fun σ => if σ.cond.sat S then σ.gens else []

/-- Gens of satisfied sites that are not yet in `S`. -/
def newGens (sites : List Site) (S : List Mark) : List Mark :=
  (satGens sites S).filter fun m => !S.contains m

/-- All gens of all sites, with repetitions. -/
def allGens (sites : List Site) : List Mark :=
  sites.flatMap (·.gens)

/-- Fuel-bounded rounds: each round adds every newly enabled gen. -/
def closeLoop (sites : List Site) : Nat → List Mark → List Mark
  | 0, S => S
  | k + 1, S =>
    if (newGens sites S).isEmpty then S else closeLoop sites k (S ++ newGens sites S)

/-- Fuel for `closure`: the number of gens (with repetitions) plus one. -/
def closureFuel (sites : List Site) : Nat := (allGens sites).length + 1

/-- The least superset of `init` closed under the sites: if `σ.cond.sat S`
then `σ.gens ⊆ S`. -/
def closure (sites : List Site) (init : List Mark) : List Mark :=
  closeLoop sites (closureFuel sites) init

namespace CollapseLemmas

/-- Termination measure: gens (with repetitions) that are still missing. -/
def missing (sites : List Site) (S : List Mark) : Nat :=
  ((allGens sites).filter fun m => !S.contains m).length

theorem mem_satGens {sites : List Site} {S : List Mark} {m : Mark} :
    m ∈ satGens sites S ↔ ∃ σ, σ ∈ sites ∧ σ.cond.sat S = true ∧ m ∈ σ.gens := by
  unfold satGens
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨σ, hσ, hm⟩
    by_cases hs : σ.cond.sat S = true
    · rw [if_pos hs] at hm; exact ⟨σ, hσ, hs, hm⟩
    · rw [if_neg hs] at hm; cases hm
  · rintro ⟨σ, hσ, hs, hm⟩
    exact ⟨σ, hσ, by rw [if_pos hs]; exact hm⟩

theorem mem_newGens {sites : List Site} {S : List Mark} {m : Mark} :
    m ∈ newGens sites S ↔ m ∈ satGens sites S ∧ m ∉ S := by
  unfold newGens
  rw [List.mem_filter]
  simp

theorem mem_allGens {sites : List Site} {m : Mark} :
    m ∈ allGens sites ↔ ∃ σ, σ ∈ sites ∧ m ∈ σ.gens := by
  unfold allGens; rw [List.mem_flatMap]

theorem filter_nil_of_false {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = false) → l.filter p = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons, h x List.mem_cons_self]
    exact filter_nil_of_false p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem newGens_nil_iff {sites : List Site} {S : List Mark} :
    newGens sites S = [] ↔ ∀ σ, σ ∈ sites → σ.cond.sat S = true → Subset σ.gens S := by
  constructor
  · intro h σ hσ hs m hm
    cases hc : S.contains m with
    | true => exact List.contains_iff_mem.1 hc
    | false =>
      have : m ∈ newGens sites S := by
        unfold newGens
        rw [List.mem_filter]
        exact ⟨mem_satGens.2 ⟨σ, hσ, hs, hm⟩, by simp only [hc, Bool.not_false]⟩
      rw [h] at this; cases this
  · intro h
    unfold newGens
    apply filter_nil_of_false
    intro m hm
    obtain ⟨σ, hσ, hs, hg⟩ := mem_satGens.1 hm
    have : S.contains m = true := List.contains_iff_mem.2 (h σ hσ hs m hg)
    simp only [this, Bool.not_true]

theorem missing_le (sites : List Site) (S : List Mark) :
    missing sites S ≤ (allGens sites).length :=
  List.length_filter_le _ _

theorem missing_lt {sites : List Site} {S : List Mark} (h : newGens sites S ≠ []) :
    missing sites (S ++ newGens sites S) < missing sites S := by
  unfold missing
  apply filter_length_lt_of_imp
  · intro x _ hx
    have hx' : (S ++ newGens sites S).contains x = false := by simpa using hx
    have : S.contains x = false := by
      cases hc : S.contains x with
      | false => rfl
      | true =>
        have := List.contains_iff_mem.1 hc
        have h2 : (S ++ newGens sites S).contains x = true :=
          List.contains_iff_mem.2 (List.mem_append_left _ this)
        rw [hx'] at h2; cases h2
    simp only [this, Bool.not_false]
  · cases hn : newGens sites S with
    | nil => exact absurd hn h
    | cons m ms =>
      have hm : m ∈ newGens sites S := by rw [hn]; exact List.mem_cons_self
      obtain ⟨hsat, hnot⟩ := mem_newGens.1 hm
      obtain ⟨σ, hσ, _, hg⟩ := mem_satGens.1 hsat
      refine ⟨m, mem_allGens.2 ⟨σ, hσ, hg⟩, ?_, ?_⟩
      · cases hc : S.contains m with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.1 hc) hnot
      · have : (S ++ m :: ms).contains m = true :=
          List.contains_iff_mem.2 (List.mem_append_right _ List.mem_cons_self)
        simp only [this]; decide

theorem closeLoop_of_nil {sites : List Site} {S : List Mark} (h : newGens sites S = []) :
    ∀ k, closeLoop sites k S = S
  | 0 => rfl
  | k + 1 => by simp [closeLoop, h]

theorem closeLoop_step {sites : List Site} {S : List Mark} (h : newGens sites S ≠ []) (k : Nat) :
    closeLoop sites (k + 1) S = closeLoop sites k (S ++ newGens sites S) := by
  have : (newGens sites S).isEmpty = false := by
    cases hn : newGens sites S with
    | nil => exact absurd hn h
    | cons _ _ => rfl
  simp only [closeLoop, this]; rfl

/-- The fuel is enough: with more rounds than missing gens, the loop ends at a
fixpoint. -/
theorem closeLoop_fix (sites : List Site) :
    ∀ k S, missing sites S < k → newGens sites (closeLoop sites k S) = []
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, S, h => by
    by_cases hn : newGens sites S = []
    · rw [closeLoop_of_nil hn]; exact hn
    · rw [closeLoop_step hn]
      exact closeLoop_fix sites k _ (Nat.lt_of_lt_of_le (missing_lt hn) (Nat.le_of_lt_succ h))

/-- Extra fuel never changes the result. -/
theorem closeLoop_fuel_irrel (sites : List Site) :
    ∀ k k' S, missing sites S < k → missing sites S < k' →
      closeLoop sites k S = closeLoop sites k' S
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, k' + 1, S, h, h' => by
    by_cases hn : newGens sites S = []
    · rw [closeLoop_of_nil hn, closeLoop_of_nil hn]
    · rw [closeLoop_step hn, closeLoop_step hn]
      have hl := missing_lt hn
      exact closeLoop_fuel_irrel sites k k' _
        (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ h))
        (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ h'))

theorem closeLoop_extensive (sites : List Site) :
    ∀ k S, Subset S (closeLoop sites k S)
  | 0, _ => subset_refl _
  | k + 1, S => by
    by_cases hn : newGens sites S = []
    · rw [closeLoop_of_nil hn]; exact subset_refl _
    · rw [closeLoop_step hn]
      exact subset_trans (fun m hm => List.mem_append_left _ hm) (closeLoop_extensive sites k _)

theorem closeLoop_induction (sites : List Site) (P : Mark → Prop)
    (hstep : ∀ σ, σ ∈ sites → ∀ S, (∀ x, x ∈ S → P x) → σ.cond.sat S = true →
      ∀ g, g ∈ σ.gens → P g) :
    ∀ k S, (∀ x, x ∈ S → P x) → ∀ m, m ∈ closeLoop sites k S → P m
  | 0, _, hS => hS
  | k + 1, S, hS => by
    by_cases hn : newGens sites S = []
    · rw [closeLoop_of_nil hn]; exact hS
    · rw [closeLoop_step hn]
      apply closeLoop_induction sites P hstep k
      intro x hx
      cases List.mem_append.1 hx with
      | inl h => exact hS x h
      | inr h =>
        obtain ⟨hsat, _⟩ := mem_newGens.1 h
        obtain ⟨σ, hσ, hs, hg⟩ := mem_satGens.1 hsat
        exact hstep σ hσ S hS hs x hg

end CollapseLemmas

/-- `closure` is a superset of its seed. -/
theorem closure_extensive (sites : List Site) (init : List Mark) :
    Subset init (closure sites init) :=
  closeLoop_extensive sites _ init

/-- The fuel `closureFuel` suffices: `closure` is closed under every site. -/
theorem closure_closed {sites : List Site} {init : List Mark} {σ : Site} (hσ : σ ∈ sites)
    (hs : σ.cond.sat (closure sites init) = true) : Subset σ.gens (closure sites init) :=
  newGens_nil_iff.1
    (closeLoop_fix sites _ init (Nat.lt_succ_of_le (missing_le sites init))) σ hσ hs

/-- Any fuel beyond `closureFuel` computes the same list: the chosen fuel is
not an approximation. -/
theorem closure_fuel_enough (sites : List Site) (init : List Mark) (k : Nat)
    (hk : closureFuel sites ≤ k) : closeLoop sites k init = closure sites init := by
  have h0 : missing sites init < closureFuel sites := Nat.lt_succ_of_le (missing_le sites init)
  exact closeLoop_fuel_irrel sites k _ init (Nat.lt_of_lt_of_le h0 hk) h0

/-- Induction principle: a property of the seed that is preserved by every
site holds on the whole closure. -/
theorem closure_induction (sites : List Site) (init : List Mark) (P : Mark → Prop)
    (hinit : ∀ m, m ∈ init → P m)
    (hstep : ∀ σ, σ ∈ sites → ∀ S, (∀ x, x ∈ S → P x) → σ.cond.sat S = true →
      ∀ g, g ∈ σ.gens → P g) :
    ∀ m, m ∈ closure sites init → P m :=
  closeLoop_induction sites P hstep _ init hinit

/-- `closure` is the least closed superset of the seed. -/
theorem closure_least {sites : List Site} {init T : List Mark} (hinit : Subset init T)
    (hT : ∀ σ, σ ∈ sites → σ.cond.sat T = true → Subset σ.gens T) :
    Subset (closure sites init) T :=
  closure_induction sites init (· ∈ T) hinit
    (fun σ hσ _ hS hs g hg => hT σ hσ (dnf_sat_mono hS hs) g hg)

/-- `closure` is monotone in the sites and in the seed. -/
theorem closure_mono {s1 s2 : List Site} {i1 i2 : List Mark}
    (hs : ∀ σ, σ ∈ s1 → σ ∈ s2) (hi : Subset i1 i2) :
    Subset (closure s1 i1) (closure s2 i2) :=
  closure_least (subset_trans hi (closure_extensive s2 i2))
    (fun σ hσ hsat => closure_closed (hs σ hσ) hsat)

/-- A seed that is already closed is returned unchanged (as a list). -/
theorem closure_of_closed {sites : List Site} {S : List Mark}
    (h : ∀ σ, σ ∈ sites → σ.cond.sat S = true → Subset σ.gens S) : closure sites S = S :=
  closeLoop_of_nil (newGens_nil_iff.2 h) _

/-- `closure` is idempotent, even as a list. -/
theorem closure_idem (sites : List Site) (init : List Mark) :
    closure sites (closure sites init) = closure sites init :=
  closure_of_closed (fun _ hσ hs => closure_closed hσ hs)

/-! ## 3. Well-formed programs and reachability -/

/-- Roots are nodes, and every callee of a node is a node. -/
def WF (p : Program) : Prop :=
  (∀ r, r ∈ p.roots → r ∈ p.nodes) ∧ ∀ n, n ∈ p.nodes → ∀ c, c ∈ p.callees n → c ∈ p.nodes

/-- Executable check of `WF`. -/
def wfb (p : Program) : Bool :=
  p.roots.all (fun r => p.nodes.contains r) &&
    p.nodes.all fun n => (p.callees n).all fun c => p.nodes.contains c

theorem wfb_iff (p : Program) : wfb p = true ↔ WF p := by
  simp [wfb, WF, List.all_eq_true]

instance (p : Program) : Decidable (WF p) := decidable_of_iff _ (wfb_iff p)

/-- A reachability step as a site: "if `x` is reached, its callees are". -/
def reachSite (p : Program) (x : Node) : Site :=
  { rule := 0, kind := .passThrough, cond := [[x]], gens := p.callees x }

/-- Executable reachability, computed by `closure` over the edge sites (fuel:
number of call edges + 1). -/
def reachList (p : Program) (n : Node) : List Node :=
  closure (p.nodes.map (reachSite p)) [n]

namespace CollapseLemmas

theorem reaches_trans {p : Program} {a b c : Node} (h1 : Reaches p a b) (h2 : Reaches p b c) :
    Reaches p a c := by
  induction h1 with
  | refl => exact h2
  | step hab _ ih => exact Reaches.step hab (ih h2)

theorem reaches_snoc {p : Program} {a b c : Node} (h : Reaches p a b) (hc : c ∈ p.callees b) :
    Reaches p a c :=
  reaches_trans h (Reaches.step hc (Reaches.refl c))

theorem reaches_nodes {p : Program} (hwf : WF p) {a b : Node} (h : Reaches p a b) :
    a ∈ p.nodes → b ∈ p.nodes := by
  induction h with
  | refl => exact id
  | step hab _ ih => exact fun ha => ih (hwf.2 _ ha _ hab)

theorem reachSite_sat {p : Program} {x : Node} {S : List Mark} :
    (reachSite p x).cond.sat S = true ↔ x ∈ S := by
  rw [dnf_sat_iff]
  simp [reachSite]

end CollapseLemmas

/-- `reachList` computes call-graph reachability from a node of a well-formed
program. -/
theorem mem_reachList {p : Program} {n k : Node} (hwf : WF p) (hn : n ∈ p.nodes) :
    k ∈ reachList p n ↔ Reaches p n k := by
  constructor
  · intro hk
    refine closure_induction _ [n] (Reaches p n) ?_ ?_ k hk
    · intro m hm
      rw [List.mem_singleton.1 hm]; exact Reaches.refl n
    · intro σ hσ S hS hs g hg
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hσ
      exact reaches_snoc (hS x (reachSite_sat.1 hs)) hg
  · have key : ∀ a, Reaches p a k → a ∈ p.nodes → a ∈ reachList p n → k ∈ reachList p n := by
      intro a hak
      induction hak with
      | refl => exact fun _ h => h
      | @step a b _ hab _ ih =>
        intro ha hin
        have hsat : (reachSite p a).cond.sat (reachList p n) = true := reachSite_sat.2 hin
        have hb : b ∈ reachList p n :=
          closure_closed (List.mem_map.2 ⟨a, ha, rfl⟩) hsat b hab
        exact ih (hwf.2 a ha b hab) hb
    intro h
    exact key n h hn (closure_extensive _ _ n (List.mem_singleton_self n))

/-- A node is always in its own reachability list (no `WF` needed). -/
theorem self_mem_reachList (p : Program) (n : Node) : n ∈ reachList p n :=
  closure_extensive _ _ n (List.mem_singleton_self n)

/-- The abstract sites of one node. -/
def nodeAbsSites (p : Program) (n : Node) : List Site :=
  (p.nodeSites n).map (·.2.abstract)

/-- The abstract sites of every node reachable from `n`. -/
def reachSites (p : Program) (n : Node) : List Site :=
  (reachList p n).flatMap (nodeAbsSites p)

namespace CollapseLemmas

theorem mem_reachSites {p : Program} {n : Node} {σ : Site} :
    σ ∈ reachSites p n ↔ ∃ k, k ∈ reachList p n ∧ σ ∈ nodeAbsSites p k := by
  unfold reachSites; rw [List.mem_flatMap]

theorem nodeAbsSites_sub_reachSites (p : Program) (n : Node) :
    ∀ σ, σ ∈ nodeAbsSites p n → σ ∈ reachSites p n :=
  fun _ h => mem_reachSites.2 ⟨n, self_mem_reachList p n, h⟩

theorem reachSites_mono {p : Program} (hwf : WF p) {a b : Node} (ha : a ∈ p.nodes)
    (hab : Reaches p a b) : ∀ σ, σ ∈ reachSites p b → σ ∈ reachSites p a := by
  intro σ hσ
  obtain ⟨k, hk, hσk⟩ := mem_reachSites.1 hσ
  have hb : b ∈ p.nodes := reaches_nodes hwf hab ha
  have hbk : Reaches p b k := (mem_reachList hwf hb).1 hk
  exact mem_reachSites.2 ⟨k, (mem_reachList hwf ha).2 (reaches_trans hab hbk), hσk⟩

end CollapseLemmas

/-! ## 4. The concept and its collapse -/

/-- The literal (context-sensitive) concept: `T n I` is the `OUT` of node `n`
analyzed with input `I`. -/
def IsConceptSolution (p : Program) (T : Node → List Mark → List Mark) : Prop :=
  ∀ n, n ∈ p.nodes → ∀ I : List Mark,
    Subset I (T n I) ∧
    (∀ σ, σ ∈ nodeAbsSites p n → σ.cond.sat (T n I) = true → Subset σ.gens (T n I)) ∧
    (∀ c, c ∈ p.callees n → Subset (T c (T n I)) (T n I))

/-- The collapsed table: one closure over all reachable sites. -/
def collapseTable (p : Program) : Node → List Mark → List Mark :=
  fun n I => closure (reachSites p n) I

/-- The collapsed table `n, I ↦ closure (reachSites p n) I` satisfies every
clause of the literal concept. -/
theorem collapse_is_solution {p : Program} (hwf : WF p) :
    IsConceptSolution p (fun n I => closure (reachSites p n) I) := by
  intro n hn I
  refine ⟨closure_extensive _ _, ?_, ?_⟩
  · intro σ hσ hs
    exact closure_closed (nodeAbsSites_sub_reachSites p n σ hσ) hs
  · intro c hc
    have hsub := reachSites_mono hwf hn (Reaches.step hc (Reaches.refl c))
    have h1 := closure_mono (i1 := closure (reachSites p n) I) hsub (subset_refl _)
    rw [closure_idem] at h1
    exact h1

namespace CollapseLemmas

/-- In any concept solution, `T a I` is closed under the sites of every node
reachable from `a`. -/
theorem solution_closed_reach {p : Program} {T : Node → List Mark → List Mark} (hwf : WF p)
    (hT : IsConceptSolution p T) {a k : Node} (hak : Reaches p a k) :
    a ∈ p.nodes → ∀ I, ∀ σ, σ ∈ nodeAbsSites p k → σ.cond.sat (T a I) = true →
      Subset σ.gens (T a I) := by
  induction hak with
  | refl a => exact fun ha I => (hT a ha I).2.1
  | @step a b _ hab _ ih =>
    intro ha I σ hσ hs
    have hb := hwf.2 a ha b hab
    obtain ⟨hext, _, hcall⟩ := hT a ha I
    have hextb := (hT b hb (T a I)).1
    have hs' := dnf_sat_mono hextb hs
    exact subset_trans (ih hb (T a I) σ hσ hs') (hcall b hab)

end CollapseLemmas

/-- Every concept solution contains the collapsed closure pointwise, so the
collapsed table is the least concept solution: no per-`(node, IN)` tabulation
can select fewer marks. -/
theorem collapse_least {p : Program} {T : Node → List Mark → List Mark} {n : Node}
    {I : List Mark} (hwf : WF p) (hT : IsConceptSolution p T) (hn : n ∈ p.nodes) :
    Subset (closure (reachSites p n) I) (T n I) := by
  apply closure_least (hT n hn I).1
  intro σ hσ hs
  obtain ⟨k, hk, hσk⟩ := mem_reachSites.1 hσ
  exact solution_closed_reach hwf hT ((mem_reachList hwf hn).1 hk) hn I σ hσk hs

/-- Inside the call tree of `E`, the context fed by the root's `OUT` is already
a fixpoint: analyzing any reachable `k` with input `S_E` returns `S_E` itself
(literally, not only as a set). -/
theorem collapse_context_tree_node {p : Program} {E k : Node} (hwf : WF p) (hE : E ∈ p.nodes)
    (hk : Reaches p E k) :
    closure (reachSites p k) (closure (reachSites p E) []) = closure (reachSites p E) [] :=
  closure_of_closed fun σ hσ hs =>
    closure_closed (reachSites_mono hwf hE hk σ hσ) hs

/-- For a root `E` and any `k` in its call tree, `k` analyzed with input
`S_E` has output set-equal to `S_E`: context sensitivity is vacuous in the
flow-insensitive mode. -/
theorem collapse_context_tree {p : Program} {E k : Node} (hwf : WF p) (hE : E ∈ p.roots)
    (hk : Reaches p E k) :
    Subset (closure (reachSites p k) (closure (reachSites p E) [])) (closure (reachSites p E) []) ∧
    Subset (closure (reachSites p E) []) (closure (reachSites p k) (closure (reachSites p E) [])) := by
  rw [collapse_context_tree_node hwf (hwf.1 E hE) hk]
  exact ⟨subset_refl _, subset_refl _⟩

/-! ## 5. Link to `InS` in the join-free fragment -/

/-- No cube of any site has two or more literals. -/
def JoinFree (p : Program) : Prop :=
  ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.abstract.cond → c.length ≤ 1

namespace CollapseLemmas

theorem mem_nodeSites {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (h : (pc, σ) ∈ p.nodeSites n) : σ ∈ p.sites n pc := by
  unfold Program.nodeSites at h
  obtain ⟨pc', _, h2⟩ := List.mem_flatMap.1 h
  obtain ⟨σ', hσ', e⟩ := List.mem_map.1 h2
  cases e
  exact hσ'

theorem abstract_mem_nodeAbsSites {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (h : (pc, σ) ∈ p.nodeSites n) : σ.abstract ∈ nodeAbsSites p n :=
  List.mem_map.2 ⟨(pc, σ), h, rfl⟩

end CollapseLemmas

/-- Without joined cubes, `S_E` of `Basic` (`InS`) is exactly the closure of
`[]` under the sites reachable from the root `E`. -/
theorem inS_iff_closure {p : Program} {E : Node} {m : Mark} (hwf : WF p) (hjf : JoinFree p)
    (hE : E ∈ p.roots) : InS p E m ↔ m ∈ closure (reachSites p E) [] := by
  constructor
  · intro h
    induction h with
    | @single E n pc σ c g hE' hEn hσ hc _ _ hg ih =>
      have hEn' : E ∈ p.nodes := hwf.1 E hE'
      have hin : σ.abstract ∈ reachSites p E :=
        mem_reachSites.2 ⟨n, (mem_reachList hwf hEn').2 hEn, abstract_mem_nodeAbsSites hσ⟩
      have hs : σ.abstract.cond.sat (closure (reachSites p E) []) = true :=
        (dnf_sat_iff _ _).2 ⟨c, hc, fun x hx => ih x hx hE'⟩
      exact closure_closed hin hs g hg
    | @joined E n pc σ c g _ _ hσ hc h2 _ _ _ _ _ _ =>
      have := hjf n pc σ c (mem_nodeSites hσ) hc
      exact absurd (Nat.le_trans h2 this) (by decide)
  · intro h
    refine closure_induction _ [] (InS p E) (fun _ h => by cases h) ?_ m h
    intro σ hσ S hS hs g hg
    obtain ⟨k, hk, hσk⟩ := mem_reachSites.1 hσ
    obtain ⟨⟨pc, σ'⟩, hσ', e⟩ := List.mem_map.1 hσk
    cases e
    obtain ⟨c, hc, hall⟩ := (dnf_sat_iff _ _).1 hs
    exact InS.single hE ((mem_reachList hwf (hwf.1 E hE)).1 hk) hσ' hc
      (hjf k pc σ' c (mem_nodeSites hσ') hc) (fun x hx => hS x (hall x hx)) hg

/-! ## 6. Contexts visited by the literal concept -/

/-- Unfolding of the literal concept from `(n, I)` to depth `k`: the node is
analyzed with `I`, and each callee with the caller's `OUT`. -/
def ctxLoop (p : Program) : Nat → Node → List Mark → List (Node × List Mark)
  | 0, n, I => [(n, I)]
  | k + 1, n, I => (n, I) :: (p.callees n).flatMap fun c => ctxLoop p k c (closure (reachSites p n) I)

/-- The `(node, IN)` pairs the literal concept visits from root `E` (depth
bounded by the number of nodes, which covers every simple call chain). -/
def conceptContexts (p : Program) (E : Node) : List (Node × List Mark) :=
  ctxLoop p p.nodes.length E []

/-- The `IN` the concept feeds to the last node of a call chain `E → c₁ → … `:
`feedIn p n I cs` starts at `n` with input `I`. -/
def feedIn (p : Program) : Node → List Mark → List Node → List Mark
  | _, I, [] => I
  | n, I, c :: cs => feedIn p c (closure (reachSites p n) I) cs

/-- `cs` is a call chain starting at a callee of `n`. -/
def IsChain (p : Program) : Node → List Node → Prop
  | _, [] => True
  | n, c :: cs => c ∈ p.callees n ∧ IsChain p c cs

namespace CollapseLemmas

theorem ctxLoop_inner {p : Program} {E : Node} (hwf : WF p) (hE : E ∈ p.nodes) :
    ∀ k n, Reaches p E n → ∀ x, x ∈ ctxLoop p k n (closure (reachSites p E) []) →
      Reaches p E x.1 ∧ x.2 = closure (reachSites p E) []
  | 0, n, hn, x, hx => by
    rw [List.mem_singleton.1 hx]; exact ⟨hn, rfl⟩
  | k + 1, n, hn, x, hx => by
    cases List.mem_cons.1 hx with
    | inl e => rw [e]; exact ⟨hn, rfl⟩
    | inr h =>
      obtain ⟨c, hc, hx'⟩ := List.mem_flatMap.1 h
      rw [collapse_context_tree_node hwf hE hn] at hx'
      exact ctxLoop_inner hwf hE k c (reaches_snoc hn hc) x hx'

theorem feedIn_inner {p : Program} {E : Node} (hwf : WF p) (hE : E ∈ p.nodes) :
    ∀ n cs, Reaches p E n → IsChain p n cs →
      feedIn p n (closure (reachSites p E) []) cs = closure (reachSites p E) []
  | _, [], _, _ => rfl
  | n, c :: cs, hn, ⟨hc, hcs⟩ => by
    simp only [feedIn]
    rw [collapse_context_tree_node hwf hE hn]
    exact feedIn_inner hwf hE c cs (reaches_snoc hn hc) hcs

end CollapseLemmas

/-- Every `(node, IN)` pair visited by the literal concept from root `E` is
either the root with `IN = []` or has `IN` equal (as a list) to `S_E`. So each
root induces at most two distinct contexts, instead of up to `2^|marks|` for a
table indexed by mark sets. -/
theorem conceptContexts_collapse {p : Program} {E : Node} (hwf : WF p) (hE : E ∈ p.roots) :
    ∀ x, x ∈ conceptContexts p E →
      (x.1 = E ∧ x.2 = []) ∨ (Reaches p E x.1 ∧ x.2 = closure (reachSites p E) []) := by
  intro x hx
  have hEn := hwf.1 E hE
  unfold conceptContexts at hx
  cases hlen : p.nodes.length with
  | zero => rw [List.length_eq_zero_iff.1 hlen] at hEn; cases hEn
  | succ k =>
    rw [hlen] at hx
    cases List.mem_cons.1 hx with
    | inl e => exact Or.inl (by rw [e]; exact ⟨rfl, rfl⟩)
    | inr h =>
      obtain ⟨c, hc, hx'⟩ := List.mem_flatMap.1 h
      exact Or.inr (ctxLoop_inner hwf hEn k c (Reaches.step hc (Reaches.refl c)) x hx')

/-- The distinct inputs used from root `E` are among `[]` and `S_E`. -/
theorem conceptContexts_inputs {p : Program} {E : Node} (hwf : WF p) (hE : E ∈ p.roots) :
    ∀ I, I ∈ (conceptContexts p E).map Prod.snd → I = [] ∨ I = closure (reachSites p E) [] := by
  intro I hI
  obtain ⟨x, hx, e⟩ := List.mem_map.1 hI
  subst e
  cases conceptContexts_collapse hwf hE x hx with
  | inl h => exact Or.inl h.2
  | inr h => exact Or.inr h.2

/-- Along every call chain `E → c₁ → … → cₖ` (k ≥ 1) from a root, the input
the concept feeds to `cₖ` is exactly `S_E`. -/
theorem feedIn_collapse {p : Program} {E c : Node} {cs : List Node} (hwf : WF p)
    (hE : E ∈ p.roots) (hch : IsChain p E (c :: cs)) :
    feedIn p E [] (c :: cs) = closure (reachSites p E) [] := by
  simp only [feedIn]
  exact feedIn_inner hwf (hwf.1 E hE) c cs (Reaches.step hch.1 (Reaches.refl c)) hch.2

/-! ## Sanity checks -/

section Examples

private def exSites : List Site :=
  [ { rule := 0, kind := .source, cond := [[]], gens := [1] },
    { rule := 1, kind := .passThrough, cond := [[1]], gens := [2] },
    { rule := 2, kind := .passThrough, cond := [[2, 3]], gens := [4] },
    { rule := 3, kind := .passThrough, cond := [[2]], gens := [3] } ]

example : closure exSites [] = [1, 2, 3, 4] := by decide

/-- Root `0` calls `1`; `1` and `2` call each other. Node `0` has a source of
mark `1`; node `2` turns mark `1` into mark `2`. -/
private def exProg : Program where
  nodes := [0, 1, 2]
  roots := [0]
  pcs := fun _ => [0]
  succ := fun _ _ => []
  exits := fun _ => [0]
  sites := fun n _ =>
    if n = 0 then [{ rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }]
    else if n = 2 then
      [{ rule := 1, kind := .passThrough, cond := [[⟨⟨0, 1⟩, false⟩]], assigns := [⟨0, 2⟩],
         copies := [] }]
    else []
  calls := fun n _ => if n = 0 then [1] else if n = 1 then [2] else [1]
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false

example : wfb exProg = true := by decide
example : reachList exProg 1 = [1, 2] := by decide
example : closure (reachSites exProg 0) [] = [1, 2] := by decide
example : closure (reachSites exProg 1) [] = [] := by decide
example : conceptContexts exProg 0 = [(0, []), (1, [1, 2]), (2, [1, 2]), (1, [1, 2])] := by decide

end Examples

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
