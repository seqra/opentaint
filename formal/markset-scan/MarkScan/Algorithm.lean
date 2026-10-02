import MarkScan.Basic

/-!
# Algorithms for the mark-set scan: reference and optimized

The declarative specification (`InS`, `Applicable`, `Needed` in `Basic`) is a
least fixpoint. This module gives two executable algorithms for it.

* **(A) The reference algorithm** favours clarity. `refSets` runs a global
  round-based fixpoint over all roots at once. In each round, every site at
  every node reachable from a root is evaluated again. `refInS`,
  `refApplicable` and `refNeeded` read the answers off the result, and
  `refInS_iff`, `refApplicable_iff` and `refNeeded_iff` prove that they are
  exactly the specification.
* **(B) The optimized algorithm** ("signature propagation") mirrors the planned
  Kotlin code. A site's *signature* is its abstract `(cond, gens)` pair. The
  single-literal part of a round is evaluated once per distinct signature
  reachable from a root, not once per statement. Joined cubes and sinks are
  evaluated once per node and signature, on the method-level union
  `U(method node)`, and their gens go to every root that reaches the node.
  `opt_eq_ref` and its corollaries prove that this computes the same answers,
  and in the same number of rounds. `closure_dedup` is the standalone form of
  the key fact: a closure over a list of sites equals the closure over its
  deduplicated signatures.
* **Unions suffice for applicability.** `applicable_iff_union` shows that, at a
  reachable node, `Applicable` only depends on the node-level union `U(n)` (for
  cubes of at most one literal) and the method-level union `U(method n)` (for
  joined cubes). `optApplicableU` is the corresponding executable check, and
  `optApplicableU_eq` proves it agrees with `optApplicable` on reachable nodes.
* **Cost.** `refSteps` and `optSteps` count cube evaluations. `optSteps_le`
  gives the general upper bound, and the family `famProg r k` (`k` statements
  with the same signature in one node, reached by `r` roots) shows the gap:
  `fam_speedup` proves `optSteps · k ≤ refSteps` for all `r, k`, and small
  instances are checked by `decide`.

The generic machinery (a fuelled "iterate until stable" loop, deduplication,
list-counting lemmas) lives in `MarkScan.AlgorithmLemmas`. Well-formedness and
reachability live in `MarkScan.Algorithm`, to avoid clashing with other
modules.
-/

namespace MarkScan

deriving instance DecidableEq for ESite

namespace AlgorithmLemmas

/-! ## Generic machinery -/

/-- Iterate `f` from `x` until `stab` holds, for at most `fuel` rounds. The
result is the final state and the number of rounds that applied `f`. -/
def iterC {α : Type} (f : α → α) (stab : α → Bool) : Nat → α → α × Nat
  | 0, x => (x, 0)
  | k + 1, x => if stab x then (x, 0) else
      let r := iterC f stab k (f x)
      (r.1, r.2 + 1)

theorem iterC_inv {α : Type} (f : α → α) (stab : α → Bool) (P : α → Prop)
    (hf : ∀ y, P y → P (f y)) : ∀ (n : Nat) (x : α), P x → P (iterC f stab n x).1
  | 0, _, hx => hx
  | n + 1, x, hx => by
    simp only [iterC]
    split
    · exact hx
    · exact iterC_inv f stab P hf n (f x) (hf x hx)

theorem iterC_rounds_le {α : Type} (f : α → α) (stab : α → Bool) :
    ∀ (n : Nat) (x : α), (iterC f stab n x).2 ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, x => by
    simp only [iterC]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (iterC_rounds_le f stab n (f x))

/-- If every non-final round strictly decreases a measure `μ`, then fuel
`> μ x` suffices: the loop stops because `stab` holds, not because it ran out
of fuel. -/
theorem iterC_stable {α : Type} (f : α → α) (stab : α → Bool) (P : α → Prop) (μ : α → Nat)
    (hf : ∀ y, P y → P (f y)) (hdec : ∀ y, P y → stab y = false → μ (f y) < μ y) :
    ∀ (n : Nat) (x : α), P x → μ x < n → stab (iterC f stab n x).1 = true
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, hlt => by
    simp only [iterC]
    cases hs : stab x with
    | true => simp [hs]
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact iterC_stable f stab P μ hf hdec n (f x) (hf x hx)
        (Nat.lt_of_lt_of_le (hdec x hx hs) (Nat.le_of_lt_succ hlt))

/-- The number of rounds that applied `f` is bounded by the initial measure. -/
theorem iterC_rounds_le_measure {α : Type} (f : α → α) (stab : α → Bool) (P : α → Prop)
    (μ : α → Nat) (hf : ∀ y, P y → P (f y)) (hdec : ∀ y, P y → stab y = false → μ (f y) < μ y) :
    ∀ (n : Nat) (x : α), P x → (iterC f stab n x).2 ≤ μ x
  | 0, _, _ => Nat.zero_le _
  | n + 1, x, hx => by
    simp only [iterC]
    cases hs : stab x with
    | true => exact Nat.zero_le _
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have := iterC_rounds_le_measure f stab P μ hf hdec n (f x) (hf x hx)
      have := hdec x hx hs
      omega

/-- Two loops run in lockstep on related states: if the stop tests agree on
related states and the steps preserve the relation, the results are related
and the round counts are equal. -/
theorem iterC_lockstep {α β : Type} (f : α → α) (g : β → β) (sf : α → Bool) (sg : β → Bool)
    (R : α → β → Prop) (hs : ∀ a b, R a b → sf a = sg b) (hst : ∀ a b, R a b → R (f a) (g b)) :
    ∀ (n : Nat) (x : α) (y : β), R x y →
      R (iterC f sf n x).1 (iterC g sg n y).1 ∧ (iterC f sf n x).2 = (iterC g sg n y).2
  | 0, _, _, h => ⟨h, rfl⟩
  | n + 1, x, y, h => by
    simp only [iterC]
    rw [hs x y h]
    split
    · exact ⟨h, rfl⟩
    · have ih := iterC_lockstep f g sf sg R hs hst n (f x) (g y) (hst x y h)
      exact ⟨ih.1, by rw [ih.2]⟩

/-- Add the elements of `xs` that are not yet in `acc`, in order. -/
def addNew {α : Type} [DecidableEq α] (acc xs : List α) : List α :=
  xs.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc

theorem mem_addNew {α : Type} [DecidableEq α] :
    ∀ (xs acc : List α) (x : α), x ∈ addNew acc xs ↔ x ∈ acc ∨ x ∈ xs
  | [], acc, x => by simp [addNew]
  | y :: ys, acc, x => by
    have ih := mem_addNew ys (if y ∈ acc then acc else acc ++ [y]) x
    simp only [addNew, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hy : y ∈ acc
    · simp only [hy, if_true, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl hy
        · exact Or.inr h
    · simp only [hy, if_false, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem nodup_addNew {α : Type} [DecidableEq α] :
    ∀ (xs acc : List α), acc.Nodup → (addNew acc xs).Nodup
  | [], _, h => h
  | y :: ys, acc, h => by
    simp only [addNew, List.foldl_cons]
    apply nodup_addNew ys
    by_cases hy : y ∈ acc
    · simp only [hy, if_true]; exact h
    · simp only [hy, if_false]
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb heq
      rw [List.mem_singleton] at hb
      subst hb; subst heq
      exact hy ha

/-- Deduplication, keeping first occurrences. -/
def dedup {α : Type} [DecidableEq α] (l : List α) : List α := addNew [] l

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (x : α) : x ∈ dedup l ↔ x ∈ l := by
  simp [dedup, mem_addNew]

theorem nodup_dedup {α : Type} [DecidableEq α] (l : List α) : (dedup l).Nodup :=
  nodup_addNew l [] List.nodup_nil

theorem filter_ne_length_lt {α : Type} [DecidableEq α] (a : α) :
    ∀ (m : List α), a ∈ m → (m.filter fun x => !decide (x = a)).length < m.length
  | [], h => absurd h List.not_mem_nil
  | b :: t, h => by
    simp only [List.filter_cons, List.length_cons]
    by_cases hb : b = a
    · subst hb
      simp only [decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · simp only [hb, decide_false, Bool.not_false, if_true, List.length_cons]
      have ht : a ∈ t := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hb
        · exact h
      exact Nat.succ_lt_succ (filter_ne_length_lt a t ht)

/-- A duplicate-free list that is contained in `m` is no longer than `m`
(constructive; the core lemma `List.Nodup.length_le_of_subset` uses
`Classical.choice`). -/
theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ (l m : List α), l.Nodup → (∀ x, x ∈ l → x ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, m, hn, hs => by
    have ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have ham : a ∈ m := hs a List.mem_cons_self
    have hsub : ∀ x, x ∈ t → x ∈ m.filter fun x => !decide (x = a) := by
      intro x hx
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      exact List.mem_filter.mpr ⟨hs x (List.mem_cons_of_mem a hx), by simp [hne]⟩
    have ih := length_le_of_nodup_subset t _ ht hsub
    have hlt := filter_ne_length_lt a m ham
    simp only [List.length_cons]
    omega

theorem length_dedup_le {α : Type} [DecidableEq α] (l : List α) : (dedup l).length ≤ l.length :=
  length_le_of_nodup_subset _ _ (nodup_dedup l) (fun x hx => (mem_dedup l x).mp hx)

theorem filter_length_le_mono {α : Type} (P Q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → Q x = true → P x = true) →
      (l.filter Q).length ≤ (l.filter P).length
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
    have ih := filter_length_le_mono P Q t (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hq : Q a <;> cases hp : P a <;> simp_all <;> omega

theorem filter_length_lt_mono {α : Type} (P Q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → Q x = true → P x = true) →
      (∃ x, x ∈ l ∧ P x = true ∧ Q x = false) →
      (l.filter Q).length < (l.filter P).length
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: t, h, ⟨x, hx, hpx, hqx⟩ => by
    have hle := filter_length_le_mono P Q t (fun y hy => h y (List.mem_cons_of_mem a hy))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · simp only [hpx, hqx]; simp; omega
    · have ih := filter_length_lt_mono P Q t (fun y hy => h y (List.mem_cons_of_mem a hy))
        ⟨x, hxt, hpx, hqx⟩
      cases hq : Q a <;> cases hp : P a <;> simp_all <;> omega

theorem sum_map_le {α : Type} (f g : α → Nat) :
    ∀ (l : List α), (∀ x, x ∈ l → f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
    have ih := sum_map_le f g t (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_lt {α : Type} (f g : α → Nat) :
    ∀ (l : List α), (∀ x, x ∈ l → f x ≤ g x) → (∃ x, x ∈ l ∧ f x < g x) →
      (l.map f).sum < (l.map g).sum
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: t, h, ⟨x, hx, hlt⟩ => by
    have hle := sum_map_le f g t (fun y hy => h y (List.mem_cons_of_mem a hy))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · omega
    · have ih := sum_map_lt f g t (fun y hy => h y (List.mem_cons_of_mem a hy)) ⟨x, hxt, hlt⟩
      omega

theorem sum_map_le_mul {α : Type} (f : α → Nat) (B : Nat) :
    ∀ (l : List α), (∀ x, x ∈ l → f x ≤ B) → (l.map f).sum ≤ l.length * B
  | [], _ => by simp
  | a :: t, h => by
    have ih := sum_map_le_mul f B t (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem all_false_wit {α : Type} {q : α → Bool} :
    ∀ {l : List α}, l.all q = false → ∃ x, x ∈ l ∧ q x = false
  | [], h => by simp at h
  | a :: t, h => by
    cases ha : q a with
    | false => exact ⟨a, List.mem_cons_self, ha⟩
    | true =>
      simp only [List.all_cons, ha, Bool.true_and] at h
      obtain ⟨x, hx, hq⟩ := all_false_wit h
      exact ⟨x, List.mem_cons_of_mem a hx, hq⟩

theorem contains_iff {l : List Nat} {m : Nat} : l.contains m = true ↔ m ∈ l := by simp

theorem not_contains_iff {l : List Nat} {m : Nat} : (!l.contains m) = true ↔ m ∉ l := by simp

theorem not_contains_false {l : List Nat} {m : Nat} : (!l.contains m) = false ↔ m ∈ l := by simp

end AlgorithmLemmas

open AlgorithmLemmas

/-! ## Well-formedness and reachability -/

namespace Algorithm

/-- Well-formed programs: roots are nodes, the node set is closed under
calls, every site sits at a listed node and at a statement listed in `pcs`,
and so does every recorded cleaner atom. The last two let the algorithm
enumerate all sites and cleaner atoms: in v2 a joined cube of a node that no
root reaches can still be satisfied (via another context of its method), and
`Needed.cleanerAtom` is unconditional. -/
structure WF (p : Program) : Prop where
  roots_sub : ∀ r, r ∈ p.roots → r ∈ p.nodes
  callees_sub : ∀ n, n ∈ p.nodes → ∀ c, c ∈ p.callees n → c ∈ p.nodes
  sites_pc : ∀ n pc σ, n ∈ p.nodes → σ ∈ p.sites n pc → pc ∈ p.pcs n
  sites_node : ∀ n pc σ, σ ∈ p.sites n pc → n ∈ p.nodes
  cleaner_sub : ∀ n pc m, m ∈ p.cleanerAtoms n pc → n ∈ p.nodes ∧ pc ∈ p.pcs n

theorem Reaches.tail {p : Program} {a b c : Node} (h : Reaches p a b) (hc : c ∈ p.callees b) :
    Reaches p a c := by
  induction h with
  | refl n => exact Reaches.step hc (Reaches.refl c)
  | step hab _ ih => exact Reaches.step hab (ih hc)

theorem Reaches.nodes {p : Program} (hw : WF p) {a b : Node} (h : Reaches p a b)
    (ha : a ∈ p.nodes) : b ∈ p.nodes := by
  induction h with
  | refl _ => exact ha
  | step hab _ ih => exact ih (hw.callees_sub _ ha _ hab)

def reachStep (p : Program) (R : List Node) : List Node := addNew R (R.flatMap p.callees)

def reachStable (p : Program) (R : List Node) : Bool := (R.flatMap p.callees).all R.contains

/-- The nodes reachable from `n` (including `n`), by saturation. -/
def reachList (p : Program) (n : Node) : List Node :=
  (iterC (reachStep p) (reachStable p) (p.nodes.length + 1) [n]).1

theorem mem_reachStep {p : Program} {R : List Node} {x : Node} :
    x ∈ reachStep p R ↔ x ∈ R ∨ ∃ a, a ∈ R ∧ x ∈ p.callees a := by
  simp [reachStep, mem_addNew, List.mem_flatMap]

/-- Soundness of `reachList` needs no well-formedness. -/
theorem reachList_reaches (p : Program) (n k : Node) (h : k ∈ reachList p n) : Reaches p n k := by
  have := iterC_inv (reachStep p) (reachStable p) (fun R => ∀ x, x ∈ R → Reaches p n x)
    (by
      intro R hR x hx
      rcases mem_reachStep.mp hx with h | ⟨a, ha, hxa⟩
      · exact hR x h
      · exact Reaches.tail (hR a ha) hxa)
    (p.nodes.length + 1) [n]
    (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact Reaches.refl _)
  exact this k h

theorem reachList_closed (p : Program) (hw : WF p) (n : Node) (hn : n ∈ p.nodes) :
    n ∈ reachList p n ∧ ∀ a, a ∈ reachList p n → ∀ c, c ∈ p.callees a → c ∈ reachList p n := by
  let P : List Node → Prop := fun R => n ∈ R ∧ ∀ x, x ∈ R → x ∈ p.nodes
  have hf : ∀ R, P R → P (reachStep p R) := by
    intro R ⟨hnR, hRn⟩
    refine ⟨mem_reachStep.mpr (Or.inl hnR), ?_⟩
    intro x hx
    rcases mem_reachStep.mp hx with h | ⟨a, ha, hxa⟩
    · exact hRn x h
    · exact hw.callees_sub a (hRn a ha) x hxa
  have h0 : P [n] := ⟨List.mem_singleton_self n, by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hn⟩
  have hinv := iterC_inv (reachStep p) (reachStable p) P hf (p.nodes.length + 1) [n] h0
  have hstab := iterC_stable (reachStep p) (reachStable p) P
    (fun R => (p.nodes.filter fun x => !R.contains x).length) hf
    (by
      intro R ⟨_, hRn⟩ hs
      obtain ⟨y, hy, hyR⟩ := all_false_wit hs
      obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
      apply filter_length_lt_mono
      · intro x _ hx
        rw [not_contains_iff] at hx ⊢
        exact fun h => hx (mem_reachStep.mpr (Or.inl h))
      · refine ⟨y, hw.callees_sub a (hRn a ha) y hya, ?_, ?_⟩
        · rw [not_contains_iff]; intro h; rw [contains_iff.mpr h] at hyR; exact Bool.noConfusion hyR
        · rw [not_contains_false]; exact mem_reachStep.mpr (Or.inr ⟨a, ha, hya⟩))
    (p.nodes.length + 1) [n] h0 (Nat.lt_succ_of_le (List.length_filter_le _ _))
  refine ⟨hinv.1, ?_⟩
  intro a ha c hc
  simp only [reachStable, List.all_eq_true, List.mem_flatMap] at hstab
  exact contains_iff.mp (hstab c ⟨a, ha, hc⟩)

/-- `reachList` computes exactly the call-graph reachability of `Basic`. -/
theorem mem_reachList (p : Program) (hw : WF p) (n k : Node) (hn : n ∈ p.nodes) :
    k ∈ reachList p n ↔ Reaches p n k := by
  constructor
  · exact reachList_reaches p n k
  · intro h
    have ⟨h0, hcl⟩ := reachList_closed p hw n hn
    suffices ∀ a b, Reaches p a b → a ∈ reachList p n → b ∈ reachList p n from this n k h h0
    intro a b hab
    induction hab with
    | refl _ => exact id
    | step hab' _ ih => exact fun ha => ih (hcl _ ha _ hab')

theorem mem_nodeSites {p : Program} {n : Node} {pc : Pc} {σ : ESite} :
    (pc, σ) ∈ p.nodeSites n ↔ pc ∈ p.pcs n ∧ σ ∈ p.sites n pc := by
  simp [Program.nodeSites, List.mem_flatMap]

end Algorithm

open Algorithm

namespace AlgorithmLemmas

theorem find_witness {α : Type} {l : List α} {q : α → Bool} (d : α)
    (h : ∃ x, x ∈ l ∧ q x = true) :
    (l.find? q).getD d ∈ l ∧ q ((l.find? q).getD d) = true := by
  cases hf : l.find? q with
  | none =>
    obtain ⟨x, hx, hq⟩ := h
    exact absurd hq (List.find?_eq_none.mp hf x hx)
  | some a => exact ⟨List.mem_of_find?_eq_some hf, List.find?_some hf⟩

theorem lookup_map_self (F : Node → List Mark) :
    ∀ (l : List Node) (E : Node), E ∈ l → (l.map fun x => (x, F x)).lookup E = some (F E)
  | [], _, h => absurd h List.not_mem_nil
  | a :: t, E, h => by
    simp only [List.map_cons, List.lookup_cons]
    cases hb : E == a with
    | true => rw [beq_iff_eq] at hb; subst hb; rfl
    | false =>
      have hne : E ≠ a := fun h' => by rw [h', beq_iff_eq.mpr rfl] at hb; exact Bool.noConfusion hb
      exact lookup_map_self F t E ((List.mem_cons.mp h).resolve_left hne)

end AlgorithmLemmas

/-! ## (A) The reference algorithm

A state assigns a mark set to every node; only the entries of roots matter. -/

/-- `U(k)`: the node-level union of the sets of the roots that reach `k`. -/
def refU (p : Program) (S : Node → List Mark) (k : Node) : List Mark :=
  p.roots.flatMap fun E => if k ∈ reachList p E then S E else []

/-- The pairs `(E, n')` of a root and a node it reaches. -/
def rootPairs (p : Program) : List (Node × Node) :=
  p.roots.flatMap fun E => (reachList p E).map fun n' => (E, n')

/-- `U(method k)`: the method-level union of the sets of the roots that reach
some node of the same method as `k`. -/
def refUM (p : Program) (S : Node → List Mark) (k : Node) : List Mark :=
  (rootPairs p).flatMap fun q => if p.method q.2 = p.method k then S q.1 else []

/-- The executable witness for `m ∈ U(method k)`: the first pair `(E, n')` of
`rootPairs` with `method n' = method k` and `m ∈ S E`. -/
def umWit (p : Program) (S : Node → List Mark) (k : Node) (m : Mark) : Node × Node :=
  ((rootPairs p).find? fun q => decide (p.method q.2 = p.method k) && decide (m ∈ S q.1)).getD (0, 0)

/-- Evaluate cube `c` of a non-sink site at node `k`, for root `E`. A cube of
at most one literal is read on `S E`, a joined cube on `U(method k)`. -/
def refCubeOk (p : Program) (S : Node → List Mark) (E k : Node) (c : Cube) : Bool :=
  if c.length ≤ 1 then c.all (fun m => decide (m ∈ S E))
  else c.all (fun m => decide (m ∈ refUM p S k))

/-- Whether the site `σ` at node `k` contributes its gens to root `E`. A sink's
gens are zero-context facts (`InS.sinkGen`): some cube must hold on
`U(method k)`. A single-literal cube on `S E` implies this, so one evaluation
per cube suffices for a sink too. Other sites use `refCubeOk`. -/
def refSiteOk (p : Program) (S : Node → List Mark) (E k : Node) (σ : ESite) : Bool :=
  if σ.kind = .sink then σ.abstract.cond.any fun c => c.all fun m => decide (m ∈ refUM p S k)
  else σ.abstract.cond.any (refCubeOk p S E k)

/-- The marks generated for root `E` in one round: the gens of every site at
every node reachable from `E` that is satisfied (`refSiteOk`). -/
def refGens (p : Program) (S : Node → List Mark) (E : Node) : List Mark :=
  (reachList p E).flatMap fun k => (p.nodeSites k).flatMap fun ps =>
    if refSiteOk p S E k ps.2 then ps.2.abstract.gens else []

def refRound (p : Program) (S : Node → List Mark) : Node → List Mark :=
  fun E => addNew (S E) (refGens p S E)

def refStable (p : Program) (S : Node → List Mark) : Bool :=
  p.roots.all fun E => (refGens p S E).all fun g => decide (g ∈ S E)

/-- The distinct gens of all sites in the program. -/
def refUniverse (p : Program) : List Mark :=
  dedup (p.nodes.flatMap fun k => (p.nodeSites k).flatMap fun ps => ps.2.abstract.gens)

/-- Fuel: `|roots| · |distinct gens| + 1`. `refFuel_suffices` proves it is
enough. -/
def refFuel (p : Program) : Nat := p.roots.length * (refUniverse p).length + 1

/-- Missing (root, gen) pairs. Every non-final round strictly decreases it. -/
def refMeasure (p : Program) (S : Node → List Mark) : Nat :=
  (p.roots.map fun E => ((refUniverse p).filter fun g => !decide (g ∈ S E)).length).sum

def refIter (p : Program) : (Node → List Mark) × Nat :=
  iterC (refRound p) (refStable p) (refFuel p) (fun _ => [])

def refFinal (p : Program) : Node → List Mark := (refIter p).1

/-- Rounds that added something (the final, confirming round is not counted). -/
def refRounds (p : Program) : Nat := (refIter p).2

/-- The reference result: the mark set of each root. -/
def refSets (p : Program) : List (Node × List Mark) :=
  p.roots.map fun E => (E, refFinal p E)

def refInS (p : Program) (E : Node) (m : Mark) : Bool :=
  decide (m ∈ ((refSets p).lookup E).getD [])

/-- Executable `CubeSat` on a state. -/
def refCubeSat (p : Program) (F : Node → List Mark) (n : Node) (c : Cube) : Bool :=
  if c.length ≤ 1 then
    p.roots.any fun E => decide (n ∈ reachList p E) && c.all (fun m => decide (m ∈ F E))
  else c.all (fun m => decide (m ∈ refUM p F n))

def applicableOn (p : Program) (F : Node → List Mark) (n : Node) (pc : Pc) (σ : ESite) : Bool :=
  decide (σ ∈ p.sites n pc) && σ.abstract.cond.any (refCubeSat p F n)

def refApplicable (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Bool :=
  applicableOn p (refFinal p) n pc σ

/-- The sites selected by `app`. -/
def appSites (p : Program) (app : Node → Pc → ESite → Bool) : List ESite :=
  p.nodes.flatMap fun n => ((p.nodeSites n).filter fun ps => app n ps.1 ps.2).map (·.2)

/-- Seeds contributed by the selected sites: the atoms and gens of sinks, and
the atoms of pass-throughs. -/
def needSeeds (A : List ESite) : List Mark :=
  A.flatMap fun σ =>
    if σ.kind = .sink then σ.abstract.cond.atoms ++ σ.abstract.gens
    else if σ.kind = .passThrough then σ.abstract.cond.atoms else []

/-- Every recorded cleaner atom, over the listed nodes and their statements
(`WF.cleaner_sub` makes this exhaustive). -/
def cleanerSeeds (p : Program) : List Mark :=
  p.nodes.flatMap fun n => (p.pcs n).flatMap (p.cleanerAtoms n)

def needGens (A : List ESite) (N : List Mark) : List Mark :=
  A.flatMap fun σ => if σ.abstract.gens.any (fun g => decide (g ∈ N)) then σ.abstract.cond.atoms else []

def needStep (A : List ESite) (N : List Mark) : List Mark := addNew N (needGens A N)

def needStable (A : List ESite) (N : List Mark) : Bool := (needGens A N).all fun m => decide (m ∈ N)

def needUniverse (A : List ESite) : List Mark :=
  dedup (needSeeds A ++ A.flatMap fun σ => σ.abstract.cond.atoms)

/-- The backward relevance pass over the sites `A`, with the extra seeds `C`. -/
def neededSet (A : List ESite) (C : List Mark) : List Mark :=
  (iterC (needStep A) (needStable A) ((needUniverse A).length + 1) (needSeeds A ++ C)).1

def refNeeded (p : Program) (m : Mark) : Bool :=
  decide (m ∈ neededSet (appSites p (refApplicable p)) (cleanerSeeds p))

/-! ### Correctness of the reference algorithm -/

namespace AlgorithmLemmas

theorem mem_refU {p : Program} {S : Node → List Mark} {k : Node} {m : Mark} :
    m ∈ refU p S k ↔ ∃ E, E ∈ p.roots ∧ k ∈ reachList p E ∧ m ∈ S E := by
  simp only [refU, List.mem_flatMap]
  constructor
  · rintro ⟨E, hE, hm⟩
    by_cases hk : k ∈ reachList p E
    · simp only [hk, if_true] at hm; exact ⟨E, hE, hk, hm⟩
    · simp [hk] at hm
  · rintro ⟨E, hE, hk, hm⟩
    exact ⟨E, hE, by simp only [hk, if_true]; exact hm⟩

theorem mem_rootPairs {p : Program} {q : Node × Node} :
    q ∈ rootPairs p ↔ q.1 ∈ p.roots ∧ q.2 ∈ reachList p q.1 := by
  obtain ⟨E, n'⟩ := q
  simp only [rootPairs, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨E', hE', n'', hn'', rfl, rfl⟩; exact ⟨hE', hn''⟩
  · rintro ⟨hE, hn'⟩; exact ⟨E, hE, n', hn', rfl, rfl⟩

theorem mem_refUM {p : Program} {S : Node → List Mark} {k : Node} {m : Mark} :
    m ∈ refUM p S k ↔
      ∃ E n', E ∈ p.roots ∧ n' ∈ reachList p E ∧ p.method n' = p.method k ∧ m ∈ S E := by
  simp only [refUM, List.mem_flatMap]
  constructor
  · rintro ⟨⟨E, n'⟩, hq, hm⟩
    obtain ⟨hE, hn'⟩ := mem_rootPairs.mp hq
    by_cases hmeth : p.method n' = p.method k
    · simp only [hmeth, if_true] at hm; exact ⟨E, n', hE, hn', hmeth, hm⟩
    · simp [hmeth] at hm
  · rintro ⟨E, n', hE, hn', hmeth, hm⟩
    exact ⟨(E, n'), mem_rootPairs.mpr ⟨hE, hn'⟩, by simp only [hmeth, if_true]; exact hm⟩

/-- The executable witness `umWit` is correct. -/
theorem umWit_spec {p : Program} {S : Node → List Mark} {k : Node} {m : Mark}
    (h : m ∈ refUM p S k) :
    (umWit p S k m).1 ∈ p.roots ∧ (umWit p S k m).2 ∈ reachList p (umWit p S k m).1 ∧
      p.method (umWit p S k m).2 = p.method k ∧ m ∈ S (umWit p S k m).1 := by
  obtain ⟨E, n', hE, hn', hmeth, hm⟩ := mem_refUM.mp h
  have hw := find_witness (l := rootPairs p)
    (q := fun q => decide (p.method q.2 = p.method k) && decide (m ∈ S q.1)) (0, 0)
    ⟨(E, n'), mem_rootPairs.mpr ⟨hE, hn'⟩, by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨hmeth, hm⟩⟩
  obtain ⟨h1, h2⟩ := hw
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
  have h1' := mem_rootPairs.mp h1
  exact ⟨h1'.1, h1'.2, h2.1, h2.2⟩

theorem refCubeOk_iff {p : Program} {S : Node → List Mark} {E k : Node} {c : Cube} :
    refCubeOk p S E k c = true ↔
      (c.length ≤ 1 ∧ ∀ m, m ∈ c → m ∈ S E) ∨
        (2 ≤ c.length ∧ ∀ m, m ∈ c → m ∈ refUM p S k) := by
  unfold refCubeOk
  by_cases hl : c.length ≤ 1
  · simp only [hl, if_true, List.all_eq_true, decide_eq_true_eq, true_and]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h, _⟩)
      · exact h
      · omega
  · simp only [hl, if_false, List.all_eq_true, decide_eq_true_eq, false_and, false_or]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · exact fun h => h.2

theorem refSiteOk_iff {p : Program} {S : Node → List Mark} {E k : Node} {σ : ESite} :
    refSiteOk p S E k σ = true ↔
      (σ.kind = .sink ∧ ∃ c, c ∈ σ.abstract.cond ∧ ∀ m, m ∈ c → m ∈ refUM p S k) ∨
      (σ.kind ≠ .sink ∧ ∃ c, c ∈ σ.abstract.cond ∧ refCubeOk p S E k c = true) := by
  unfold refSiteOk
  by_cases hk : σ.kind = .sink
  · rw [if_pos hk, List.any_eq_true]
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h; exact Or.inl ⟨hk, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd hk h
  · rw [if_neg hk, List.any_eq_true]
    constructor
    · intro h; exact Or.inr ⟨hk, h⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h hk
      · exact h

/-- A cube contained in `U(method k)` makes a sink, or a site through a joined
cube, contribute. -/
theorem refSiteOk_of_union {p : Program} {S : Node → List Mark} {E k : Node} {σ : ESite}
    {c : Cube} (hc : c ∈ σ.abstract.cond) (hU : ∀ m, m ∈ c → m ∈ refUM p S k)
    (h : σ.kind = .sink ∨ 2 ≤ c.length) : refSiteOk p S E k σ = true := by
  apply refSiteOk_iff.mpr
  by_cases hk : σ.kind = .sink
  · exact Or.inl ⟨hk, c, hc, hU⟩
  · have hl : 2 ≤ c.length := h.resolve_left hk
    exact Or.inr ⟨hk, c, hc, refCubeOk_iff.mpr (Or.inr ⟨hl, hU⟩)⟩

/-- A cube of at most one literal contained in `S E`, for a root `E` that
reaches `k`, makes any site contribute. -/
theorem refSiteOk_of_single {p : Program} {S : Node → List Mark} {E k : Node} {σ : ESite}
    {c : Cube} (hc : c ∈ σ.abstract.cond) (hl : c.length ≤ 1) (hE : E ∈ p.roots)
    (hk : k ∈ reachList p E) (hS : ∀ m, m ∈ c → m ∈ S E) : refSiteOk p S E k σ = true := by
  apply refSiteOk_iff.mpr
  by_cases hkind : σ.kind = .sink
  · exact Or.inl ⟨hkind, c, hc, fun m hm => mem_refUM.mpr ⟨E, k, hE, hk, rfl, hS m hm⟩⟩
  · exact Or.inr ⟨hkind, c, hc, refCubeOk_iff.mpr (Or.inl ⟨hl, hS⟩)⟩

theorem mem_refGens {p : Program} {S : Node → List Mark} {E : Node} {g : Mark} :
    g ∈ refGens p S E ↔ ∃ k, k ∈ reachList p E ∧ ∃ pc σ, (pc, σ) ∈ p.nodeSites k ∧
      refSiteOk p S E k σ = true ∧ g ∈ σ.abstract.gens := by
  simp only [refGens, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, ⟨pc, σ⟩, hps, hg⟩
    by_cases hf : refSiteOk p S E k σ = true
    · simp only [hf, if_true] at hg
      exact ⟨k, hk, pc, σ, hps, hf, hg⟩
    · simp [hf] at hg
  · rintro ⟨k, hk, pc, σ, hps, hf, hg⟩
    exact ⟨k, hk, (pc, σ), hps, by simp only [hf, if_true]; exact hg⟩

theorem mem_refRound {p : Program} {S : Node → List Mark} {E : Node} {m : Mark} :
    m ∈ refRound p S E ↔ m ∈ S E ∨ m ∈ refGens p S E := by
  simp [refRound, mem_addNew]

theorem refStable_iff {p : Program} {S : Node → List Mark} :
    refStable p S = true ↔ ∀ E, E ∈ p.roots → ∀ g, g ∈ refGens p S E → g ∈ S E := by
  simp [refStable, List.all_eq_true]

theorem refGens_universe {p : Program} (hw : WF p) {S : Node → List Mark} {E : Node}
    (hE : E ∈ p.roots) {g : Mark} (hg : g ∈ refGens p S E) : g ∈ refUniverse p := by
  obtain ⟨k, hk, pc, σ, hps, _, hg⟩ := mem_refGens.mp hg
  have hkn : k ∈ p.nodes :=
    Reaches.nodes hw (reachList_reaches p E k hk) (hw.roots_sub E hE)
  rw [refUniverse, mem_dedup, List.mem_flatMap]
  exact ⟨k, hkn, List.mem_flatMap.mpr ⟨(pc, σ), hps, hg⟩⟩

/-- Every non-final round strictly grows the total (the measure drops). -/
theorem refMeasure_dec (p : Program) (hw : WF p) (S : Node → List Mark)
    (hs : refStable p S = false) : refMeasure p (refRound p S) < refMeasure p S := by
  obtain ⟨E, hE, hE'⟩ := all_false_wit hs
  obtain ⟨g, hg, hgS⟩ := all_false_wit hE'
  have hgS' : g ∉ S E := of_decide_eq_false hgS
  have hmono : ∀ E', ∀ x, x ∈ refUniverse p →
      (!decide (x ∈ refRound p S E')) = true → (!decide (x ∈ S E')) = true := by
    intro E' x _ hx
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hx ⊢
    exact fun h => hx (mem_refRound.mpr (Or.inl h))
  unfold refMeasure
  apply sum_map_lt
  · intro E' _
    exact filter_length_le_mono _ _ _ (hmono E')
  · refine ⟨E, hE, filter_length_lt_mono _ _ _ (hmono E) ⟨g, refGens_universe hw hE hg, ?_, ?_⟩⟩
    · rw [Bool.not_eq_true', decide_eq_false_iff_not]; exact hgS'
    · rw [Bool.not_eq_false', decide_eq_true_eq]; exact mem_refRound.mpr (Or.inr hg)

/-- The fuel `refFuel` suffices: the loop ends at a stable state. -/
theorem refFinal_stable (p : Program) (hw : WF p) : refStable p (refFinal p) = true :=
  iterC_stable (refRound p) (refStable p) (fun _ => True) (refMeasure p) (fun _ _ => trivial)
    (fun y _ hs => refMeasure_dec p hw y hs) (refFuel p) _ trivial
    (Nat.lt_succ_of_le (sum_map_le_mul _ _ _ (fun _ _ => List.length_filter_le _ _)))

theorem refGens_sound (p : Program) (S : Node → List Mark)
    (hS : ∀ E, E ∈ p.roots → ∀ m, m ∈ S E → InS p E m) {E : Node} (hE : E ∈ p.roots)
    {g : Mark} (hg : g ∈ refGens p S E) : InS p E g := by
  obtain ⟨k, hk, pc, σ, hps, hok, hg⟩ := mem_refGens.mp hg
  have hR := reachList_reaches p E k hk
  -- the executable witnesses of the method-level union
  let w : Mark → Node := fun m => (umWit p S k m).1
  let wn : Mark → Node := fun m => (umWit p S k m).2
  rcases refSiteOk_iff.mp hok with ⟨hkind, c, hc, hall⟩ | ⟨_, c, hc, hc'⟩
  · exact InS.sinkGen hE hR hps hkind hc w wn
      (fun m hm => (umWit_spec (hall m hm)).1)
      (fun m hm => reachList_reaches p _ _ (umWit_spec (hall m hm)).2.1)
      (fun m hm => (umWit_spec (hall m hm)).2.2.1)
      (fun m hm => hS _ (umWit_spec (hall m hm)).1 m (umWit_spec (hall m hm)).2.2.2) hg
  · rcases refCubeOk_iff.mp hc' with ⟨hl, hall⟩ | ⟨hl, hall⟩
    · exact InS.single hE hR hps hc hl (fun m hm => hS E hE m (hall m hm)) hg
    · exact InS.joined hE hR hps hc hl w wn
        (fun m hm => (umWit_spec (hall m hm)).1)
        (fun m hm => reachList_reaches p _ _ (umWit_spec (hall m hm)).2.1)
        (fun m hm => (umWit_spec (hall m hm)).2.2.1)
        (fun m hm => hS _ (umWit_spec (hall m hm)).1 m (umWit_spec (hall m hm)).2.2.2) hg

/-- Soundness of the reference sets (no well-formedness needed). -/
theorem refFinal_sound (p : Program) :
    ∀ E, E ∈ p.roots → ∀ m, m ∈ refFinal p E → InS p E m :=
  iterC_inv (refRound p) (refStable p) (fun S => ∀ E, E ∈ p.roots → ∀ m, m ∈ S E → InS p E m)
    (by
      intro S hS E hE m hm
      rcases mem_refRound.mp hm with h | h
      · exact hS E hE m h
      · exact refGens_sound p S hS hE h)
    (refFuel p) _ (fun _ _ _ h => absurd h List.not_mem_nil)

/-- Completeness: a stable state contains every `InS` mark. -/
theorem refFinal_complete (p : Program) (hw : WF p) {E : Node} {m : Mark} (h : InS p E m) :
    m ∈ refFinal p E := by
  have hst := refStable_iff.mp (refFinal_stable p hw)
  have hre : ∀ E x, E ∈ p.roots → Reaches p E x → x ∈ reachList p E :=
    fun E x hE hR => (mem_reachList p hw _ _ (hw.roots_sub _ hE)).mpr hR
  induction h with
  | @single E n pc σ c g hE hR hps hc hl _ hg ih =>
    exact hst _ hE _ (mem_refGens.mpr ⟨n, hre E n hE hR, pc, σ, hps,
      refSiteOk_of_single hc hl hE (hre E n hE hR) ih, hg⟩)
  | @joined E n pc σ c g hE hR hps hc hl w wn hwr hwR hwm _ hg ih =>
    exact hst _ hE _ (mem_refGens.mpr ⟨n, hre E n hE hR, pc, σ, hps,
      refSiteOk_of_union hc (fun m hm => mem_refUM.mpr ⟨w m, wn m, hwr m hm,
        hre _ _ (hwr m hm) (hwR m hm), hwm m hm, ih m hm⟩) (Or.inr hl), hg⟩)
  | @sinkGen E n pc σ c g hE hR hps hkind hc w wn hwr hwR hwm _ hg ih =>
    exact hst _ hE _ (mem_refGens.mpr ⟨n, hre E n hE hR, pc, σ, hps,
      refSiteOk_of_union hc (fun m hm => mem_refUM.mpr ⟨w m, wn m, hwr m hm,
        hre _ _ (hwr m hm) (hwR m hm), hwm m hm, ih m hm⟩) (Or.inl hkind), hg⟩)

theorem refFinal_iff (p : Program) (hw : WF p) {E : Node} (hE : E ∈ p.roots) (m : Mark) :
    m ∈ refFinal p E ↔ InS p E m :=
  ⟨refFinal_sound p E hE m, refFinal_complete p hw⟩

theorem refCubeSat_iff (p : Program) (hw : WF p) (F : Node → List Mark)
    (hF : ∀ E, E ∈ p.roots → ∀ m, m ∈ F E ↔ InS p E m) (n : Node) (c : Cube) :
    refCubeSat p F n c = true ↔ CubeSat p n c := by
  have hre : ∀ E x, E ∈ p.roots → (x ∈ reachList p E ↔ Reaches p E x) :=
    fun E x hE => mem_reachList p hw E x (hw.roots_sub E hE)
  unfold refCubeSat CubeSat
  by_cases hl : c.length ≤ 1
  · simp only [hl, if_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, true_and]
    constructor
    · rintro ⟨E, hE, hn, hall⟩
      exact Or.inl ⟨E, hE, (hre E n hE).mp hn, fun m hm => (hF E hE m).mp (hall m hm)⟩
    · rintro (⟨E, hE, hn, hall⟩ | ⟨h2, _⟩)
      · exact ⟨E, hE, (hre E n hE).mpr hn, fun m hm => (hF E hE m).mpr (hall m hm)⟩
      · omega
  · simp only [hl, if_false, List.all_eq_true, decide_eq_true_eq, false_and, false_or]
    constructor
    · intro hall
      refine ⟨by omega, fun m hm => ?_⟩
      obtain ⟨E, n', hE, hn', hmeth, hmE⟩ := mem_refUM.mp (hall m hm)
      exact ⟨E, n', hE, (hre E n' hE).mp hn', hmeth, (hF E hE m).mp hmE⟩
    · intro ⟨_, hall⟩ m hm
      obtain ⟨E, n', hE, hn', hmeth, hmE⟩ := hall m hm
      exact mem_refUM.mpr ⟨E, n', hE, (hre E n' hE).mpr hn', hmeth, (hF E hE m).mpr hmE⟩

theorem applicableOn_iff (p : Program) (hw : WF p) (F : Node → List Mark)
    (hF : ∀ E, E ∈ p.roots → ∀ m, m ∈ F E ↔ InS p E m) (n : Node) (pc : Pc) (σ : ESite) :
    applicableOn p F n pc σ = true ↔ Applicable p n pc σ := by
  unfold applicableOn Applicable
  rw [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨h1, c, hc, h2⟩
    exact ⟨h1, c, hc, (refCubeSat_iff p hw F hF n c).mp h2⟩
  · rintro ⟨h1, c, hc, h2⟩
    exact ⟨h1, c, hc, (refCubeSat_iff p hw F hF n c).mpr h2⟩

theorem mem_appSites {p : Program} {app : Node → Pc → ESite → Bool} {σ : ESite} :
    σ ∈ appSites p app ↔
      ∃ n, n ∈ p.nodes ∧ ∃ pc, (pc, σ) ∈ p.nodeSites n ∧ app n pc σ = true := by
  simp only [appSites, List.mem_flatMap, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨n, hn, ⟨pc, σ'⟩, ⟨hps, happ⟩, rfl⟩
    exact ⟨n, hn, pc, hps, happ⟩
  · rintro ⟨n, hn, pc, hps, happ⟩
    exact ⟨n, hn, (pc, σ), ⟨hps, happ⟩, rfl⟩

theorem mem_needSeeds {A : List ESite} {m : Mark} :
    m ∈ needSeeds A ↔ ∃ σ, σ ∈ A ∧
      ((σ.kind = .sink ∧ (m ∈ σ.abstract.cond.atoms ∨ m ∈ σ.abstract.gens)) ∨
        (σ.kind = .passThrough ∧ m ∈ σ.abstract.cond.atoms)) := by
  simp only [needSeeds, List.mem_flatMap]
  constructor
  · rintro ⟨σ, hσ, hm⟩
    by_cases hk : σ.kind = .sink
    · rw [if_pos hk, List.mem_append] at hm; exact ⟨σ, hσ, Or.inl ⟨hk, hm⟩⟩
    · rw [if_neg hk] at hm
      by_cases hp : σ.kind = .passThrough
      · rw [if_pos hp] at hm; exact ⟨σ, hσ, Or.inr ⟨hp, hm⟩⟩
      · rw [if_neg hp] at hm; exact absurd hm List.not_mem_nil
  · rintro ⟨σ, hσ, ⟨hk, hm⟩ | ⟨hp, hm⟩⟩
    · exact ⟨σ, hσ, by rw [if_pos hk, List.mem_append]; exact hm⟩
    · have hk : σ.kind ≠ .sink := by rw [hp]; exact fun h => Kind.noConfusion h
      exact ⟨σ, hσ, by rw [if_neg hk, if_pos hp]; exact hm⟩

theorem mem_cleanerSeeds {p : Program} (hw : WF p) {m : Mark} :
    m ∈ cleanerSeeds p ↔ ∃ n pc, m ∈ p.cleanerAtoms n pc := by
  simp only [cleanerSeeds, List.mem_flatMap]
  constructor
  · rintro ⟨n, _, pc, _, hm⟩; exact ⟨n, pc, hm⟩
  · rintro ⟨n, pc, hm⟩
    have ⟨hn, hpc⟩ := hw.cleaner_sub n pc m hm
    exact ⟨n, hn, pc, hpc, hm⟩

theorem mem_needGens {A : List ESite} {N : List Mark} {m : Mark} :
    m ∈ needGens A N ↔ ∃ σ, σ ∈ A ∧ (∃ g, g ∈ σ.abstract.gens ∧ g ∈ N) ∧
      m ∈ σ.abstract.cond.atoms := by
  simp only [needGens, List.mem_flatMap]
  constructor
  · rintro ⟨σ, hσ, hm⟩
    by_cases hg : σ.abstract.gens.any (fun g => decide (g ∈ N)) = true
    · simp only [hg, if_true] at hm
      obtain ⟨g, hg1, hg2⟩ := List.any_eq_true.mp hg
      exact ⟨σ, hσ, ⟨g, hg1, of_decide_eq_true hg2⟩, hm⟩
    · simp [hg] at hm
  · rintro ⟨σ, hσ, ⟨g, hg1, hg2⟩, hm⟩
    have hg : σ.abstract.gens.any (fun g => decide (g ∈ N)) = true :=
      List.any_eq_true.mpr ⟨g, hg1, decide_eq_true hg2⟩
    exact ⟨σ, hσ, by simp only [hg, if_true]; exact hm⟩

theorem mem_needStep {A : List ESite} {N : List Mark} {m : Mark} :
    m ∈ needStep A N ↔ m ∈ N ∨ m ∈ needGens A N := by
  simp [needStep, mem_addNew]

theorem neededSet_stable (A : List ESite) (C : List Mark) :
    needStable A (neededSet A C) = true := by
  apply iterC_stable (needStep A) (needStable A) (fun _ => True)
    (fun N => ((needUniverse A).filter fun x => !decide (x ∈ N)).length) (fun _ _ => trivial)
  · intro N _ hs
    obtain ⟨m, hm, hmN⟩ := all_false_wit hs
    have hmN' : m ∉ N := of_decide_eq_false hmN
    apply filter_length_lt_mono
    · intro x _ hx
      rw [Bool.not_eq_true', decide_eq_false_iff_not] at hx ⊢
      exact fun h => hx (mem_needStep.mpr (Or.inl h))
    · refine ⟨m, ?_, ?_, ?_⟩
      · obtain ⟨σ, hσ, _, hat⟩ := mem_needGens.mp hm
        rw [needUniverse, mem_dedup, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨σ, hσ, hat⟩
      · rw [Bool.not_eq_true', decide_eq_false_iff_not]; exact hmN'
      · rw [Bool.not_eq_false', decide_eq_true_eq]; exact mem_needStep.mpr (Or.inr hm)
  · trivial
  · exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The backward pass computes `Needed`, provided `A` lists exactly the
applicable sites and `C` exactly the recorded cleaner atoms. -/
theorem neededSet_iff (p : Program) (A : List ESite) (C : List Mark)
    (hA : ∀ σ, σ ∈ A ↔ ∃ n pc, Applicable p n pc σ)
    (hC : ∀ m, m ∈ C ↔ ∃ n pc, m ∈ p.cleanerAtoms n pc) (m : Mark) :
    m ∈ neededSet A C ↔ Needed p m := by
  have hinv := iterC_inv (needStep A) (needStable A)
    (fun N => (∀ m, m ∈ N → Needed p m) ∧ ∀ m, m ∈ needSeeds A ++ C → m ∈ N)
    (by
      intro N ⟨hN, hseed⟩
      refine ⟨?_, fun m hm => mem_needStep.mpr (Or.inl (hseed m hm))⟩
      intro m hm
      rcases mem_needStep.mp hm with h | h
      · exact hN m h
      · obtain ⟨σ, hσ, ⟨g, hg, hgN⟩, hat⟩ := mem_needGens.mp h
        obtain ⟨n, pc, happ⟩ := (hA σ).mp hσ
        exact Needed.trans happ hg (hN g hgN) hat)
    ((needUniverse A).length + 1) (needSeeds A ++ C)
    (by
      refine ⟨?_, fun _ h => h⟩
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨σ, hσ, ⟨hk, hm⟩ | ⟨hk, hm⟩⟩ := mem_needSeeds.mp hm
        · obtain ⟨n, pc, happ⟩ := (hA σ).mp hσ
          rcases hm with h | h
          · exact Needed.sinkAtom happ hk h
          · exact Needed.sinkGen happ hk h
        · obtain ⟨n, pc, happ⟩ := (hA σ).mp hσ
          exact Needed.passAtom happ hk hm
      · obtain ⟨n, pc, h⟩ := (hC m).mp hm
        exact Needed.cleanerAtom h)
  have hst : ∀ m, m ∈ needGens A (neededSet A C) → m ∈ neededSet A C := by
    have := neededSet_stable A C
    unfold needStable at this
    intro m hm
    exact of_decide_eq_true (List.all_eq_true.mp this m hm)
  have hseed : ∀ m, m ∈ needSeeds A → m ∈ neededSet A C :=
    fun m h => hinv.2 m (List.mem_append_left C h)
  constructor
  · exact hinv.1 m
  · intro h
    induction h with
    | sinkAtom happ hk hat =>
      exact hseed _ (mem_needSeeds.mpr ⟨_, (hA _).mpr ⟨_, _, happ⟩, Or.inl ⟨hk, Or.inl hat⟩⟩)
    | sinkGen happ hk hg =>
      exact hseed _ (mem_needSeeds.mpr ⟨_, (hA _).mpr ⟨_, _, happ⟩, Or.inl ⟨hk, Or.inr hg⟩⟩)
    | trans happ hg _ hat ih =>
      exact hst _ (mem_needGens.mpr ⟨_, (hA _).mpr ⟨_, _, happ⟩, ⟨_, hg, ih⟩, hat⟩)
    | cleanerAtom hm =>
      exact hinv.2 _ (List.mem_append_right _ ((hC _).mpr ⟨_, _, hm⟩))
    | passAtom happ hk hat =>
      exact hseed _ (mem_needSeeds.mpr ⟨_, (hA _).mpr ⟨_, _, happ⟩, Or.inr ⟨hk, hat⟩⟩)

theorem mem_appSites_applicable (p : Program) (hw : WF p) (app : Node → Pc → ESite → Bool)
    (happ : ∀ n pc σ, app n pc σ = true ↔ Applicable p n pc σ) (σ : ESite) :
    σ ∈ appSites p app ↔ ∃ n pc, Applicable p n pc σ := by
  rw [mem_appSites]
  constructor
  · rintro ⟨n, _, pc, _, h⟩
    exact ⟨n, pc, (happ n pc σ).mp h⟩
  · rintro ⟨n, pc, h⟩
    have hn := hw.sites_node n pc σ h.1
    exact ⟨n, hn, pc, mem_nodeSites.mpr ⟨hw.sites_pc n pc σ hn h.1, h.1⟩, (happ n pc σ).mpr h⟩

end AlgorithmLemmas

open AlgorithmLemmas

/-! ### Main theorems for the reference algorithm -/

/-- The reference algorithm computes exactly the per-root mark sets `S_E` of
the specification, including the method-level join correction and the
zero-context placement of sink gens. -/
theorem refInS_iff (p : Program) (hw : WF p) {E : Node} (hE : E ∈ p.roots) (m : Mark) :
    refInS p E m = true ↔ InS p E m := by
  unfold refInS refSets
  rw [lookup_map_self _ _ _ hE, Option.getD_some, decide_eq_true_eq]
  exact refFinal_iff p hw hE m

/-- The reference algorithm selects exactly the applicable sites. The
hypothesis `n ∈ p.nodes` of the requested statement is not needed. -/
theorem refApplicable_iff (p : Program) (hw : WF p) (n : Node) (pc : Pc) (σ : ESite) :
    refApplicable p n pc σ = true ↔ Applicable p n pc σ :=
  applicableOn_iff p hw (refFinal p) (fun _ hE m => refFinal_iff p hw hE m) n pc σ

/-- The reference backward pass computes exactly the needed marks, including
every recorded cleaner atom and the atoms of applicable pass-throughs. -/
theorem refNeeded_iff (p : Program) (hw : WF p) (m : Mark) :
    refNeeded p m = true ↔ Needed p m := by
  unfold refNeeded
  rw [decide_eq_true_eq]
  exact neededSet_iff p _ _ (mem_appSites_applicable p hw _ (refApplicable_iff p hw))
    (fun _ => mem_cleanerSeeds hw) m

/-- The fuel `refFuel = |roots| · |distinct gens| + 1` suffices: the reference
loop stops at a stable state, and it adds something in at most
`|roots| · |distinct gens|` rounds. -/
theorem refFuel_suffices (p : Program) (hw : WF p) :
    refStable p (refFinal p) = true ∧ refRounds p ≤ p.roots.length * (refUniverse p).length := by
  refine ⟨refFinal_stable p hw, ?_⟩
  exact Nat.le_trans
    (iterC_rounds_le_measure (refRound p) (refStable p) (fun _ => True) (refMeasure p)
      (fun _ _ => trivial) (fun y _ hs => refMeasure_dec p hw y hs) (refFuel p) _ trivial)
    (sum_map_le_mul _ _ _ (fun _ _ => List.length_filter_le _ _))

/-! ## (B) The optimized algorithm: signature propagation

A site's signature is its abstract `(cond, gens)` pair. The closure only
depends on the *set* of signatures reachable from a root, and many statements
share a signature. So the optimized round works as follows.
* Before the loop (state-independent, computed once): `nodeSigs k` is the
  deduplicated signature set of the non-sink sites of node `k`, `sinkSigs k`
  that of its sinks, and `rootSigs E` is the deduplicated union of `nodeSigs`
  over `reachList E`. In Kotlin this is a bottom-up bitset union over the SCC
  condensation; here it is a direct union. The point is the deduplication.
* Per round and root: single-literal cubes of non-sink sites are evaluated
  once per signature in `rootSigs E` (`sigGens`).
* Per round and node: joined cubes of non-sink sites, and every cube of a
  sink, are evaluated once per signature of the node, on the method-level
  union `U(method node)`. Their gens do not depend on the root (they are
  zero-context facts), so they go into a table `nodeTable` that each root then
  reads for the nodes it reaches. -/

abbrev Sig := Dnf × List Mark

def Site.sig (s : Site) : Sig := (s.cond, s.gens)

/-- Some cube of at most one literal holds on `S`. -/
def singleSat (S : List Mark) (sg : Sig) : Bool :=
  sg.1.any fun c => decide (c.length ≤ 1) && c.all fun m => decide (m ∈ S)

/-- The signature has a joined cube. -/
def isJoinedSig (sg : Sig) : Bool := sg.1.any fun c => decide (2 ≤ c.length)

/-- Some joined cube holds on `U`. -/
def joinedSat (U : List Mark) (sg : Sig) : Bool :=
  sg.1.any fun c => decide (2 ≤ c.length) && c.all fun m => decide (m ∈ U)

/-- Some cube, of any length, holds on `U` (used for sinks). -/
def anySat (U : List Mark) (sg : Sig) : Bool :=
  sg.1.any fun c => c.all fun m => decide (m ∈ U)

/-- The site of a statement entry is a sink. -/
def isSinkSite (ps : Pc × ESite) : Bool := decide (ps.2.kind = .sink)

/-- The distinct signatures of the non-sink sites of node `k`. -/
def nodeSigs (p : Program) (k : Node) : List Sig :=
  dedup (((p.nodeSites k).filter fun ps => !isSinkSite ps).map fun ps => ps.2.abstract.sig)

/-- The distinct signatures of the sinks of node `k`. -/
def sinkSigs (p : Program) (k : Node) : List Sig :=
  dedup (((p.nodeSites k).filter isSinkSite).map fun ps => ps.2.abstract.sig)

def rootSigs (p : Program) (E : Node) : List Sig :=
  dedup ((reachList p E).flatMap (nodeSigs p))

def joinedSigs (p : Program) (k : Node) : List Sig := (nodeSigs p k).filter isJoinedSig

/-- The nodes reachable from some root. -/
def reachAll (p : Program) : List Node := dedup (p.roots.flatMap (reachList p))

/-- The gens of the single-literal cubes of a signature list that hold on `S`. -/
def sigGens (S : List Mark) (L : List Sig) : List Mark :=
  L.flatMap fun sg => if singleSat S sg then sg.2 else []

/-- The root-independent gens of node `k`: joined signatures and sink
signatures whose cube holds on `U(method k)`. -/
def tableGensAt (p : Program) (S : Node → List Mark) (k : Node) : List Mark :=
  (joinedSigs p k).flatMap (fun sg => if joinedSat (refUM p S k) sg then sg.2 else []) ++
    (sinkSigs p k).flatMap (fun sg => if anySat (refUM p S k) sg then sg.2 else [])

/-- Root-independent gens, evaluated once per reachable node and round. -/
def nodeTable (p : Program) (S : Node → List Mark) : List (Node × List Mark) :=
  (reachAll p).map fun k => (k, tableGensAt p S k)

def optGens (p : Program) (J : List (Node × List Mark)) (S : Node → List Mark) (E : Node) :
    List Mark :=
  sigGens (S E) (rootSigs p E) ++ (reachList p E).flatMap fun k => (J.lookup k).getD []

def optRound (p : Program) (S : Node → List Mark) : Node → List Mark :=
  let J := nodeTable p S
  fun E => addNew (S E) (optGens p J S E)

def optStable (p : Program) (S : Node → List Mark) : Bool :=
  let J := nodeTable p S
  p.roots.all fun E => (optGens p J S E).all fun g => decide (g ∈ S E)

def optIter (p : Program) : (Node → List Mark) × Nat :=
  iterC (optRound p) (optStable p) (refFuel p) (fun _ => [])

def optFinal (p : Program) : Node → List Mark := (optIter p).1

def optRounds (p : Program) : Nat := (optIter p).2

def optSets (p : Program) : List (Node × List Mark) :=
  p.roots.map fun E => (E, optFinal p E)

def optInS (p : Program) (E : Node) (m : Mark) : Bool :=
  decide (m ∈ ((optSets p).lookup E).getD [])

def optApplicable (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Bool :=
  applicableOn p (optFinal p) n pc σ

def optNeeded (p : Program) (m : Mark) : Bool :=
  decide (m ∈ neededSet (appSites p (optApplicable p)) (cleanerSeeds p))

/-- The single-literal closure of a mark set over a list of signatures. -/
def singleClosure (L : List Sig) (fuel : Nat) (S0 : List Mark) : List Mark × Nat :=
  iterC (fun S => addNew S (sigGens S L)) (fun S => (sigGens S L).all fun g => decide (g ∈ S))
    fuel S0

namespace AlgorithmLemmas

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem singleSat_iff {S : List Mark} {sg : Sig} :
    singleSat S sg = true ↔ ∃ c, c ∈ sg.1 ∧ c.length ≤ 1 ∧ ∀ m, m ∈ c → m ∈ S := by
  simp [singleSat, List.any_eq_true, List.all_eq_true]

theorem joinedSat_iff {U : List Mark} {sg : Sig} :
    joinedSat U sg = true ↔ ∃ c, c ∈ sg.1 ∧ 2 ≤ c.length ∧ ∀ m, m ∈ c → m ∈ U := by
  simp [joinedSat, List.any_eq_true, List.all_eq_true]

theorem anySat_iff {U : List Mark} {sg : Sig} :
    anySat U sg = true ↔ ∃ c, c ∈ sg.1 ∧ ∀ m, m ∈ c → m ∈ U := by
  simp [anySat, List.any_eq_true, List.all_eq_true]

theorem mem_sigGens {S : List Mark} {L : List Sig} {g : Mark} :
    g ∈ sigGens S L ↔ ∃ sg, sg ∈ L ∧ singleSat S sg = true ∧ g ∈ sg.2 := by
  simp only [sigGens, List.mem_flatMap]
  constructor
  · rintro ⟨sg, hsg, hg⟩
    by_cases h : singleSat S sg = true
    · simp only [h, if_true] at hg; exact ⟨sg, hsg, h, hg⟩
    · simp [h] at hg
  · rintro ⟨sg, hsg, h, hg⟩
    exact ⟨sg, hsg, by simp only [h, if_true]; exact hg⟩

theorem mem_nodeSigs {p : Program} {k : Node} {sg : Sig} :
    sg ∈ nodeSigs p k ↔
      ∃ pc σ, (pc, σ) ∈ p.nodeSites k ∧ σ.kind ≠ .sink ∧ σ.abstract.sig = sg := by
  simp only [nodeSigs, mem_dedup, List.mem_map, List.mem_filter, isSinkSite,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨pc, σ⟩, ⟨h, hk⟩, rfl⟩; exact ⟨pc, σ, h, hk, rfl⟩
  · rintro ⟨pc, σ, h, hk, rfl⟩; exact ⟨(pc, σ), ⟨h, hk⟩, rfl⟩

theorem mem_sinkSigs {p : Program} {k : Node} {sg : Sig} :
    sg ∈ sinkSigs p k ↔
      ∃ pc σ, (pc, σ) ∈ p.nodeSites k ∧ σ.kind = .sink ∧ σ.abstract.sig = sg := by
  simp only [sinkSigs, mem_dedup, List.mem_map, List.mem_filter, isSinkSite, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨pc, σ⟩, ⟨h, hk⟩, rfl⟩; exact ⟨pc, σ, h, hk, rfl⟩
  · rintro ⟨pc, σ, h, hk, rfl⟩; exact ⟨(pc, σ), ⟨h, hk⟩, rfl⟩

theorem mem_rootSigs {p : Program} {E : Node} {sg : Sig} :
    sg ∈ rootSigs p E ↔ ∃ k, k ∈ reachList p E ∧ sg ∈ nodeSigs p k := by
  simp [rootSigs, mem_dedup, List.mem_flatMap]

theorem mem_ite_nil {c : Bool} {l : List Mark} {g : Mark} :
    g ∈ (if c = true then l else []) ↔ c = true ∧ g ∈ l := by
  cases c <;> simp

theorem mem_tableGensAt {p : Program} {S : Node → List Mark} {k : Node} {g : Mark} :
    g ∈ tableGensAt p S k ↔
      (∃ sg, sg ∈ nodeSigs p k ∧ joinedSat (refUM p S k) sg = true ∧ g ∈ sg.2) ∨
      (∃ sg, sg ∈ sinkSigs p k ∧ anySat (refUM p S k) sg = true ∧ g ∈ sg.2) := by
  simp only [tableGensAt, joinedSigs, List.mem_append, List.mem_flatMap, List.mem_filter,
    mem_ite_nil]
  constructor
  · rintro (⟨sg, ⟨hsg, _⟩, h, hg⟩ | ⟨sg, hsg, h, hg⟩)
    · exact Or.inl ⟨sg, hsg, h, hg⟩
    · exact Or.inr ⟨sg, hsg, h, hg⟩
  · rintro (⟨sg, hsg, h, hg⟩ | ⟨sg, hsg, h, hg⟩)
    · have hj : isJoinedSig sg = true := by
        obtain ⟨c, hc, hl, _⟩ := joinedSat_iff.mp h
        exact List.any_eq_true.mpr ⟨c, hc, decide_eq_true hl⟩
      exact Or.inl ⟨sg, ⟨hsg, hj⟩, h, hg⟩
    · exact Or.inr ⟨sg, hsg, h, hg⟩

theorem mem_reachAll {p : Program} {k : Node} :
    k ∈ reachAll p ↔ ∃ E, E ∈ p.roots ∧ k ∈ reachList p E := by
  simp [reachAll, mem_dedup, List.mem_flatMap]

/-- For a root, one optimized round generates exactly what one reference round
generates (as sets). -/
theorem mem_optGens (p : Program) (S : Node → List Mark) {E : Node} (hE : E ∈ p.roots)
    (g : Mark) : g ∈ optGens p (nodeTable p S) S E ↔ g ∈ refGens p S E := by
  have hJ : ∀ k, k ∈ reachList p E →
      ((nodeTable p S).lookup k).getD [] = tableGensAt p S k := by
    intro k hk
    unfold nodeTable
    rw [lookup_map_self (tableGensAt p S) _ k (mem_reachAll.mpr ⟨E, hE, hk⟩), Option.getD_some]
  rw [optGens, List.mem_append, mem_refGens]
  constructor
  · rintro (h | h)
    · obtain ⟨sg, hsg, hsat, hg⟩ := mem_sigGens.mp h
      obtain ⟨k, hk, hsk⟩ := mem_rootSigs.mp hsg
      obtain ⟨pc, σ, hps, _, rfl⟩ := mem_nodeSigs.mp hsk
      obtain ⟨c, hc, hl, hall⟩ := singleSat_iff.mp hsat
      exact ⟨k, hk, pc, σ, hps, refSiteOk_of_single hc hl hE hk hall, hg⟩
    · obtain ⟨k, hk, hg⟩ := List.mem_flatMap.mp h
      rw [hJ k hk] at hg
      rcases mem_tableGensAt.mp hg with ⟨sg, hsk, hsat, hg⟩ | ⟨sg, hsk, hsat, hg⟩
      · obtain ⟨pc, σ, hps, _, rfl⟩ := mem_nodeSigs.mp hsk
        obtain ⟨c, hc, hl, hall⟩ := joinedSat_iff.mp hsat
        exact ⟨k, hk, pc, σ, hps, refSiteOk_of_union hc hall (Or.inr hl), hg⟩
      · obtain ⟨pc, σ, hps, hkind, rfl⟩ := mem_sinkSigs.mp hsk
        obtain ⟨c, hc, hall⟩ := anySat_iff.mp hsat
        exact ⟨k, hk, pc, σ, hps, refSiteOk_of_union hc hall (Or.inl hkind), hg⟩
  · rintro ⟨k, hk, pc, σ, hps, hok, hg⟩
    rcases refSiteOk_iff.mp hok with ⟨hkind, c, hc, hall⟩ | ⟨hkind, c, hc, hc'⟩
    · have hsk : σ.abstract.sig ∈ sinkSigs p k := mem_sinkSigs.mpr ⟨pc, σ, hps, hkind, rfl⟩
      refine Or.inr (List.mem_flatMap.mpr ⟨k, hk, ?_⟩)
      rw [hJ k hk]
      exact mem_tableGensAt.mpr (Or.inr ⟨σ.abstract.sig, hsk, anySat_iff.mpr ⟨c, hc, hall⟩, hg⟩)
    · have hsk : σ.abstract.sig ∈ nodeSigs p k := mem_nodeSigs.mpr ⟨pc, σ, hps, hkind, rfl⟩
      rcases refCubeOk_iff.mp hc' with ⟨hl, hall⟩ | ⟨hl, hall⟩
      · exact Or.inl (mem_sigGens.mpr ⟨σ.abstract.sig, mem_rootSigs.mpr ⟨k, hk, hsk⟩,
          singleSat_iff.mpr ⟨c, hc, hl, hall⟩, hg⟩)
      · refine Or.inr (List.mem_flatMap.mpr ⟨k, hk, ?_⟩)
        rw [hJ k hk]
        exact mem_tableGensAt.mpr
          (Or.inl ⟨σ.abstract.sig, hsk, joinedSat_iff.mpr ⟨c, hc, hl, hall⟩, hg⟩)

/-- Two states that agree on the roots. -/
def RootEq (p : Program) (S T : Node → List Mark) : Prop :=
  ∀ E, E ∈ p.roots → ∀ m, m ∈ S E ↔ m ∈ T E

theorem mem_refU_congr {p : Program} {S T : Node → List Mark} (h : RootEq p S T) (k : Node)
    (m : Mark) : m ∈ refU p S k ↔ m ∈ refU p T k := by
  rw [mem_refU, mem_refU]
  constructor
  · rintro ⟨E, hE, hk, hm⟩; exact ⟨E, hE, hk, (h E hE m).mp hm⟩
  · rintro ⟨E, hE, hk, hm⟩; exact ⟨E, hE, hk, (h E hE m).mpr hm⟩

theorem mem_refUM_congr {p : Program} {S T : Node → List Mark} (h : RootEq p S T) (k : Node)
    (m : Mark) : m ∈ refUM p S k ↔ m ∈ refUM p T k := by
  rw [mem_refUM, mem_refUM]
  constructor
  · rintro ⟨E, n', hE, hn', hmeth, hm⟩; exact ⟨E, n', hE, hn', hmeth, (h E hE m).mp hm⟩
  · rintro ⟨E, n', hE, hn', hmeth, hm⟩; exact ⟨E, n', hE, hn', hmeth, (h E hE m).mpr hm⟩

theorem refCubeOk_congr {p : Program} {S T : Node → List Mark} (h : RootEq p S T) {E : Node}
    (hE : E ∈ p.roots) (k : Node) (c : Cube) : refCubeOk p S E k c = refCubeOk p T E k c := by
  apply bool_eq_of_iff
  rw [refCubeOk_iff, refCubeOk_iff]
  constructor
  · rintro (⟨hl, hall⟩ | ⟨hl, hall⟩)
    · exact Or.inl ⟨hl, fun m hm => (h E hE m).mp (hall m hm)⟩
    · exact Or.inr ⟨hl, fun m hm => (mem_refUM_congr h k m).mp (hall m hm)⟩
  · rintro (⟨hl, hall⟩ | ⟨hl, hall⟩)
    · exact Or.inl ⟨hl, fun m hm => (h E hE m).mpr (hall m hm)⟩
    · exact Or.inr ⟨hl, fun m hm => (mem_refUM_congr h k m).mpr (hall m hm)⟩

/-- A round's gens depend only on the root sets, as sets. -/
theorem mem_refGens_congr {p : Program} {S T : Node → List Mark} (h : RootEq p S T)
    {E : Node} (hE : E ∈ p.roots) (g : Mark) : g ∈ refGens p S E ↔ g ∈ refGens p T E := by
  have hok : ∀ k σ, refSiteOk p S E k σ = true ↔ refSiteOk p T E k σ = true := by
    intro k σ
    rw [refSiteOk_iff, refSiteOk_iff]
    constructor
    · rintro (⟨hk, c, hc, hall⟩ | ⟨hk, c, hc, ho⟩)
      · exact Or.inl ⟨hk, c, hc, fun m hm => (mem_refUM_congr h k m).mp (hall m hm)⟩
      · exact Or.inr ⟨hk, c, hc, refCubeOk_congr h hE k c ▸ ho⟩
    · rintro (⟨hk, c, hc, hall⟩ | ⟨hk, c, hc, ho⟩)
      · exact Or.inl ⟨hk, c, hc, fun m hm => (mem_refUM_congr h k m).mpr (hall m hm)⟩
      · exact Or.inr ⟨hk, c, hc, (refCubeOk_congr h hE k c).symm ▸ ho⟩
  rw [mem_refGens, mem_refGens]
  constructor
  · rintro ⟨k, hk, pc, σ, hps, ho, hg⟩
    exact ⟨k, hk, pc, σ, hps, (hok k σ).mp ho, hg⟩
  · rintro ⟨k, hk, pc, σ, hps, ho, hg⟩
    exact ⟨k, hk, pc, σ, hps, (hok k σ).mpr ho, hg⟩

theorem opt_ref_lockstep (p : Program) :
    RootEq p (optFinal p) (refFinal p) ∧ optRounds p = refRounds p := by
  apply iterC_lockstep (optRound p) (refRound p) (optStable p) (refStable p) (RootEq p)
  · intro S T h
    apply bool_eq_of_iff
    rw [refStable_iff]
    simp only [optStable, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro hs E hE g hg
      exact (h E hE g).mp (hs E hE g ((mem_optGens p S hE g).mpr ((mem_refGens_congr h hE g).mpr hg)))
    · intro hs E hE g hg
      exact (h E hE g).mpr (hs E hE g ((mem_refGens_congr h hE g).mp ((mem_optGens p S hE g).mp hg)))
  · intro S T h E hE m
    simp only [optRound, mem_addNew, mem_refRound]
    rw [h E hE m, mem_optGens p S hE m, mem_refGens_congr h hE m]
  · intro E _ m; exact Iff.rfl

theorem lookup_map_congr (F G : Node → List Mark) (m : Mark) (E : Node) :
    ∀ (l : List Node), (∀ x, x ∈ l → (m ∈ F x ↔ m ∈ G x)) →
      (m ∈ ((l.map fun x => (x, F x)).lookup E).getD [] ↔
        m ∈ ((l.map fun x => (x, G x)).lookup E).getD [])
  | [], _ => Iff.rfl
  | a :: t, h => by
    simp only [List.map_cons, List.lookup_cons]
    cases E == a with
    | true => exact h a List.mem_cons_self
    | false => exact lookup_map_congr F G m E t (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem refCubeSat_congr (p : Program) {F G : Node → List Mark} (h : RootEq p F G) (n : Node)
    (c : Cube) : refCubeSat p F n c = refCubeSat p G n c := by
  apply bool_eq_of_iff
  unfold refCubeSat
  by_cases hl : c.length ≤ 1
  · simp only [hl, if_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true]
    constructor
    · rintro ⟨E, hE, hn, hall⟩; exact ⟨E, hE, hn, fun m hm => (h E hE m).mp (hall m hm)⟩
    · rintro ⟨E, hE, hn, hall⟩; exact ⟨E, hE, hn, fun m hm => (h E hE m).mpr (hall m hm)⟩
  · simp only [hl, if_false, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro hall m hm; exact (mem_refUM_congr h n m).mp (hall m hm)
    · intro hall m hm; exact (mem_refUM_congr h n m).mpr (hall m hm)

end AlgorithmLemmas

/-! ### Main theorems: the optimized algorithm equals the reference -/

/-- Signature propagation computes the same root sets as the reference
algorithm, in exactly the same number of rounds. No well-formedness is needed. -/
theorem opt_eq_ref (p : Program) :
    (∀ E, E ∈ p.roots → ∀ m, m ∈ optFinal p E ↔ m ∈ refFinal p E) ∧
      optRounds p = refRounds p :=
  opt_ref_lockstep p

/-- The optimized algorithm answers every `InS` query as the reference does. -/
theorem optInS_eq (p : Program) (E : Node) (m : Mark) : optInS p E m = refInS p E m := by
  apply bool_eq_of_iff
  unfold optInS refInS optSets refSets
  rw [decide_eq_true_eq, decide_eq_true_eq]
  exact lookup_map_congr _ _ m E p.roots (fun x hx => (opt_eq_ref p).1 x hx m)

/-- The optimized algorithm selects the same sites as the reference. -/
theorem optApplicable_eq (p : Program) : optApplicable p = refApplicable p := by
  funext n pc σ
  unfold optApplicable refApplicable applicableOn
  have h : refCubeSat p (optFinal p) n = refCubeSat p (refFinal p) n :=
    funext fun c => refCubeSat_congr p (opt_eq_ref p).1 n c
  rw [h]

/-- The optimized algorithm needs the same marks as the reference. -/
theorem optNeeded_eq (p : Program) : optNeeded p = refNeeded p := by
  funext m
  unfold optNeeded refNeeded
  rw [optApplicable_eq]

/-- The optimized algorithm meets the specification (via the reference). -/
theorem optInS_iff (p : Program) (hw : Algorithm.WF p) {E : Node} (hE : E ∈ p.roots) (m : Mark) :
    optInS p E m = true ↔ InS p E m := by
  rw [optInS_eq]; exact refInS_iff p hw hE m

theorem optApplicable_iff (p : Program) (hw : Algorithm.WF p) (n : Node) (pc : Pc) (σ : ESite) :
    optApplicable p n pc σ = true ↔ Applicable p n pc σ := by
  rw [optApplicable_eq]; exact refApplicable_iff p hw n pc σ

theorem optNeeded_iff (p : Program) (hw : Algorithm.WF p) (m : Mark) :
    optNeeded p m = true ↔ Needed p m := by
  rw [optNeeded_eq]; exact refNeeded_iff p hw m

/-- The single-literal closure depends only on the *set* of signatures, not on
their order or multiplicity. The result is the same as a set, and the number
of rounds is the same too. -/
theorem closure_sig_congr (L L' : List Sig) (hL : ∀ sg, sg ∈ L ↔ sg ∈ L') (fuel : Nat)
    (S0 : List Mark) :
    (∀ m, m ∈ (singleClosure L fuel S0).1 ↔ m ∈ (singleClosure L' fuel S0).1) ∧
      (singleClosure L fuel S0).2 = (singleClosure L' fuel S0).2 := by
  have hg : ∀ S T : List Mark, (∀ m, m ∈ S ↔ m ∈ T) → ∀ g, g ∈ sigGens S L ↔ g ∈ sigGens T L' := by
    intro S T h g
    have hs : ∀ sg, singleSat S sg = singleSat T sg := by
      intro sg; apply bool_eq_of_iff; rw [singleSat_iff, singleSat_iff]
      constructor
      · rintro ⟨c, hc, hl, hall⟩; exact ⟨c, hc, hl, fun m hm => (h m).mp (hall m hm)⟩
      · rintro ⟨c, hc, hl, hall⟩; exact ⟨c, hc, hl, fun m hm => (h m).mpr (hall m hm)⟩
    rw [mem_sigGens, mem_sigGens]
    constructor
    · rintro ⟨sg, h1, h2, h3⟩; exact ⟨sg, (hL sg).mp h1, (hs sg) ▸ h2, h3⟩
    · rintro ⟨sg, h1, h2, h3⟩; exact ⟨sg, (hL sg).mpr h1, (hs sg).symm ▸ h2, h3⟩
  apply iterC_lockstep _ _ _ _ (fun S T => ∀ m, m ∈ S ↔ m ∈ T)
  · intro S T h
    apply bool_eq_of_iff
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro hs g hgT; exact (h g).mp (hs g ((hg S T h g).mpr hgT))
    · intro hs g hgS; exact (h g).mpr (hs g ((hg S T h g).mp hgS))
  · intro S T h m
    rw [mem_addNew, mem_addNew, h m, hg S T h m]
  · intro m; exact Iff.rfl

/-- `closure_dedup`: the closure over the signatures of a list of sites (one
entry per statement) equals the closure over its deduplicated signatures, in
result and in rounds. This is why the Kotlin scan can evaluate each distinct
signature once. -/
theorem closure_dedup (L : List Site) (fuel : Nat) (S0 : List Mark) :
    (∀ m, m ∈ (singleClosure (L.map Site.sig) fuel S0).1 ↔
      m ∈ (singleClosure (dedup (L.map Site.sig)) fuel S0).1) ∧
    (singleClosure (L.map Site.sig) fuel S0).2 =
      (singleClosure (dedup (L.map Site.sig)) fuel S0).2 :=
  closure_sig_congr _ _ (fun sg => (mem_dedup _ sg).symm) fuel S0

/-! ## Applicability from unions only

At a node reachable from some root, a cube of at most one literal is satisfied
by some root's set iff each of its marks lies in the node-level union `U(n)`:
it has at most one mark, and the empty cube only needs a root that reaches
`n`. So after the fixpoint, selection only needs the per-node unions `U(n)` and
the per-method unions `U(method n)`, not a per-root record of which signatures
were satisfied. -/

/-- Applicability read off the unions of the final sets only: a cube of at most
one literal is checked on `U(n)`, a joined cube on `U(method n)`. -/
def optApplicableU (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Bool :=
  decide (σ ∈ p.sites n pc) && σ.abstract.cond.any fun c =>
    if c.length ≤ 1 then c.all (fun m => decide (m ∈ refU p (optFinal p) n))
    else c.all (fun m => decide (m ∈ refUM p (optFinal p) n))

namespace AlgorithmLemmas

/-- For a cube of at most one literal, "one witness for all marks" equals "a
witness per mark", provided some witness exists at all (for the empty cube). -/
theorem single_cube_swap {P : Node → Prop} {Q : Node → Mark → Prop} {c : Cube}
    (hl : c.length ≤ 1) (hne : ∃ E, P E) :
    (∃ E, P E ∧ ∀ m, m ∈ c → Q E m) ↔ ∀ m, m ∈ c → ∃ E, P E ∧ Q E m := by
  constructor
  · rintro ⟨E, hP, hQ⟩ m hm; exact ⟨E, hP, hQ m hm⟩
  · intro h
    match c, hl with
    | [], _ =>
      obtain ⟨E, hE⟩ := hne
      exact ⟨E, hE, fun _ hm => absurd hm List.not_mem_nil⟩
    | [a], _ =>
      obtain ⟨E, hP, hQ⟩ := h a List.mem_cons_self
      refine ⟨E, hP, fun m hm => ?_⟩
      rw [List.mem_singleton] at hm; subst hm; exact hQ
    | _ :: _ :: _, hl => simp at hl

theorem refCubeSat_union (p : Program) (F : Node → List Mark) {n : Node}
    (hn : n ∈ reachAll p) (c : Cube) :
    refCubeSat p F n c =
      if c.length ≤ 1 then c.all (fun m => decide (m ∈ refU p F n))
      else c.all (fun m => decide (m ∈ refUM p F n)) := by
  unfold refCubeSat
  by_cases hl : c.length ≤ 1
  · rw [if_pos hl, if_pos hl]
    apply bool_eq_of_iff
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    have hsw := single_cube_swap (P := fun E => E ∈ p.roots ∧ n ∈ reachList p E)
      (Q := fun E m => m ∈ F E) hl (mem_reachAll.mp hn)
    constructor
    · rintro ⟨E, hE, hnE, hall⟩ m hm
      obtain ⟨E', ⟨hE', hnE'⟩, hmE'⟩ := hsw.mp ⟨E, ⟨hE, hnE⟩, hall⟩ m hm
      exact mem_refU.mpr ⟨E', hE', hnE', hmE'⟩
    · intro hall
      obtain ⟨E, ⟨hE, hnE⟩, hall'⟩ := hsw.mpr (fun m hm => by
        obtain ⟨E, hE, hnE, hmE⟩ := mem_refU.mp (hall m hm)
        exact ⟨E, ⟨hE, hnE⟩, hmE⟩)
      exact ⟨E, hE, hnE, hall'⟩
  · rw [if_neg hl, if_neg hl]

end AlgorithmLemmas

/-- `applicable_iff_union`: at a node reachable from some root, applicability
depends only on unions. A cube of at most one literal is satisfied iff each of
its marks is in the node-level union `U(n)`, and a joined cube iff it is
contained in the method-level union `U(method n)`. This justifies an
implementation that stores only per-node union bitsets, not per-root
satisfied-signature bitsets. -/
theorem applicable_iff_union (p : Program) {n : Node}
    (hn : ∃ E, E ∈ p.roots ∧ Reaches p E n) (pc : Pc) (σ : ESite) :
    Applicable p n pc σ ↔ σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧
      ((c.length ≤ 1 ∧ ∀ m, m ∈ c → ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ InS p E m) ∨
       (2 ≤ c.length ∧ ∀ m, m ∈ c →
          ∃ E n', E ∈ p.roots ∧ Reaches p E n' ∧ p.method n' = p.method n ∧ InS p E m)) := by
  have hcube : ∀ c : Cube, CubeSat p n c ↔
      ((c.length ≤ 1 ∧ ∀ m, m ∈ c → ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ InS p E m) ∨
       (2 ≤ c.length ∧ ∀ m, m ∈ c →
          ∃ E n', E ∈ p.roots ∧ Reaches p E n' ∧ p.method n' = p.method n ∧ InS p E m)) := by
    intro c
    unfold CubeSat
    constructor
    · rintro (⟨hl, E, hE, hR, hall⟩ | h)
      · exact Or.inl ⟨hl, fun m hm => ⟨E, hE, hR, hall m hm⟩⟩
      · exact Or.inr h
    · rintro (⟨hl, hall⟩ | h)
      · have hsw := single_cube_swap (P := fun E => E ∈ p.roots ∧ Reaches p E n)
          (Q := fun E m => InS p E m) hl hn
        obtain ⟨E, ⟨hE, hR⟩, hall'⟩ := hsw.mpr (fun m hm => by
          obtain ⟨E, hE, hR, h⟩ := hall m hm
          exact ⟨E, ⟨hE, hR⟩, h⟩)
        exact Or.inl ⟨hl, E, hE, hR, hall'⟩
      · exact Or.inr h
  unfold Applicable
  constructor
  · rintro ⟨hs, c, hc, h⟩; exact ⟨hs, c, hc, (hcube c).mp h⟩
  · rintro ⟨hs, c, hc, h⟩; exact ⟨hs, c, hc, (hcube c).mpr h⟩

/-- The union-only check `optApplicableU` agrees with `optApplicable` at every
node reached from some root (no well-formedness needed). -/
theorem optApplicableU_eq_of_reachAll (p : Program) {n : Node} (hn : n ∈ reachAll p)
    (pc : Pc) (σ : ESite) : optApplicableU p n pc σ = optApplicable p n pc σ := by
  unfold optApplicableU optApplicable applicableOn
  have h : refCubeSat p (optFinal p) n = fun c =>
      if c.length ≤ 1 then c.all (fun m => decide (m ∈ refU p (optFinal p) n))
      else c.all (fun m => decide (m ∈ refUM p (optFinal p) n)) :=
    funext fun c => refCubeSat_union p (optFinal p) hn c
  rw [h]

/-- The union-only check `optApplicableU` agrees with `optApplicable` at every
node reachable from a root, and hence decides `Applicable` there. An
implementation may therefore keep only per-node and per-method union bitsets
after the fixpoint. -/
theorem optApplicableU_eq (p : Program) (hw : Algorithm.WF p) {n : Node}
    (hn : ∃ E, E ∈ p.roots ∧ Reaches p E n) (pc : Pc) (σ : ESite) :
    optApplicableU p n pc σ = optApplicable p n pc σ := by
  obtain ⟨E, hE, hR⟩ := hn
  exact optApplicableU_eq_of_reachAll p
    (mem_reachAll.mpr ⟨E, hE, (mem_reachList p hw E n (hw.roots_sub E hE)).mpr hR⟩) pc σ

theorem optApplicableU_iff (p : Program) (hw : Algorithm.WF p) {n : Node}
    (hn : ∃ E, E ∈ p.roots ∧ Reaches p E n) (pc : Pc) (σ : ESite) :
    optApplicableU p n pc σ = true ↔ Applicable p n pc σ := by
  rw [optApplicableU_eq p hw hn]; exact optApplicable_iff p hw n pc σ


/-! ## Cost comparison

The unit of cost is one *cube evaluation*: testing one cube of one condition
against a mark set. It is counted without short-circuiting, so it is an upper
bound on the work of any evaluation order.
* Reference round: every root, every node it reaches, every statement's
  site, every cube. (A sink's cube is evaluated once, on `U(method k)`; see
  `refSiteOk`.)
* Optimized round: every root and every *distinct* non-sink signature it
  reaches, every cube; plus, once per reachable node, every cube of each
  distinct joined signature and each distinct sink signature of that node
  (`nodeTable`).
The unions `U`, like the signature sets (`nodeSigs`, `sinkSigs`, `rootSigs`,
`reachAll`), are not cube evaluations and are not counted. The signature sets
do not depend on the
state. They are computed once before the loop, and their cost is not a
per-round cost. The loop evaluates the gens `rounds + 1` times: once per
round that adds marks, plus the final round that confirms stability. -/

def refRoundCost (p : Program) : Nat :=
  (p.roots.map fun E => ((reachList p E).map fun k =>
    ((p.nodeSites k).map fun ps => ps.2.abstract.cond.length).sum).sum).sum

def optRoundCost (p : Program) : Nat :=
  (p.roots.map fun E => ((rootSigs p E).map fun sg => sg.1.length).sum).sum +
    ((reachAll p).map fun k => ((joinedSigs p k).map fun sg => sg.1.length).sum +
      ((sinkSigs p k).map fun sg => sg.1.length).sum).sum

/-- The reference algorithm with its step counter: `(result, cube evaluations)`. -/
def refRun (p : Program) : (Node → List Mark) × Nat :=
  (refFinal p, (refRounds p + 1) * refRoundCost p)

/-- The optimized algorithm with its step counter. -/
def optRun (p : Program) : (Node → List Mark) × Nat :=
  (optFinal p, (optRounds p + 1) * optRoundCost p)

def refSteps (p : Program) : Nat := (refRun p).2
def optSteps (p : Program) : Nat := (optRun p).2

/-- All distinct signatures of the program (of sinks and of other sites). -/
def allSigs (p : Program) : List Sig :=
  dedup (p.nodes.flatMap fun k => nodeSigs p k ++ sinkSigs p k)

/-- The largest number of cubes in a condition. -/
def maxCond (p : Program) : Nat := ((allSigs p).map fun sg => sg.1.length).foldl max 0

/-- Statements (with multiplicity) evaluated in the node table, over the
reachable nodes: non-sink sites with a joined cube, and sinks. -/
def joinedSiteCount (p : Program) : Nat :=
  ((reachAll p).map fun k =>
    ((p.nodeSites k).filter fun ps => !isSinkSite ps && isJoinedSig ps.2.abstract.sig).length +
      ((p.nodeSites k).filter isSinkSite).length).sum

namespace AlgorithmLemmas

theorem le_foldl_max : ∀ (l : List Nat) (acc : Nat),
    acc ≤ l.foldl max acc ∧ ∀ x, x ∈ l → x ≤ l.foldl max acc
  | [], acc => ⟨Nat.le_refl acc, fun _ h => absurd h List.not_mem_nil⟩
  | a :: t, acc => by
    have ih := le_foldl_max t (max acc a)
    simp only [List.foldl_cons]
    refine ⟨Nat.le_trans (Nat.le_max_left acc a) ih.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right acc x) ih.1
    · exact ih.2 x hx

theorem foldl_max_le : ∀ (l : List Nat) (acc B : Nat), acc ≤ B → (∀ x, x ∈ l → x ≤ B) →
    l.foldl max acc ≤ B
  | [], _, _, h, _ => h
  | a :: t, acc, B, h, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le t (max acc a) B (Nat.max_le.mpr ⟨h, hl a List.mem_cons_self⟩)
      (fun x hx => hl x (List.mem_cons_of_mem a hx))

theorem sum_map_mul_right {α : Type} (f : α → Nat) (M : Nat) :
    ∀ (l : List α), (l.map fun x => f x * M).sum = (l.map f).sum * M
  | [] => by simp
  | a :: t => by
    simp only [List.map_cons, List.sum_cons, sum_map_mul_right f M t, Nat.add_mul]

theorem le_sum_map_of_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => absurd h List.not_mem_nil
  | a :: t, x, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · have := le_sum_map_of_mem f t x h; omega

theorem mul_le_sum_map {α : Type} (f : α → Nat) (B : Nat) :
    ∀ (l : List α), (∀ x, x ∈ l → B ≤ f x) → l.length * B ≤ (l.map f).sum
  | [], _ => by simp
  | a :: t, h => by
    have ih := mul_le_sum_map f B t (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem sig_le_maxCond (p : Program) {sg : Sig} (h : sg ∈ allSigs p) : sg.1.length ≤ maxCond p :=
  (le_foldl_max _ 0).2 _ (List.mem_map.mpr ⟨sg, h, rfl⟩)

theorem mem_allSigs {p : Program} {sg : Sig} :
    sg ∈ allSigs p ↔ ∃ k, k ∈ p.nodes ∧ (sg ∈ nodeSigs p k ∨ sg ∈ sinkSigs p k) := by
  simp [allSigs, mem_dedup, List.mem_flatMap]

theorem reachAll_nodes (p : Program) (hw : WF p) {k : Node} (h : k ∈ reachAll p) : k ∈ p.nodes := by
  obtain ⟨E, hE, hk⟩ := mem_reachAll.mp h
  exact Reaches.nodes hw (reachList_reaches p E k hk) (hw.roots_sub E hE)

theorem rootSigs_cost_le (p : Program) (hw : WF p) {E : Node} (hE : E ∈ p.roots) :
    ((rootSigs p E).map fun sg => sg.1.length).sum ≤ (allSigs p).length * maxCond p := by
  have hsub : ∀ sg, sg ∈ rootSigs p E → sg ∈ allSigs p := by
    intro sg hsg
    obtain ⟨k, hk, hsk⟩ := mem_rootSigs.mp hsg
    have hkn : k ∈ p.nodes :=
      Reaches.nodes hw (reachList_reaches p E k hk) (hw.roots_sub E hE)
    exact mem_allSigs.mpr ⟨k, hkn, Or.inl hsk⟩
  refine Nat.le_trans (sum_map_le_mul _ (maxCond p) _ (fun sg h => sig_le_maxCond p (hsub sg h))) ?_
  exact Nat.mul_le_mul_right _ (length_le_of_nodup_subset _ _ (nodup_dedup _) hsub)

theorem joinedSigs_cost_le (p : Program) (hw : WF p) {k : Node} (hk : k ∈ reachAll p) :
    ((joinedSigs p k).map fun sg => sg.1.length).sum ≤
      ((p.nodeSites k).filter fun ps => !isSinkSite ps && isJoinedSig ps.2.abstract.sig).length *
        maxCond p := by
  have hkn := reachAll_nodes p hw hk
  have hsub : ∀ sg, sg ∈ joinedSigs p k → sg ∈ allSigs p := by
    intro sg hsg
    exact mem_allSigs.mpr ⟨k, hkn, Or.inl (List.mem_filter.mp hsg).1⟩
  refine Nat.le_trans (sum_map_le_mul _ (maxCond p) _ (fun sg h => sig_le_maxCond p (hsub sg h))) ?_
  apply Nat.mul_le_mul_right
  have hnd : (joinedSigs p k).Nodup := (nodup_dedup _).filter _
  have := length_le_of_nodup_subset (joinedSigs p k)
    (((p.nodeSites k).filter fun ps => !isSinkSite ps && isJoinedSig ps.2.abstract.sig).map
      fun ps => ps.2.abstract.sig)
    hnd (by
      intro sg hsg
      obtain ⟨hsk, hj⟩ := List.mem_filter.mp hsg
      obtain ⟨pc, σ, hps, hkind, rfl⟩ := mem_nodeSigs.mp hsk
      refine List.mem_map.mpr ⟨(pc, σ), List.mem_filter.mpr ⟨hps, ?_⟩, rfl⟩
      simp only [isSinkSite, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      exact ⟨hkind, hj⟩)
  rw [List.length_map] at this
  exact this

theorem sinkSigs_cost_le (p : Program) (hw : WF p) {k : Node} (hk : k ∈ reachAll p) :
    ((sinkSigs p k).map fun sg => sg.1.length).sum ≤
      ((p.nodeSites k).filter isSinkSite).length * maxCond p := by
  have hkn := reachAll_nodes p hw hk
  have hsub : ∀ sg, sg ∈ sinkSigs p k → sg ∈ allSigs p :=
    fun sg hsg => mem_allSigs.mpr ⟨k, hkn, Or.inr hsg⟩
  refine Nat.le_trans (sum_map_le_mul _ (maxCond p) _ (fun sg h => sig_le_maxCond p (hsub sg h))) ?_
  apply Nat.mul_le_mul_right
  have := length_le_of_nodup_subset (sinkSigs p k)
    (((p.nodeSites k).filter isSinkSite).map fun ps => ps.2.abstract.sig) (nodup_dedup _)
    (fun sg hsg => by
      obtain ⟨pc, σ, hps, hkind, rfl⟩ := mem_sinkSigs.mp hsg
      exact List.mem_map.mpr ⟨(pc, σ), List.mem_filter.mpr ⟨hps, decide_eq_true hkind⟩, rfl⟩)
  rw [List.length_map] at this
  exact this

end AlgorithmLemmas

/-- The reference cost is, by definition, `(rounds + 1) · Σ_E Σ_{k ∈ reach E}
Σ_{sites at k} |cond|`: it scales with the number of *statements* reachable
from each root. -/
theorem refSteps_eq (p : Program) :
    refSteps p = (refRounds p + 1) *
      (p.roots.map fun E => ((reachList p E).map fun k =>
        ((p.nodeSites k).map fun ps => ps.2.abstract.cond.length).sum).sum).sum := rfl

/-- One optimized round costs at most `|roots| · |distinct signatures| ·
maxCond + |joined and sink statements| · maxCond` cube evaluations, whatever
the number of statements that share a signature. -/
theorem optRoundCost_le (p : Program) (hw : Algorithm.WF p) :
    optRoundCost p ≤
      p.roots.length * ((allSigs p).length * maxCond p) + joinedSiteCount p * maxCond p := by
  unfold optRoundCost
  apply Nat.add_le_add
  · exact sum_map_le_mul _ _ _ (fun E hE => rootSigs_cost_le p hw hE)
  · unfold joinedSiteCount
    rw [← sum_map_mul_right]
    refine sum_map_le _ _ _ (fun k hk => ?_)
    rw [Nat.add_mul]
    exact Nat.add_le_add (joinedSigs_cost_le p hw hk) (sinkSigs_cost_le p hw hk)

/-- The optimized algorithm's total cost: rounds (the same as the reference's,
`opt_eq_ref`, and at most `|roots| · |distinct gens|` of them,
`refFuel_suffices`) times the per-round bound. -/
theorem optSteps_le (p : Program) (hw : Algorithm.WF p) :
    optSteps p ≤ (refRounds p + 1) *
      (p.roots.length * ((allSigs p).length * maxCond p) + joinedSiteCount p * maxCond p) := by
  unfold optSteps optRun
  rw [(opt_eq_ref p).2]
  exact Nat.mul_le_mul_left _ (optRoundCost_le p hw)

/-! ## The separating family

`famProg r k`: node `0` has `k` statements whose sites all carry the same
signature (a constant-true source generating mark `1`), and each of the
roots `1..r` calls node `0`. -/

def famSite : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }

def famProg (r k : Nat) : Program :=
  { nodes := 0 :: (List.range r).map (· + 1)
    roots := (List.range r).map (· + 1)
    pcs := fun n => if n = 0 then List.range k else [0]
    succ := fun _ _ => []
    exits := fun _ => []
    sites := fun n pc => if n = 0 ∧ pc < k then [famSite] else []
    calls := fun n _ => if n = 0 then [] else [0]
    mapIn := fun _ _ _ => none
    mapOut := fun _ _ _ => none
    kills := fun _ _ _ => false
    method := id
    cleanerAtoms := fun _ _ => [] }

namespace AlgorithmLemmas

theorem fam_sites {r k n : Nat} {pc : Pc} {σ : ESite} (h : σ ∈ (famProg r k).sites n pc) :
    σ = famSite ∧ n = 0 ∧ pc < k := by
  change σ ∈ (if n = 0 ∧ pc < k then [famSite] else []) at h
  by_cases hc : n = 0 ∧ pc < k
  · rw [if_pos hc, List.mem_singleton] at h; exact ⟨h, hc⟩
  · rw [if_neg hc] at h; exact absurd h List.not_mem_nil

theorem fam_nodeSites {r k n : Nat} {ps : Pc × ESite} (h : ps ∈ (famProg r k).nodeSites n) :
    ps.2 = famSite :=
  (fam_sites (mem_nodeSites.mp h).2).1

theorem fam_wf (r k : Nat) : WF (famProg r k) where
  roots_sub := fun _ h => List.mem_cons_of_mem 0 h
  callees_sub := by
    intro n _ c hc
    obtain ⟨pc, _, hc⟩ := List.mem_flatMap.mp hc
    change c ∈ (if n = 0 then [] else [0]) at hc
    by_cases hn : n = 0
    · rw [if_pos hn] at hc; exact absurd hc List.not_mem_nil
    · rw [if_neg hn, List.mem_singleton] at hc; subst hc; exact List.mem_cons_self
  sites_pc := by
    intro n pc σ _ h
    obtain ⟨_, hn, hpc⟩ := fam_sites h
    subst hn
    change pc ∈ (if 0 = 0 then List.range k else [0])
    rw [if_pos rfl, List.mem_range]; exact hpc
  sites_node := by
    intro n pc σ h
    obtain ⟨_, hn, _⟩ := fam_sites h
    subst hn; exact List.mem_cons_self
  cleaner_sub := fun _ _ _ h => absurd h List.not_mem_nil

theorem length_flatMap_one {α β : Type} (f : α → List β) :
    ∀ (l : List α), (∀ x, x ∈ l → (f x).length = 1) → (l.flatMap f).length = l.length
  | [], _ => rfl
  | a :: t, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      length_flatMap_one f t (fun x hx => h x (List.mem_cons_of_mem a hx)), List.length_cons,
      Nat.add_comm]

theorem filter_length_zero {α : Type} (q : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → q x = false) → (l.filter q).length = 0
  | [], _ => rfl
  | a :: t, h => by
    rw [List.filter_cons, h a List.mem_cons_self]
    exact filter_length_zero q t (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem fam_roots_length (r k : Nat) : (famProg r k).roots.length = r := by
  change ((List.range r).map (· + 1)).length = r
  rw [List.length_map, List.length_range]

/-- Every root reaches the shared node `0`, which carries `k` sites of one
condition each. -/
theorem fam_root_cost (r k : Nat) {E : Node} (hE : E ∈ (famProg r k).roots) :
    k ≤ ((reachList (famProg r k) E).map fun n =>
      (((famProg r k).nodeSites n).map fun ps => ps.2.abstract.cond.length).sum).sum := by
  have hw := fam_wf r k
  have hE0 : E ≠ 0 := by
    intro h; subst h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hE
    exact Nat.succ_ne_zero i hi
  have h0 : (0 : Node) ∈ (famProg r k).callees E := by
    apply List.mem_flatMap.mpr
    refine ⟨0, ?_, ?_⟩
    · change 0 ∈ (if E = 0 then List.range k else [0]); rw [if_neg hE0]; exact List.mem_singleton_self 0
    · change 0 ∈ (if E = 0 then [] else [0]); rw [if_neg hE0]; exact List.mem_singleton_self 0
  have hr : (0 : Node) ∈ reachList (famProg r k) E :=
    (mem_reachList _ hw E 0 (hw.roots_sub E hE)).mpr (Reaches.step h0 (Reaches.refl 0))
  refine Nat.le_trans ?_ (le_sum_map_of_mem _ _ 0 hr)
  have hone : ∀ ps, ps ∈ (famProg r k).nodeSites 0 → ps.2.abstract.cond.length = 1 := by
    intro ps hps; rw [fam_nodeSites hps]; rfl
  have hlen : ((famProg r k).nodeSites 0).length = k := by
    unfold Program.nodeSites
    rw [length_flatMap_one]
    · change (if (0 : Nat) = 0 then List.range k else [0]).length = k
      rw [if_pos rfl, List.length_range]
    · intro pc hpc
      change pc ∈ (if (0 : Nat) = 0 then List.range k else [0]) at hpc
      rw [if_pos rfl, List.mem_range] at hpc
      change ((if (0 : Nat) = 0 ∧ pc < k then [famSite] else []).map fun s => (pc, s)).length = 1
      rw [if_pos ⟨rfl, hpc⟩]; rfl
  have := mul_le_sum_map (fun ps : Pc × ESite => ps.2.abstract.cond.length) 1 _ (fun ps h => Nat.le_of_eq (hone ps h).symm)
  rw [hlen, Nat.mul_one] at this
  exact this

end AlgorithmLemmas

/-- On the family, one reference round costs at least `r · k` cube
evaluations: every root re-evaluates all `k` statements. -/
theorem fam_ref_round_ge (r k : Nat) : r * k ≤ refRoundCost (famProg r k) := by
  unfold refRoundCost
  have := mul_le_sum_map _ k _ (fun E hE => fam_root_cost r k hE)
  rw [fam_roots_length] at this
  exact this

/-- On the family, one optimized round costs at most `r` cube evaluations:
each root evaluates the single shared signature once, whatever `k` is. -/
theorem fam_opt_round_le (r k : Nat) : optRoundCost (famProg r k) ≤ r := by
  have hw := fam_wf r k
  have hsig : ∀ sg, sg ∈ allSigs (famProg r k) → sg = famSite.abstract.sig := by
    intro sg hsg
    obtain ⟨n, _, hsn | hsn⟩ := mem_allSigs.mp hsg
    · obtain ⟨pc, σ, hps, _, rfl⟩ := mem_nodeSigs.mp hsn
      rw [(fam_sites (mem_nodeSites.mp hps).2).1]
    · obtain ⟨pc, σ, hps, _, rfl⟩ := mem_sinkSigs.mp hsn
      rw [(fam_sites (mem_nodeSites.mp hps).2).1]
  have hA : (allSigs (famProg r k)).length ≤ 1 :=
    length_le_of_nodup_subset _ [famSite.abstract.sig] (nodup_dedup _)
      (fun sg h => by rw [hsig sg h]; exact List.mem_singleton_self _)
  have hM : maxCond (famProg r k) ≤ 1 := by
    apply foldl_max_le _ 0 1 (Nat.zero_le 1)
    intro x hx
    obtain ⟨sg, hsg, rfl⟩ := List.mem_map.mp hx
    rw [hsig sg hsg]; exact Nat.le_refl 1
  have hJ : joinedSiteCount (famProg r k) = 0 := by
    unfold joinedSiteCount
    apply Nat.eq_zero_of_le_zero
    have := sum_map_le_mul (fun n => (((famProg r k).nodeSites n).filter
      fun ps => !isSinkSite ps && isJoinedSig ps.2.abstract.sig).length +
        (((famProg r k).nodeSites n).filter isSinkSite).length) 0 (reachAll (famProg r k))
      (fun n _ => Nat.le_of_eq (by
        rw [filter_length_zero _ _ (fun ps hps => by rw [isSinkSite, fam_nodeSites hps]; rfl),
          filter_length_zero _ _ (fun ps hps => by rw [isSinkSite, fam_nodeSites hps]; rfl)]))
    rw [Nat.mul_zero] at this
    exact this
  refine Nat.le_trans (optRoundCost_le _ hw) ?_
  rw [hJ, Nat.zero_mul, Nat.add_zero, fam_roots_length]
  calc r * ((allSigs (famProg r k)).length * maxCond (famProg r k))
      ≤ r * (1 * 1) := Nat.mul_le_mul_left r (Nat.mul_le_mul hA hM)
    _ = r := Nat.mul_one r

/-- The family separates the two algorithms by a factor of `k` in total cube
evaluations. Both run the same number of rounds, and every optimized round is
`k` times cheaper. -/
theorem fam_speedup (r k : Nat) : optSteps (famProg r k) * k ≤ refSteps (famProg r k) := by
  unfold optSteps refSteps optRun refRun
  simp only
  rw [(opt_eq_ref (famProg r k)).2]
  calc (refRounds (famProg r k) + 1) * optRoundCost (famProg r k) * k
      ≤ (refRounds (famProg r k) + 1) * r * k :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul_left _ (fam_opt_round_le r k))
    _ = (refRounds (famProg r k) + 1) * (r * k) := Nat.mul_assoc _ _ _
    _ ≤ (refRounds (famProg r k) + 1) * refRoundCost (famProg r k) :=
        Nat.mul_le_mul_left _ (fam_ref_round_ge r k)

/-! Checked instances (kernel `decide`): `r = 3` roots, `k = 4` statements. The
reference evaluates `12` cubes per round and the optimized algorithm `3`.
There is one round that adds marks, plus the confirming round. -/

example : refRoundCost (famProg 3 4) = 12 := by decide
example : optRoundCost (famProg 3 4) = 3 := by decide
example : refRounds (famProg 3 4) = 1 ∧ optRounds (famProg 3 4) = 1 := by decide
example : refSteps (famProg 3 4) = 24 ∧ optSteps (famProg 3 4) = 6 := by decide
example : refSteps (famProg 2 10) = 40 ∧ optSteps (famProg 2 10) = 4 := by decide
example : refInS (famProg 3 4) 2 1 = true ∧ optInS (famProg 3 4) 2 1 = true := by decide

/-! ## A worked example with a joined cube

Roots `1` and `2` both call node `0`. Root `1` generates mark `10` and root `2`
generates mark `11`. At node `0`, a site with the joined cube `10 ∧ 11` (two
facts on different bases) generates `13`, and a sink checks `13`. A third site
needs `12`, which is never generated. By the D1 correction, `13` enters both
`S_1` and `S_2`, although neither set alone satisfies the cube. -/

def algExLit (b m : Nat) : ELit := ⟨⟨b, m⟩, false⟩

def algExSrc (g : Mark) : ESite :=
  { rule := g, kind := .source, cond := [[]], assigns := [⟨0, g⟩], copies := [] }
def algExJoin : ESite :=
  { rule := 3, kind := .source, cond := [[algExLit 0 10, algExLit 1 11]], assigns := [⟨0, 13⟩],
    copies := [] }
def algExSink : ESite :=
  { rule := 4, kind := .sink, cond := [[algExLit 0 13]], assigns := [], copies := [] }
def algExDead : ESite :=
  { rule := 5, kind := .source, cond := [[algExLit 0 12]], assigns := [⟨0, 14⟩], copies := [] }

def algExProg : Program :=
  { nodes := [0, 1, 2]
    roots := [1, 2]
    pcs := fun n => if n = 0 then [0, 1, 2] else [0]
    succ := fun _ _ => []
    exits := fun _ => []
    sites := fun n pc =>
      if n = 1 ∧ pc = 0 then [algExSrc 10] else if n = 2 ∧ pc = 0 then [algExSrc 11]
      else if n = 0 ∧ pc = 0 then [algExJoin] else if n = 0 ∧ pc = 1 then [algExSink]
      else if n = 0 ∧ pc = 2 then [algExDead] else []
    calls := fun n _ => if n = 0 then [] else [0]
    mapIn := fun _ _ _ => none
    mapOut := fun _ _ _ => none
    kills := fun _ _ _ => false
    method := id
    cleanerAtoms := fun _ _ => [] }

example : (refFinal algExProg 1, refFinal algExProg 2) = ([10, 13], [11, 13]) := by decide
example : refInS algExProg 1 13 = true ∧ refInS algExProg 2 13 = true ∧ refInS algExProg 1 11 = false :=
  by decide
example : refApplicable algExProg 0 0 algExJoin = true ∧ refApplicable algExProg 0 1 algExSink = true ∧
    refApplicable algExProg 0 2 algExDead = false := by decide
example : ([10, 11, 12, 13, 14].map (refNeeded algExProg)) = [true, true, false, true, false] := by
  decide
example : ([10, 11, 12, 13, 14].map (optNeeded algExProg)) = [true, true, false, true, false] := by
  decide

/-! ## A worked example for the v2 features

Two contexts of one method: node `0` (called by root `1`) and node `3` (called
by root `2`) both have method `0`. Node `4` is a third context of method `0`
that no root reaches. Root `1` generates `10` and `15`, root `2` generates `11`.
* Statement `0` of method `0` has the joined cube `10 ∧ 11 → 13`. It holds on
  the method-level union, so `13` enters `S_1` (via node `0`) and `S_2` (via
  node `3`).
* `(0, 1)` is a sink `11` with `trackFactsReachAnalysisEnd` mark `20`. `11` is
  in `U(method 0)` (from node `3`), so `InS.sinkGen` puts `20` into `S_1`. But
  the sink is not `Applicable` at node `0`: its single-literal cube needs `11`
  in a root that reaches node `0`, and only root `1` does.
* `(0, 2)` is a pass-through on `15`; `(0, 3)` is a sink on `13`; `(0, 1)`
  records the cleaner atom `30`. -/

def ex2SinkGen : ESite :=
  { rule := 6, kind := .sink, cond := [[algExLit 0 11]], assigns := [⟨0, 20⟩], copies := [] }
def ex2Pass : ESite :=
  { rule := 7, kind := .passThrough, cond := [[algExLit 0 15]], assigns := [], copies := [(0, 1)] }

def ex2Prog : Program :=
  { nodes := [0, 1, 2, 3, 4]
    roots := [1, 2]
    pcs := fun n => if n = 0 then [0, 1, 2, 3] else [0]
    succ := fun _ _ => []
    exits := fun _ => []
    sites := fun n pc =>
      if n = 1 ∧ pc = 0 then [algExSrc 10, algExSrc 15]
      else if n = 2 ∧ pc = 0 then [algExSrc 11]
      else if (n = 0 ∨ n = 3 ∨ n = 4) ∧ pc = 0 then [algExJoin]
      else if n = 0 ∧ pc = 1 then [ex2SinkGen]
      else if n = 0 ∧ pc = 2 then [ex2Pass]
      else if n = 0 ∧ pc = 3 then [algExSink] else []
    calls := fun n _ => if n = 1 then [0] else if n = 2 then [3] else []
    mapIn := fun _ _ _ => none
    mapOut := fun _ _ _ => none
    kills := fun _ _ _ => false
    method := fun n => if n = 3 ∨ n = 4 then 0 else n
    cleanerAtoms := fun n pc => if n = 0 ∧ pc = 1 then [30] else [] }

/-- The per-root sets: the joined gen `13` reaches both roots through the
method-level union; the sink gen `20` reaches root `1` only (the root that
reaches node `0`). -/
example : ([10, 11, 13, 15, 20].map (refInS ex2Prog 1)) = [true, false, true, true, true] ∧
    ([10, 11, 13, 15, 20].map (refInS ex2Prog 2)) = [false, true, true, false, false] := by
  decide

example : refApplicable ex2Prog 0 0 algExJoin = true ∧ refApplicable ex2Prog 3 0 algExJoin = true ∧
    refApplicable ex2Prog 0 1 ex2SinkGen = false ∧ refApplicable ex2Prog 0 2 ex2Pass = true ∧
    refApplicable ex2Prog 0 3 algExSink = true := by decide

/-- A joined cube at the unreached context `4` of method `0` is applicable too:
the v2 joined case of `CubeSat` does not ask for a root that reaches `n`. -/
example : refApplicable ex2Prog 4 0 algExJoin = true := by decide

/-- Needed: `13` (sink atom), `10` and `11` (backward through the join), `15`
(pass-through atom), `30` (cleaner atom). Not `20`: the sink `11 → 20` is not
applicable. -/
example : ([10, 11, 13, 15, 20, 30].map (refNeeded ex2Prog)) =
    [true, true, true, true, false, true] := by decide
example : ([10, 11, 13, 15, 20, 30].map (optNeeded ex2Prog)) =
    [true, true, true, true, false, true] := by decide
example : optApplicableU ex2Prog 0 1 ex2SinkGen = false ∧ optApplicableU ex2Prog 0 0 algExJoin = true ∧
    optApplicableU ex2Prog 3 0 algExJoin = true := by decide

namespace AlgorithmLemmas

theorem ex2_wf : WF ex2Prog where
  roots_sub := by decide
  callees_sub := by
    intro n _ c hc
    obtain ⟨pc, _, hc⟩ := List.mem_flatMap.mp hc
    simp only [ex2Prog] at hc
    split at hc
    · rw [List.mem_singleton] at hc; subst hc; decide
    · split at hc
      · rw [List.mem_singleton] at hc; subst hc; decide
      · exact absurd hc List.not_mem_nil
  sites_pc := by
    intro n pc σ _ h
    simp only [ex2Prog] at h ⊢
    repeat' split at h
    all_goals first
      | exact absurd h List.not_mem_nil
      | (split <;> simp_all)
  sites_node := by
    intro n pc σ h
    simp only [ex2Prog] at h ⊢
    repeat' split at h
    all_goals first
      | exact absurd h List.not_mem_nil
      | simp_all
  cleaner_sub := by
    intro n pc m h
    simp only [ex2Prog] at h ⊢
    split at h
    · obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›; decide
    · exact absurd h List.not_mem_nil

end AlgorithmLemmas

/-- Design observation on v2 `InS.sinkGen`: a sink's gens are placed when one
of its cubes lies in the method-level union `U(method n)`, even when the sink
is not `Applicable` at `n` (its single-literal cube is read per root). Here
`20 ∈ S_1` although the sink `11 → 20` at node `0` is never selected, so no
restricted run can emit `20`. This is sound (an over-approximation) but
imprecise. -/
theorem ex2_sinkGen_not_applicable :
    InS ex2Prog 1 20 ∧ ¬ Applicable ex2Prog 0 1 ex2SinkGen :=
  ⟨(refInS_iff ex2Prog ex2_wf (by decide) 20).mp (by decide),
   fun h => absurd ((refApplicable_iff ex2Prog ex2_wf 0 1 ex2SinkGen).mpr h) (by decide)⟩

/-- Design observation on v2 `CubeSat`: its joined case does not require a
root that reaches `n`, so a joined site at an unreached context of a reached
method is `Applicable` (sound, imprecise; the algorithms reproduce it exactly,
which is why `WF.sites_node` is needed to enumerate such sites). -/
theorem ex2_unreached_applicable :
    Applicable ex2Prog 4 0 algExJoin ∧ ¬ ∃ E, E ∈ ex2Prog.roots ∧ Reaches ex2Prog E 4 := by
  refine ⟨(refApplicable_iff ex2Prog ex2_wf 4 0 algExJoin).mp (by decide), ?_⟩
  rintro ⟨E, hE, hR⟩
  have h4 := (mem_reachList ex2Prog ex2_wf E 4 (ex2_wf.roots_sub E hE)).mpr hR
  exact absurd h4 ((by decide : ∀ E, E ∈ ex2Prog.roots → 4 ∉ reachList ex2Prog E) E hE)

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
