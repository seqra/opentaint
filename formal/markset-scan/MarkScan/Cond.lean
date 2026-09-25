import MarkScan.Basic

/-!
# The condition layer

This module validates the residual-condition layer of the mark-set scan:

* the tree form (`Cond.sat`, what the implementation evaluates) and the DNF form
  (`Dnf.sat`, what the model reasons about) agree;
* satisfaction is monotone in the mark set, so over-approximating mark sets is
  safe;
* option 4* (`Dnf.relax`, "any mark suffices") over-approximates, needs no
  cross-fact join, and is join-distributive, while exact satisfaction is not;
* the literal reading of 4* (`Dnf.naiveAny`) is unsound on constant-true cubes;
* erasing positions from engine literals over-approximates, and negated
  literals are ignored;
* tree and DNF have equal semantics but exponentially different size.
-/

namespace MarkScan

/-! ## Helpers -/

namespace CondLemmas

theorem dnf_sat_iff (φ : Dnf) (s : List Mark) :
    φ.sat s = true ↔ ∃ c, c ∈ φ ∧ ∀ m, m ∈ c → m ∈ s := by
  simp [Dnf.sat, List.any_eq_true, List.all_eq_true]

theorem dnf_sat_append (φ ψ : Dnf) (s : List Mark) :
    Dnf.sat (φ ++ ψ) s = (φ.sat s || ψ.sat s) := by
  simp [Dnf.sat, List.any_append]

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem dnf_sat_product (φ ψ : Dnf) (s : List Mark) :
    Dnf.sat (φ.flatMap fun x => ψ.map fun y => x ++ y) s = (φ.sat s && ψ.sat s) := by
  apply bool_eq_of_iff
  rw [Bool.and_eq_true, dnf_sat_iff, dnf_sat_iff, dnf_sat_iff]
  constructor
  · rintro ⟨c, hc, hall⟩
    rw [List.mem_flatMap] at hc
    obtain ⟨x, hx, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    exact ⟨⟨x, hx, fun m hm => hall m (List.mem_append_left y hm)⟩,
           ⟨y, hy, fun m hm => hall m (List.mem_append_right x hm)⟩⟩
  · rintro ⟨⟨x, hx, hxs⟩, ⟨y, hy, hys⟩⟩
    refine ⟨x ++ y, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩
    · intro m hm
      rcases List.mem_append.mp hm with h | h
      · exact hxs m h
      · exact hys m h

theorem any_isEmpty_iff (φ : Dnf) : φ.any List.isEmpty = true ↔ [] ∈ φ := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, he⟩
    rw [List.isEmpty_iff] at he
    exact he ▸ hc
  · intro h
    exact ⟨[], h, rfl⟩

theorem sat_singletons_iff (l : List Mark) (s : List Mark) :
    Dnf.sat (l.map fun m => [m]) s = true ↔ ∃ m, m ∈ l ∧ m ∈ s := by
  rw [dnf_sat_iff]
  constructor
  · rintro ⟨c, hc, hall⟩
    rw [List.mem_map] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨m, hm, hall m (List.mem_singleton_self m)⟩
  · rintro ⟨m, hm, hs⟩
    refine ⟨[m], List.mem_map.mpr ⟨m, hm, rfl⟩, ?_⟩
    intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hs

theorem sat_unit : Dnf.sat [[]] s = true := rfl

end CondLemmas

open CondLemmas

/-! ## 1. Tree vs DNF -/

/-- The implementation evaluates the condition tree (`Cond.sat`), while the
model reasons on its DNF (`Dnf.sat ∘ Cond.toDnf`). The two agree on every mark
set, so every DNF-level theorem transfers to the implementation. -/
theorem Cond.sat_toDnf (c : Cond) (s : List Mark) : c.toDnf.sat s = c.sat s := by
  induction c with
  | tt => rfl
  | ff => rfl
  | atom m => simp [Cond.toDnf, Cond.sat, Dnf.sat]
  | and a b iha ihb => rw [Cond.toDnf, dnf_sat_product, iha, ihb]; rfl
  | or a b iha ihb => rw [Cond.toDnf, dnf_sat_append, iha, ihb]; rfl

/-! ## 2. Monotonicity -/

/-- Satisfaction of a DNF is monotone in the mark set: an over-approximated mark
set (the scan's `S_E`) never loses a satisfied condition. -/
theorem Dnf.sat_mono {φ : Dnf} {s t : List Mark} (hst : Subset s t) :
    φ.sat s = true → φ.sat t = true := by
  rw [dnf_sat_iff, dnf_sat_iff]
  rintro ⟨c, hc, hall⟩
  exact ⟨c, hc, fun m hm => hst m (hall m hm)⟩

/-- Tree-form satisfaction is monotone in the mark set, so the implementation's
evaluator is safe on over-approximated mark sets. -/
theorem Cond.sat_mono {c : Cond} {s t : List Mark} (hst : Subset s t) :
    c.sat s = true → c.sat t = true := by
  rw [← Cond.sat_toDnf, ← Cond.sat_toDnf]
  exact Dnf.sat_mono hst

/-! ## 3–5. Option 4* (relaxed conditions) -/

/-- Characterisation of relaxed satisfaction: a relaxed condition holds iff the
original has a constant-true cube or some atom of it is present. -/
theorem Dnf.relax_sat_iff (φ : Dnf) (s : List Mark) :
    φ.relax.sat s = true ↔ (φ.any List.isEmpty = true ∨ ∃ m, m ∈ φ.atoms ∧ m ∈ s) := by
  unfold Dnf.relax
  cases h : φ.any List.isEmpty with
  | true => simp [sat_unit]
  | false =>
    simp only [Bool.false_eq_true, if_false, false_or]
    exact sat_singletons_iff φ.flatten s

/-- Option 4* over-approximates: whenever the exact condition holds, the relaxed
one holds too, so selecting sites by relaxed conditions never drops a finding. -/
theorem Dnf.relax_sound {φ : Dnf} {s : List Mark} (h : φ.sat s = true) :
    φ.relax.sat s = true := by
  rw [Dnf.relax_sat_iff]
  rw [dnf_sat_iff] at h
  obtain ⟨c, hc, hall⟩ := h
  cases c with
  | nil => exact Or.inl ((any_isEmpty_iff φ).mpr hc)
  | cons m rest =>
    refine Or.inr ⟨m, ?_, hall m (List.mem_cons_self ..)⟩
    exact List.mem_flatten.mpr ⟨m :: rest, hc, List.mem_cons_self ..⟩

/-- Every cube of a relaxed condition has at most one literal, so under 4* the
D1 cross-fact join machinery (`InS.joined`, `genJoined`) is never needed. -/
theorem Dnf.relax_cubes_small {φ : Dnf} {c : Cube} (h : c ∈ φ.relax) : c.length ≤ 1 := by
  unfold Dnf.relax at h
  split at h
  · rw [List.mem_singleton] at h; subst h; simp
  · rw [List.mem_map] at h
    obtain ⟨m, _, rfl⟩ := h
    simp

/-- Relaxed satisfaction is join-distributive: it holds on a union of mark sets
iff it holds on one of them. This is what makes a per-mark (IFDS-style,
distributive) propagation exact for 4*. -/
theorem Dnf.relax_union (φ : Dnf) (s t : List Mark) :
    φ.relax.sat (s ++ t) = (φ.relax.sat s || φ.relax.sat t) := by
  apply bool_eq_of_iff
  rw [Bool.or_eq_true, Dnf.relax_sat_iff, Dnf.relax_sat_iff, Dnf.relax_sat_iff]
  constructor
  · rintro (h | ⟨m, hm, hst⟩)
    · exact Or.inl (Or.inl h)
    · rcases List.mem_append.mp hst with h | h
      · exact Or.inl (Or.inr ⟨m, hm, h⟩)
      · exact Or.inr (Or.inr ⟨m, hm, h⟩)
  · rintro ((h | ⟨m, hm, h⟩) | (h | ⟨m, hm, h⟩))
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, List.mem_append_left t h⟩
    · exact Or.inl h
    · exact Or.inr ⟨m, hm, List.mem_append_right s h⟩

/-! ## 6. Exact satisfaction is not join-distributive -/

/-- Witness: the cube `1 ∧ 2`, with mark `1` coming from one fact set and mark
`2` from another. -/
def nonDistribWitness : Dnf × List Mark × List Mark := ([[1, 2]], [1], [2])

/-- Exact satisfaction is not join-distributive: `[[1,2]]` holds on `[1] ++ [2]`
but on neither part. A per-mark distributive propagation therefore cannot decide
multi-literal cubes; they need the D1 join over contexts. -/
theorem Dnf.sat_not_join_distributive :
    let (φ, s, t) := nonDistribWitness
    φ.sat (s ++ t) = true ∧ (φ.sat s || φ.sat t) = false := by
  decide

/-! ## 7. The literal reading of 4* is unsound -/

/-- Witness: the condition `true ∨ 1`, evaluated on the empty mark set. -/
def naiveWitness : Dnf × List Mark := ([[], [1]], [])

/-- Design bug in the literal reading of 4* ("satisfiable if any of its marks is
present"): a condition with a constant-true cube holds with no marks at all, but
`naiveAny` rejects it. `Dnf.relax` must (and does) keep constant-true cubes. -/
theorem naiveAny_unsound :
    naiveWitness.1.sat naiveWitness.2 = true ∧
    naiveWitness.1.naiveAny naiveWitness.2 = false := by
  decide

/-- The literal reading of 4* is sound once constant-true cubes are excluded:
if no cube is empty, exact satisfaction implies some atom is present. -/
theorem naiveAny_sound_of_no_empty_cube {φ : Dnf} {s : List Mark}
    (hne : ∀ c, c ∈ φ → c ≠ []) (h : φ.sat s = true) : φ.naiveAny s = true := by
  rw [dnf_sat_iff] at h
  obtain ⟨c, hc, hall⟩ := h
  cases c with
  | nil => exact absurd rfl (hne [] hc)
  | cons m rest =>
    unfold Dnf.naiveAny Dnf.atoms
    rw [List.any_eq_true]
    refine ⟨m, List.mem_flatten.mpr ⟨m :: rest, hc, List.mem_cons_self ..⟩, ?_⟩
    rw [List.contains_iff_mem]
    exact hall m (List.mem_cons_self ..)

/-! ## 8. Precision loss of 4* -/

/-- Witness: the condition `1 ∧ 2` on the mark set `[1]`. -/
def relaxLossWitness : Dnf × List Mark := ([[1, 2]], [1])

/-- Option 4* loses precision: `1 ∧ 2` is false on `[1]`, but its relaxation is
true. The scan may select sites the exact semantics would skip. -/
theorem relax_precision_loss :
    relaxLossWitness.1.sat relaxLossWitness.2 = false ∧
    relaxLossWitness.1.relax.sat relaxLossWitness.2 = true := by
  decide

/-! ## 9. Engine literals vs abstract (mark-only) literals -/

/-- Erasing bases over-approximates: if a set of engine facts `F` contains every
fact a cube positively needs, the abstract cube (its marks) is satisfied by the
marks of `F`. -/
theorem ECube.abstract_sound (c : ECube) (F : List Fact)
    (h : ∀ f, f ∈ c.positive → f ∈ F) :
    Dnf.sat [c.positive.map (·.mark)] (F.map (·.mark)) = true := by
  rw [dnf_sat_iff]
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  intro m hm
  rw [List.mem_map] at hm ⊢
  obtain ⟨f, hf, rfl⟩ := hm
  exact ⟨f, h f hf, rfl⟩

/-- Adding a negated literal to a cube does not change the facts it needs:
negated mark literals are dropped, as the engine treats them as satisfied. -/
theorem ECube.positive_ignores_negated (c : ECube) (f : Fact) :
    ECube.positive (c ++ [⟨f, true⟩]) = ECube.positive c := by
  simp [ECube.positive, List.filter_append]

/-- Engine-level satisfaction of a cube on a fact set (all positive facts
present). -/
def ECube.satFacts (c : ECube) (F : List Fact) : Bool :=
  c.positive.all fun f => F.contains f

/-- Witness: the cube needs `(base 0, mark 1)`; the facts contain only
`(base 1, mark 1)`. -/
def erasureWitness : ECube × List Fact := ([⟨⟨0, 1⟩, false⟩], [⟨1, 1⟩])

/-- Erasing bases loses precision: the engine cube is not satisfied (wrong
base), but its abstract cube is (right mark). -/
theorem erasure_precision_loss :
    ECube.satFacts erasureWitness.1 erasureWitness.2 = false ∧
    Dnf.sat [erasureWitness.1.positive.map (·.mark)] (erasureWitness.2.map (·.mark)) = true := by
  decide

/-! ## 10. Concept vs optimization: tree vs DNF cost -/

/-- Size of a condition tree (number of nodes). -/
def Cond.size : Cond → Nat
  | .tt | .ff | .atom _ => 1
  | .and a b | .or a b => a.size + b.size + 1

/-- `(a₀ ∨ b₀) ∧ (a₁ ∨ b₁) ∧ … ∧ true`, with `k` disjunctions. -/
def andOrChain : Nat → Cond
  | 0 => .tt
  | k + 1 => .and (.or (.atom (2 * k)) (.atom (2 * k + 1))) (andOrChain k)

/-- The DNF of a chain of `k` binary disjunctions has `2^k` cubes. -/
theorem andOrChain_toDnf_length (k : Nat) : (andOrChain k).toDnf.length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [andOrChain, Cond.toDnf, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      List.length_map, ih, Nat.pow_succ]
    omega

/-- The tree of a chain of `k` binary disjunctions has `4k + 1` nodes. -/
theorem andOrChain_size (k : Nat) : (andOrChain k).size = 4 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [andOrChain, Cond.size, ih]; omega

/-- Concept vs optimization: the tree and its DNF have the same semantics
(`Cond.sat_toDnf`), but the DNF can be exponentially larger than the tree. The
implementation must evaluate the tree; the DNF is a proof device only. -/
theorem tree_vs_dnf_cost (k : Nat) (s : List Mark) :
    (andOrChain k).toDnf.sat s = (andOrChain k).sat s ∧
    (andOrChain k).size = 4 * k + 1 ∧
    (andOrChain k).toDnf.length = 2 ^ k :=
  ⟨Cond.sat_toDnf _ _, andOrChain_size k, andOrChain_toDnf_length k⟩

end MarkScan

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

