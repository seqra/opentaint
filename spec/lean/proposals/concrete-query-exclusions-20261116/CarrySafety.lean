import CarryPolicy
namespace CarrySafety
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

open CarryPolicy

theorem carry_preserves_all_other_coordinates (a : Offered) (q : Seed) :
    (carry a q).ap.base = q.ap.base ∧ (carry a q).ap.path = q.ap.path ∧
    (carry a q).ap.tail = q.ap.tail ∧ (carry a q).ap.mark = q.ap.mark ∧
    (carry a q).ap.mx = q.ap.mx ∧ (carry a q).demand = q.demand := by
  unfold carry; split <;> simp

theorem no_E_union_or_synthetic_exclusion (a : Offered) (q : Seed) :
    (carry a q).ap.e = q.ap.e ∨ (carry a q).ap.e = a.ap.e := by
  unfold carry; split <;> simp

theorem different_actual_head_is_not_shifted (a : Offered) (q : Seed)
    (different : q.ap.path ≠ a.ap.path) : carry a q = q := by
  simp [carry,eligible,different]

theorem already_excluded_queries_are_unchanged (a : Offered) (q : Seed)
    (nonempty : q.ap.e.isEmpty = false) : carry a q = q := by
  simp [carry,eligible,nonempty]

theorem exactly_the_same_initial_family_size (run k : Nat) (back : Bool) (d : Ap) (a : Offered) :
    (CarryPolicy.emit run k back d a).length = (NonEmptyPolicy.emit run k back d a).length := by
  unfold CarryPolicy.emit; split <;> simp

theorem each_new_initial_has_an_old_initial_witness
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (present : q ∈ CarryPolicy.emit run k back d a) :
    ∃ old ∈ NonEmptyPolicy.emit run k back d a, q = old ∨ q = carry a old := by
  unfold CarryPolicy.emit at present
  split at present
  · exact ⟨q,present,Or.inl rfl⟩
  · rcases List.mem_map.mp present with ⟨old,oldIn,same⟩
    exact ⟨old,oldIn,Or.inr same.symm⟩

theorem emitted_legal (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (present : q ∈ CarryPolicy.emit run k back d a) : legalSeed k (selector d) q := by
  rcases each_new_initial_has_an_old_initial_witness run k back d a q present with ⟨old,oldIn,same⟩
  have legal := NonEmptyPolicy.emitted_legal run k back d a old oldIn
  rcases same with oldEq | carried
  · simpa [oldEq] using legal
  · rw [carried]
    simpa only [legalSeed,(carry_preserves_all_other_coordinates a old).2.1,
      (carry_preserves_all_other_coordinates a old).2.2.1] using legal

theorem no_owned_may_or_ne (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (present : q ∈ CarryPolicy.emit run k back d a) : q.ap.tail ≠ .may ∧ q.ap.tail ≠ .ne := by
  rcases (emitted_legal run k back d a q present).2.2 with exactTail | starTail | mustTail
  · rw [exactTail]; decide
  · rw [starTail]; decide
  · rw [mustTail]; decide

/-- A correlated query has weaker taint knowledge than MUST. Its geometric
    admissible region nevertheless includes exactly the actual region at
    this same head; no actual concrete refinement point is discarded. -/
theorem eligible_copy_preserves_the_entire_actual_point_region
    (a : Offered) (q : Seed) (yes : eligible a q = true) (location : Path) :
    UniformActual.locationIn (carry a q).ap location ↔ UniformActual.locationIn a.ap location := by
  have shape := yes
  unfold eligible at shape
  simp only [Bool.and_eq_true] at shape
  have paths : q.ap.path = a.ap.path := by simpa only [beq_iff_eq] using shape.1.1.2
  have qtail : q.ap.tail = .star := by
    cases qt : q.ap.tail <;> simp_all
  cases actualTail : a.ap.tail <;>
    simp_all [eligible,carry,UniformActual.locationIn,admits]
  constructor
  · rintro ⟨rest,whereAt,allowed⟩
    refine ⟨rest,whereAt,?_⟩
    cases rest with
    | nil => rfl
    | cons f rest => exact allowed
  · rintro ⟨rest,whereAt,allowed⟩
    refine ⟨rest,whereAt,?_⟩
    cases rest with
    | nil => rfl
    | cons f rest => exact allowed

theorem E_is_still_scoped_after_its_original_head :
    let a : Offered := ⟨⟨0,[1,2],.must,some 7,[2],[]⟩,false⟩
    let q : Seed := ⟨⟨0,[1],.star,some 7,[],[]⟩,true⟩
    carry a q = q := by decide +kernel

theorem no_extra_forward_uniform_or_backward_uniform_seed
    (a : Offered) (q : Seed) (uniform : q.ap.tail = .must) : carry a q = q := by
  simp [carry,eligible,uniform]

theorem abstract_raw_C5_image_is_unchanged (run k : Nat) (back : Bool) (d : Ap)
    (as : List Offered) (abstract : d.mark = none) :
    CarryPolicy.rawImage run k back d as = NonEmptyPolicy.rawImage run k back d as := by
  simp [CarryPolicy.rawImage,NonEmptyPolicy.rawImage,abstract_demands_are_exactly_the_old_policy,
    abstract]

theorem every_C5_initial_has_a_constructive_offer (run k : Nat) (back : Bool)
    (d : Ap) (as : List Offered) (raw : Ap)
    (present : raw ∈ CarryPolicy.rawImage run k back d as) :
    ∃ a ∈ as, ∃ q ∈ CarryPolicy.emit run k back d a, q.ap = raw := by
  rcases List.mem_flatMap.mp present with ⟨a,offered,inMap⟩
  rcases List.mem_map.mp inMap with ⟨q,emitted,same⟩
  exact ⟨a,offered,q,emitted,same⟩

theorem flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons,List.flatMap_cons,h x (by simp)]
      rw [ih (fun a ha => h a (by simp [ha]))]

theorem empty_actuals_raw_C5_image_is_unchanged (run k : Nat) (back : Bool) (d : Ap)
    (as : List Offered) (empty : ∀ a ∈ as, a.ap.e = []) :
    CarryPolicy.rawImage run k back d as = NonEmptyPolicy.rawImage run k back d as := by
  unfold CarryPolicy.rawImage NonEmptyPolicy.rawImage
  apply flatMap_congr
  intro a inside
  rw [CarryPolicy.empty_actual_E_is_exactly_the_old_policy run k back d a (empty a inside)]

theorem empty_actuals_C5_is_unchanged (run k : Nat) (back : Bool) (as : List Offered)
    (raw : Ap) (c : Value) (row : Row) (empty : ∀ a ∈ as, a.ap.e = []) :
    CarryPolicy.restrictOne run k back as raw c row =
      NonEmptyRestriction.restrictOne run k back as raw c row := by
  simp only [CarryPolicy.restrictOne,NonEmptyRestriction.restrictOne,
    empty_actuals_raw_C5_image_is_unchanged run k back row.entry as empty]

theorem abstract_C5_is_unchanged (run k : Nat) (back : Bool) (as : List Offered)
    (raw : Ap) (c : Value) (row : Row) (abstract : row.entry.mark = none) :
    CarryPolicy.restrictOne run k back as raw c row =
      NonEmptyRestriction.restrictOne run k back as raw c row := by
  simp only [CarryPolicy.restrictOne,NonEmptyRestriction.restrictOne,
    abstract_raw_C5_image_is_unchanged run k back row.entry as abstract]

theorem empty_members (as : List Offered)
    (yes : as.all (fun a => a.ap.e.isEmpty) = true) : ∀ a ∈ as, a.ap.e = [] := by
  intro a inside
  have empty := List.all_eq_true.mp yes a inside
  cases h : a.ap.e <;> simp_all

end CarrySafety

