import UniformActual

namespace UniformSafety
open NonEmptyPolicy NonEmptyRestriction ExactSupport UniformActual
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

structure Point where
  base : Nat
  path : Path
  mark : Nat
  deriving DecidableEq, Repr

def supports (x : Item) (p : Point) : Prop :=
  x.key.ap.base = p.base ∧ x.key.ap.mark = some p.mark ∧ locationIn x.key.ap p.path

theorem every_possible_point_has_the_retained_definite_support (n x : Item)
    (covered : covers n x = true) (p : Point) (candidate : supports x p) : supports n p := by
  have original := covered
  unfold covers at covered
  simp only [Bool.and_eq_true] at covered
  have bases : n.key.ap.base = x.key.ap.base := by
    simpa only [beq_iff_eq] using covered.1.1.1.1.1.1.1.1.2
  have marks : n.key.ap.mark = x.key.ap.mark := by
    simpa only [beq_iff_eq] using covered.1.1.1.1.1.1.1.2
  exact ⟨bases.trans candidate.1,marks.trans candidate.2.1,
    deletion_covers_every_refinement_point n x original p.path candidate.2.2⟩

/-- Reuse exactly the same selected points of a complete guard binding.
    This is not a relaxation of AND or a summary-premise union. -/
theorem all_selected_points_of_a_binding_remain_supported (n x : Item)
    (covered : covers n x = true) (binding : List Point)
    (old : ∀ p ∈ binding, supports x p) : ∀ p ∈ binding, supports n p := by
  intro p hp
  exact every_possible_point_has_the_retained_definite_support n x covered p (old p hp)

/-- Concrete reachability continuations can depend on mark/path, and can
    contain any finite ordinary transfer sequence. Keep their exact trace;
    the stronger provider supplies the same starting point. -/
def concreteContinuation (trace : Point → List α) (x : Item) (result : α) : Prop :=
  ∃ start, supports x start ∧ result ∈ trace start

theorem every_finite_concrete_continuation_is_preserved (trace : Point → List α)
    (n x : Item) (covered : covers n x = true) (result : α)
    (old : concreteContinuation trace x result) : concreteContinuation trace n result := by
  rcases old with ⟨start,supported,reached⟩
  exact ⟨start,every_possible_point_has_the_retained_definite_support n x covered start supported,reached⟩

theorem the_filter_emits_no_new_initial_or_call_probe (queries : Item → List α)
    (ready packet : List Item) (query : α)
    (new : query ∈ (filter false ready packet).flatMap queries) : query ∈ packet.flatMap queries := by
  rcases List.mem_flatMap.mp new with ⟨x,present,emitted⟩
  exact List.mem_flatMap.mpr ⟨x,subset false ready packet x present,emitted⟩

theorem fewer_candidates_at_a_fixed_delivery_plan (queries : Item → List α)
    (ready packet : List Item) :
    ((filter false ready packet).flatMap queries).length ≤ (packet.flatMap queries).length := by
  have general (ys : List Item) (pred : Item → Bool) :
      ((ys.filter pred).flatMap queries).length ≤ (ys.flatMap queries).length := by
    induction ys generalizing pred with
    | nil => simp
    | cons h tail ih =>
        cases hp : pred h
        · simp only [List.filter_cons,hp,Bool.false_eq_true,ite_false,
            List.flatMap_cons,List.length_append]
          exact Nat.le_trans (ih pred) (Nat.le_add_left _ _)
        · simpa only [List.filter_cons,hp,ite_true,List.flatMap_cons,List.length_append] using
            Nat.add_le_add_left (ih pred) (queries h).length
  unfold filter
  simp only [Bool.false_eq_true,ite_false]
  exact general _ _

/-- A genuine later field cut still creates a new demand. Its pre-cut
    NORMAL MUST is not a legal provider at that new delivery boundary. -/
theorem a_real_cut_does_not_become_normal_uniform_coverage :
    let before : Value := ⟨⟨1,[1,2],.must,some 2,[],[]⟩,false,false⟩
    let after := cut 1 before
    after.demand = true ∧ after.ap.tail = .ne ∧
    foldValues false [] [after] = [after] := by decide

theorem a_short_normal_EXACT_is_not_a_uniform_provider :
    filter false [] [item .may true,item .exact false] = [item .may true,item .exact false] := by decide

theorem an_existing_child_uniform_is_kept_when_it_does_not_cover_the_question :
    filter false [] [item .may true,item .must false [1]] =
      [item .may true,item .must false [1]] := by decide

theorem an_excluded_whole_uniform_region_can_cover_its_root_point :
    filter false [] [item .exact true,item .must false [] [1]] =
      [item .must false [] [1]] := by decide

theorem actual_uniform_child_demand_with_its_own_hole_is_covered :
    filter false [] [item .must true [2] [1],item .must false [] [1]] =
      [item .must false [] [1]] := by decide

end UniformSafety
