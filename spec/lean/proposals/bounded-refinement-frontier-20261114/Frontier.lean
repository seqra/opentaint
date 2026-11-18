import Coverage
import Partition

/- Candidate design: keep the existing global and paired relative cuts.
   Queries split only one OBSERVED field per existing demand row. The
   refinement view is not the semantic union of executable conclusions. -/
namespace BoundedRefinementFrontier
open NonEmptyPolicy NonEmptyRestriction BoundedMayPartition

def splitOne (field : Nat) : List Region :=
  [⟨[],.exact,[]⟩,⟨[],.star,[field]⟩,
   ⟨[field],.exact,[]⟩,⟨[field],.star,[]⟩]

def splitMany (fields : List Nat) : List Region :=
  [⟨[],.exact,[]⟩,⟨[],.star,fields⟩] ++
    fields.flatMap (fun f => [⟨[f],.exact,[]⟩,⟨[f],.star,[]⟩])

theorem many_guards_cover_every_suffix (fields : List Nat) (suffix : Path) :
    ∃ q ∈ splitMany fields, accepts q suffix = true := by
  cases suffix with
  | nil => exact ⟨⟨[],.exact,[]⟩,by simp [splitMany],rfl⟩
  | cons next rest =>
    by_cases chosen : next ∈ fields
    · refine ⟨⟨[next],.star,[]⟩,?_,?_⟩
      · simp only [splitMany,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨next,chosen,by simp⟩
      · cases rest <;> simp [accepts,dropHead,admits] <;> rfl
    · refine ⟨⟨[],.star,fields⟩,by simp [splitMany],?_⟩
      have absent : fields.contains next = false := by simpa using chosen
      change (!fields.contains next) = true
      rw [absent]
      rfl

theorem many_guards_have_linear_query_count (fields : List Nat) :
    (splitMany fields).length = 2+2*fields.length := by
  have count : (fields.flatMap (fun f =>
      ([⟨[f],.exact,[]⟩,⟨[f],.star,[]⟩] : List Region))).length = 2*fields.length := by
    induction fields with
    | nil => rfl
    | cons f fs ih => simp [ih]; omega
  simp [splitMany,count]
  omega

def routePoint (fields : List Nat) : Path → Region
  | [] => ⟨[],.exact,[]⟩
  | field :: _ => if fields.contains field then ⟨[field],.star,[]⟩
                 else ⟨[],.star,fields⟩

theorem routed_point_is_kept (fields : List Nat) (point : Path) :
    routePoint fields point ∈ splitMany fields ∧
    accepts (routePoint fields point) point = true := by
  cases point with
  | nil => simp [routePoint,splitMany,accepts,dropHead,admits]; rfl
  | cons field suffix =>
    by_cases selected : fields.contains field = true
    · simp only [routePoint,selected,ite_true]
      have member : field ∈ fields := by simpa using selected
      constructor
      · simp only [splitMany,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨field,member,by simp⟩
      · cases suffix <;> simp [accepts,dropHead,admits] <;> rfl
    · simp only [routePoint,selected,ite_false]
      constructor
      · simp [splitMany]
      · change (!fields.contains field) = true
        have absent : fields.contains field = false := by
          cases h : fields.contains field <;> simp_all
        rw [absent]
        rfl

inductive Routed (fields : List Nat) : List Region → List Path → Prop where
  | nil : Routed fields [] []
  | cons {q point qs points}
      (kept : q ∈ splitMany fields ∧ accepts q point = true)
      (tail : Routed fields qs points) : Routed fields (q::qs) (point::points)

/-- Route an already matched cube; do not enumerate a Cartesian product
    of regions. The complete input tuple and its rule relation stay intact. -/
theorem complete_cube_has_linear_routing (fields : List Nat) (points : List Path) :
    Routed fields (points.map (routePoint fields)) points := by
  induction points with
  | nil => exact .nil
  | cons point points ih => exact .cons (routed_point_is_kept fields point) ih

theorem same_output_permission_is_preserved (field : Nat)
    (transfer : Path → Path → Prop) (permission : Path → Prop)
    (input output : Path) :
    (transfer input output ∧ permission output) ↔
      ∃ q ∈ splitOne field, accepts q input = true ∧
        transfer input output ∧ permission output := by
  constructor
  · rintro ⟨hit,allowed⟩
    rcases many_guards_cover_every_suffix [field] input with ⟨q,member,yes⟩
    exact ⟨q,by simpa [splitOne,splitMany] using member,yes,hit,allowed⟩
  · rintro ⟨_,_,_,hit,allowed⟩; exact ⟨hit,allowed⟩

theorem split_covers_every_suffix (field : Nat) (suffix : Path) :
    ∃ q ∈ splitOne field, accepts q suffix = true := by
  cases suffix with
  | nil => exact ⟨⟨[],.exact,[]⟩,by simp [splitOne],rfl⟩
  | cons next rest =>
    by_cases same : next = field
    · subst next
      refine ⟨⟨[field],.star,[]⟩,by simp [splitOne],?_⟩
      cases rest <;> simp [accepts,dropHead,admits] <;> rfl
    · refine ⟨⟨[],.star,[field]⟩,by simp [splitOne],?_⟩
      simp [accepts,dropHead,admits,same]
      rfl

theorem split_never_enumerates_a_second_field (field : Nat) (q : Region)
    (inside : q ∈ splitOne field) : q.path.length ≤ 1 := by
  simp only [splitOne,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with h | h | h | h <;> subst q <;> simp

theorem split_query_count_is_constant (field : Nat) :
    (splitOne field).length = 4 := rfl

theorem split_preserves_any_point_transfer (field : Nat)
    (transfer : Path → Path → Prop) (input output : Path) :
    transfer input output ↔
      ∃ q ∈ splitOne field, accepts q input = true ∧ transfer input output := by
  constructor
  · intro hit
    rcases split_covers_every_suffix field input with ⟨q,member,yes⟩
    exact ⟨q,member,yes,hit⟩
  · rintro ⟨_,_,_,hit⟩; exact hit

def projected (seed : Seed) (region : Region) : Seed :=
  ⟨{seed.ap with path := seed.ap.path ++ region.path,
                   tail := region.tail,e := region.excluded},
   if seed.ap.mark.isNone then false else true⟩

/-- Split starts are authorized at the head of an existing demand row.
    This constructor is never applied recursively to newly created starts. -/
def oneFieldPlan (limit : Nat) (d : Ap) (base : Seed) (field : Nat) : List Seed :=
  if base.ap.path = d.path ∧ d.path.length+1 ≤ limit then
    ((splitOne field).filter fun r =>
      !(d.tail == .ne && r.path.isEmpty && r.tail == .exact)).map (projected base)
  else [base]

theorem projected_path_has_at_most_one_new_field (base : Seed) (field : Nat)
    (r : Region) (inside : r ∈ splitOne field) :
    (projected base r).ap.path.length ≤ base.ap.path.length+1 := by
  simpa only [projected,List.length_append] using
    Nat.add_le_add_left (split_never_enumerates_a_second_field field r inside)
      base.ap.path.length

theorem one_field_plan_keeps_both_original_bounds (limit : Nat) (d : Ap)
    (base q : Seed) (field : Nat) (old : legalSeed limit d base)
    (member : q ∈ oneFieldPlan limit d base field) :
    q.ap.path.length ≤ limit ∧ q.ap.path.length ≤ d.path.length+1 := by
  unfold oneFieldPlan at member
  split at member
  · rename_i allowed
    rcases List.mem_map.mp member with ⟨r,filtered,same⟩
    have inside := (List.mem_filter.mp filtered).1
    subst q
    have h := projected_path_has_at_most_one_new_field base field r inside
    rw [allowed.1] at h
    exact ⟨Nat.le_trans h allowed.2,h⟩
  · simp only [List.mem_singleton] at member
    subst q
    exact ⟨old.1,old.2.1⟩

theorem a_guessed_concrete_point_is_demand (base : Seed) (r : Region)
    (concrete : base.ap.mark.isNone = false) :
    (projected base r).demand = true := by simp [projected,concrete]

theorem no_may_or_ne_premise_is_added (base : Seed) (field : Nat)
    (r : Region) (inside : r ∈ splitOne field) :
    (projected base r).ap.tail ≠ .may ∧ (projected base r).ap.tail ≠ .ne := by
  simp only [splitOne,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with h | h | h | h <;> subst r <;> simp [projected]

/-- Same-head membership is deduplicated. A different head is an independent
    refinement key even if an executable MAY union absorbs its language. -/
def retainHead (heads : List Path) (head : Path) : List Path :=
  if heads.contains head then heads else head :: heads

theorem a_deeper_cut_head_survives_a_broad_may :
    retainHead [[]] [1] = [[1],[]] := by decide

theorem exact_child_point_is_not_lost (field : Nat) :
    accepts ⟨[field],.exact,[]⟩ [field] = true := by
  simp [accepts,dropHead,admits]
  rfl

/-- Actual submitted data is still bounded by the ordinary global cut. -/
theorem actual_cuts_are_not_bypassed (limit : Nat) (c : Value)
    (long : c.ap.path.length > limit) :
    (cut limit c).ap.tail = .ne ∧ (cut limit c).demand = true :=
  ⟨(real_cut_has_ne_demand_and_keeps_mark_protection limit c long).1,
   (real_cut_has_ne_demand_and_keeps_mark_protection limit c long).2.1⟩

theorem ne_plan_does_not_add_the_forbidden_empty_start :
    (oneFieldPlan 2 (flow .ne) ⟨flow .star,false⟩ 1).all
      (fun q => !(q.ap.path.isEmpty && q.ap.tail == .exact)) = true := by decide

end BoundedRefinementFrontier

#print axioms BoundedRefinementFrontier.split_covers_every_suffix
#print axioms BoundedRefinementFrontier.many_guards_cover_every_suffix
#print axioms BoundedRefinementFrontier.many_guards_have_linear_query_count
#print axioms BoundedRefinementFrontier.routed_point_is_kept
#print axioms BoundedRefinementFrontier.complete_cube_has_linear_routing
#print axioms BoundedRefinementFrontier.same_output_permission_is_preserved
#print axioms BoundedRefinementFrontier.split_never_enumerates_a_second_field
#print axioms BoundedRefinementFrontier.split_query_count_is_constant
#print axioms BoundedRefinementFrontier.split_preserves_any_point_transfer
#print axioms BoundedRefinementFrontier.projected_path_has_at_most_one_new_field
#print axioms BoundedRefinementFrontier.one_field_plan_keeps_both_original_bounds
#print axioms BoundedRefinementFrontier.a_guessed_concrete_point_is_demand
#print axioms BoundedRefinementFrontier.no_may_or_ne_premise_is_added
#print axioms BoundedRefinementFrontier.a_deeper_cut_head_survives_a_broad_may
#print axioms BoundedRefinementFrontier.exact_child_point_is_not_lost
#print axioms BoundedRefinementFrontier.actual_cuts_are_not_bypassed
#print axioms BoundedRefinementFrontier.ne_plan_does_not_add_the_forbidden_empty_start
