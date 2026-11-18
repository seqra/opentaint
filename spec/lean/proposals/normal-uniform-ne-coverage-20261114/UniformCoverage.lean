import LocalRouting
import OrdinaryCycle

/- Proposed conservative egress law. Do not change C2, C5, field cuts,
   intraprocedural transfer, or backward MUST views. A legally admitted
   NORMAL uniform FLOW output can cover a post-C5 NE result under the SAME
   complete uniform FLOW premise. Protected/marked/ND cases are excluded. -/
namespace NormalUniformNE
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

abbrev Edge := Ap × Value

def uniformCovers (normal weak : Edge) : Bool :=
  decide (normal.1 = weak.1) &&
  normal.1.tail == .must && normal.1.mark.isNone &&
  normal.1.e.isEmpty && normal.1.mx.isEmpty &&
  !normal.2.demand && !normal.2.h && !weak.2.h && weak.2.demand &&
  normal.2.ap.tail == .must && weak.2.ap.tail == .ne &&
  normal.2.ap.mark.isNone && weak.2.ap.mark.isNone &&
  normal.2.ap.base == weak.2.ap.base &&
  normal.2.ap.e.isEmpty && normal.2.ap.mx.isEmpty &&
  weak.2.ap.e.isEmpty && weak.2.ap.mx.isEmpty &&
  (dropHead normal.2.ap.path weak.2.ap.path).isSome

/-- Existing interface equality includes owner/direction/ports in the
    embedding. This component is one fixed qualified forward owner. -/
def compact (forward : Bool) (edges : List Edge) : List Edge :=
  if forward then edges.filter fun e => !(edges.any fun n => uniformCovers n e)
  else edges

theorem protected_ne_is_never_removed (normal weak : Edge)
    (isProtected : weak.2.h = true) : uniformCovers normal weak = false := by
  simp [uniformCovers,isProtected]

theorem a_normal_provider_is_never_removed (normal weak : Edge)
    (complete : weak.2.demand = false) : uniformCovers normal weak = false := by
  simp [uniformCovers,complete]

theorem a_star_premise_is_outside_the_new_rule (normal weak : Edge)
    (star : normal.1.tail = .star) : uniformCovers normal weak = false := by
  simp [uniformCovers,star]

theorem may_outputs_are_outside_the_new_rule (normal weak : Edge)
    (may : weak.2.ap.tail = .may) : uniformCovers normal weak = false := by
  simp [uniformCovers,may]

theorem backward_behavior_is_unchanged (edges : List Edge) :
    compact false edges = edges := rfl

theorem a_normal_witness_stays_in_the_final_basis
    (edges : List Edge) (normal : Edge) (member : normal ∈ edges)
    (complete : normal.2.demand = false) : normal ∈ compact true edges := by
  have noCover : ∀ e, uniformCovers e normal = false :=
    fun e => a_normal_provider_is_never_removed e normal complete
  simp [compact,member,noCover]

theorem nothing_is_removed_without_a_retained_normal_witness
    (edges : List Edge) (weak : Edge) (member : weak ∈ edges)
    (removed : weak ∉ compact true edges) :
    ∃ normal ∈ edges, uniformCovers normal weak = true ∧
      normal.2.demand = false := by
  have yes : (edges.any fun n => uniformCovers n weak) = true := by
    by_cases h : (edges.any fun n => uniformCovers n weak) = true
    · exact h
    · have no : (edges.any fun n => uniformCovers n weak) = false := by
        cases eqn : edges.any (fun n => uniformCovers n weak) <;> simp_all
      apply False.elim
      apply removed
      simp [compact,member,no]
  rcases List.any_eq_true.mp yes with ⟨normal,inList,covered⟩
  refine ⟨normal,inList,covered,?_⟩
  by_cases demanded : normal.2.demand = false
  · exact demanded
  · cases d : normal.2.demand <;> simp_all [uniformCovers]

/-- A complete NORMAL uniform cone contains every point in the covered
    NE cone. The suffix witness is executable concatenation, not a stored
    unbounded cross-call evidence object. -/
theorem suffix_prefix_composition (pre mid suffix : Path)
    (accepted : dropHead pre mid = some suffix) (rest : Path) :
    dropHead pre (mid ++ rest) = some (suffix ++ rest) := by
  induction pre generalizing mid suffix with
  | nil =>
    simp only [dropHead] at accepted
    cases accepted
    rfl
  | cons field pre ih =>
    cases mid with
    | nil => simp [dropHead] at accepted
    | cons next mid =>
      simp only [dropHead] at accepted
      split at accepted
      · rename_i same
        simp only [List.cons_append,dropHead,same,ite_true]
        exact ih mid suffix accepted
      · simp at accepted

theorem uniform_provider_contains_every_covered_ne_point
    (pre head suffix rest : Path)
    (covered : dropHead pre head = some suffix) :
    ∃ normalSuffix : Path,
      dropHead pre (head ++ rest) = some normalSuffix ∧
      admits .must [] normalSuffix = true := by
  refine ⟨suffix ++ rest,suffix_prefix_composition pre head suffix covered rest,?_⟩
  cases shape : suffix ++ rest <;> rfl

theorem executable_coverage_constructs_the_point_witness
    (normal weak : Edge) (covered : uniformCovers normal weak = true)
    (rest : Path) :
    ∃ normalSuffix : Path,
      dropHead normal.2.ap.path (weak.2.ap.path ++ rest) = some normalSuffix ∧
      admits .must [] normalSuffix = true := by
  unfold uniformCovers at covered
  cases shape : dropHead normal.2.ap.path weak.2.ap.path with
  | none => simp [shape] at covered
  | some extra =>
    exact uniform_provider_contains_every_covered_ne_point _ _ _ rest shape

def sampleNormal : Edge :=
  (data p 1 .must,val (data ret 0 .must))
def sampleNE : Edge :=
  (data p 1 .must,val (data ret 2 .ne) true)

theorem the_counterexample_cut_is_removed_by_its_uniform_reader :
    compact true [sampleNE,sampleNormal] = [sampleNormal] := by decide

theorem either_arrival_order_has_the_same_basis :
    compact true [sampleNE,sampleNormal] = compact true [sampleNormal,sampleNE] := by decide

theorem a_normal_star_result_cannot_remove_the_ne_cut :
    uniformCovers (sampleNormal.1,val (data ret 0 .star)) sampleNE = false := by decide

theorem different_premises_do_not_borrow_uniformity :
    uniformCovers ({sampleNormal.1 with path := []},sampleNormal.2) sampleNE = false := by decide

theorem concrete_mark_and_cleaner_rows_remain_outside_the_new_rule :
    uniformCovers
      ({sampleNormal.1 with mark := some t},{sampleNormal.2 with ap := {sampleNormal.2.ap with mark := some t}})
      ({sampleNE.1 with mark := some t},{sampleNE.2 with ap := {sampleNE.2.ap with mark := some t}}) = false := by decide

theorem the_older_wrapper_normal_reader_is_retained :
    compact true [(childExact.seed.ap,(val (ap p [3] .exact)))] =
      [(childExact.seed.ap,(val (ap p [3] .exact)))] := by decide

end NormalUniformNE

#print axioms NormalUniformNE.protected_ne_is_never_removed
#print axioms NormalUniformNE.a_normal_provider_is_never_removed
#print axioms NormalUniformNE.a_star_premise_is_outside_the_new_rule
#print axioms NormalUniformNE.may_outputs_are_outside_the_new_rule
#print axioms NormalUniformNE.backward_behavior_is_unchanged
#print axioms NormalUniformNE.a_normal_witness_stays_in_the_final_basis
#print axioms NormalUniformNE.nothing_is_removed_without_a_retained_normal_witness
#print axioms NormalUniformNE.suffix_prefix_composition
#print axioms NormalUniformNE.uniform_provider_contains_every_covered_ne_point
#print axioms NormalUniformNE.executable_coverage_constructs_the_point_witness
#print axioms NormalUniformNE.the_counterexample_cut_is_removed_by_its_uniform_reader
#print axioms NormalUniformNE.either_arrival_order_has_the_same_basis
#print axioms NormalUniformNE.a_normal_star_result_cannot_remove_the_ne_cut
#print axioms NormalUniformNE.different_premises_do_not_borrow_uniformity
#print axioms NormalUniformNE.concrete_mark_and_cleaner_rows_remain_outside_the_new_rule
#print axioms NormalUniformNE.the_older_wrapper_normal_reader_is_retained
