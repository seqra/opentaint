import Frontier

/- A proposed admission exception, not an unrestricted STAR-inside rule.
   Precise STAR/EXACT selectors keep their existing rejection. -/
namespace BoundedRefinementBinding
open NonEmptyPolicy NonEmptyRestriction BoundedRefinementFrontier

structure Admission where
  query : Seed
  possible : Bool
  deriving DecidableEq, Repr

def uncertainDescent (limit : Nat) (d : Ap) (a : Offered) : List Admission :=
  if a.ap.tail == .star && (d.tail == .may || d.tail == .ne) &&
      marksOK d a.ap && d.base == a.ap.base &&
      decide (d.path.length ≤ limit) then
    match dropHead a.ap.path d.path with
    | some (field :: _) =>
      if a.ap.e.contains field then [] else
      let tails : List Tail := if d.tail == .may then [.exact,.star] else [.star]
      tails.map fun tail =>
        ⟨⟨{d with tail := tail,e := [],mx := []},d.mark.isSome⟩,true⟩
    | _ => []
  else []

def resumedDemand (admission : Admission) (original : Offered) (summaryD : Bool) : Bool :=
  admission.possible || original.demand || summaryD

def canComposeNormalTarget (admission : Admission) (original : Offered)
    (summaryD : Bool) : Bool := !(resumedDemand admission original summaryD)

def canonicalQuery (q : Seed) : Ap :=
  if q.ap.mark.isNone then normalAp q.ap else q.ap

/-- Frame equality stands for the existing qualified owner/ports/read-role
    scope. A binding cannot enable some other deeper current record. -/
def authorizesCurrent (admission : Admission) (ownFrame recordFrame : Nat)
    (recordPremise : Ap) : Bool :=
  ownFrame == recordFrame && decide (canonicalQuery admission.query = recordPremise)

theorem possible_admission_cannot_confirm_a_target (admission : Admission)
    (original : Offered) (summaryD : Bool) (possible : admission.possible = true) :
    resumedDemand admission original summaryD = true ∧
    canComposeNormalTarget admission original summaryD = false := by
  simp [resumedDemand,canComposeNormalTarget,possible]

def rootStar : Offered := ⟨⟨0,[],.star,some 7,[],[]⟩,false⟩
def child (tail : Tail) : Ap := ⟨0,[1],tail,some 7,[],[]⟩

theorem precise_entries_still_reject_the_ancestor_star :
    uncertainDescent 2 (child .exact) rootStar = [] ∧
    uncertainDescent 2 (child .star) rootStar = [] := by decide

theorem ne_child_is_a_bounded_possible_star_query :
    uncertainDescent 2 (child .ne) rootStar =
      [⟨⟨{child .ne with tail := .star},true⟩,true⟩] := by decide

theorem may_child_keeps_the_empty_residual_as_demand :
    uncertainDescent 2 (child .may) rootStar =
      [⟨⟨{child .may with tail := .exact},true⟩,true⟩,
       ⟨⟨{child .may with tail := .star},true⟩,true⟩] := by decide

theorem real_field_exclusions_are_respected :
    uncertainDescent 2 (child .ne)
      {rootStar with ap := {rootStar.ap with e := [1]}} = [] := by decide

theorem wrong_marks_are_not_invented :
    uncertainDescent 2 {child .ne with mark := some 8} rootStar = [] := by decide

theorem global_limit_is_respected :
    uncertainDescent 0 (child .ne) rootStar = [] := by decide

theorem guessed_exact_is_not_normal_even_from_normal_star :
    (uncertainDescent 2 (child .may) rootStar).all
      (fun admission => admission.query.demand && admission.possible) = true := by decide

def admittedF : Admission := ⟨⟨{child .ne with tail := .star},true⟩,true⟩

theorem admission_does_not_enable_a_different_current_premise :
    authorizesCurrent admittedF 1 1
      {child .ne with path := [1,2],tail := .star} = false := by decide

theorem admission_does_not_cross_owner_or_port_frames :
    authorizesCurrent admittedF 1 2 (canonicalQuery admittedF.query) = false := by decide

theorem admission_enables_only_its_own_current_query :
    authorizesCurrent admittedF 1 1 (canonicalQuery admittedF.query) = true := by decide

end BoundedRefinementBinding

#print axioms BoundedRefinementBinding.possible_admission_cannot_confirm_a_target
#print axioms BoundedRefinementBinding.precise_entries_still_reject_the_ancestor_star
#print axioms BoundedRefinementBinding.ne_child_is_a_bounded_possible_star_query
#print axioms BoundedRefinementBinding.may_child_keeps_the_empty_residual_as_demand
#print axioms BoundedRefinementBinding.real_field_exclusions_are_respected
#print axioms BoundedRefinementBinding.wrong_marks_are_not_invented
#print axioms BoundedRefinementBinding.global_limit_is_respected
#print axioms BoundedRefinementBinding.guessed_exact_is_not_normal_even_from_normal_star
#print axioms BoundedRefinementBinding.admission_does_not_enable_a_different_current_premise
#print axioms BoundedRefinementBinding.admission_does_not_cross_owner_or_port_frames
#print axioms BoundedRefinementBinding.admission_enables_only_its_own_current_query
