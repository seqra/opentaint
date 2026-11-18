import Pipeline
import Binding

/- Qualified scope/ports are fixed here. Model the proposed publication
   split only for identical-premise independent MAY/NE result rows. -/
namespace BoundedRefinementPublication
open NonEmptyPolicy NonEmptyRestriction NonEmptyCoverage AcyclicMayCycle
open BoundedRefinementPipeline BoundedRefinementBinding

abbrev Edge := Ap × Value

def dataCovers (x y : Edge) : Bool :=
  decide (x.1 = y.1) && x.2.demand == y.2.demand && x.2.h == y.2.h &&
    x.2.ap.base == y.2.ap.base && decide (x.2.ap.mark = y.2.ap.mark) &&
    decide (x.2.ap.mx = y.2.ap.mx) &&
    x.2.ap.e.isEmpty && y.2.ap.e.isEmpty && x.2.ap.tail == .may &&
    (y.2.ap.tail == .may || y.2.ap.tail == .ne) &&
    (dropHead x.2.ap.path y.2.ap.path).isSome

def visible (all : List Edge) : List Edge :=
  all.filter fun y => !(all.any fun x => decide (x ≠ y) && dataCovers x y)

def broad : Edge := (ap p [] .star,val (ap ret [] .may) true)
def fine : Edge := (ap p [] .star,val (ap ret [f] .ne) true)
def fineNormal : Edge := (ap p [] .star,val (ap ret [f] .star))

theorem callers_can_receive_just_the_may_row :
    visible [broad,fine] = [broad] := by decide

theorem callee_keeps_both_paired_refinement_rows :
    handoff [broad,fine] =
      [⟨ap ret [] .may,ap p [] .star⟩,
       ⟨ap ret [f] .ne,ap p [] .star⟩] := by decide

theorem rebuilding_callee_demand_from_publication_would_lose_a_row :
    handoff (visible [broad,fine]) =
      [⟨ap ret [] .may,ap p [] .star⟩] := by decide

theorem coarse_may_offer_still_starts_the_precise_callee_query :
    emit 4 3 true (ap ret [f] .ne) sinkNeed =
      [⟨ap ret [f] .star,false⟩] := by decide

theorem wrapper_star_offer_uses_the_explicit_possible_binding :
    uncertainDescent 3 (ap ret [f] .ne) ⟨ap ret [] .star,true⟩ =
      [⟨⟨ap ret [f] .star,false⟩,true⟩] := by decide

theorem future_normal_refinement_is_not_suppressed :
    visible [broad,fine,fineNormal] = [broad,fineNormal] := by decide

theorem protected_refinement_is_not_suppressed_by_plain_may :
    visible [broad,(fine.1,{fine.2 with h := true})] =
      [broad,(fine.1,{fine.2 with h := true})] := by decide

theorem a_different_mark_is_not_suppressed :
    visible [broad,(fine.1,{fine.2 with ap := {fine.2.ap with mark := some t}})] =
      [broad,(fine.1,{fine.2 with ap := {fine.2.ap with mark := some t}})] := by decide

theorem the_batched_visible_basis_is_arrival_independent :
    visible [fine,broad] = visible [broad,fine] := by decide

theorem visible_may_covers_the_suppressed_locations :
    coversPost [] .may [f] .nonEmpty := by
  simpa using may_prefix_covers_nonempty_descendant [] [f]

end BoundedRefinementPublication

#print axioms BoundedRefinementPublication.callers_can_receive_just_the_may_row
#print axioms BoundedRefinementPublication.callee_keeps_both_paired_refinement_rows
#print axioms BoundedRefinementPublication.rebuilding_callee_demand_from_publication_would_lose_a_row
#print axioms BoundedRefinementPublication.coarse_may_offer_still_starts_the_precise_callee_query
#print axioms BoundedRefinementPublication.wrapper_star_offer_uses_the_explicit_possible_binding
#print axioms BoundedRefinementPublication.future_normal_refinement_is_not_suppressed
#print axioms BoundedRefinementPublication.protected_refinement_is_not_suppressed_by_plain_may
#print axioms BoundedRefinementPublication.a_different_mark_is_not_suppressed
#print axioms BoundedRefinementPublication.the_batched_visible_basis_is_arrival_independent
#print axioms BoundedRefinementPublication.visible_may_covers_the_suppressed_locations
