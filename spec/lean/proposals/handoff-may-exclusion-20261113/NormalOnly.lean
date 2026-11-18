import Exclusion

/- A NORMAL child row does not justify excluding every other dependence
   into that field. Saved replay is included, not skipped in this witness.
   NORMAL records retain the existing persisted-only role at handoff. -/
namespace NormalOnlyHandoffExclusion
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle HandoffMayExclusion

def original : Ap := ap p [] .star
def normalChild : Ap × Value := (original,val (ap ret [f] .star))
def broadLoss : Ap × Value := (original,val broad true)

theorem child_witness_is_really_normal_with_the_same_premise :
    move p ret [] [f] original = some normalChild.2 ∧
    normalChild.2.demand = false ∧ normalChild.1 = broadLoss.1 := by decide

theorem code_also_derives_the_other_branch_loss :
    move p ret [g] [] original = some broadLoss.2 := by decide

theorem normal_child_has_no_real_field_cut_at_run1 :
    cut 1 normalChild.2 = normalChild.2 := by decide

theorem saved_normal_reverse_answers_the_exact_offer :
    move ret p [f] [] need.ap = some (val (ap p [] .exact (some t))) := by decide

/-- A taint requirement overlaps the real source subtree p.g.MUST/T.
    This finite geometry test is enough for the reached cells. -/
def sourceOverlap (a : Ap) : Bool :=
  if a.base != actualSource.ap.base || a.mark != actualSource.ap.mark then false
  else if a.path == actualSource.ap.path then true
  else match dropHead a.path actualSource.ap.path with
    | some (field :: rest) => admits a.tail a.e (field :: rest)
    | _ => match dropHead actualSource.ap.path a.path with
      | some rest => admits actualSource.ap.tail actualSource.ap.e rest
      | _ => false

theorem replayed_point_does_not_hit_the_actual_named_source :
    sourceOverlap (ap p [] .exact (some t)) = false := by decide

theorem omitted_read_branch_would_have_the_needed_requirement :
    move ret p [] [g] need.ap = some (val (ap p [g,f] .exact (some t))) := by decide

theorem its_run2_cut_still_hits_the_real_source :
    cut 1 (val (ap p [g,f] .exact (some t))) =
      val (ap p [g] .ne (some t)) true ∧
    sourceOverlap (ap p [g] .ne (some t)) = true := by decide

theorem current_admission_remains_empty_despite_the_normal_record :
    candidate 2 1 broad [f] need = [] ∧ emit 2 1 true narrow need = [] := by decide

/-- Code paths define two different correlated relations. A true-branch
    source suffix g.f reaches result f; the NORMAL writer does not do so. -/
def readRelation (input output : Path) : Prop := input = g :: output
def writeRelation (input output : Path) : Prop := output = f :: input

theorem exact_suffix_witness_refutes_complete_branch_coverage :
    readRelation [g,f] [f] ∧ ¬ writeRelation [g,f] [f] := by
  exact ⟨rfl,by intro impossible; cases impossible⟩

theorem the_normal_writer_on_the_real_source_does_not_mark_field_root :
    move p ret [] [f] actualSource.ap =
      some (val (ap ret [f,g] .must (some t))) ∧
    ¬ ([f,g] = [f]) := by decide

theorem baseline_normal_read_provider_is_still_available_without_exclusion :
    restrictOne 2 1 true [need] (ap ret [] .exact)
      (val (ap p [g] .exact)) pair =
        some (ap ret [] .star,val (ap p [g] .star)) := by decide

theorem the_other_normal_relation_covers_the_real_sink_need :
    move p ret [g] [] actualSource.ap = some (val (ap ret [] .must (some t))) ∧
    admits .must [] [f] = true := by decide

end NormalOnlyHandoffExclusion

#print axioms NormalOnlyHandoffExclusion.child_witness_is_really_normal_with_the_same_premise
#print axioms NormalOnlyHandoffExclusion.code_also_derives_the_other_branch_loss
#print axioms NormalOnlyHandoffExclusion.normal_child_has_no_real_field_cut_at_run1
#print axioms NormalOnlyHandoffExclusion.saved_normal_reverse_answers_the_exact_offer
#print axioms NormalOnlyHandoffExclusion.replayed_point_does_not_hit_the_actual_named_source
#print axioms NormalOnlyHandoffExclusion.omitted_read_branch_would_have_the_needed_requirement
#print axioms NormalOnlyHandoffExclusion.its_run2_cut_still_hits_the_real_source
#print axioms NormalOnlyHandoffExclusion.current_admission_remains_empty_despite_the_normal_record
#print axioms NormalOnlyHandoffExclusion.exact_suffix_witness_refutes_complete_branch_coverage
#print axioms NormalOnlyHandoffExclusion.the_normal_writer_on_the_real_source_does_not_mark_field_root
#print axioms NormalOnlyHandoffExclusion.baseline_normal_read_provider_is_still_available_without_exclusion
#print axioms NormalOnlyHandoffExclusion.the_other_normal_relation_covers_the_real_sink_need
