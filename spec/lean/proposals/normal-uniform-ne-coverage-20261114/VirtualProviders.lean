import Closure

/- If existing correlated-NORMAL precoverage omitted a redundant U row,
   reconstruct its legal current-row image transiently from the retained
   provider. Do not retain raw candidates or bypass a global/paired cut. -/
namespace UniformNEVirtual
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE UniformNEClosure

def readerRecord : Edge := (data p 2 .star,val (data ret 0 .star))
def writerRecord : Edge := (data p 0 .star,val (data ret 2 .star))
def warmRecords : List Edge := [readerRecord,writerRecord]

def projectedProvider (q : Seed) (seeds : List Seed) (row : Row)
    (provider : Edge) : Option Edge := do
  if q.ap.tail != .must || !q.ap.mark.isNone ||
      !q.ap.e.isEmpty || !q.ap.mx.isEmpty || provider.2.h ||
      !provider.1.mark.isNone || !provider.2.ap.mark.isNone ||
      !provider.1.e.isEmpty || !provider.1.mx.isEmpty ||
      !provider.2.ap.e.isEmpty || !provider.2.ap.mx.isEmpty then none else
  let output ← normalApply provider ⟨q.ap,false⟩
  if output.demand || output.ap.path.length > 2 then none else
  let admitted ← restricted 2 seeds q (val output.ap) row
  if admitted.2.demand || admitted.2.ap.tail != .must then none
  else some admitted

def transientViews (rows : List Row) (a : Offered) (prior : List Edge) : List Edge :=
  rows.flatMap fun row =>
    let commands := plan 3 2 false row a
    let seeds := commands.map Command.seed
    commands.flatMap fun q => prior.filterMap (projectedProvider q.seed seeds row)

def exactPriorImage (prior : List Edge) (q : Seed) (raw : Value) : Bool :=
  !raw.demand && prior.any fun edge =>
    decide (normalApply edge ⟨q.ap,false⟩ = some ⟨raw.ap,false⟩)

def warmCandidates : List Edge :=
  newRows3.flatMap fun row =>
    let commands := plan 3 2 false row rootUniform
    let seeds := commands.map Command.seed
    commands.flatMap fun q =>
      [moveE p ret [f,f] [] q.seed.ap,moveE p ret [] [f,f] q.seed.ap].filterMap id
        |>.filterMap fun raw =>
          if raw.ap.path.length ≤ 2 && exactPriorImage warmRecords q.seed raw then none
          else restricted 2 seeds q.seed (cut 2 raw) row

def warmViews := transientViews newRows3 rootUniform warmRecords
def warmPublished := warmCandidates.filter fun edge =>
  !(warmViews.any fun provider => uniformCovers provider edge)

theorem correlated_precoverage_alone_still_leaves_the_global_cut :
    warmCandidates.isEmpty = false ∧
    warmCandidates.all (fun edge => edge.2.demand) = true := by decide

theorem legal_uniform_views_remove_the_remaining_global_cut :
    warmPublished = [] ∧ warmViews.isEmpty = false ∧
    warmViews.all (fun edge => !edge.2.demand && edge.2.ap.tail == .must) = true := by decide

theorem original_actual_replay_with_warm_records_is_already_complete :
    replayAll warmRecords rootUniform = [rootUniform] ∧
    (replayAll warmRecords rootUniform).flatMap (replayAll warmRecords) =
      [rootUniform] := by decide

theorem a_global_cut_is_not_relabelled_as_a_normal_view :
    projectedProvider (queryF 0) [queryF 0] (rowF 0) writerRecord = none := by decide

theorem a_star_input_cannot_borrow_a_must_output :
    projectedProvider (queryF2 0) [queryF2 0] (rowF 0) readerRecord = none := by decide

theorem a_weak_reverse_view_is_not_a_normal_provider :
    projectedProvider (queryF 0) [queryF 0] (rowF 0)
      (data p 0 .star,val (data ret 0 .may) true) = none := by decide

theorem a_protected_or_mark_generating_record_cannot_be_a_flow_view :
    projectedProvider (queryF 0) [queryF 0] (rowF 0)
      (readerRecord.1,{readerRecord.2 with h := true}) = none ∧
    projectedProvider (queryF 0) [queryF 0] (rowF 0)
      (readerRecord.1,{readerRecord.2 with ap := {readerRecord.2.ap with mark := some t}}) =
        none := by decide

theorem a_concrete_initial_cannot_be_retyped_as_flow :
    projectedProvider ⟨{(queryF 0).ap with mark := some t},false⟩
      [queryF 0] (rowF 0) readerRecord = none := by decide

theorem demand_support_on_original_actuals_stays_demand :
    (normalApply readerRecord {rootUniform with demand := true}).all
      Offered.demand = true := by decide

theorem the_normal_and_weak_layer_join_is_not_changed
    (provider : Edge) (actual : Offered) (result : Offered)
    (applied : normalApply provider actual = some result)
    (inputD : actual.demand = true) : result.demand = true := by
  unfold normalApply at applied
  split at applied
  · simp at applied
  · split at applied
    · have same := Option.some.inj applied
      rw [← same]
      exact inputD
    · split at applied
      · cases m : moveE provider.1.base provider.2.ap.base provider.1.path
          provider.2.ap.path actual.ap with
        | none => simp [m] at applied
        | some value =>
          simp only [m,Option.map_some] at applied
          have same := Option.some.inj applied
          rw [← same]
          simp [inputD]
      · simp at applied

end UniformNEVirtual

#print axioms UniformNEVirtual.correlated_precoverage_alone_still_leaves_the_global_cut
#print axioms UniformNEVirtual.legal_uniform_views_remove_the_remaining_global_cut
#print axioms UniformNEVirtual.original_actual_replay_with_warm_records_is_already_complete
#print axioms UniformNEVirtual.a_global_cut_is_not_relabelled_as_a_normal_view
#print axioms UniformNEVirtual.a_star_input_cannot_borrow_a_must_output
#print axioms UniformNEVirtual.a_weak_reverse_view_is_not_a_normal_provider
#print axioms UniformNEVirtual.a_protected_or_mark_generating_record_cannot_be_a_flow_view
#print axioms UniformNEVirtual.a_concrete_initial_cannot_be_retyped_as_flow
#print axioms UniformNEVirtual.demand_support_on_original_actuals_stays_demand
#print axioms UniformNEVirtual.the_normal_and_weak_layer_join_is_not_changed
