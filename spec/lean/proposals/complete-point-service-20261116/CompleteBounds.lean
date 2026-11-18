import CompleteCold
import LateCompleteCold
import CompleteService
import HeadControls
namespace CompleteBounds
open CompletePoint CompleteService NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

-- The list reference checks a finite closure; it is not a path generator.
theorem completion_keys_are_existing_owned_queries (run k : Nat) (rows : List Row)
    (saved : List CompletePoint.Saved) (domains : List Offered) (current : List CompletePoint.Edge)
    (a : Ap) (member : a ∈ certify run k rows saved domains current) :
    ∃ q ∈ queries run k false rows saved domains, q.ap=a := by
  unfold certify at member
  split at member
  · cases member
  · rcases List.mem_map.mp member with ⟨q,inside,equal⟩
    exact ⟨q,(List.mem_filter.mp inside).1,equal⟩

theorem complete_never_adds_a_query (run k : Nat) (rows : List Row)
    (saved : List CompletePoint.Saved) (domains : List Offered) (current : List CompletePoint.Edge) :
    (certify run k rows saved domains current).length ≤ (queries run k false rows saved domains).length := by
  unfold certify
  split
  · simp
  · rw [List.length_map]
    exact List.length_filter_le _ _

theorem same_saved_native_service (back : Bool) (all : List CompletePoint.Saved) :
    views back all = ExactGuard.views back
      (all.map fun s => (⟨s.edge,s.back⟩ : ExactGuard.Saved)) := by
  simp only [views,ExactGuard.views,List.map_map]
  rfl

theorem C5_keeps_its_paired_output_bound
    (run k : Nat) (back : Bool) (as : List Offered) (raw : Ap)
    (c : Value) (row : Row) (result : Ap × Value)
    (ok : HeadPolicy.restrictOne run k back as raw c row=some result) :
    result.2.ap.path.length≤min k (row.exit.path.length+1) :=
  HeadControls.C5_output_bound_is_unchanged run k back as raw c row result ok

def ordinaryBound (run : Nat) (old next : CompletePoint.State) : Bool :=
  (next.data.domains.flatMap fun a => old.rows.flatMap fun row =>
    prepare run (limit run) (run%2==0) row old.rows old.saved a).all fun q =>
      q.ap.path.length<=limit run

theorem no_extra_global_fields_in_any_executed_repaired_run :
    ordinaryBound 2 CompleteCold.s1 CompleteCold.s2=true ∧
    ordinaryBound 3 CompleteCold.s2 CompleteCold.s3=true := by decide +kernel

theorem new_case_has_exactly_three_ready_point_keys :
    CompleteCold.s3.complete.length=3 ∧
    CompleteCold.s3.complete.all (fun a => a.tail==.exact && a.path.length<=2 && a.e.isEmpty)=true := by decide +kernel

theorem no_new_NORMAL_service_rows_are_generated_to_repair_the_case :
    CompleteCold.s3.saved.length=6 ∧
    CompleteCold.s3.saved.all (fun s => !s.edge.2.demand)=true := by decide +kernel

theorem targets_are_never_cancelled_by_a_later_ready_service
    (test : α → Bool) (advance : α → α) (fuel : Nat) (data : α)
    (already : test data=true) : UniformSticky.seenDemand test advance fuel data=true :=
  UniformSticky.an_emitted_target_is_never_erased test advance fuel data already

theorem late_completion_keeps_the_old_target_and_still_stops :
    LateCompleteCold.s3.observationActive=true ∧
    LateCompleteCold.s5.observationActive=false ∧
    LateCompletePoint.stopped 7 LateCompleteCold.s7=true := by decide +kernel

end CompleteBounds
