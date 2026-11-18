import ScopedCold
import LateScopedCold
import ScopedProof
import HeadControls
namespace ScopedBounds
open ScopedBody NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

theorem scoped_keys_reference_only_existing_queries_and_groups
    (run k : Nat) (rows : List Row) (saved : List ScopedBody.Saved) (as : List Offered)
    (current : List ScopedCore.Edge) (key : Ap × Nat)
    (inside : key ∈ certifyMarks run k rows saved as current) :
    ∃ q ∈ queries run k false rows saved as,
      key.1=q.ap ∧ key.2 ∈ ScopedCore.existingMarks current q := by
  unfold certifyMarks at inside
  split at inside
  · cases inside
  · rcases List.mem_flatMap.mp inside with ⟨q,hq,member⟩
    rcases List.mem_map.mp member with ⟨m,hm,eq⟩
    subst key
    exact ⟨q,hq,rfl,ScopedCore.output_cell_has_an_existing_NORMAL_group current q _ m hm⟩

theorem only_two_sparse_cells_are_added_in_the_new_case :
    ScopedCold.s3.complete.length=1 ∧ ScopedCold.s3.services.length=2 ∧
    ScopedCold.s3.services.all (fun key => key.1.tail==.exact && key.2==2)=true := by decide +kernel

theorem no_V_summary_archive_or_new_NORMAL_rows_are_created :
    ScopedCold.s3.saved.length=6 ∧
    ScopedCold.s3.saved.all (fun n => n.edge.2.ap.mark != some ScopedBody.extraMark)=true ∧
    ScopedCold.s3.data.raw.all (fun n => n.2.ap.mark != some ScopedBody.extraMark)=true := by decide +kernel

def bounded (run : Nat) (old next : ScopedBody.State) : Bool :=
  next.data.domains.all fun a => old.rows.all fun row =>
    (prepare run (limit run) (run%2==0) row old.rows old.saved a).all fun q =>
      decide (q.ap.path.length≤limit run ∧ q.ap.path.length≤row.entry.path.length+1)

theorem every_prepared_family_keeps_both_input_caps :
    bounded 2 ScopedCold.s1 ScopedCold.s2=true ∧ bounded 3 ScopedCold.s2 ScopedCold.s3=true := by decide +kernel

theorem C5_keeps_its_paired_output_cap
    (run k : Nat) (back : Bool) (as : List Offered) (raw : Ap) (c : Value)
    (row : Row) (out : Ap × Value)
    (ok : HeadPolicy.restrictOne run k back as raw c row=some out) :
    out.2.ap.path.length≤min k (row.exit.path.length+1) :=
  HeadControls.C5_output_bound_is_unchanged run k back as raw c row out ok

theorem already_emitted_Target_is_never_cancelled
    (test : α → Bool) (advance : α → α) (fuel : Nat) (data : α) (seen : test data=true) :
    UniformSticky.seenDemand test advance fuel data=true :=
  UniformSticky.an_emitted_target_is_never_erased test advance fuel data seen

theorem late_receipts_preserve_the_earlier_target_and_still_stop :
    LateScopedCold.s3.observationActive=true ∧ LateScopedCold.s5.observationActive=false ∧
    LateScopedBody.stopped 7 LateScopedCold.s7=true := by decide +kernel

end ScopedBounds
