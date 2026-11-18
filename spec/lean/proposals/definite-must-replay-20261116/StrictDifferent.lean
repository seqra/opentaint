import DefiniteMustReplay

namespace StrictDifferent
open NonEmptyPolicy NonEmptyRestriction DifferentUniformReply
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def replies (records current : List Edge) (actual : Offered) : List Value :=
  DefiniteReplySupport.foldValues (canonicalValues (
    records.filterMap (fun e => DefiniteMustReplay.saved e actual) ++
    current.filterMap (fun e => currentForward e actual)))

def forward (run k : Nat) (st : State) : State := Id.run do
  let offers := (if st.permissionB then [rootActual] else []) ++
    (if st.permissionA then [fieldActual] else [])
  let raw := if run == 1 then startEdges else candidates run k false st.rows st.records offers
  let current := canonicalEdges raw
  let bp := if st.permissionB then replies st.records current rootActual else []
  let ap := if st.permissionA then replies st.records current fieldActual else []
  let observations := bp.map (terminal 0) ++ ap.map (terminal 1)
  return ⟨outputRows raw,save st.records current,
    observations.any TargetZeroKernel.continuationRelevant,
    st.permissionB,st.permissionA,
    (st.reports ++ TargetZeroKernel.collectReports [0] observations).eraseDups,
    (if bp.any (·.demand) then [0] else []) ++ (if ap.any (·.demand) then [1] else [])⟩


def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)
def stopped : State := ⟨[],completeRecords,false,true,true,[0,1],[]⟩
def idle : State := ⟨[],completeRecords,false,false,false,[0,1],[]⟩

theorem repair_does_not_depend_on_another_reply_or_confirmed_report :
    replies [rootUniform] [] fieldActual = [] := by decide

theorem the_actual_packet_has_only_the_definite_field_results :
    replies completeRecords [] fieldActual = [v (out [f] .exact),v (out [f] .must)] := by decide

theorem a_root_only_observation_is_not_proved_by_the_repaired_packet :
    (replies completeRecords [] fieldActual).all (fun c => !c.ap.path.isEmpty) = true := by decide

theorem cold_run1_unchanged : history 1 = s1 := by decide
theorem cold_run2_unchanged : history 2 = s2 := by decide
theorem cold_run3_unchanged : history 3 = s3 := by decide
theorem cold_run4_unchanged : history 4 = s4 := by decide
theorem cold_run5_naturally_stops : history 5 = stopped := by decide
theorem no_earlier_stop : (List.range 4).all (fun i => (history (i+1)).rootDemand) = true := by decide
theorem reports_and_normal_records_preserved :
    (history 5).reports = [0,1] ∧ (history 5).records = completeRecords := by decide
theorem stopped_frontier_is_empty : (history 5).rows = [] ∧ (history 5).rootDemand = false := by decide

theorem forced_run6_is_idle : history 6 = idle := by decide

theorem idle_forward (run k : Nat) (notFirst : run ≠ 1) : forward run k idle = idle := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,idle]
  simp only [first,Bool.false_eq_true,ite_false,empty_rows_admit_nothing]
  rfl
theorem idle_backward (run k : Nat) : backward run k idle = idle := by
  dsimp only [backward,idle]
  rw [empty_rows_admit_nothing]
  rfl

theorem forced_later_step_is_idle (n : Nat) : step (n+7) idle = idle := by
  unfold step
  split
  · exact idle_backward _ _
  · exact idle_forward _ _ (by omega)
theorem uncapped_no_revival (n : Nat) : history (n+6) = idle := by
  induction n with
  | zero => exact forced_run6_is_idle
  | succ n ih =>
      change step (n+7) (history (n+6)) = idle
      rw [ih]
      exact forced_later_step_is_idle n

end StrictDifferent
