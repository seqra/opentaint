import DefiniteSupport

namespace DefiniteUniformCycle
open NonEmptyPolicy NonEmptyRestriction ProvisionalUniformCycle

def replies (records current : List Edge) (actual : Offered) : List Value :=
  (DefiniteReplySupport.foldValues (records.filterMap fun e => savedForward e actual) ++
    current.filterMap (fun e => currentForward e actual)).eraseDups

def forward (run limit : Nat) (st : State) : State := Id.run do
  let offers := (if st.permissionRoot then [rootActual] else []) ++
    (if st.permissionField then [fieldActual] else [])
  let current := if run == 1 then [startRecord]
    else candidatesForOffers run limit false st.rows offers
  let rootPacket := if st.permissionRoot then replies st.records current rootActual else []
  let fieldPacket := if st.permissionField then replies st.records current fieldActual else []
  let observations := rootPacket.map (terminal 0) ++ fieldPacket.map (terminal 1)
  let reports := (st.reports ++ TargetZeroKernel.collectReports [0] observations).eraseDups
  -- Existing sink seed permission, separate from the anonymous Target label.
  let seeds := ((if rootPacket.any (·.demand) then [0] else []) ++
    (if fieldPacket.any (·.demand) then [1] else []))
  return ⟨outputRows current, save st.records current, hasDemand observations,
    st.permissionRoot,st.permissionField,reports,seeds⟩


def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)

def stopped : State := ⟨[],completeRecords,false,false,true,[0,1],[]⟩
def idle : State := ⟨[],completeRecords,false,false,false,[0,1],[]⟩

theorem actual_uniform_packet_keeps_normal_only :
    replies completeRecords [] fieldActual = [⟨re,false,false⟩,⟨ru,false,false⟩] := by decide

theorem additional_exact_members_are_not_required_to_close_uniform_support :
    replies [rootRecord,fieldRecord] [] fieldActual = [⟨ru,false,false⟩] := by decide

theorem actual_demand_cannot_borrow_normal_record_support :
    replies completeRecords [] ⟨fieldActual.ap,true⟩ =
      [⟨re,true,false⟩,⟨ru,true,false⟩] := by decide

theorem lone_provisional_stays_demand :
    replies [rootRecord] [] fieldActual = [⟨ru,true,false⟩] := by decide

theorem cold_run1_unchanged : history 1 = s1 := by decide
theorem cold_run2_unchanged : history 2 = s2 := by decide
theorem cold_run3_unchanged : history 3 = s3 := by decide
theorem cold_run4_unchanged : history 4 = s4 := by decide
theorem cold_run5_unchanged : history 5 = s5 := by decide
theorem cold_run6_unchanged : history 6 = s6 := by decide
theorem cold_run7_naturally_stops : history 7 = stopped := by decide

theorem reports_and_all_normal_members_are_preserved :
    (history 7).reports = [0,1] ∧ (history 7).records = completeRecords := by decide

theorem first_empty_frontier_is_run7 :
    (history 7).rootDemand = false ∧ (history 7).rows = [] ∧
    (List.range 6).all (fun i => (history (i+1)).rootDemand) = true := by decide

theorem no_extra_query_at_run7 :
    candidatesForOffers 7 6 false (history 6).rows [fieldActual] = [] := by decide

theorem ready_saved_basis_does_not_renew_target (run k : Nat) (notFirst : run ≠ 1) :
    forward run k s6 = stopped := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,s6]
  simp only [first,Bool.false_eq_true,ite_false,empty_demand_creates_no_new_queries]
  rfl

theorem forced_run8_is_idle : history 8 = idle := by decide

theorem idle_forward (run k : Nat) (notFirst : run ≠ 1) : forward run k idle = idle := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,idle]
  simp only [first,Bool.false_eq_true,ite_false,empty_demand_creates_no_new_queries]
  rfl

theorem idle_backward (run k : Nat) : backward run k idle = idle := by
  dsimp only [backward,currentCandidates,idle]
  rw [empty_demand_creates_no_new_queries]
  rfl

theorem forced_later_step_is_idle (n : Nat) : step (n+9) idle = idle := by
  unfold step
  split
  · exact idle_backward _ _
  · exact idle_forward _ _ (by omega)

theorem uncapped_no_revival (n : Nat) : history (n+8) = idle := by
  induction n with
  | zero => exact forced_run8_is_idle
  | succ n ih =>
      change step (n+9) (history (n+8)) = idle
      rw [ih]
      exact forced_later_step_is_idle n

end DefiniteUniformCycle
