import ExactSupport

namespace ExactSupportCycle
open NonEmptyPolicy NonEmptyRestriction ProvisionalMustCycle

def wrap (v : Value) : ExactSupport.Item :=
  ⟨⟨0,[0],0,v.ap,v.h⟩,v.demand⟩
def unwrap (x : ExactSupport.Item) : Value := ⟨x.key.ap,x.demand,x.key.h⟩
def foldValues (xs : List Value) : List Value :=
  (ExactSupport.absorb (xs.map wrap)).map unwrap

theorem value_roundtrip (v : Value) : unwrap (wrap v) = v := by cases v; rfl

theorem folded_native_field_packet :
    foldValues (ProvisionalMustCycle.replies [rootRecord,fieldRecord] [] fieldActual) =
      [⟨ru,false,false⟩] := by decide

theorem solitary_provisional_record_is_not_discarded :
    foldValues (ProvisionalMustCycle.replies [rootRecord] [] fieldActual) =
      [⟨ru,true,false⟩] := by decide

theorem actual_demand_cannot_borrow_normal_record_support :
    foldValues (ProvisionalMustCycle.replies [rootRecord,fieldRecord] []
      ⟨fieldActual.ap,true⟩) = [⟨ru,true,false⟩] := by decide

theorem no_new_normal_fact_is_inferred_from_absorption :
    foldValues [⟨ru,true,false⟩] = [⟨ru,true,false⟩] ∧
    foldValues [⟨ru,true,false⟩,⟨ru,false,false⟩] = [⟨ru,false,false⟩] := by decide

/-- Only already-ready saved results form this batch. A later current reply
    does not cancel work that has already reached an observation. -/
def replies (records current : List Edge) (actual : Offered) : List Value :=
  (foldValues (records.filterMap fun e => savedForward e actual) ++
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
  let seeds := ((if rootPacket.any (·.demand) then [0] else []) ++
    (if fieldPacket.any (·.demand) then [1] else []))
  return ⟨outputRows current,save st.records current,hasDemand observations,
    st.permissionRoot,st.permissionField,reports,seeds⟩

def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)

def stopped : State := ⟨[],[rootRecord,fieldRecord],false,false,true,[0,1],[]⟩
def idle : State := ⟨[],[rootRecord,fieldRecord],false,false,false,[0,1],[]⟩

theorem cold_run1_unchanged : history 1 = s1 := by decide
theorem cold_run2_unchanged : history 2 = s2 := by decide
theorem cold_run3_unchanged : history 3 = s3 := by decide
theorem cold_run4_unchanged : history 4 = s4 := by decide
theorem cold_run5_unchanged : history 5 = s5 := by decide
theorem cold_run6_unchanged : history 6 = s6 := by decide
theorem cold_run7_naturally_stops : history 7 = stopped := by decide

theorem reports_and_both_normal_records_are_preserved :
    (history 7).reports = [0,1] ∧
    (history 7).records = [rootRecord,fieldRecord] := by decide

theorem first_empty_frontier_is_run7 :
    (history 7).rootDemand = false ∧ (history 7).rows = [] ∧
    (List.range 6).all (fun i => (history (i+1)).rootDemand) = true := by decide

theorem no_extra_current_queries_at_run7 :
    candidatesForOffers 7 6 false (history 6).rows [fieldActual] = [] := by decide

theorem ready_saved_basis_cannot_renew_the_target (run k : Nat) (notFirst : run ≠ 1) :
    forward run k s6 = stopped := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,s6]
  simp only [first,Bool.false_eq_true,ite_false,empty_rows_have_no_candidates_for_any_offers]
  rfl

theorem forced_run8_is_idle : history 8 = idle := by decide

theorem idle_forward (run k : Nat) (notFirst : run ≠ 1) : forward run k idle = idle := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,idle]
  simp only [first,Bool.false_eq_true,ite_false,empty_rows_have_no_candidates_for_any_offers]
  rfl

theorem idle_backward (run k : Nat) : backward run k idle = idle := by
  dsimp only [backward,idle]
  rw [empty_current_demand_adds_no_queries]
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

theorem no_cut_or_new_child_query_needed :
    (history 7).rows = [] ∧
    (history 7).records.all (fun e => decide (e.1.path.length ≤ 1 ∧
      e.2.ap.path.length ≤ 1) && !e.2.demand) = true := by decide

end ExactSupportCycle
