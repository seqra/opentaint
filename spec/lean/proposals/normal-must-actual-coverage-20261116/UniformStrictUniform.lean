import UniformActual
import StrictUniform

namespace UniformStrictUniform
open NonEmptyPolicy NonEmptyRestriction ProvisionalUniformCycle
set_option maxRecDepth 32768
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
set_option maxHeartbeats 16000000

def replies (records current : List Edge) (actual : Offered) : List Value :=
  (UniformActual.filter false [] ((StrictUniform.replies records current actual).map ExactSupportCycle.wrap)).map ExactSupportCycle.unwrap


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
def stopped : State := ⟨[],completeRecords,false,true,true,[0,1],[]⟩
def idle : State := ⟨[],completeRecords,false,false,false,[0,1],[]⟩

theorem cold_run1_unchanged : history 1 = s1 := by decide
theorem cold_run2_unchanged : history 2 = s2 := by decide
theorem cold_run3_transfer_and_reports_preserved :
    (history 3).rows = s3.rows ∧ (history 3).records = s3.records ∧ (history 3).reports = s3.reports := by decide
theorem cold_run4_transfer_and_reports_preserved :
    (history 4).rows = s4.rows ∧ (history 4).records = s4.records ∧ (history 4).reports = s4.reports := by decide
theorem cold_run5_naturally_stops :
    (history 5).rows = [] ∧ (history 5).rootDemand = false ∧ (history 5).reports = [0,1] := by decide
theorem no_earlier_stop : (List.range 4).all (fun i => (history (i+1)).rootDemand) = true := by decide
theorem reports_and_normal_records_preserved :
    (history 5).reports = [0,1] ∧ (history 5).records = completeRecords := by decide
theorem stopped_frontier_is_empty : (history 5).rows = [] ∧ (history 5).rootDemand = false := by decide

theorem forced_run6_is_idle : history 6 = idle := by decide

theorem idle_forward (run k : Nat) (notFirst : run ≠ 1) : forward run k idle = idle := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,idle]
  simp only [first,Bool.false_eq_true,ite_false,empty_demand_creates_no_new_queries]
  rfl
theorem idle_backward (run k : Nat) : backward run k idle = idle := by
  dsimp only [backward,currentCandidates,idle]
  rw [empty_demand_creates_no_new_queries]
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

end UniformStrictUniform
