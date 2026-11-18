import HeadSafety
import UniformStrictExact
namespace HeadStrictExact
open NonEmptyPolicy NonEmptyRestriction ProvisionalMustCycle
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
def candidatesForOffers (run limit : Nat) (back : Bool) (rows : List Row)
    (actuals : List Offered) : List Edge :=
  (actuals.flatMap fun a => rows.flatMap fun row =>
    (HeadPolicy.emit run limit back row.entry a).flatMap fun q =>
      (if back then reverseProduce q else produce q).toList.filterMap fun c =>
        HeadPolicy.restrictOne run limit back [a] q.ap c row).eraseDups

def currentCandidates (run limit : Nat) (back : Bool) (rows : List Row) : List Edge :=
  candidatesForOffers run limit back rows
    (if back then [returnActual] else [rootActual,fieldActual])


def forward (run limit : Nat) (st : State) : State := Id.run do
  let offers := (if st.permissionRoot then [rootActual] else []) ++
    (if st.permissionField then [fieldActual] else [])
  let current := if run == 1 then [startRecord]
    else candidatesForOffers run limit false st.rows offers
  let rootPacket := if st.permissionRoot then UniformStrictExact.replies st.records current rootActual else []
  let fieldPacket := if st.permissionField then UniformStrictExact.replies st.records current fieldActual else []
  let observations := rootPacket.map (terminal 0) ++ fieldPacket.map (terminal 1)
  let reports := (st.reports ++ TargetZeroKernel.collectReports [0] observations).eraseDups
  let seeds := ((if rootPacket.any (·.demand) then [0] else []) ++
    (if fieldPacket.any (·.demand) then [1] else []))
  return ⟨outputRows current,save st.records current,hasDemand observations,
    st.permissionRoot,st.permissionField,reports,seeds⟩



def backward (run limit : Nat) (st : State) : State := Id.run do
  let current := currentCandidates run limit true st.rows
  let all := reverseReplies st.records current
  let rootPermission := st.sinkSeeds.contains 0 && all.any (producesPermission [])
  let fieldPermission := st.sinkSeeds.contains 1 && all.any (producesPermission [f])
  -- Accepted reversed producers yield ZERO, then the existing ZERO->Target
  -- conversion. Both rows use (entry=Target,exit=ZERO) at the root.
  return ⟨outputRows current,st.records,rootPermission || fieldPermission,
    rootPermission,fieldPermission,st.reports,st.sinkSeeds⟩

def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)
theorem candidates_eq_old (run k : Nat) (back : Bool) (rows : List Row)
    (as : List Offered) (empty : ∀ a ∈ as, a.ap.e = []) :
    candidatesForOffers run k back rows as = ProvisionalMustCycle.candidatesForOffers run k back rows as := by
  unfold candidatesForOffers ProvisionalMustCycle.candidatesForOffers
  congr 1
  apply HeadSafety.flatMap_congr
  intro a inside
  have one : ∀ x ∈ [a], x.ap.e = [] := by
    intro x member
    simp only [List.mem_singleton] at member
    subst x
    exact empty a inside
  simp only [HeadPolicy.empty_actual_E_is_exactly_the_old_policy run k back _ a (empty a inside),
    HeadSafety.empty_actuals_C5_is_unchanged run k back [a] _ _ _ one]

theorem current_eq_old (run k : Nat) (back : Bool) (rows : List Row) :
    currentCandidates run k back rows = ProvisionalMustCycle.currentCandidates run k back rows := by
  unfold currentCandidates ProvisionalMustCycle.currentCandidates
  apply candidates_eq_old
  apply HeadSafety.empty_members
  cases back <;> rfl

theorem forward_eq_old (run k : Nat) (st : State) : forward run k st = UniformStrictExact.forward run k st := by
  let as := (if st.permissionRoot then [rootActual] else []) ++
    (if st.permissionField then [fieldActual] else [])
  have empty : ∀ a ∈ as, a.ap.e = [] := by
    apply HeadSafety.empty_members
    cases hp : st.permissionRoot <;> cases hf : st.permissionField <;>
      simp [as,hp,hf,rootActual,fieldActual,pt]
  have same := candidates_eq_old run k false st.rows as empty
  dsimp only [as] at same
  simp only [forward,UniformStrictExact.forward,same]

theorem backward_eq_old (run k : Nat) (st : State) : backward run k st = ProvisionalMustCycle.backward run k st := by
  simp only [backward,ProvisionalMustCycle.backward,current_eq_old run k true st.rows]

theorem step_eq_old (run : Nat) (st : State) : step run st = UniformStrictExact.step run st := by
  simp only [step,UniformStrictExact.step,forward_eq_old,backward_eq_old]

theorem history_eq_old (run : Nat) : history run = UniformStrictExact.history run := by
  induction run with
  | zero => rfl
  | succ n ih =>
      change step (n+1) (history n) = UniformStrictExact.step (n+1) (UniformStrictExact.history n)
      rw [ih,step_eq_old]

theorem stop_run5_and_both_observations : (history 5).rows = [] ∧
    (history 5).rootDemand = false ∧ (history 5).reports = [0,1] := by
  rw [history_eq_old]
  exact UniformStrictExact.cold_run5_naturally_stops

theorem uncapped_no_revival (n : Nat) : history (n+6) = UniformStrictExact.idle := by
  rw [history_eq_old]
  exact UniformStrictExact.uncapped_no_revival n
end HeadStrictExact
