import HeadSafety
import UniformStrictDifferent
namespace HeadStrictDifferent
open NonEmptyPolicy NonEmptyRestriction DifferentUniformReply
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
def prepare (run k : Nat) (back : Bool) (row : Row) (rows : List Row)
    (records : List Edge) (actual : Offered) : List Seed :=
  let base := HeadPolicy.emit run k back row.entry actual
  let children := if (row.entry.tail == .may || row.entry.tail == .ne) && !base.isEmpty then
    (nextFields back row rows records).flatMap fun field =>
      let child := {row.entry with path := row.entry.path ++ [field],tail := .may}
      (HeadPolicy.emit run k back child actual).filter fun q =>
        q.ap.path == child.path && decide (q.ap.path.length ≤ row.entry.path.length+1)
  else []
  (base ++ children).eraseDups

def publish (_run k : Nat) (_back : Bool) (row : Row) (qs : List Seed)
    (q : Seed) (c : Value) : Option Edge := do
  if qs.contains q then
    let normalized := normalize q.ap c
    let selected ← intersectExit normalized.2 row.exit
    return normalize normalized.1 (cut (min k (row.exit.path.length+1)) selected)
  else none

def candidates (run k : Nat) (back : Bool) (rows : List Row) (records : List Edge)
    (offers : List Offered) : List Edge :=
  (offers.flatMap fun a => rows.flatMap fun row =>
    let qs := prepare run k back row rows records a
    qs.flatMap fun q => (if back then reverseBody q else forwardBody q).filterMap
      (publish run k back row qs q)).eraseDups

def forward (run k : Nat) (st : State) : State := Id.run do
  let offers := (if st.permissionB then [rootActual] else []) ++
    (if st.permissionA then [fieldActual] else [])
  let raw := if run == 1 then startEdges else candidates run k false st.rows st.records offers
  let current := canonicalEdges raw
  let bp := if st.permissionB then UniformStrictDifferent.replies st.records current rootActual else []
  let ap := if st.permissionA then UniformStrictDifferent.replies st.records current fieldActual else []
  let observations := bp.map (terminal 0) ++ ap.map (terminal 1)
  return ⟨outputRows raw,save st.records current,
    observations.any TargetZeroKernel.continuationRelevant,
    st.permissionB,st.permissionA,
    (st.reports ++ TargetZeroKernel.collectReports [0] observations).eraseDups,
    (if bp.any (·.demand) then [0] else []) ++ (if ap.any (·.demand) then [1] else [])⟩


def backward (run k : Nat) (st : State) : State := Id.run do
  let current := candidates run k true st.rows st.records [returnActual]
  let all := st.records.filterMap savedBackward ++ current.map (·.2)
  let b := st.sinkSeeds.contains 0 && all.any (permission [])
  let a := st.sinkSeeds.contains 1 && all.any (permission [f])
  return ⟨outputRows current,st.records,b || a,b,a,st.reports,st.sinkSeeds⟩

def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)

theorem prepare_eq_old (run k : Nat) (back : Bool) (row : Row) (rows : List Row)
    (records : List Edge) (a : Offered) (empty : a.ap.e = []) :
    prepare run k back row rows records a = DifferentUniformReply.prepare run k back row rows records a := by
  simp only [prepare,DifferentUniformReply.prepare,
    HeadPolicy.empty_actual_E_is_exactly_the_old_policy run k back _ a empty]

theorem candidates_eq_old (run k : Nat) (back : Bool) (rows : List Row) (records : List Edge)
    (as : List Offered) (empty : ∀ a ∈ as, a.ap.e = []) :
    candidates run k back rows records as = DifferentUniformReply.candidates run k back rows records as := by
  unfold candidates DifferentUniformReply.candidates
  congr 1
  apply HeadSafety.flatMap_congr
  intro a inside
  simp only [prepare_eq_old run k back _ rows records a (empty a inside)]
  rfl

theorem forward_eq_old (run k : Nat) (st : State) : forward run k st = UniformStrictDifferent.forward run k st := by
  let as := (if st.permissionB then [rootActual] else []) ++ (if st.permissionA then [fieldActual] else [])
  have empty : ∀ a ∈ as, a.ap.e = [] := by
    apply HeadSafety.empty_members
    cases hp : st.permissionB <;> cases hf : st.permissionA <;>
      simp [as,hp,hf,rootActual,fieldActual,pt]
  have same := candidates_eq_old run k false st.rows st.records as empty
  dsimp only [as] at same
  simp only [forward,UniformStrictDifferent.forward,same]

theorem backward_eq_old (run k : Nat) (st : State) : backward run k st = DifferentUniformReply.backward run k st := by
  have empty : ∀ a ∈ [returnActual], a.ap.e = [] := HeadSafety.empty_members _ (by rfl)
  simp only [backward,DifferentUniformReply.backward,candidates_eq_old run k true st.rows st.records _ empty]

theorem step_eq_old (run : Nat) (st : State) : step run st = UniformStrictDifferent.step run st := by
  simp only [step,UniformStrictDifferent.step,forward_eq_old,backward_eq_old]

theorem history_eq_old (run : Nat) : history run = UniformStrictDifferent.history run := by
  induction run with
  | zero => rfl
  | succ n ih =>
      change step (n+1) (history n) = UniformStrictDifferent.step (n+1) (UniformStrictDifferent.history n)
      rw [ih,step_eq_old]

theorem stop_run5_and_both_observations : (history 5).rows = [] ∧
    (history 5).rootDemand = false ∧ (history 5).reports = [0,1] := by
  rw [history_eq_old]
  exact UniformStrictDifferent.cold_run5_naturally_stops

theorem uncapped_no_revival (n : Nat) : history (n+6) = UniformStrictDifferent.idle := by
  rw [history_eq_old]
  exact UniformStrictDifferent.uncapped_no_revival n
end HeadStrictDifferent
