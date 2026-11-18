import Restriction
import TargetZeroKernel

/- Fully analyzed synthetic code plus one unary conditional producer.
   Two NORMAL inputs: T uniformly at p and uniformly only at p.f.
   No loop, recursion, cleaner, pass rule, alias or intrinsic MAY producer.
   Native MUST replay has its existing definite/provisional lanes. -/
namespace ProvisionalMustCycle
open NonEmptyPolicy NonEmptyRestriction
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

def f : Nat := 1
def t : Nat := 1
def u : Nat := 2
def p : Nat := 0
def ret : Nat := 1
def pt (path : Path) (tail : Tail) : Ap := ⟨p,path,tail,some t,[],[]⟩
def ru : Ap := ⟨ret,[],.exact,some u,[],[]⟩
def rootActual : Offered := ⟨pt [] .must,false⟩
def fieldActual : Offered := ⟨pt [f] .must,false⟩
def returnActual : Offered := ⟨ru,false⟩
abbrev Edge := Ap × Value
def rootRecord : Edge := (pt [] .must,⟨ru,false,false⟩)
def fieldRecord : Edge := (pt [f] .must,⟨ru,false,false⟩)
def startRecord : Edge := (pt [] .star,⟨ru,true,false⟩)
def fieldDemandRecord : Edge := (pt [f] .star,⟨ru,true,false⟩)

/-- Ordinary producer: CM(p.MAY,T) generates U exactly at fresh r;
    the following ordinary return moves r to ret. No suffix is copied. -/
def produce (q : Seed) : Option Value :=
  if q.ap.base == p && q.ap.mark == some t then
    some ⟨ru,q.demand,false⟩ else none

/-- Reversal of the configured producer: exact U requires MAY/T at p.
    A MAY requirement is DEMAND, independently of the exact-U input layer. -/
def reverseProduce (q : Seed) : Option Value :=
  if q.ap == ru then some ⟨pt [] .may,true,false⟩ else none

def mustCovers (actual required : Ap) : Bool :=
  actual.base == required.base && actual.mark == required.mark &&
  actual.tail == .must && (dropHead actual.path required.path).isSome

def mustOverlaps (actual required : Ap) : Bool :=
  actual.base == required.base && actual.mark == required.mark &&
  actual.tail == .must &&
  ((dropHead actual.path required.path).isSome ||
   (dropHead required.path actual.path).isSome)

/-- Direct saved MUST read: native matching admits a residual uniform child,
    then commits pending demotion after the ordinary call suffix. -/
def savedForward (record : Edge) (actual : Offered) : Option Value :=
  if record.1.tail == .must && mustOverlaps actual.ap record.1 then
    some {record.2 with demand := actual.demand || !mustCovers actual.ap record.1}
  else none

/-- CURRENT MUST application is definite. It has no saved provisional lane. -/
def currentForward (edge : Edge) (actual : Offered) : Option Value :=
  let accepts := if edge.1.tail == .must then mustCovers actual.ap edge.1
    else actual.ap.base == p && actual.ap.mark == some t &&
      ((dropHead edge.1.path actual.ap.path).isSome ||
       (actual.ap.tail == .must && (dropHead actual.ap.path edge.1.path).isSome))
  if accepts then some {edge.2 with demand := actual.demand || edge.2.demand}
  else none

/-- Existing native reverse-MUST/exact read; the old MUST becomes MAY. -/
def savedBackward (record : Edge) (actual : Offered) : Option Value :=
  if record.1.tail == .must && actual.ap == record.2.ap then
    some ⟨{record.1 with tail := .may},true,false⟩ else none

def candidatesForOffers (run limit : Nat) (back : Bool) (rows : List Row)
    (actuals : List Offered) : List Edge :=
  (actuals.flatMap fun a => rows.flatMap fun row =>
    (emit run limit back row.entry a).flatMap fun q =>
      (if back then reverseProduce q else produce q).toList.filterMap fun c =>
        restrictOne run limit back [a] q.ap c row).eraseDups

def currentCandidates (run limit : Nat) (back : Bool) (rows : List Row) : List Edge :=
  candidatesForOffers run limit back rows
    (if back then [returnActual] else [rootActual,fieldActual])

def seedRows : List Row := [⟨ru,pt [] .star⟩]
def outputRows (edges : List Edge) : List Row :=
  (edges.filterMap fun e => if e.2.demand then some ⟨e.2.ap,e.1⟩ else none).eraseDups
def save (previous current : List Edge) : List Edge :=
  (previous ++ current.filter (fun e => !e.2.demand)).eraseDups

/-- Same-layer exact packet union. Neither NORMAL nor DEMAND upgrades or
    erases the other support. No MUST/MUST descendant is present here. -/
def replies (records current : List Edge) (actual : Offered) : List Value :=
  ((records.filterMap fun e => savedForward e actual) ++
    (current.filterMap fun e => currentForward e actual)).eraseDups

def reverseReplies (records current : List Edge) : List Value :=
  ((records.filterMap fun e => savedBackward e returnActual) ++ current.map (·.2)).eraseDups

def producesPermission (path : Path) (v : Value) : Bool :=
  v.ap.base == p && v.ap.mark == some t &&
    match dropHead v.ap.path path with
    | some rest => admits v.ap.tail v.ap.e rest
    | none => (dropHead path v.ap.path).isSome

def terminal (id : Nat) (v : Value) : TargetZeroKernel.Summary :=
  TargetZeroKernel.forwardSinkTarget 0 .zero (if v.demand then .demand else .normal) id

def hasDemand (all : List TargetZeroKernel.Summary) : Bool :=
  all.any TargetZeroKernel.continuationRelevant

structure State where
  rows : List Row
  records : List Edge
  rootDemand : Bool
  permissionRoot : Bool
  permissionField : Bool
  reports : List Nat
  sinkSeeds : List Nat
  deriving DecidableEq, BEq, Repr

def initial : State := ⟨[],[],false,true,true,[],[]⟩

/-- Calls replay persisted records before lookup, even if rows is empty.
    Root Target guidance admits ZERO; the existing seed index selects checks.
    NORMAL records and reports persist after their fresh permission ends. -/
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

def backward (run limit : Nat) (st : State) : State := Id.run do
  let current := currentCandidates run limit true st.rows
  let all := reverseReplies st.records current
  let rootPermission := st.sinkSeeds.contains 0 && all.any (producesPermission [])
  let fieldPermission := st.sinkSeeds.contains 1 && all.any (producesPermission [f])
  -- Accepted reversed producers yield ZERO, then the existing ZERO->Target
  -- conversion. Both rows use (entry=Target,exit=ZERO) at the root.
  return ⟨outputRows current,st.records,rootPermission || fieldPermission,
    rootPermission,fieldPermission,st.reports,st.sinkSeeds⟩

def limit (run : Nat) : Nat := max 1 (run-1)
def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)

def s1 : State := ⟨seedRows,[],true,true,true,[],[0,1]⟩
def s2 : State := ⟨[⟨pt [] .may,ru⟩],[],true,true,true,[],[0,1]⟩
def s3 : State := ⟨[⟨ru,pt [f] .star⟩],[rootRecord],true,true,true,[0],[0,1]⟩
def s4 : State := ⟨[⟨pt [f] .may,ru⟩],[rootRecord],true,true,true,[0],[0,1]⟩
def s5 : State := ⟨[],[rootRecord,fieldRecord],true,true,true,[0,1],[1]⟩
def s6 : State := ⟨[],[rootRecord,fieldRecord],true,false,true,[0,1],[1]⟩

theorem cold_run1 : history 1 = s1 := by decide
theorem cold_run2 : history 2 = s2 := by decide
theorem cold_run3 : history 3 = s3 := by decide
theorem cold_run4 : history 4 = s4 := by decide
theorem cold_run5 : history 5 = s5 := by decide
theorem cold_run6 : history 6 = s6 := by decide

theorem definite_and_provisional_native_reads :
    savedForward rootRecord rootActual = some ⟨ru,false,false⟩ ∧
    savedForward rootRecord fieldActual = some ⟨ru,true,false⟩ ∧
    savedForward fieldRecord fieldActual = some ⟨ru,false,false⟩ := by decide

theorem complete_field_reply_keeps_both_supports :
    replies s5.records [] fieldActual = [⟨ru,true,false⟩,⟨ru,false,false⟩] := by decide

theorem backward_views_renew_the_remaining_field_permission :
    reverseReplies s5.records [] = [⟨pt [] .may,true,false⟩,⟨pt [f] .may,true,false⟩] ∧
    (backward 6 5 s5).permissionRoot = false ∧
    (backward 6 5 s5).permissionField = true := by decide

theorem empty_current_demand_adds_no_queries (run k : Nat) (back : Bool) :
    currentCandidates run k back [] = [] := by cases back <;> rfl

theorem empty_rows_have_no_candidates_for_any_offers (run k : Nat) (back : Bool)
    (offers : List Offered) : candidatesForOffers run k back [] offers = [] := by
  simp [candidatesForOffers]
  induction offers with
  | nil => rfl
  | cons a rest ih => simpa using ih

theorem every_later_forward_is_fixed (run k : Nat) (notFirst : run ≠ 1) :
    forward run k s6 = s6 := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,s6]
  simp only [first,Bool.false_eq_true,ite_false,empty_rows_have_no_candidates_for_any_offers]
  rfl

theorem every_later_backward_is_fixed (run k : Nat) : backward run k s6 = s6 := by
  dsimp only [backward,s6]
  rw [empty_current_demand_adds_no_queries]
  rfl

theorem arbitrary_later_step_is_fixed (n : Nat) : step (n+7) s6 = s6 := by
  unfold step
  split
  · exact every_later_backward_is_fixed _ _
  · exact every_later_forward_is_fixed _ _ (by omega)

theorem all_later_completed_iterations (n : Nat) : history (n+6) = s6 := by
  induction n with
  | zero => exact cold_run6
  | succ n ih =>
      change step (n+7) (history (n+6)) = s6
      rw [ih]
      exact arbitrary_later_step_is_fixed n

theorem root_target_repeats_without_an_iteration_limit (n : Nat) :
    (history (n+6)).rootDemand = true := by
  rw [all_later_completed_iterations]; rfl

theorem local_data_demand_is_already_empty (n : Nat) :
    (history (n+6)).rows = [] := by rw [all_later_completed_iterations]; rfl

theorem all_required_findings_are_already_normal (n : Nat) :
    (history (n+6)).reports = [0,1] := by rw [all_later_completed_iterations]; rfl

theorem steady_replay_has_no_field_cut (k : Nat) :
    NonEmptyRestriction.cut k ⟨ru,true,false⟩ = ⟨ru,true,false⟩ := by
  simp [NonEmptyRestriction.cut,ru]

theorem saved_replay_does_not_depend_on_an_admission_or_child_plan (run k : Nat) :
    hasDemand ((replies s5.records (currentCandidates run k false []) fieldActual).map (terminal 1)) = true := by
  rw [empty_current_demand_adds_no_queries]
  decide

theorem selected_root_control_pair_accepts_the_repeated_target :
    TargetZeroKernel.entryIntersects (fun _ _ => false) .target .zero = true ∧
    TargetZeroKernel.exitIntersect (fun _ _ => none) .zero (.target .demandTarget) =
      some (.target .demandTarget) := by decide

/-- More ready NORMAL services do not retract the old direct replay offer. -/
theorem root_replay_witness_survives_additional_records (extra : List Edge) :
    (⟨ru,true,false⟩ : Value) ∈
      (rootRecord :: extra).filterMap (fun e => savedForward e fieldActual) := by
  simp only [List.filterMap_cons,definite_and_provisional_native_reads.2.1]
  exact List.mem_cons_self

theorem current_empty_demand_cannot_gate_saved_root_replay :
    savedForward rootRecord fieldActual = some ⟨ru,true,false⟩ ∧
    currentCandidates 7 6 false [] = [] := by decide

theorem no_flow_backing_or_ne_retirement_cell :
    rootRecord.1.mark ≠ rootRecord.2.ap.mark ∧
    rootRecord.1.mark.isNone = false ∧
    rootRecord.2.ap.tail ≠ .ne ∧
    (ru.tail ≠ .ne) := by decide

theorem only_field_producer_permission_is_needed_forever (n : Nat) :
    (history (n+6)).permissionRoot = false ∧
    (history (n+6)).permissionField = true := by
  rw [all_later_completed_iterations]; decide

theorem a_normal_report_does_not_cancel_the_demand_target :
    hasDemand [terminal 1 ⟨ru,false,false⟩,terminal 1 ⟨ru,true,false⟩] = true ∧
    TargetZeroKernel.collectReports [0]
      [terminal 1 ⟨ru,false,false⟩,terminal 1 ⟨ru,true,false⟩] = [1] := by decide

theorem all_native_record_endpoints_are_within_field_limit_one :
    [rootRecord,fieldRecord].all (fun e => decide (e.1.path.length ≤ 1 ∧
      e.2.ap.path.length ≤ 1) && !e.2.demand) = true := by decide

theorem source_rule_never_generates_intrinsic_may (q : Seed) (v : Value)
    (generated : produce q = some v) : v.ap.tail = .exact := by
  unfold produce at generated
  split at generated
  · cases generated; rfl
  · contradiction

theorem saved_weak_result_remains_exact_and_unprotected :
    savedForward rootRecord fieldActual = some ⟨ru,true,false⟩ ∧
    ru.tail = .exact := by decide

theorem no_completed_run_reaches_empty_continuation (n : Nat) :
    (history (n+1)).rootDemand = true := by
  by_cases early : n < 5
  · have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst n <;> decide
  · have index : n+1 = (n-5)+6 := by omega
    rw [index]
    exact root_target_repeats_without_an_iteration_limit (n-5)

end ProvisionalMustCycle
