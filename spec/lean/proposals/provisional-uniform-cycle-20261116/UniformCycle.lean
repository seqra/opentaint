import ClosedCycle

/- Fully analyzed synthetic code plus one unary conditional uniform producer.
   Two NORMAL inputs: T uniformly at p and uniformly only at p.f.
   No loop, recursion, cleaner, pass rule, alias or intrinsic MAY producer.
   Native MUST replay has its existing definite/provisional lanes. -/
namespace ProvisionalUniformCycle
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
def ru : Ap := ⟨ret,[],.must,some u,[],[]⟩
def re : Ap := {ru with tail := .exact}
def rootActual : Offered := ⟨pt [] .must,false⟩
def fieldActual : Offered := ⟨pt [f] .must,false⟩
def returnActual : Offered := ⟨{ru with tail := .may},true⟩
abbrev Edge := Ap × Value
def rootRecord : Edge := (pt [] .must,⟨ru,false,false⟩)
def fieldRecord : Edge := (pt [f] .must,⟨ru,false,false⟩)
def startRecord : Edge := (pt [] .star,⟨ru,true,false⟩)
def fieldDemandRecord : Edge := (pt [f] .star,⟨ru,true,false⟩)

/-- Ordinary producer: CM(p.MAY,T) generates U uniformly at fresh r;
    the following ordinary return moves r to ret. No suffix is copied. -/
def produce (q : Seed) : Option Value :=
  if q.ap.base == p && q.ap.mark == some t then
    some ⟨ru,q.demand,false⟩ else none

/-- Reversal of the configured producer: a U point or STAR requires MAY/T at p.
    A MAY requirement is DEMAND, independently of the U input layer. -/
def reverseProduce (q : Seed) : Option Value :=
  if q.ap.base == ret && q.ap.path == [] && q.ap.mark == some u then
    some ⟨pt [] .may,true,false⟩ else none

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

/-- Native concrete MUST read: old uniform output has a STAR read
    premise; old exact output has an EXACT premise. Both match this MAY offer.
    Old uniform input becomes MAY/DEMAND. -/
def savedBackward (record : Edge) (actual : Offered) : Option Value :=
  if record.1.tail == .must && actual.ap.base == record.2.ap.base &&
      actual.ap.path == record.2.ap.path && actual.ap.mark == record.2.ap.mark &&
      (record.2.ap.tail == .must || record.2.ap.tail == .exact) then
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

def guidance (a : Ap) : Ap :=
  if a.tail == .must then {a with tail := .may} else a

def seedRows : List Row := [⟨guidance ru,pt [] .star⟩]
def outputRows (edges : List Edge) : List Row :=
  (edges.filterMap fun e => if e.2.demand then some ⟨guidance e.2.ap,guidance e.1⟩ else none).eraseDups
def save (previous current : List Edge) : List Edge :=
  (previous ++ current.filter (fun e => !e.2.demand)).eraseDups

/-- Apply the selected exact-support absorption to each complete saved batch.
    Its guard does not erase uniform replies; retain layer-separated MUSTs. -/
def replies (records current : List Edge) (actual : Offered) : List Value :=
  (ExactSupportCycle.foldValues (records.filterMap fun e => savedForward e actual) ++
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
def rootExact : Edge := (pt [] .must,⟨re,false,false⟩)
def fieldExact : Edge := (pt [f] .must,⟨re,false,false⟩)
def completeRecords : List Edge := [rootExact,rootRecord,fieldExact,fieldRecord]
def s1 : State := ⟨seedRows,[],true,true,true,[],[0,1]⟩
def s2 : State := ⟨[⟨pt [] .may,re⟩,⟨pt [] .may,{ru with tail := .star}⟩],
  [],true,true,true,[],[0,1]⟩
def s3 : State := ⟨[⟨re,pt [f] .star⟩,⟨guidance ru,pt [f] .star⟩],
  [rootExact,rootRecord],true,true,true,[0],[0,1]⟩
def s4 : State := ⟨[⟨pt [f] .may,re⟩,⟨pt [f] .may,{ru with tail := .star}⟩],
  [rootExact,rootRecord],true,true,true,[0],[0,1]⟩
def s5 : State := ⟨[],completeRecords,true,true,true,[0,1],[1]⟩
def s6 : State := ⟨[],completeRecords,true,false,true,[0,1],[1]⟩

theorem cold_run1 : history 1 = s1 := by decide
theorem cold_run2 : history 2 = s2 := by decide
theorem cold_run3 : history 3 = s3 := by decide
theorem cold_run4 : history 4 = s4 := by decide
theorem cold_run5 : history 5 = s5 := by decide
theorem cold_run6 : history 6 = s6 := by decide

theorem native_uniform_definite_and_provisional_cells :
    savedForward rootRecord rootActual = some ⟨ru,false,false⟩ ∧
    savedForward rootRecord fieldActual = some ⟨ru,true,false⟩ ∧
    savedForward fieldRecord fieldActual = some ⟨ru,false,false⟩ := by decide

theorem selected_exact_absorption_runs_and_uniform_demand_survives :
    replies completeRecords [] fieldActual =
      [⟨ru,true,false⟩,⟨re,false,false⟩,⟨ru,false,false⟩] := by decide

theorem the_extra_point_records_do_not_fix_the_uniform_cycle :
    ExactSupportCycle.foldValues [⟨re,true,false⟩,⟨ru,true,false⟩,
      ⟨re,false,false⟩,⟨ru,false,false⟩] =
      [⟨ru,true,false⟩,⟨re,false,false⟩,⟨ru,false,false⟩] := by decide

theorem new_filter_is_inert_on_the_uniform_pair :
    ExactSupportCycle.foldValues [⟨ru,true,false⟩,⟨ru,false,false⟩] =
      [⟨ru,true,false⟩,⟨ru,false,false⟩] := by decide

theorem uniform_witness_survives_any_extra_ready_results (xs : List Value)
    (present : (⟨ru,true,false⟩ : Value) ∈ xs) :
    (⟨ru,true,false⟩ : Value) ∈ ExactSupportCycle.foldValues xs := by
  apply List.mem_map.mpr
  refine ⟨ExactSupportCycle.wrap ⟨ru,true,false⟩,?_,rfl⟩
  apply ExactSupport.unsupported_members_retained
  · exact List.mem_map.mpr ⟨⟨ru,true,false⟩,present,rfl⟩
  · decide

theorem swapped_saved_enumeration_keeps_the_demand :
    hasDemand ((replies completeRecords.reverse [] fieldActual).map (terminal 1)) = true := by decide

theorem native_reverse_uniform_record_renews_may :
    savedBackward rootRecord returnActual = some ⟨pt [] .may,true,false⟩ ∧
    savedBackward fieldRecord returnActual = some ⟨pt [f] .may,true,false⟩ := by decide

theorem empty_demand_creates_no_new_queries (run k : Nat) (back : Bool)
    (offers : List Offered) : candidatesForOffers run k back [] offers = [] := by
  simp [candidatesForOffers]
  induction offers with
  | nil => rfl
  | cons a rest ih => simpa using ih

theorem every_later_forward_is_fixed (run k : Nat) (notFirst : run ≠ 1) :
    forward run k s6 = s6 := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,s6]
  simp only [first,Bool.false_eq_true,ite_false,empty_demand_creates_no_new_queries]
  rfl

theorem every_later_backward_is_fixed (run k : Nat) : backward run k s6 = s6 := by
  dsimp only [backward,currentCandidates,s6]
  rw [empty_demand_creates_no_new_queries]
  rfl

theorem arbitrary_later_step_is_fixed (n : Nat) : step (n+7) s6 = s6 := by
  unfold step
  split
  · exact every_later_backward_is_fixed _ _
  · exact every_later_forward_is_fixed _ _ (by omega)

theorem uncapped_recurrence (n : Nat) : history (n+6) = s6 := by
  induction n with
  | zero => exact cold_run6
  | succ n ih =>
      change step (n+7) (history (n+6)) = s6
      rw [ih]
      exact arbitrary_later_step_is_fixed n

theorem root_target_repeats_forever (n : Nat) :
    (history (n+6)).rootDemand = true := by rw [uncapped_recurrence]; rfl

theorem no_current_helper_demand_remains (n : Nat) :
    (history (n+6)).rows = [] := by rw [uncapped_recurrence]; rfl

theorem both_findings_are_already_normal (n : Nat) :
    (history (n+6)).reports = [0,1] := by rw [uncapped_recurrence]; rfl

theorem only_the_field_source_is_renewed (n : Nat) :
    (history (n+6)).permissionRoot = false ∧
    (history (n+6)).permissionField = true := by rw [uncapped_recurrence]; decide

theorem the_exact_filter_guard_rejects_the_surviving_uniform_value :
    ExactSupport.eligible (ExactSupportCycle.wrap ⟨ru,true,false⟩).key = false := by decide

theorem no_uniform_ne_or_flow_backing_rule_applies :
    rootRecord.1.mark ≠ rootRecord.2.ap.mark ∧ rootRecord.1.mark.isNone = false ∧
    rootRecord.2.ap.tail ≠ .ne ∧ rootRecord.2.ap.tail ≠ .exact := by decide

theorem all_saved_geometry_fits_limit_one :
    completeRecords.all (fun e => decide (e.1.path.length ≤ 1 ∧ e.2.ap.path.length ≤ 1)
      && !e.2.demand) = true := by decide

theorem surviving_uniform_result_never_gets_field_cut (k : Nat) :
    NonEmptyRestriction.cut k ⟨ru,true,false⟩ = ⟨ru,true,false⟩ := by
  simp [NonEmptyRestriction.cut,ru]

theorem no_iteration_reaches_an_empty_continuation (n : Nat) :
    (history (n+1)).rootDemand = true := by
  by_cases early : n < 5
  · have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst n <;> decide
  · have index : n+1 = (n-5)+6 := by omega
    rw [index]
    exact root_target_repeats_forever (n-5)

theorem selected_root_control_pair_accepts_the_repeated_target :
    TargetZeroKernel.entryIntersects (fun _ _ => false) .target .zero = true ∧
    TargetZeroKernel.exitIntersect (fun _ _ => none) .zero (.target .demandTarget) =
      some (.target .demandTarget) := by decide

theorem producer_has_no_intrinsic_may (q : Seed) (v : Value)
    (generated : produce q = some v) : v.ap.tail = .must := by
  unfold produce at generated
  split at generated
  · cases generated; rfl
  · contradiction

theorem producer_generates_u_without_copying_t (q : Seed) (v : Value)
    (generated : produce q = some v) : v.ap = ru ∧ v.ap.mark ≠ q.ap.mark := by
  unfold produce at generated
  split at generated
  · rename_i guard
    have marks : q.ap.mark = some t := by
      have checked := guard
      simp only [Bool.and_eq_true,beq_iff_eq] at checked
      exact checked.2
    cases generated
    constructor
    · rfl
    · rw [marks]
      change (some u : Option Nat) ≠ some t
      decide
  · contradiction

end ProvisionalUniformCycle
