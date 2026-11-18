import DefiniteSupport

/- Two fully analyzed acyclic owners, two unary T-to-U producers.
   The broad root-U record requires p.g; the f-input record produces only
   ret.f/U. Latest definite reply absorption is enabled. No cleaner/pass,
   unknown body, alias, field cut, loop, recursion or guessed source. -/
namespace DifferentUniformReply
open NonEmptyPolicy NonEmptyRestriction
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def f : Nat := 1
def g : Nat := 2
def t : Nat := 1
def u : Nat := 2
def p : Nat := 0
def ret : Nat := 1
def pt (path : Path) (tail : Tail) : Ap := ⟨p,path,tail,some t,[],[]⟩
def out (path : Path) (tail : Tail) : Ap := ⟨ret,path,tail,some u,[],[]⟩
abbrev Edge := Ap × Value
def rootActual : Offered := ⟨pt [] .must,false⟩
def fieldActual : Offered := ⟨pt [f] .must,false⟩
def returnActual : Offered := ⟨out [] .may,true⟩
def v (a : Ap) (d : Bool := false) : Value := ⟨a,d,false⟩
def guidance (a : Ap) : Ap := if a.tail == .must then {a with tail := .may} else a

/-- CM(p.g.M,T) -> GEN(r.MUST,U), followed by return r.
    A known selected subtree proves the condition. An unknown ancestor read
    instead creates MAY/DEMAND. A point at an ancestor cannot meet g. -/
def rootProducer (q : Seed) : Option Value :=
  if q.ap.base != p || q.ap.mark != some t then none
  else if (dropHead [g] q.ap.path).isSome then some (v (out [] .must) q.demand)
  else if (dropHead q.ap.path [g]).isSome && q.ap.tail != .exact then
    some (v (out [] (if q.ap.tail == .must then .must else .may))
      (q.demand || q.ap.tail != .must))
  else none

/-- CM(p.M,T) -> GEN(r.f.MUST,U). Known marked descendants satisfy the
    condition, but no suffix is copied from T to U. -/
def fieldProducer (q : Seed) : Option Value :=
  if q.ap.base == p && q.ap.mark == some t then
    some (v (out [f] .must) q.demand) else none

def forwardBody (q : Seed) : List Value :=
  [rootProducer q,fieldProducer q].filterMap id

/-- Reverse each producer's real target. At the root EXACT cannot hit the
    child-f action; STAR/MAY can. Every reverse CM result is MAY/DEMAND. -/
def reverseBody (q : Seed) : List Value :=
  if q.ap.base != ret || q.ap.mark != some u then [] else
  [some (v (pt [g] .may) true),
    if (dropHead [f] q.ap.path).isSome ||
        ((dropHead q.ap.path [f]).isSome && q.ap.tail != .exact) then
      some (v (pt [] .may) true) else none].filterMap id

/-- Collect first fields from qualified D rows with the SAME paired Dp,
    and from retained NORMAL native input guards in the read direction.
    Only one first field is taken; the newly built child is not expanded. -/
def nextFields (back : Bool) (row : Row) (rows : List Row) (records : List Edge) : List Nat :=
  let heads := (rows.filter (fun r => r.exit == row.exit)).map (·.entry) ++
    records.map (fun e => if back then e.2.ap else e.1)
  (heads.filterMap fun head =>
    if head.base != row.entry.base || head.mark != row.entry.mark then none
    else match dropHead row.entry.path head.path with
      | some (a :: _) => some a
      | _ => none).eraseDups

/-- Complete bounded plan. The MUST exception is kept at compatible heads;
    it does not split one uniform offer into artificial point/STAR copies.
    Children keep the original row, support and FL(Dc)+1 budget. -/
def prepare (run k : Nat) (back : Bool) (row : Row) (rows : List Row)
    (records : List Edge) (actual : Offered) : List Seed :=
  let base := emit run k back row.entry actual
  let children := if (row.entry.tail == .may || row.entry.tail == .ne) && !base.isEmpty then
    (nextFields back row rows records).flatMap fun field =>
      let child := {row.entry with path := row.entry.path ++ [field],tail := .may}
      (emit run k back child actual).filter fun q =>
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

def mustCovers (a required : Ap) : Bool :=
  a.base == required.base && a.mark == required.mark && a.tail == .must &&
    (dropHead a.path required.path).isSome
def overlaps (a b : Ap) : Bool :=
  a.base == b.base && a.mark == b.mark &&
    ((dropHead a.path b.path).isSome || (dropHead b.path a.path).isSome)

/-- Saved MUST provisional lane; mark-changing output keeps its literal
    generated path. Actual support is joined after ordinary return binding. -/
def savedForward (record : Edge) (a : Offered) : Option Value :=
  if record.1.tail == .must && overlaps a.ap record.1 then
    some {record.2 with demand := a.demand || !mustCovers a.ap record.1}
  else none

def currentForward (record : Edge) (a : Offered) : Option Value :=
  let accepts := if record.1.tail == .must then mustCovers a.ap record.1
    else a.ap.base == p && a.ap.mark == some t &&
      ((dropHead record.1.path a.ap.path).isSome ||
        (a.ap.tail == .must && (dropHead a.ap.path record.1.path).isSome))
  if accepts then some {record.2 with demand := a.demand || record.2.demand} else none

def savedBackward (record : Edge) : Option Value :=
  if record.1.tail == .must && overlaps returnActual.ap record.2.ap then
    some (v {record.1 with tail := .may} true) else none

/-- Existing same-initial/layer MUST canonicalization; EXACT is kept.
    D rows are captured BEFORE this executable union. -/
def coveredMust (a b : Value) : Bool :=
  a.demand == b.demand && a.h == b.h && a.ap.base == b.ap.base &&
    a.ap.mark == b.ap.mark && a.ap.mx == b.ap.mx && a.ap.e == b.ap.e &&
    a.ap.tail == .must && b.ap.tail == .must &&
    a.ap.path != b.ap.path && (dropHead a.ap.path b.ap.path).isSome
def canonicalValues (xs : List Value) : List Value :=
  (xs.eraseDups).filter fun x => !(xs.any (fun y => coveredMust y x))
def canonicalEdges (xs : List Edge) : List Edge :=
  (xs.eraseDups).filter fun x => !(xs.any (fun y => y.1 == x.1 && coveredMust y.2 x.2))
def replies (records current : List Edge) (a : Offered) : List Value :=
  DefiniteReplySupport.foldValues (canonicalValues (
    records.filterMap (fun e => savedForward e a) ++
    current.filterMap (fun e => currentForward e a)))
def save (old fresh : List Edge) : List Edge :=
  canonicalEdges (old ++ fresh.filter (fun e => !e.2.demand))
def outputRows (xs : List Edge) : List Row :=
  (xs.filterMap fun e => if e.2.demand then some ⟨guidance e.2.ap,guidance e.1⟩ else none).eraseDups
def startEdges : List Edge :=
  [(pt [] .star,v (out [] .may) true), (pt [] .star,v (out [f] .must) true)]

structure State where
  rows : List Row
  records : List Edge
  rootDemand : Bool
  permissionB : Bool
  permissionA : Bool
  reports : List Nat
  sinkSeeds : List Nat
  deriving DecidableEq, BEq, Repr
def initial : State := ⟨[],[],false,true,true,[],[]⟩
def terminal (id : Nat) (value : Value) : TargetZeroKernel.Summary :=
  TargetZeroKernel.forwardSinkTarget 0 .zero (if value.demand then .demand else .normal) id
def permission (path : Path) (value : Value) : Bool :=
  value.ap.base == p && value.ap.mark == some t &&
    match dropHead value.ap.path path with
    | some rest => admits value.ap.tail value.ap.e rest
    | none => (dropHead path value.ap.path).isSome

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

def backward (run k : Nat) (st : State) : State := Id.run do
  let current := candidates run k true st.rows st.records [returnActual]
  let all := st.records.filterMap savedBackward ++ current.map (·.2)
  let b := st.sinkSeeds.contains 0 && all.any (permission [])
  let a := st.sinkSeeds.contains 1 && all.any (permission [f])
  return ⟨outputRows current,st.records,b || a,b,a,st.reports,st.sinkSeeds⟩
def limit (run : Nat) : Nat := max 1 (run-1)
def step (run : Nat) (st : State) : State :=
  if run % 2 == 0 then backward run (limit run) st else forward run (limit run) st
def history : Nat → State
  | 0 => initial
  | n+1 => step (n+1) (history n)

def gExact : Edge := (pt [g] .must,v (out [] .exact))
def gUniform : Edge := (pt [g] .must,v (out [] .must))
def rootUniform : Edge := (pt [] .must,v (out [] .must))
def gFieldExact : Edge := (pt [g] .must,v (out [f] .exact))
def rootFieldExact : Edge := (pt [] .must,v (out [f] .exact))
def fExact : Edge := (pt [f] .must,v (out [f] .exact))
def fUniform : Edge := (pt [f] .must,v (out [f] .must))
def earlyRecords : List Edge := [gExact,gUniform,rootUniform,gFieldExact,rootFieldExact]
def completeRecords : List Edge := earlyRecords ++ [fExact,fUniform]
def s1 : State := ⟨[⟨out [] .may,pt [] .star⟩,⟨out [f] .may,pt [] .star⟩],
  [],true,true,true,[],[0,1]⟩
def s2 : State := ⟨[
  ⟨pt [g] .may,out [] .exact⟩,⟨pt [g] .may,out [] .star⟩,⟨pt [] .may,out [] .star⟩,
  ⟨pt [g] .may,out [f] .exact⟩,⟨pt [] .may,out [f] .exact⟩,
  ⟨pt [g] .may,out [f] .star⟩,⟨pt [] .may,out [f] .star⟩],
  [],true,true,true,[],[0,1]⟩
def s3 : State := ⟨[⟨out [f] .may,pt [f] .star⟩,⟨out [f] .exact,pt [f] .star⟩],
  earlyRecords,true,true,true,[0],[0,1]⟩
def s4 : State := ⟨[⟨pt [f] .may,out [f] .exact⟩,⟨pt [f] .may,out [f] .star⟩],
  earlyRecords,true,true,true,[0],[0,1]⟩
def s5 : State := ⟨[],completeRecords,true,true,true,[0,1],[1]⟩
def s6 : State := ⟨[],completeRecords,true,false,true,[0,1],[1]⟩

theorem cold_run1 : history 1 = s1 := by decide
theorem cold_run2 : history 2 = s2 := by decide
theorem cold_run3 : history 3 = s3 := by decide
theorem cold_run4 : history 4 = s4 := by decide
theorem cold_run5 : history 5 = s5 := by decide
theorem cold_run6 : history 6 = s6 := by decide

theorem empty_rows_admit_nothing (run k : Nat) (back : Bool)
    (records : List Edge) (offers : List Offered) :
    candidates run k back [] records offers = [] := by
  unfold candidates
  induction offers with
  | nil => rfl
  | cons a rest ih => simpa using ih

theorem forward_fixed (run k : Nat) (notFirst : run ≠ 1) : forward run k s6 = s6 := by
  have first : (run == 1) = false := by simp [notFirst]
  dsimp only [forward,s6]
  simp only [first,Bool.false_eq_true,ite_false,empty_rows_admit_nothing]
  rfl

theorem backward_fixed (run k : Nat) : backward run k s6 = s6 := by
  dsimp only [backward,s6]
  rw [empty_rows_admit_nothing]
  rfl

theorem later_step_fixed (n : Nat) : step (n+7) s6 = s6 := by
  unfold step
  split
  · exact backward_fixed _ _
  · exact forward_fixed _ _ (by omega)

theorem uncapped_recurrence (n : Nat) : history (n+6) = s6 := by
  induction n with
  | zero => exact cold_run6
  | succ n ih =>
      change step (n+7) (history (n+6)) = s6
      rw [ih]
      exact later_step_fixed n

theorem root_target_repeats_forever (n : Nat) :
    (history (n+6)).rootDemand = true := by rw [uncapped_recurrence]; rfl

theorem no_current_helper_work_remains (n : Nat) :
    (history (n+6)).rows = [] := by rw [uncapped_recurrence]; rfl

theorem both_reports_are_already_normal (n : Nat) :
    (history (n+6)).reports = [0,1] := by rw [uncapped_recurrence]; rfl

theorem only_a_is_resubmitted (n : Nat) :
    (history (n+6)).permissionA = true ∧ (history (n+6)).permissionB = false := by
  rw [uncapped_recurrence]; decide

theorem no_early_stop (n : Nat) : (history (n+1)).rootDemand = true := by
  by_cases early : n < 5
  · have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases cases with h | h | h | h | h <;> subst n <;> decide
  · have index : n+1 = (n-5)+6 := by omega
    rw [index]
    exact root_target_repeats_forever (n-5)

theorem actual_packet_is_different_not_identical_support :
    replies completeRecords [] fieldActual =
      [v (out [] .must) true,v (out [f] .exact),v (out [f] .must)] := by decide

theorem different_paths_survive_the_latest_filter_in_both_orders :
    DefiniteReplySupport.foldValues [v (out [] .must) true,v (out [f] .must)] =
      [v (out [] .must) true,v (out [f] .must)] ∧
    DefiniteReplySupport.foldValues [v (out [f] .must),v (out [] .must) true] =
      [v (out [f] .must),v (out [] .must) true] := by decide

theorem same_layer_canonicalization_does_not_cross_support :
    canonicalValues [v (out [] .must) true,v (out [f] .must)] =
      [v (out [] .must) true,v (out [f] .must)] := by decide

theorem no_normal_root_reply_can_absorb_the_witness :
    (completeRecords.filterMap (fun e => savedForward e fieldActual)).all
      (fun x => !(x.ap.path.isEmpty && !x.demand)) = true := by decide

theorem without_broad_record_no_demand_reply_remains :
    (replies (completeRecords.filter (fun e => e != rootUniform)) [] fieldActual).all
      (fun value => !value.demand) = true := by decide

theorem added_g_guards_cannot_supply_the_f_actual :
    savedForward gExact fieldActual = none ∧ savedForward gUniform fieldActual = none ∧
    savedForward gFieldExact fieldActual = none := by decide

theorem broad_reply_has_normal_support_at_b_but_not_at_a :
    savedForward rootUniform rootActual = some (v (out [] .must)) ∧
    savedForward rootUniform fieldActual = some (v (out [] .must) true) := by decide

theorem more_precise_current_root_guard_cannot_match_a :
    currentForward rootUniform fieldActual = none ∧
    currentForward fUniform fieldActual = some (v (out [f] .must)) := by decide

theorem backward_saved_reply_renews_both_relevant_input_heads :
    savedBackward rootUniform = some (v (pt [] .may) true) ∧
    savedBackward fUniform = some (v (pt [f] .may) true) := by decide

theorem qualified_child_head_survives_executable_root_may :
    (outputRows startEdges).length = 2 ∧
    (outputRows startEdges).any (fun row => row.entry.path == [f]) = true := by decide

theorem prepared_children_are_enabled_in_the_cold_run :
    (prepare 2 1 true ⟨out [] .may,pt [] .star⟩ s1.rows [] returnActual).any
      (fun q => q.ap.path == [f] && q.ap.tail == .exact) = true ∧
    (prepare 3 2 false ⟨pt [] .may,out [] .star⟩ s2.rows [] rootActual).any
      (fun q => q.ap.path == [g] && q.ap.tail == .must) = true := by decide

theorem extra_exact_and_g_records_are_retained :
    gExact ∈ (history 6).records ∧ gUniform ∈ (history 6).records ∧
    rootFieldExact ∈ (history 6).records ∧ fExact ∈ (history 6).records := by
  rw [cold_run6]
  simp [s6,completeRecords,earlyRecords]

theorem full_cold_saved_basis_is_normal_unprotected_and_fits_one_field :
    completeRecords.all (fun e => !e.2.demand && !e.2.h &&
      decide (e.1.path.length ≤ 1 && e.2.ap.path.length ≤ 1)) = true := by decide

theorem neither_producer_copies_t_to_u (q : Seed) (c : Value)
    (member : c ∈ forwardBody q) : c.ap.mark = some u := by
  simp only [forwardBody,List.mem_filterMap,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ⟨choice,(h | h),same⟩
  · subst choice
    unfold rootProducer at same
    split at same
    · contradiction
    · split at same
      · cases same; rfl
      · split at same
        · cases same; rfl
        · contradiction
  · subst choice
    unfold fieldProducer at same
    split at same
    · cases same; rfl
    · contradiction

theorem all_runs_can_use_the_existing_target_zero_pair :
    TargetZeroKernel.entryIntersects (fun _ _ => false) .target .zero = true ∧
    TargetZeroKernel.exitIntersect (fun _ _ => none) .zero (.target .demandTarget) =
      some (.target .demandTarget) := by decide

end DifferentUniformReply
