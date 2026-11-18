import DisjointCleaner
namespace CleanerRepairTrace
open NonEmptyPolicy NonEmptyRestriction AuditCleanerGetter
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def clean (v : Value) : Option Value :=
  if v.ap.mark.isNone && DisjointCleaner.safeCone v.ap.path [] .exact then some v
  else AuditCleanerGetter.clean v

def body (back : Bool) (q : Seed) : List Value :=
  let v : Value := ⟨q.ap,q.demand,false⟩
  if back then ((moveValue true v).bind clean).toList
  else match clean v with
    | none => []
    | some w => w :: (moveValue false w).toList

def summaries1 : List Edge := starts1.flatMap fun q =>
  (body false q).map fun v => (q.ap,cut 1 v)

def summaries2 : List Edge := (handoff summaries1).flatMap fun row =>
  (HeadPolicy.emit 2 1 true row.entry need).flatMap fun q =>
    (body true q).filterMap fun v =>
      HeadPolicy.restrictOne 2 1 true [need] q.ap (cut 1 v) row

def normalBackward : Edge :=
  (a ret [] .star none,⟨a p [g] .star none,false,false⟩)
def normalForward : Edge :=
  (a p [g] .star none,⟨a ret [] .star none,false,false⟩)

theorem root_run1_is_exactly_unchanged : summaries1=AuditCleanerGetter.summaries1 := by decide +kernel

theorem no_new_C2_query_or_admission_exception :
    queries 2 1 true (handoff summaries1) need=
    queries 2 1 true (handoff AuditCleanerGetter.summaries1) need := by
  rw [root_run1_is_exactly_unchanged]

theorem run2_C5_now_publishes_the_missing_NORMAL_relation :
    summaries2=[(a ret [] .exact,⟨a p [g] .exact,true,true⟩),
                (a ret [] .star,⟨a p [g] .star,true,true⟩),normalBackward] := by decide +kernel

theorem marked_guides_and_their_protection_are_unchanged :
    summaries2.filter (fun edge => edge.2.demand)=AuditCleanerGetter.summaries2 := by decide +kernel

theorem new_NORMAL_service_is_not_a_cut_or_a_new_limit_exception :
    normalBackward.2.demand=false ∧ normalBackward.1.path.length=0 ∧
    normalBackward.2.ap.path.length=1 ∧
    cut 1 normalBackward.2=normalBackward.2 := by decide +kernel

theorem precise_run3_admission_stays_rejected :
    queries 3 2 false (handoff summaries2) ⟨source.ap,false⟩=[] := by decide +kernel

theorem saved_replay_alone_recovers_the_real_NORMAL_observation :
    bind normalForward ⟨source.ap,false⟩=
      some ⟨a ret [h] .must,false⟩ := by decide +kernel

theorem NORMAL_service_transports_any_actual_suffix_without_unrolling
    (suffix : Path) (tail : Tail) (layer : Bool) :
    bind normalForward ⟨a p ([g]++suffix) tail,layer⟩=
      some ⟨a ret suffix tail,layer⟩ := by
  simp [AuditCleanerGetter.bind,normalForward,a,p,ret,g,marksOK,marksMeet,dropHead]

-- A quiet suffix after a NORMAL report. The cutoff is not part of this
-- controller: the computed report has no outgoing DEMAND Target.
structure Result where
  report : Bool
  demand : Bool
  deriving DecidableEq

def observe (v : Offered) : Result :=
  ⟨v.ap.base==ret && v.ap.mark==some t && v.ap.tail==.must && !v.demand,v.demand⟩
def run3 : Result := match bind normalForward ⟨source.ap,false⟩ with
  | some v => observe v
  | none => ⟨false,false⟩
def next (state : Result) : Result :=
  if state.demand then state else ⟨state.report,false⟩
def later : Nat → Result
  | 0 => run3
  | n+1 => next (later n)

theorem the_repaired_case_finishes_naturally_in_run3 : run3=⟨true,false⟩ := by decide +kernel

theorem no_later_uncapped_round_loses_the_report_or_revives_demand (n : Nat) :
    later n=⟨true,false⟩ := by
  induction n with
  | zero => exact the_repaired_case_finishes_naturally_in_run3
  | succ n ih => simp [later,ih,next]

theorem overlapping_root_FLOW_still_excludes_T :
    clean ⟨a p [] .star none,false,false⟩=
      some ⟨{a p [] .star none with mx:=[t]},false,false⟩ := by decide +kernel

theorem a_demand_input_is_never_upgraded_by_the_new_route :
    bind normalForward ⟨source.ap,true⟩=some ⟨a ret [h] .must,true⟩ := by decide +kernel

theorem concrete_selected_cleaner_and_same_head_MUST_revision_are_unchanged
    (v : Value) (concrete : v.ap.mark≠none) : clean v=AuditCleanerGetter.clean v := by
  simp [clean,Option.isNone_iff_eq_none,concrete]

end CleanerRepairTrace
