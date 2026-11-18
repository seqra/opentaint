import Frontier
import Cycle

/- Closed neutral-prefix reference for the proposed BOTH-DIRECTION plan.
   The only initial NORMAL provider is the writer learned at run-1.
   No pre-existing complete reader or untruncated cross-call evidence is used.
   Native rules/aliases/ND service equivalence remains an integration obligation. -/
namespace BoundedRefinementPipeline
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle BoundedRefinementFrontier

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def moveE (fromBase toBase : Nat) (read write : Path) (q : Ap) : Option Value :=
  match dropHead q.path read with
  | some (field :: _) =>
    if q.e.contains field then none
    else (move fromBase toBase read write q).map fun v =>
      if v.ap.tail == .may then {v with ap := {v.ap with e := []}} else v
  | _ => move fromBase toBase read write q

def readPath : Path := [f,g]

def bodyE (backward : Bool) (q : Ap) : List Value :=
  if backward then
    [moveE ret p [] readPath q,moveE ret p [f] [] q].filterMap id
  else
    [moveE p ret readPath [] q,moveE p ret [] [f] q].filterMap id

/-- In this example the saved writer's input guard is empty forward and
    exactly f in its ordinary backward view. Guards refine only one level. -/
def prepare (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Seed :=
  ((emit run limit backward row.entry a).flatMap fun q =>
    if backward && q.ap.tail == .star && q.ap.mark.isNone && q.ap.e.isEmpty then
      match dropHead row.entry.path [f] with
      | some [field] => oneFieldPlan limit row.entry q field
      | _ => [q]
    else [q]).eraseDups

def normalWriterCover (backward : Bool) (q : Ap) (c : Value) : Bool :=
  !c.demand && !c.h &&
    ((if backward then moveE ret p [f] [] q else moveE p ret [] [f] q) == some c)

def restricted (limit : Nat) (qs : List Seed) (q : Seed) (c : Value)
    (row : Row) : Option (Ap × Value) := do
  if qs.any (fun w => decide (w.ap = q.ap)) then
    let pair := normalize q.ap c
    let selected ← intersectExit pair.2 row.exit
    return normalize pair.1 (cut (min limit (row.exit.path.length+1)) selected)
  else none

def publish (limit : Nat) (backward : Bool) (qs : List Seed)
    (q : Seed) (c : Value) (row : Row) : Option (Ap × Value) :=
  if c.ap.path.length ≤ limit && normalWriterCover backward q.ap c then none
  else restricted limit qs q (cut limit c) row

def summaries (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) :
    List (Ap × Value) :=
  let qs := prepare run limit backward row a
  qs.flatMap fun q => (bodyE backward q.ap).filterMap fun c =>
    publish limit backward qs q c row

theorem paired_c5_output_bound_is_unchanged (limit : Nat) (qs : List Seed)
    (q : Seed) (c : Value) (row : Row) (edge : Ap × Value)
    (emitted : restricted limit qs q c row = some edge) :
    edge.2.ap.path.length ≤ min limit (row.exit.path.length+1) := by
  unfold restricted at emitted
  split at emitted
  · dsimp only at emitted
    cases result : intersectExit (normalize q.ap c).2 row.exit with
    | none => simp [result] at emitted
    | some value =>
      simp only [result] at emitted
      have same := Option.some.inj emitted
      rw [← same]
      rw [(normalize_preserves_paths_marks_layers_protection
        (normalize q.ap c).1 (cut (min limit (row.exit.path.length+1)) value)).2.1]
      exact cut_respects_depth _ _
  · simp at emitted

def handoff (edges : List (Ap × Value)) : List Row :=
  (edges.filterMap fun edge =>
    if edge.2.demand then some ⟨edge.2.ap,edge.1⟩ else none).eraseDups

theorem run1_already_has_the_writer_provider :
    moveE p ret [] [f] (ap p [] .star) =
      some (val (ap ret [f] .star)) := by decide

theorem run2_plan_uses_only_one_new_field_and_no_must :
    (prepare 2 1 true backwardRow sinkNeed).length = 4 ∧
    (prepare 2 1 true backwardRow sinkNeed).all
      (fun q => decide (q.ap.path.length ≤ 1) && q.ap.tail != .must) = true := by decide

theorem the_backward_unknown_writer_loss_is_removed :
    moveE ret p [f] [] {ap ret [] .star with e := [f]} = none ∧
    moveE ret p [f] [] (ap ret [f] .star) = some (val (ap p [] .star)) := by decide

def run2Edges := summaries 2 1 true backwardRow sinkNeed
def run3Rows := handoff run2Edges

theorem run2_publishes_refinement_at_f_not_root_may :
    run2Edges.isEmpty = false ∧
    run2Edges.all (fun edge => edge.2.demand &&
      decide (edge.2.ap = ap p [f] .ne)) = true := by decide

theorem run3_keeps_the_existing_uniform_lane :
    (run3Rows.flatMap fun row => prepare 3 2 false row source).all
      (fun q => decide (q.ap = ap p [f] .must) && !q.demand) = true := by decide

def first3Edges := run3Rows.flatMap fun row => summaries 3 2 false row source

theorem run3_derives_the_normal_uniform_reader :
    first3Edges.any (fun edge => decide (edge.1 = ap p [f] .must) &&
      decide (edge.2.ap = ap ret [] .must) && !edge.2.demand) = true := by decide

theorem no_relative_writer_cut_is_created_for_the_first_call :
    first3Edges.all (fun edge => !edge.2.demand) = true := by decide

/-- The same derivation works for any longer read starting with f.g.
    The q=f.MUST query never enumerates the remaining path. -/
theorem uniform_reader_does_not_need_the_full_read_prefix (rest : Path) :
    moveE p ret ([f,g] ++ rest) [] (ap p [f] .must) =
      some (val (ap ret [] .must)) := by
  simp [moveE,move,dropHead,ap,val,f,g,p,ret]

theorem a_long_backward_read_still_cuts_at_one_field (rest : Path) :
    cut 1 (val (ap p ([f,g] ++ rest) .star)) =
      val (ap p [f] .ne) true := by
  simp [cut,ap,val,f,g]

/-- This NORMAL relation was actually derived above. Its premise requires
    genuine uniform taint at f; an ff-only input does not satisfy it. -/
def learnedReader (a : Offered) : Option Value :=
  if a.ap.tail == .must then
    match dropHead a.ap.path [f] with
    | some suffix => if admits a.ap.tail a.ap.e suffix then
        some (val {a.ap with base := ret,path := [],e := []} a.demand)
        else none
    | none => none
  else none

def normalReplay (limit : Nat) (a : Offered) : List Offered :=
  [learnedReader a,moveE p ret [] [f] a.ap].filterMap id |>.map fun c =>
    let bounded := cut limit {c with demand := a.demand || c.demand}
    ⟨{bounded.ap with base := p},bounded.demand⟩

def firstActual3 := normalReplay 2 source
def finalActual3 := firstActual3.flatMap (normalReplay 2)
def firstActual5 := normalReplay 4 source
def finalActual5 := firstActual5.flatMap (normalReplay 4)

theorem actual_first_call_keeps_uniform_precision :
    firstActual3 =
      [⟨ap p [] .must (some t),false⟩,
       ⟨ap p [f,f] .must (some t),false⟩] := by decide

theorem run3_retains_the_genuine_global_cut :
    finalActual3 =
      [⟨ap p [] .must (some t),false⟩,
       ⟨ap p [f] .must (some t),false⟩,
       ⟨ap p [f,f] .ne (some t),true⟩] := by decide

theorem a_normal_and_a_demand_sink_witness_coexist_at_run3 :
    finalActual3.any (fun a => !a.demand) = true ∧
    finalActual3.any Offered.demand = true := by decide

def run3Edges := run3Rows.flatMap fun row =>
  summaries 3 2 false row source ++
  firstActual3.flatMap (summaries 3 2 false row)
def run4Rows := handoff run3Edges

theorem the_only_remaining_run3_helper_demand_is_from_the_long_writer :
    run4Rows.isEmpty = false ∧
    run4Rows.all (fun row =>
      decide (row.exit = ap p [f,f] .star) &&
      (decide (row.entry = ap ret [f] .ne) ||
       decide (row.entry = ap ret [f,f] .ne))) = true := by decide

def run4Edges := run4Rows.flatMap fun row => summaries 4 3 true row sinkNeed
def run5Rows := handoff run4Edges

theorem helper_demand_is_empty_after_run4 : run5Rows = [] := by decide

def reverseWriterOnOriginal (a : Offered) : Option Offered :=
  (moveE ret p [f] [] a.ap).map fun c =>
    ⟨{c.ap with base := ret},a.demand || c.demand⟩

theorem ordinary_backward_writer_replay_keeps_source_permission :
    reverseWriterOnOriginal sinkNeed = some sinkNeed ∧
    ((reverseWriterOnOriginal sinkNeed).bind reverseWriterOnOriginal).map
      (fun a => sourceHit {a with ap := {a.ap with base := p}}) = some true := by decide

theorem run5_saved_records_produce_only_precise_normal_results :
    finalActual5 =
      [⟨ap p [] .must (some t),false⟩,
       ⟨ap p [f] .must (some t),false⟩,
       ⟨ap p [f,f,f] .must (some t),false⟩] := by decide

theorem learned_record_matches_the_real_body_on_required_actuals :
    (bodyE false source.ap).map (fun c => c.ap) =
      [ap ret [] .must (some t),ap ret [f,f] .must (some t)] ∧
    bodyE false (ap p [f,f] .must (some t)) =
      [val (ap ret [f,f,f] .must (some t))] := by decide

/-- Target status follows actual sink witnesses. A normal hit never erases
    a demand hit. Current helper demand comes from the computed handoff. -/
def outgoing (rows : List Row) (actuals : List Offered) : List Bool :=
  rows.map (fun _ => true) ++ actuals.filterMap fun a =>
    if a.demand then some true else none

theorem no_premature_stop_after_run3 :
    (outgoing run4Rows finalActual3).isEmpty = false := by decide

theorem natural_stop_after_run5_without_a_hard_cap :
    outgoing run5Rows finalActual5 = [] ∧
    finalActual5.any (fun a => !a.demand && a.ap.tail == .must) = true := by decide

/-- BB variant: the readBB's NORMAL f.MUST -> ret.MUST record has the
    existing weak backward view ret.STAR -> f.MAY/DEMAND. Do not naively
    reverse its MUST endpoints. That extra native replay can leave a method
    demand at run-4, and must be included in the termination check. -/
def bbRun4Edges : List (Ap × Value) := run4Rows.flatMap fun row =>
  let qs := prepare 4 3 true row sinkNeed
  qs.filterMap fun q => restricted 3 qs q (val (ap p [f] .may) true) row

def bbRun5Rows := handoff bbRun4Edges

theorem bb_weak_reverse_must_view_is_not_silently_discarded :
    bbRun5Rows.isEmpty = false ∧
    bbRun5Rows.all (fun row => decide (row.entry = ap p [f,f] .may)) = true := by decide

def bbRun5Edges := bbRun5Rows.flatMap fun row =>
  let qs := prepare 5 4 false row source
  qs.flatMap fun q =>
    -- The current f.f.MUST query does not prove the old f.MUST premise.
    -- readBB has no current DATA demand, so only its saved reader can run.
    [learnedReader ⟨{q.ap with mark := some t},q.demand⟩ |>.map
       (fun v => {v with ap := {v.ap with mark := none}}),
     moveE p ret [] [f] q.ap].filterMap id |>.filterMap fun c =>
       publish 4 false qs q c row

theorem bb_run5_reuses_the_existing_uniform_query :
    (bbRun5Rows.flatMap fun row => prepare 5 4 false row source).all
      (fun q => decide (q.ap = ap p [f,f] .must) && !q.demand) = true := by decide

theorem bb_run5_produces_no_fresh_helper_demand : bbRun5Edges = [] := by decide

theorem bb_natural_stop_after_run5_keeps_the_finding :
    outgoing (handoff bbRun5Edges) finalActual5 = [] ∧
    finalActual5.any (fun a => !a.demand && a.ap.tail == .must) = true := by decide

end BoundedRefinementPipeline

#print axioms BoundedRefinementPipeline.run1_already_has_the_writer_provider
#print axioms BoundedRefinementPipeline.paired_c5_output_bound_is_unchanged
#print axioms BoundedRefinementPipeline.run2_plan_uses_only_one_new_field_and_no_must
#print axioms BoundedRefinementPipeline.the_backward_unknown_writer_loss_is_removed
#print axioms BoundedRefinementPipeline.run2_publishes_refinement_at_f_not_root_may
#print axioms BoundedRefinementPipeline.run3_keeps_the_existing_uniform_lane
#print axioms BoundedRefinementPipeline.run3_derives_the_normal_uniform_reader
#print axioms BoundedRefinementPipeline.no_relative_writer_cut_is_created_for_the_first_call
#print axioms BoundedRefinementPipeline.uniform_reader_does_not_need_the_full_read_prefix
#print axioms BoundedRefinementPipeline.a_long_backward_read_still_cuts_at_one_field
#print axioms BoundedRefinementPipeline.actual_first_call_keeps_uniform_precision
#print axioms BoundedRefinementPipeline.run3_retains_the_genuine_global_cut
#print axioms BoundedRefinementPipeline.a_normal_and_a_demand_sink_witness_coexist_at_run3
#print axioms BoundedRefinementPipeline.the_only_remaining_run3_helper_demand_is_from_the_long_writer
#print axioms BoundedRefinementPipeline.helper_demand_is_empty_after_run4
#print axioms BoundedRefinementPipeline.ordinary_backward_writer_replay_keeps_source_permission
#print axioms BoundedRefinementPipeline.run5_saved_records_produce_only_precise_normal_results
#print axioms BoundedRefinementPipeline.learned_record_matches_the_real_body_on_required_actuals
#print axioms BoundedRefinementPipeline.no_premature_stop_after_run3
#print axioms BoundedRefinementPipeline.natural_stop_after_run5_without_a_hard_cap
#print axioms BoundedRefinementPipeline.bb_weak_reverse_must_view_is_not_silently_discarded
#print axioms BoundedRefinementPipeline.bb_run5_reuses_the_existing_uniform_query
#print axioms BoundedRefinementPipeline.bb_run5_produces_no_fresh_helper_demand
#print axioms BoundedRefinementPipeline.bb_natural_stop_after_run5_keeps_the_finding
