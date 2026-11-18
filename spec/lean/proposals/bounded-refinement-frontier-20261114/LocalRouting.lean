import Publication

/- Replacement for artificial E=G. Ownership is in the admission plan.
   Facts, raw initial keys, summaries and native field exclusions are ordinary.
   Only an already covered unknown correlated-STAR read is delegated. -/
namespace BoundedLocalRouting
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle BoundedRefinementFrontier
open BoundedRefinementPipeline

structure Command where
  seed : Seed
  delegated : List Nat := []
  deriving DecidableEq, BEq, Repr

def plan (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Command :=
  ((emit run limit backward row.entry a).flatMap fun q =>
    if backward && q.ap.tail == .star && q.ap.mark.isNone && q.ap.e.isEmpty &&
        q.ap.path == row.entry.path && decide (row.entry.path.length+1 ≤ limit) then
      match dropHead row.entry.path [f] with
      | some [field] =>
          -- The empty-head command comes ONLY from the original C2 family.
          -- A STAR-only offer does not acquire a new empty-head command.
          [⟨q,[field]⟩,
           ⟨⟨{q.ap with path := q.ap.path ++ [field],tail := .exact},false⟩,[]⟩,
           ⟨⟨{q.ap with path := q.ap.path ++ [field]},false⟩,[]⟩]
      | _ => [⟨q,[]⟩]
    else [⟨q,[]⟩]).eraseDups

/-- The test uses the first field of the correlated symbolic suffix, not
    a field in the already concrete path and not a result's first field. -/
def routedMove (q : Command) (fromBase toBase : Nat) (read write : Path) : Option Value :=
  let ordinary := moveE fromBase toBase read write q.seed.ap
  if q.seed.ap.tail == .star then
    match dropHead q.seed.ap.path read with
    | some (field :: _) =>
      match ordinary with
      | some value =>
        if q.delegated.contains field && value.demand && value.ap.tail == .may
        then none else ordinary
      | none => none
    | _ => ordinary
  else ordinary

theorem routing_does_not_modify_any_emitted_result (q : Command)
    (fromBase toBase : Nat) (read write : Path) (value : Value)
    (emitted : routedMove q fromBase toBase read write = some value) :
    moveE fromBase toBase read write q.seed.ap = some value := by
  unfold routedMove at emitted
  dsimp only at emitted
  split at emitted
  · cases shape : dropHead q.seed.ap.path read with
    | none => simpa [shape] using emitted
    | some suffix =>
      cases suffix with
      | nil => simpa [shape] using emitted
      | cons field rest =>
        cases result : moveE fromBase toBase read write q.seed.ap with
        | none => simp [shape,result] at emitted
        | some ordinary =>
          simp only [shape,result] at emitted
          split at emitted
          · simp at emitted
          · exact emitted
  · exact emitted

theorem normal_results_are_forwarded_unchanged (q : Command)
    (fromBase toBase : Nat) (read write : Path) (value : Value)
    (ordinary : moveE fromBase toBase read write q.seed.ap = some value)
    (normal : value.demand = false) :
    routedMove q fromBase toBase read write = some value := by
  simp only [routedMove,ordinary]
  split
  · cases shape : dropHead q.seed.ap.path read with
    | none => simp [shape]
    | some suffix =>
      cases suffix with
      | nil => simp [shape]
      | cons field rest => simp [shape,normal]
  · rfl

def bodyRouted (backward : Bool) (q : Command) : List Value :=
  if backward then
    [routedMove q ret p [] readPath,routedMove q ret p [f] []].filterMap id
  else
    [routedMove q p ret readPath [],routedMove q p ret [] [f]].filterMap id

def summariesRouted (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) :
    List (Ap × Value) :=
  let commands := plan run limit backward row a
  let seeds := commands.map Command.seed
  commands.flatMap fun q => (bodyRouted backward q).filterMap fun c =>
    publish limit backward seeds q.seed c row

def coarse : Command := ⟨⟨ap ret [] .star,false⟩,[f]⟩
def childExact : Command := ⟨⟨ap ret [f] .exact,false⟩,[]⟩
def childStar : Command := ⟨⟨ap ret [f] .star,false⟩,[]⟩

theorem ordinary_star_has_no_artificial_exclusion :
    coarse.seed.ap = ap ret [] .star ∧ coarse.seed.ap.e = [] := by decide

theorem coarse_unknown_read_is_delegated :
    routedMove coarse ret p [f] [] = none := by decide

theorem both_child_cases_execute_the_known_read :
    routedMove childExact ret p [f] [] = some (val (ap p [] .exact)) ∧
    routedMove childStar ret p [f] [] = some (val (ap p [] .star)) := by decide

theorem no_new_empty_head_is_admitted_from_star_only :
    (plan 2 1 true backwardRow ⟨ap ret [] .star,false⟩).all
      (fun q => !(q.seed.ap.path.isEmpty && q.seed.ap.tail == .exact)) = true := by decide

theorem may_input_still_gets_its_existing_empty_case :
    (plan 2 1 true backwardRow sinkNeed).length = 4 ∧
    (plan 2 1 true backwardRow sinkNeed).any
      (fun q => decide (q.seed.ap = ap ret [] .exact)) = true := by decide

theorem all_emitted_initials_have_empty_real_exclusion_in_this_fixture :
    (plan 2 1 true backwardRow sinkNeed).all
      (fun q => q.seed.ap.e.isEmpty && decide (q.seed.ap.path.length ≤ 1)) = true := by decide

theorem known_g_write_exports_the_full_normal_reader :
    routedMove coarse ret p [] [g] = some (val (ap p [g] .star)) := by decide

theorem the_full_g_reader_can_transport_its_f_descendant :
    moveE p ret [g] [] (ap p [g,f] .must (some t)) =
      some (val (ap ret [f] .must (some t))) := by decide

/-- Retired promotion-ban regression: the middle writer reads f then
    prefixes h backwards. The mandatory child EXACT query recovers it. -/
def middleReader (q : Command) : Option Value := do
  let value ← routedMove q ret p [f] []
  moveE p p [] [3] value.ap

theorem middle_branch_is_delegated_but_not_lost :
    middleReader coarse = none ∧
    middleReader childExact = some (val (ap p [3] .exact)) := by decide

theorem middle_child_reader_is_a_full_normal_summary :
    normalize childExact.seed.ap (val (ap p [3] .exact)) =
      (ap ret [f] .star,val (ap p [3] .star)) := by decide

theorem this_reader_recovers_the_h_source :
    moveE p ret [3] [f] (ap p [3] .must (some t)) =
      some (val (ap ret [f] .must (some t))) := by decide

def edges2 := summariesRouted 2 1 true backwardRow sinkNeed
def rows3 := handoff edges2
def sourceEdges3 := rows3.flatMap fun row => summariesRouted 3 2 false row source
def edges3 := rows3.flatMap fun row =>
  summariesRouted 3 2 false row source ++
  firstActual3.flatMap (summariesRouted 3 2 false row)
def rows4 := handoff edges3
def edges4 := rows4.flatMap fun row => summariesRouted 4 3 true row sinkNeed

theorem local_frontier_still_has_f_refinement :
    rows3.isEmpty = false ∧
    rows3.all (fun row => decide (row.entry = ap p [f] .ne)) = true := by decide

theorem normal_uniform_reader_is_still_derived :
    sourceEdges3.any (fun edge => decide (edge.1 = ap p [f] .must) &&
      decide (edge.2.ap = ap ret [] .must) && !edge.2.demand) = true := by decide

theorem real_run3_cut_demands_are_unchanged : rows4 = run4Rows := by decide

theorem new_method_only_run5_frontier_is_empty :
    outgoing (handoff edges4) finalActual5 = [] := by decide

/-- BB replay from the existing weak MUST view still needs preservation. -/
def bbEdges4 := rows4.flatMap fun row =>
  let seeds := (plan 4 3 true row sinkNeed).map Command.seed
  seeds.filterMap fun q => restricted 3 seeds q (val (ap p [f] .may) true) row
def bbRows5 := handoff bbEdges4
def bbEdges5 := bbRows5.flatMap fun row =>
  let seeds := (plan 5 4 false row source).map Command.seed
  seeds.flatMap fun q =>
    [learnedReader ⟨{q.ap with mark := some t},q.demand⟩ |>.map
      (fun v => {v with ap := {v.ap with mark := none}}),
     moveE p ret [] [f] q.ap].filterMap id |>.filterMap fun c =>
      publish 4 false seeds q c row

theorem bb_weak_reverse_view_is_still_kept : bbRows5 = bbRun5Rows := by decide

theorem both_reference_cases_keep_the_finding_and_naturally_stop :
    outgoing (handoff edges4) finalActual5 = [] ∧
    outgoing (handoff bbEdges5) finalActual5 = [] ∧
    finalActual5.any (fun a => !a.demand && a.ap.tail == .must) = true := by decide

/-- A shared raw initial cannot get contradictory masks through AP dedup.
    Delegation must be justified for EVERY service sharing that initial. -/
def safeCommonDelegation (plans : List (List Nat)) (f : Nat) : Bool :=
  !plans.isEmpty && plans.all (fun fields => fields.contains f)

theorem an_uncovered_consumer_prevents_shared_delegation :
    safeCommonDelegation [[1],[]] 1 = false := by decide

theorem agreement_can_delegate_without_changing_the_initial_key :
    safeCommonDelegation [[1],[1,2]] 1 = true ∧
    coarse.seed.ap = ap ret [] .star := by decide

end BoundedLocalRouting

#print axioms BoundedLocalRouting.ordinary_star_has_no_artificial_exclusion
#print axioms BoundedLocalRouting.routing_does_not_modify_any_emitted_result
#print axioms BoundedLocalRouting.normal_results_are_forwarded_unchanged
#print axioms BoundedLocalRouting.coarse_unknown_read_is_delegated
#print axioms BoundedLocalRouting.both_child_cases_execute_the_known_read
#print axioms BoundedLocalRouting.no_new_empty_head_is_admitted_from_star_only
#print axioms BoundedLocalRouting.may_input_still_gets_its_existing_empty_case
#print axioms BoundedLocalRouting.all_emitted_initials_have_empty_real_exclusion_in_this_fixture
#print axioms BoundedLocalRouting.known_g_write_exports_the_full_normal_reader
#print axioms BoundedLocalRouting.the_full_g_reader_can_transport_its_f_descendant
#print axioms BoundedLocalRouting.middle_branch_is_delegated_but_not_lost
#print axioms BoundedLocalRouting.middle_child_reader_is_a_full_normal_summary
#print axioms BoundedLocalRouting.this_reader_recovers_the_h_source
#print axioms BoundedLocalRouting.local_frontier_still_has_f_refinement
#print axioms BoundedLocalRouting.normal_uniform_reader_is_still_derived
#print axioms BoundedLocalRouting.real_run3_cut_demands_are_unchanged
#print axioms BoundedLocalRouting.new_method_only_run5_frontier_is_empty
#print axioms BoundedLocalRouting.bb_weak_reverse_view_is_still_kept
#print axioms BoundedLocalRouting.both_reference_cases_keep_the_finding_and_naturally_stop
#print axioms BoundedLocalRouting.an_uncovered_consumer_prevents_shared_delegation
#print axioms BoundedLocalRouting.agreement_can_delegate_without_changing_the_initial_key
