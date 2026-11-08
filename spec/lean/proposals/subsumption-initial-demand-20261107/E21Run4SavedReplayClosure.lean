/-
Correction to the E21 transaction catalog: close one actually reached
run-4 DATA packet under saved NORMAL replay and the kept repeat gate.
The parent original is preserved. This is not a whole native-port/driver
closure theorem. Adjacent/enclosing DATA observers are empty in the same
declared scalar reduction as the earlier E21 models.
-/
import E21PrefixExactCompanion

namespace E21Run4SavedReplayClosure
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def permissions := E21PrefixExactCompanion.demand4
def commands4 (a : Actual) := E21PrefixExactCompanion.dataCommands modeB4 permissions a

def gate4 (a : Actual) : Option Actual :=
  let expected := commands4 a
  if expected.isEmpty then none else
    let budgets := (List.range a.pattern.path.length).map (fun n => n+1)
    (budgets.find? fun budget => equalCommandSets expected (commands4 (cutAt budget a)))
      |>.map (fun budget => cutAt budget a)

def step (a : Actual) : Option Actual := do
  let raw ← growFromDerived a
  gate4 (cutAt modeB4.limit raw)

def replay : Nat → Actual → Option Actual
  | 0,a => some a
  | n+1,a => (replay n a).bind step

def first : Actual := actual [f] .exact .normal
def second : Actual := actual [f,f] .exact .normal
def stable : Actual := actual [f,f] .any .demand
def coarseFirst : Actual := actual [f] .star .demand
def coarseSecond : Actual := actual [f,f] .star .demand

def advance (edge : Edge) : Option Edge := do
  let a ← match edge.result with | .data a => some a | _ => none
  let b ← step a
  pure ⟨edge.original,.data b⟩

def trace : List Actual := [first,second,stable]
def domain : List Actual := trace ++
  [actual [f] .exact .demand,actual [f,f] .exact .demand]
def localCommands := E21PrefixExactCompanion.commands modeB4 permissions domain
def currentRows := allSelected modeB4 permissions (localCommands.flatMap (body modeB4 false))
def nextPermissions := handoff .backward currentRows
def nextSourceRows := allSelected modeF5 nextPermissions (body modeF5 (sourceEnabled currentRows) .zero)
def nextSourceImages : List Actual := nextSourceRows.filterMap fun edge =>
  match edge.result with | .data a => some a | _ => none

theorem saved_shrinker_is_really_derived_before_run4 :
    normalShrinker.isSome = true := by decide

theorem first_saved_application_delivers_the_precise_two_field_fact :
    step first = some second := by decide

theorem second_saved_application_cuts_before_repeat_delivery :
    growFromDerived second = some (actual [f,f,f] .exact .normal) ∧
    step second = some stable := by decide

theorem global_limit_is_not_the_cut_in_that_transaction :
    cutAt modeB4.limit (actual [f,f,f] .exact .normal) = actual [f,f,f] .exact .normal := by decide

theorem depth_two_MAY_preserves_all_repeat_commands :
    equalCommandSets (commands4 (actual [f,f,f] .exact .normal)) (commands4 stable) = true ∧
    equalCommandSets (commands4 (actual [f,f,f] .exact .normal))
      (commands4 (actual [f] .any .demand)) = false := by decide

theorem saved_replay_reaches_an_actual_fixed_point : step stable = some stable := by decide

theorem every_further_saved_application_returns_the_same_fact (n : Nat) :
    replay n stable = some stable := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [replay,ih] using saved_replay_reaches_an_actual_fixed_point

theorem all_five_packet_shapes_are_closed_under_saved_replay :
    domain.all (fun a => (step a).any (fun b => decide (b ∈ domain))) = true := by decide

theorem both_layers_of_the_regenerated_sink_packet_are_in_the_domain :
    first ∈ domain ∧ actual [f] .exact .demand ∈ domain := by decide

theorem STAR_feedback_also_reaches_that_MAY_fixed_point :
    step coarseFirst = some coarseSecond ∧ step coarseSecond = some stable := by decide

theorem the_existing_completion_is_no_longer_fresh :
    (step stable).any (fun a => decide (a ∉ trace)) = false := by decide

theorem saved_application_keeps_the_parent_original (original : Original) :
    advance ⟨original,.data second⟩ = some ⟨original,.data stable⟩ := by
  simp [advance,second_saved_application_cuts_before_repeat_delivery.2]

theorem delivered_MAY_selects_the_real_ff_STAR_source_actor :
    ⟨p [f,f] .star T,.demand⟩ ∈ commands4 stable := by decide

theorem this_replay_route_does_not_deliver_the_shallower_MAY :
    actual [f] .any .demand ∉ domain := by decide

theorem current_rows_for_the_closed_replay_packet_have_three_families :
    currentRows =
      [⟨.zero,.data (actual [f] .exact .normal)⟩,
       ⟨.data (p [f,f] .star T),.reach .demand⟩,
       ⟨.data (p [f,f] .star T),.target .demand⟩] := by decide

theorem no_new_local_DATA_row_is_the_parent_MAY_completion :
    currentRows.all (fun row => match row.result with
      | .data a => decide (a = first) | _ => true) = true := by decide

theorem the_next_source_has_no_shorter_DEMAND_image_from_this_packet :
    nextSourceImages = [rawF5] := by decide

theorem that_precise_source_still_fails_the_supplied_next_gate :
    E21PrefixExactCompanion.dataCommands modeF5 nextPermissions rawF5 = [] := by decide

#eval ("E21_R4_ACTUALLY_KEPT_DATA_TRACE",reprStr trace)
#eval ("E21_R4_CURRENT_ROWS_FROM_THAT_PACKET",reprStr currentRows)
#eval ("E21_F5_SOURCE_IMAGES_FROM_THAT_PACKET",reprStr nextSourceImages)

end E21Run4SavedReplayClosure
