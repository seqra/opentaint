/-
Reached repeat-component closure for E21, run-2 and run-3. A configured,
CFG-reached ZERO control input is supplied; no DATA frame is supplied.
Each round performs C2, body transfer, paired C5, publication replay to all
standing scalar inputs, native AP application, the global bound and the
repeat gate. The monotone input list is a proof witness of scalar offers,
not a proposed runtime input archive or a native packed-store equality.

Other physical ports, root scheduling and the complete native driver remain
adapter obligations. Nonzero backward Reach/Target results are terminal:
they do not create a new ZERO repeat input. Backward ZERO-premise rows are
handoff guidance, not saved DATA records.
-/
import E21Run4SavedReplayClosure
import E21LateLocalAudit

namespace E21Run2Run3WorklistClosure
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies
open ApSpec

set_option maxRecDepth 16384
set_option maxHeartbeats 64000000

structure State where
  inputs : List Actual := []
  rows : List Edge := []
  deriving DecidableEq, Repr

def unique [DecidableEq α] (xs : List α) : List α := xs.eraseDups
def seedCommands (mode : Mode) (rows : List DemandRow) (inputs : List Actual) : List Choice :=
  E21PrefixExactCompanion.commands mode rows inputs

def fromAP (a : ApSpec.AFact) : Option Actual := do
  if a.fact.base ≠ x+1 then none else
    let tail ← match a.fact.kind with
      | .exact => some Tail.exact
      | .star _ => some .star
      | .any => some .any
    let mark ← match a.fact.mark with
      | .conc t => some (.full t : ScalarMark)
      | .star => some .flow
      | .starEx _ => none
    let e := match a.fact.kind with | .star (.set e) => e | _ => []
    pure ⟨⟨x,a.fact.path,tail,mark,e⟩,(if a.demand then .demand else .normal),false⟩

/-- Native AP geometry includes ancestor-ANY matching. The earlier applyFlow
helper implements only the at/below lane and must not replace this step. -/
def applyData (row : Edge) (input : Actual) : List Actual :=
  match row.original,row.result with
  | .data initial,.data output =>
      match toAP input,toAP ⟨initial,.normal,false⟩,toAP output with
      | some actual,some premise,some result =>
          (ApSpec.Run1CorrelatedConcreteInitials.rawSummary actual premise.fact result).facts.filterMap fromAP
      | _,_,_ => []
  | _,_ => []

def depthOriginal : Original → Nat
  | .zero => 0 | .data p => p.path.length
def growing (row : Edge) : Bool :=
  match row.result with
  | .data a => decide (a.pattern.path.length > depthOriginal row.original)
  | _ => false

def gate (mode : Mode) (permissions : List DemandRow) (input : Actual) : Option Actual :=
  let observe := E21PrefixExactCompanion.dataCommands mode permissions
  let baseline := observe input
  if baseline.isEmpty then none else
    let budgets := (List.range input.pattern.path.length).map (fun n => n+1)
    (budgets.find? fun b => equalCommandSets baseline (observe (cutAt b input)))
      |>.map (fun b => cutAt b input)

def retainApplied (mode : Mode) (permissions : List DemandRow)
    (row : Edge) (input : Actual) : List Actual :=
  let bounded := cutAt mode.limit input
  if growing row then (gate mode permissions bounded).toList else [bounded]

/-- Only the actually reached NORMAL ZERO may activate zero-original DATA
rows. Source/Target callbacks never call this function with a new ZERO. -/
def fromReachedZero (mode : Mode) (permissions : List DemandRow) (row : Edge) : List Actual :=
  match row.original,row.result with
  | .zero,.data output => retainApplied mode permissions row output
  | _,_ => []

def round (mode : Mode) (permissions : List DemandRow) (saved : List Edge)
    (sourceAllowed : Bool) (state : State) : State :=
  let inferred := allSelected mode permissions
    ((seedCommands mode permissions state.inputs).flatMap (body mode sourceAllowed))
  let published := canonical (state.rows ++ inferred)
  let zeroResults := published.flatMap (fromReachedZero mode permissions)
  let dataResults := (saved ++ published).flatMap fun row =>
    state.inputs.flatMap fun input =>
      (applyData row input).flatMap (retainApplied mode permissions row)
  ⟨unique (state.inputs ++ zeroResults ++ dataResults),published⟩

def runRounds (mode : Mode) (permissions : List DemandRow) (saved : List Edge)
    (sourceAllowed : Bool) : Nat → State
  | 0 => {}
  | n+1 => round mode permissions saved sourceAllowed (runRounds mode permissions saved sourceAllowed n)

def permissions2 := E21PrefixExactCompanion.demand2
def stage2 (n : Nat) := runRounds modeB2 permissions2 [] false n
def closed2 := stage2 3

def sameSet [DecidableEq α] (a b : List α) : Bool :=
  a.all (fun x => decide (x ∈ b)) && b.all (fun x => decide (x ∈ a))

/-- Only nonzero NORMAL pure FLOW rows in this program are saved/reversed.
Zero rows remain in the handoff but do not enter the DATA record list. -/
def reversedNormalData (row : Edge) : Option Edge :=
  match row.original,row.result with
  | .data initial,.data output =>
      if output.layer = .normal ∧ initial.mark = .flow ∧ output.pattern.mark = .flow ∧
          initial.tail = .star ∧ output.pattern.tail = .star then
        some ⟨.data output.pattern,.data ⟨initial,.normal,false⟩⟩
      else none
  | _,_ => none

def permissions3 := handoff .backward closed2.rows
def saved3 := closed2.rows.filterMap reversedNormalData
def sourceAllowed3 := sourceEnabled closed2.rows
def stage3 (n : Nat) := runRounds modeF3 permissions3 saved3 sourceAllowed3 n
def closed3 := stage3 2

def partialInput : Actual := actual [f] .any .demand
def exactInput : Actual := actual [f] .exact .normal
def flowDemandRow : Edge :=
  ⟨.data (p [f] .star .flow),.data (actual [f] .any .demand .flow)⟩
def flowGrower : Edge :=
  ⟨.data (p [] .star .flow),.data (actual [f] .star .normal .flow)⟩
def flowShrinker : Edge :=
  ⟨.data (p [f] .star .flow),.data (actual [] .star .normal .flow)⟩

theorem run2_begins_without_a_DATA_frame : (stage2 0).inputs=[] := rfl
theorem run2_reached_ZERO_generates_the_actual_sink_read :
    (stage2 1).inputs=[exactInput] := by decide
theorem run2_publication_replays_to_the_standing_exact_input :
    flowDemandRow ∈ (stage2 2).rows ∧ partialInput ∈ (stage2 2).inputs := by decide
theorem run2_FLOW_DEMAND_read_is_an_organic_MAY_producer :
    applyData flowDemandRow exactInput=[partialInput] := by decide
theorem run2_NORMAL_grower_independently_produces_the_same_capped_MAY :
    (applyData flowGrower exactInput).flatMap (retainApplied modeB2 permissions2 flowGrower) =
      [partialInput] := by decide
theorem run2_late_MAY_admits_the_STAR_actor_not_a_DEMAND_exact_actor :
    ⟨p [f] .star T,.demand⟩ ∈ E21PrefixExactCompanion.dataCommands modeB2 permissions2 partialInput ∧
    ⟨p [f] .exact T,.demand⟩ ∉ E21PrefixExactCompanion.dataCommands modeB2 permissions2 partialInput := by decide
theorem run2_both_real_input_shapes_reach_a_fixed_point :
    closed2.inputs=[exactInput,partialInput] ∧
    round modeB2 permissions2 [] false closed2=closed2 := by decide
theorem run2_stabilizes_the_same_eight_publication_families :
    closed2.rows.length=8 ∧ sameSet closed2.rows E21PrefixExactCompanion.final2=true := by decide
theorem run2_current_publications_are_closed_on_every_standing_input :
    (closed2.rows.flatMap fun row => closed2.inputs.flatMap fun input =>
      (applyData row input).flatMap (retainApplied modeB2 permissions2 row)).all
        (fun result => decide (result ∈ closed2.inputs)) = true := by decide
theorem run2_both_DATA_publications_stabilize_the_MAY_input :
    applyData flowDemandRow partialInput=[partialInput] ∧
    (applyData flowGrower partialInput).flatMap (retainApplied modeB2 permissions2 flowGrower)=
      [partialInput] := by decide
theorem run2_completed_source_actors_supply_run3_permission : sourceAllowed3=true := by decide
theorem backward_ZERO_DATA_is_guidance_not_a_saved_DATA_provider :
    saved3=[flowShrinker] := by decide
theorem run3_handoff_has_all_seven_complete_pairs :
    permissions3.length=7 ∧ sameSet permissions3 E21PrefixExactCompanion.demand3=true := by decide
theorem run3_ZERO_source_selects_both_original_C5_images :
    sameSet (stage3 1).inputs [actual [f] .any .demand,actual [f] .exact .demand]=true := by decide
theorem saved_and_current_shrinkers_add_the_missing_parent_point_facts :
    sameSet closed3.inputs [actual [f] .any .demand,actual [f] .exact .demand,
      actual [] .any .demand,actual [] .exact .demand]=true := by decide
theorem native_MAY_inside_matching_closes_the_root_repeat :
    applyData flowShrinker (actual [] .any .demand)=[actual [] .any .demand] ∧
    applyData flowShrinker (actual [] .exact .demand)=[] := by decide
theorem run3_never_promotes_a_real_T_input_to_NORMAL :
    closed3.inputs.all (fun a => decide (a.layer=.demand ∧ a.pattern.mark=T))=true := by decide
theorem run3_conditional_FLOW_initials_do_not_become_real_FLOW_inputs :
    closed3.inputs.all (fun a => decide (a.pattern.mark≠.flow))=true := by decide
theorem run3_is_closed_under_saved_current_and_ZERO_DATA_replay :
    round modeF3 permissions3 saved3 sourceAllowed3 closed3=closed3 := by decide
theorem run3_has_the_same_five_local_publication_families :
    closed3.rows.length=5 ∧ sameSet closed3.rows E21PrefixExactCompanion.final3=true := by decide
theorem run3_outgoing_demand_preserves_the_same_three_paired_rows :
    (handoff .forward closed3.rows).length=3 ∧
    sameSet (handoff .forward closed3.rows) E21PrefixExactCompanion.demand4=true := by decide

theorem run3_does_not_need_a_separate_exact_offer_for_these_publications :
    sameSet (allSelected modeF3 permissions3
      ((seedCommands modeF3 permissions3
        [actual [f] .any .demand,actual [] .any .demand]).flatMap (body modeF3 sourceAllowed3)))
      closed3.rows=true := by decide

def further (step : State → State) : Nat → State → State
  | 0,s => s
  | n+1,s => step (further step n s)

theorem every_further_run2_round_is_unchanged (n : Nat) :
    further (round modeB2 permissions2 [] false) n closed2=closed2 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [further,ih] using run2_both_real_input_shapes_reach_a_fixed_point.2

theorem every_further_run3_round_is_unchanged (n : Nat) :
    further (round modeF3 permissions3 saved3 sourceAllowed3) n closed3=closed3 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [further,ih] using run3_is_closed_under_saved_current_and_ZERO_DATA_replay

#eval ("E21_R2_REACHED_ROUNDS",reprStr (stage2 1),reprStr (stage2 2),reprStr closed2)
#eval ("E21_R3_REACHED_ROUNDS",reprStr (stage3 1),reprStr closed3)

end E21Run2Run3WorklistClosure
