import Run2Relay
namespace RelayTrace
open NonEmptyPolicy NonEmptyRestriction
open NestedSTAR
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

-- Only C2's run-2 same-head STAR cell and its raw C5 image are replaced.
-- Write, both paired rows, actuals, limits and saved application are old.
def queries (actual : Offered) : List Seed := (handoff inner1).flatMap fun row =>
  Run2Relay.emit 2 1 true row.entry actual

def inner (actual : Offered) : List Edge := (handoff inner1).flatMap fun row =>
  (Run2Relay.emit 2 1 true row.entry actual).flatMap fun q =>
    (backwardBody q).filterMap fun v =>
      Run2Relay.restrictOne 2 1 true [actual] q.ap v row

def outerStarts : List Seed := (handoff wrapper1).flatMap fun row =>
  Run2Relay.emit 2 1 true row.entry backwardOffer

def wrapper : List Edge := outerStarts.flatMap fun q => inner (asInnerOffer q)

theorem run1_is_literal_unchanged_input_to_this_repair :
    inner1=[(ap p,⟨ap p,true,false⟩),(ap p,⟨ap ret,true,false⟩)] ∧
    wrapper1=inner1 := by decide +kernel

theorem deeper_outer_offer_and_same_head_inner_offer_both_start :
    outerStarts=[⟨ap ret,false⟩] ∧
    queries ⟨ap ret,false⟩=[⟨ap ret,false⟩] := by decide +kernel

theorem the_inner_publishes_the_strong_write_NORMAL_summary :
    inner ⟨ap ret,false⟩=[normalBackward] := by decide +kernel

theorem wrapper_C5_keeps_the_same_NORMAL_relation :
    wrapper=[normalBackward] ∧
    Run2Relay.restrictOne 2 1 true [backwardOffer] (ap ret) normalBackward.2
      ⟨ap ret,ap p⟩=some normalBackward := by decide +kernel

-- This failed raw permission is essential at a head already at the cap:
-- an inner run-2 STAR offer is its own constructive witness, with no
-- invented deeper input and no public-normalization shortcut.
theorem the_new_same_head_offer_is_the_actual_raw_C5_witness :
    Run2Relay.rawImage 2 1 true (ap ret) [⟨ap ret,false⟩]=[ap ret] ∧
    Run2Relay.restrictOne 2 1 true [⟨ap ret,false⟩] (ap ret) normalBackward.2
      ⟨ap ret,ap p⟩=some normalBackward := by decide +kernel

-- Another transparent wrapper uses the same current start and own pair.
def throughWrapper (replies : List Edge) : List Edge :=
  if queries ⟨ap ret,false⟩ == [⟨ap ret,false⟩] then
    replies.filterMap fun edge =>
      Run2Relay.restrictOne 2 1 true [⟨ap ret,false⟩] edge.1 edge.2 ⟨ap ret,ap p⟩
  else []
def nested : Nat → List Edge
  | 0 => inner ⟨ap ret,false⟩
  | n+1 => throughWrapper (nested n)

theorem any_finite_wrapper_depth_retains_the_same_NORMAL_reply (n : Nat) :
    nested n=[normalBackward] := by
  induction n with
  | zero => exact the_inner_publishes_the_strong_write_NORMAL_summary
  | succ n ih =>
    change throughWrapper (nested n)=[normalBackward]
    rw [ih]
    decide +kernel

theorem wrapper_depth_does_not_multiply_summary_shapes (n : Nat) :
    (nested n).length=1 := by rw [any_finite_wrapper_depth_retains_the_same_NORMAL_reply];rfl

-- Usual saved backward-record reversal gives normalForward. E stays at
-- the write's scope; the sibling point is preserved and overwritten f is not.
theorem run3_saved_NORMAL_replay_has_the_precise_observation :
    saved normalForward source=some ⟨ap ret .exact [g] (some t),false⟩ ∧
    saved normalForward ⟨ap p .exact [f] (some t),false⟩=none := by decide +kernel

theorem a_DEMAND_caller_cannot_be_confirmed_by_the_new_NORMAL_provider :
    saved normalForward {source with demand:=true}=
      some ⟨ap ret .exact [g] (some t),true⟩ := by decide +kernel

theorem a_real_exclusion_is_not_an_unconditional_star_identity :
    saved (ap p,⟨ap ret,false,false⟩) ⟨ap p .exact [f] (some t),false⟩=
      some ⟨ap ret .exact [f] (some t),false⟩ ∧
    saved normalForward ⟨ap p .exact [f] (some t),false⟩=none := by decide +kernel

-- This trace ends at run-3 by the existing no-DEMAND rule. It is not
-- stopped at a hard limit; the retained NORMAL observation is cumulative.
def hasNormalObservation : Bool :=
  saved normalForward source == some ⟨ap ret .exact [g] (some t),false⟩
def hasNextDemand : Bool := false

theorem natural_run3_completion_retains_the_real_observation :
    hasNormalObservation=true ∧ hasNextDemand=false := by decide +kernel

def retain (seen : Bool) : Bool := seen || hasNormalObservation

theorem no_uncapped_later_iteration_can_remove_the_repaired_observation (n : Nat) :
    Nat.rec hasNormalObservation (fun _ seen => retain seen) n=true := by
  induction n with
  | zero => exact natural_run3_completion_retains_the_real_observation.1
  | succ n ih =>
    change retain (Nat.rec hasNormalObservation (fun _ seen => retain seen) n)=true
    rw [ih]
    rfl

end RelayTrace
