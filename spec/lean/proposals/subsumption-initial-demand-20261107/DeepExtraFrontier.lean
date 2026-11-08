/-
Prepared E21 extra-frontier supplement. Ordinary counted fields, no static
anchors. It closes a source/read producer grammar and arbitrary bounded query
families, not the exhaustive native dispatcher/store adapter. No native
recovery, canonical replacement or whole-driver scheduling theorem is claimed.
-/
import DeepGuidanceArrival
import GeneralLoopAdmissionOneStep

namespace DeepExtraFrontier
open PlainStarRelativeAdmission
open DeepFlowCompletion
open DeepGuidanceArrival
open GeneralLoopAdmissionBound
open GeneralLoopAdmissionOneStep

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

abbrev FPattern := FlowDemandCompletion.Pattern
abbrev FRow := FlowDemandCompletion.Row

def entryBound (h : Nat) : FlowDemandCompletion.Entry → Prop
  | .zero | .target => True
  | .data value => RelativeRestriction.depth value.path ≤ h

def exitBound (h : Nat) : FlowDemandCompletion.Exit → Prop
  | .zero => True
  | .data value => RelativeRestriction.depth value.path ≤ h

def rowBound (h : Nat) (row : FRow) : Prop := entryBound h row.entry ∧ exitBound h row.exit

theorem encoded_counted_depth (pattern : PlainStarRelativeAdmission.Pattern) :
    RelativeRestriction.depth (encode pattern).path = pattern.path.length := by
  change RelativeRestriction.depth (pattern.path.map RelativeRestriction.Accessor.field) = pattern.path.length
  induction pattern.path with
  | nil => rfl
  | cons head rest ih => simpa only [List.map_cons,RelativeRestriction.depth,List.length_cons] using congrArg Nat.succ ih

theorem public_initial_keeps_counted_depth (pattern : PlainStarRelativeAdmission.Pattern) :
    RelativeRestriction.depth (encode (publicInitial pattern)).path = pattern.path.length := by
  rw [encoded_counted_depth]
  exact public_normalization_keeps_key_depth pattern

theorem endpoint_member_is_bounded (h : Nat) (row : FRow) (bounded : rowBound h row)
    (pattern : FPattern)
    (present : pattern ∈ FlowDemandCompletion.entryEndpoint row.entry ++ FlowDemandCompletion.exitEndpoint row.exit) :
    RelativeRestriction.depth pattern.path ≤ h := by
  rcases List.mem_append.mp present with left | right
  · cases which : row.entry with
    | zero => simp [FlowDemandCompletion.entryEndpoint,which] at left
    | target => simp [FlowDemandCompletion.entryEndpoint,which] at left
    | data value =>
      have same : pattern = value := by simpa [FlowDemandCompletion.entryEndpoint,which] using left
      subst pattern
      simpa only [entryBound,which] using bounded.1
  · cases which : row.exit with
    | zero => simp [FlowDemandCompletion.exitEndpoint,which] at right
    | data value =>
      have same : pattern = value := by simpa [FlowDemandCompletion.exitEndpoint,which] using right
      subst pattern
      simpa only [exitBound,which] using bounded.2

theorem prefix_addition_keeps_both_head_bounds (h : Nat) (source result : FRow)
    (bounded : rowBound h source) (present : result ∈ FlowDemandCompletion.prefixRows source) :
    rowBound h result := by
  obtain ⟨pattern,inEndpoints,inSelf⟩ := List.mem_flatMap.mp present
  obtain ⟨eligible,head,inHeads,same⟩ :=
    FlowDemandCompletion.self_result_has_one_real_endpoint source.interface pattern result inSelf
  have bound := Nat.le_trans (FlowDemandCompletion.valid_prefix_depth_bound pattern head inHeads)
    (endpoint_member_is_bounded h source bounded pattern inEndpoints)
  rw [same]
  exact ⟨bound,bound⟩

theorem paired_addition_keeps_both_head_bounds (h : Nat) (source result : FRow)
    (bounded : rowBound h source) (present : result ∈ FlowDemandCompletion.pairedRow source) :
    rowBound h result := by
  obtain ⟨left,right,leftIs,rightIs,leftLegal,rightLegal,same⟩ :=
    FlowDemandCompletion.paired_result_keeps_both_heads source result present
  rw [same]
  constructor
  · simpa only [rowBound,entryBound,leftIs,FlowDemandCompletion.flowAny] using bounded.1
  · simpa only [rowBound,exitBound,rightIs,FlowDemandCompletion.flowAny] using bounded.2

theorem ALL_completed_rows_keep_both_head_bounds (h : Nat) (rows : List FRow)
    (bounded : ∀ row ∈ rows, rowBound h row) :
    ∀ row ∈ FlowDemandCompletion.completed rows, rowBound h row := by
  intro row present
  rcases List.mem_append.mp present with old | added
  · exact bounded row old
  · obtain ⟨source,inRows,inAdditions⟩ := FlowDemandCompletion.generated_row_has_one_final_complete_source rows row added
    rcases List.mem_append.mp inAdditions with pref | pair
    · exact prefix_addition_keeps_both_head_bounds h source row (bounded source inRows) pref
    · exact paired_addition_keeps_both_head_bounds h source row (bounded source inRows) pair

/- The B2 budget establishes both sides of all admitted ordinary DATA rows:
initial keys use the C2 image budget, DATA conclusions use C5's global bound.
Persisted earlier ordinary rows require the same original global-budget adapter. -/
theorem every_raw_B2_public_initial_and_Target_head_has_depth_at_most_one
    (demand : Demand) (actual : Actual) (seed : Seed)
    (emitted : emit modeB2 demand actual = some seed) :
    (publicInitial seed.initial).path.length ≤ 1 := by
  rw [public_normalization_keeps_key_depth]
  have image := arbitrary_actual_emission_is_in_raw_image modeB2 demand actual seed emitted
  have budget := (raw_image_preserves_base_mark_budget_and_has_no_ANY modeB2 demand seed.initial image).2.2.1
  exact budget

theorem every_B2_C5_DATA_output_has_depth_at_most_one
    (raw kept : AnnotatedC5Exit.Fact) (selector : AnnotatedC5Exit.Pattern)
    (accepted : AnnotatedC5Exit.restrictData false 1 raw selector = some kept) :
    RelativeRestriction.depth kept.path ≤ 1 :=
  (AnnotatedC5Exit.restricted_depth_uses_its_own_exit false 1 raw kept selector accepted).1

/- The program's physical DATA feedback is a keep/source return followed by
its mandatory field read. Keep and source results are globally capped before
that read. No expected output depth is assumed in this transition. -/
theorem read_after_global_cap_two_has_depth_at_most_one (input output : Actual)
    (executed : forwardRead (cutAt 2 input) = some output) : output.pattern.path.length ≤ 1 := by
  cases input with
  | mk pattern layer hasH =>
    cases pattern with
    | mk base path tail mark excluded =>
      cases path with
      | nil =>
        simp only [cutAt,List.length_nil,show 0 ≤ 2 by decide,if_true,forwardRead] at executed
        split at executed
        next => cases executed; simp
        next => cases executed
      | cons first rest =>
        cases rest with
        | nil =>
          simp only [cutAt,List.length_cons,List.length_nil,show 1 ≤ 2 by decide,if_true,
            forwardRead,readKnownHead] at executed
          split at executed
          next => cases executed; simp
          next => cases executed
        | cons second later =>
          cases later with
          | nil =>
            simp only [cutAt,List.length_cons,List.length_nil,show 2 ≤ 2 by decide,if_true,
              forwardRead,readKnownHead] at executed
            split at executed
            next => cases executed; simp
            next => cases executed
          | cons third remaining =>
            have overflow : ¬ (first :: second :: third :: remaining).length ≤ 2 := by simp
            simp only [cutAt,overflow,if_false,List.take_succ_cons,List.take_zero,
              forwardRead,readKnownHead] at executed
            split at executed
            next => cases executed; simp
            next => cases executed

theorem ordinary_forward_or_opposite_read_never_increases_depth (input output : Actual)
    (executed : forwardRead input = some output) : output.pattern.path.length ≤ input.pattern.path.length := by
  cases input with
  | mk pattern layer hasH =>
    cases pattern with
    | mk base path tail mark excluded =>
      cases path with
      | nil =>
        simp only [forwardRead] at executed
        split at executed
        next => cases executed; exact Nat.le_refl _
        next => cases executed
      | cons first rest =>
        simp only [forwardRead,readKnownHead] at executed
        split at executed
        next => cases executed; simp
        next => cases executed

/-- Unbounded finite read-replay grammar. Physical round constructors cover
arbitrary carry or GEN values; every physical round still executes the real
cap/read. Replay is ordinary forward read or the opposite of a NORMAL
backward field-read relation, not an arbitrary supplied summary output.
Its native exhaustive-adapter obligation is intentionally separate. -/
inductive F3Boundary : Actual → Type where
  | physical (input output : Actual) (executed : forwardRead (cutAt 2 input) = some output) : F3Boundary output
  | replay (input output : Actual) (before : F3Boundary input)
      (executed : forwardRead input = some output) : F3Boundary output

theorem every_F3_grammar_boundary_has_depth_at_most_one (output : Actual) (arrival : F3Boundary output) :
    output.pattern.path.length ≤ 1 := by
  induction arrival with
  | physical input output executed => exact read_after_global_cap_two_has_depth_at_most_one input output executed
  | replay input output before executed ih =>
      exact Nat.le_trans (ordinary_forward_or_opposite_read_never_increases_depth input output executed) ih

structure F3Initial where
  demand : Demand
  actual : Actual
  arrival : F3Boundary actual
  seed : Seed
  queriedHead : demand.path.length ≤ 1
  emitted : ExactFlowInputBridge.nativeEmit modeF3 demand actual = some seed

theorem every_F3_grammar_initial_and_Target_head_has_depth_at_most_one (witness : F3Initial) :
    (publicInitial witness.seed.initial).path.length ≤ 1 := by
  rw [public_normalization_keeps_key_depth]
  exact Nat.le_trans (native_C2_key_depth_bound modeF3 witness.demand witness.actual witness.seed witness.emitted)
    (Nat.max_le.mpr ⟨witness.queriedHead,every_F3_grammar_boundary_has_depth_at_most_one witness.actual witness.arrival⟩)

def f3Publication (owner : Interface) (original : Option F3Initial)
    (output : Actual) : Publication :=
  ⟨owner,match original with | none => .zero | some witness => .data witness.seed.initial,.data output⟩

theorem every_F3_grammar_publication_handoff_has_both_heads_at_most_one
    (owner : Interface) (original : Option F3Initial) (output : Actual) (arrival : F3Boundary output) :
    rowBound 1 (projectData (f3Publication owner original output)) := by
  constructor
  · change RelativeRestriction.depth (encode output.pattern).path ≤ 1
    rw [encoded_counted_depth]
    exact every_F3_grammar_boundary_has_depth_at_most_one output arrival
  · cases original with
    | none => exact True.intro
    | some witness =>
      change RelativeRestriction.depth (encode (publicInitial witness.seed.initial)).path ≤ 1
      rw [encoded_counted_depth]
      exact every_F3_grammar_initial_and_Target_head_has_depth_at_most_one witness

theorem every_F3_grammar_Target_handoff_keeps_exact_original_head_bound
    (owner : Interface) (witness : F3Initial) :
    rowBound 1 (projectTarget ⟨owner,.data witness.seed.initial⟩) := by
  refine ⟨True.intro,?_⟩
  change RelativeRestriction.depth (encode (publicInitial witness.seed.initial)).path ≤ 1
  rw [encoded_counted_depth]
  exact every_F3_grammar_initial_and_Target_head_has_depth_at_most_one witness

/- B4 originals and conclusions need different laws. The origin law must not
be reused for a DATA output. Exits use their own complete paired selector. -/
theorem ALL_B4_queried_origins_are_at_most_two (demand : Demand) (actual : Actual) (seed : Seed)
    (head : demand.path.length ≤ 1)
    (emitted : ExactFlowInputBridge.nativeEmit modeB4 demand actual = some seed) :
    (publicInitial seed.initial).path.length ≤ 2 := by
  have bound := native_public_key_at_most_one_past_demand modeB4 demand actual seed emitted
  omega

theorem ALL_B4_queried_C5_premises_are_at_most_two (demand : Demand) (stored : PlainStarRelativeAdmission.Pattern)
    (head : demand.path.length ≤ 1) (permitted : canStoreInitial modeB4 demand stored = true) :
    stored.path.length ≤ 2 := by
  have bound := C5_queried_member_at_most_one_past_demand modeB4 demand stored permitted
  omega

theorem ALL_B4_DATA_results_use_their_own_exit_head_bound
    (raw kept : AnnotatedC5Exit.Fact) (selector : AnnotatedC5Exit.Pattern)
    (head : RelativeRestriction.depth selector.path ≤ 1)
    (accepted : AnnotatedC5Exit.restrictData false 3 raw selector = some kept) :
    RelativeRestriction.depth kept.path ≤ 2 := by
  have bound := (AnnotatedC5Exit.restricted_depth_uses_its_own_exit false 3 raw kept selector accepted).2
  omega

/-- This is the head-only projection of an already admitted complete B4 row.
Actual slot, layer, H, owner and port labels are carried by the caller; this
projection neither decides matching nor changes any runtime row. -/
def reverseHeadPair (owner : Interface) (entry exit : FPattern) : FRow :=
  ⟨reverseInterface owner,.data exit,.data entry⟩

theorem complete_B4_pair_reversal_keeps_both_independent_bounds
    (owner : Interface) (entry exit : FPattern)
    (entryDepth : RelativeRestriction.depth entry.path ≤ 2)
    (exitDepth : RelativeRestriction.depth exit.path ≤ 2) :
    rowBound 2 (reverseHeadPair owner entry exit) := ⟨exitDepth,entryDepth⟩

theorem ALL_F5_extra_completion_heads_stay_at_most_two (rows : List FRow)
    (allProduced : ∀ row ∈ rows, rowBound 2 row) :
    ∀ row ∈ FlowDemandCompletion.completed rows, rowBound 2 row :=
  ALL_completed_rows_keep_both_head_bounds 2 rows allProduced

/- The whole query below is arbitrary: every family, scope and port has its
own label. No fixed 3-row/11-row enumeration or family absence is assumed. -/
universe u

theorem ALL_F5_cut_commands_from_ANY_bounded_family_have_depth_at_most_two
    {Label : Type u} (query : List (Query Label)) (coarse : Actual)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 2)
    (cutDepth : coarse.pattern.path.length ≤ 2) (command : Command Label)
    (present : command ∈ commands modeF5 query coarse) : command.seed.initial.path.length ≤ 2 :=
  ALL_cut_commands_are_bounded_by_the_entire_query modeF5 query coarse 2 heads cutDepth command present

theorem NO_F5_extra_bounded_family_can_mask_the_real_depth_three_key
    {Label : Type u} (query : List (Query Label)) (coarse : Actual)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 2)
    (cutDepth : coarse.pattern.path.length ≤ 2) (command : Command Label)
    (present : command ∈ commands modeF5 query coarse) :
    command.seed.initial ≠ (fineSeed x [f,f] f).initial := by
  exact NO_cut_from_ANY_other_family_reproduces_the_fine_key modeF5 query coarse x [f,f] f heads cutDepth command present

theorem F5_full_actual_has_its_real_labelled_fine_key
    {Label : Type u} (query : List (Query Label)) (label : Label)
    (selfPair : (⟨label,fineDemand x [f,f]⟩ : Query Label) ∈ query) :
    (⟨label,fineSeed x [f,f] f⟩ : Command Label) ∈ commands modeF5 query rawF5 := by
  exact fine_command_is_present_with_its_own_label modeF5 query label x [f,f] f 1 (by decide) (by decide) selfPair

theorem every_proper_F5_scalar_trial_rejects_for_the_entire_bounded_query
    {Label : Type u} (query : List (Query Label)) (label : Label)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 2)
    (selfPair : (⟨label,fineDemand x [f,f]⟩ : Query Label) ∈ query)
    (budget : Nat) (proper : 1 ≤ budget ∧ budget < 3) :
    (⟨label,fineSeed x [f,f] f⟩ : Command Label) ∈ commands modeF5 query rawF5 ∧
    (⟨label,fineSeed x [f,f] f⟩ : Command Label) ∉ commands modeF5 query (cutAt budget rawF5) := by
  refine ⟨F5_full_actual_has_its_real_labelled_fine_key query label selfPair,?_⟩
  intro member
  have bounded : (cutAt budget rawF5).pattern.path.length ≤ 2 := by
    have casesBudget : budget = 1 ∨ budget = 2 := by omega
    rcases casesBudget with one | two
    · subst budget; decide
    · subst budget; decide
  have impossible := NO_F5_extra_bounded_family_can_mask_the_real_depth_three_key
    query (cutAt budget rawF5) heads bounded ⟨label,fineSeed x [f,f] f⟩ member
  exact impossible rfl

theorem every_proper_F5_trial_changes_the_entire_labelled_query
    {Label : Type u} (query : List (Query Label)) (label : Label)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 2)
    (selfPair : (⟨label,fineDemand x [f,f]⟩ : Query Label) ∈ query)
    (budget : Nat) (proper : 1 ≤ budget ∧ budget < 3) :
    commands modeF5 query rawF5 ≠ commands modeF5 query (cutAt budget rawF5) := by
  obtain ⟨rawPresent,cutAbsent⟩ := every_proper_F5_scalar_trial_rejects_for_the_entire_bounded_query query label heads selfPair budget proper
  intro same
  rw [same] at rawPresent
  exact cutAbsent rawPresent

structure WholeObservation (Label Adjacent Enclosing : Type u) where
  adjacent : Adjacent
  repeatCommands : List (Command Label)
  enclosing : Enclosing

def observeWhole {Label Adjacent Enclosing : Type u} (query : List (Query Label))
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) (input : Actual) :
    WholeObservation Label Adjacent Enclosing :=
  ⟨adjacent input,commands modeF5 query input,enclosing input⟩

theorem arbitrary_other_observer_components_cannot_hide_the_repeat_difference
    {Label Adjacent Enclosing : Type u} (query : List (Query Label)) (label : Label)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 2)
    (selfPair : (⟨label,fineDemand x [f,f]⟩ : Query Label) ∈ query)
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing)
    (budget : Nat) (proper : 1 ≤ budget ∧ budget < 3) :
    observeWhole query adjacent enclosing rawF5 ≠
      observeWhole query adjacent enclosing (cutAt budget rawF5) := by
  intro same
  exact every_proper_F5_trial_changes_the_entire_labelled_query query label heads selfPair budget proper
    (congrArg WholeObservation.repeatCommands same)

theorem actual_F5_mode_is_four_and_not_the_earlier_local_B4_cell :
    modeF5 = (⟨5,4,.forward⟩ : Mode) := rfl

theorem computed_arrival_supplies_the_required_scope_and_saved_shrinker :
    necessaryF5Rows = some [DeepFlowCompletion.finalData,DeepFlowCompletion.finalZero,DeepFlowCompletion.finalTarget] ∧
    f3NormalShrinker = some ⟨iface true 5 5,.data (p [f] .star .flow),.data (actual [] .star .normal .flow)⟩ :=
  ⟨actual_F5_required_three_rows_are_produced_not_supplied,F3_NORMAL_shrinker_is_derived_from_the_generated_frontier⟩

#print axioms DeepExtraFrontier.encoded_counted_depth
#print axioms DeepExtraFrontier.public_initial_keeps_counted_depth
#print axioms DeepExtraFrontier.endpoint_member_is_bounded
#print axioms DeepExtraFrontier.prefix_addition_keeps_both_head_bounds
#print axioms DeepExtraFrontier.paired_addition_keeps_both_head_bounds
#print axioms DeepExtraFrontier.ALL_completed_rows_keep_both_head_bounds
#print axioms DeepExtraFrontier.every_raw_B2_public_initial_and_Target_head_has_depth_at_most_one
#print axioms DeepExtraFrontier.every_B2_C5_DATA_output_has_depth_at_most_one
#print axioms DeepExtraFrontier.read_after_global_cap_two_has_depth_at_most_one
#print axioms DeepExtraFrontier.ordinary_forward_or_opposite_read_never_increases_depth
#print axioms DeepExtraFrontier.every_F3_grammar_boundary_has_depth_at_most_one
#print axioms DeepExtraFrontier.every_F3_grammar_initial_and_Target_head_has_depth_at_most_one
#print axioms DeepExtraFrontier.every_F3_grammar_publication_handoff_has_both_heads_at_most_one
#print axioms DeepExtraFrontier.every_F3_grammar_Target_handoff_keeps_exact_original_head_bound
#print axioms DeepExtraFrontier.ALL_B4_queried_origins_are_at_most_two
#print axioms DeepExtraFrontier.ALL_B4_queried_C5_premises_are_at_most_two
#print axioms DeepExtraFrontier.ALL_B4_DATA_results_use_their_own_exit_head_bound
#print axioms DeepExtraFrontier.complete_B4_pair_reversal_keeps_both_independent_bounds
#print axioms DeepExtraFrontier.ALL_F5_extra_completion_heads_stay_at_most_two
#print axioms DeepExtraFrontier.ALL_F5_cut_commands_from_ANY_bounded_family_have_depth_at_most_two
#print axioms DeepExtraFrontier.NO_F5_extra_bounded_family_can_mask_the_real_depth_three_key
#print axioms DeepExtraFrontier.F5_full_actual_has_its_real_labelled_fine_key
#print axioms DeepExtraFrontier.every_proper_F5_scalar_trial_rejects_for_the_entire_bounded_query
#print axioms DeepExtraFrontier.every_proper_F5_trial_changes_the_entire_labelled_query
#print axioms DeepExtraFrontier.arbitrary_other_observer_components_cannot_hide_the_repeat_difference
#print axioms DeepExtraFrontier.actual_F5_mode_is_four_and_not_the_earlier_local_B4_cell
#print axioms DeepExtraFrontier.computed_arrival_supplies_the_required_scope_and_saved_shrinker

end DeepExtraFrontier
