/-
PREPARED for the root-only checker. A finite late-iteration fragment of the
small UniformPrefix mapper, not a proof of Conductor or of the whole driver.

The F3 boundary actual is the explicit source-supported uniform packet.
C2 computes its field STAR and root EXACT FLOW initials. Earlier whole-driver
arrival is not proved here. Return rows are computed from both mapper branches
with ordinary read/write/move operations and the current global limit.
B4 uses the actual same-head concrete EXACT offer, current C2, the reversed
ordinary micro-edges, complete FLOW normalization and each row's own C5 exit.
The NORMAL inverse is generated from the resulting real NORMAL row.

F5 MUST admission uses the four-tail C2 model. The two post-body MUST values
are conditional C5 candidates: producing them by native MUST read/application
is a separate adapter check. Neither is passed through the older three-kind
RootExactCleanerGap codec, which does not represent MUST. In particular the
DEMAND candidate below is not a claim that a driver has reached a fixed point
or naturally stopped at F5. No NORMAL provider or frame is supplied as input.
-/
import RootExactCleanerGap

namespace ConductorLateIterations
open PlainStarRelativeAdmission
open ApSpec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

abbrev Value := RootExactCleanerGap.Value
abbrev Row := RootExactCleanerGap.Row

def p : Nat := 10
def ret : Nat := 11
def out : Nat := 12
def part : Nat := 13
def f : Nat := 1
def g : Nat := 2
def e : Nat := 3
def h : Nat := 4
def extra : Nat := 5
def t : Nat := 7

def f3 : Mode := ⟨3,2,.forward⟩
def b4 : Mode := ⟨4,3,.backward⟩
def f5 : Mode := ⟨5,4,.forward⟩

def pat (base : Nat) (path : List Nat) (tail : Tail)
    (mark : ScalarMark := .flow) : Pattern := ⟨base,path,tail,mark,[]⟩

def val (base : Nat) (path : List Nat) (tail : Tail)
    (layer : Layer := .normal) : Value :=
  RootExactCleanerGap.value (pat base path tail) layer

def side (base : Nat) (path : List Nat) : PFact :=
  ⟨base,path,.star (.set []),.star⟩

/-- An ordinary correlated micro-edge followed by the current global limit.
There are no custom body transfer or mark-generation rules in this adapter. -/
def micro (limit : Nat) (fromBase : Nat) (fromPath : List Nat)
    (toBase : Nat) (toPath : List Nat) (input : Value) : List Value :=
  (ApSpec.Run1CorrelatedConcreteInitials.rawApply input.data
    (side fromBase fromPath) (side toBase toPath)).facts.map fun value =>
      ⟨ApSpec.limitF (fun _ => true) limit value,input.h⟩

/-- Good branch: part = p.f.g; out.e.h = part; return out. -/
def forwardGoodReturn (input : Value) : List Value :=
  (micro f3.limit p [f,g] part [] input).flatMap fun read =>
    (micro f3.limit part [] out [e,h] read).flatMap fun written =>
      micro f3.limit out [] ret [] written

/-- Bad branch: out.e.h.extra = p; return out. The exact prefix
cannot take the good read, but this real deep copy produces its coarse row. -/
def forwardBadReturn (input : Value) : List Value :=
  (micro f3.limit p [] out [e,h,extra] input).flatMap
    (micro f3.limit out [] ret [])

def forwardReturn (input : Value) : List Value :=
  forwardBadReturn input ++ forwardGoodReturn input

def f3Initials : List Seed :=
  [⟨pat p [f] .star,.normal⟩,⟨pat p [] .exact,.normal⟩]

def f3Entry : Demand := ⟨p,[],.any,.flow,[]⟩
def f3Actual : Actual := ⟨pat p [f] .must (.full t),.normal,false⟩

theorem F3_actual_C2_keeps_the_root_prefix_EXACT_until_execution :
    ExactFlowPrefixCompanion.emitSeeds f3 f3Entry f3Actual = f3Initials := by decide

def f3Rows : List Row := RootExactCleanerGap.unique (f3Initials.flatMap fun initial =>
  (forwardReturn (RootExactCleanerGap.startValue initial)).map
    (RootExactCleanerGap.publicRow initial.initial))

def f3ChildRow : Row := ⟨pat p [f] .star,val ret [e,h] .any .demand⟩
def f3RootRow : Row := ⟨pat p [] .star,val ret [e,h] .any .demand⟩

theorem generic_field_names_are_distinct :
    f ≠ g ∧ f ≠ e ∧ f ≠ h ∧ f ≠ extra ∧ g ≠ e ∧ g ≠ h ∧
      g ≠ extra ∧ e ≠ h ∧ e ≠ extra ∧ h ≠ extra := by decide

theorem F3_child_read_loses_the_unbound_suffix_into_MAY_DEMAND :
    micro 2 p [f,g] part [] (val p [f] .star) =
      [val part [] .any .demand] := by decide

theorem F3_live_EXACT_root_cannot_read_the_missing_fields :
    micro 2 p [f,g] part [] (val p [] .exact) = [] := by decide

theorem F3_live_EXACT_root_gets_its_return_from_the_deep_copy :
    forwardBadReturn (val p [] .exact) = [val ret [e,h] .any .demand] ∧
      forwardGoodReturn (val p [] .exact) = [] := by decide

theorem F3_write_and_move_keep_the_two_field_MAY_return :
    (micro 2 part [] out [e,h] (val part [] .any .demand)).flatMap
      (micro 2 out [] ret []) = [val ret [e,h] .any .demand] := by decide

theorem F3_both_return_rows_are_computed_from_the_body :
    f3Rows = [f3ChildRow,f3RootRow] := by decide

theorem F3_return_rows_do_not_supply_a_saved_NORMAL_provider :
    RootExactCleanerGap.normal f3Rows = [] := by decide

/-- A single method/root interface, reversed for B4. Complete paired rows
share an entry and keep their distinct output selectors and budgets. -/
def b4Ports : FlowDemandCompletion.Interface := ⟨42,false,0,-2,-1⟩
def guideOf (row : Row) : FlowDemandCompletion.Row :=
  ⟨b4Ports,
    .data (RootExactCleanerGap.encode (RootExactCleanerGap.uncore row.output.data.fact)),
    .data (RootExactCleanerGap.encode row.initial)⟩
def b4Guides : List FlowDemandCompletion.Row := f3Rows.map guideOf
def b4ChildGuide : FlowDemandCompletion.Row := guideOf f3ChildRow
def b4RootGuide : FlowDemandCompletion.Row := guideOf f3RootRow
def b4Entry : Demand := ⟨ret,[e,h],.any,.flow,[]⟩
def b4Actual : Actual := ⟨pat ret [e,h] .exact (.full t),.normal,false⟩
def b4Seed : Seed := ⟨pat ret [e,h] .exact,.normal⟩

theorem B4_handoff_has_two_complete_rows_with_the_same_entry :
    b4Guides = [b4ChildGuide,b4RootGuide] ∧
      RootExactCleanerGap.entry b4ChildGuide = some b4Entry ∧
      RootExactCleanerGap.entry b4RootGuide = some b4Entry ∧
      RootExactCleanerGap.exit b4ChildGuide = some (pat p [f] .star) ∧
      RootExactCleanerGap.exit b4RootGuide = some (pat p [] .star) := by decide

theorem B4_same_head_concrete_EXACT_offer_starts_raw_EXACT_FLOW_NORMAL :
    ExactFlowPrefixCompanion.emitSeeds b4 b4Entry b4Actual = [b4Seed] := by decide

theorem B4_seed_is_a_real_H_free_exact_identity :
    start b4Seed = ⟨pat ret [e,h] .exact,.normal,false⟩ := by decide

theorem B4_public_initial_has_a_constructive_C5_image :
    ConcreteStarFlowCompanion.StoredPermission b4 b4Entry
      (publicInitial b4Seed.initial) := by
  apply (ExactFlowPrefixCompanion.complete_normalized_C5_image_is_unchanged
    b4 b4Entry (publicInitial b4Seed.initial)).mpr
  exact ⟨b4Actual,b4Seed,by decide,rfl⟩

/-- Reverse return move, reverse out.e.h = part, reverse part = p.f.g.
All three are actual rawApply operations, not an injected summary. -/
def backwardReturn (input : Value) : List Value :=
  (micro b4.limit ret [] out [] input).flatMap fun moved =>
    (micro b4.limit out [e,h] part [] moved).flatMap fun read =>
      micro b4.limit part [] p [f,g] read

def b4Raw : Value := val p [f,g] .exact
def b4Public : Row :=
  RootExactCleanerGap.publicRow b4Seed.initial b4Raw
def b4NormalRow : Row := ⟨pat ret [e,h] .star,val p [f,g] .star⟩
def b4DemandRow : Row := ⟨pat ret [e,h] .star,val p [f] .any .demand⟩

theorem B4_reverse_move_and_write_reach_part_exact_NORMAL :
    (micro 3 ret [] out [] (val ret [e,h] .exact)).flatMap
      (micro 3 out [e,h] part []) = [val part [] .exact] := by decide

theorem B4_reverse_read_builds_the_raw_two_field_exact_FLOW_output :
    backwardReturn (RootExactCleanerGap.startValue b4Seed) = [b4Raw] := by decide

theorem B4_whole_FLOW_normalization_converts_both_exact_endpoints :
    b4Public = b4NormalRow := by decide

theorem B4_normalization_preserves_base_paths_layer_empty_E_and_H :
    b4Public.initial.base = ret ∧ b4Public.initial.path = [e,h] ∧
      b4Public.output = val p [f,g] .star .normal := by decide

def b4Run (row : FlowDemandCompletion.Row) : List Row :=
  match RootExactCleanerGap.entry row with
  | none => []
  | some dc => (ExactFlowPrefixCompanion.emitSeeds b4 dc b4Actual).flatMap fun seed =>
      (backwardReturn (RootExactCleanerGap.startValue seed)).filterMap
        (RootExactCleanerGap.finish b4 row seed)

def b4Rows : List Row := b4Guides.flatMap b4Run

theorem B4_each_exit_uses_its_own_relative_budget :
    AnnotatedC5Exit.pairBudget 3 (RootExactCleanerGap.toExitPattern (pat p [f] .star)) = 2 ∧
      AnnotatedC5Exit.pairBudget 3 (RootExactCleanerGap.toExitPattern (pat p [] .star)) = 1 := by decide

theorem B4_child_pair_keeps_the_raw_computation_as_NORMAL :
    b4Run b4ChildGuide = [b4NormalRow] := by decide

theorem B4_root_pair_cuts_the_same_computation_to_a_new_child_MAY_DEMAND :
    b4Run b4RootGuide = [b4DemandRow] := by decide

theorem B4_union_keeps_both_normal_and_demand_results :
    b4Rows = [b4NormalRow,b4DemandRow] := by decide

theorem B4_equal_entry_is_not_permission_to_borrow_the_other_exit_budget :
    b4NormalRow ≠ b4DemandRow ∧ b4Run b4RootGuide ≠ [b4NormalRow] ∧
      b4Run b4ChildGuide ≠ [b4DemandRow] := by decide

def savedInverse : List Row :=
  (RootExactCleanerGap.normal b4Rows).map RootExactCleanerGap.reverseNormal
def savedForwardRow : Row := ⟨pat p [f,g] .star,val ret [e,h] .star⟩

theorem B4_only_the_real_NORMAL_result_is_saved_and_reversed :
    savedInverse = [savedForwardRow] := by decide

theorem B4_public_NORMAL_pair_and_its_inverse_use_only_STAR_EMPTY_E :
    b4NormalRow.initial = pat ret [e,h] .star ∧
      savedForwardRow.initial = pat p [f,g] .star ∧
      savedForwardRow.output = val ret [e,h] .star := by decide

/-- Only the real B4 DEMAND result supplies the next handoff. The already
derived NORMAL inverse above is not turned into a demand permission. -/
def f5Guides : List FlowDemandCompletion.Row := RootExactCleanerGap.handoff f5 b4Rows
def f5Guide : FlowDemandCompletion.Row :=
  ⟨⟨42,true,0,-1,-2⟩,
    .data (RootExactCleanerGap.encode (pat p [f] .any)),
    .data (RootExactCleanerGap.encode (pat ret [e,h] .star))⟩
def f5Entry : Demand := ⟨p,[f],.any,.flow,[]⟩
def f5Actual : Actual := ⟨pat p [f] .must (.full t),.normal,false⟩
def f5Seed : Seed := ⟨pat p [f] .must,.normal⟩

theorem F5_new_child_guide_comes_from_the_B4_relative_cut :
    f5Guides = [f5Guide] ∧ RootExactCleanerGap.entry f5Guide = some f5Entry ∧
      RootExactCleanerGap.exit f5Guide = some (pat ret [e,h] .star) := by decide

theorem F5_actual_MUST_keeps_MUST_and_NORMAL_in_its_FLOW_initial :
    ExactFlowPrefixCompanion.emitSeeds f5 f5Entry f5Actual = [f5Seed] := by decide

theorem F5_identity_start_is_MUST_FLOW_NORMAL_with_no_ANY_codec :
    start f5Seed = ⟨pat p [f] .must,.normal,false⟩ := by decide

theorem F5_MUST_initial_has_a_constructive_C5_image :
    ConcreteStarFlowCompanion.StoredPermission f5 f5Entry
      (publicInitial f5Seed.initial) := by
  apply (ExactFlowPrefixCompanion.complete_normalized_C5_image_is_unchanged
    f5 f5Entry (publicInitial f5Seed.initial)).mpr
  exact ⟨f5Actual,f5Seed,by decide,rfl⟩

theorem F5_MUST_image_is_accepted_by_the_executable_entry_check :
    RootExactCleanerGap.stores f5 f5Entry f5Seed.initial = true := by decide

/-! From this point MUST is represented directly in AnnotatedC5Exit.
The following two post-body candidate values are not a native MUST producer
proof. They show what the same real paired exit must keep and must cut. -/
def exitFact (path : List Nat) (tail : RelativeRestriction.Tail)
    (layer : RelativeRestriction.Layer) (flag : Bool := false) : AnnotatedC5Exit.Fact :=
  ⟨⟨ret,path.map RelativeRestriction.Accessor.field,tail,.flow [],[]⟩,layer,flag⟩
def f5Exit : AnnotatedC5Exit.Pattern :=
  RootExactCleanerGap.toExitPattern (pat ret [e,h] .star)
def goodMUST : AnnotatedC5Exit.Fact := exitFact [e,h] .must .normal
def badMUST : AnnotatedC5Exit.Fact := exitFact [e,h,extra,f] .must .normal
def badMAY : AnnotatedC5Exit.Fact := exitFact [e,h,extra] .may .demand

/-- One complete entry/exit ticket; the entry image does not supply output
support. The candidate output still has to pass this ticket's own C5 exit. -/
def finishF5MUST (raw : AnnotatedC5Exit.Fact) : Option AnnotatedC5Exit.Fact :=
  if RootExactCleanerGap.stores f5 f5Entry f5Seed.initial then
    AnnotatedC5Exit.restrictData true f5.limit raw f5Exit
  else none

theorem F5_pair_budget_is_three_although_global_limit_is_four :
    AnnotatedC5Exit.pairBudget f5.limit f5Exit = 3 := by decide

theorem F5_good_MUST_candidate_is_kept_with_NORMAL_support :
    finishF5MUST goodMUST = some goodMUST := by decide

theorem F5_bad_MUST_candidate_fits_the_global_limit :
    RelativeRestriction.depth badMUST.path = 4 ∧
      AnnotatedC5Exit.cut f5.limit badMUST = badMUST := by decide

theorem F5_same_paired_exit_cuts_the_bad_candidate_to_MAY_DEMAND :
    finishF5MUST badMUST = some badMAY := by decide

theorem F5_cut_does_not_borrow_the_global_budget_or_keep_NORMAL :
    finishF5MUST badMUST ≠ some badMUST ∧ badMAY.layer = .demand ∧
      badMAY.tail = .may ∧ badMAY.exclusion = [] := by decide

theorem F5_MUST_checks_do_not_identify_the_good_and_bad_outputs :
    goodMUST ≠ badMUST ∧ goodMUST ≠ badMAY := by decide

theorem F5_good_and_cut_outputs_transport_the_input_H (flag : Bool) :
    finishF5MUST (exitFact [e,h] .must .normal flag) =
      some (exitFact [e,h] .must .normal flag) ∧
    finishF5MUST (exitFact [e,h,extra,f] .must .normal flag) =
      some (exitFact [e,h,extra] .may .demand flag) := by
  cases flag <;> decide

theorem F5_relative_exit_can_still_leave_a_DEMAND_candidate :
    ∃ kept, finishF5MUST badMUST = some kept ∧ kept.layer = .demand :=
  ⟨badMAY,F5_same_paired_exit_cuts_the_bad_candidate_to_MAY_DEMAND,rfl⟩

#print axioms generic_field_names_are_distinct
#print axioms F3_child_read_loses_the_unbound_suffix_into_MAY_DEMAND
#print axioms F3_actual_C2_keeps_the_root_prefix_EXACT_until_execution
#print axioms F3_live_EXACT_root_cannot_read_the_missing_fields
#print axioms F3_live_EXACT_root_gets_its_return_from_the_deep_copy
#print axioms F3_write_and_move_keep_the_two_field_MAY_return
#print axioms F3_both_return_rows_are_computed_from_the_body
#print axioms F3_return_rows_do_not_supply_a_saved_NORMAL_provider
#print axioms B4_handoff_has_two_complete_rows_with_the_same_entry
#print axioms B4_same_head_concrete_EXACT_offer_starts_raw_EXACT_FLOW_NORMAL
#print axioms B4_seed_is_a_real_H_free_exact_identity
#print axioms B4_public_initial_has_a_constructive_C5_image
#print axioms B4_reverse_move_and_write_reach_part_exact_NORMAL
#print axioms B4_reverse_read_builds_the_raw_two_field_exact_FLOW_output
#print axioms B4_whole_FLOW_normalization_converts_both_exact_endpoints
#print axioms B4_normalization_preserves_base_paths_layer_empty_E_and_H
#print axioms B4_each_exit_uses_its_own_relative_budget
#print axioms B4_child_pair_keeps_the_raw_computation_as_NORMAL
#print axioms B4_root_pair_cuts_the_same_computation_to_a_new_child_MAY_DEMAND
#print axioms B4_union_keeps_both_normal_and_demand_results
#print axioms B4_equal_entry_is_not_permission_to_borrow_the_other_exit_budget
#print axioms B4_only_the_real_NORMAL_result_is_saved_and_reversed
#print axioms B4_public_NORMAL_pair_and_its_inverse_use_only_STAR_EMPTY_E
#print axioms F5_new_child_guide_comes_from_the_B4_relative_cut
#print axioms F5_actual_MUST_keeps_MUST_and_NORMAL_in_its_FLOW_initial
#print axioms F5_identity_start_is_MUST_FLOW_NORMAL_with_no_ANY_codec
#print axioms F5_MUST_initial_has_a_constructive_C5_image
#print axioms F5_MUST_image_is_accepted_by_the_executable_entry_check
#print axioms F5_pair_budget_is_three_although_global_limit_is_four
#print axioms F5_good_MUST_candidate_is_kept_with_NORMAL_support
#print axioms F5_bad_MUST_candidate_fits_the_global_limit
#print axioms F5_same_paired_exit_cuts_the_bad_candidate_to_MAY_DEMAND
#print axioms F5_cut_does_not_borrow_the_global_budget_or_keep_NORMAL
#print axioms F5_MUST_checks_do_not_identify_the_good_and_bad_outputs
#print axioms F5_good_and_cut_outputs_transport_the_input_H
#print axioms F5_relative_exit_can_still_leave_a_DEMAND_candidate

end ConductorLateIterations
