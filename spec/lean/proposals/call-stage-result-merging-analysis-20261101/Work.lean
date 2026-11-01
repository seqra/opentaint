import Suffix

/-!
Executable local workload controls. Producer effects already happened before
collection; only equal downstream continuation executions are removed.
Lookup/allocation costs and separate replay invocations remain explicit limits.
-/
namespace CallStageMerge
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def fixtureScope : Scope :=
  ⟨0, 0, 0, 0, .unknown, .demand, .demand, false⟩

def fixturePayload : Payload :=
  ⟨.taint, 0, 0, .may, Bits.zero, Bits.zero, .full .t, ⟨true, false, false, false⟩⟩

def aliasKey : Key := ⟨fixtureScope, fixturePayload⟩
def aliasResult : Row := plain aliasKey

def identityResult : Row :=
  plain ⟨fixtureScope, { fixturePayload with base := 1 }⟩

def aliasResults : List Row := List.replicate 64 aliasResult
def wholeResults : List Row := aliasResults ++ [identityResult]

theorem alias_has_64_equal_results : aliasResults.length = 64 := by decide

theorem alias_merges_to_one_exact_result : normalize aliasResults = [aliasResult] := by decide

theorem whole_has_65_results : wholeResults.length = 65 := by decide

theorem separate_identity_keeps_two_results :
    normalize wholeResults = [aliasResult, identityResult] := by decide

def downstreamWork (rows : List Row) (suffixSteps : Nat) : Nat := rows.length * suffixSteps

theorem old_alias_work (steps : Nat) : downstreamWork aliasResults steps = 64 * steps := by
  rw [downstreamWork, alias_has_64_equal_results]

theorem merged_alias_work (steps : Nat) :
    downstreamWork (normalize aliasResults) steps = steps := by
  rw [alias_merges_to_one_exact_result]
  simp [downstreamWork]

theorem old_total_work (steps : Nat) : downstreamWork wholeResults steps = 65 * steps := by
  rw [downstreamWork, whole_has_65_results]

theorem merged_total_work (steps : Nat) :
    downstreamWork (normalize wholeResults) steps = 2 * steps := by
  rw [separate_identity_keeps_two_results]
  rfl

theorem original_stage_still_has_64_producer_effects : aliasResults.length = 64 := by decide

theorem alias_ordinary_and_protected_sets_equal (observation : Observation) :
    observe (normalize wholeResults) observation = observe wholeResults observation := by
  exact normalize_observation wholeResults observation

/-- No unconditional time win is claimed: a collector has a cost too. -/
def estimatedCollectedWork (suffixSteps lookupCost : Nat) : Nat :=
  64 * lookupCost + 2 * suffixSteps

theorem cost_win_requires_enough_repeated_suffix_work (steps lookupCost : Nat) :
    estimatedCollectedWork steps lookupCost < 65 * steps ↔ 64 * lookupCost < 63 * steps := by
  unfold estimatedCollectedWork
  have splitTotal : 65 * steps = 63 * steps + 2 * steps := Nat.add_mul 63 2 steps
  rw [splitTotal]
  exact Nat.add_lt_add_iff_right

def allowsAlias (scope : Scope) : Bool :=
  scope.layer == .demand || scope.identity != .yes

def finalLayer (scope : Scope) : Layer :=
  if scope.pendingDemotion then .demand else scope.layer

theorem identity_flag_is_part_of_the_key :
    ({ fixtureScope with layer := .normal, identity := .yes } : Scope) ≠
      { fixtureScope with layer := .normal, identity := .no } ∧
    allowsAlias { fixtureScope with layer := .normal, identity := .yes } = false ∧
    allowsAlias { fixtureScope with layer := .normal, identity := .no } = true := by decide

theorem pending_demotion_is_part_of_the_key :
    finalLayer { fixtureScope with layer := .normal, pendingDemotion := false } = .normal ∧
    finalLayer { fixtureScope with layer := .normal, pendingDemotion := true } = .demand := by decide

theorem different_originals_remain_two_rows :
    (normalize [aliasResult,
      plain ⟨{ fixtureScope with original := 1 }, fixturePayload⟩]).length = 2 := by decide

def flowResult : Row :=
  plain ⟨fixtureScope, { fixturePayload with kind := .flow, mark := .flow }⟩

def reachResult : Row :=
  plain ⟨fixtureScope, { fixturePayload with kind := .reach, tail := .exact, mark := .zero }⟩

theorem three_fact_kinds_stay_separate :
    (normalize [aliasResult, flowResult, reachResult]).length = 3 := by decide

theorem different_full_marks_stay_separate :
    (normalize [aliasResult,
      plain ⟨fixtureScope, { fixturePayload with mark := .full .u }⟩]).length = 2 := by decide

def protectedAlias : Row := ⟨aliasKey, ⟨true, false, false, false⟩⟩

theorem plain_after_protected_keeps_the_flag :
    protectedMember (normalize [protectedAlias, aliasResult]) aliasKey .s0 := by
  unfold protectedMember
  decide

def twoMemberKey : Key :=
  ⟨fixtureScope, { fixturePayload with members := ⟨true, true, false, false⟩ }⟩

theorem incomparable_protection_bits_are_joined :
    (normalize [⟨twoMemberKey, ⟨true, false, false, false⟩⟩,
      ⟨twoMemberKey, ⟨false, true, false, false⟩⟩]).map Row.protection =
      [⟨true, true, false, false⟩] := by decide

theorem both_protected_members_survive :
    protectedMember (normalize [⟨twoMemberKey, ⟨true, false, false, false⟩⟩,
      ⟨twoMemberKey, ⟨false, true, false, false⟩⟩]) twoMemberKey .s0 ∧
    protectedMember (normalize [⟨twoMemberKey, ⟨true, false, false, false⟩⟩,
      ⟨twoMemberKey, ⟨false, true, false, false⟩⟩]) twoMemberKey .s1 := by
  unfold protectedMember
  decide

end CallStageMerge
