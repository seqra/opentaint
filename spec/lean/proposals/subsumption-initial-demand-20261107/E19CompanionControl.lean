import StaticFlowCompletion
import E21OperatorLedger

/- The earlier E19 static interface, now with the selected expanded C2.
No completed demand row is used. This is an interface control, not a native
prescan/static-carry correspondence theorem. -/
namespace E19CompanionControl
open PlainStarRelativeAdmission FlowCompletionOperational

def outputPattern (d : Demand) : Pattern :=
  ⟨d.base,d.path,
    match d.shape with | .exact => .exact | .star => .star | .any => .any,
    d.mark,d.exclusion⟩

def originalOnly (written : Nat) : List (Pattern × Actual) :=
  match encodePair originalStaticRow with
  | none => []
  | some pair =>
    (RejectAncestorStarAdmission.emitSeeds b2 pair.entry actualRun2).filterMap fun seed => do
      let raw ← strongNamedWrite written (start seed)
      E21OperatorLedger.finishData b2 pair.entry (some (outputPattern pair.exit)) seed raw

theorem FLOW_provider_exists_under_the_original_T_pair :
    (qStar,⟨qStar,.normal,false⟩) ∈ originalOnly 8 := by decide

theorem original_pair_also_keeps_the_primary_T_DEMAND_before_backing :
    (({qStar with mark := .full 7}),⟨{qStar with mark := .full 7},.demand,false⟩) ∈
      originalOnly 8 := by decide

theorem strong_same_field_write_still_kills_both_seeds : originalOnly 9 = [] := by decide

theorem inferred_NORMAL_FLOW_transports_the_real_precise_descendant :
    applySaved staticExpected preciseSource = some preciseSource := by decide

end E19CompanionControl
