/-
Local continuation audit only. The larger B6/F7 attempt is preserved under
unverified/E21LatestContinuation.lean and failed the root resource check.
These eight local laws do not prove its later family closure or convergence.
The typed-Zero adapter is confined to the borrowed raw model terminal.
-/
import E21PrefixExactCompanion

namespace E21LateLocalAudit
open PlainStarRelativeAdmission DeepFlowCompletion DeepGuidanceArrival E21ClosedFamilies
set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def canonicalTypedZero (value : ApSpec.AFact) : ApSpec.AFact :=
  if value.fact.base = zeroTo.base ∧ value.fact.path = zeroTo.path ∧
      value.fact.mark = zeroTo.mark ∧ value.fact.kind = .star .univ then
    {value with fact := zeroTo}
  else value

def readTypedZero (premisePattern : Pattern) (input : Actual) : Option Layer := do
  let premise ← toAP ⟨premisePattern,intrinsic premisePattern,false⟩
  let scalar ← toAP input
  let result := ApSpec.Run1CorrelatedConcreteInitials.rawApply scalar premise.fact zeroTo
  match result.facts with
  | [raw] =>
      let kept := canonicalTypedZero raw
      if kept.fact = zeroTo then some (if kept.demand then .demand else .normal) else none
  | _ => none

def lateSourceReach (input : Actual) : Option Layer :=
  readTypedZero (p [f,f,f,f] .exact T) input


def completed5 := E21PrefixExactCompanion.completed5
def rootDemandImage : Actual := actual [] .any .demand

def shrinkTwice (input : Actual) : Option Actual := do
  let first ← shrinkByDerived input
  shrinkByDerived first

def rootFlowD : Edge :=
  ⟨.data (p [] .star .flow),.data (actual [] .any .demand .flow)⟩

def realRootFlowD : List Edge :=
  allSelected modeF5 completed5
    ((commands modeF5 completed5 [rootDemandImage]).flatMap (body modeF5 false))

structure OwnedNormal where
  original : Original
  reportId : Nat
  scope : Nat
deriving DecidableEq, Repr

def keepTarget (saved : List OwnedNormal) (scope reportId : Nat) (row : Edge) : Bool :=
  match row.result with
  | .target .normal => !saved.contains ⟨row.original,reportId,scope⟩
  | _ => true

def known5 : List OwnedNormal :=
  [⟨.zero,0,0⟩,⟨.data (p [f] .exact T),0,2⟩]

theorem old_readToZero_misses_the_same_head_STAR_zero_normal_form :
    sourceReach (actual [f,f,f,f] .star .demand) = none := by decide

theorem typed_ZERO_adapter_recovers_same_head_STAR_source_DEMAND :
    lateSourceReach (actual [f,f,f,f] .star .demand) = some .demand := by decide

theorem typed_ZERO_adapter_keeps_exact_source_NORMAL :
    lateSourceReach (actual [f,f,f,f] .exact .normal) = some .normal := by decide

theorem typed_ZERO_adapter_does_not_satisfy_source_with_FLOW :
    lateSourceReach (actual [f,f,f,f] .star .normal .flow) = none := by decide

theorem typed_ZERO_adapter_preserves_pre_R6_backward_source_cells :
    (actualUniverse modeB4 [0,1,2,3] false).all (fun a => decide
      (lateSourceReach (backwardReadAt 3 a) = sourceReach (backwardReadAt 3 a))) = true := by decide

theorem the_shorter_F5_SOURCE_image_reaches_a_real_root_MAY :
    shrinkTwice (cutAt 2 rawF5) = some rootDemandImage := by decide

theorem the_new_F5_FLOW_DEMAND_family_is_accepted_by_a_complete_pair :
    rootFlowD ∈ realRootFlowD := by decide

theorem normal_target_persistence_does_not_suppress_DemandTarget :
    keepTarget known5 2 0 ⟨.data (p [f] .exact T),.target .demand⟩ = true ∧
    keepTarget known5 2 0 ⟨.data (p [f] .exact T),.target .normal⟩ = false := by decide


#print axioms E21LateLocalAudit.old_readToZero_misses_the_same_head_STAR_zero_normal_form
#print axioms E21LateLocalAudit.typed_ZERO_adapter_recovers_same_head_STAR_source_DEMAND
#print axioms E21LateLocalAudit.typed_ZERO_adapter_keeps_exact_source_NORMAL
#print axioms E21LateLocalAudit.typed_ZERO_adapter_does_not_satisfy_source_with_FLOW
#print axioms E21LateLocalAudit.typed_ZERO_adapter_preserves_pre_R6_backward_source_cells
#print axioms E21LateLocalAudit.the_shorter_F5_SOURCE_image_reaches_a_real_root_MAY
#print axioms E21LateLocalAudit.the_new_F5_FLOW_DEMAND_family_is_accepted_by_a_complete_pair
#print axioms E21LateLocalAudit.normal_target_persistence_does_not_suppress_DemandTarget

#eval ("E21_LATE_LOCAL_REAL_FLOW_D",reprStr realRootFlowD)

end E21LateLocalAudit
