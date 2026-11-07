/- Operator transaction ledger only, not a full fixed-point/native driver. -/
import DeepGuidanceArrival
import RejectAncestorStarAdmission

namespace E21OperatorLedger
open PlainStarRelativeAdmission
open DeepFlowCompletion
open DeepGuidanceArrival

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

-- This finite query classifier is the selected companion StoredPermission
-- branch specialized to this scalar FULL/EmptyE program. It retains the
-- primary's containment before changing only its mark. No history is added.
def stores (mode : Mode) (d : Demand) (stored : Pattern) : Bool :=
  canStoreInitial mode d stored ||
    match stored.tail,stored.mark,d.mark with
    | .star,.flow,.full mark =>
        let primary := {stored with mark := .full mark}
        rawImage mode d primary && insideDemand d primary
    | _,_,_ => false

def publicData (initial : Pattern) (value : Actual) : Actual :=
  if initial.mark = .flow ∧ value.pattern.mark = .flow then
    {value with pattern := publicInitial value.pattern} else value

def finishData (mode : Mode) (d : Demand) (exit : Option Pattern) (seed : Seed)
    (raw : Actual) : Option (Pattern × Actual) := do
  let original := publicInitial seed.initial
  if !stores mode d original then none else
    let selector ← exit
    let value := publicData original raw
    let kept ← AnnotatedC5Exit.restrictData (isForward mode) mode.limit
      (asExitFact value) (asExitPattern selector)
    let result ← fromExit kept
    pure (original,{result with pattern := publicInitial result.pattern})

def d (head : List Nat) (shape : Shape) (mark : ScalarMark := T) : Demand :=
  ⟨x,head,shape,mark,[]⟩

def backwardTransactions (mode : Mode) (entry : Demand) (exit : Option Pattern)
    (submitted : Actual) : List (Pattern × Actual) :=
  (RejectAncestorStarAdmission.emitSeeds mode entry submitted).filterMap fun seed =>
    finishData mode entry exit seed (backwardReadAt mode.limit (start seed))

def forwardTransactions (mode : Mode) (entry : Demand) (exit : Option Pattern)
    (submitted : Actual) : List (Pattern × Actual) :=
  (RejectAncestorStarAdmission.emitSeeds mode entry submitted).filterMap fun seed => do
    let raw ← forwardRead (start seed)
    finishData mode entry exit seed raw

-- All commands and all paired DATA selections for each declared transaction.
def b2RootFlowRaw := RejectAncestorStarAdmission.emitSeeds modeB2 (d [] .any .flow)
  (actual [] .exact .normal)
def b2RootFlowPublic := backwardTransactions modeB2 (d [] .any .flow)
  (some (p [] .star .flow)) (actual [] .exact .normal)
def b2FineFlowPublic := backwardTransactions modeB2 (d [] .any .flow)
  (some (p [] .star .flow)) (actual [f] .exact .normal)
def b2ConcreteAndCompanion := backwardTransactions modeB2 (d [] .any T)
  (some (p [] .star T)) (actual [f] .any .demand)

def f3ShrinkerWithoutCompletion := forwardTransactions modeF3 (d [f] .any .flow)
  (some (p [f] .star .flow)) (actual [f] .any .demand)
def f3ConcreteAndCompanion := forwardTransactions modeF3 (d [f] .any T)
  (some (p [f] .star T)) (actual [f] .any .demand)

def b4ZeroExitCommands := RejectAncestorStarAdmission.emitSeeds modeB4 (d [f] .any T)
  (actual [f,f,f] .exact .normal)
def b4ZeroExitData := backwardTransactions modeB4 (d [f] .any T) none
  (actual [f,f,f] .exact .normal)
def b4SelfCompletionData := backwardTransactions modeB4 (d [f] .any .flow)
  (some (p [f] .any .flow)) (actual [f,f,f] .exact .normal)
def f5RawCommands := RejectAncestorStarAdmission.emitSeeds modeF5 (d [f,f] .any .flow) rawF5
def f5DepthTwoCommands := RejectAncestorStarAdmission.emitSeeds modeF5 (d [f,f] .any .flow) (cutAt 2 rawF5)

def ancestorChecks : List (Shape × ScalarMark × List Seed) :=
  ([((.any : Shape),T),(.star,T),(.exact,T),(.any,.flow),(.star,.flow)] : List (Shape × ScalarMark)).map fun selector =>
    let shape := selector.1
    let mark := selector.2
    (shape,mark,RejectAncestorStarAdmission.emitSeeds modeF3 (d [f] shape mark)
      (actual [] .star (if mark = .flow then .normal else .demand) mark))

def checks : List (String × Bool) := [
  ("B2 raw root key is EXACT/FLOW before public normalization",
    decide (b2RootFlowRaw = [⟨p [] .exact .flow,.normal⟩])),
  ("B2 NORMAL grower exists without FLOW completion",
    decide (b2RootFlowPublic = [(p [] .star .flow,actual [f] .star .normal .flow)])),
  ("F3 NORMAL shrinker exists from original DEMAND FLOW family",
    decide (f3ShrinkerWithoutCompletion = [(p [f] .star .flow,actual [] .star .normal .flow)])),
  ("B4 concrete STAR and FLOW companion commands both exist",
    decide (b4ZeroExitCommands = [⟨p [f,f] .star T,.demand⟩,⟨p [f,f] .star .flow,.normal⟩])),
  ("The same ZERO exit rejects ALL their DATA results",decide (b4ZeroExitData = [])),
  ("FLOW self completion permits real B4 DEMAND FLOW family",
    decide (b4SelfCompletionData = [(p [f,f] .star .flow,actual [f,f] .any .demand .flow)])),
  ("F5 raw depth3 and cut depth2 command streams differ",decide (f5RawCommands ≠ f5DepthTwoCommands)),
  ("ALL strict ancestor STAR example cells reject",ancestorChecks.all fun row => row.2.2.isEmpty)
]

#eval ("E21_OPERATOR_LEDGER_NOT_A_FULL_DRIVER",reprStr b2RootFlowRaw)
#eval ("B2_ROOT_FLOW_PUBLIC_ALL",reprStr b2RootFlowPublic)
#eval ("B2_FINE_FLOW_PUBLIC_ALL",reprStr b2FineFlowPublic)
#eval ("B2_CONCRETE_AND_COMPANION_ALL",reprStr b2ConcreteAndCompanion)
#eval ("F3_SHRINKER_WITHOUT_COMPLETION_ALL",reprStr f3ShrinkerWithoutCompletion)
#eval ("F3_CONCRETE_AND_COMPANION_ALL",reprStr f3ConcreteAndCompanion)
#eval ("B4_ZERO_EXIT_COMMANDS_ALL",reprStr b4ZeroExitCommands)
#eval ("B4_ZERO_EXIT_DATA_ALL",reprStr b4ZeroExitData)
#eval ("B4_SELF_COMPLETION_DATA_ALL",reprStr b4SelfCompletionData)
#eval ("F5_RAW_COMMANDS_ALL",reprStr f5RawCommands)
#eval ("F5_CUT2_COMMANDS_ALL",reprStr f5DepthTwoCommands)
#eval ("ANCESTOR_STAR_CELLS_ALL",reprStr ancestorChecks)
#eval ("E21_OPERATOR_CHECKS",reprStr checks)
#eval ("E21_OPERATOR_CHECKS_ALL_TRUE=" ++ toString (checks.all Prod.snd))

theorem all_declared_operator_checks_pass : checks.all Prod.snd = true := by decide

end E21OperatorLedger
