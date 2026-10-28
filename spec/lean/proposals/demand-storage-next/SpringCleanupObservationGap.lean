/-
PROPOSAL ONLY, 2026-10-28. No runtime behavior is selected by this file.

Local counterexample: a reachable ZERO cleanup call has an unconditional exit
sink. A transfer-only model can preserve control/static transfer while losing
that sink observation. This model does not assert that every provider rule is
unconditional. Conditional/ND rules need their original complete guard and
source/origin semantics if an event-aware predefined model is selected.
-/
import Init

namespace DemandStorageNext.SpringCleanupObservationGap
set_option autoImplicit false

structure Transfer where
  zeroReturns : Bool
  registryIdentity : Bool
  otherStaticReturns : Bool

structure Observable where
  transfer : Transfer
  exitReports : List Nat

def cleanupTransfer : Transfer := ⟨true, true, false⟩

/-- One genuine ZERO invocation and one matching unconditional method-exit sink. -/
def ordinaryZeroInvocation (sinkId : Nat) : Observable :=
  ⟨cleanupTransfer, [sinkId]⟩

/-- Complete transfer rows alone do not include provider observations. -/
def rowsOnlyInvocation : Observable := ⟨cleanupTransfer, []⟩

theorem equal_transfer (sinkId : Nat) :
    (ordinaryZeroInvocation sinkId).transfer = rowsOnlyInvocation.transfer := rfl

theorem different_observations (sinkId : Nat) :
    (ordinaryZeroInvocation sinkId).exitReports ≠ rowsOnlyInvocation.exitReports := by
  intro equal
  cases equal

theorem not_observably_equal (sinkId : Nat) :
    ordinaryZeroInvocation sinkId ≠ rowsOnlyInvocation := by
  intro equal
  exact different_observations sinkId (congrArg Observable.exitReports equal)

/-- Explicit observation events require no method CFG execution in this model. -/
def completeEventModelInvocation (sinkId : Nat) : Observable :=
  ⟨cleanupTransfer, [sinkId]⟩

theorem explicit_event_model_preserves_example (sinkId : Nat) :
    completeEventModelInvocation sinkId = ordinaryZeroInvocation sinkId := rfl

#print axioms equal_transfer
#print axioms different_observations
#print axioms not_observably_equal
#print axioms explicit_event_model_preserves_example

end DemandStorageNext.SpringCleanupObservationGap
