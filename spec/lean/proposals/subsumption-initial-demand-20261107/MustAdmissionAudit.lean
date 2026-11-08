/-
Read-only remaining-obligation audit. This computes the complete selected C2
streams at the real E29 root/child coordinate pattern, including the latest
EXACT/FLOW prefix companion. It is NOT a new whole-program false-negative
example and does not assume a missing NORMAL method provider. The source is
a legal uniform source at p.f; actual E29/query and finite source/mapper
programs are already captured natively in the linked report/catalog.
-/
import ExactFlowPrefixCompanion
import WrapperRecovery
import ConcreteConverterWrapper

namespace MustAdmissionAudit
open PlainStarRelativeAdmission
open ApSpec

def mode : Mode := ⟨3,2,.forward⟩
def f : Nat := 4
def g : Nat := 5
def base : Nat := PlainStarWrapperRecovery.argBase
def root : Demand := ⟨base,[],.any,.flow,[]⟩
def child : Demand := ⟨base,[f],.any,.flow,[]⟩
def actual : Actual := ⟨⟨base,[f],.must,.full 7,[]⟩,.normal,false⟩
def starSeed : Seed := ⟨⟨base,[f],.star,.flow,[]⟩,.normal⟩
def prefixSeed : Seed := ⟨⟨base,[],.exact,.flow,[]⟩,.normal⟩
def mustSeed : Seed := ⟨⟨base,[f],.must,.flow,[]⟩,.normal⟩

def coarse : List Seed := ExactFlowPrefixCompanion.emitSeeds mode root actual
def fine : List Seed := ExactFlowPrefixCompanion.emitSeeds mode child actual
def twoReads (seed : Seed) : Option Actual :=
  (PlainStarWrapperRecovery.readForward 2 f (start seed)).bind
    (PlainStarWrapperRecovery.readForward 2 g)

def nativePrefixRead : ApSpec.Res :=
  ApSpec.Run1CorrelatedConcreteInitials.rawApply
    ⟨⟨base,[],.exact,.star⟩,false⟩
    ⟨base,[f],.star (.set []),.star⟩
    ⟨PlainStarWrapperRecovery.retBase,[],.star (.set []),.star⟩

theorem complete_coarse_stream_still_does_not_preserve_uniformness :
    coarse = [starSeed,prefixSeed] := by decide

theorem complete_fine_stream_preserves_the_actual_MUST : fine = [mustSeed] := by decide

theorem latest_prefix_does_not_replace_the_removed_MUST_command :
    mustSeed ∉ coarse ∧ mustSeed ∈ fine := by decide

theorem spatially_covered_child_changes_the_complete_C2_observation :
    coarse ≠ coarse ++ fine := by decide

theorem retained_STAR_query_loses_uniformness_on_the_second_read :
    twoReads starSeed = some
      ⟨⟨PlainStarWrapperRecovery.retBase,[],.any,.flow,[]⟩,.demand,false⟩ := by decide

theorem exact_prefix_cannot_read_the_missing_first_field :
    twoReads prefixSeed = none ∧ nativePrefixRead.facts = [] := by decide

theorem observed_query_has_legal_normal_uniform_source_support :
    legalActual mode actual ∧ actual.layer = .normal ∧ actual.hasProtection = false ∧
      root.path.length ≤ mode.limit ∧ child.path.length ≤ mode.limit := by decide

end MustAdmissionAudit

#print axioms MustAdmissionAudit.complete_coarse_stream_still_does_not_preserve_uniformness
#print axioms MustAdmissionAudit.complete_fine_stream_preserves_the_actual_MUST
#print axioms MustAdmissionAudit.latest_prefix_does_not_replace_the_removed_MUST_command
#print axioms MustAdmissionAudit.spatially_covered_child_changes_the_complete_C2_observation
#print axioms MustAdmissionAudit.retained_STAR_query_loses_uniformness_on_the_second_read
#print axioms MustAdmissionAudit.exact_prefix_cannot_read_the_missing_first_field
#print axioms MustAdmissionAudit.observed_query_has_legal_normal_uniform_source_support
