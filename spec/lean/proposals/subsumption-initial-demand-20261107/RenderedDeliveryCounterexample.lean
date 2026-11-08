/-
Contract countermodel only, not an observed Kotlin defect. Uses the exact
checked U/H coverage reference. A transport which publishes only additions
to OR-rendered rows cannot reproduce the producer's hidden U certificates
at a downstream owner. Same final producer views need not imply equal
downstream canonical basis. No new runtime mechanism is proposed here.
-/
import PlainCoverageFlagViews

namespace RenderedDeliveryCounterexample
open PlainCoverageFlagViews
open FlagMatchedSubsumption (Row)

structure Link where
  producer : Views := emptyViews
  consumer : Views := emptyViews
deriving DecidableEq

def visibleDelta (before after : Views) : List Row :=
  (render after).filter fun row => decide (row ∉ render before)

def forwardRendered (link : Link) (incoming : Row) : Link :=
  let after := offer link.producer incoming
  ⟨after,(visibleDelta link.producer after).foldl offer link.consumer⟩

def execute (arrivals : List Row) : Link := arrivals.foldl forwardRendered ⟨emptyViews,emptyViews⟩

def protectedFirst : Link := execute [parent true,parent false]
def plainFirst : Link := execute [parent false,parent true]
def childAfterProtectedFirst : Views := offer protectedFirst.consumer (child false)
def childAfterPlainFirst : Views := offer plainFirst.consumer (child false)

theorem both_orders_have_the_same_complete_producer_authority :
    protectedFirst.producer = plainFirst.producer ∧
    protectedFirst.producer = ⟨[parentGeometry],[parentGeometry]⟩ := by decide

theorem both_orders_have_the_same_single_visible_producer_row :
    render protectedFirst.producer = [parent true] ∧
    render plainFirst.producer = [parent true] := by decide

theorem late_plain_certificate_changes_authority_without_a_visible_delta :
    offer (run [parent true]) (parent false) ≠ run [parent true] ∧
    visibleDelta (run [parent true]) (offer (run [parent true]) (parent false)) = [] := by decide

theorem downstream_loses_plain_authority_only_in_protected_first_order :
    protectedFirst.consumer = ⟨[],[parentGeometry]⟩ ∧
    plainFirst.consumer = ⟨[parentGeometry],[parentGeometry]⟩ := by decide

theorem downstream_plain_child_coverage_is_arrival_order_dependent :
    logicalCover protectedFirst.consumer (child false) = false ∧
    logicalCover plainFirst.consumer (child false) = true := by decide

theorem downstream_visible_basis_is_different_after_the_same_plain_child :
    render childAfterProtectedFirst = [parent true,child false] ∧
    render childAfterPlainFirst = [parent true] := by decide

end RenderedDeliveryCounterexample

#print axioms RenderedDeliveryCounterexample.both_orders_have_the_same_complete_producer_authority
#print axioms RenderedDeliveryCounterexample.both_orders_have_the_same_single_visible_producer_row
#print axioms RenderedDeliveryCounterexample.late_plain_certificate_changes_authority_without_a_visible_delta
#print axioms RenderedDeliveryCounterexample.downstream_loses_plain_authority_only_in_protected_first_order
#print axioms RenderedDeliveryCounterexample.downstream_plain_child_coverage_is_arrival_order_dependent
#print axioms RenderedDeliveryCounterexample.downstream_visible_basis_is_different_after_the_same_plain_child
