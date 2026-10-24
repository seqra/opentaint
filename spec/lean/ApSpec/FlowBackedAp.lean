/- Original AP execution: cross-premise ANY instantiation, without StrongQueries. -/
import ApSpec.Run1FlowTaintCoverage
import ApSpec.CurrentDemand

namespace ApSpec.FlowBackedAp
open ApSpec ApSpec.Abs ApSpec.Run1FlowTaintCoverage

/-- The AP reducer returns exactly the same facts, requests and layers.
    Geometry and the concrete input are arbitrary; the covering output is ANY. -/
theorem any_summary_application (a : AFact) (ib ob : Base)
    (ip op : List Acc) (t : Mark) (xs : List Mark) (layer : Bool)
    (actual : a.fact.mark = .conc t) (allowed : memB t xs = false) :
    applySummary a (initial ib ip (.conc t)) ⟨anyFinal ob op (.conc t), layer⟩ =
    applySummary a (initial ib ip .star) ⟨anyFinal ob op (.starEx xs), layer⟩ := by
  simp [applySummary, applyEdge, initial, anyFinal, actual, markGate, markComp, allowed]

/-- Reversing the abstract guide uses the existing emitter's FLOW form. -/
theorem abstract_guide_start (b : Base) (p : List Acc) (t : Mark) :
    emitW (anyFinal b p .star) ⟨b, p, .exact, .conc t⟩ =
      some (initial b p .star) := by
  simp [emitW, emitM, anyFinal, initial, flowForm, relate,
    CoreAux.dropPrefix_some.mpr (List.append_nil p).symm, markMatchB, meetK, flowK]

/-- Explicit protected guides still select the original concrete emitter. -/
theorem protected_guide_start (b : Base) (p : List Acc) (t : Mark) :
    emitW (anyFinal b p (.conc t)) ⟨b, p, .exact, .conc t⟩ =
      some ⟨b, p, .exact, .conc t⟩ := by
  simp [emitW, emitM, anyFinal, relate,
    CoreAux.dropPrefix_some.mpr (List.append_nil p).symm, markMatchB, meetK]

#print axioms any_summary_application
#print axioms abstract_guide_start
#print axioms protected_guide_start
end ApSpec.FlowBackedAp
