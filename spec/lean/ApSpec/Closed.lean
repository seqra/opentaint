/-
  ApSpec.Closed — the licence to reuse the records of a closed initial fact.

  `closed_records_exact`: if the analysis raised NO request on the initial fact
  `i` and every exit edge of `i` is in the normal layer, then the exit records of `i` are
  EXACTLY the concrete flow from the location set of `i` to the method exit.
  It joins the coverage theorem (`Coverage.coverage`) and the exactness theorem
  (`Exact.closed_exact`). The "no request" condition is necessary: the coverage
  theorem gives "an edge OR a request", and a request means that some flow from
  `i` is covered only by an answered initial fact, not by the records of `i`.
-/
import ApSpec.Coverage
import ApSpec.Exact

namespace ApSpec.Closed
open ApSpec

theorem closed_records_exact {P : Program} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {i : PFact}
    (hi : D P counted L α sinks roots (.init M i))
    (hnoreq : ∀ t, ¬ D P counted L α sinks roots (.req M i t))
    (hcomp : ∀ g, D P counted L α sinks roots (.edge M i (P.exit M) g) → g.demand = false)
    {l0 : Loc} (h0 : i.covers l0) (l : Loc) :
    Flow P M l0 (P.exit M) l ↔
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l := by
  have hcov : ∀ l0 l, i.covers l0 → Flow P M l0 (P.exit M) l →
      ∃ g, D P counted L α sinks roots (.edge M i (P.exit M) g) ∧ den i g.fact l0 l := by
    intro l0 l hc hfl
    rcases Coverage.coverage P counted L α sinks roots hwf hα hfl i hi hc with hcv | hrq
    · exact hcv
    · exact absurd hrq (hnoreq _)
  exact Exact.closed_exact hcov hcomp h0 l

#print axioms closed_records_exact

end ApSpec.Closed
