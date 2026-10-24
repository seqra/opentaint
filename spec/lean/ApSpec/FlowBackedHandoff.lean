/- Constructive handoff boundary, built from the original C2/C5 operations.
   This does not admit queries from actual inputs without a demand. -/
import ApSpec.FlowBackedAp
import ApSpec.FlowBackedProtection

namespace ApSpec.FlowBackedHandoff
open ApSpec ApSpec.Abs ApSpec.CurrentDemand ApSpec.FlowBackedProtection

/-- The retained FLOW guide selects the query, including its whole-premise
    gate. The marked input only supplies the ordinary overlap witness. -/
def startFromFlowGuide (d a : PFact) (l : Loc)
    (abstract : d.mark = .star) (tail : PatTailB d.kind = true)
    (demanded : d.covers l) (actual : a.covers l) : Emission d a l :=
  emitCertificate d a l (fun _ => tail)
    (fun impossible => False.elim (impossible abstract)) demanded actual

/-- Reduction is the original demand restriction, not an extra response
    permission. The returned object has the exact computed layer/subset proof. -/
def publishFromFlowGuide {d : DemandEdge} {a : PFact} {l0 l1 : Loc}
    (emission : Emission d.din a l0) (summary : AFact) (exit : PFact)
    (pair : den emission.premise summary.fact l0 l1)
    (exitPattern : d.dout = some exit) (demanded : exit.covers l1) :
    Reduction emission.premise summary d l0 l1 :=
  reduceEmission emission summary exit pair exitPattern demanded

/-- The removed same-mark obligation has an executable pure recipe. No
    generation/selected cleaner barrier is omitted from the replay. -/
def removedDependencyReplay {Op t u p} (derivation : Derivation Op t u p)
    (diagonal : u = t) (plain : p = false) : ReplayWitness derivation :=
  replayWitness derivation diagonal plain

theorem no_concrete_barrier_removed {Op t u p} (d : Derivation Op t u p)
    (diagonal : u = t) (plain : p = false) : barriers d = 0 :=
  (removedDependencyReplay d diagonal plain).noBarrier

/-- An explicit trace, not an existential oracle, replays in a second
    interpreter when each of its actual transport steps is equal. The spec
    uses this only at certified neutral adapters; all other boundaries decode. -/
def execute {Op State} (step : Op → State → State) (ops : List Op) (s : State) : State :=
  ops.foldl (fun state op => step op state) s

theorem execute_equal {Op State} (a b : Op → State → State)
    (same : ∀ op state, a op state = b op state) (ops : List Op) (s : State) :
    execute a ops s = execute b ops s := by
  simp [execute, same]

theorem removed_recipe_equal {Op State t u p} (d : Derivation Op t u p)
    (diagonal : u = t) (plain : p = false) (a b : Op → State → State)
    (same : ∀ op state, a op state = b op state) (s : State) :
    execute a (removedDependencyReplay d diagonal plain).tree.operations s =
      execute b (operations d) s := by
  rw [(removedDependencyReplay d diagonal plain).sameOperations]
  exact execute_equal a b same _ s

def controls : List Bool := [
  decide (ruleFlag false 7 7 9 = false),
  decide (ruleFlag false 7 9 7 = true),
  decide (ruleFlag false 4 7 7 = true),
  decide (callFlag false false 7 9 7 = true),
  decide (callFlag false false 7 7 7 = false),
  decide (ruleFlag false 7 7 7 = true),
  decide (callFlag false true 7 9 10 = true),
  decide (joinFlag false true = true),
  decide (joinFlag true false = true)
]

#print axioms startFromFlowGuide
#print axioms publishFromFlowGuide
#print axioms removedDependencyReplay
#print axioms no_concrete_barrier_removed
#print axioms execute_equal
#print axioms removed_recipe_equal
end ApSpec.FlowBackedHandoff
