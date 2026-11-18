import Lean.Elab.Tactic.Decide

/- This is the ordinary `of_decide_eq_true rfl` certificate, closed over
   local parameters and checked directly by Lean's kernel. It changes no
   logical axiom and uses no native evaluator or external proof oracle. -/
open Lean Meta Elab Tactic
elab "kernel_decide_open" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    if type.hasMVar then throwError "Unresolved metavariables"
    let vars := (← getLCtx).getFVarIds.map mkFVar
    let decision ← mkDecide type
    let refl ← mkEqRefl (mkConst ``Bool.true)
    let proof := mkApp3 (mkConst ``of_decide_eq_true) type decision.appArg!
      refl
    let closedType ← mkForallFVars vars type
    let closedProof ← mkLambdaFVars vars proof
    if closedType.hasFVar || closedProof.hasFVar then throwError "Unclosed certificate"
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma [] closedType closedProof
    goal.assign (mkAppN (mkConst name) vars)
    replaceMainGoal []
