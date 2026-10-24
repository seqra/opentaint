import ApSpec.FlowBackedProtection
import ApSpec.FlowBackedAp
import ApSpec.FlowBackedStore
import ApSpec.FlowBackedPriority
import ApSpec.FlowBackedHandoff
import ApSpec.FlowBackedRelationsCounterexamples
import Lean

open Lean Elab Command

run_elab do
  let owners := #[`ApSpec.FlowBackedProtection, `ApSpec.FlowBackedAp,
    `ApSpec.FlowBackedStore, `ApSpec.FlowBackedPriority,
    `ApSpec.FlowBackedHandoff, `ApSpec.FlowBackedRelationsCounterexamples]
  let env ← getEnv
  let mut total : Nat := 0
  for owner in owners do
    let mut count : Nat := 0
    for (name, _) in env.constants.toList do
      let module := match env.getModuleIdxFor? name with
        | some index => env.header.moduleNames[index.toNat]!
        | none => Name.anonymous
      if module == owner then
        count := count + 1
        let dependencies ← collectAxioms name
        let forbidden := dependencies.filter (fun ax => ax != `propext && ax != `Quot.sound)
        if !forbidden.isEmpty then throwError "Unexpected axioms: {name}: {forbidden}"
    if count == 0 then throwError "No declarations audited for {owner}"
    total := total + count
    logInfo m!"Audited {owner}: {count} declarations."
  logInfo m!"Total FLOW-backed declarations: {total}; no unexpected axioms."

#eval do
  let controls := ApSpec.FlowBackedPriority.controls ++
    ApSpec.FlowBackedHandoff.controls ++ ApSpec.FlowBackedRelationsCounterexamples.controls
  if !(controls.all id) then throw (IO.userError "FLOW-backed control failed")
  IO.println s!"Executable FLOW-backed controls: {controls.length} passed."
