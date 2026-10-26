import ApSpec.Run1CorrelatedConcreteInitials
import Lean

open Lean Elab Command

run_elab do
  let owner := `ApSpec.Run1CorrelatedConcreteInitials
  let env ← getEnv
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
  logInfo m!"Audited {owner}: {count} declarations; no unexpected axioms."

#eval do
  let controls := ApSpec.Run1CorrelatedConcreteInitials.controls
  if !(controls.all id) then throw (IO.userError "Correlated concrete initial control failed")
  IO.println s!"Executable correlated concrete initial controls: {controls.length} passed."
