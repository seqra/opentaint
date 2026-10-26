import ApSpec.CorrelatedConcreteImplementation
import Lean

open Lean Elab Command

run_elab do
  let owners := #[`ApSpec.Run1CorrelatedConcreteInitials, `ApSpec.CorrelatedConcreteImplementation]
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
    logInfo m!"Audited {owner}: {count} declarations."
    total := total + count
  logInfo m!"Total correlated-concrete declarations: {total}; no unexpected axioms."

#eval do
  let controls := ApSpec.Run1CorrelatedConcreteInitials.controls ++
    ApSpec.CorrelatedConcreteImplementation.controls
  if !(controls.all id) then throw (IO.userError "Correlated concrete implementation control failed")
  IO.println s!"Executable correlated concrete implementation controls: {controls.length} passed."
