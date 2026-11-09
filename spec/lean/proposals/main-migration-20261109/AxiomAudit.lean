import MainMigration
import Lean

open Lean Elab Command

run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  let mut failures : List Name := []
  for (name, info) in env.constants.toList do
    if name.getPrefix == `MainMigration || name.getPrefix == `MainMigration.Examples then
      if let .thmInfo _ := info then
        let dependencies ← collectAxioms name
        let forbidden := dependencies.filter (fun dep => dep != `propext && dep != `Quot.sound)
        if !forbidden.isEmpty then
          failures := name :: failures
          logInfo m!"FORBIDDEN_PROOF_DEPENDENCIES {name}: {forbidden}"
        count := count + 1
        logInfo m!"MAIN_MIGRATION_THEOREM {name} dependencies={dependencies}"
  if count < 40 then throwError "Incomplete model audit: only {count} theorems"
  if !failures.isEmpty then throwError "Forbidden proof dependencies in {failures}"
  logInfo m!"MAIN_MIGRATION_AUDIT theorems={count}; no custom axioms or classical choice"
