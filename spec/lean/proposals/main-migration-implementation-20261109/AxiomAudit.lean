import Plan
import Lean

open Lean Elab Command

run_elab do
  let env ← getEnv
  let mut base : Nat := 0
  let mut plan : Nat := 0
  let mut examples : Nat := 0
  let mut failures : List Name := []
  for (name, info) in env.constants.toList do
    let parent := name.getPrefix
    let isBase := parent == `MainMigration || parent == `MainMigration.Examples
    let isPlan := parent == `MainMigrationPlan || parent == `MainMigrationPlan.Examples
    if isBase || isPlan then
      if let .thmInfo _ := info then
        let dependencies ← collectAxioms name
        let forbidden := dependencies.filter (fun dep => dep != `propext && dep != `Quot.sound)
        if !forbidden.isEmpty then
          failures := name :: failures
          logInfo m!"FORBIDDEN_DEPENDENCIES {name}: {forbidden}"
        if isBase then base := base + 1 else plan := plan + 1
        if parent == `MainMigration.Examples || parent == `MainMigrationPlan.Examples then
          examples := examples + 1
        logInfo m!"MIGRATION_IMPL_THEOREM {name} dependencies={dependencies}"
  if base != 51 || plan != 19 || examples != 14 then
    throwError "Incorrect theorem inventory: base={base}, plan={plan}, examples={examples}"
  if !failures.isEmpty then throwError "Forbidden theorem dependencies: {failures}"
  logInfo m!"MIGRATION_IMPL_AUDIT base={base} plan={plan} examples={examples}; no forbidden dependencies"
