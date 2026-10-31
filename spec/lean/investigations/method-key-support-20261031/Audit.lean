import MethodSupport
import Lean

open Lean Elab Command

/- Audit every imported kernel declaration, including generated helpers. -/
run_elab do
  let env ← getEnv
  let mut audited : Nat := 0
  let mut theorems : Nat := 0
  let mut failed : Nat := 0
  let mut allAxioms : List Name := []
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]! == `MethodSupport
      | none => false
    if owned then
      audited := audited + 1
      match info with
      | .thmInfo _ => theorems := theorems + 1
      | _ => pure ()
      let deps ← collectAxioms name
      for dep in deps do
        if dep ∉ allAxioms then allAxioms := dep :: allAxioms
      let unexpected := deps.filter (fun dep => dep != `propext && dep != `Quot.sound)
      if !unexpected.isEmpty then
        failed := failed + 1
        logInfo m!"Unexpected axioms: {name}: {unexpected}"
  logInfo m!"Audited {audited} MethodSupport declarations, including {theorems} theorem declarations; {failed} have unexpected axioms."
  logInfo m!"Transitive axiom union: {allAxioms}"
  if failed > 0 then throwError "Constructive axiom audit failed."

#print axioms MethodSupport.analysed_subset_incoming
#print axioms MethodSupport.forward_outgoing_subset_incoming
#print axioms MethodSupport.new_backward_publication_is_zero
#print axioms MethodSupport.new_backward_outgoing_has_zero_witness
#print axioms MethodSupport.new_backward_outgoing_is_zero_only
#print axioms MethodSupport.dedup_support_iff
#print axioms MethodSupport.stored_support_arbitrarily_grows
#print axioms MethodSupport.support_contraction_counterexample

#eval do
  if !MethodSupport.Controls.checks then
    throw (IO.userError "Finite controls failed")
  IO.println "Six exact controls passed: 2/10 support; seed removal; implicit ZERO suppression; NORMAL requirement retained."
  for n in [2, 10, 1000] do
    let seeded := MethodSupport.storedChainRows true n
    let unseeded := MethodSupport.storedChainRows false n
    if seeded.length != n || !unseeded.isEmpty then
      throw (IO.userError s!"Chain control failed at {n}")
    if (seeded.map MethodSupport.Row.owner) != List.range n then
      throw (IO.userError s!"Distinct method support failed at {n}")
    IO.println s!"Chain {n}: incoming support 1; nonzero initial support 0; seeded outgoing support {seeded.length}; unseeded outgoing support {unseeded.length}."
