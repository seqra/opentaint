import Lean

/-!
# The constructivity gate

`formal/` is constructive by contract.  Nothing enforces that on its own — a single
`by simp` reaching a classically-proved lemma pulls `Classical.choice` in silently, and
`#print axioms` only reports it if someone remembers to look.  So we make it a build
error instead.

`propext` and `Quot.sound` are permitted: they are Lean's extensionality and quotient
axioms, not choice, and rejecting them would rule out ordinary equality reasoning.
`Classical.choice` is the one that makes a proof non-constructive, and it is refused.
-/

namespace Opentaint

open Lean Elab Command

/-- Allowed axioms.  Anything outside this set fails the build. -/
private def allowedAxioms : List Name := [``propext, ``Quot.sound]

/--
`#constructive foo bar` fails elaboration unless `foo` and `bar` are provable from the
allowed axioms alone.  Put every load-bearing theorem through it.
-/
elab "#constructive " ids:ident+ : command => do
  for id in ids do
    let cst ← liftCoreM <| realizeGlobalConstNoOverload id
    let axs ← liftCoreM <| Lean.collectAxioms cst
    let bad := axs.filter fun a => !(allowedAxioms.contains a)
    unless bad.isEmpty do
      throwError
        "{cst} is not constructive: it depends on {bad.toList}.\n\
         Allowed axioms are {allowedAxioms}."

end Opentaint
