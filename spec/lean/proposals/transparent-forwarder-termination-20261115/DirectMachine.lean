import OwnerProjection

/- Same cold AP machine, with the caller's original offer delivered directly
   to choose's existing owner. No raw initial is created for the relay. -/
namespace DirectOwnerMachine
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NormalUniformNE NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

def round (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in [0,1,2] do
    let mut out := state.offers[j+1]!
    for a in state.offers[j]! do
      state := register 1 a state
      out := out ++ offer run limit (rows[1]!) (saved[1]!) (state.current[1]!) a
    state := {state with offers := state.offers.set (j+1) (values out)}
  return process run limit 1 rows saved state

def rounds (fuel run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) : State :=
  fuel.rec (initial run limit) (fun _ st => round run limit rows saved st)

end DirectOwnerMachine
