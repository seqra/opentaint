import NestedWriteReplay

/- Candidate only. EXACT is a point inside a raw query. A keep whose guard
   is strictly below that point has no contribution. No C2/C5, query, mark,
   layer, exclusion, saved service, original offer or budget is changed. -/
namespace PointWriteReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

inductive Op where
  | call (owner : Nat)
  | move (read write : Path)
  | overwrite (field : Nat)
  | nestedWrite (path : Path)
  deriving DecidableEq, BEq, Repr
abbrev Method := List (List Op)
def reversed (branch : List Op) : List Op := branch.reverse.map fun op =>
  match op with
  | .call owner => .call owner
  | .move r w => .move w r
  | .overwrite field => .overwrite field
  | .nestedWrite path => .nestedWrite path


def blocked (head : Path) (a : Value) : Bool :=
  decide (a.ap.tail = .exact ∧ a.ap.mark = none) &&
    match dropHead a.ap.path head with | some (_ :: _) => true | _ => false

def keep (run : Nat) (head : Path) (field : Nat) (a : Value) : Option Value :=
  if blocked head a then none else NestedWriteReplay.keep run head field a

/-- Parallel existing native keep micro-edges, with the point correction. -/
def nestedWrite (run limit : Nat) (path : Path) (mask : List Nat) (a : Value) : List Value :=
  path.zipIdx |>.filterMap fun (field,k) => do
    let head := path.take k
    let c ← keep run head field a
    let delegated := a.ap.tail == .star && c.demand && c.ap.tail == .may &&
      match dropHead a.ap.path head with | some (h :: _) => mask.contains h | _ => false
    if delegated then none else some (cut limit c)

def body (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (branch : List Op) (q : Seed) (mask callMask : List Nat)
    (st : State) : State × List Value := Id.run do
  let mut state := st
  let mut vals := [val q.ap]
  for op in (if run % 2 == 0 then reversed branch else branch) do
    let mut out := []
    for a in vals do
      match op with
      | .nestedWrite path =>
        out := nestedWrite run limit path mask a ++ out
      | .overwrite field =>
        match overwrite run field a with
        | none => pure ()
        | some c => out := c :: out
      | .move r w =>
        match move r w a.ap with
        | none => pure ()
        | some c =>
          let blocked := a.ap.tail == .star && c.demand && c.ap.tail == .may &&
            match dropHead a.ap.path r with | some (f :: _) => mask.contains f | _ => false
          if !blocked then out := cut limit {c with demand := c.demand || a.demand} :: out
      | .call child =>
        let actual : Offered := ⟨a.ap,a.demand⟩
        -- Exactly the old original input is registered, once.
        state := register child actual state
        let norms := OverwriteReplay.views (run % 2 == 0) (saved[child]!)
        for e in norms do
          let result := ExclusionChildReplay.route true q.ap callMask e actual
          match result with
          | none => pure ()
          | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
        -- Current-summary matching, admission and subscription are unchanged.
        let ps := (rows[child]!).map fun row => plan run limit (run % 2 == 0) (rows[child]!) norms row actual
        if run == 1 || ps.any (fun p => !p.isEmpty) then
          for e in executable (state.current[child]!) do
            let possible := ps.any fun pl => pl.any fun q =>
              decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
            match apply possible e actual with
            | none => pure ()
            | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
    vals := (OverwriteReplay.values (out.map fun a => ⟨a.ap,a.demand⟩)).map fun a => val a.ap a.demand
  return (state,vals.map fun a => {a with ap := {a.ap with base := ret}})

def process (run limit owner : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let norms := OverwriteReplay.views (run % 2 == 0) (saved[owner]!)
  let work := cells run limit (run % 2 == 0) (rows[owner]!) norms (st.domains[owner]!)
  let mut state := st
  let mut generated := []
  for (row,pl) in work do
    for (q,_) in pl do
      let mask := commonMask work q
      for branch in methods[owner]! do
        let callMask := readyMask run limit (rows[owner]!) norms q.ap mask
        let (next,outputs) := body run limit rows saved branch q mask callMask state
        state := next
        for c in outputs do
          match OverwriteReplay.pub run limit norms row (pl.map (·.1)) q c with
          | none => pure ()
          | some e => generated := e :: generated
  let basis := unique OverwriteReplay.edgeKey (state.current[owner]! ++ generated)
  let providers := basis ++ norms.map (·.1) ++ (if run % 2 == 0 then [] else
    work.flatMap fun (row,pl) => pl.flatMap fun (q,_) => providerViews limit norms row q)
  let compacted := if run % 2 == 0 then basis else
    basis.filter fun e => !(providers.any fun n => uniformCover n e)
  return {state with current := state.current.set owner compacted}

def round (run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in List.range calls do
    let mut out := state.offers[j+1]!
    for a in state.offers[j]! do
      state := register 0 a state
      -- The real outer caller uses the completely unchanged native OverwriteReplay.offer.
      out := out ++ OverwriteReplay.offer run limit (rows[0]!) (saved[0]!) (state.current[0]!) a
    state := {state with offers := state.offers.set (j+1) (OverwriteReplay.values out)}
  for owner in List.range methods.length do
    state := process run limit owner methods rows saved state
  return state

def rounds (fuel run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (OverwriteReplay.initial run limit methods.length calls source)
    (fun _ st => round run limit calls methods rows saved st)


end PointWriteReplay
