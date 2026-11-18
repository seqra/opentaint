import ExclusionCover

/- Ordinary parallel strongKeep for a nested replacement. The new operator
   spells out existing native field-write micro-edges; no proposed semantics
   are added. All original C2/C5, child masks, E, saved replay and H stay. -/
namespace NestedWriteReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

inductive Op where
  | move (read write : Path)
  | overwrite (field : Nat)
  | nestedWrite (path : Path)
  deriving DecidableEq, BEq, Repr
abbrev Method := List (List Op)
def reversed (branch : List Op) : List Op := branch.reverse.map fun op =>
  match op with
  | .move r w => .move w r
  | .overwrite field => .overwrite field
  | .nestedWrite path => .nestedWrite path

/-- One excluded-identity keep. The EXACT/FLOW inside case is intentional:
    native Reference.above and EdgeApplication.flow both implement it. -/
def keep (run : Nat) (headPath : Path) (field : Nat) (a : Value) : Option Value :=
  match dropHead headPath a.ap.path with
  | some (h :: _) => if h == field then none else some a
  | some [] =>
    if a.ap.tail == .may || a.ap.tail == .ne then
      some {a with ap := {a.ap with e := []}}
    else if run == 1 then some {a with demand := true,ap := {a.ap with e := []}}
    else some {a with ap := {a.ap with e := union a.ap.e [field]}}
  | none => match dropHead a.ap.path headPath with
    | some (h :: _) => if a.ap.e.contains h || (a.ap.tail == .exact && a.ap.mark.isSome) then none else
      if a.ap.tail == .must then
        some {a with ap := {a.ap with path := headPath,e := [field]},demand := a.demand || run == 1}
      else some {a with ap := {a.ap with path := headPath,tail := .may,e := []},demand := true}
    | _ => none

/-- All keep micro-edges consume the same offered value, in parallel. -/
def nestedWrite (run limit : Nat) (path : Path) (mask : List Nat) (a : Value) : List Value :=
  path.zipIdx |>.filterMap fun (field,k) => do
    let headPath := path.take k
    let c ← keep run headPath field a
    let blocked := a.ap.tail == .star && c.demand && c.ap.tail == .may &&
      match dropHead a.ap.path headPath with | some (h :: _) => mask.contains h | _ => false
    if blocked then none else some (cut limit c)

def step (run limit : Nat) (mask : List Nat) (op : Op) (a : Value) : List Value :=
  match op with
  | .nestedWrite path => nestedWrite run limit path mask a
  | .overwrite field => (overwrite run field a).toList
  | .move r w => match move r w a.ap with
    | none => []
    | some c =>
      let blocked := a.ap.tail == .star && c.demand && c.ap.tail == .may &&
        match dropHead a.ap.path r with | some (h :: _) => mask.contains h | _ => false
      if blocked then [] else [cut limit {c with demand := c.demand || a.demand}]

def through (run limit : Nat) (mask : List Nat) : List Op → List Value → List Value
  | [],xs => xs
  | op :: rest,xs =>
    let out := xs.flatMap (fun a => step run limit mask op a)
    let canonical := (OverwriteReplay.values (out.map fun a => ⟨a.ap,a.demand⟩)).map
      fun a => val a.ap a.demand
    through run limit mask rest canonical

/-- There is no nested call in this witness. The ordinary outer caller still
    uses unchanged saved-first offer. This body is precisely the parallel
    keep/move instruction pipeline, with per-statement canonicalization. -/
def body (run limit : Nat) (_rows : List (List Row))
    (_saved : List (List Saved)) (branch : List Op) (q : Seed) (mask _callMask : List Nat)
    (st : State) : State × List Value :=
  (st,(through run limit mask (if run % 2 == 0 then reversed branch else branch)
    [val q.ap]).map fun a => {a with ap := {a.ap with base := ret}})

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


end NestedWriteReplay
