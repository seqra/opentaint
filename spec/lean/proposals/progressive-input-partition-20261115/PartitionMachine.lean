import PartitionCover

namespace ProgressiveMachine
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 40000000

inductive Op where
  | move (read write : Path)
  | call (owner : Nat)
  deriving DecidableEq, BEq, Repr
abbrev Method := List (List Op)
abbrev Trees := List (List Path)
structure State where
  cold : NestedColdMachine.State
  pending : List (Option Path)
  deriving DecidableEq, BEq, Repr
structure Cell where
  original : Row
  localRow : Row
  q : Seed
  mask : List Nat
  deriving DecidableEq, BEq, Repr

def children (tree : List Path) (limit : Nat) (head : Path) : List Nat :=
  unique id (tree.filterMap fun h =>
    if h.length ≤ limit then match dropHead head h with
      | some [f] => some f
      | _ => none
    else none)

def cells (run limit : Nat) (backward : Bool) (tree : List Path)
    (row : Row) (a : Offered) : List Cell := Id.run do
  let ordinary := baseFamily run limit backward row a
  if !(row.entry.tail == .may || row.entry.tail == .ne) ||
      ordinary.any (fun q => q.ap.tail == .must) then
    return ordinary.map fun q => ⟨row,row,q,[]⟩
  let heads := unique pathKey (row.entry.path :: (tree.filter fun h =>
    (dropHead row.entry.path h).isSome && decide (h.length ≤ limit)))
  let mut out := []
  for h in heads do
    let localRow : Row := ⟨{row.entry with path := h,tail := if h == row.entry.path then row.entry.tail else .may},row.exit⟩
    let cs := children tree limit h
    for q in baseFamily run limit backward localRow a do
      let delegated := match dropHead h a.ap.path with
        | some (f :: _) => cs.contains f && q.ap.path != h
        | _ => false
      if !delegated then
        out := ⟨row,localRow,q,
          if q.ap.tail == .star then children tree limit q.ap.path else []⟩ :: out
  return out

def plans (run limit owner : Nat) (trees : Trees) (rows : List (List Row))
    (a : Offered) : List Cell :=
  (rows[owner]!).flatMap fun row => cells run limit (run % 2 == 0) (trees[owner]!) row a

def offer (run limit owner : Nat) (trees : Trees) (rows : List (List Row))
    (saved : List (List Saved)) (current : List (List Edge)) (a : Offered) : List Offered :=
  let ps := plans run limit owner trees rows a
  let old := (views (run % 2 == 0) (saved[owner]!)).filterMap fun e =>
    (applyEdge e.2 e.1 a).map (cutOffer limit)
  let now := if run == 1 || !ps.isEmpty then
    (executable (current[owner]!)).filterMap fun e =>
      let possible := ps.any fun q => decide (q.q.ap = e.1) || decide (normalAp q.q.ap = e.1)
      (applyEdge possible e a).map (cutOffer limit)
    else []
  values (old ++ now)

def priority (path : Path) : Nat := path.foldl (fun k x => k*3+(if x == f then 2 else 1)) 1

def firstMissing (tree : List Path) : Path → Option Path
  | [] => none
  | h :: rest => Id.run do
    let mut head := []
    for x in h :: rest do
      head := head ++ [x]
      if !(tree.contains head) then return some head
    return none

def hint (owner : Nat) (trees : Trees) (path : Path) (state : State) : State :=
  match firstMissing (trees[owner]!) path with
  | none => state
  | some next =>
    let old := state.pending[owner]!
    let better := match old with | none => true | some p => priority next < priority p
    if better then {state with pending := state.pending.set owner (some next)} else state

def register (owner : Nat) (a : Offered) (st : State) : State :=
  {st with cold := NestedColdMachine.register owner a st.cold}

def reversed (branch : List Op) : List Op := branch.reverse.map fun op =>
  match op with | .move r w => .move w r | .call owner => .call owner

def body (run limit owner : Nat) (trees : Trees) (rows : List (List Row))
    (saved : List (List Saved)) (branch : List Op) (q : Seed) (mask : List Nat)
    (st : State) : State × List Value := Id.run do
  let mut state := st
  let mut vals := [val q.ap]
  for op in (if run % 2 == 0 then reversed branch else branch) do
    let mut out := []
    for a in vals do
      match op with
      | .move r w =>
        match moveE p p r w a.ap with
        | none => pure ()
        | some c =>
          let loss := q.ap.tail == .star && a.ap.tail == .star && c.demand && c.ap.tail == .may
          let mut blocked := false
          if loss then
            match dropHead a.ap.path r with
            | some (f :: _) =>
              state := hint owner trees (q.ap.path ++ [f]) state
              blocked := mask.contains f
            | _ => pure ()
          if !blocked then out := cut limit {c with demand := c.demand || a.demand} :: out
      | .call child =>
        let actual : Offered := ⟨a.ap,a.demand⟩
        state := register child actual state
        let replies := offer run limit child trees rows saved state.cold.current actual
        if q.ap.tail == .star && a.ap.tail == .star then
          let mut kept := []
          for (e,opposite) in views (run % 2 == 0) (saved[child]!) do
            match applyEdge opposite e actual with
            | none => pure ()
            | some reply =>
              let mut blocked := false
              if e.1.tail == .star && e.2.ap.tail == .star && !e.2.demand && opposite then
                match dropHead a.ap.path e.1.path with
                | some (f :: _) =>
                  state := hint owner trees (q.ap.path ++ [f]) state
                  blocked := mask.contains f
                | _ => pure ()
              if !blocked then kept := cutOffer limit reply :: kept
          let ps := plans run limit child trees rows actual
          if run == 1 || !ps.isEmpty then
            for e in executable (state.cold.current[child]!) do
              let possible := ps.any fun q => decide (q.q.ap = e.1) || decide (normalAp q.q.ap = e.1)
              match applyEdge possible e actual with
              | none => pure ()
              | some reply => kept := cutOffer limit reply :: kept
          out := out ++ kept.map (fun a => val a.ap a.demand)
        else out := out ++ replies.map (fun a => val a.ap a.demand)
    vals := (values (out.map fun a => ⟨a.ap,a.demand⟩)).map fun a => val a.ap a.demand
  return (state,vals.map fun a => {a with ap := {a.ap with base := ret}})

def providerViews (limit : Nat) (norms : List (Edge × Bool)) (cell : Cell) : List Edge :=
  if cell.q.ap.tail != .must then [] else norms.filterMap fun (record,inside) => do
    let image ← applyEdge inside record ⟨cell.q.ap,false⟩
    if image.demand || image.ap.path.length > limit then none else
    let pub ← restricted limit [cell.q] cell.q (val {image.ap with base := ret}) cell.original
    if pub.2.demand || pub.2.ap.tail != .must then none else some pub

def process (run limit owner : Nat) (methods : List Method) (trees : Trees)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let work := if run == 1 then
      if (st.cold.domains[owner]!).isEmpty then [] else
        let row : Row := ⟨point p [] .may,point ret [] .star⟩
        [Cell.mk row row ⟨point p [] .star,false⟩ []]
    else (st.cold.domains[owner]!).flatMap (plans run limit owner trees rows)
  let mut state := st
  let mut generated := []
  let norms := views (run % 2 == 0) (saved[owner]!)
  for cell in work do
    let q := cell.q
    let occurrences := work.filter fun c => decide (c.q.ap = q.ap)
    let mask := [f,g].filter fun f => !occurrences.isEmpty && occurrences.all (fun c => c.mask.contains f)
    for branch in methods[owner]! do
      let (next,outputs) := body run limit owner trees rows saved branch q mask state
      state := next
      for c in outputs do
        let pub := if run != 1 && normalsCover norms q.ap c then none
          else if run == 1 then some (normalize q.ap c)
          else restricted limit [q] q c cell.original
        match pub with
        | none => pure ()
        | some e => generated := e :: generated
  let basis := unique edgeKey (state.cold.current[owner]! ++ generated)
  let providers := basis ++ norms.map (·.1) ++ (if run % 2 == 0 then [] else work.flatMap (providerViews limit norms))
  let compacted := if run % 2 == 0 then basis else
    basis.filter fun e => !(providers.any fun n => SameLaneUniform.covers n e)
  return {state with cold := {state.cold with current := state.cold.current.set owner compacted}}

def initial (run limit count calls : Nat) (source : Offered) : State :=
  {cold := {domains := List.replicate count [],current := List.replicate count [],offers := [if run % 2 == 0 then need else cutOffer limit source] :: List.replicate calls []},
   pending := List.replicate count none}

def round (run limit calls : Nat) (methods : List Method) (trees : Trees)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in List.range calls do
    let mut out := state.cold.offers[j+1]!
    for a in state.cold.offers[j]! do
      state := register 0 a state
      out := out ++ offer run limit 0 trees rows saved state.cold.current a
    state := {state with cold := {state.cold with offers := state.cold.offers.set (j+1) (values out)}}
  for owner in List.range methods.length do
    state := process run limit owner methods trees rows saved state
  return state

def rounds (fuel run limit calls : Nat) (methods : List Method) (trees : Trees)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (initial run limit methods.length calls source)
    (fun _ st => round run limit calls methods trees rows saved st)

def install (trees : Trees) (st : State) : Trees :=
  trees.zipWith ProgressiveInputPartition.install st.pending

def outputSaved (run : Nat) (prior : List (List Saved)) (st : State) : List (List Saved) :=
  (List.range st.cold.current.length).map fun j => unique savedKey
    (prior[j]! ++ (st.cold.current[j]!).filterMap fun e =>
      if e.2.demand then none else some ⟨if run % 2 == 0 then reverseEdge e else e,run % 2 == 0⟩)

end ProgressiveMachine
