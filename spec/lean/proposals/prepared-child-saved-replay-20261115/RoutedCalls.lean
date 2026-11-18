import ColdMachine
import Acceptance

/- Existing C2/C5 and entry queries. Only a saved NORMAL contribution inside
   an owned query can be omitted by the already prepared common child cover. -/
namespace PreparedChildReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 16384
set_option maxHeartbeats 60000000

inductive Op where
  | move (read write : Path)
  | call (owner : Nat)
  deriving DecidableEq, BEq, Repr
abbrev Method := List (List Op)

def delegated (q : Ap) (mask : List Nat) (e : Edge) (opposite : Bool) (a : Offered) : Bool :=
  q.tail == .star && a.ap.tail == .star && !a.demand && opposite &&
  q.mark.isNone && a.ap.mark.isNone && e.1.mark.isNone && e.2.ap.mark.isNone &&
  q.e.isEmpty && q.mx.isEmpty && a.ap.e.isEmpty && a.ap.mx.isEmpty &&
  e.1.e.isEmpty && e.1.mx.isEmpty && e.2.ap.e.isEmpty && e.2.ap.mx.isEmpty && !e.2.h &&
  e.1.tail == .star && e.2.ap.tail == .star && !e.2.demand &&
  match dropHead a.ap.path e.1.path with
  | some (f :: _) => mask.contains f
  | _ => false

def route (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) : Option Offered :=
  if delegated q mask e.1 e.2 a then none else applyEdge e.2 e.1 a

theorem every_kept_result_is_the_unmodified_native_result
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a result : Offered)
    (kept : route q mask e a = some result) : applyEdge e.2 e.1 a = some result := by
  unfold route at kept
  split at kept
  · contradiction
  · exact kept

theorem no_extra_saved_contributions_for_any_fixed_offer
    (q : Ap) (mask : List Nat) (es : List (Edge × Bool)) (a : Offered) :
    ((es.filterMap fun e => route q mask e a).length) ≤
      ((es.filterMap fun e => applyEdge e.2 e.1 a).length) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases flag : delegated q mask e.1 e.2 a <;>
      cases native : applyEdge e.2 e.1 a <;>
      simp_all [route] <;> omega

theorem no_child_mask_means_exactly_old_replay
    (q : Ap) (e : Edge × Bool) (a : Offered) :
    route q [] e a = applyEdge e.2 e.1 a := by
  simp [route,delegated]
  split <;> simp

theorem demand_support_is_not_pruned
    (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) :
    route q mask e {a with demand := true} = applyEdge e.2 e.1 {a with demand := true} := by
  simp [route,delegated]

def reversed (branch : List Op) : List Op := branch.reverse.map fun op =>
  match op with | .move r w => .move w r | .call owner => .call owner

/-- Computed from the immutable previous frontier and saved records, not
    from the arrival order of submitted offers. -/
def readyMask (run limit : Nat) (rows : List Row) (norms : List (Edge × Bool))
    (q : Ap) (legacy : List Nat) : List Nat :=
  if limit < q.path.length+1 then [] else
    let potential := rows.filter fun row =>
      (((row.entry.tail == .may || row.entry.tail == .ne) &&
        match dropHead row.entry.path q.path with | some rest => decide (rest.length ≤ 1) | none => false) ||
       (run == 2 && row.entry.tail == .star && decide (row.entry.path = q.path)))
    if potential.isEmpty then [] else legacy.filter fun f => potential.all fun row =>
      decide (row.entry.path = q.path) && (row.entry.tail == .may || row.entry.tail == .ne) &&
      decide (q.path.length+1 ≤ limit) && (fields rows norms row).contains f

def body (enabled : Bool) (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (branch : List Op) (q : Seed) (mask callMask : List Nat)
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
          let blocked := a.ap.tail == .star && c.demand && c.ap.tail == .may &&
            match dropHead a.ap.path r with | some (f :: _) => mask.contains f | _ => false
          if !blocked then out := cut limit {c with demand := c.demand || a.demand} :: out
      | .call child =>
        let actual : Offered := ⟨a.ap,a.demand⟩
        -- Exactly the old original input is registered, once.
        state := register child actual state
        let norms := views (run % 2 == 0) (saved[child]!)
        for e in norms do
          let result := if enabled then route q.ap callMask e actual else applyEdge e.2 e.1 actual
          match result with
          | none => pure ()
          | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
        -- Current-summary matching, admission and subscription are unchanged.
        let ps := (rows[child]!).map fun row => plan run limit (run % 2 == 0) (rows[child]!) norms row actual
        if run == 1 || ps.any (fun p => !p.isEmpty) then
          for e in executable (state.current[child]!) do
            let possible := ps.any fun pl => pl.any fun q =>
              decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
            match applyEdge possible e actual with
            | none => pure ()
            | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
    vals := (values (out.map fun a => ⟨a.ap,a.demand⟩)).map fun a => val a.ap a.demand
  return (state,vals.map fun a => {a with ap := {a.ap with base := ret}})

def providerViews (limit : Nat) (norms : List (Edge × Bool)) (row : Row)
    (q : Seed) : List Edge :=
  if q.ap.tail != .must then [] else norms.filterMap fun (record,inside) => do
    let image ← applyEdge inside record ⟨q.ap,false⟩
    if image.demand || image.ap.path.length > limit then none else
    let pub ← restricted limit [q] q (val {image.ap with base := ret}) row
    if pub.2.demand || pub.2.ap.tail != .must then none else some pub

def process (enabled : Bool) (run limit owner : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let norms := views (run % 2 == 0) (saved[owner]!)
  let work := cells run limit (run % 2 == 0) (rows[owner]!) norms (st.domains[owner]!)
  let mut state := st
  let mut generated := []
  for (row,pl) in work do
    for (q,_) in pl do
      let mask := commonMask work q
      for branch in methods[owner]! do
        let callMask := readyMask run limit (rows[owner]!) norms q.ap mask
        let (next,outputs) := body enabled run limit rows saved branch q mask callMask state
        state := next
        for c in outputs do
          match pub run limit norms row (pl.map (·.1)) q c with
          | none => pure ()
          | some e => generated := e :: generated
  let basis := unique edgeKey (state.current[owner]! ++ generated)
  let providers := basis ++ norms.map (·.1) ++ (if run % 2 == 0 then [] else
    work.flatMap fun (row,pl) => pl.flatMap fun (q,_) => providerViews limit norms row q)
  let compacted := if run % 2 == 0 then basis else
    basis.filter fun e => !(providers.any fun n => SameLaneUniform.covers n e)
  return {state with current := state.current.set owner compacted}

def initial (run limit count calls : Nat) (source : Offered) : State :=
  {domains := List.replicate count [],current := List.replicate count [],offers :=
    [if run % 2 == 0 then need else cutOffer limit source] :: List.replicate calls []}

def round (enabled : Bool) (run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in List.range calls do
    let mut out := state.offers[j+1]!
    for a in state.offers[j]! do
      state := register 0 a state
      -- The real outer caller uses the completely unchanged native offer.
      out := out ++ offer run limit (rows[0]!) (saved[0]!) (state.current[0]!) a
    state := {state with offers := state.offers.set (j+1) (values out)}
  for owner in List.range methods.length do
    state := process enabled run limit owner methods rows saved state
  return state

def rounds (enabled : Bool) (fuel run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (initial run limit methods.length calls source)
    (fun _ st => round enabled run limit calls methods rows saved st)

def outputSaved (run : Nat) (prior : List (List Saved)) (st : State) : List (List Saved) :=
  (List.range st.current.length).map fun j => unique savedKey
    (prior[j]! ++ (st.current[j]!).filterMap fun e =>
      if e.2.demand then none else some ⟨if run % 2 == 0 then reverseEdge e else e,run % 2 == 0⟩)

end PreparedChildReplay

#print axioms PreparedChildReplay.every_kept_result_is_the_unmodified_native_result
#print axioms PreparedChildReplay.no_extra_saved_contributions_for_any_fixed_offer
#print axioms PreparedChildReplay.no_child_mask_means_exactly_old_replay
#print axioms PreparedChildReplay.demand_support_is_not_pruned
