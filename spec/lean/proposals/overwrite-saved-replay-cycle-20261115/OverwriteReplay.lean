import RoutedCalls

/- Native ordinary overwrite extension of the prepared-child reference.
   Only the return cone is represented. Fields are f/g; no rule transfer,
   abstract library model, loop, recursion, alias-derived return or cleaner.
   All real field exclusions stay on values and NORMAL records. -/
namespace OverwriteReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

def union (a b : List Nat) := sortBy id (a ++ b).eraseDups

def apKey (a : Ap) := NestedColdMachine.apKey a * 4 +
  (if a.e.contains f then 1 else 0) + (if a.e.contains g then 2 else 0)
def valueKey (a : Offered) := apKey a.ap*2+(if a.demand then 1 else 0)
def edgeKey (e : Edge) := pairKey (apKey e.1) (apKey e.2.ap)*2+(if e.2.demand then 1 else 0)
def rowKey (r : Row) := pairKey (apKey r.entry) (apKey r.exit)
def savedKey (s : Saved) := edgeKey s.edge*2+(if s.backward then 1 else 0)

def valueCovered (a b : Offered) : Bool :=
  decide (a ≠ b) && a.demand == b.demand && decide (a.ap.mark = b.ap.mark) &&
  match dropHead a.ap.path b.ap.path with
  | none => false
  | some rest => a.ap.tail == .may ||
      (a.ap.tail == .must && b.ap.tail == .must &&
        match rest with | [] => a.ap.e.all b.ap.e.contains | h :: _ => !a.ap.e.contains h)
def values (xs : List Offered) := unique valueKey (xs.filter fun b => !(xs.any fun a => valueCovered a b))

def move (r w : Path) (a : Ap) : Option Value :=
  match dropHead r a.path with
  | some rest => some (val {a with path := w ++ rest})
  | none => match dropHead a.path r with
    | some (h :: _) => if a.tail == .exact || a.e.contains h then none else
        some (val {a with path := w,tail := if a.tail == .must then .must else .may,e := []}
          (a.tail != .must))
    | _ => none

def overwrite (run field : Nat) (a : Value) : Option Value :=
  match a.ap.path with
  | h :: _ => if h == field then none else some a
  | [] => if a.ap.tail == .star || a.ap.tail == .exact || a.ap.tail == .must then
      if run == 1 then some {a with demand := true,ap := {a.ap with e := []}}
      else some {a with ap := {a.ap with e := union a.ap.e [field]}}
    else some a

def apply (inside : Bool) (e : Edge) (a : Offered) : Option Offered :=
  let mk (result : Ap) (weak : Bool := false) : Offered :=
    ⟨{result with base := p,mark := a.ap.mark},a.demand || e.2.demand || weak⟩
  if e.1.tail == .must then
    if a.ap.tail != .must then none else
      match dropHead a.ap.path e.1.path with
      | none => none
      | some rest => if (match rest with | [] => !(a.ap.e.all e.1.e.contains) | h :: _ => a.ap.e.contains h) then none
        else some (mk e.2.ap)
  else match dropHead e.1.path a.ap.path with
  | some rest =>
    if e.1.tail == .exact && (!rest.isEmpty || a.ap.tail != .exact) then none else
    let shared := union e.1.e (if e.2.ap.tail == .star then e.2.ap.e else [])
    if (match rest with | [] => false | h :: _ => shared.contains h) then none else
    if e.2.ap.tail == .star then
      some (mk {e.2.ap with path := e.2.ap.path ++ rest,tail := a.ap.tail,e := if rest.isEmpty then union a.ap.e shared else a.ap.e})
    else some (mk e.2.ap)
  | none => match dropHead a.ap.path e.1.path with
    | some (h :: _) =>
      if a.ap.tail == .exact || a.ap.e.contains h || (a.ap.tail == .star && !inside) then none
      else if a.ap.tail == .must then
        some (mk {e.2.ap with tail := if e.2.ap.tail == .star then .must else e.2.ap.tail})
      else some (mk {e.2.ap with tail := if e.2.ap.tail == .star then .may else e.2.ap.tail,e := []} true)
    | _ => none

def reverseEdge (e : Edge) : Edge :=
  if e.1.tail == .must || e.2.ap.tail == .must then
    ({e.2.ap with base := p,tail := .star},val {e.1 with base := ret,tail := .may,e := []} true)
  else
    let shared := if e.1.tail == .star && e.2.ap.tail == .star then union e.1.e e.2.ap.e else []
    ({e.2.ap with base := p,e := []},val {e.1 with base := ret,e := shared} e.2.demand)
def views (backward : Bool) (all : List Saved) : List (Edge × Bool) :=
  all.map fun s => (if backward then reverseEdge s.edge else s.edge,s.backward != backward)
def route (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) : Option Offered :=
  if PreparedChildReplay.delegated q mask e.1 e.2 a then none else apply e.2 e.1 a

def normalsCover (normals : List (Edge × Bool)) (q : Ap) (c : Value) : Bool :=
  !c.demand && normals.any (fun s => !s.1.2.demand && s.1.1.tail == .star &&
    s.1.2.ap.tail == .star &&
    decide (apply s.2 s.1 ⟨q,false⟩ = some ⟨{c.ap with base := p},false⟩))
def pub (run limit : Nat) (norms : List (Edge × Bool)) (row : Row)
    (qs : List Seed) (q : Seed) (raw : Value) : Option Edge :=
  if run != 1 && normalsCover norms q.ap raw then none
  else if run == 1 then some (normalize q.ap raw)
  else restricted limit qs q raw row

def uniformCover (normal edge : Edge) : Bool :=
  normal.1.e.isEmpty && normal.2.ap.e.isEmpty && edge.1.e.isEmpty && edge.2.ap.e.isEmpty &&
    SameLaneUniform.covers normal edge

def offer (run limit : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (a : Offered) : List Offered :=
  let norms := views (run % 2 == 0) saved
  let ps := rows.map fun row => plan run limit (run % 2 == 0) rows norms row a
  let old := norms.filterMap fun e => (apply e.2 e.1 a).map (cutOffer limit)
  let now := if run == 1 || ps.any (fun p => !p.isEmpty) then
    (executable current).filterMap fun e =>
      let possible := ps.any fun pl => pl.any fun q =>
        decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
      (apply possible e a).map (cutOffer limit)
    else []
  values (old ++ now)

inductive Op where
  | move (read write : Path)
  | call (owner : Nat)
  | overwrite (field : Nat)
  deriving DecidableEq, BEq, Repr
abbrev Method := List (List Op)
def reversed (branch : List Op) : List Op := branch.reverse.map fun op =>
  match op with | .move r w => .move w r | .call owner => .call owner | .overwrite field => .overwrite field
abbrev readyMask := PreparedChildReplay.readyMask

def body (enabled : Bool) (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (branch : List Op) (q : Seed) (mask callMask : List Nat)
    (st : State) : State × List Value := Id.run do
  let mut state := st
  let mut vals := [val q.ap]
  for op in (if run % 2 == 0 then reversed branch else branch) do
    let mut out := []
    for a in vals do
      match op with
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
        let norms := views (run % 2 == 0) (saved[child]!)
        for e in norms do
          let result := if enabled then route q.ap callMask e actual else apply e.2 e.1 actual
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
    vals := (values (out.map fun a => ⟨a.ap,a.demand⟩)).map fun a => val a.ap a.demand
  return (state,vals.map fun a => {a with ap := {a.ap with base := ret}})

def providerViews (limit : Nat) (norms : List (Edge × Bool)) (row : Row)
    (q : Seed) : List Edge :=
  if q.ap.tail != .must then [] else norms.filterMap fun (record,inside) => do
    let image ← apply inside record ⟨q.ap,false⟩
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
    basis.filter fun e => !(providers.any fun n => uniformCover n e)
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


def outputRows (st : State) : List (List Row) := st.current.map fun es =>
  unique rowKey (es.filterMap fun e => if e.2.demand then
    some ⟨{e.2.ap with base := p,e := []},{e.1 with base := ret,e := []}⟩ else none)
def outputSaved (run : Nat) (prior : List (List Saved)) (st : State) : List (List Saved) :=
  (List.range st.current.length).map fun j => unique savedKey
    (prior[j]! ++ (st.current[j]!).filterMap fun e =>
      if e.2.demand then none else some ⟨if run % 2 == 0 then reverseEdge e else e,run % 2 == 0⟩)
end OverwriteReplay
