import StablePackets

/- Executable cold-start certificate machine for this positive, unary,
   empty-E, full-mark example. Entry/exit are renamed into one local frame
   after every call. No production core or instruction model is changed. -/
namespace NestedColdMachine
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

structure Saved where
  edge : Edge
  backward : Bool
  deriving DecidableEq, BEq, Repr

structure State where
  domains : List (List Offered) := [[],[]]
  current : List (List Edge) := [[],[]]
  offers : List (List Offered) := [[],[],[],[]]
  deriving DecidableEq, BEq, Repr

def pairKey (a b : Nat) : Nat := (a+b)*(a+b+1)/2+b
def pathKey (a : Path) : Nat := a.foldl (fun k x => k*3+x) 1
def tailKey : Tail → Nat
  | .exact => 0 | .star => 1 | .may => 2 | .ne => 3 | .must => 4
def apKey (a : Ap) : Nat := (pathKey a.path*5+tailKey a.tail)*8+a.mark.getD 0
def valueKey (a : Offered) : Nat := apKey a.ap*2+(if a.demand then 1 else 0)
def edgeKey (e : Edge) : Nat := pairKey (apKey e.1) (apKey e.2.ap)*2+(if e.2.demand then 1 else 0)
def rowKey (r : Row) : Nat := pairKey (apKey r.entry) (apKey r.exit)
def savedKey (s : Saved) : Nat := edgeKey s.edge*2+(if s.backward then 1 else 0)
def unique (key : α → Nat) [BEq α] (xs : List α) : List α := sortBy key xs.eraseDups

def valueCovered (a b : Offered) : Bool :=
  decide (a ≠ b) && a.demand == b.demand && decide (a.ap.mark = b.ap.mark) &&
  (dropHead a.ap.path b.ap.path).isSome &&
  (a.ap.tail == .may || (a.ap.tail == .must && b.ap.tail == .must))
def values (xs : List Offered) : List Offered :=
  unique valueKey (xs.filter fun b => !(xs.any fun a => valueCovered a b))
def executable (xs : List Edge) : List Edge :=
  unique edgeKey (xs.filter fun b => !(xs.any fun a =>
    decide (a ≠ b) && decide (a.1 = b.1) && a.2.demand == b.2.demand &&
    a.2.ap.tail == .may && (dropHead a.2.ap.path b.2.ap.path).isSome))

def reverseEdge (e : Edge) : Edge :=
  if e.1.tail == .must || e.2.ap.tail == .must then
    ({e.2.ap with base := p,tail := .star},val {e.1 with base := ret,tail := .may} true)
  else ({e.2.ap with base := p},val {e.1 with base := ret} e.2.demand)
def views (backward : Bool) (all : List Saved) : List (Edge × Bool) :=
  all.map fun s => (if backward then reverseEdge s.edge else s.edge,s.backward != backward)

def applyEdge (inside : Bool) (e : Edge) (a : Offered) : Option Offered := do
  let mk (path : Path) (tail : Tail) (weak : Bool) : Offered :=
    ⟨{e.2.ap with base := p,path := path,tail := tail,mark := a.ap.mark},a.demand || e.2.demand || weak⟩
  if e.1.tail == .must then
    if a.ap.tail == .must && (dropHead a.ap.path e.1.path).isSome then
      return mk e.2.ap.path e.2.ap.tail false
    else none
  else match dropHead e.1.path a.ap.path with
  | some rest =>
    if e.1.tail == .exact && (!rest.isEmpty || a.ap.tail != .exact) then none
    else if e.2.ap.tail == .star then return mk (e.2.ap.path ++ rest) a.ap.tail false
    else return mk e.2.ap.path e.2.ap.tail false
  | none => match dropHead a.ap.path e.1.path with
    | some (_ :: _) =>
      if a.ap.tail == .exact || (a.ap.tail == .star && !inside) then none
      else if a.ap.tail == .must then
        return mk e.2.ap.path (if e.2.ap.tail == .star then .must else e.2.ap.tail) false
      else return mk e.2.ap.path (if e.2.ap.tail == .star then .may else e.2.ap.tail) true
    | _ => none

def cutOffer (limit : Nat) (a : Offered) : Offered :=
  let v := cut limit (val a.ap a.demand)
  ⟨v.ap,v.demand⟩

def baseFamily (run limit : Nat) (backward : Bool) (row : Row) (a : Offered) : List Seed :=
  let ordinary := emit run limit backward row.entry a
  if ordinary.isEmpty && a.ap.tail == .star &&
      (row.entry.tail == .may || row.entry.tail == .ne) &&
      (dropHead a.ap.path row.entry.path).isSome && a.ap.path != row.entry.path then
    emit run limit backward row.entry {a with ap := {a.ap with path := row.entry.path,tail := .may}}
  else ordinary

def fields (rows : List Row) (normals : List (Edge × Bool)) (row : Row) : List Nat :=
  let heads := (rows.filter fun r => decide (r.exit = row.exit)).map (·.entry.path) ++
    ((normals.filter fun r => !r.1.2.demand).map (·.1.1.path))
  (heads.filterMap fun h => match dropHead row.entry.path h with
    | some (f :: _) => some f | _ => none).eraseDups

def compatibleChild (a : Offered) (path : Path) : Bool :=
  ((dropHead a.ap.path path).isSome || (dropHead path a.ap.path).isSome) &&
    (a.ap.tail != .exact || a.ap.path == path)

def plan (run limit : Nat) (backward : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (row : Row) (a : Offered) : List (Seed × List Nat) :=
  let next := fields rows normals row
  let qs := baseFamily run limit backward row a
  unique (fun q => apKey q.1.ap) (qs.flatMap fun q =>
    if q.ap.tail == .star && q.ap.path == row.entry.path &&
        (row.entry.tail == .may || row.entry.tail == .ne) then
      let chosen := next.filter fun f =>
        decide (q.ap.path.length+1 ≤ min limit (row.entry.path.length+1)) &&
        compatibleChild a (q.ap.path ++ [f])
      [(q,chosen)] ++ chosen.flatMap (fun f =>
        [(⟨{q.ap with path := q.ap.path ++ [f],tail := .exact},false⟩,[]),
         (⟨{q.ap with path := q.ap.path ++ [f]},false⟩,[])])
    else [(q,[])])

abbrev Cell := Row × List (Seed × List Nat)
def cells (run limit : Nat) (backward : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (domain : List Offered) : List Cell :=
  if run == 1 then
    if domain.isEmpty then [] else [(⟨point p [] .may,point ret [] .star⟩,[(⟨point p [] .star,false⟩,[])])]
  else rows.flatMap fun row => domain.map fun a => (row,plan run limit backward rows normals row a)

def commonMask (all : List Cell) (q : Seed) : List Nat :=
  let occurrences := all.flatMap fun c => c.2.filter (fun x => decide (x.1.ap = q.ap))
  [f,g].filter fun field => !occurrences.isEmpty && occurrences.all (fun x => x.2.contains field)

def normalsCover (normals : List (Edge × Bool)) (q : Ap) (c : Value) : Bool :=
  !c.demand && normals.any (fun s => !s.1.2.demand && s.1.1.tail == .star &&
    s.1.2.ap.tail == .star &&
    match dropHead s.1.1.path q.path with
    | some rest => decide ({q with base := ret,path := s.1.2.ap.path ++ rest} = c.ap)
    | none => false)

def leafStep (limit : Nat) (mask : List Nat) (read : Bool) (a : Value) : Option Value := do
  let c ← moveE p p (if read then [f] else []) (if read then [] else [f]) a.ap
  if read && a.ap.tail == .star && a.ap.path.isEmpty &&
      mask.contains f && c.demand && c.ap.tail == .may then none
  else return cut limit {c with demand := c.demand || a.demand}
def leafBody (limit : Nat) (mask : List Nat) (q : Ap) : List Value :=
  [false,true].filterMap fun read => do
    let a ← leafStep limit mask read (val q)
    let b ← leafStep limit mask read a
    return {b with ap := {b.ap with base := ret}}

def offer (run limit : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (a : Offered) : List Offered :=
  let norms := views (run % 2 == 0) saved
  let ps := rows.map fun row => plan run limit (run % 2 == 0) rows norms row a
  let old := norms.filterMap fun e => (applyEdge e.2 e.1 a).map (cutOffer limit)
  let now := if run == 1 || ps.any (fun p => !p.isEmpty) then
      (executable current).filterMap fun e =>
        let possible := ps.any fun pl => pl.any fun q =>
          decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
        (applyEdge possible e a).map (cutOffer limit)
    else []
  values (old ++ now)

def pub (run limit : Nat) (norms : List (Edge × Bool)) (row : Row)
    (qs : List Seed) (q : Seed) (raw : Value) : Option Edge :=
  if run != 1 && normalsCover norms q.ap raw then none
  else if run == 1 then some (normalize q.ap raw)
  else restricted limit qs q raw row

def register (owner : Nat) (a : Offered) (st : State) : State :=
  {st with domains := st.domains.modify owner (fun xs => unique valueKey (a :: xs))}

def process (run limit owner : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (st : State) : State := Id.run do
  let norms := views (run % 2 == 0) (saved[owner]!)
  let work := cells run limit (run % 2 == 0) (rows[owner]!) norms (st.domains[owner]!)
  let mut state := st
  let mut generated := []
  let scheduled := sortBy (fun item =>
    if item.2.2.ap.tail == .exact then 0 else if item.2.2.ap.tail == .must then 1 else 2)
    (work.flatMap fun (row,pl) => pl.map fun (q,_) => (row,pl,q))
  for (row,pl,q) in scheduled do
    let mask := commonMask work q
    let mut outputs := []
    if owner == 1 then outputs := leafBody limit mask q.ap
    else
      let a : Offered := ⟨q.ap,q.demand⟩
      state := register 1 a state
      outputs := (offer run limit (rows[1]!) (saved[1]!) (state.current[1]!) a).map
        fun v => val {v.ap with base := ret} v.demand
    for c in outputs do
      match pub run limit norms row (pl.map (·.1)) q c with
      | some e => generated := e :: generated
      | none => pure ()
  let basis := unique edgeKey (state.current[owner]! ++ generated)
  let providers := basis ++ norms.map (·.1)
  let compacted := if run % 2 == 0 then basis else
    basis.filter fun e => !(providers.any fun n => SameLaneUniform.covers n e)
  return {state with current := state.current.set owner compacted}

def round (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in [0,1,2] do
    let mut out := state.offers[j+1]!
    for a in state.offers[j]! do
      state := register 0 a state
      out := out ++ offer run limit (rows[0]!) (saved[0]!) (state.current[0]!) a
    state := {state with offers := state.offers.set (j+1) (values out)}
  state := process run limit 0 rows saved state
  return process run limit 1 rows saved state

def initial (run limit : Nat) : State :=
  {offers := [[if run % 2 == 0 then need else cutOffer limit (NestedSavedReplayCycle.source 0)],[],[],[]]}

def rounds (fuel run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) : State :=
  fuel.rec (initial run limit) (fun _ st => round run limit rows saved st)

def outputRows (st : State) : List (List Row) := st.current.map fun es =>
  unique rowKey (es.filterMap fun e => if e.2.demand then
    some ⟨{e.2.ap with base := p},{e.1 with base := ret}⟩ else none)
def outputSaved (run : Nat) (prior : List (List Saved)) (st : State) : List (List Saved) :=
  [0,1].map fun j => unique savedKey (prior[j]! ++ (st.current[j]!).filterMap fun e =>
    if e.2.demand then none else some ⟨if run % 2 == 0 then reverseEdge e else e,run % 2 == 0⟩)

end NestedColdMachine
