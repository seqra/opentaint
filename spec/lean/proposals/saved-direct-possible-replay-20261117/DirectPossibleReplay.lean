import ReplayCases

/- Candidate repair: only saved NORMAL neutral STAR relations receive an
   additional possible replay lane. C2/C5 and all cut operators are reused. -/
namespace DirectPossibleReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

/-- This changes permission for a possible overlap, never record direction.
    Ordinary definite/opposite replay remains first and unchanged. -/
def possible (e : Edge) (opposite : Bool) (a : Offered) : Bool :=
  !opposite && !e.2.demand && e.1.mark.isNone && e.2.ap.mark.isNone &&
  e.1.tail == .star && e.2.ap.tail == .star && a.ap.tail == .star &&
  match dropHead a.ap.path e.1.path with
  | some (_ :: _) => true
  | _ => false

def permission (e : Edge × Bool) (a : Offered) : Bool := e.2 || possible e.1 e.2 a

/-- Only a blocked direct NORMAL FLOW read can add a possible reply.
    A failed field-hole guard adds nothing. Uncertainty clears E, as in
    the existing possible-inside transfer, and is always DEMAND. -/
def extra (e : Edge × Bool) (a : Offered) : Option Offered :=
  if possible e.1 e.2 a then
    match dropHead a.ap.path e.1.1.path with
    | some (first :: _) => if a.ap.e.contains first then none else
        some ⟨{e.1.2.ap with base:=p,mark:=a.ap.mark,tail:=.may,e:=[]},true⟩
    | _ => none
  else none

def savedApply (e : Edge × Bool) (a : Offered) : Option Offered :=
  match OverwriteReplay.apply e.2 e.1 a with
  | some result => some result
  | none => extra e a

def savedRoute (q : Ap) (mask : List Nat) (e : Edge × Bool) (a : Offered) : Option Offered :=
  match ExclusionChildReplay.route true q mask e a with
  | some result => some result
  | none =>
    -- The ready-child predicate is geometric. Keep the record direction.
    -- Reuse this proof only for the additional possible reply.
    if ExclusionChildReplay.eligible q mask e.1 (permission e a) a then none
    else extra e a

-- Latest C2, including R32. This family uses FLOW demand only, so F72
-- is already satisfied. Concrete actual marks remain on caller bindings.
def baseFamily (run k : Nat) (back : Bool) (row : Row) (a : Offered) : List Seed :=
  let ordinary:=Run2Relay.emit run k back row.entry a
  if ordinary.isEmpty && a.ap.tail==.star &&
      (row.entry.tail==.may || row.entry.tail==.ne) &&
      (dropHead a.ap.path row.entry.path).isSome && a.ap.path≠row.entry.path then
    Run2Relay.emit run k back row.entry {a with ap:={a.ap with path:=row.entry.path,tail:=.may}}
  else ordinary

def plan (run k : Nat) (back : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (row : Row) (a : Offered) : List (Seed × List Nat) :=
  let next:=NestedColdMachine.fields rows normals row
  let qs:=baseFamily run k back row a
  unique (fun q => NestedColdMachine.apKey q.1.ap) (qs.flatMap fun q =>
    if q.ap.tail==.star && q.ap.path==row.entry.path &&
        (row.entry.tail==.may || row.entry.tail==.ne) then
      let chosen:=next.filter fun f =>
        decide (q.ap.path.length+1≤min k (row.entry.path.length+1)) &&
        NestedColdMachine.compatibleChild a (q.ap.path++[f])
      [(q,chosen)] ++ chosen.flatMap (fun f =>
        [(⟨{q.ap with path:=q.ap.path++[f],tail:=.exact},false⟩,[]),
         (⟨{q.ap with path:=q.ap.path++[f]},false⟩,[])])
    else [(q,[])])

def cells (run k : Nat) (back : Bool) (rows : List Row)
    (normals : List (Edge × Bool)) (domain : List Offered) : List Cell :=
  if run==1 then
    if domain.isEmpty then [] else [(⟨point p [] .may,point ret [] .star⟩,[(⟨point p [] .star,false⟩,[])])]
  else rows.flatMap fun row => domain.map fun a => (row,plan run k back rows normals row a)

def offer (run k : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (a : Offered) : List Offered :=
  let norms:=OverwriteReplay.views (run%2==0) saved
  let ps:=rows.map fun row => plan run k (run%2==0) rows norms row a
  let old:=norms.filterMap fun e => (savedApply e a).map (cutOffer k)
  let now:=if run==1 || ps.any (fun p => !p.isEmpty) then
    (executable current).filterMap fun e =>
      let possible:=ps.any fun pl => pl.any fun q => decide (q.1.ap=e.1) || decide (normalAp q.1.ap=e.1)
      (OverwriteReplay.apply possible e a).map (cutOffer k)
    else []
  OverwriteReplay.values (old++now)

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
          let result := savedRoute q.ap callMask e actual
          match result with
          | none => pure ()
          | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
        -- Reuse the current prepared initial family for current-summary service.
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
      -- Saved-first outer delivery uses this same current C2 plan.
      out := out ++ DirectPossibleReplay.offer run limit (rows[0]!) (saved[0]!) (state.current[0]!) a
    state := {state with offers := state.offers.set (j+1) (OverwriteReplay.values out)}
  for owner in List.range methods.length do
    state := process run limit owner methods rows saved state
  return state

def rounds (fuel run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (OverwriteReplay.initial run limit methods.length calls source)
    (fun _ st => round run limit calls methods rows saved st)


end DirectPossibleReplay
