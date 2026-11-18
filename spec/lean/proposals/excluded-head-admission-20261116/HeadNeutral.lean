import HeadNeutralPlan
namespace HeadNeutral
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay PointWriteReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def offer (run limit : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (a : Offered) : List Offered :=
  let norms := OverwriteReplay.views (run % 2 == 0) saved
  let ps := rows.map fun row => HeadNeutralPlan.plan run limit (run % 2 == 0) rows norms row a
  let old := norms.filterMap fun e => (OverwriteReplay.apply e.2 e.1 a).map (cutOffer limit)
  let now := if run == 1 || ps.any (fun p => !p.isEmpty) then
    (executable current).filterMap fun e =>
      let possible := ps.any fun pl => pl.any fun q =>
        decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
      (OverwriteReplay.apply possible e a).map (cutOffer limit)
    else []
  OverwriteReplay.values (old ++ now)

def normalizeOffers (back : Bool) (xs : List Offered) : List Offered :=
  (UniformActual.foldValues back [] (xs.map fun a => (⟨a.ap,a.demand,false⟩ : Value))).map
    (fun v => (⟨v.ap,v.demand⟩ : Offered))

def body (run limit : Nat) (rows : List (List Row))
    (saved : List (List Saved)) (branch : List PointWriteReplay.Op) (q : Seed) (mask callMask : List Nat)
    (st : State) : State × List Value := Id.run do
  let mut state := st
  let mut vals := [val q.ap]
  for op in (if run % 2 == 0 then PointWriteReplay.reversed branch else branch) do
    let mut out := []
    for a in vals do
      match op with
      | .nestedWrite path =>
        out := PointWriteReplay.nestedWrite run limit path mask a ++ out
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
        let ps := (rows[child]!).map fun row => HeadNeutralPlan.plan run limit (run % 2 == 0) (rows[child]!) norms row actual
        if run == 1 || ps.any (fun p => !p.isEmpty) then
          for e in executable (state.current[child]!) do
            let possible := ps.any fun pl => pl.any fun q =>
              decide (q.1.ap = e.1) || decide (normalAp q.1.ap = e.1)
            match apply possible e actual with
            | none => pure ()
            | some reply => out := val (cutOffer limit reply).ap (cutOffer limit reply).demand :: out
    vals := (normalizeOffers (run % 2 == 0) (OverwriteReplay.values (out.map fun a => ⟨a.ap,a.demand⟩))).map fun a => val a.ap a.demand
  return (state,vals.map fun a => {a with ap := {a.ap with base := ret}})

def process (run limit owner : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let norms := OverwriteReplay.views (run % 2 == 0) (saved[owner]!)
  let work := HeadNeutralPlan.cells run limit (run % 2 == 0) (rows[owner]!) norms (st.domains[owner]!)
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

def round (run limit calls : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State) : State := Id.run do
  let mut state := st
  for j in List.range calls do
    let mut out := state.offers[j+1]!
    for a in state.offers[j]! do
      state := register 0 a state
      -- The real outer caller uses the completely unchanged native OverwriteReplay.offer.
      out := out ++ offer run limit (rows[0]!) (saved[0]!) (state.current[0]!) a
    state := {state with offers := state.offers.set (j+1) (normalizeOffers (run % 2 == 0) (OverwriteReplay.values out))}
  for owner in List.range methods.length do
    state := process run limit owner methods rows saved state
  return state

def rounds (fuel run limit calls : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (OverwriteReplay.initial run limit methods.length calls source)
    (fun _ st => round run limit calls methods rows saved st)




def FlowAll (rows : List (List Row)) : Bool :=
  rows.all fun xs => xs.all fun row => row.entry.mark.isNone

theorem flow_at_index (rows : List (List Row)) (yes : FlowAll rows = true) (j : Nat) :
    HeadNeutralPlan.FlowRows (rows[j]!) := by
  rw [List.getElem!_eq_getElem?_getD]
  cases found : rows[j]? with
  | none =>
      change HeadNeutralPlan.FlowRows ([] : List Row)
      intro row inside
      cases inside
  | some xs =>
      have members : xs ∈ rows := List.mem_of_getElem? found
      have inner := List.all_eq_true.mp yes xs members
      intro row inside
      have yes := List.all_eq_true.mp inner row inside
      cases mark : row.entry.mark <;> simp_all

theorem offer_eq_old (run k : Nat) (rows : List Row) (saved : List Saved)
    (current : List Edge) (a : Offered) (flow : HeadNeutralPlan.FlowRows rows) :
    offer run k rows saved current a = OverwriteReplay.offer run k rows saved current a := by
  simp only [offer,OverwriteReplay.offer,
    HeadNeutralPlan.plan_list_eq_old run k (run % 2 == 0) rows _ a flow]

theorem body_eq_old (run k : Nat) (rows : List (List Row)) (saved : List (List Saved))
    (branch : List PointWriteReplay.Op) (q : Seed) (mask callMask : List Nat) (st : State)
    (flow : FlowAll rows = true) :
    body run k rows saved branch q mask callMask st =
      UniformReplay.body run k rows saved branch q mask callMask st := by
  have plans (j : Nat) (ns : List (Edge × Bool)) (a : Offered) :=
    HeadNeutralPlan.plan_list_eq_old run k (run % 2 == 0) (rows[j]!) ns a (flow_at_index rows flow j)
  simp only [body,UniformReplay.body,plans]
  rfl

theorem process_eq_old (run k owner : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State)
    (flow : FlowAll rows = true) :
    process run k owner methods rows saved st = UniformReplay.process run k owner methods rows saved st := by
  simp only [process,UniformReplay.process,
    HeadNeutralPlan.cells_eq_old run k (run % 2 == 0) (rows[owner]!) _ _ (flow_at_index rows flow owner)]
  simp only [body_eq_old run k rows saved _ _ _ _ _ flow]
  rfl

theorem round_eq_old (run k calls : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (st : State)
    (flow : FlowAll rows = true) :
    round run k calls methods rows saved st = UniformReplay.round run k calls methods rows saved st := by
  simp only [round,UniformReplay.round,
    offer_eq_old run k (rows[0]!) _ _ _ (flow_at_index rows flow 0),
    process_eq_old run k _ methods rows saved _ flow]
  rfl

theorem rounds_eq_old (fuel run k calls : Nat) (methods : List PointWriteReplay.Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered)
    (flow : FlowAll rows = true) :
    rounds fuel run k calls methods rows saved source =
      UniformReplay.rounds fuel run k calls methods rows saved source := by
  simp only [rounds,UniformReplay.rounds,round_eq_old run k calls methods rows saved _ flow]
end HeadNeutral
