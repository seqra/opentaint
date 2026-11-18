import OverwriteReplay

namespace ExclusionChildReplay
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE NestedSavedReplayCycle NestedColdMachine
open OverwriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

/-- Same already-prepared child service. Real operand and record field E
    no longer disable routing. q.E stays empty under the supported raw C2
    STAR family; mark exclusions and every other gate stay unchanged. -/
def eligible (q : Ap) (mask : List Nat) (e : Edge) (opposite : Bool) (a : Offered) : Bool :=
  q.tail == .star && a.ap.tail == .star && !a.demand && opposite &&
  q.mark.isNone && a.ap.mark.isNone && e.1.mark.isNone && e.2.ap.mark.isNone &&
  q.e.isEmpty && q.mx.isEmpty && a.ap.mx.isEmpty &&
  e.1.mx.isEmpty && e.2.ap.mx.isEmpty && !e.2.h &&
  e.1.tail == .star && e.2.ap.tail == .star && !e.2.demand &&
  match dropHead a.ap.path e.1.path with
  | some (field :: _) => mask.contains field
  | _ => false

def route (extended : Bool) (q : Ap) (mask : List Nat)
    (e : Edge × Bool) (a : Offered) : Option Offered :=
  if extended then
    if eligible q mask e.1 e.2 a then none else OverwriteReplay.apply e.2 e.1 a
  else OverwriteReplay.route q mask e a

theorem old_eligible_implies_new_eligible (q : Ap) (mask : List Nat)
    (e : Edge) (opposite : Bool) (a : Offered)
    (old : PreparedChildReplay.delegated q mask e opposite a = true) :
    eligible q mask e opposite a = true := by
  simp_all [PreparedChildReplay.delegated,eligible]
  exact old.2

theorem every_new_reply_is_the_unmodified_old_reply (q : Ap) (mask : List Nat)
    (e : Edge × Bool) (a result : Offered)
    (kept : route true q mask e a = some result) :
    route false q mask e a = some result := by
  cases old : PreparedChildReplay.delegated q mask e.1 e.2 a
  · have native : eligible q mask e.1 e.2 a = false ∧ OverwriteReplay.apply e.2 e.1 a = some result := by
      simpa [route] using kept
    simpa [route,OverwriteReplay.route,old] using native.2
  · have new := old_eligible_implies_new_eligible q mask e.1 e.2 a old
    simp [route,new] at kept

theorem every_kept_reply_preserves_native_fields_marks_layers (q : Ap) (mask : List Nat)
    (e : Edge × Bool) (a result : Offered)
    (kept : route true q mask e a = some result) :
    OverwriteReplay.apply e.2 e.1 a = some result := by
  unfold route at kept
  simp only [Bool.true_eq,ite_true] at kept
  split at kept
  · contradiction
  · exact kept

theorem no_extra_postprocessing_work_for_any_fixed_offer
    (q : Ap) (mask : List Nat) (es : List (Edge × Bool)) (a : Offered)
    (post : Offered → List α) :
    ((es.filterMap fun e => route true q mask e a).flatMap post).length ≤
      ((es.filterMap fun e => route false q mask e a).flatMap post).length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases old : route false q mask e a with
    | none =>
      cases new : route true q mask e a with
      | none => simp only [List.filterMap_cons,old,new,List.flatMap_cons,List.flatMap_nil,List.nil_append,List.length_append]; exact ih
      | some result =>
        have impossible := every_new_reply_is_the_unmodified_old_reply q mask e a result new
        simp [old] at impossible
    | some oldResult =>
      cases new : route true q mask e a with
      | none => simp only [List.filterMap_cons,old,new,List.flatMap_cons,List.flatMap_nil,List.nil_append,List.length_append]; omega
      | some newResult =>
        have eq := every_new_reply_is_the_unmodified_old_reply q mask e a newResult new
        have same := Option.some.inj (old.symm.trans eq)
        subst newResult
        simp only [List.filterMap_cons,old,new,List.flatMap_cons,List.flatMap_nil,List.nil_append,List.length_append]
        omega

def body (extended : Bool) (run limit : Nat) (rows : List (List Row))
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
        let norms := OverwriteReplay.views (run % 2 == 0) (saved[child]!)
        for e in norms do
          let result := route extended q.ap callMask e actual
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

def process (extended : Bool) (run limit owner : Nat) (methods : List Method)
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
        let (next,outputs) := body extended run limit rows saved branch q mask callMask state
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

def round (extended : Bool) (run limit calls : Nat) (methods : List Method)
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
    state := process extended run limit owner methods rows saved state
  return state

def rounds (extended : Bool) (fuel run limit calls : Nat) (methods : List Method)
    (rows : List (List Row)) (saved : List (List Saved)) (source : Offered) : State :=
  fuel.rec (OverwriteReplay.initial run limit methods.length calls source)
    (fun _ st => round extended run limit calls methods rows saved st)



end ExclusionChildReplay
#print axioms ExclusionChildReplay.old_eligible_implies_new_eligible
#print axioms ExclusionChildReplay.every_new_reply_is_the_unmodified_old_reply
#print axioms ExclusionChildReplay.every_kept_reply_preserves_native_fields_marks_layers
#print axioms ExclusionChildReplay.no_extra_postprocessing_work_for_any_fixed_offer
