import GuardedTermination
import BoundCore
import ClosedExactSupport
import ClosedUniformSupport

namespace TerminalReplay

set_option maxRecDepth 65536
set_option maxHeartbeats 300000000

-- In these straight-line root models the only consumers of ZERO -> DT
-- are the listed observations and their own backward source permissions.
-- DATA histories and publication stay in the provided transition.
structure Model (State : Type) where
  initial : State
  step : Nat → State → State
  witnesses : Nat → State → State → List Nat
  required : List Nat
  omitRoot : State → State

structure Frame (State : Type) where
  body : State
  witnessed : List Nat
  deriving Inhabited

def advance (m : Model α) (run : Nat) (old : Frame α) : Frame α :=
  let next := m.step run old.body
  let forward := run % 2 == 1
  let closed := m.required.all (fun id => decide (id ∈ old.witnessed))
  let keepBody := !(forward && GuardedTermination.retireTarget closed [] [] [] [])
  ⟨if keepBody then next else m.omitRoot next,
   if forward then (old.witnessed ++ m.witnesses run old.body next).eraseDups
   else old.witnessed⟩

def history (m : Model α) : Nat → Frame α
  | 0 => ⟨m.initial,[]⟩
  | n+1 => advance m (n+1) (history m n)

theorem an_unwitnessed_binding_prevents_retirement (m : Model α) (id : Nat)
    (needed : id ∈ m.required) (missing : id ∉ old.witnessed) :
    (advance m run old).body = m.step run old.body := by
  have closed : m.required.all (fun id => decide (id ∈ old.witnessed)) = false := by
    cases h : m.required.all (fun id => decide (id ∈ old.witnessed))
    · rfl
    · exact False.elim (missing (of_decide_eq_true (List.all_eq_true.mp h _ needed)))
  simp [advance,closed,GuardedTermination.retireTarget]

theorem a_quiet_body_and_complete_receipts_cannot_restart (m : Model α)
    (body : α) (receipts : List Nat)
    (fixed : ∀ run, m.step run body = body)
    (noRoot : m.omitRoot body = body)
    (noNew : ∀ run, m.witnesses run body body = [])
    (unique : receipts.eraseDups = receipts) (start : Nat)
    (reached : history m start = ⟨body,receipts⟩) (n : Nat) :
    ((history m (n+start)).body = body) := by
  suffices ∀ n, history m (n+start) = ⟨body,receipts⟩ by exact congrArg Frame.body (this n)
  intro n
  induction n with
  | zero => simpa using reached
  | succ n ih =>
    rw [Nat.succ_add,history,ih]
    simp [advance,fixed,noRoot,noNew,unique]

open NonEmptyPolicy NonEmptyRestriction

-- A receipt contains a supported return from the actual call binding.
-- A potential match using an unsupported MUST lane yields demand, so
-- the receipt check rejects it.
def received (saved : List (Ap × Value)) (apply : (Ap × Value) → Offered → Option Value)
    (actual : Offered) (finish : Value → Bool) : Bool :=
  saved.any fun record => (apply record actual).any fun out => !out.demand && finish out

namespace Exact
open ProvisionalMustCycle

def model : Model State where
  initial := initial
  step := step
  required := [0,1]
  -- Calls are independent and each marking action accepts any input T.
  -- The root source reaches x, and the field source reaches y.
  witnesses _ old next :=
    (if old.permissionRoot && received next.records savedForward rootActual (fun x => x.ap == ru)
      then [0] else []) ++
    (if old.permissionField && received next.records savedForward fieldActual (fun x => x.ap == ru)
      then [1] else [])
  omitRoot state := {state with rootDemand := false, sinkSeeds := []}

theorem run7_stops_with_both_normal_bindings :
    let h := TerminalReplay.history model 7
    h.witnessed = [0,1] ∧ h.body.reports = [0,1] ∧ h.body.rows = [] ∧ h.body.rootDemand = false :=
  by decide

end Exact

namespace Uniform
open ProvisionalUniformCycle

def model : Model State where
  initial := initial
  step := step
  required := [0,1]
  witnesses _ old next :=
    (if old.permissionRoot && received next.records savedForward rootActual (fun x => x.ap == ru)
      then [0] else []) ++
    (if old.permissionField && received next.records savedForward fieldActual (fun x => x.ap == ru)
      then [1] else [])
  omitRoot state := {state with rootDemand := false, sinkSeeds := []}

theorem run7_stops_with_both_normal_bindings :
    let h := TerminalReplay.history model 7
    h.witnessed = [0,1] ∧ h.body.reports = [0,1] ∧ h.body.rows = [] ∧ h.body.rootDemand = false :=
  by decide

end Uniform

namespace Different
open DifferentUniformReply

-- b supplies both sites. a.f cannot satisfy the g condition, so it
-- supplies only the field site. The third receipt must use this call's
-- actual f input, even though both observations accept any position.
def model : Model State where
  initial := initial
  step := step
  required := [0,1,2]
  witnesses _ old next :=
    (if old.permissionB && received next.records savedForward rootActual (fun x => x.ap == out [] .must)
      then [0] else []) ++
    (if old.permissionB && received next.records savedForward rootActual (fun x => x.ap == out [f] .must)
      then [1] else []) ++
    (if old.permissionA && received next.records savedForward fieldActual (fun x => x.ap == out [f] .must)
      then [2] else [])
  omitRoot state := {state with rootDemand := false, sinkSeeds := []}

theorem the_field_source_cannot_satisfy_the_other_sites_guard :
    dropHead fieldActual.ap.path [g] = none ∧ dropHead [g] fieldActual.ap.path = none := by decide

theorem run7_stops_with_all_three_normal_bindings :
    let h := TerminalReplay.history model 7
    h.witnessed = [0,1,2] ∧ h.body.reports = [0,1] ∧ h.body.rows = [] ∧ h.body.rootDemand = false :=
  by decide

end Different

namespace Alternating
open AlternatingCondition GuardedTermination

def routes : List (List Bool) := alternatives 3

-- The record must be present in the retained run, and its own paired
-- publication must admit this actual. No witness comes from guessing
-- an input or from the execution that suppressed replies.
def committed (run : Nat) (prior next : UniformAlternating.State) :
    List Bool → Nat → Offered → Color → Bool
  | [], _, _, _ => true
  | atField :: rest, stage, offer, mark =>
    let expected := value p (nextOffer atField mark).ap.path .must mark.flip false
    (next.data.offers[stage+1]!).any (fun actual => BoundCore.covers actual expected) &&
    (UniformAlternating.candidates run (UniformAlternating.limit run) false prior.rows prior.saved [offer]).any
      (fun edge => decide (edge ∈ next.data.raw) &&
        UniformAlternating.read edge offer == some expected) &&
    committed run prior next rest (stage+1) (nextOffer atField mark) mark.flip

def model : Model UniformAlternating.State where
  initial := UniformAlternating.initial
  step := retainedStep
  required := List.range routes.length
  witnesses run old next :=
    if old.sourceAllowed then (List.range routes.length).filter fun i => committed run old next routes[i]! 0 source .t
    else []
  omitRoot state := {state with observationActive := false}

local instance : Inhabited UniformAlternating.State := ⟨UniformAlternating.initial⟩

#eval do
  let states := (List.range 7).scanl (fun frame k => advance model (k+1) frame) ⟨model.initial,[]⟩
  for run in List.range' 1 7 do
    let before := states[run-1]!.body
    let after := states[run]!
    let active := if run % 2 == 0 then before.observationActive else before.sourceAllowed
    if active && decide (UniformAlternating.round false run (UniformAlternating.limit run)
        before.rows before.saved after.body.data ≠ after.body.data) then
      throw (IO.userError s!"alternating run-{run} did not reach closure")
    if UniformAlternating.stopped run after.body != (run == 7) then
      throw (IO.userError s!"unexpected alternating stop at run-{run}")
    if run % 2 == 1 then
      IO.println s!"alternating run-{run}: {after.witnessed}, DATA={after.body.rows.length}, Target={after.body.observationActive}, NORMAL={after.body.report}"
  let final := states[7]!
  if states[3]!.witnessed != List.range 8 ||
      decide (final.body ≠ UniformAlternating.quiet true final.body.saved) then
    throw (IO.userError "incomplete alternating service")

end Alternating

end TerminalReplay
