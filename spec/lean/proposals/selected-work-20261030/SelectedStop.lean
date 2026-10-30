import Std
import ApSpec.CurrentDemandFrontier

/-!
Executable selected stop contract. This file reuses the checked normalized
builder model; it does not redefine AP transfer or claim that later runs have
no work. A completed barrier supplies an exact explicit snapshot. Production
binding: HandOff.of -> DemandStore.Builder.add + counts.merge, then frontier.
-/
namespace SelectedWork.Stop

open ApSpec.CurrentDemandFrontier

/-- A list witness for method-key support; repeated keys do not affect emptiness. -/
def methodKeys (rows : List Key) : List Nat := rows.map (·.method)

theorem method_keys_empty_iff (rows : List Key) :
    methodKeys rows = [] ↔ rows = [] := by
  cases rows <;> simp [methodKeys]

theorem normalized_count_empty_iff (keys : List Key) :
    (build keys).count = 0 ↔ (build keys).entries = [] := by
  rw [build_count]
  exact List.length_eq_zero_iff

theorem normalized_key_support_empty_iff (keys : List Key) :
    methodKeys (build keys).entries = [] ↔ (build keys).count = 0 := by
  rw [method_keys_empty_iff, normalized_count_empty_iff]

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr

inductive Status where
  | complete | timeout | oom | failed
  deriving DecidableEq, Repr

inductive Reason where
  | stopRule | noDemand | policy | abnormal
  deriving DecidableEq, Repr

inductive Decision where
  | next (index : Nat) (policyCalled : Bool)
  | done (status : Status) (reason : Reason) (policyCalled : Bool)
  deriving DecidableEq, Repr

structure Input where
  run : Nat
  direction : Direction
  reportHasDemand : Bool
  explicitRows : List Key
  hasStaticCompletion : Bool := false
  hasSharedStaticCarry : Bool := false
  observedDemandCounter : Nat := 0
  continuePolicy : Bool := true
  deriving DecidableEq, Repr

/-- Exactly the post-barrier order in the selected Kotlin patch. -/
def choose (i : Input) : Decision :=
  match i.direction with
  | .backward => .next (i.run + 1) false
  | .forward =>
      if !i.reportHasDemand then .done .complete .stopRule false
      else if i.run != 1 then
        if i.hasStaticCompletion || i.hasSharedStaticCarry then .done .failed .abnormal false
        else if i.explicitRows.isEmpty then .done .complete .noDemand false
        else if i.continuePolicy then .next (i.run + 1) true
        else .done .complete .policy true
      else if i.continuePolicy then .next (i.run + 1) true
      else .done .complete .policy true

theorem restricted_empty_stops (i : Input)
    (hf : i.direction = .forward) (hr : i.run ≠ 1)
    (hd : i.reportHasDemand = true) (he : i.explicitRows = [])
    (hs : i.hasStaticCompletion = false) (hc : i.hasSharedStaticCarry = false) :
    choose i = .done .complete .noDemand false := by
  simp [choose, hf, hr, hd, he, hs, hc]

theorem report_empty_wins (i : Input)
    (hf : i.direction = .forward) (hd : i.reportHasDemand = false) :
    choose i = .done .complete .stopRule false := by
  simp [choose, hf, hd]

theorem backward_continues (i : Input) (hb : i.direction = .backward) :
    choose i = .next (i.run + 1) false := by
  simp [choose, hb]

theorem run1_does_not_take_new_stop (i : Input) (hr : i.run = 1) :
    choose i ≠ .done .complete .noDemand false := by
  cases hd : i.direction <;> cases hrp : i.reportHasDemand <;>
    cases hp : i.continuePolicy <;> simp [choose, hd, hr, hrp, hp]

theorem nonempty_does_not_take_new_stop (i : Input) (he : i.explicitRows ≠ []) :
    choose i ≠ .done .complete .noDemand false := by
  cases hd : i.direction <;> cases hrp : i.reportHasDemand <;>
    cases hp : i.continuePolicy <;> cases hs : i.hasStaticCompletion <;>
    cases hc : i.hasSharedStaticCarry <;>
    by_cases hr : i.run = 1 <;> simp_all [choose, List.isEmpty_iff]

theorem observed_counter_irrelevant (i : Input) (n : Nat) :
    choose { i with observedDemandCounter := n } = choose i := by
  rfl

/-- Immutable report payload, including states, identities and witness IDs. -/
structure ReportEntry where
  identity : Nat
  confirmed : Bool
  witnessIds : List Nat
  deriving DecidableEq, Repr

structure Snapshot where
  report : List ReportEntry
  persistedRecords : List Nat
  frontierLog : List Nat
  deriving DecidableEq, Repr

structure Output where
  decision : Decision
  snapshot : Snapshot
  deriving DecidableEq, Repr

/-- ready means report/persist/HandOff/frontier work has completed. -/
inductive BarrierEnd where
  | ready | oom | failed
  deriving DecidableEq, Repr

/-- Late memory-guard cancellation overrides even an already chosen stop. -/
def finish (engine : Status) (barrier : BarrierEnd) (active : Bool)
    (i : Input) (snapshotSoFar : Snapshot) : Output :=
  let d := match engine with
    | .timeout => .done .timeout .abnormal false
    | .oom => .done .oom .abnormal false
    | .failed => .done .failed .abnormal false
    | .complete => match barrier with
      | .oom => .done .oom .abnormal false
      | .failed => .done .failed .abnormal false
      | .ready => if active then choose i else .done .oom .abnormal false
  ⟨d, snapshotSoFar⟩

theorem payload_unchanged (engine : Status) (barrier : BarrierEnd) (active : Bool)
    (i : Input) (s : Snapshot) :
    (finish engine barrier active i s).snapshot = s := by
  rfl

theorem incomplete_not_success (engine : Status) (he : engine ≠ .complete)
    (barrier : BarrierEnd) (active : Bool) (i : Input) (s : Snapshot) :
    (finish engine barrier active i s).decision = .done engine .abnormal false := by
  cases engine <;> simp_all [finish]

theorem failed_barrier_not_success (i : Input) (s : Snapshot) (active : Bool) :
    (finish .complete .failed active i s).decision = .done .failed .abnormal false := by
  rfl

theorem guard_cancellation_wins (i : Input) (s : Snapshot) :
    (finish .complete .ready false i s).decision = .done .oom .abnormal false := by
  rfl

namespace Controls

def emptyForward (run : Nat) (observed : Nat) : Input :=
  ⟨run, .forward, true, [], false, false, observed, true⟩
def oneRow : List Key := [⟨4, 8⟩]

theorem positive_observed_empty_stops :
    choose (emptyForward 5 999) = .done .complete .noDemand false := rfl

theorem zero_observed_nonempty_continues :
    choose { emptyForward 5 0 with explicitRows := oneRow } = .next 6 true := rfl

theorem run1_empty_continues : choose (emptyForward 1 999) = .next 2 true := rfl

theorem empty_backward_continues :
    choose { emptyForward 4 999 with direction := .backward } = .next 5 false := rfl

theorem report_empty_precedes_empty_demand :
    choose { emptyForward 5 999 with reportHasDemand := false } =
      .done .complete .stopRule false := rfl

theorem no_policy_after_empty :
    choose { emptyForward 5 999 with continuePolicy := false } =
      .done .complete .noDemand false := rfl

theorem virtual_family_rejected_on_restricted_forward :
    choose { emptyForward 5 0 with hasStaticCompletion := true } =
      .done .failed .abnormal false := rfl

/-- Synthetic controller fixture uses the measured outgoing counts only. -/
def measuredCounts : List Nat := [111374, 112217, 85, 200801, 0]


/-- Only emptiness matters here; avoid constructing the large cardinalities. -/
def rowPresence (n : Nat) : List Key := if n = 0 then [] else oneRow

def continueCount (run : Nat) (n : Nat) : Decision :=
  choose { emptyForward run 999 with
    direction := if run % 2 = 1 then .forward else .backward
    explicitRows := rowPresence n }

def measuredDecisions : List Decision :=
  measuredCounts.zipIdx.map fun (n, offset) => continueCount (offset + 1) n

theorem owasp_sequence_ends_at_5 : measuredDecisions =
    [.next 2 true, .next 3 false, .next 4 true, .next 5 false,
     .done .complete .noDemand false] := by decide

def sampleReport : Snapshot :=
  ⟨[⟨7, false, [3, 9]⟩, ⟨8, true, [4]⟩], [10, 12], [1, 2, 3, 4, 5]⟩

theorem report_persistence_frontier_retained :
    finish .complete .ready true (emptyForward 5 999) sampleReport =
      ⟨.done .complete .noDemand false, sampleReport⟩ := rfl

def check : Bool :=
  choose (emptyForward 5 999) == .done .complete .noDemand false &&
  choose { emptyForward 5 0 with explicitRows := oneRow } == .next 6 true &&
  choose (emptyForward 1 999) == .next 2 true &&
  choose { emptyForward 4 0 with direction := .backward } == .next 5 false &&
  (finish .complete .ready false (emptyForward 5 999) sampleReport).decision ==
    .done .oom .abnormal false

theorem checked : check = true := rfl

end Controls

#print axioms normalized_count_empty_iff
#print axioms normalized_key_support_empty_iff
#print axioms restricted_empty_stops
#print axioms nonempty_does_not_take_new_stop
#print axioms observed_counter_irrelevant
#print axioms payload_unchanged
#print axioms incomplete_not_success
#print axioms guard_cancellation_wins
#print axioms Controls.owasp_sequence_ends_at_5
#print axioms Controls.checked

end SelectedWork.Stop
