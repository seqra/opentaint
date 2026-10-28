/-
Field-limit schedule experiment. The current schedule is 1, 1, 2, 3, ... .
The selected experiment uses 1, 2, 3, 4, ... . Only the limit selector changes.

Scope: positive run numbers and limits, the unchanged default, monotonicity,
and independence of direction and mark-mode selection from the schedule.
This model does not prove AP equivalence, analyzer soundness, termination,
runtime adapter correctness, or a performance bound. A larger field limit
can change an iteration's facts and demands. The experiment must measure it.
-/
import Lean

namespace ApSpec.RunIndexFieldLimitExperiment
set_option autoImplicit false

/-- The value is a zero-based offset, not a public run number.
    Offset 0 denotes run-1; `Run.number` can never return 0. -/
abbrev Run := Nat

def Run.number (run : Run) : Nat := run + 1
def Run.next (run : Run) : Run := run + 1
def first : Run := 0

inductive Schedule where
  | repeatRun1
  | runIndex
  deriving DecidableEq, Repr

def defaultSchedule : Schedule := .repeatRun1

def fieldLimit (schedule : Schedule) (run : Run) : Nat :=
  match schedule with
  | .repeatRun1 => max 1 run
  | .runIndex => run.number

inductive Direction where
  | forward
  | backward
  deriving DecidableEq, Repr

inductive MarkMode where
  | group
  | full
  deriving DecidableEq, Repr

/-- These selectors do not use the field limit or its schedule. -/
def direction (run : Run) : Direction :=
  if run.number % 2 = 1 then .forward else .backward

def markMode (run : Run) (selectedRun1Mode : MarkMode) : MarkMode :=
  if run = 0 then selectedRun1Mode else .full

/-- Product fields avoid introducing any new equality axiom. -/
abbrev Config := Nat × Nat × Direction × MarkMode

def Config.index (value : Config) : Nat := value.1
def Config.limit (value : Config) : Nat := value.2.1
def Config.direction (value : Config) : Direction := value.2.2.1
def Config.markMode (value : Config) : MarkMode := value.2.2.2

def config (schedule : Schedule) (run : Run) (selectedRun1Mode : MarkMode) : Config :=
  ⟨run.number, fieldLimit schedule run, direction run, markMode run selectedRun1Mode⟩

/-- The current selector is `max(1, index - 1)`. -/
def originalConfig (run : Run) (selectedRun1Mode : MarkMode) : Config :=
  ⟨run.number, max 1 (run.number - 1), direction run, markMode run selectedRun1Mode⟩

theorem run_number_positive (run : Run) : 0 < run.number :=
  Nat.zero_lt_succ run

theorem no_run_zero (run : Run) : run.number ≠ 0 :=
  Nat.ne_of_gt (run_number_positive run)

theorem next_number (run : Run) : run.next.number = run.number + 1 := rfl

theorem field_limit_positive (schedule : Schedule) (run : Run) :
    0 < fieldLimit schedule run := by
  cases schedule with
  | repeatRun1 =>
    cases run with
    | zero => exact Nat.zero_lt_succ 0
    | succ n => exact Nat.zero_lt_succ n
  | runIndex => exact run_number_positive run

theorem first_number : first.number = 1 := rfl

theorem first_limit (schedule : Schedule) : fieldLimit schedule first = 1 := by
  cases schedule <;> rfl

theorem default_is_repeat_run1 : defaultSchedule = .repeatRun1 := rfl

theorem default_limit_unchanged (run : Run) :
    fieldLimit defaultSchedule run = max 1 (run.number - 1) := by
  cases run <;> rfl

theorem default_config_unchanged (run : Run) (mode : MarkMode) :
    config defaultSchedule run mode = originalConfig run mode := by
  cases run <;> rfl

theorem run_index_limit_is_number (run : Run) :
    fieldLimit .runIndex run = run.number := rfl

theorem limits_nondecreasing (schedule : Schedule) (a b : Run)
    (ordered : a ≤ b) : fieldLimit schedule a ≤ fieldLimit schedule b := by
  cases schedule with
  | repeatRun1 =>
    cases a with
    | zero =>
      cases b with
      | zero => exact Nat.le_refl 1
      | succ b => exact Nat.succ_le_succ (Nat.zero_le b)
    | succ a =>
      cases b with
      | zero => exact False.elim (Nat.not_succ_le_zero a ordered)
      | succ b => exact ordered
  | runIndex => exact Nat.succ_le_succ ordered

theorem run_index_strictly_increasing (a b : Run) (ordered : a < b) :
    fieldLimit .runIndex a < fieldLimit .runIndex b :=
  Nat.succ_lt_succ ordered

theorem run_index_next_limit (run : Run) :
    fieldLimit .runIndex run.next = fieldLimit .runIndex run + 1 := rfl

theorem next_limit_does_not_decrease (schedule : Schedule) (run : Run) :
    fieldLimit schedule run ≤ fieldLimit schedule run.next :=
  limits_nondecreasing schedule run run.next (Nat.le_succ run)

theorem config_index_independent (a b : Schedule) (run : Run) (mode : MarkMode) :
    (config a run mode).index = (config b run mode).index := rfl

theorem config_direction_independent (a b : Schedule) (run : Run) (mode : MarkMode) :
    (config a run mode).direction = (config b run mode).direction := rfl

theorem config_mark_mode_independent (a b : Schedule) (run : Run) (mode : MarkMode) :
    (config a run mode).markMode = (config b run mode).markMode := rfl

theorem first_direction : direction first = .forward := rfl

theorem first_uses_selected_mode (mode : MarkMode) : markMode first mode = mode := rfl

theorem later_runs_use_full (run : Run) (later : run ≠ 0) (mode : MarkMode) :
    markMode run mode = .full := by
  exact if_neg later

namespace Controls
def firstSix : List Run := [0, 1, 2, 3, 4, 5]

def checks : List Bool := [
  decide (firstSix.map Run.number = [1, 2, 3, 4, 5, 6]),
  decide (firstSix.map (fieldLimit defaultSchedule) = [1, 1, 2, 3, 4, 5]),
  decide (firstSix.map (fieldLimit .runIndex) = [1, 2, 3, 4, 5, 6]),
  decide (firstSix.map direction = [.forward, .backward, .forward, .backward, .forward, .backward]),
  decide (firstSix.map (fun run => markMode run .group) = [.group, .full, .full, .full, .full, .full]),
  decide (firstSix.map (fun run => markMode run .full) = [.full, .full, .full, .full, .full, .full]),
  decide (fieldLimit defaultSchedule first.next = 1),
  decide (fieldLimit .runIndex first.next = 2)
]

theorem checks_pass : checks.all id = true := by decide
end Controls

end ApSpec.RunIndexFieldLimitExperiment

/- Audit all owned declarations. No axiom is permitted, including choice,
propositional extensionality and quotient soundness. This audit is stronger
than merely searching the source for `sorry` or `axiom`. -/
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "ApSpec.RunIndexFieldLimitExperiment." then
      count := count + 1
      let axioms ← collectAxioms name
      if !axioms.isEmpty then
        throwError "Unexpected axioms: {name}: {axioms}"
  if count == 0 then throwError "No schedule declarations found"
  logInfo m!"Audited {count} schedule declarations; every axiom set is empty."

#eval do
  let checks := ApSpec.RunIndexFieldLimitExperiment.Controls.checks
  if !(checks.all id) then throw (IO.userError "Schedule controls failed")
  IO.println s!"Executable schedule controls passed: {checks.length}."

#print axioms ApSpec.RunIndexFieldLimitExperiment.field_limit_positive
#print axioms ApSpec.RunIndexFieldLimitExperiment.default_config_unchanged
#print axioms ApSpec.RunIndexFieldLimitExperiment.limits_nondecreasing
#print axioms ApSpec.RunIndexFieldLimitExperiment.run_index_strictly_increasing
#print axioms ApSpec.RunIndexFieldLimitExperiment.config_direction_independent
#print axioms ApSpec.RunIndexFieldLimitExperiment.config_mark_mode_independent
