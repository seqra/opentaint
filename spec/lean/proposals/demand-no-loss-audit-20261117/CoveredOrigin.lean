import CondensedDemandRefinement
import LostMarkOrigin

namespace CoveredOrigin

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine

-- One ordinary exact read after a retained prefix consumes the unknown
-- suffix. A coarse result can therefore reach the same observer as a
-- second source with actual uniform support.
def normalA : Value := val (ap p [] .must (some t))
def sourceB : Value := LostMarkOrigin.sourceB
def resultB (k : Nat) := LostMarkOrigin.resultB k

def baselineCut (k : Nat) (c : Value) : Value :=
  if c.ap.path.length > k then
    {c with ap := {c.ap with path := c.ap.path.take k, tail := .may, e := []}, demand := true}
  else c

theorem both_field_cut_domains_expose_the_same_coarse_join_value :
    resultB 2 = some (val (ap p [] .may (some t)) true) ∧
    LostMarkOrigin.readThree (baselineCut 2 sourceB) = resultB 2 := by decide

theorem the_late_exact_track_uses_the_second_marking_point :
    resultB 4 = some (val (ap p [f] .exact (some t))) := by decide

theorem at_run3_the_old_geometric_coverage_guard_accepts_b :
    normalA.demand = false ∧ normalA.ap.tail = .must ∧
    (resultB 2).any (fun b => b.demand && b.ap.tail == .may &&
      b.ap.base == normalA.ap.base && b.ap.path == normalA.ap.path &&
      b.ap.mark == normalA.ap.mark && b.ap.e.isEmpty &&
      b.h == normalA.h) = true := by decide

-- Both branches converge at one statement in a void root. There are no
-- exported DATA edges from the merged local. Backward reach is checked
-- separately on the ordinary field chain below.
structure Frame where
  report : Bool
  deepTrack : Bool
  rootDemand : Bool
  deriving Repr, DecidableEq, BEq

def forward (dropCovered : Bool) (n : Nat) (active : Bool) : Frame :=
  if !active then ⟨false,false,false⟩ else
  let run := 2*n+1
  let k := max 1 (run-1)
  ⟨true, LostMarkOrigin.normalB k,
    LostMarkOrigin.demandB k && !(dropCovered && n != 0)⟩

def cold (dropCovered : Bool) : Nat → Frame
  | 0 => forward dropCovered 0 true
  | n+1 => forward dropCovered (n+1) (cold dropCovered n).rootDemand

theorem backward_source_permission_uses_the_old_and_new_ordinary_field_path :
    admits (LostMarkOrigin.backThree 1).ap.tail [] [f,f,f] = true ∧
    admits (LostMarkOrigin.backThree 3).ap.tail [] [f] = true := by decide

theorem baseline_finishes_after_the_deep_track_is_present :
    cold false 0 = ⟨true,false,true⟩ ∧ cold false 1 = ⟨true,false,true⟩ ∧
    cold false 2 = ⟨true,true,false⟩ := by decide

theorem data_only_coverage_finishes_before_the_deep_track :
    cold true 1 = ⟨true,false,false⟩ := by decide

theorem there_is_no_later_recovery_under_the_data_only_rule (n : Nat) :
    cold true (n+2) = ⟨false,false,false⟩ := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.succ_add,cold,ih]; rfl

end CoveredOrigin
