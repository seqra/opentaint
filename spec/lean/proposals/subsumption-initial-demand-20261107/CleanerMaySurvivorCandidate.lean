/-
Candidate policy only; no selected spec or runtime cleaner change.
Reuse the checked cleaner counterexample. A selected partial concrete
STAR/DEMAND survivor becomes MAY, with the original, layer and H retained.
The finite example has an empty-path EXACT selected cleaner and Empty E.
-/
import RootExactCleanerGap

namespace CleanerMaySurvivorCandidate
open PlainStarRelativeAdmission ApSpec RootExactCleanerGap

set_option maxRecDepth 16384
set_option maxHeartbeats 32000000

def widen (v : Value) : Value :=
  match v.data.fact.kind with
  | .star _ =>
      if v.data.fact.base = arg ∧ v.data.fact.mark = .conc t ∧ v.data.demand then
        {v with data := ⟨{v.data.fact with kind := .any},true⟩}
      else v
  | _ => v

def candidateClean (v : Value) : List Value := (clean v).map widen
def candidateBoundary (mode : Mode) (v : Value) : List Value :=
  if mode.direction = .forward then
    (candidateClean v).flatMap fun a => [a] ++ copy arg ret a
  else (copy ret arg v).flatMap candidateClean

def firstRows : List Row := zeroRow :: unique (r1Seeds.flatMap fun seed =>
  (candidateBoundary ⟨1,1,.forward⟩ (startValue seed)).map (publicRow seed.initial))

def candidateInfer (mode : Mode) (permissions : List FlowDemandCompletion.Row)
    (v : Value) : List Row :=
  unique ((commands mode permissions v).flatMap fun seed =>
    (candidateBoundary mode (startValue seed)).flatMap fun raw =>
      permissions.filterMap fun permission => finish mode permission seed raw)

def secondRows : List Row :=
  candidateInfer b2 (handoff b2 firstRows) sinkReverse
def nextSaved : List Row := normal firstRows ++ (normal secondRows).map reverseNormal

theorem STAR_relation_is_contained_in_MAY_relation
    (initial output : PFact) (e : Excl) (l0 l1 : Loc)
    (_shape : output.kind = .star e) (old : den initial output l0 l1) :
    den initial {output with kind := .any} l0 l1 := by
  obtain ⟨b0,b1,m0,m1,m2,suffixIn,suffixOut,p0,p1,ki,kf⟩ := old
  exact ⟨b0,b1,m0,m1,m2,suffixIn,suffixOut,p0,p1,ki,True.intro⟩

theorem widening_retains_layer_and_protection (v : Value) :
    (widen v).data.demand = v.data.demand ∧ (widen v).h = v.h := by
  cases h : v.data.fact.kind with
  | star e =>
      by_cases accepted : v.data.fact.base = arg ∧ v.data.fact.mark = .conc t ∧
          v.data.demand = true
      · simp [widen,h,accepted,accepted.2.2]
      · simp [widen,h,accepted]
  | any => simp [widen,h]
  | exact => simp [widen,h]

theorem exact_and_FLOW_cleaner_results_are_unchanged :
    candidateClean source = clean source ∧
    candidateClean (startValue ⟨pat arg [] .star,.normal⟩) =
      clean (startValue ⟨pat arg [] .star,.normal⟩) := by decide

theorem partial_STAR_survivor_becomes_protected_MAY_DEMAND :
    candidateClean (startValue ⟨pat arg [] .star (.full t),.demand⟩) =
      [value (pat arg [] .any (.full t)) .demand true] := by decide

theorem first_phase_keeps_STAR_premises_and_widens_only_T_conclusions :
    firstRows = [zeroRow,expectedFlowArg,expectedFlowRet,
      ⟨pat arg [] .star (.full t),value (pat arg [] .any (.full t)) .demand true⟩,
      ⟨pat arg [] .star (.full t),value (pat ret [] .any (.full t)) .demand true⟩] := by decide

theorem second_phase_admits_exact_child_and_exact_FLOW_prefix :
    commands b2 (handoff b2 firstRows) sinkReverse =
      [⟨pat ret [g] .exact (.full t),.normal⟩,⟨pat ret [] .exact,.normal⟩] := by decide

theorem second_phase_recovers_the_precise_NORMAL_relation :
    secondRows = [⟨pat ret [g] .exact (.full t),
      value (pat arg [g] .exact (.full t)) .normal true⟩] := by decide

theorem real_source_permission_is_retained :
    (applyRows secondRows sinkReverse).any sourceHit = true := by decide

theorem saved_opposite_relation_transports_the_precise_NORMAL_source :
    (applyRows nextSaved source).filterMap hitSink = [false] := by decide

theorem the_third_forward_phase_has_a_NORMAL_finding :
    targets nextSaved = [false] := by decide

end CleanerMaySurvivorCandidate
