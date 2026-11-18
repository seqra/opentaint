import UniformCoverage

/- Ordinary configured source, selected cleaner and sink. No pass action,
   loop, recursion, field write, field cut or analyzable helper is present.
   The selected cleaner scalar row is Reference.kt concPart: a MUST at
   the exact cleaned root is PART and keeps its shape on DEMAND. -/
namespace UniformRootCleanerCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NormalUniformNE

def x : Nat := 20
def sourceValue : Value := val (ap x [] .must (some t))
def sinkRequirement : Value := val (ap x [] .may (some t)) true

/-- Selected RemoveMark(T), EXACT reach at x. A surviving selected mark
    has the existing protection bit. STAR alone loses correlation to MAY;
    the existing MUST and MAY partial rows keep their tail on DEMAND. -/
def cleanRoot (c : Value) : Option Value :=
  if c.ap.base != x || c.ap.mark != some t then some c
  else if !c.ap.path.isEmpty then some {c with h := true}
  else if c.ap.tail == .exact then none
  else some {c with ap := {c.ap with tail :=
    if c.ap.tail == .star then .may else c.ap.tail},demand := true,h := true}

def cleanedSource : Value := {sourceValue with demand := true,h := true}
def cleanedRequirement : Value := {sinkRequirement with h := true}

inductive Endpoint where | zero | target
  deriving DecidableEq, BEq, Repr
structure Terminal where
  premise : Endpoint
  conclusion : Endpoint
  demand : Bool
  deriving DecidableEq, BEq, Repr
structure ControlRow where
  entry : Endpoint
  exit : Endpoint
  deriving DecidableEq, BEq, Repr

def target : Terminal := ⟨.zero,.target,true⟩
def completion : Terminal := ⟨.zero,.zero,false⟩
def guidance : ControlRow := ⟨.target,.zero⟩

/-- Existing typed Target admission, not an owned DATA/MAY initial. -/
def admitted (rows : List ControlRow) : Bool := rows.contains guidance
def controlC5 (row : ControlRow) (edge : Terminal) : Option Terminal :=
  if row == guidance && edge.premise == .zero then some edge else none
def handoff (edges : List Terminal) : List ControlRow :=
  edges.filterMap fun edge => if edge.demand then
    some ⟨edge.conclusion,edge.premise⟩ else none

/-- CM(x.[any],T). A concrete uniform/MAY witness overlaps this literal;
    its existing DEMAND support cannot confirm a NormalTarget. -/
def sinkForward (c : Value) : Option Terminal :=
  if c.ap.base == x && c.ap.mark == some t && c.ap.path.isEmpty &&
      (c.ap.tail == .must || c.ap.tail == .may || c.ap.tail == .ne ||
       c.ap.tail == .exact) then some ⟨.zero,.target,c.demand⟩ else none

/-- The persisted NORMAL source is ZERO -> x.MUST/T. Its opposite-direction
    weak view accepts the overlapping MAY requirement. ZERO in the reversed
    application becomes Target. The requirement is already DEMAND. -/
def sourceMatches (c : Value) : Bool :=
  c.ap.base == x && c.ap.mark == some t && c.ap.path.isEmpty &&
    (c.ap.tail == .may || c.ap.tail == .ne || c.ap.tail == .must || c.ap.tail == .exact)
def sourceBackward (c : Value) : Option Terminal :=
  if sourceMatches c then some ⟨.zero,.target,true⟩ else none

structure Capture where
  summaries : List Terminal := []
  sourcePermission : Bool := false
  sinkPermission : Bool := false
  deriving DecidableEq, BEq, Repr

def forwardRun (run : Nat) (rows : List ControlRow) (sourcePermission : Bool) : Capture :=
  if (run == 1 || admitted rows) && (run == 1 || sourcePermission) then
    let raw := (cleanRoot sourceValue).bind sinkForward
    let published := if run == 1 then raw.toList
      else raw.toList.filterMap (controlC5 guidance)
    ⟨completion :: published,false,raw.isSome⟩
  else ⟨[],false,false⟩

def backwardRun (rows : List ControlRow) (sinkPermission : Bool) : Capture :=
  if admitted rows && sinkPermission then
    let input := cleanRoot sinkRequirement
    let published := (input.bind sourceBackward).toList.filterMap (controlC5 guidance)
    ⟨completion :: published,input.any sourceMatches,false⟩
  else ⟨[],false,false⟩

def forwardFixed : Capture := ⟨[completion,target],false,true⟩
def backwardFixed : Capture := ⟨[completion,target],true,false⟩

theorem exact_root_is_actually_cleaned :
    cleanRoot (val (ap x [] .exact (some t))) = none := by decide

theorem normal_uniform_source_becomes_demand_without_a_field_cut :
    cleanRoot sourceValue = some cleanedSource ∧
    cleanedSource.ap.tail = .must ∧ cleanedSource.demand = true := by decide

theorem backward_may_survivor_is_unchanged_and_protected :
    cleanRoot sinkRequirement = some cleanedRequirement ∧
    cleanedRequirement.ap.tail = .may ∧ cleanedRequirement.h = true := by decide

theorem a_real_child_of_the_source_is_not_cleaned :
    cleanRoot (val (ap x [f] .exact (some t))) =
      some {val (ap x [f] .exact (some t)) with h := true} := by decide

theorem source_support_and_sink_support_really_join_to_demand :
    (cleanRoot sourceValue).bind sinkForward = some target ∧
    (cleanRoot sinkRequirement).bind sourceBackward = some target := by decide

theorem no_limit_can_refine_these_zero_length_facts (limit : Nat) :
    cut limit sourceValue = sourceValue ∧
    cut limit cleanedSource = cleanedSource ∧
    cut limit sinkRequirement = sinkRequirement ∧
    cut limit cleanedRequirement = cleanedRequirement := by
  simp [cut,sourceValue,cleanedSource,sinkRequirement,cleanedRequirement,val,ap]

theorem the_flow_complement_cannot_supply_the_cleaned_mark :
    marksMeet {ap x [] .star with mx := [t]} (ap x [] .may (some t)) = false ∧
    marksOK {ap x [] .star with mx := [t]} (ap x [] .must (some t)) = false := by decide

theorem no_normal_uniform_ne_rule_can_remove_the_cleaner_survivor (normal : Edge) :
    uniformCovers normal (ap x [] .must (some t),cleanedSource) = false := by
  exact protected_ne_is_never_removed normal _ rfl

theorem even_unprotected_concrete_must_is_outside_the_new_ne_rule (normal : Edge) :
    uniformCovers normal (ap x [] .must (some t),{cleanedSource with h := false}) = false := by
  simp [uniformCovers,sourceValue,cleanedSource,val,ap]

theorem raw_target_passes_paired_control_c5 :
    controlC5 guidance target = some target ∧
    handoff [completion,target] = [guidance] := by decide

theorem run1_computes_its_target_instead_of_assuming_one :
    forwardRun 1 [] false = forwardFixed := by decide

theorem backward_recomputes_source_permission_and_the_same_target :
    backwardRun (handoff forwardFixed.summaries) forwardFixed.sinkPermission = backwardFixed := by decide

theorem missing_source_or_sink_permission_is_not_invented :
    forwardRun 3 [guidance] false = ⟨[],false,false⟩ ∧
    backwardRun [guidance] false = ⟨[],false,false⟩ ∧
    backwardRun [] true = ⟨[],false,false⟩ := by decide

theorem later_forward_run_recomputes_its_target (n : Nat) :
    forwardRun (n+3) (handoff backwardFixed.summaries)
      backwardFixed.sourcePermission = forwardFixed := by
  have later : (n+3 == 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have impossible := Nat.eq_of_beq_eq_true h
    omega
  unfold forwardRun
  rw [later]
  rfl

def forwardHandoffs : Nat → Capture
  | 0 => forwardRun 1 [] false
  | n+1 =>
      let before := forwardHandoffs n
      let backward := backwardRun (handoff before.summaries) before.sinkPermission
      forwardRun (2*n+3) (handoff backward.summaries) backward.sourcePermission

theorem every_forward_handoff_repeats_the_nonempty_target (n : Nat) :
    forwardHandoffs n = forwardFixed := by
  induction n with
  | zero => exact run1_computes_its_target_instead_of_assuming_one
  | succ n ih =>
    simp only [forwardHandoffs,ih,backward_recomputes_source_permission_and_the_same_target]
    exact later_forward_run_recomputes_its_target (2*n)

theorem every_backward_handoff_also_repeats_the_target (n : Nat) :
    backwardRun (handoff (forwardHandoffs n).summaries)
      (forwardHandoffs n).sinkPermission = backwardFixed := by
  rw [every_forward_handoff_repeats_the_nonempty_target]
  exact backward_recomputes_source_permission_and_the_same_target

theorem outgoing_forward_demand_is_never_empty (n : Nat) :
    handoff (forwardHandoffs n).summaries = [guidance] := by
  rw [every_forward_handoff_repeats_the_nonempty_target]
  decide

theorem outgoing_backward_demand_is_never_empty (n : Nat) :
    handoff (backwardRun (handoff (forwardHandoffs n).summaries)
      (forwardHandoffs n).sinkPermission).summaries = [guidance] := by
  rw [every_backward_handoff_also_repeats_the_target]
  decide

theorem the_required_run3_run5_repetition_is_literal :
    handoff (forwardHandoffs 1).summaries = handoff (forwardHandoffs 2).summaries ∧
    handoff (forwardHandoffs 2).summaries = [guidance] := by decide

theorem per_run_summary_domain_is_finite_but_no_normal_target_exists (n : Nat) :
    (forwardHandoffs n).summaries.length = 2 ∧
    ((forwardHandoffs n).summaries.filter fun e =>
      e.conclusion == .target && !e.demand) = [] := by
  rw [every_forward_handoff_repeats_the_nonempty_target]
  decide

end UniformRootCleanerCycle

#print axioms UniformRootCleanerCycle.exact_root_is_actually_cleaned
#print axioms UniformRootCleanerCycle.normal_uniform_source_becomes_demand_without_a_field_cut
#print axioms UniformRootCleanerCycle.backward_may_survivor_is_unchanged_and_protected
#print axioms UniformRootCleanerCycle.a_real_child_of_the_source_is_not_cleaned
#print axioms UniformRootCleanerCycle.source_support_and_sink_support_really_join_to_demand
#print axioms UniformRootCleanerCycle.no_limit_can_refine_these_zero_length_facts
#print axioms UniformRootCleanerCycle.the_flow_complement_cannot_supply_the_cleaned_mark
#print axioms UniformRootCleanerCycle.no_normal_uniform_ne_rule_can_remove_the_cleaner_survivor
#print axioms UniformRootCleanerCycle.even_unprotected_concrete_must_is_outside_the_new_ne_rule
#print axioms UniformRootCleanerCycle.raw_target_passes_paired_control_c5
#print axioms UniformRootCleanerCycle.run1_computes_its_target_instead_of_assuming_one
#print axioms UniformRootCleanerCycle.backward_recomputes_source_permission_and_the_same_target
#print axioms UniformRootCleanerCycle.missing_source_or_sink_permission_is_not_invented
#print axioms UniformRootCleanerCycle.later_forward_run_recomputes_its_target
#print axioms UniformRootCleanerCycle.every_forward_handoff_repeats_the_nonempty_target
#print axioms UniformRootCleanerCycle.every_backward_handoff_also_repeats_the_target
#print axioms UniformRootCleanerCycle.outgoing_forward_demand_is_never_empty
#print axioms UniformRootCleanerCycle.outgoing_backward_demand_is_never_empty
#print axioms UniformRootCleanerCycle.the_required_run3_run5_repetition_is_literal
#print axioms UniformRootCleanerCycle.per_run_summary_domain_is_finite_but_no_normal_target_exists
