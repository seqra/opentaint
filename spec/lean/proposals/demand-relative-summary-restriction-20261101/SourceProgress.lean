import Restriction

/-!
A finite producer/consumer trace with no unrestricted NORMAL cache:

  factory: configured source assigns T at ret.a.b.c.$
  root:    value = factory(); sinkT(value.a.b.c)

The model isolates the producer boundary after a real ZERO route has been
admitted. The supplied initial guide is ret.[any]/T. The global body limit is
3. A complete Target/ZERO control route is assumed present at each round, as
specified in Controls. The sink supplies the exact source path. C2 exposes its
first new field under the MAY guide and starts the concrete STAR key on DEMAND.
The actual backward source transfer, not mere admission,
must match the marked code location before it records the source action ID.
This is a finite executable witness, not all sources, all C2 cells, or the JVM.
-/
namespace RelativeRestriction.SourceProgress
set_option autoImplicit false

def fullSource : Scalar :=
  ⟨⟨1, [.field 1, .field 2, .field 3], .exact, 7⟩, .normal, false⟩
def rootGuide : Pattern := ⟨1, [], .may, 7⟩

/-- Already completed real source action ID; neither an AP nor a synthetic hit. -/
def sourceId : Nat := 42

/-- The real reverse action is checked against the source's declared output.
No match means no action permission. STAR is a correlated query whose result
stays DEMAND; it is not evidence of uniform actual taint. -/
def reverseSource (need : Scalar) : List Nat :=
  if need.base == fullSource.base && need.mark == fullSource.mark then
    match need.tail with
    | .exact => if need.path == fullSource.path then [sourceId] else []
    | .may | .star => if need.path.IsPrefix fullSource.path then [sourceId] else []
    | .must => []
  else []

/-- ZERO is already admitted via the complete control pair. Source permission
enables the real action; an absent permission does not create a payload. -/
def forwardSource (hits : List Nat) (guide : Pattern) : Option Scalar :=
  if sourceId ∈ hits then
    (restrictExit fullSource guide).map (limit (pairBudget 3 guide))
  else none

def nativeCandidate (value : Scalar) : Option Scalar :=
  match value.layer with | .normal => some value | .demand => none

def firstForward : Scalar := limit (pairBudget 3 rootGuide) fullSource

/-- Concrete instantiation of the unchanged first-new-field C2 cell. The actual
sink seed is fullSource's exact path, not the cut forward publication. -/
def backwardActual : Scalar := fullSource
def firstBackwardInitial : Scalar :=
  ⟨⟨1, clip (depth firstForward.path + 1) backwardActual.path, .star, 7⟩, .demand, false⟩
def backwardContext : Context := ⟨3, false, false⟩
def firstHits : List Nat := reverseSource firstBackwardInitial
def secondForward : Option Scalar := forwardSource firstHits firstBackwardInitial.toPattern

theorem first_cut_has_demand_no_native_and_no_hidden_full_payload :
    firstForward.path = [.field 1] ∧ firstForward.tail = .may ∧
    firstForward.layer = .demand ∧ nativeCandidate firstForward = none := by decide

theorem first_complete_exit_selects_the_source_before_cut :
    restrictExit fullSource rootGuide = some fullSource ∧
    forwardSource [42] rootGuide = some firstForward := by decide

theorem actual_reverse_action_recovers_the_real_source_id :
    firstHits = [42] := by decide

theorem backward_initial_is_in_the_unchanged_c2_image :
    entryImage backwardContext firstForward.toPattern firstBackwardInitial.toPattern = true ∧
    firstBackwardInitial.path = [.field 1, .field 2] ∧
    firstBackwardInitial.tail = .star ∧ firstBackwardInitial.layer = .demand := by decide

theorem permission_restores_the_precise_normal_producer :
    secondForward = some fullSource ∧ nativeCandidate fullSource = some fullSource := by decide

theorem no_source_permission_emits_no_fact (guide : Pattern) :
    forwardSource [] guide = none := rfl

theorem unrelated_mark_or_field_cannot_create_a_source_hit :
    reverseSource {firstBackwardInitial with mark := 8} = [] ∧
    reverseSource {firstBackwardInitial with path := [.field 99]} = [] := by decide

theorem permission_does_not_bypass_the_data_exit_gate :
    forwardSource [42] {rootGuide with mark := 8} = none ∧
    forwardSource [42] {rootGuide with path := [.field 99]} = none := by decide

/-- Report production requires the now-exact NORMAL source-to-sink witness. -/
def report (value : Scalar) : Option Nat :=
  if value.base == fullSource.base && value.layer == .normal && value.tail == .exact &&
      value.path == fullSource.path && value.mark == fullSource.mark then some 9 else none

theorem provisional_rounds_do_not_report :
    report firstForward = none ∧ report firstBackwardInitial = none := by decide

theorem precise_admitted_round_reports :
    secondForward.bind report = some 9 := by decide

end RelativeRestriction.SourceProgress
