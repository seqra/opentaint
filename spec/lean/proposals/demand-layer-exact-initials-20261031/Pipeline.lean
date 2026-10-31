import C2C5Image
import AdmissionStore
import TargetLayers

/- Finite code-under-analysis model:
   make(p,q): if CM(p,T1) AND CM(q,T2), assign U to return.
   main: a=sourceT1(); b=sourceT2(); good=make(a,b); tmp.g=good;
         out.f=tmp; bad=make(a,clean); sinkU(out.f.g); sinkU(bad).
   F1 uses weak unary DEMAND arms; B2 executes the real reverse action;
   F3 retains the complete ND dependency and binds it per call. This is
   finding coverage through F3, not a proof of a global stop at F3. -/
namespace ExactDemand.Pipeline
open ExactDemand NDProjection
set_option autoImplicit false

structure Call where
  t1 : Bool
  t2 : Bool
  deriving DecidableEq, Repr

def goodCall : Call := ⟨true,true⟩
def badCall : Call := ⟨true,false⟩
def otherBadCall : Call := ⟨false,true⟩

def fullNDApplicable (call : Call) : Bool := call.t1 && call.t2

def hasOrigin (call : Call) : Origin → Bool
  | .zero => true | .input 0 => call.t1 | .input 1 => call.t2 | .input _ => false

def run1SourceArms : List Arm := project [1,2] NDProjection.Controls.both

def run1Effects (call : Call) : List Layer :=
  run1SourceArms.filterMap fun arm => if hasOrigin call arm.origin then some arm.layer else none

def run1Targets (call : Call) (sinkId : Nat) : List Target :=
  (run1Effects call).map (sinkTarget sinkId)

theorem both_callers_have_only_provisional_run1_targets :
    run1Targets goodCall 10 = [.demand,.demand] ∧
    run1Targets badCall 11 = [.demand] := ⟨rfl,rfl⟩

def retDemand : Demand := ⟨⟨2,[],.exact,.concrete 3,[]⟩,.demand⟩
/-- Physical backward sink seeds start with the existing NORMAL policy.
The good sink's two-field chain is cut at limit1; bad has no field cut. -/
def backwardSinkSeed (cut : Bool) : Actual :=
  if cut then ⟨⟨2,[],.may,.concrete 3,[]⟩,.demand⟩
  else ⟨⟨2,[],.exact,.concrete 3,[]⟩,.normal⟩
def cutReturn : Actual := backwardSinkSeed true

def backwardInitial : Option Seed := emitExact 1 retDemand cutReturn
def badBackwardInitial : Option Seed := emitExact 1 retDemand (backwardSinkSeed false)

/-- The old directed-MAY rejection has no reverse action opportunity. -/
def oldBackwardInitial : Option Seed := none

def argDemand (slot mark : Nat) : Demand := ⟨⟨slot,[],.exact,.concrete mark,[]⟩,.demand⟩
def markedActual (slot mark : Nat) : Actual := ⟨⟨slot,[],.exact,.concrete mark,[]⟩,.normal⟩

structure ReverseResult where
  requirements : List (Pattern × Layer)
  permissions : List Nat
  deriving DecidableEq, Repr

/-- This is the actual reverse source-rule invocation after C2 admitted
    the return. It checks the declared U return premise and emits both CM
    prerequisites. Merely admitting an unrelated initial creates no hit. -/
def executeReverseSource (seed : Seed) : ReverseResult :=
  if seed.initial == exactKey retDemand.pattern then
    ⟨[((argDemand 0 1).pattern,seed.layer),((argDemand 1 2).pattern,seed.layer)],
      sourcePermissions (.acceptedReverseAction 31)⟩
  else ⟨[],[]⟩

def backwardResult : ReverseResult :=
  match backwardInitial with | none => ⟨[],[]⟩ | some seed => executeReverseSource seed

def badBackwardResult : ReverseResult :=
  match badBackwardInitial with | none => ⟨[],[]⟩ | some seed => executeReverseSource seed

/-- Binding is per call: arg0 maps to sourceA; arg1 maps to sourceB in
    the good call, but to a clean new object in the bad call. Accepted
    reverse GEN callbacks record only the matching real source action. -/
def reverseRootSources (binding : Call) (result : ReverseResult) : List Nat :=
  result.requirements.flatMap fun requirement =>
    if requirement.1 == (argDemand 0 1).pattern && binding.t1 then
      sourcePermissions (.acceptedReverseAction 41)
    else if requirement.1 == (argDemand 1 2).pattern && binding.t2 then
      sourcePermissions (.acceptedReverseAction 42)
    else []

def permissionsFrom (good bad : ReverseResult) : List Nat :=
  good.permissions ++ bad.permissions ++
    reverseRootSources goodCall good ++ reverseRootSources badCall bad

def backwardPermissions : List Nat := permissionsFrom backwardResult badBackwardResult

def oldBackwardPermissions : List Nat := permissionsFrom ⟨[],[]⟩ badBackwardResult

def run3Permission : Bool := 31 ∈ backwardPermissions

theorem backward_sink_seed_lanes_are_independent_of_forward_arm_layer :
    backwardInitial = some ⟨exactKey retDemand.pattern,.demand⟩ ∧
    badBackwardInitial = some ⟨exactKey retDemand.pattern,.normal⟩ := ⟨rfl,rfl⟩

theorem backward_may_runs_exact_demand_and_actual_reverse_action :
    backwardResult.requirements =
      [((argDemand 0 1).pattern,.demand),((argDemand 1 2).pattern,.demand)] ∧
    badBackwardResult.requirements =
      [((argDemand 0 1).pattern,.normal),((argDemand 1 2).pattern,.normal)] ∧
    backwardPermissions = [31,31,41,42,41] := ⟨rfl,rfl,rfl⟩

theorem only_new_good_route_recovers_source_b_permission :
    oldBackwardPermissions = [31,41] ∧
    (42 ∈ oldBackwardPermissions) = False ∧
    (42 ∈ backwardPermissions) := ⟨rfl, by decide, by decide⟩

theorem old_rejection_has_no_good_action_opportunity : oldBackwardInitial = none := rfl

theorem unrelated_initial_does_not_create_source_action_permission :
    (executeReverseSource ⟨.zero,.demand⟩).permissions = [] := rfl

/-- The forward root may generate a/b only under the source-action seeds.
    Current caller bindings still decide whether each result is passed to make. -/
def sourcePermission (permissions : List Nat) (mark : Nat) : Bool :=
  if mark == 1 then 41 ∈ permissions else if mark == 2 then 42 ∈ permissions else false

def currentRequirements : List Pattern :=
  (backwardResult.requirements ++ badBackwardResult.requirements).map Prod.fst

/-- Exact current evidence discharges prior guideD. Permissions enable
    rule execution, and do not create marks on a clean bound argument. -/
def admitRun3ArgWith (permissions : List Nat) (present : Bool) (slot mark : Nat) : Option Seed :=
  if present && sourcePermission permissions mark && (argDemand slot mark).pattern ∈ currentRequirements then
    emitExact 2 (argDemand slot mark) (markedActual slot mark)
  else none

def admitRun3Arg (present : Bool) (slot mark : Nat) : Option Seed :=
  admitRun3ArgWith backwardPermissions present slot mark

def run3Arg0 : Option Seed := admitRun3Arg true 0 1
def run3Arg1 : Option Seed := admitRun3Arg true 1 2

theorem run3_exact_inputs_discharge_old_guide_layer :
    run3Arg0 = some ⟨exactKey (argDemand 0 1).pattern,.normal⟩ ∧
    run3Arg1 = some ⟨exactKey (argDemand 1 2).pattern,.normal⟩ := ⟨rfl,rfl⟩

/-- Each call binds its own complete two-input premise. Method-global
    initial availability does not fill a missing caller slot. -/
def run3Inputs (call : Call) : Option Layer :=
  match admitRun3Arg call.t1 0 1, admitRun3Arg call.t2 1 2 with
  | some first, some second => some (join first.layer second.layer)
  | _, _ => none

/-- Later FULL runs keep full ND, not the run-1 unary approximation. -/
def run3Effect (permission : Bool) (call : Call) : Option Layer :=
  if permission then run3Inputs call else none

theorem full_current_binding_is_per_call (permission : Bool) (call : Call) :
    run3Effect permission call =
      if permission && fullNDApplicable call then some .normal else none := by
  cases call with
  | mk first second => cases permission <;> cases first <;> cases second <;> rfl

def run3OldInputs (call : Call) : Option Layer :=
  match admitRun3ArgWith oldBackwardPermissions call.t1 0 1,
        admitRun3ArgWith oldBackwardPermissions call.t2 1 2 with
  | some first, some second => some (join first.layer second.layer)
  | _, _ => none

theorem old_c2_loss_prevents_the_real_two_input_source :
    run3OldInputs goodCall = none ∧
    sourcePermission oldBackwardPermissions 1 = true ∧
    sourcePermission oldBackwardPermissions 2 = false := ⟨rfl,rfl,rfl⟩

def run3Target (permission : Bool) (call : Call) (id : Nat) : Option Target :=
  (run3Effect permission call).map (sinkTarget id)

def run3Report (permission : Bool) (call : Call) (id : Nat) : Option Nat :=
  (run3Target permission call id).bind (report true)

theorem good_report_is_normal_by_run3_and_bad_is_absent :
    run3Target run3Permission goodCall 10 = some (.normal 10) ∧
    run3Report run3Permission goodCall 10 = some 10 ∧
    run3Target run3Permission badCall 11 = none ∧
    run3Report run3Permission badCall 11 = none := ⟨rfl,rfl,rfl,rfl⟩

theorem no_permission_does_not_invent_the_source :
    run3Report false goodCall 10 = none := rfl

theorem different_call_contexts_cannot_fill_each_others_slots :
    fullNDApplicable badCall = false ∧ fullNDApplicable otherBadCall = false ∧
    run3Report true badCall 11 = none ∧ run3Report true otherBadCall 12 = none :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- Separate ND sink: check(p,q) { sink(CM(p,T1) AND CM(q,T2)); }.
   Opposite single-input callers must remain negative. -/
def run3NDSink (call : Call) (id : Nat) : Option Nat :=
  (run3Inputs call).bind fun layer => report true (sinkTarget id layer)

theorem nd_sink_good_and_crossed_bad_callers :
    projectedSinkTargets 42 [1,2] NDProjection.Controls.both =
      [(.input 0,.demand),(.input 1,.demand)] ∧
    physicalSinkSeed [1,2] = [1,2] ∧
    run3NDSink goodCall 42 = some 42 ∧
    run3NDSink badCall 42 = none ∧ run3NDSink otherBadCall 42 = none :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

end ExactDemand.Pipeline
