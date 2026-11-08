/-
PREPARED only. Finite E21 whole-query experiment plus an arbitrary-length
nongrowing saved-read chain. This is not a native adapter/driver proof.

Inputs are the recorded final paired incoming scopes. Completion is computed
from those final rows, never historical erased rows. NORMAL read support is
derived below by C2, identity start, an ordinary field read and paired C5;
it is not supplied as an expected saved record. Typed Target publication
permission and arrival of the next run's final rows remain separate gates.
-/
import RelativeAdmission
import AnnotatedC5Exit
import FlowDemandCompletion

namespace DeepFlowCompletion
open PlainStarRelativeAdmission
open ApSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

abbrev Interface := FlowDemandCompletion.Interface
abbrev DemandRow := FlowDemandCompletion.Row

def x : Nat := 0
def f : Nat := 0
def T : ScalarMark := .full 1
def p (path : List Nat) (tail : Tail) (mark : ScalarMark := T) : Pattern :=
  ⟨x,path,tail,mark,[]⟩
def actual (path : List Nat) (tail : Tail) (layer : Layer) (mark : ScalarMark := T) : Actual :=
  ⟨p path tail mark,layer,false⟩
def atDepth (n : Nat) : Actual := actual (List.replicate n f) .exact .normal
def f3 : Mode := ⟨3,2,.forward⟩
def b4 : Mode := ⟨4,2,.backward⟩
def f5 : Mode := ⟨5,4,.forward⟩

def cutAt (budget : Nat) (input : Actual) : Actual :=
  if input.pattern.path.length ≤ budget then input
  else ⟨⟨input.pattern.base,input.pattern.path.take budget,.any,input.pattern.mark,[]⟩,
    .demand,input.hasProtection⟩

/- The read subdomain needed here has a known nonempty field head. It keeps
the actual tail, mark, layer and H. Root-STAR/MAY reads are not modeled. -/
def readKnownHead (field : Nat) (input : Actual) : Option Actual :=
  match input.pattern.path with
  | [] => none
  | head :: rest => if head = field then
      some {input with pattern := {input.pattern with path := rest}} else none

def reverseRead (field : Nat) (input : Actual) : Actual :=
  {input with pattern := {input.pattern with path := field :: input.pattern.path}}

def sourceFFFF : Actual := atDepth 4
def sourceR3 : Option Actual := readKnownHead f (cutAt 2 sourceFFFF)
def sourceR5 : Option Actual := readKnownHead f (cutAt 4 sourceFFFF)
def rawF5 : Actual := atDepth 3

theorem source_read_has_real_R3_MAY_support :
    sourceR3 = some (actual [f] .any .demand) := by decide

theorem source_read_has_real_R5_exact_NORMAL_support : sourceR5 = some rawF5 := by decide

/- Provisional EXACT support and Target typing remain unchanged. An ordinary
local base x=0 is distinct from the typed ZERO original below. -/
inductive Original where | zero | data (initial : Pattern)
deriving DecidableEq, Repr
inductive TargetKind where | normalReport | demandTarget
deriving DecidableEq, Repr
structure TargetResult where
  original : Original
  kind : TargetKind
deriving DecidableEq, Repr

def exactSink (original : Original) (input : Actual) : Option TargetResult :=
  if input.pattern = p [] .exact T then
    some ⟨original,if input.layer = .normal then .normalReport else .demandTarget⟩
  else none

def f3ProvisionalTarget : Option TargetResult := do
  let incoming ← sourceR3
  let seed ← emit f3 ⟨x,[f],.exact,T,[]⟩ incoming
  let output ← readKnownHead f (start seed)
  exactSink (.data seed.initial) output

theorem F3_exact_on_MAY_keeps_exact_Target_original_and_DEMAND :
    f3ProvisionalTarget = some ⟨.data (p [f] .exact T),.demandTarget⟩ := by decide

theorem F3_provisional_Target_is_not_a_NORMAL_report :
    f3ProvisionalTarget ≠ some ⟨.data (p [f] .exact T),.normalReport⟩ := by decide

/- Method/context 17 is an opaque model label. Native port/block numbers are
retained: repeat entry 5, DATA control exit 11, terminal handoff entry -1.
ZERO below is a typed selector, never ordinary base x=0. -/
def repeatPort5 : Interface := ⟨17,true,2,5,5⟩
def dataPort11 : Interface := ⟨17,true,2,5,11⟩
def targetPort : Interface := ⟨17,true,2,-1,5⟩

def fp (fields : List Nat) (tail : FlowDemandCompletion.Tail)
    (mark : FlowDemandCompletion.Mark := .full 1) : FlowDemandCompletion.Pattern :=
  ⟨.local x,fields.map RelativeRestriction.Accessor.field,tail,mark,[]⟩

def finalData : DemandRow := ⟨dataPort11,.data (fp [f] .exact),.zero⟩
def finalZero : DemandRow := ⟨repeatPort5,.zero,.data (fp [f,f] .star)⟩
def finalTarget : DemandRow := ⟨targetPort,.target,.data (fp [f,f] .star)⟩
def finalRows : List DemandRow := [finalData,finalZero,finalTarget]
def completedRows : List DemandRow := FlowDemandCompletion.completed finalRows

def natPath : RelativeRestriction.Path → Option (List Nat)
  | [] => some []
  | .field field :: rest => (natPath rest).map (List.cons field)
  | _ => none

def scalarBase : FlowDemandCompletion.Base → Option Nat
  | .local id => some id
  | .staticRoot => none
def scalarMark : FlowDemandCompletion.Mark → Option ScalarMark
  | .flow => some .flow
  | .full id => some (.full id)
  | .group _ => none
def scalarTail : FlowDemandCompletion.Tail → Tail
  | .exact => .exact
  | .star => .star
  | .may => .any
  | .must => .must

def scalarPattern (value : FlowDemandCompletion.Pattern) : Option Pattern := do
  let base ← scalarBase value.base
  let path ← natPath value.path
  let mark ← scalarMark value.mark
  let excluded ← natPath value.exclusion
  pure ⟨base,path,scalarTail value.tail,mark,excluded⟩

def scalarDemand (value : Pattern) : Option Demand :=
  match value.tail with
  | .exact => some ⟨value.base,value.path,.exact,value.mark,value.exclusion⟩
  | .star => some ⟨value.base,value.path,.star,value.mark,value.exclusion⟩
  | .any => some ⟨value.base,value.path,.any,value.mark,value.exclusion⟩
  | .must => none

structure ViewScope where
  methodContext : Nat
  direction : Bool
  block : Nat
  entryPort : Int
deriving DecidableEq, Repr

def viewOf (interface : Interface) : ViewScope :=
  ⟨interface.methodContext,interface.direction,interface.scope,interface.entryPort⟩

structure Key where
  view : ViewScope
  seed : Seed
deriving DecidableEq, Repr

/- C2 unions all paired exits at one entry. Its observation key does not
invent an output-port label. C5 still uses each row's complete paired exit. -/
def rowKey (mode : Mode) (row : DemandRow) (input : Actual) : Option Key :=
  match row.entry with
  | .zero | .target => none
  | .data selector => do
      let pattern ← scalarPattern selector
      let demand ← scalarDemand pattern
      let seed ← emit mode demand input
      pure ⟨viewOf row.interface,seed⟩

def query (mode : Mode) (view : ViewScope) (rows : List DemandRow) (input : Actual) : List Key :=
  rows.filterMap fun row =>
    if viewOf row.interface = view then rowKey mode row input else none

def repeatView : ViewScope := viewOf repeatPort5
def repeatQuery (input : Actual) : List Key := query f5 repeatView completedRows input
def fineKey : Key := ⟨repeatView,⟨p [f,f,f] .star .flow,.normal⟩⟩

theorem all_three_final_rows_are_kept_literally :
    finalData ∈ completedRows ∧ finalZero ∈ completedRows ∧ finalTarget ∈ completedRows := by decide

theorem Target_row_keeps_its_own_entry_not_repeat5 :
    finalTarget.interface.entryPort = -1 ∧ finalZero.interface.entryPort = 5 := ⟨rfl,rfl⟩

theorem completed_whole_input_has_eleven_rows : completedRows.length = 11 := by decide

theorem original_whole_repeat_query_is_empty_for_raw_and_cut :
    query f5 repeatView finalRows rawF5 = [] ∧
    query f5 repeatView finalRows (cutAt 2 rawF5) = [] := by decide

theorem completed_whole_query_has_fine_raw_key : fineKey ∈ repeatQuery rawF5 := by decide

theorem completed_whole_depth_two_query_has_no_fine_key :
    fineKey ∉ repeatQuery (cutAt 2 rawF5) := by decide

theorem completed_whole_depth_one_query_has_no_fine_key :
    fineKey ∉ repeatQuery (cutAt 1 rawF5) := by decide

structure Observation (Adjacent Enclosing : Type) where
  adjacent : Adjacent
  enclosing : Enclosing
  repeatKeys : List Key

def wholeObserve {Adjacent Enclosing : Type}
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) (input : Actual) :
    Observation Adjacent Enclosing := ⟨adjacent input,enclosing input,repeatQuery input⟩

theorem depth_two_cut_changes_every_full_observation {Adjacent Enclosing : Type}
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) :
    wholeObserve adjacent enclosing rawF5 ≠ wholeObserve adjacent enclosing (cutAt 2 rawF5) := by
  intro same
  have keys := congrArg (fun view : Observation Adjacent Enclosing => view.repeatKeys) same
  change repeatQuery rawF5 = repeatQuery (cutAt 2 rawF5) at keys
  exact completed_whole_depth_two_query_has_no_fine_key
    (keys ▸ completed_whole_query_has_fine_raw_key)

theorem depth_one_cut_changes_every_full_observation {Adjacent Enclosing : Type}
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) :
    wholeObserve adjacent enclosing rawF5 ≠ wholeObserve adjacent enclosing (cutAt 1 rawF5) := by
  intro same
  have keys := congrArg (fun view : Observation Adjacent Enclosing => view.repeatKeys) same
  change repeatQuery rawF5 = repeatQuery (cutAt 1 rawF5) at keys
  exact completed_whole_depth_one_query_has_no_fine_key
    (keys ▸ completed_whole_query_has_fine_raw_key)

theorem depth_three_trial_is_raw_identity : cutAt 3 rawF5 = rawF5 := by decide

theorem depth_three_keeps_every_full_observation {Adjacent Enclosing : Type}
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) :
    wholeObserve adjacent enclosing (cutAt 3 rawF5) = wholeObserve adjacent enclosing rawF5 := by
  rw [depth_three_trial_is_raw_identity]

theorem all_proper_scalar_trials_reject {Adjacent Enclosing : Type}
    (adjacent : Actual → Adjacent) (enclosing : Actual → Enclosing) (budget : Nat)
    (trial : budget ∈ [1,2]) :
    wholeObserve adjacent enclosing rawF5 ≠ wholeObserve adjacent enclosing (cutAt budget rawF5) := by
  have casesOfBudget : budget = 1 ∨ budget = 2 := by simpa using trial
  rcases casesOfBudget with one | two
  · subst budget; exact depth_one_cut_changes_every_full_observation adjacent enclosing
  · subst budget; exact depth_two_cut_changes_every_full_observation adjacent enclosing

/- Provider construction. A recorded final F3 ZERO->xf.STAR endpoint produces
the complete FLOW/ANY self pair at xf. We find that pair in completion, then
run actual source-supported C2, identity start, field read and paired C5. -/
def f3FinalZero : DemandRow := ⟨repeatPort5,.zero,.data (fp [f] .star)⟩
def providerPair : DemandRow := FlowDemandCompletion.selfPair repeatPort5 (fp [f] .star)
  [RelativeRestriction.Accessor.field f]
def providerView : List DemandRow := FlowDemandCompletion.completed [f3FinalZero]

theorem provider_pair_is_generated_from_final_F3_row : providerPair ∈ providerView := by decide

def asExitPattern (value : Pattern) : AnnotatedC5Exit.Pattern :=
  ⟨value.base,value.path.map RelativeRestriction.Accessor.field,
    match value.tail with | .exact => .exact | .star => .star | .any => .may | .must => .must,
    match value.mark with | .flow => .flow [] | .full mark => .full mark,
    value.exclusion.map RelativeRestriction.Accessor.field⟩
def asExitFact (value : Actual) : AnnotatedC5Exit.Fact :=
  ⟨asExitPattern value.pattern,
    match value.layer with | .normal => .normal | .demand => .demand,value.hasProtection⟩

structure SavedRead where
  interface : Interface
  initial : Pattern
  output : Actual
deriving DecidableEq, Repr

def inferShrinker : Option SavedRead := do
  let row ← providerView.find? (fun candidate => decide (candidate = providerPair))
  let entry ← match row.entry with | .data selector => scalarPattern selector | _ => none
  let demand ← scalarDemand entry
  let incoming ← sourceR3
  let seed ← emit f3 demand incoming
  let output ← readKnownHead f (start seed)
  let exit ← match row.exit with | .data selector => scalarPattern selector | _ => none
  if canStoreInitial f3 demand seed.initial &&
      decide (AnnotatedC5Exit.restrictData true 2 (asExitFact output) (asExitPattern exit) =
        some (asExitFact output)) then
    pure ⟨row.interface,publicInitial seed.initial,output⟩
  else none

def derivedShrinker : SavedRead :=
  ⟨repeatPort5,p [f] .star .flow,⟨p [] .star .flow,.normal,false⟩⟩

theorem ordinary_body_C2_and_paired_C5_derive_NORMAL_shrinker :
    inferShrinker = some derivedShrinker := by decide

theorem concrete_selector_does_not_accept_the_FLOW_provider :
    canStoreInitial f3 ⟨x,[f],.any,T,[]⟩ (p [f] .star .flow) = false := by decide

theorem concrete_source_support_is_NOT_promoted_to_NORMAL :
    sourceR3 = some (actual [f] .any .demand) ∧
    (derivedShrinker.output.layer = .normal) ∧ derivedShrinker.initial.mark = .flow := by decide

/- Apply a correlated ordinary STAR FLOW relation to the actual suffix.
This is the same explicit-head read subdomain as the provider body. -/
def applySaved (row : SavedRead) (input : Actual) : Option Actual :=
  if row.interface = repeatPort5 ∧ row.initial.base = input.pattern.base ∧
      row.initial.tail = .star ∧ row.initial.mark = .flow ∧ row.output.pattern.tail = .star then
    match dropPrefix row.initial.path input.pattern.path with
    | none => none
    | some suffix => some ⟨⟨row.output.pattern.base,row.output.pattern.path ++ suffix,
        input.pattern.tail,input.pattern.mark,input.pattern.exclusion⟩,
        joinLayer row.output.layer input.layer,row.output.hasProtection || input.hasProtection⟩
  else none

def replayOne (input : Actual) : Option Actual :=
  inferShrinker.bind fun row => applySaved row input

theorem derived_saved_read_shrinks_one_actual_field (n : Nat) :
    replayOne (atDepth (n+1)) = some (atDepth n) := by
  rw [replayOne,ordinary_body_C2_and_paired_C5_derive_NORMAL_shrinker]
  simp [Option.bind_some,applySaved,derivedShrinker,atDepth,actual,p,x,f,
    List.replicate_succ,dropPrefix,joinLayer]

theorem applying_NORMAL_FLOW_shrinker_to_MAY_keeps_DEMAND :
    replayOne (actual [f] .any .demand) = some (actual [] .any .demand) := by decide

def replay : Nat → Actual → Option Actual
  | 0, input => some input
  | steps+1, input => (replayOne input).bind (replay steps)

theorem finite_saved_read_chain_reaches_root_NORMAL (n : Nat) :
    replay n (atDepth n) = some (atDepth 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replay,derived_saved_read_shrinks_one_actual_field,Option.bind_some]
    exact ih

theorem exact_four_source_then_three_saved_reads_reaches_NORMAL_root :
    sourceR5.bind (replay 3) = some (actual [] .exact .normal) := by decide

def sinkNORMAL (input : Actual) : Bool :=
  decide (input.pattern = p [] .exact T ∧ input.layer = .normal)

theorem finite_source_read_chain_has_a_NORMAL_sink :
    ((sourceR5.bind (replay 3)).map sinkNORMAL) = some true := by decide

theorem exact_four_chain_preserves_ZERO_source_origin_at_NORMAL_sink :
    (sourceR5.bind (replay 3)).bind (exactSink .zero) =
      some ⟨.zero,.normalReport⟩ := by decide

/- B4 structural checks. These prove selected admission and ordinary reverse
field transport, not Target publication/physical delivery. The supplied
concrete ANY selector is in the captured B4 control-demand view. -/
def b4Demand : Demand := ⟨x,[f],.any,T,[]⟩
def b4Incoming : Actual := actual [f] .any .demand
def b4First : Seed := ⟨p [f] .star T,.demand⟩
def b4Growing : Actual := reverseRead f (start b4First)
def b4Next : Seed := ⟨p [f,f] .star T,.demand⟩

theorem B4_incoming_has_the_recorded_F3_source_support : sourceR3 = some b4Incoming := by decide

theorem B4_first_admission_is_plain_STAR_DEMAND : emit b4 b4Demand b4Incoming = some b4First := by decide

theorem B4_identity_reverse_read_grows_to_ff_STAR_DEMAND :
    b4Growing = actual [f,f] .star .demand := by decide

theorem B4_growing_STAR_has_legal_C2_reentry : emit b4 b4Demand b4Growing = some b4Next := by decide

theorem B4_growing_key_is_in_shared_image_and_not_ANY :
    rawImage b4 b4Demand b4Next.initial = true ∧ b4Next.initial.tail ≠ .any ∧
      publicInitial b4Next.initial = b4Next.initial := by decide

theorem B4_growing_key_contains_the_physical_four_field_source :
    dropPrefix b4Next.initial.path sourceFFFF.pattern.path = some [f,f] ∧
      tailAdmits b4Next.initial.tail b4Next.initial.exclusion [f,f] = true := by decide

def reverseInterface (interface : Interface) : Interface :=
  ⟨interface.methodContext,!interface.direction,interface.scope,interface.outputPort,interface.entryPort⟩

theorem captured_B4_Target_pair_reverses_to_its_own_F5_ports :
    reverseInterface ⟨17,false,2,5,-1⟩ = targetPort := by decide

theorem captured_B4_repeat_pair_reverses_to_repeat5 :
    reverseInterface ⟨17,false,2,5,5⟩ = repeatPort5 := by decide

theorem generated_completion_never_changes_interface (source result : DemandRow)
    (member : result ∈ FlowDemandCompletion.additions source) :
    result.interface = source.interface :=
  FlowDemandCompletion.all_additions_keep_exact_interface source result member

end DeepFlowCompletion

#print axioms DeepFlowCompletion.source_read_has_real_R3_MAY_support
#print axioms DeepFlowCompletion.source_read_has_real_R5_exact_NORMAL_support
#print axioms DeepFlowCompletion.F3_exact_on_MAY_keeps_exact_Target_original_and_DEMAND
#print axioms DeepFlowCompletion.F3_provisional_Target_is_not_a_NORMAL_report
#print axioms DeepFlowCompletion.all_three_final_rows_are_kept_literally
#print axioms DeepFlowCompletion.Target_row_keeps_its_own_entry_not_repeat5
#print axioms DeepFlowCompletion.completed_whole_input_has_eleven_rows
#print axioms DeepFlowCompletion.original_whole_repeat_query_is_empty_for_raw_and_cut
#print axioms DeepFlowCompletion.completed_whole_query_has_fine_raw_key
#print axioms DeepFlowCompletion.completed_whole_depth_two_query_has_no_fine_key
#print axioms DeepFlowCompletion.completed_whole_depth_one_query_has_no_fine_key
#print axioms DeepFlowCompletion.depth_two_cut_changes_every_full_observation
#print axioms DeepFlowCompletion.depth_one_cut_changes_every_full_observation
#print axioms DeepFlowCompletion.depth_three_trial_is_raw_identity
#print axioms DeepFlowCompletion.depth_three_keeps_every_full_observation
#print axioms DeepFlowCompletion.all_proper_scalar_trials_reject
#print axioms DeepFlowCompletion.provider_pair_is_generated_from_final_F3_row
#print axioms DeepFlowCompletion.ordinary_body_C2_and_paired_C5_derive_NORMAL_shrinker
#print axioms DeepFlowCompletion.concrete_selector_does_not_accept_the_FLOW_provider
#print axioms DeepFlowCompletion.concrete_source_support_is_NOT_promoted_to_NORMAL
#print axioms DeepFlowCompletion.derived_saved_read_shrinks_one_actual_field
#print axioms DeepFlowCompletion.applying_NORMAL_FLOW_shrinker_to_MAY_keeps_DEMAND
#print axioms DeepFlowCompletion.finite_saved_read_chain_reaches_root_NORMAL
#print axioms DeepFlowCompletion.exact_four_source_then_three_saved_reads_reaches_NORMAL_root
#print axioms DeepFlowCompletion.finite_source_read_chain_has_a_NORMAL_sink
#print axioms DeepFlowCompletion.exact_four_chain_preserves_ZERO_source_origin_at_NORMAL_sink
#print axioms DeepFlowCompletion.B4_incoming_has_the_recorded_F3_source_support
#print axioms DeepFlowCompletion.B4_first_admission_is_plain_STAR_DEMAND
#print axioms DeepFlowCompletion.B4_identity_reverse_read_grows_to_ff_STAR_DEMAND
#print axioms DeepFlowCompletion.B4_growing_STAR_has_legal_C2_reentry
#print axioms DeepFlowCompletion.B4_growing_key_is_in_shared_image_and_not_ANY
#print axioms DeepFlowCompletion.B4_growing_key_contains_the_physical_four_field_source
#print axioms DeepFlowCompletion.captured_B4_Target_pair_reverses_to_its_own_F5_ports
#print axioms DeepFlowCompletion.captured_B4_repeat_pair_reverses_to_repeat5
#print axioms DeepFlowCompletion.generated_completion_never_changes_interface
