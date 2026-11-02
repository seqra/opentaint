import Std

/-!
PROVISIONAL INTERFACE MODEL. The boundary-span contract is selected.
No runtime adapter is selected or verified by this file.

This finite model uses an actual NORMAL entry GEN relation and an ordinary
NORMAL before-region FLOW relation. It models their genuine pre-rule/post-rule
interfaces, composition, native forward replay and native reverse ZERO discharge.
It does not execute a new boundary evaluator or create a source-hit permission.

Scope: one concrete mark, finite named/element fields, exclusion-free NORMAL
source-MUST and FLOW records, unary composition. The full AP/MUST residue,
conditional/ND rules, Kotlin storage and general convergence are not verified.
The DEMAND extension checks guidance transport, the existing same-prefix MAY
C2 cell, group-to-full mark binding in one finite group and complete Target C5.
It does not prove the actual deep-source transfer or whole GROUP-mode coverage.
The symmetric suffix laws assume a genuine eligible suffix row exists. They
do not construct run-1 scoped Target ownership, the missing paired guidance
interface or recursive ancestor-boundary coverage. A root completion snapshot
alone is not a verified complete adapter.
-/
namespace EntryPrefixNativeRecords
set_option autoImplicit false

inductive Base where
  | zero | request | cookies | param
  deriving DecidableEq, Repr
inductive Mark where
  | zero | t | u | flow | group
  deriving DecidableEq, Repr
inductive Tail where
  | exact | star | must | may
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr
inductive Field where
  | element | value
  deriving DecidableEq, Repr
inductive Boundary where
  | preEntry | postEntry | prefixExit | afterLoop | normalExit | unrelated
  deriving DecidableEq, Repr
inductive Kind where
  | gen | flow
  deriving DecidableEq, Repr

structure Fact where
  base : Base
  path : List Field
  mark : Mark
  tail : Tail
  deriving DecidableEq, Repr
structure Packet where
  fact : Fact
  layer : Layer
  protection : Bool
  deriving DecidableEq, Repr
structure Input where
  point : Boundary
  original : Nat
  packet : Packet
  deriving DecidableEq, Repr
structure Span where
  entry : Boundary
  exit : Boundary
  deriving DecidableEq, Repr
structure Relation where
  span : Span
  kind : Kind
  premise : Fact
  conclusion : Fact
  layer : Layer
  deriving DecidableEq, Repr
inductive Outcome where
  | data (next : Input)
  | demandTarget (point : Boundary) (original : Nat)
  deriving DecidableEq, Repr
structure Replay where
  result : Outcome
  sourceHits : List Nat
  deriving DecidableEq, Repr

private def zeroFact : Fact :=
  { base := .zero, path := [], mark := .zero, tail := .exact }
private def requestMust : Fact :=
  { base := .request, path := [], mark := .t, tail := .must }
private def flow (base : Base) (path : List Field := []) : Fact :=
  { base := base, path := path, mark := .flow, tail := .star }

def entrySource : Relation :=
  { span := { entry := .preEntry, exit := .postEntry }, kind := .gen,
    premise := zeroFact, conclusion := requestMust, layer := .normal }
def beforePass : Relation :=
  { span := { entry := .postEntry, exit := .prefixExit }, kind := .flow,
    premise := flow .request, conclusion := flow .cookies, layer := .normal }

def persistable (r : Relation) : Bool :=
  decide (r.layer = .normal) && match r.kind with
  | .gen => decide (r.premise = zeroFact ∧ r.conclusion.base ≠ .zero ∧
                    r.conclusion.mark ≠ .flow ∧ r.conclusion.mark ≠ .zero)
  | .flow => decide (r.premise.mark = .flow ∧ r.premise.tail = .star ∧
                     r.conclusion.mark = .flow ∧ r.conclusion.tail = .star)

private def mergedLayer (a b : Layer) : Layer :=
  if a = .demand ∨ b = .demand then .demand else .normal

/-- Existing prefix/suffix transfer for this finite FLOW slice. A uniform input
also covers a field read below its own path. No uniform taint is inferred from
an exact ancestor. -/
def flowImage (src dst : Fact) (input : Packet) : Option Packet :=
  if input.fact.base ≠ src.base then none
  else if src.path.isPrefixOf input.fact.path then
    some { input with fact := { input.fact with base := dst.base, path := dst.path ++ input.fact.path.drop src.path.length } }
  else if input.fact.tail = .must ∧ input.fact.path.isPrefixOf src.path then
    some { input with fact := { input.fact with base := dst.base, path := dst.path } }
  else none

def sourceCovers (source actual : Fact) : Bool :=
  decide (source.base = actual.base ∧ source.mark = actual.mark) &&
    match source.tail with
    | .must => source.path.isPrefixOf actual.path
    | .exact => decide (source.path = actual.path ∧ actual.tail = .exact)
    | .star | .may => false

/-- Native replay uses only the stored NORMAL relation and the actually reached
input interface. It records no live source event. -/
def replayForward (r : Relation) (input : Input) : Option Replay :=
  if !persistable r || input.point ≠ r.span.entry then none
  else match r.kind with
  | .gen => if input.packet.fact = r.premise then
      some { result := .data { input with point := r.span.exit, packet := { fact := r.conclusion, layer := mergedLayer r.layer input.packet.layer, protection := input.packet.protection } }, sourceHits := [] }
    else none
  | .flow => (flowImage r.premise r.conclusion input.packet).map fun packet =>
      { result := .data { input with point := r.span.exit, packet := { packet with layer := mergedLayer r.layer packet.layer } }, sourceHits := [] }

def replayBackward (r : Relation) (input : Input) : Option Replay :=
  if !persistable r || input.point ≠ r.span.exit then none
  else match r.kind with
  | .gen => if sourceCovers r.conclusion input.packet.fact then
      some { result := .demandTarget r.span.entry input.original, sourceHits := [] }
    else none
  | .flow => (flowImage r.conclusion r.premise input.packet).map fun packet =>
      { result := .data { input with point := r.span.entry, packet := { packet with layer := mergedLayer r.layer packet.layer } }, sourceHits := [] }

/-- Build this prefix only from a NORMAL entry relation and a connected NORMAL
before-region relation. The entry's genuine pre-rule premise is retained. -/
def composePrefix (entry before : Relation) : Option Relation :=
  if !persistable entry || !persistable before || entry.kind ≠ .gen || before.kind ≠ .flow ||
      entry.span.exit ≠ before.span.entry then none
  else (flowImage before.premise before.conclusion
    { fact := entry.conclusion, layer := entry.layer, protection := false }).map fun packet =>
    { span := { entry := entry.span.entry, exit := before.span.exit }, kind := .gen,
      premise := entry.premise, conclusion := packet.fact,
      layer := mergedLayer packet.layer before.layer }

def prefixRecord : Relation :=
  { span := { entry := .preEntry, exit := .prefixExit }, kind := .gen,
    premise := zeroFact,
    conclusion := { base := .cookies, path := [], mark := .t, tail := .must },
    layer := .normal }

def rootZero : Input :=
  { point := .preEntry, original := 0,
    packet := { fact := zeroFact, layer := .normal, protection := false } }

def cookieAt (path : List Field) : Input :=
  { point := .prefixExit, original := 0,
    packet := { fact := { base := .cookies, path := path, mark := .t, tail := .exact },
                layer := .normal, protection := false } }

def sequentialBackward (input : Input) : Option Replay :=
  match replayBackward beforePass input with
  | some { result := .data request, .. } => replayBackward entrySource request
  | _ => none

def sequentialForward (input : Input) : Option Replay :=
  match replayForward entrySource input with
  | some { result := .data request, .. } => replayForward beforePass request
  | _ => none

theorem entry_and_before_are_native_NORMAL :
    persistable entrySource = true ∧ persistable beforePass = true := by decide

theorem true_prefix_composes_the_entry_source :
    composePrefix entrySource beforePass = some prefixRecord := by decide

theorem composition_keeps_the_true_pre_rule_premise_and_ports :
    prefixRecord.premise = zeroFact ∧ prefixRecord.span.entry = .preEntry ∧
    prefixRecord.span.exit = .prefixExit ∧ prefixRecord.layer = .normal := by decide

theorem backward_array_uses_existing_native_ZERO_discharge :
    replayBackward prefixRecord (cookieAt [.element]) =
      some { result := .demandTarget .preEntry 0, sourceHits := [] } := by decide

theorem ordinary_field_has_the_same_native_discharge :
    replayBackward prefixRecord (cookieAt [.value]) =
      some { result := .demandTarget .preEntry 0, sourceHits := [] } := by decide

theorem backward_composed_and_two_segment_replay_agree_for_array :
    replayBackward prefixRecord (cookieAt [.element]) = sequentialBackward (cookieAt [.element]) := by decide

theorem backward_composed_and_two_segment_replay_agree_for_named_field :
    replayBackward prefixRecord (cookieAt [.value]) = sequentialBackward (cookieAt [.value]) := by decide

theorem backward_composition_preserves_every_exact_field_suffix (path : List Field) :
    replayBackward prefixRecord (cookieAt path) = sequentialBackward (cookieAt path) := by
  rfl

theorem native_prefix_discharge_preserves_the_waiting_original
    (path : List Field) (original : Nat) :
    replayBackward prefixRecord { cookieAt path with original := original } =
      some { result := .demandTarget .preEntry original, sourceHits := [] } := by
  rfl

theorem forward_prefix_replay_is_the_actual_two_segment_transfer :
    replayForward prefixRecord rootZero = sequentialForward rootZero := by decide

theorem cached_NORMAL_source_needs_no_new_source_hit :
    replayForward prefixRecord rootZero = some {
      result := .data { point := .prefixExit, original := 0, packet := { fact := { base := .cookies, path := [], mark := .t, tail := .must }, layer := .normal, protection := false } }, sourceHits := [] } := by decide

/-- Merely relabelling the after-rule BL span does not insert the GEN premise. -/
def relabelledAfterRule : Relation :=
  { beforePass with span := { entry := .preEntry, exit := .prefixExit } }

theorem wrong_post_rule_premise_cannot_replay_on_method_ZERO :
    replayForward relabelledAfterRule rootZero = none ∧
    (replayForward prefixRecord rootZero).isSome = true := by decide

theorem wrong_post_rule_premise_does_not_discharge_the_source :
    replayBackward relabelledAfterRule (cookieAt [.element]) = some {
      result := .data { point := .preEntry, original := 0, packet := { fact := { base := .request, path := [.element], mark := .t, tail := .exact }, layer := .normal, protection := false } }, sourceHits := [] } := by decide

theorem disconnected_control_interfaces_do_not_compose :
    composePrefix entrySource { beforePass with span := { beforePass.span with entry := .unrelated } } = none := by decide

theorem prefix_replay_does_not_alias_an_unrelated_entry :
    replayForward prefixRecord { rootZero with point := .unrelated } = none := by decide

theorem prefix_reverse_does_not_alias_an_unrelated_exit :
    replayBackward prefixRecord { cookieAt [.element] with point := .unrelated } = none := by decide

def demandEntry : Relation := { entrySource with layer := .demand }

theorem nonNORMAL_entry_cannot_be_persisted_or_promoted :
    persistable demandEntry = false ∧ composePrefix demandEntry beforePass = none ∧
    replayForward demandEntry rootZero = none := by decide

theorem nonNORMAL_prefix_cannot_be_replayed_as_native :
    replayBackward { prefixRecord with layer := .demand } (cookieAt [.element]) = none := by decide

/-- The model exposes only the actual configured GEN result, with its real
input layer. It does not fabricate a source when no earlier producer ran. -/
def actualEntryGEN (configured : Bool) (input : Input) : Option Relation :=
  if configured && input.point = .preEntry && input.packet.fact = zeroFact then
    some { entrySource with layer := input.packet.layer }
  else none

def admittedPrefix (configured : Bool) (input : Input) : Option Relation :=
  (actualEntryGEN configured input).bind fun observed => composePrefix observed beforePass

theorem normal_prefix_has_a_real_configured_entry_derivation :
    admittedPrefix true rootZero = some prefixRecord := by decide

theorem no_actual_entry_source_means_no_source_prefix :
    admittedPrefix false rootZero = none := by decide

theorem demand_actual_entry_is_not_a_NORMAL_source_prefix :
    admittedPrefix true { rootZero with packet := { rootZero.packet with layer := .demand } } = none := by decide

/-- Existing normal-exit entry-mark removal applies to source-origin argument
images. Local cookie images are also not public method summary bases. -/
def wholeMethodArgumentCandidate : Relation :=
  { entrySource with span := { entry := .preEntry, exit := .normalExit } }

def wholeMethodLocalCandidate : Relation :=
  { prefixRecord with span := { entry := .preEntry, exit := .normalExit } }

def exitMarkRemoval (r : Relation) : Option Relation :=
  if r.span.exit = .normalExit ∧ r.premise = zeroFact ∧
      r.conclusion.base = .request ∧ r.conclusion.mark = .t then none
  else some r

def wholeMethodExport (r : Relation) : Option Relation :=
  if r.span.exit ≠ .normalExit then none
  else (exitMarkRemoval r).bind fun kept =>
    if kept.conclusion.base = .cookies ∨ kept.conclusion.base = .param then none
    else some kept

theorem whole_method_exit_removal_does_not_replace_the_entry_segment :
    wholeMethodExport wholeMethodArgumentCandidate = none ∧ persistable entrySource = true := by decide

theorem public_local_base_filter_does_not_replace_the_scoped_prefix :
    wholeMethodExport wholeMethodLocalCandidate = none ∧ persistable prefixRecord = true := by decide

theorem exit_removal_does_not_run_at_the_entry_segment :
    exitMarkRemoval entrySource = some entrySource := by decide

/-- A stored refined NORMAL read. Its inference is outside this interface model. -/
def refinedRead : Relation :=
  { span := { entry := .prefixExit, exit := .afterLoop }, kind := .flow,
    premise := flow .cookies [.element], conclusion := flow .param, layer := .normal }

def replayWithExistingPrefix (_freshSourcePermission : Bool) : Option Replay :=
  match replayForward prefixRecord rootZero with
  | some { result := .data cookies, .. } => replayForward refinedRead cookies
  | _ => none

def normalSinkHit (value : Option Replay) : Bool :=
  match value with
  | some { result := .data data, .. } =>
      decide (data.point = .afterLoop ∧ data.packet.fact.base = .param ∧
              data.packet.fact.mark = .t ∧ data.packet.layer = .normal) &&
        sourceCovers data.packet.fact { base := .param, path := [], mark := .t, tail := .exact }
  | _ => false

theorem cached_prefix_and_refined_read_retain_the_forward_finding :
    normalSinkHit (replayWithExistingPrefix false) = true := by decide

theorem cached_NORMAL_producer_does_not_need_a_fresh_permission :
    replayWithExistingPrefix false = replayWithExistingPrefix true := rfl

theorem cached_prefix_and_read_do_not_synthesize_source_hits :
    (replayWithExistingPrefix false).map Replay.sourceHits = some [] := by decide

theorem demand_input_cannot_be_promoted_to_a_NORMAL_prefix_result :
    replayForward prefixRecord { rootZero with packet := { rootZero.packet with layer := .demand } } = some {
      result := .data { point := .prefixExit, original := 0, packet := { fact := { base := .cookies, path := [], mark := .t, tail := .must }, layer := .demand, protection := false } }, sourceHits := [] } := by decide


/-! DEMAND producer coverage. These definitions model only the already selected
same-prefix concrete MAY C2 cell and one complete paired Target C5 cell.
They do not introduce an ANY-refinement policy or prove a general C2 matcher. -/

/-- Actual summary composition preserves a DEMAND layer. Native persistence is
an independent later filter; it is not a restriction on live block summaries. -/
def summarizeActualPrefix (entry before : Relation) : Option Relation :=
  if entry.kind ≠ .gen || before.kind ≠ .flow || entry.span.exit ≠ before.span.entry then none
  else (flowImage before.premise before.conclusion
    { fact := entry.conclusion, layer := entry.layer, protection := false }).map fun packet =>
    { span := { entry := entry.span.entry, exit := before.span.exit }, kind := .gen,
      premise := entry.premise, conclusion := packet.fact,
      layer := mergedLayer packet.layer before.layer }

def deepRawEntry : Relation :=
  { entrySource with conclusion := { requestMust with path := [.element, .value] } }

def globalFieldOneCut (entry : Relation) : Relation :=
  if entry.conclusion.path.length > 1 then
    { entry with conclusion := { entry.conclusion with path := entry.conclusion.path.take 1, tail := .may }, layer := .demand }
  else entry

def deepBoundedEntry : Relation :=
  { entrySource with conclusion := { requestMust with path := [.element], tail := .may }, layer := .demand }

def deepDemandPrefix : Relation :=
  { prefixRecord with conclusion := { prefixRecord.conclusion with path := [.element], tail := .may }, layer := .demand }

def groupedEntry : Relation :=
  { entrySource with conclusion := { requestMust with mark := .group }, layer := .demand }

def groupedDemandPrefix : Relation :=
  { prefixRecord with conclusion := { prefixRecord.conclusion with mark := .group }, layer := .demand }

theorem deep_entry_uses_the_existing_global_cut_before_storage :
    globalFieldOneCut deepRawEntry = deepBoundedEntry ∧
    deepBoundedEntry.conclusion.path.length = 1 ∧ deepBoundedEntry.layer = .demand := by decide

theorem ordinary_prefix_composition_keeps_deep_entry_DEMAND :
    summarizeActualPrefix deepBoundedEntry beforePass = some deepDemandPrefix := by decide

theorem ordinary_prefix_composition_keeps_grouped_entry_DEMAND :
    summarizeActualPrefix groupedEntry beforePass = some groupedDemandPrefix := by decide

theorem deep_and_grouped_producers_are_not_native_NORMAL_records :
    persistable deepBoundedEntry = false ∧ persistable deepDemandPrefix = false ∧
    persistable groupedEntry = false ∧ persistable groupedDemandPrefix = false := by decide

theorem normal_only_boundary_record_completion_misses_the_DEMAND_prefix :
    composePrefix deepBoundedEntry beforePass = none ∧
    summarizeActualPrefix deepBoundedEntry beforePass = some deepDemandPrefix := by decide

structure DemandPair where
  span : Span
  entry : Fact
  exit : Fact
  deriving DecidableEq, Repr

def guidanceFact (fact : Fact) : Fact :=
  if fact.tail = .must then { fact with tail := .may } else fact

/-- Ordinary selected DEMAND handoff exchanges control endpoints and AP ends. -/
def demandHandoff (r : Relation) : Option DemandPair :=
  if r.layer = .demand then some {
    span := { entry := r.span.exit, exit := r.span.entry },
    entry := guidanceFact r.conclusion, exit := guidanceFact r.premise }
  else none

def markCompatible (required actual : Mark) : Bool :=
  if required = .group then decide (actual = .t ∨ actual = .u)
  else decide (required = actual)

/-- The existing same-prefix MAY/MAY cell, with the current full mark bound
from a group demand where applicable. Initials remain DEMAND. -/
def existingSamePrefixMayC2 (d : DemandPair) (actual : Input) : Option Input :=
  if actual.point = d.span.entry ∧ d.entry.base = actual.packet.fact.base ∧
      d.entry.path = actual.packet.fact.path ∧ d.entry.tail = .may ∧
      actual.packet.fact.tail = .may ∧ markCompatible d.entry.mark actual.packet.fact.mark then
    some { actual with packet := { actual.packet with layer := .demand } }
  else none

/-- One complete paired cell. The same row matches the true original and both
control endpoints; its ZERO exit accepts the anonymous Target. -/
def existingSamePrefixMayTargetC5 (d : DemandPair) (initial : Input) (target : Outcome) : Bool :=
  match target with
  | .data _ => false
  | .demandTarget output original =>
      decide (initial.point = d.span.entry ∧ output = d.span.exit ∧
        original = initial.original ∧ d.entry.base = initial.packet.fact.base ∧
        d.entry.path = initial.packet.fact.path ∧ d.entry.tail = .may ∧
        initial.packet.fact.tail = .may ∧ d.exit = zeroFact) &&
        markCompatible d.entry.mark initial.packet.fact.mark

def deepReversePair : DemandPair :=
  { span := { entry := .prefixExit, exit := .preEntry },
    entry := deepDemandPrefix.conclusion, exit := zeroFact }

def deepCarrier : Input :=
  { point := .prefixExit, original := 1,
    packet := { fact := deepDemandPrefix.conclusion, layer := .demand, protection := false } }

def groupReversePair : DemandPair :=
  { span := { entry := .prefixExit, exit := .preEntry },
    entry := { groupedDemandPrefix.conclusion with tail := .may }, exit := zeroFact }

def fullCarrierForGroup : Input :=
  { point := .prefixExit, original := 2,
    packet := { fact := { base := .cookies, path := [], mark := .t, tail := .may },
                layer := .demand, protection := false } }

theorem deep_prefix_exports_the_actual_bounded_DEMAND_pair :
    demandHandoff deepDemandPrefix = some deepReversePair := by decide

theorem grouped_prefix_exports_group_guidance_without_native_persistence :
    demandHandoff groupedDemandPrefix = some groupReversePair ∧
    persistable groupedDemandPrefix = false := by decide

theorem same_prefix_concrete_MAY_carrier_is_admitted_only_as_DEMAND :
    existingSamePrefixMayC2 deepReversePair deepCarrier = some deepCarrier ∧
    deepCarrier.packet.layer = .demand := by decide

theorem complete_deep_prefix_pair_permits_its_actual_terminal_result :
    existingSamePrefixMayTargetC5 deepReversePair deepCarrier (.demandTarget .preEntry 1) = true := by decide

theorem group_request_binds_the_full_mark_and_keeps_the_DEMAND_layer :
    existingSamePrefixMayC2 groupReversePair fullCarrierForGroup = some fullCarrierForGroup ∧
    fullCarrierForGroup.packet.fact.mark = .t ∧ fullCarrierForGroup.packet.layer = .demand := by decide

theorem grouped_complete_pair_keeps_the_existing_full_mark_terminal :
    existingSamePrefixMayTargetC5 groupReversePair fullCarrierForGroup (.demandTarget .preEntry 2) = true := by decide

theorem wrong_mark_does_not_use_the_deep_prefix_pair :
    existingSamePrefixMayC2 deepReversePair { deepCarrier with packet := {
      deepCarrier.packet with fact := { deepCarrier.packet.fact with mark := .u } } } = none := by decide

theorem wrong_control_entry_does_not_use_the_DEMAND_pair :
    existingSamePrefixMayC2 deepReversePair { deepCarrier with point := .postEntry } = none := by decide

theorem complete_DEMAND_pair_does_not_alias_another_terminal_exit :
    existingSamePrefixMayTargetC5 deepReversePair deepCarrier (.demandTarget .postEntry 1) = false := by decide

theorem NORMAL_prefix_uses_native_records_instead_of_a_fake_DEMAND_row :
    demandHandoff prefixRecord = none ∧ persistable prefixRecord = true := by decide


/-- Existing local Target application substitutes the exact waiting parent
original. This is binding of a proved child result, not a new source emission. -/
def bindChildTarget (expectedChildOriginal parentOriginal : Nat) (target : Outcome) : Option Outcome :=
  match target with
  | .demandTarget point original =>
      if original = expectedChildOriginal then some (.demandTarget point parentOriginal) else none
  | .data _ => none

def fullMethodZeroTargetC5 (target : Outcome) : Bool :=
  match target with
  | .demandTarget point original => decide (point = .preEntry ∧ original = 0)
  | .data _ => false

theorem deep_prefix_terminal_reaches_the_exact_waiting_method_original :
    bindChildTarget 1 0 (.demandTarget .preEntry 1) = some (.demandTarget .preEntry 0) ∧
    fullMethodZeroTargetC5 (.demandTarget .preEntry 0) = true := by decide

theorem another_child_original_cannot_supply_the_waiting_method_Target :
    bindChildTarget 1 0 (.demandTarget .preEntry 2) = none := by decide

theorem parent_binding_does_not_change_the_terminal_port :
    bindChildTarget 1 0 (.demandTarget .postEntry 1) = some (.demandTarget .postEntry 0) ∧
    fullMethodZeroTargetC5 (.demandTarget .postEntry 0) = false := by decide


/-! Symmetric suffix interface. An actual backward ZERO-origin NORMAL row is
selected as guidance by the existing handoff exception. It is not a backward
native record. No new sink evaluator is used by the loop observer. -/

inductive RunDirection where
  | forward | backward
  deriving DecidableEq, Repr

def nativePersistInDirection (direction : RunDirection) (r : Relation) : Bool :=
  persistable r && !(direction = .backward && r.premise = zeroFact)

def selectedSummaryHandoff (direction : RunDirection) (r : Relation) : Option DemandPair :=
  if r.layer = .demand ∨ direction = .backward ∧ r.premise = zeroFact then some {
    span := { entry := r.span.exit, exit := r.span.entry },
    entry := guidanceFact r.conclusion, exit := guidanceFact r.premise }
  else none

def backwardExitSuffix : Relation :=
  { span := { entry := .normalExit, exit := .prefixExit }, kind := .gen,
    premise := zeroFact,
    conclusion := { base := .cookies, path := [.value], mark := .t, tail := .exact },
    layer := .normal }

def forwardSuffixPair : DemandPair :=
  { span := { entry := .prefixExit, exit := .normalExit },
    entry := backwardExitSuffix.conclusion, exit := zeroFact }

def uniformFieldCarrier : Input :=
  { point := .prefixExit, original := 3,
    packet := { fact := { backwardExitSuffix.conclusion with tail := .must },
                layer := .normal, protection := false } }

/-- Existing same-prefix concrete EXACT demand answered by a definite uniform
NORMAL input. The abstract MUST transfer table is not changed. -/
def existingExactFromUniformC2 (d : DemandPair) (actual : Input) : Option Input :=
  if actual.point = d.span.entry ∧ d.entry.base = actual.packet.fact.base ∧
      d.entry.path = actual.packet.fact.path ∧ d.entry.tail = .exact ∧
      actual.packet.fact.tail = .must ∧ markCompatible d.entry.mark actual.packet.fact.mark then
    some { actual with packet := { actual.packet with fact := { actual.packet.fact with tail := .exact } } }
  else none

def suffixRead : Relation :=
  { span := { entry := .prefixExit, exit := .normalExit }, kind := .flow,
    premise := flow .cookies [.value], conclusion := flow .param, layer := .normal }

def actualNormalExitSinkMatch (result : Option Replay) : Bool :=
  match result with
  | some { result := .data out, .. } => decide (
      out.point = .normalExit ∧ out.packet.fact.base = .param ∧
      out.packet.fact.mark = .t ∧ out.packet.fact.path = [] ∧
      out.packet.fact.tail = .exact ∧ out.packet.layer = .normal)
  | _ => false

def ordinarySuffixFinding (carrier : Input) : Bool :=
  match existingExactFromUniformC2 forwardSuffixPair carrier with
  | some admitted => actualNormalExitSinkMatch (replayForward suffixRead admitted)
  | none => false

theorem backward_ZERO_NORMAL_suffix_is_not_a_native_record :
    nativePersistInDirection .backward backwardExitSuffix = false := by decide

theorem backward_ZERO_NORMAL_suffix_uses_existing_handoff_guidance :
    selectedSummaryHandoff .backward backwardExitSuffix = some forwardSuffixPair := by decide

theorem normal_forward_prefix_still_uses_native_persistence :
    nativePersistInDirection .forward prefixRecord = true ∧
    selectedSummaryHandoff .forward prefixRecord = none := by decide

theorem suffix_C2_admits_the_definite_uniform_field_at_NORMAL :
    existingExactFromUniformC2 forwardSuffixPair uniformFieldCarrier = some {
      uniformFieldCarrier with packet := { uniformFieldCarrier.packet with
        fact := { uniformFieldCarrier.packet.fact with tail := .exact } } } := by decide

theorem ordinary_exit_inclusive_suffix_reaches_the_actual_NORMAL_sink :
    ordinarySuffixFinding uniformFieldCarrier = true := by decide

theorem DEMAND_carrier_cannot_create_a_NORMAL_exit_finding :
    ordinarySuffixFinding { uniformFieldCarrier with
      packet := { uniformFieldCarrier.packet with layer := .demand } } = false := by decide

theorem suffix_C2_does_not_alias_a_wrong_control_interface :
    existingExactFromUniformC2 forwardSuffixPair { uniformFieldCarrier with point := .postEntry } = none := by decide

theorem existing_backward_ZERO_exception_does_not_select_an_ordinary_NORMAL_flow_row :
    selectedSummaryHandoff .backward beforePass = none := by decide

end EntryPrefixNativeRecords

/- Per-module axiom audit; the package checker audits these declarations too. -/
#print axioms EntryPrefixNativeRecords.entrySource
#print axioms EntryPrefixNativeRecords.beforePass
#print axioms EntryPrefixNativeRecords.persistable
#print axioms EntryPrefixNativeRecords.flowImage
#print axioms EntryPrefixNativeRecords.sourceCovers
#print axioms EntryPrefixNativeRecords.replayForward
#print axioms EntryPrefixNativeRecords.replayBackward
#print axioms EntryPrefixNativeRecords.composePrefix
#print axioms EntryPrefixNativeRecords.prefixRecord
#print axioms EntryPrefixNativeRecords.rootZero
#print axioms EntryPrefixNativeRecords.cookieAt
#print axioms EntryPrefixNativeRecords.sequentialBackward
#print axioms EntryPrefixNativeRecords.sequentialForward
#print axioms EntryPrefixNativeRecords.entry_and_before_are_native_NORMAL
#print axioms EntryPrefixNativeRecords.true_prefix_composes_the_entry_source
#print axioms EntryPrefixNativeRecords.composition_keeps_the_true_pre_rule_premise_and_ports
#print axioms EntryPrefixNativeRecords.backward_array_uses_existing_native_ZERO_discharge
#print axioms EntryPrefixNativeRecords.ordinary_field_has_the_same_native_discharge
#print axioms EntryPrefixNativeRecords.backward_composed_and_two_segment_replay_agree_for_array
#print axioms EntryPrefixNativeRecords.backward_composed_and_two_segment_replay_agree_for_named_field
#print axioms EntryPrefixNativeRecords.backward_composition_preserves_every_exact_field_suffix
#print axioms EntryPrefixNativeRecords.native_prefix_discharge_preserves_the_waiting_original
#print axioms EntryPrefixNativeRecords.forward_prefix_replay_is_the_actual_two_segment_transfer
#print axioms EntryPrefixNativeRecords.cached_NORMAL_source_needs_no_new_source_hit
#print axioms EntryPrefixNativeRecords.relabelledAfterRule
#print axioms EntryPrefixNativeRecords.wrong_post_rule_premise_cannot_replay_on_method_ZERO
#print axioms EntryPrefixNativeRecords.wrong_post_rule_premise_does_not_discharge_the_source
#print axioms EntryPrefixNativeRecords.disconnected_control_interfaces_do_not_compose
#print axioms EntryPrefixNativeRecords.prefix_replay_does_not_alias_an_unrelated_entry
#print axioms EntryPrefixNativeRecords.prefix_reverse_does_not_alias_an_unrelated_exit
#print axioms EntryPrefixNativeRecords.demandEntry
#print axioms EntryPrefixNativeRecords.nonNORMAL_entry_cannot_be_persisted_or_promoted
#print axioms EntryPrefixNativeRecords.nonNORMAL_prefix_cannot_be_replayed_as_native
#print axioms EntryPrefixNativeRecords.actualEntryGEN
#print axioms EntryPrefixNativeRecords.admittedPrefix
#print axioms EntryPrefixNativeRecords.normal_prefix_has_a_real_configured_entry_derivation
#print axioms EntryPrefixNativeRecords.no_actual_entry_source_means_no_source_prefix
#print axioms EntryPrefixNativeRecords.demand_actual_entry_is_not_a_NORMAL_source_prefix
#print axioms EntryPrefixNativeRecords.wholeMethodArgumentCandidate
#print axioms EntryPrefixNativeRecords.wholeMethodLocalCandidate
#print axioms EntryPrefixNativeRecords.exitMarkRemoval
#print axioms EntryPrefixNativeRecords.wholeMethodExport
#print axioms EntryPrefixNativeRecords.whole_method_exit_removal_does_not_replace_the_entry_segment
#print axioms EntryPrefixNativeRecords.public_local_base_filter_does_not_replace_the_scoped_prefix
#print axioms EntryPrefixNativeRecords.exit_removal_does_not_run_at_the_entry_segment
#print axioms EntryPrefixNativeRecords.refinedRead
#print axioms EntryPrefixNativeRecords.replayWithExistingPrefix
#print axioms EntryPrefixNativeRecords.normalSinkHit
#print axioms EntryPrefixNativeRecords.cached_prefix_and_refined_read_retain_the_forward_finding
#print axioms EntryPrefixNativeRecords.cached_NORMAL_producer_does_not_need_a_fresh_permission
#print axioms EntryPrefixNativeRecords.cached_prefix_and_read_do_not_synthesize_source_hits
#print axioms EntryPrefixNativeRecords.demand_input_cannot_be_promoted_to_a_NORMAL_prefix_result
#print axioms EntryPrefixNativeRecords.summarizeActualPrefix
#print axioms EntryPrefixNativeRecords.deepRawEntry
#print axioms EntryPrefixNativeRecords.globalFieldOneCut
#print axioms EntryPrefixNativeRecords.deepBoundedEntry
#print axioms EntryPrefixNativeRecords.deepDemandPrefix
#print axioms EntryPrefixNativeRecords.groupedEntry
#print axioms EntryPrefixNativeRecords.groupedDemandPrefix
#print axioms EntryPrefixNativeRecords.deep_entry_uses_the_existing_global_cut_before_storage
#print axioms EntryPrefixNativeRecords.ordinary_prefix_composition_keeps_deep_entry_DEMAND
#print axioms EntryPrefixNativeRecords.ordinary_prefix_composition_keeps_grouped_entry_DEMAND
#print axioms EntryPrefixNativeRecords.deep_and_grouped_producers_are_not_native_NORMAL_records
#print axioms EntryPrefixNativeRecords.normal_only_boundary_record_completion_misses_the_DEMAND_prefix
#print axioms EntryPrefixNativeRecords.guidanceFact
#print axioms EntryPrefixNativeRecords.demandHandoff
#print axioms EntryPrefixNativeRecords.markCompatible
#print axioms EntryPrefixNativeRecords.existingSamePrefixMayC2
#print axioms EntryPrefixNativeRecords.existingSamePrefixMayTargetC5
#print axioms EntryPrefixNativeRecords.deepReversePair
#print axioms EntryPrefixNativeRecords.deepCarrier
#print axioms EntryPrefixNativeRecords.groupReversePair
#print axioms EntryPrefixNativeRecords.fullCarrierForGroup
#print axioms EntryPrefixNativeRecords.deep_prefix_exports_the_actual_bounded_DEMAND_pair
#print axioms EntryPrefixNativeRecords.grouped_prefix_exports_group_guidance_without_native_persistence
#print axioms EntryPrefixNativeRecords.same_prefix_concrete_MAY_carrier_is_admitted_only_as_DEMAND
#print axioms EntryPrefixNativeRecords.complete_deep_prefix_pair_permits_its_actual_terminal_result
#print axioms EntryPrefixNativeRecords.group_request_binds_the_full_mark_and_keeps_the_DEMAND_layer
#print axioms EntryPrefixNativeRecords.grouped_complete_pair_keeps_the_existing_full_mark_terminal
#print axioms EntryPrefixNativeRecords.wrong_mark_does_not_use_the_deep_prefix_pair
#print axioms EntryPrefixNativeRecords.wrong_control_entry_does_not_use_the_DEMAND_pair
#print axioms EntryPrefixNativeRecords.complete_DEMAND_pair_does_not_alias_another_terminal_exit
#print axioms EntryPrefixNativeRecords.NORMAL_prefix_uses_native_records_instead_of_a_fake_DEMAND_row
#print axioms EntryPrefixNativeRecords.bindChildTarget
#print axioms EntryPrefixNativeRecords.fullMethodZeroTargetC5
#print axioms EntryPrefixNativeRecords.deep_prefix_terminal_reaches_the_exact_waiting_method_original
#print axioms EntryPrefixNativeRecords.another_child_original_cannot_supply_the_waiting_method_Target
#print axioms EntryPrefixNativeRecords.parent_binding_does_not_change_the_terminal_port
#print axioms EntryPrefixNativeRecords.nativePersistInDirection
#print axioms EntryPrefixNativeRecords.selectedSummaryHandoff
#print axioms EntryPrefixNativeRecords.backwardExitSuffix
#print axioms EntryPrefixNativeRecords.forwardSuffixPair
#print axioms EntryPrefixNativeRecords.uniformFieldCarrier
#print axioms EntryPrefixNativeRecords.existingExactFromUniformC2
#print axioms EntryPrefixNativeRecords.suffixRead
#print axioms EntryPrefixNativeRecords.actualNormalExitSinkMatch
#print axioms EntryPrefixNativeRecords.ordinarySuffixFinding
#print axioms EntryPrefixNativeRecords.backward_ZERO_NORMAL_suffix_is_not_a_native_record
#print axioms EntryPrefixNativeRecords.backward_ZERO_NORMAL_suffix_uses_existing_handoff_guidance
#print axioms EntryPrefixNativeRecords.normal_forward_prefix_still_uses_native_persistence
#print axioms EntryPrefixNativeRecords.suffix_C2_admits_the_definite_uniform_field_at_NORMAL
#print axioms EntryPrefixNativeRecords.ordinary_exit_inclusive_suffix_reaches_the_actual_NORMAL_sink
#print axioms EntryPrefixNativeRecords.DEMAND_carrier_cannot_create_a_NORMAL_exit_finding
#print axioms EntryPrefixNativeRecords.suffix_C2_does_not_alias_a_wrong_control_interface
#print axioms EntryPrefixNativeRecords.existing_backward_ZERO_exception_does_not_select_an_ordinary_NORMAL_flow_row
