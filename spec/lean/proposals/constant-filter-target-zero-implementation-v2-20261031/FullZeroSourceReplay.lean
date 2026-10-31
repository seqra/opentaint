import SelectedCore

/-!
Historical first FULL ZERO-origin layer correction, 2026-10-31.
The later selected FULL computed-layer override is FullComputedLayer.force.
Nonzero-only demotion theorems below describe the superseded narrow policy.
ZERO-native and bounded-cleanup kernels are reused through the checked
compatibility theorem; this module does not select current nonzero demotion.

This kernel models the layer override after ordinary AP transfer has computed
its payload and layer. It does not recompute field transfer, exclusions or
matching. Only FULL taint with a ZERO origin and a nonstatic conclusion is
released from the old unconditional DEMAND override. All nonzero FULL taint,
GROUP taint, and static-dependent packets keep the old override.

The native read kernel below is limited to a NORMAL ZERO -> exact ordinary
full-mark record, the same method/base/path/mark on a backward exact/MAY
input, and a forward ZERO input. Existing native matching is an adapter;
this kernel does not change C2 or prove every AP/native geometry case.
-/
namespace FullZeroSourceReplay
open SelectedCore
set_option autoImplicit false

inductive Mode where | full | group deriving DecidableEq, Repr
inductive Kind where | flow | fullTaint | groupTaint deriving DecidableEq, Repr
inductive Origin where | zero | ordinary | static deriving DecidableEq, Repr
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr

structure SourceKey where
  method : Nat
  base : Nat
  path : List Nat
  mark : Nat
  deriving DecidableEq, Repr

structure Packet where
  key : SourceKey
  tail : Tail
  kind : Kind
  origin : Origin
  staticConclusion : Bool
  layer : Layer
  deriving DecidableEq, Repr

def staticDependent (p : Packet) : Bool := p.staticConclusion || p.origin == .static

def oldDemote (p : Packet) : Bool :=
  match p.kind with | .flow => staticDependent p | _ => true

/-- The permitted new cell is ZERO-origin FULL taint at an ordinary result. -/
def releasedCell (p : Packet) : Bool :=
  p.kind == .fullTaint && p.origin == .zero && !p.staticConclusion

def mustDemote (p : Packet) : Bool :=
  match p.kind with
  | .flow => staticDependent p
  | .groupTaint => true
  | .fullTaint => p.origin != .zero || p.staticConclusion

def oldForce (run1 : Bool) (p : Packet) : Packet :=
  if run1 && oldDemote p then { p with layer := .demand } else p

def force (run1 : Bool) (p : Packet) : Packet :=
  if run1 && mustDemote p then { p with layer := .demand } else p

theorem outside_released_cell_unchanged (run1 : Bool) (p : Packet)
    (outside : releasedCell p = false) : force run1 p = oldForce run1 p := by
  cases p with
  | mk key tail kind origin stat layer =>
    cases kind <;> cases origin <;> cases stat <;>
      simp_all [releasedCell, force, oldForce, mustDemote, oldDemote, staticDependent]

theorem later_run_unchanged (p : Packet) : force false p = p := rfl

theorem packet_geometry_and_kind_preserved (run1 : Bool) (p : Packet) :
    (force run1 p).key = p.key ∧ (force run1 p).tail = p.tail ∧
      (force run1 p).kind = p.kind ∧ (force run1 p).origin = p.origin ∧
      (force run1 p).staticConclusion = p.staticConclusion := by
  unfold force
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem raw_demand_never_promoted (run1 : Bool) (p : Packet) (raw : p.layer = .demand) :
    (force run1 p).layer = .demand := by
  unfold force
  split
  · rfl
  · exact raw

theorem full_zero_ordinary_keeps_computed_layer (key : SourceKey) (tail : Tail) (layer : Layer) :
    force true ⟨key, tail, .fullTaint, .zero, false, layer⟩ =
      ⟨key, tail, .fullTaint, .zero, false, layer⟩ := rfl

theorem exact_full_zero_normal_stays_normal (key : SourceKey) :
    (force true ⟨key, .exact, .fullTaint, .zero, false, .normal⟩).layer = .normal := rfl

theorem must_full_zero_normal_stays_normal (key : SourceKey) :
    (force true ⟨key, .must, .fullTaint, .zero, false, .normal⟩).layer = .normal := rfl

theorem cut_full_zero_demand_stays_demand (key : SourceKey) (tail : Tail) :
    (force true ⟨key, tail, .fullTaint, .zero, false, .demand⟩).layer = .demand := rfl

theorem group_taint_stays_demand (key : SourceKey) (tail : Tail) (origin : Origin)
    (stat : Bool) (layer : Layer) :
    (force true ⟨key, tail, .groupTaint, origin, stat, layer⟩).layer = .demand := rfl

theorem nonzero_full_taint_stays_demand (key : SourceKey) (tail : Tail) (origin : Origin)
    (stat : Bool) (layer : Layer) (nonzero : origin ≠ .zero) :
    (force true ⟨key, tail, .fullTaint, origin, stat, layer⟩).layer = .demand := by
  cases origin <;> simp_all [force, mustDemote]

theorem static_conclusion_stays_demand (key : SourceKey) (tail : Tail) (kind : Kind)
    (origin : Origin) (layer : Layer) :
    (force true ⟨key, tail, kind, origin, true, layer⟩).layer = .demand := by
  cases kind <;> simp [force, mustDemote, staticDependent]

theorem static_origin_stays_demand (key : SourceKey) (tail : Tail) (kind : Kind)
    (stat : Bool) (layer : Layer) :
    (force true ⟨key, tail, kind, .static, stat, layer⟩).layer = .demand := by
  cases kind <;> simp [force, mustDemote, staticDependent]

theorem ordinary_flow_keeps_computed_layer (key : SourceKey) (tail : Tail) (layer : Layer) :
    force true ⟨key, tail, .flow, .ordinary, false, layer⟩ =
      ⟨key, tail, .flow, .ordinary, false, layer⟩ := rfl

/-- Necessary NORMAL-layer filter only; legal native shape checks stay external. -/
def normalLayerCandidate (packet : Packet) : Option SourceKey :=
  if packet.layer == .normal then some packet.key else none

theorem demand_has_no_normal_candidate (packet : Packet) (demand : packet.layer = .demand) :
    normalLayerCandidate packet = none := by simp [normalLayerCandidate, demand]

theorem nonzero_full_has_no_normal_candidate (key : SourceKey) (tail : Tail) (raw : Layer) :
    normalLayerCandidate (force true ⟨key, tail, .fullTaint, .ordinary, false, raw⟩) = none := rfl

structure SourceRule where
  key : SourceKey
  group : Nat
  deriving DecidableEq, Repr

/-- A fitting ordinary ZERO-origin exact source before the layer override. -/
def sourcePacket (mode : Mode) (rule : SourceRule) (raw : Layer) : Packet :=
  match mode with
  | .full => ⟨rule.key, .exact, .fullTaint, .zero, false, raw⟩
  | .group => ⟨{rule.key with mark := rule.group}, .exact, .groupTaint, .zero, false, raw⟩

def sourceEmission (mode : Mode) (rule : SourceRule) (raw : Layer) : Packet :=
  force true (sourcePacket mode rule raw)

/-- This specialized native record type represents NORMAL ZERO -> exact key. -/
def persistSource (mode : Mode) (rule : SourceRule) (raw : Layer) : Option SourceKey :=
  normalLayerCandidate (sourceEmission mode rule raw)

theorem exact_full_source_is_persisted (rule : SourceRule) :
    persistSource .full rule .normal = some rule.key := rfl

theorem group_source_is_not_normal_record (rule : SourceRule) (raw : Layer) :
    persistSource .group rule raw = none := rfl

theorem already_demand_source_is_not_normal_record (mode : Mode) (rule : SourceRule) :
    persistSource mode rule .demand = none := by cases mode <;> rfl

theorem full_normal_source_is_not_refinement_demand (rule : SourceRule) (payload : Atom) :
    selectHandoff ordinarySelected .forward
      ⟨rule.key.method, .zero, .ap payload, (sourceEmission .full rule .normal).layer⟩ = [] := rfl

theorem group_source_remains_refinement_demand (rule : SourceRule) (raw : Layer) (payload : Atom) :
    selectHandoff ordinarySelected .forward
      ⟨rule.key.method, .zero, .ap payload, (sourceEmission .group rule raw).layer⟩ =
        [⟨rule.key.method, .ap payload, .zero⟩] := rfl

theorem cut_full_source_remains_refinement_demand (rule : SourceRule) (payload : Atom) :
    selectHandoff ordinarySelected .forward
      ⟨rule.key.method, .zero, .ap payload, (sourceEmission .full rule .demand).layer⟩ =
        [⟨rule.key.method, .ap payload, .zero⟩] := rfl

inductive Input where
  | zero (layer : Layer)
  | exact (key : SourceKey) (layer : Layer)
  | may (key : SourceKey) (layer : Layer)
  deriving DecidableEq, Repr

inductive NativeEffect where
  | zero (layer : Layer)
  | marked (key : SourceKey) (layer : Layer)
  deriving DecidableEq, Repr

/-- Selected native read cases only. A backward MAY read is a DEMAND result. -/
def readNative (direction : Direction) (saved : SourceKey) : Input → Option NativeEffect
  | .zero layer => if direction == .forward then some (.marked saved layer) else none
  | .exact actual layer =>
      if direction == .backward && actual == saved then some (.zero layer) else none
  | .may actual _ =>
      if direction == .backward && actual == saved then some (.zero .demand) else none

/-- C2 exact-data slice: no guide or a MAY actual starts no exact initial. -/
def admitExact (guide : Option SourceKey) (actual : Input) : List SourceKey :=
  match guide, actual with
  | some wanted, .exact supplied _ => if wanted == supplied then [wanted] else []
  | _, _ => []

structure CallResult where
  effects : List NativeEffect
  initials : List SourceKey
  startCurrent : Bool
  deriving DecidableEq, Repr

/-- Saved replay is computed before the unchanged current-demand gate. -/
def selectedCall (direction : Direction) (saved : List SourceKey) (guide : Option SourceKey)
    (actual : Input) : CallResult :=
  let effects := saved.filterMap (fun row => readNative direction row actual)
  let initials := admitExact guide actual
  ⟨effects, initials, !initials.isEmpty⟩

theorem exact_c2_still_rejects_may (guide key : SourceKey) (layer : Layer) :
    admitExact (some guide) (.may key layer) = [] := rfl

theorem no_guide_has_no_current_start (direction : Direction) (saved : List SourceKey) (actual : Input) :
    (selectedCall direction saved none actual).initials = [] ∧
      (selectedCall direction saved none actual).startCurrent = false := by
  cases actual <;> exact ⟨rfl, rfl⟩

theorem saved_effects_do_not_depend_on_current_guide (direction : Direction) (saved : List SourceKey)
    (left right : Option SourceKey) (actual : Input) :
    (selectedCall direction saved left actual).effects =
      (selectedCall direction saved right actual).effects := rfl

theorem every_saved_match_is_replayed (direction : Direction) (saved : List SourceKey)
    (guide : Option SourceKey) (actual : Input) (row : SourceKey) (effect : NativeEffect)
    (present : row ∈ saved) (matched : readNative direction row actual = some effect) :
    effect ∈ (selectedCall direction saved guide actual).effects := by
  change effect ∈ saved.filterMap (fun candidate => readNative direction candidate actual)
  exact List.mem_filterMap.mpr ⟨row, present, matched⟩

theorem exact_saved_source_answers_backward_may_without_initial (key : SourceKey) (layer : Layer)
    (guide : Option SourceKey) :
    selectedCall .backward [key] guide (.may key layer) = ⟨[.zero .demand], [], false⟩ := by
  cases guide <;> simp [selectedCall, readNative, admitExact]

theorem exact_saved_source_answers_forward_zero_without_current_guide (key : SourceKey) :
    selectedCall .forward [key] none (.zero .normal) = ⟨[.marked key .normal], [], false⟩ := by
  simp [selectedCall, readNative, admitExact]

theorem demand_caller_is_not_promoted_by_native_source (key : SourceKey) :
    selectedCall .forward [key] none (.zero .demand) = ⟨[.marked key .demand], [], false⟩ := by
  simp [selectedCall, readNative, admitExact]

theorem mismatched_backward_source_not_read (saved actual : SourceKey) (layer : Layer)
    (different : actual ≠ saved) : readNative .backward saved (.may actual layer) = none := by
  simp [readNative, different]

/-- A concrete native route witness, independent of any fresh source execution. -/
def routeWitness (rule : SourceRule) : SourceKey := rule.key

theorem full_exact_source_has_native_route (rule : SourceRule) :
    ∃ saved : SourceKey,
      persistSource .full rule .normal = some saved ∧
      selectedCall .backward [saved] none (.may rule.key .demand) =
        ⟨[.zero .demand], [], false⟩ ∧
      selectedCall .forward [saved] none (.zero .normal) =
        ⟨[.marked rule.key .normal], [], false⟩ := by
  refine ⟨routeWitness rule, rfl, ?_, ?_⟩
  · exact exact_saved_source_answers_backward_may_without_initial _ _ _
  · exact exact_saved_source_answers_forward_zero_without_current_guide _

namespace ExactCleanup

/-- The new header cell is NORMAL, ZERO, all-EXACT, empty-E and nonstatic.
The old FLOW/DEMAND cases are unchanged. Spatial cleaning is separate. -/
def oldFixed (p : Packet) (emptyE : Bool) : Bool :=
  emptyE && (p.kind == .flow || p.layer == .demand) &&
    (!staticDependent p || p.layer == .demand)

def fixed (p : Packet) (emptyE allExact : Bool) : Bool :=
  emptyE && (p.kind == .flow || p.layer == .demand ||
    (p.origin == .zero && allExact)) && (!staticDependent p || p.layer == .demand)

theorem existing_demand_headers_unchanged (p : Packet) (emptyE allExact : Bool)
    (demand : p.layer = .demand) : fixed p emptyE allExact = oldFixed p emptyE := by
  simp [fixed, oldFixed, demand]

theorem extension_only_normal_zero_exact (p : Packet) (emptyE allExact : Bool)
    (accepted : fixed p emptyE allExact = true) (newCell : oldFixed p emptyE = false) :
    p.kind ≠ .flow ∧ p.layer = .normal ∧ p.origin = .zero ∧
      emptyE = true ∧ allExact = true ∧ staticDependent p = false := by
  cases p with
  | mk key tail kind origin stat layer =>
    cases kind <;> cases origin <;> cases stat <;> cases layer <;>
      simp_all [fixed, oldFixed, staticDependent, Bool.and_eq_true]

theorem normal_zero_exact_accepted (key : SourceKey) :
    fixed ⟨key, .exact, .fullTaint, .zero, false, .normal⟩ true true = true := rfl

theorem normal_zero_must_falls_back (key : SourceKey) :
    fixed ⟨key, .must, .fullTaint, .zero, false, .normal⟩ true false = false := rfl

theorem normal_zero_star_falls_back (key : SourceKey) :
    fixed ⟨key, .star, .fullTaint, .zero, false, .normal⟩ true false = false := rfl

/-- Exact leaves never split into partial spatial survivors. Existing protection
is retained; a selected surviving mark gets the same protection upgrade. -/
structure Leaf where
  key : SourceKey
  protection : Bool
  deriving DecidableEq, Repr

def one (baseMatches inside : SourceKey → Bool) (selected : Nat → Bool)
    (leaf : Leaf) : Option Leaf :=
  if baseMatches leaf.key && inside leaf.key && selected leaf.key.mark then none
  else some {leaf with protection := leaf.protection ||
    (baseMatches leaf.key && selected leaf.key.mark)}

def apply (baseMatches inside : SourceKey → Bool) (selected : Nat → Bool)
    (facts : List Leaf) : List Leaf := facts.filterMap (one baseMatches inside selected)

theorem one_composition (baseMatches inside : SourceKey → Bool)
    (first second : Nat → Bool) (leaf : Leaf) :
    (one baseMatches inside first leaf).bind (one baseMatches inside second) =
      one baseMatches inside (fun mark => first mark || second mark) leaf := by
  cases leaf with
  | mk key flag =>
    cases hbase : baseMatches key <;> cases hinside : inside key <;>
      cases hfirst : first key.mark <;> cases hsecond : second key.mark <;>
      cases flag <;> simp [one, hbase, hinside, hfirst, hsecond]

theorem apply_composition (baseMatches inside : SourceKey → Bool)
    (first second : Nat → Bool) (facts : List Leaf) :
    apply baseMatches inside second (apply baseMatches inside first facts) =
      apply baseMatches inside (fun mark => first mark || second mark) facts := by
  simp only [apply, List.filterMap_filterMap, one_composition]

def mask (marks : List Nat) (mark : Nat) : Bool := decide (mark ∈ marks)

def serial (baseMatches inside : SourceKey → Bool) : List Nat → List Leaf → List Leaf
  | [], facts => facts
  | mark :: rest, facts => serial baseMatches inside rest
      (apply baseMatches inside (fun offered => decide (offered = mark)) facts)

def bulk (baseMatches inside : SourceKey → Bool) (marks : List Nat) (facts : List Leaf) : List Leaf :=
  apply baseMatches inside (mask marks) facts

theorem empty_mask_identity (baseMatches inside : SourceKey → Bool) (facts : List Leaf) :
    apply baseMatches inside (mask []) facts = facts := by
  have stable : one baseMatches inside (mask []) = some := by
    funext leaf
    cases leaf with
    | mk key flag => simp [one, mask]
  simp [apply, stable]

theorem serial_bulk_same_leaves_and_protection (baseMatches inside : SourceKey → Bool)
    (marks : List Nat) (facts : List Leaf) :
    serial baseMatches inside marks facts = bulk baseMatches inside marks facts := by
  induction marks generalizing facts with
  | nil => exact (empty_mask_identity baseMatches inside facts).symm
  | cons mark rest ih =>
    simp only [serial, ih, bulk, apply_composition]
    congr 1
    funext offered
    simp [mask, List.mem_cons]

end ExactCleanup

namespace Controls

def sampleRule : SourceRule := ⟨⟨7, 2, [], 11⟩, 5⟩

theorem full_source_stores_reusable_normal_exact :
    persistSource .full sampleRule .normal = some sampleRule.key := rfl

theorem group_source_stays_demand_and_has_no_native_route :
    (sourceEmission .group sampleRule .normal).layer = .demand ∧
      persistSource .group sampleRule .normal = none := ⟨rfl, rfl⟩

def checks : Bool :=
  decide (persistSource .full sampleRule .normal = some sampleRule.key) &&
  decide (persistSource .group sampleRule .normal = none) &&
  decide (selectedCall .backward [sampleRule.key] none (.may sampleRule.key .demand) =
    ⟨[.zero .demand], [], false⟩) &&
  decide (selectedCall .forward [sampleRule.key] none (.zero .normal) =
    ⟨[.marked sampleRule.key .normal], [], false⟩)

theorem checks_pass : checks = true := rfl
end Controls

#print axioms outside_released_cell_unchanged
#print axioms packet_geometry_and_kind_preserved
#print axioms raw_demand_never_promoted
#print axioms full_exact_source_has_native_route
#print axioms ExactCleanup.extension_only_normal_zero_exact
#print axioms ExactCleanup.serial_bulk_same_leaves_and_protection
#print axioms Controls.checks_pass
#eval Controls.checks

end FullZeroSourceReplay
