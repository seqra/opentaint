import Std
import ApSpec.CorrelatedConcreteImplementation

/- Caller component only. Keys encode ALL owner/port/original/AP/mark/E/flag
coordinates except layer. Native boundary replacement and future frontier
adapters remain separate gates. No arbitrary layer erasure is asserted. -/
namespace Thing2CallerLift
inductive Layer where | normal | demand deriving DecidableEq, Repr
structure Packet where
  key : Nat
  layer : Layer
  deriving DecidableEq, Repr
def layerCovers : Layer → Layer → Prop
  | .normal, _ => True | .demand, .demand => True | .demand, .normal => False
def covers (a b : Packet) : Prop := a.key = b.key ∧ layerCovers a.layer b.layer
def raise (layer : Layer) (force : Bool) : Layer := if force then .demand else layer

theorem raise_covers (a b : Layer) (h : layerCovers a b) (force : Bool) :
    layerCovers (raise a force) (raise b force) := by
  cases force <;> cases a <;> cases b <;> simp_all [raise, layerCovers]

/- Arbitrary executable geometry can reject/split/change payload or force D.
It cannot inspect layer; the source bridge checks this for the native suffix. -/
abbrev Geometry := Nat → List (Nat × Bool)
def geometryStep (g : Geometry) (p : Packet) : List Packet :=
  (g p.key).map (fun (key, force) => ⟨key, raise p.layer force⟩)
theorem geometry_substitution (g : Geometry) (a b r : Packet)
    (h : covers a b) (hr : r ∈ geometryStep g b) :
    ∃ s ∈ geometryStep g a, covers s r := by
  rcases h with ⟨keys, layers⟩
  simp only [geometryStep, List.mem_map] at hr
  rcases hr with ⟨⟨key, force⟩, member, rfl⟩
  refine ⟨⟨key, raise a.layer force⟩, ?_, rfl, raise_covers _ _ layers force⟩
  simp only [geometryStep, List.mem_map]
  exact ⟨(key, force), by simpa only [keys] using member, rfl⟩
def admitsAlias (identity : Bool) (layer : Layer) : Bool := layer == .demand || !identity
inductive Action where
  | ordinary (g : Geometry) | alias (identity : Bool) (g : Geometry)
def safeAction : Action → Prop
  | .ordinary _ => True | .alias identity _ => identity = false
def actionStep : Action → Packet → List Packet
  | .ordinary g, p => geometryStep g p
  | .alias identity g, p => if admitsAlias identity p.layer then geometryStep g p else []
theorem nonidentity_alias_admits (layer : Layer) : admitsAlias false layer = true := by
  cases layer <;> rfl
theorem identity_alias_is_a_real_countercell :
    admitsAlias true .normal = false ∧ admitsAlias true .demand = true := by decide
theorem action_substitution (action : Action) (safe : safeAction action)
    (a b r : Packet) (h : covers a b) (hr : r ∈ actionStep action b) :
    ∃ s ∈ actionStep action a, covers s r := by
  cases action with
  | ordinary g => exact geometry_substitution g a b r h hr
  | alias identity g =>
    simp only [safeAction] at safe
    subst identity
    simp only [actionStep, nonidentity_alias_admits, if_true] at hr ⊢
    exact geometry_substitution g a b r h hr

def runSuffix : List Action → Packet → List Packet
  | [], p => [p]
  | action :: more, p => (actionStep action p).flatMap (runSuffix more)
theorem suffix_substitution (actions : List Action)
    (safe : ∀ action ∈ actions, safeAction action)
    (a b r : Packet) (h : covers a b) (hr : r ∈ runSuffix actions b) :
    ∃ s ∈ runSuffix actions a, covers s r := by
  induction actions generalizing a b r with
  | nil =>
    simp only [runSuffix, List.mem_singleton] at hr
    subst r
    exact ⟨a, List.mem_singleton_self a, h⟩
  | cons action more ih =>
    simp only [runSuffix, List.mem_flatMap] at hr
    rcases hr with ⟨mid, hmid, hr⟩
    obtain ⟨replacement, fresh, covered⟩ :=
      action_substitution action (safe action (by simp)) a b mid h hmid
    obtain ⟨out, reached, hout⟩ := ih (by intro x hx; exact safe x (by simp [hx]))
      replacement mid r covered hr
    exact ⟨out, List.mem_flatMap.mpr ⟨replacement, fresh, reached⟩, hout⟩

def familyCovers (reduced full : List Packet) : Prop :=
  ∀ p ∈ full, ∃ q ∈ reduced, covers q p
def deliver (actions : List Action) (inputs : List Packet) : List Packet := inputs.flatMap (runSuffix actions)
theorem deliveries_covered (actions : List Action) (safe : ∀ a ∈ actions, safeAction a)
    (reduced full : List Packet) (h : familyCovers reduced full) :
    familyCovers (deliver actions reduced) (deliver actions full) := by
  intro p hp
  simp only [deliver, List.mem_flatMap] at hp
  rcases hp with ⟨input, member, reached⟩
  obtain ⟨replacement, fresh, covered⟩ := h input member
  obtain ⟨out, reachedOut, outCover⟩ := suffix_substitution actions safe replacement input p covered reached
  exact ⟨out, List.mem_flatMap.mpr ⟨replacement, fresh, reachedOut⟩, outCover⟩

/- ND uses every complete arm; its arbitrary payload function sees complete
keys, including the full parent-original union and inherited protection. -/
inductive ArmsCover : List Packet → List Packet → Prop
  | nil : ArmsCover [] []
  | cons (a b : Packet) (as bs : List Packet) : covers a b → ArmsCover as bs → ArmsCover (a :: as) (b :: bs)
def allKeys (xs : List Packet) : List Nat := xs.map Packet.key
def joinedLayer : List Packet → Layer
  | [] => .normal
  | x :: more => if x.layer == .demand then .demand else joinedLayer more
def join (combine : List Nat → Nat) (xs : List Packet) : Packet := ⟨combine (allKeys xs), joinedLayer xs⟩
theorem all_keys_preserved (reduced full : List Packet) (h : ArmsCover reduced full) :
    allKeys reduced = allKeys full := by
  induction h with
  | nil => rfl
  | @cons a b as bs covered rest ih =>
    simp only [allKeys] at ih
    simp only [allKeys, List.map_cons]
    rw [covered.1, ih]
theorem joined_layer_covered (reduced full : List Packet) (h : ArmsCover reduced full) :
    layerCovers (joinedLayer reduced) (joinedLayer full) := by
  induction h with
  | nil => trivial
  | @cons a b as bs covered rest ih =>
    cases a with | mk ak al =>
      cases b with | mk bk bl =>
        cases al <;> cases bl <;> cases ha : joinedLayer as <;> cases hb : joinedLayer bs <;>
          simp_all [covers, joinedLayer, layerCovers]
theorem complete_nd_join_covered (combine : List Nat → Nat) (reduced full : List Packet)
    (h : ArmsCover reduced full) : covers (join combine reduced) (join combine full) := by
  exact ⟨congrArg combine (all_keys_preserved reduced full h), joined_layer_covered reduced full h⟩

structure SinkObservation where
  report : Nat
  layer : Layer
  deriving DecidableEq, Repr
def observeSink (report : Nat) (parts : List Packet) : SinkObservation := ⟨report, joinedLayer parts⟩
theorem same_sink_observation_covered (report : Nat) (reduced full : List Packet)
    (h : ArmsCover reduced full) :
    (observeSink report reduced).report = (observeSink report full).report ∧
    layerCovers (observeSink report reduced).layer (observeSink report full).layer :=
  ⟨rfl, joined_layer_covered reduced full h⟩

/- Native unary NORMAL is persisted; NORMAL ND and backward-ZERO remain
handoff guidance. This explicitly avoids a blind NORMAL-layer drop. -/
inductive OriginalKind where | nativeUnary | nd | backwardZero deriving DecidableEq, Repr
def selectedForHandoff (kind : OriginalKind) (layer : Layer) : Bool := layer == .demand || kind != .nativeUnary
def persistNative (kind : OriginalKind) (p : Packet) : Bool := kind == .nativeUnary && p.layer == .normal
structure Export where
  guide : List Nat
  native : List Packet
  deriving DecidableEq, Repr
def exportPacket (projection : Nat → List Nat) (kind : OriginalKind) (p : Packet) : Export :=
  ⟨if selectedForHandoff kind p.layer then projection p.key else [], if persistNative kind p then [p] else []⟩
theorem normal_nd_guidance_is_unchanged (projection : Nat → List Nat) (key : Nat) :
    (exportPacket projection .nd ⟨key, .normal⟩).guide = (exportPacket projection .nd ⟨key, .demand⟩).guide := by rfl
theorem normal_backward_zero_guidance_is_unchanged (projection : Nat → List Nat) (key : Nat) :
    (exportPacket projection .backwardZero ⟨key, .normal⟩).guide =
    (exportPacket projection .backwardZero ⟨key, .demand⟩).guide := by rfl
theorem unary_normal_is_retained (projection : Nat → List Nat) (key : Nat) :
    ⟨key, .normal⟩ ∈ (exportPacket projection .nativeUnary ⟨key, .normal⟩).native := by simp [exportPacket, persistNative]

/- Complete caller derivations below concern required CONCRETE witnesses,
not equality of raw layer-encoded packet atoms. NORMAL does not become a
DEMAND packet merely by erasing a label. Exact permission/report identity
atoms remain distinct. The later identity-alias bridge uses the already
selected input-alias-closure contract, not safeAction and not a new producer.
Native adapters must construct the actual witnesses for these atoms. -/
structure Rule where
  inputs : List Nat
  output : Nat
  deriving DecidableEq, Repr
inductive Derives (rules : List Rule) (seeds : List Nat) : Nat → Prop
  | seed (p : Nat) : p ∈ seeds → Derives rules seeds p
  | fire (rule : Rule) : rule ∈ rules →
      (∀ p ∈ rule.inputs, Derives rules seeds p) → Derives rules seeds rule.output

theorem derivation_substitution (full reduced : List Rule) (seeds : List Nat)
    (replacement : ∀ rule ∈ full, (∀ p ∈ rule.inputs, Derives reduced seeds p) → Derives reduced seeds rule.output)
    (p : Nat) (h : Derives full seeds p) : Derives reduced seeds p := by
  induction h with
  | seed p member => exact Derives.seed p member
  | fire rule member complete ih => exact replacement rule member ih

theorem caller_derivations_preserved (shared removed replacements : List Rule) (seeds : List Nat)
    (boundary : ∀ rule ∈ removed,
      (∀ p ∈ rule.inputs, Derives (shared ++ replacements) seeds p) →
      Derives (shared ++ replacements) seeds rule.output)
    (p : Nat) (h : Derives (shared ++ removed) seeds p) :
    Derives (shared ++ replacements) seeds p := by
  apply derivation_substitution (shared ++ removed) (shared ++ replacements) seeds _ p h
  intro rule member premises
  rcases List.mem_append.mp member with old | extra
  · exact Derives.fire rule (List.mem_append_left _ old) premises
  · exact boundary rule extra premises

/- Later NORMAL identity calls may skip an alias stage taken by a DEMAND
twin. This case is NOT covered by suffix_substitution. Existing positive
input alias coverage supplies the genuine concrete consequence already.
The trace and its represented-witness map are current producer evidence;
they are not a new closure algorithm or a future-preservation Boolean. -/
abbrev AliasState := ApSpec.CorrelatedConcreteImplementation.AliasState
abbrev AliasEvent := ApSpec.CorrelatedConcreteImplementation.AliasEvent

def afterAliasTrace (events : List AliasEvent) (s : AliasState) : AliasState :=
  events.foldl ApSpec.CorrelatedConcreteImplementation.aliasStep s

theorem later_identity_genuine_alias_covered (events : List AliasEvent) (s : AliasState)
    (initial : ApSpec.CorrelatedConcreteImplementation.inputCovered s) (p q : Nat)
    (genuine : (afterAliasTrace events s).address p = (afterAliasTrace events s).address q)
    (real : (afterAliasTrace events s).tainted ((afterAliasTrace events s).address p) = true) :
    (afterAliasTrace events s).covered q = true := by
  have complete := ApSpec.CorrelatedConcreteImplementation.alias_trace_covered events s initial
  exact ApSpec.CorrelatedConcreteImplementation.identity_alias_is_redundant
    (afterAliasTrace events s) complete p q genuine real

theorem later_identity_witness_is_retained (rules : List Rule) (seeds : List Nat)
    (events : List AliasEvent) (s : AliasState)
    (initial : ApSpec.CorrelatedConcreteImplementation.inputCovered s)
    (represented : ∀ q, (afterAliasTrace events s).covered q = true → Derives rules seeds q)
    (p q : Nat)
    (genuine : (afterAliasTrace events s).address p = (afterAliasTrace events s).address q)
    (real : (afterAliasTrace events s).tainted ((afterAliasTrace events s).address p) = true) :
    Derives rules seeds q :=
  represented q (later_identity_genuine_alias_covered events s initial p q genuine real)

/- A concrete-context checker partitions a removed rule into either the
current Thing2 boundary or a later identity-only genuine alias. It supplies
the corresponding retained proof. Other ND/source/report rules are shared.
No NORMAL packet is used as a raw DEMAND atom in this induction. -/
theorem caller_with_identity_aliases_preserved
    (shared changed retained : List Rule) (seeds : List Nat)
    (reason : Rule → Bool)
    (boundary : ∀ rule ∈ changed, reason rule = false →
      (∀ p ∈ rule.inputs, Derives (shared ++ retained) seeds p) →
      Derives (shared ++ retained) seeds rule.output)
    (identityAlias : ∀ rule ∈ changed, reason rule = true →
      Derives (shared ++ retained) seeds rule.output)
    (p : Nat) (old : Derives (shared ++ changed) seeds p) :
    Derives (shared ++ retained) seeds p := by
  apply caller_derivations_preserved shared changed retained seeds _ p old
  intro rule member premises
  cases selected : reason rule with
  | false => exact boundary rule member selected premises
  | true => exact identityAlias rule member selected
end Thing2CallerLift

#print axioms Thing2CallerLift.raise_covers
#print axioms Thing2CallerLift.geometry_substitution
#print axioms Thing2CallerLift.nonidentity_alias_admits
#print axioms Thing2CallerLift.identity_alias_is_a_real_countercell
#print axioms Thing2CallerLift.action_substitution
#print axioms Thing2CallerLift.suffix_substitution
#print axioms Thing2CallerLift.deliveries_covered
#print axioms Thing2CallerLift.all_keys_preserved
#print axioms Thing2CallerLift.joined_layer_covered
#print axioms Thing2CallerLift.complete_nd_join_covered
#print axioms Thing2CallerLift.same_sink_observation_covered
#print axioms Thing2CallerLift.normal_nd_guidance_is_unchanged
#print axioms Thing2CallerLift.normal_backward_zero_guidance_is_unchanged
#print axioms Thing2CallerLift.unary_normal_is_retained
#print axioms Thing2CallerLift.derivation_substitution
#print axioms Thing2CallerLift.caller_derivations_preserved
#print axioms Thing2CallerLift.later_identity_genuine_alias_covered
#print axioms Thing2CallerLift.later_identity_witness_is_retained
#print axioms Thing2CallerLift.caller_with_identity_aliases_preserved
