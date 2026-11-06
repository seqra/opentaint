/-
Local producer algebra for the selected demand-guidance design.
No current C2 policy is changed. No native producer equivalence is asserted.

Finite scope: FLOW/DEMAND/ANY operational coordinates, ordinary bases, Empty E,
counted paths, FULL marks from a two-atom table. Headers still carry kind, base,
layer, tail, E and mx. Admitted input coordinates supply an opaque complete exit
label. No premise or admission fact is synthesized by handoff.

Raw states are executable characteristic views of finite coordinate packets.
Function equality below means coordinate membership equality, not packet order,
duplicate multiplicity, native DAG layout, queue effects or callback counts.
Runtime mark requests and every producer/adapter transition remain OPEN.
-/
import GuidanceFrontier

namespace ProducerGuidance
open ApSpec GuidanceFrontier

inductive Kind where | flow | taint | reach
deriving DecidableEq, Repr
inductive Tail where | exact | star | any | must
deriving DecidableEq, Repr

/-- Finite FULL-only exclusion table. No group/catalog normalization is modeled. -/
structure Mx where
  tExcluded : Bool
  uExcluded : Bool
deriving DecidableEq, Repr

structure Header where
  kind : Kind
  base : Nat
  layer : GuidanceFrontier.Layer
  tail : Tail
  exclusion : Excl
  mx : Mx
deriving DecidableEq, Repr

structure Coordinate where
  header : Header
  path : List Acc
  exitLabel : Nat
deriving DecidableEq, Repr

abbrev RawState := Coordinate → Bool

def emptyState : RawState := fun _ => false
def rawView : List Coordinate → RawState
  | [] => emptyState
  | head :: rest => fun coordinate => decide (coordinate = head) || rawView rest coordinate

def rawAdd (old incoming : RawState) : RawState :=
  fun coordinate => old coordinate || incoming coordinate

def rawDelta (old incoming : RawState) : RawState :=
  fun coordinate => incoming coordinate && !(old coordinate)

theorem raw_view_append (left right : List Coordinate) :
    rawView (left ++ right) = rawAdd (rawView left) (rawView right) := by
  funext coordinate
  induction left with
  | nil => rfl
  | cons head rest ih =>
    simpa only [List.cons_append, rawView, rawAdd, Bool.or_assoc] using
      congrArg (fun value => decide (coordinate = head) || value) ih

theorem raw_add_preserves_old (old incoming : RawState) (coordinate : Coordinate)
    (present : old coordinate = true) : rawAdd old incoming coordinate = true := by
  simp [rawAdd, present]

theorem raw_add_preserves_incoming (old incoming : RawState) (coordinate : Coordinate)
    (present : incoming coordinate = true) : rawAdd old incoming coordinate = true := by
  simp [rawAdd, present]

theorem raw_delta_is_exact_coordinate_freshness (old incoming : RawState)
    (coordinate : Coordinate) :
    rawDelta old incoming coordinate = true ↔
      incoming coordinate = true ∧ old coordinate = false := by
  cases hOld : old coordinate <;> cases hNew : incoming coordinate <;>
    simp [rawDelta, hOld, hNew]

theorem exact_duplicate_has_no_delta (state : RawState) :
    rawDelta state state = emptyState := by
  funext coordinate
  cases h : state coordinate <;> simp [rawDelta, emptyState, h]

theorem raw_add_is_idempotent (state : RawState) : rawAdd state state = state := by
  funext coordinate
  cases h : state coordinate <;> simp [rawAdd, h]

theorem raw_add_is_order_independent (left right : RawState) :
    rawAdd left right = rawAdd right left := by
  funext coordinate
  exact Bool.or_comm _ _

theorem delta_reconstructs_added_memberships (old incoming : RawState) :
    rawAdd old (rawDelta old incoming) = rawAdd old incoming := by
  funext coordinate
  cases hOld : old coordinate <;> cases hNew : incoming coordinate <;>
    simp [rawAdd, rawDelta, hOld, hNew]

def mxEmpty : Mx := ⟨false, false⟩
def mxT : Mx := ⟨true, false⟩
def selectedHeader : Header := ⟨.flow, p, .demand, .any, Excl.empty, mxEmpty⟩
def rootCoordinate : Coordinate := ⟨selectedHeader, [], 17⟩
def childCoordinate : Coordinate := ⟨selectedHeader, [f], 17⟩
def rootState : RawState := rawView [rootCoordinate]
def childState : RawState := rawView [childCoordinate]

theorem root_first_child_is_fresh :
    rawDelta rootState childState childCoordinate = true ∧
    rawAdd rootState childState rootCoordinate = true ∧
    rawAdd rootState childState childCoordinate = true := by decide

theorem child_first_root_is_fresh :
    rawDelta childState rootState rootCoordinate = true ∧
    rawAdd childState rootState rootCoordinate = true ∧
    rawAdd childState rootState childCoordinate = true := by decide

theorem cold_packet_preserves_both_coordinates :
    rawDelta emptyState (rawView [rootCoordinate, childCoordinate]) rootCoordinate = true ∧
    rawDelta emptyState (rawView [rootCoordinate, childCoordinate]) childCoordinate = true ∧
    rawDelta (rawView [rootCoordinate, childCoordinate])
      (rawView [rootCoordinate, childCoordinate]) childCoordinate = false := by decide

def withMx (coordinate : Coordinate) (mx : Mx) : Coordinate :=
  { coordinate with header := { coordinate.header with mx := mx } }

theorem full_header_mx_path_and_exit_are_coordinates :
    rawView [rootCoordinate] (withMx rootCoordinate mxT) = false ∧
    rawView [rootCoordinate] { rootCoordinate with
      header := { selectedHeader with layer := .normal } } = false ∧
    rawView [rootCoordinate] { rootCoordinate with
      header := { selectedHeader with tail := .star } } = false ∧
    rawView [rootCoordinate] { rootCoordinate with
      header := { selectedHeader with exclusion := .set [f] } } = false ∧
    rawView [rootCoordinate] { rootCoordinate with
      header := { selectedHeader with base := p + 1 } } = false ∧
    rawView [rootCoordinate] { rootCoordinate with
      header := { selectedHeader with kind := .taint } } = false ∧
    rawView [rootCoordinate] childCoordinate = false ∧
    rawView [rootCoordinate] { rootCoordinate with exitLabel := 18 } = false := by decide

theorem DATA_coverage_and_GUIDE_freshness_are_different :
    queryCovers d0 d1 = true ∧
    dataInsert childRow (dataInsert rootRow []) = [rootRow] ∧
    rawDelta rootState childState childCoordinate = true := by decide

/-- Projection of already supplied eligible rows. FLOW mark exclusions are
dropped by guidancePattern. This local projection does not validate admission,
create exit coordinates, evaluate C5, or prove a native producer reaches here. -/
def handoff (coordinate : Coordinate) : Option Row :=
  let header := coordinate.header
  if header.kind = .flow ∧ header.layer = .demand ∧ header.tail = .any ∧
      header.exclusion = Excl.empty then
    some ⟨⟨header.base, coordinate.path, .any, .flow⟩, coordinate.exitLabel⟩
  else none

def handoffRows (packet : List Coordinate) : List Row := packet.filterMap handoff

def rawObservation (accept : Row → Bool) : List Coordinate → Bool
  | [] => false
  | coordinate :: rest =>
    (match handoff coordinate with | none => false | some row => accept row) ||
      rawObservation accept rest

theorem handoff_preserves_exact_rows_for_any_observation
    (accept : Row → Bool) (packet : List Coordinate) :
    containsBy accept (handoffRows packet) = rawObservation accept packet := by
  induction packet with
  | nil => rfl
  | cons coordinate rest ih =>
    cases h : handoff coordinate with
    | none => simpa [handoffRows, List.filterMap_cons, h, rawObservation, containsBy] using ih
    | some row =>
      simpa only [handoffRows, List.filterMap_cons, h, rawObservation, containsBy] using
        congrArg (fun value => accept row || value) ih

theorem handoff_paired_admission_image_equivalence
    (packet : List Coordinate) (actual initial : Input) (label : Nat) :
    pairedAdmissionImage (handoffRows packet) actual initial label =
      rawObservation (fun row =>
        decide (RestrictedInitialPolicy.emit row.query actual = some initial) &&
          Nat.beq row.exitLabel label) packet :=
  handoff_preserves_exact_rows_for_any_observation _ packet

theorem handoff_root_child_both_orders :
    handoffRows [rootCoordinate, childCoordinate] = [rootRow, childRow] ∧
    handoffRows [childCoordinate, rootCoordinate] = [childRow, rootRow] := by decide

theorem current_STAR_policy_and_child_MUST_image_are_unchanged :
    RestrictedInitialPolicy.emit d0 actualChildMust = some childStarFlow ∧
    RestrictedInitialPolicy.emit d1 actualChildMust = some childMustFlow ∧
    pairedAdmissionImage (handoffRows [rootCoordinate, childCoordinate])
      actualChildMust childStarFlow 17 = true ∧
    pairedAdmissionImage (handoffRows [rootCoordinate, childCoordinate])
      actualChildMust childMustFlow 17 = true ∧
    pairedAdmissionImage (handoffRows [childCoordinate, rootCoordinate])
      actualChildMust childMustFlow 17 = true := by decide

/-- Retaining the same-head guide also exposes the existing abstract EXACT
cell. This is another scalar image, not a new emitter or layer policy. -/
theorem retained_child_keeps_existing_exact_FLOW_image :
    RestrictedInitialPolicy.emit d0 ⟨p, [f], .exact, T, false⟩ = some childStarFlow ∧
    RestrictedInitialPolicy.emit d1 ⟨p, [f], .exact, T, false⟩ =
      some ⟨p, [f], .exact, .flow, false⟩ ∧
    pairedAdmissionImage (handoffRows [rootCoordinate, childCoordinate])
      ⟨p, [f], .exact, T, false⟩ ⟨p, [f], .exact, .flow, false⟩ 17 = true := by decide

theorem handoff_projection_drops_mx (coordinate : Coordinate) (mx : Mx) :
    handoff (withMx coordinate mx) = handoff coordinate := rfl

/-- Intersection of excluded atoms is union of admitted FULL atoms. -/
def mxJoinAdmitted (left right : Mx) : Mx :=
  ⟨left.tExcluded && right.tExcluded, left.uExcluded && right.uExcluded⟩

theorem same_head_mx_union_only_after_projection
    (coordinate : Coordinate) (left right : Mx) (accept : Row → Bool) :
    rawObservation accept [withMx coordinate left, withMx coordinate right] =
      rawObservation accept [withMx coordinate (mxJoinAdmitted left right)] := by
  simp only [rawObservation, handoff_projection_drops_mx]
  cases handoff coordinate <;> simp

def requestT (coordinate : Coordinate) : Bool := !(coordinate.header.mx.tExcluded)

def requestU (coordinate : Coordinate) : Bool := !(coordinate.header.mx.uExcluded)

/-- Existing cofinite union preserves the union of requests at this exact head.
This does not authorize prefix pruning or infer equivalence from projection. -/
theorem same_head_mx_intersection_preserves_T_request_union
    (coordinate : Coordinate) (left right : Mx) :
    requestT (withMx coordinate (mxJoinAdmitted left right)) =
      (requestT (withMx coordinate left) || requestT (withMx coordinate right)) := by
  cases hl : left.tExcluded <;> cases hr : right.tExcluded <;>
    simp [requestT, withMx, mxJoinAdmitted, hl, hr]

theorem same_head_mx_intersection_preserves_U_request_union
    (coordinate : Coordinate) (left right : Mx) :
    requestU (withMx coordinate (mxJoinAdmitted left right)) =
      (requestU (withMx coordinate left) || requestU (withMx coordinate right)) := by
  cases hl : left.uExcluded <;> cases hr : right.uExcluded <;>
    simp [requestU, withMx, mxJoinAdmitted, hl, hr]

theorem same_mx_projection_does_not_prove_runtime_request_equivalence :
    handoff (withMx rootCoordinate mxEmpty) = handoff (withMx rootCoordinate mxT) ∧
    requestT (withMx rootCoordinate mxEmpty) = true ∧
    requestT (withMx rootCoordinate mxT) = false ∧
    rawDelta rootState (rawView [withMx rootCoordinate mxT])
      (withMx rootCoordinate mxT) = true := by decide

#eval handoffRows [rootCoordinate, childCoordinate]
#eval rawDelta rootState childState childCoordinate
#print axioms raw_view_append
#print axioms raw_add_preserves_old
#print axioms raw_add_preserves_incoming
#print axioms raw_delta_is_exact_coordinate_freshness
#print axioms exact_duplicate_has_no_delta
#print axioms raw_add_is_idempotent
#print axioms raw_add_is_order_independent
#print axioms delta_reconstructs_added_memberships
#print axioms root_first_child_is_fresh
#print axioms child_first_root_is_fresh
#print axioms cold_packet_preserves_both_coordinates
#print axioms full_header_mx_path_and_exit_are_coordinates
#print axioms DATA_coverage_and_GUIDE_freshness_are_different
#print axioms handoff_preserves_exact_rows_for_any_observation
#print axioms handoff_paired_admission_image_equivalence
#print axioms handoff_root_child_both_orders
#print axioms current_STAR_policy_and_child_MUST_image_are_unchanged
#print axioms retained_child_keeps_existing_exact_FLOW_image
#print axioms handoff_projection_drops_mx
#print axioms same_head_mx_union_only_after_projection
#print axioms same_head_mx_intersection_preserves_T_request_union
#print axioms same_head_mx_intersection_preserves_U_request_union
#print axioms same_mx_projection_does_not_prove_runtime_request_equivalence

end ProducerGuidance
