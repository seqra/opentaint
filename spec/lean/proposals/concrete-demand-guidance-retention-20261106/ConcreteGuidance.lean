/-
PROPOSAL ONLY. Restore effective concrete MAY coordinates in DEMAND/ANY/Empty-E
cohorts. Keep the old data canonicalizer's EXACT coordinates unchanged.

The finite current-prefix recognizer below is limited to same-header FULL
TAINT/DEMAND/ANY, Empty E, counted paths and separate ordinary/protected streams.
It is not a complete implementation of native TaintGroup or canonicalTaintState.
P, method, block and both ports are complete opaque identities. No origin product
or actual executable ND transfer is defined. Input rows are already supplied.
-/
import RestrictedInitialPolicy

namespace ConcreteGuidance
open ApSpec

inductive Kind where | taint | flow | reach
deriving DecidableEq, Repr
inductive Layer where | normal | demand
deriving DecidableEq, Repr
inductive SpanTail where | may | star | must
deriving DecidableEq, Repr
inductive LeafMask where | exact | anyMask
deriving DecidableEq, Repr
inductive Channel where | ordinary | protectedMask
deriving DecidableEq, Repr
inductive FieldE where | empty | set (fields : List Acc)
deriving DecidableEq, Repr
inductive Original where | zero | whole (identity : Nat)
deriving DecidableEq, Repr

structure FullMark where
  identity : Nat
deriving DecidableEq, Repr

structure Owner where
  method : Nat
  block : Nat
  entry : Int
  exit : Int
deriving DecidableEq, Repr

structure Header where
  kind : Kind
  base : Nat
  layer : Layer
  spanTail : SpanTail
  fieldE : FieldE
deriving DecidableEq, Repr

/-- The ordinary channel represents unannotated support; protected support is
an independent stream. A native payload is their union, not a disjoint split of
value.root. This model does not infer protection from ordinary coverage. -/
structure Coordinate where
  original : Original
  owner : Owner
  header : Header
  path : List Acc
  mark : FullMark
  mask : LeafMask
  channel : Channel
deriving DecidableEq, Repr

def selectedHeader (h : Header) : Bool :=
  decide (h.kind = .taint ∧ h.layer = .demand ∧
    h.spanTail = .may ∧ h.fieldE = .empty)

def isGuide (c : Coordinate) : Bool :=
  selectedHeader c.header && match c.mask with
    | .exact => false
    | .anyMask => true

/-- Header E applies to any-mask leaves only. EXACT leaves always have Empty E.
The native ANY-header constructor rejects nonempty E; no E join is proposed. -/
def effectiveE (c : Coordinate) : FieldE :=
  match c.mask with | .exact => .empty | .anyMask => c.header.fieldE

def legalAnyHeader (h : Header) : Bool :=
  match h.spanTail with | .may => decide (h.fieldE = .empty) | _ => true

def nextFieldAdmitted (e : FieldE) (field : Acc) : Bool :=
  match e with | .empty => true | .set fields => !(fields.contains field)

abbrev State := Coordinate → Bool
def empty : State := fun _ => false
def view : List Coordinate → State
  | [] => empty
  | head :: rest => fun c => decide (c = head) || view rest c
def union (a b : State) : State := fun c => a c || b c
def delta (old incoming : State) : State := fun c => incoming c && !(old c)
def guideView (state : State) : State := fun c => state c && isGuide c
def restore (oldData supplied : State) : State := union oldData (guideView supplied)

theorem union_membership (a b : State) (c : Coordinate) :
    union a b c = true ↔ a c = true ∨ b c = true := by
  cases ha : a c <;> cases hb : b c <;> simp [union, ha, hb]

theorem union_both_orders (a b : State) (c : Coordinate) :
    union a b c = union b a c := Bool.or_comm _ _

theorem union_no_origin_products (a b : State) (c : Coordinate)
    (ha : a c = false) (hb : b c = false) : union a b c = false := by
  simp [union, ha, hb]

theorem delta_is_exact_coordinate_freshness (old incoming : State) (c : Coordinate) :
    delta old incoming c = true ↔ incoming c = true ∧ old c = false := by
  cases ho : old c <;> cases hi : incoming c <;> simp [delta, ho, hi]

theorem duplicate_is_not_fresh (state : State) (c : Coordinate) :
    delta state state c = false := by
  cases hs : state c <;> simp [delta, hs]

theorem delta_reconstructs_union (old incoming : State) (c : Coordinate) :
    union old (delta old incoming) c = union old incoming c := by
  cases ho : old c <;> cases hi : incoming c <;> simp [union, delta, ho, hi]

theorem guide_restore_keeps_supplied (data supplied : State) (c : Coordinate)
    (present : supplied c = true) (guide : isGuide c = true) :
    restore data supplied c = true := by
  simp [restore, union, guideView, present, guide]

theorem guide_restore_keeps_data (data supplied : State) (c : Coordinate)
    (present : data c = true) : restore data supplied c = true := by
  simp [restore, union, present]

theorem restore_exact_set_unchanged (data supplied : State) (c : Coordinate)
    (hExact : c.mask = .exact) : restore data supplied c = data c := by
  simp [restore, union, guideView, isGuide, hExact]

theorem restore_adds_no_nonguide (data supplied : State) (c : Coordinate)
    (nonguide : isGuide c = false) : restore data supplied c = data c := by
  simp [restore, union, guideView, nonguide]

theorem restore_has_no_origin_product (data supplied : State) (c : Coordinate)
    (absentData : data c = false) (absentInput : supplied c = false) :
    restore data supplied c = false := by
  simp [restore, union, guideView, absentData, absentInput]

theorem view_append (left right : List Coordinate) (c : Coordinate) :
    view (left ++ right) c = (view left c || view right c) := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
    simpa only [List.cons_append, view, Bool.or_assoc] using
      congrArg (fun b => decide (c = head) || b) ih

theorem view_filter (pick : Coordinate → Bool) (rows : List Coordinate) (c : Coordinate) :
    view (rows.filter pick) c = (view rows c && pick c) := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
    by_cases same : c = head
    · subst head
      cases hp : pick c <;> simp [List.filter, view, hp, ih]
    · cases hp : pick head <;> simp [List.filter, view, hp, ih, same]

def restorePacket (data supplied : List Coordinate) : List Coordinate :=
  data ++ supplied.filter isGuide

theorem restore_packet_view (data supplied : List Coordinate) (c : Coordinate) :
    view (restorePacket data supplied) c = restore (view data) (view supplied) c := by
  rw [restorePacket, view_append, view_filter]
  rfl

theorem restore_packet_exact_set_unchanged (data supplied : List Coordinate) (c : Coordinate)
    (hExact : c.mask = .exact) :
    view (restorePacket data supplied) c = view data c := by
  rw [restore_packet_view]
  exact restore_exact_set_unchanged _ _ _ hExact

/-- Scoped current DATA witness only: ANY/T covers matching coordinates at and
below its path in this same typed header/channel. Other native header/E joins
and the complete STAR/MUST policy are intentionally not implemented here. -/
def currentCovers (broad narrow : Coordinate) : Bool :=
  decide (broad = narrow) ||
    (isGuide broad && decide (broad.original = narrow.original ∧
      broad.owner = narrow.owner ∧ broad.header = narrow.header ∧
      broad.mark = narrow.mark ∧ broad.channel = narrow.channel) &&
      (dropPrefix broad.path narrow.path).isSome)

def currentInsert (row : Coordinate) (rows : List Coordinate) : List Coordinate :=
  if rows.any (fun old => currentCovers old row) then rows
  else row :: rows.filter (fun old => !(currentCovers row old))
def currentPacket (rows : List Coordinate) : List Coordinate :=
  rows.foldl (fun old row => currentInsert row old) []
def proposalStep (old incoming : List Coordinate) : List Coordinate :=
  restorePacket (currentPacket (old ++ incoming)) (old ++ incoming)

def s : Nat := 0
def f : Acc := 7
def g : Acc := 8
def T : FullMark := ⟨11⟩
def U : FullMark := ⟨12⟩
def producer : Owner := ⟨1, 3, -2, 7⟩
def header : Header := ⟨.taint, s, .demand, .may, .empty⟩
def root : Coordinate := ⟨.zero, producer, header, [], T, .anyMask, .ordinary⟩
def child : Coordinate := { root with path := [f] }
def exactChild : Coordinate := { child with mask := .exact }
def protectedChild : Coordinate := { child with channel := .protectedMask }
def rootU : Coordinate := { root with mark := U }
def childU : Coordinate := { child with mark := U }

theorem captured_PZERO_current_root_then_child_loses_child :
    currentInsert child (currentInsert root []) = [root] := by decide

theorem current_child_then_root_loses_child :
    currentInsert root (currentInsert child []) = [root] := by decide

theorem current_same_packet_loses_child : currentPacket [root, child] = [root] := by decide

theorem proposal_same_packet_retains_both :
    view (proposalStep [] [root, child]) root = true ∧
    view (proposalStep [] [root, child]) child = true := by decide

theorem proposal_root_then_child_retains_both :
    view (proposalStep (proposalStep [] [root]) [child]) root = true ∧
    view (proposalStep (proposalStep [] [root]) [child]) child = true := by decide

theorem proposal_child_then_root_retains_both :
    view (proposalStep (proposalStep [] [child]) [root]) root = true ∧
    view (proposalStep (proposalStep [] [child]) [root]) child = true := by decide

theorem child_coordinate_is_fresh_after_root :
    delta (view [root]) (view [child]) child = true ∧
    currentCovers root child = true := by decide

theorem root_coordinate_is_fresh_after_child :
    delta (view [child]) (view [root]) root = true := by decide

theorem same_packet_coordinates_fresh_duplicate_not_fresh :
    delta empty (view [root, child]) root = true ∧
    delta empty (view [root, child]) child = true ∧
    delta (view [root, child]) (view [child, root]) child = false := by decide

theorem full_marks_are_independent_no_cross_mark_coverage :
    currentCovers root childU = false ∧
    view (proposalStep [] [root, childU]) root = true ∧
    view (proposalStep [] [root, childU]) childU = true ∧
    view (proposalStep [] [root, childU]) child = false := by decide

theorem protected_channel_not_consumed_by_ordinary_ancestor :
    currentCovers root protectedChild = false ∧
    view (proposalStep [] [root, protectedChild]) protectedChild = true ∧
    view (proposalStep [] [root, protectedChild]) child = false := by decide

def nativePayloadView (state : State) (c : Coordinate) : Bool :=
  state { c with channel := .ordinary } || state { c with channel := .protectedMask }

theorem protected_support_is_in_native_payload_without_ordinary_origin :
    nativePayloadView (view [protectedChild]) child = true ∧
    view [protectedChild] child = false ∧
    view [root] protectedChild = false := by decide

theorem protected_MAY_both_orders_and_same_packet :
    let pr := { root with channel := .protectedMask }
    view (proposalStep (proposalStep [] [pr]) [protectedChild]) protectedChild = true ∧
    view (proposalStep (proposalStep [] [protectedChild]) [pr]) pr = true ∧
    view (proposalStep [] [pr,protectedChild]) protectedChild = true := by decide

theorem both_channels_and_marks_restored_without_products :
    let supplied := [root, child, { rootU with channel := .protectedMask },
      { childU with channel := .protectedMask }]
    view (proposalStep [] supplied) child = true ∧
    view (proposalStep [] supplied) { childU with channel := .protectedMask } = true ∧
    view (proposalStep [] supplied) protectedChild = false ∧
    view (proposalStep [] supplied) childU = false := by decide

theorem mixed_EXACT_keeps_current_pruning :
    currentPacket [root, exactChild] = [root] ∧
    view (proposalStep [] [root, exactChild]) exactChild = false ∧
    view (proposalStep [] [root, exactChild]) root = true := by decide

theorem unrelated_EXACT_survives_unchanged :
    let exactU := { exactChild with mark := U }
    view (currentPacket [root, exactU]) exactU = true ∧
    view (proposalStep [] [root, exactU]) exactU = true := by decide

theorem mixed_masks_are_not_reclassified_by_ANY_header :
    isGuide root = true ∧ isGuide exactChild = false ∧
    exactChild.header.spanTail = .may ∧ exactChild.mask = .exact := by decide

theorem non_GUIDE_headers_are_not_selected :
    isGuide { child with header := { header with layer := .normal } } = false ∧
    isGuide { child with header := { header with spanTail := .star } } = false ∧
    isGuide { child with header := { header with spanTail := .must } } = false ∧
    isGuide { child with header := { header with kind := .flow } } = false ∧
    isGuide { child with header := { header with kind := .reach } } = false := by decide

theorem ANY_E_is_empty_or_rejected :
    legalAnyHeader header = true ∧
    legalAnyHeader { header with fieldE := .set [f] } = false ∧
    isGuide { child with header := { header with fieldE := .set [f] } } = false := by decide

theorem mixed_EXACT_never_inherits_header_E :
    effectiveE { exactChild with header := { header with spanTail := .star, fieldE := .set [f] } } = .empty ∧
    effectiveE { child with header := { header with spanTail := .star, fieldE := .set [f] } } = .set [f] ∧
    nextFieldAdmitted (.set [f]) f = false ∧
    nextFieldAdmitted (.set [f]) g = true := by decide

def reverseOwner (owner : Owner) : Owner :=
  { owner with entry := owner.exit, exit := owner.entry }

theorem reversing_ports_is_involutive (owner : Owner) :
    reverseOwner (reverseOwner owner) = owner := by cases owner; rfl

abbrev Demand := RestrictedInitialPolicy.Demand
abbrev Input := RestrictedInitialPolicy.Input

def scalarInput (c : Coordinate) : Input :=
  let mark : RestrictedInitialPolicy.Mark := .full c.mark.identity
  match c.mask with
  | .exact => ⟨c.header.base, c.path, .exact, mark, false⟩
  | .anyMask => match c.header.spanTail with
    | .may => ⟨c.header.base, c.path, .any, mark, false⟩
    | .must => ⟨c.header.base, c.path, .any, mark, true⟩
    | .star => ⟨c.header.base, c.path, .star, mark, false⟩

structure GuideRow where
  original : Original
  owner : Owner
  query : Demand
deriving DecidableEq, Repr

/-- Extra restored MAY rows only. The native existing exact-data handoff remains
outside this adapter. Protection is not invented as a demand field. -/
def handoff (c : Coordinate) : Option GuideRow :=
  if isGuide c then some ⟨c.original, reverseOwner c.owner,
    ⟨c.header.base, c.path, .any, .full c.mark.identity⟩⟩ else none
def handoffRows (rows : List Coordinate) : List GuideRow := rows.filterMap handoff

theorem handoff_keeps_whole_original_and_exact_reversed_owner
    (c : Coordinate) (row : GuideRow) (supplied : handoff c = some row) :
    row.original = c.original ∧ row.owner = reverseOwner c.owner := by
  unfold handoff at supplied
  cases hg : isGuide c with
  | false => simp [hg] at supplied
  | true =>
    simp only [hg, if_true, Option.some.injEq] at supplied
    cases supplied
    exact ⟨rfl, rfl⟩

def rootDemand : Demand := ⟨s, [], .any, .full T.identity⟩
def childDemand : Demand := ⟨s, [f], .any, .full T.identity⟩
def rawExact : Input := ⟨s, [f,g], .exact, .full T.identity, false⟩
def cutMay : Input := ⟨s, [f], .any, .full T.identity, false⟩
def coarse : Input := ⟨s, [f], .star, .full T.identity, false⟩

structure Admission where
  initial : Input
  layer : Layer
deriving DecidableEq, Repr

/-- FULL-only Empty-E finite adapter for unchanged native admissionLayer.
It is not a GROUP/FLOW admission policy. -/
def emittedLayer (initial actual : Input) (supplied : Layer) : Layer :=
  if initial.shape = .star ∨
      (initial.shape = .any ∧ initial.must = false) ∨ supplied = .demand ∨
      (initial.shape = .exact ∧ actual.shape = .any ∧ actual.must = false)
  then .demand else .normal

def c2 (query : Demand) (actual : Input) (layer : Layer) : Option Admission :=
  (RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget 2 query actual).map
    (fun initial => ⟨initial, emittedLayer initial actual layer⟩)

theorem root_guide_raw_and_cut_same_coarse_DEMAND :
    c2 rootDemand rawExact .normal = some ⟨coarse, .demand⟩ ∧
    c2 rootDemand cutMay .demand = some ⟨coarse, .demand⟩ := by decide

theorem child_guide_distinguishes_raw_NORMAL_from_cut_DEMAND :
    c2 childDemand rawExact .normal = some ⟨rawExact, .normal⟩ ∧
    c2 childDemand cutMay .demand = some ⟨cutMay, .demand⟩ ∧
    (Admission.mk rawExact .normal) ≠ (Admission.mk cutMay .demand) := by decide

theorem mixed_EXACT_scalar_has_no_MAY_reclassification :
    (scalarInput exactChild).shape = .exact ∧
    (scalarInput exactChild).must = false ∧
    (scalarInput child).shape = .any ∧
    (scalarInput child).must = false := by decide

def anyBy {α : Type} (test : α → Bool) : List α → Bool
  | [] => false
  | head :: rest => test head || anyBy test rest

def pairedImage (rows : List GuideRow) (actual : Input) (layer : Layer)
    (initial : Admission) (owner : Owner) (original : Original) : Bool :=
  anyBy (fun row => decide (row.owner = owner ∧ row.original = original ∧
    c2 row.query actual layer = some initial)) rows

theorem captured_PZERO_handoff_scope_and_exit :
    handoff root = some ⟨.zero, ⟨1,3,7,-2⟩, rootDemand⟩ ∧
    handoff child = some ⟨.zero, ⟨1,3,7,-2⟩, childDemand⟩ := by decide

theorem current_handoff_lacks_child_normal_image :
    pairedImage (handoffRows (currentPacket [root,child])) rawExact .normal
      ⟨rawExact,.normal⟩ (reverseOwner producer) .zero = false := by decide

theorem restored_handoff_keeps_child_normal_image_both_orders :
    pairedImage (handoffRows (proposalStep [] [root,child])) rawExact .normal
      ⟨rawExact,.normal⟩ (reverseOwner producer) .zero = true ∧
    pairedImage (handoffRows (proposalStep [] [child,root])) rawExact .normal
      ⟨rawExact,.normal⟩ (reverseOwner producer) .zero = true := by decide

theorem paired_image_does_not_borrow_exit_scope_or_original :
    let rows := handoffRows (proposalStep [] [root,child])
    pairedImage rows rawExact .normal ⟨rawExact,.normal⟩
      { reverseOwner producer with exit := 8 } .zero = false ∧
    pairedImage rows rawExact .normal ⟨rawExact,.normal⟩
      { reverseOwner producer with block := 4 } .zero = false ∧
    pairedImage rows rawExact .normal ⟨rawExact,.normal⟩
      (reverseOwner producer) (.whole 1) = false := by decide

theorem no_new_origin_combinations :
    let other := { child with original := .whole 9 }
    view (proposalStep [] [root,other]) child = false ∧
    view (proposalStep [] [root,other]) other = true := by decide

theorem concrete_handoff_never_creates_FLOW_mark :
    (handoffRows [root,child]).all (fun row =>
      match row.query.mark with | .full _ => true | .flow => false) = true := by decide

theorem mismatching_full_mark_does_not_admit :
    c2 childDemand { rawExact with mark := .full U.identity } .normal = none := by decide

/-- Deliberately unresolved by MAY-only restoration: preserving old EXACT
pruning does not preserve every possible C2 image of a same-head exact guide. -/
theorem same_head_MAY_EXACT_cell_is_not_repaired :
    let exactRoot := { root with mask := .exact }
    view (proposalStep [] [root,exactRoot]) exactRoot = false ∧
    c2 rootDemand (scalarInput root) .demand =
      some ⟨scalarInput root,.demand⟩ ∧
    c2 ⟨s,[],.exact,.full T.identity⟩ (scalarInput root) .demand =
      some ⟨⟨s,[],.exact,.full T.identity,false⟩,.demand⟩ := by decide

/-- One mark slot of the cold-packet source calculation. E is the original
EXACT bit, N the original local MAY bit, and A inherited MAY coverage. -/
def oldColdExact (e n a : Bool) : Bool := (e && !a) && !(n && !a)
def proposedColdExact (e n a : Bool) : Bool := (e && !a) && !n
def oldColdMay (n a : Bool) : Bool := n && !a
def proposedColdMay (n _a : Bool) : Bool := n

theorem cold_EXACT_boolean_mask_law (e n a : Bool) :
    oldColdExact e n a = proposedColdExact e n a := by
  cases e <;> cases n <;> cases a <;> rfl

theorem cold_EXACT_equals_original_exact_without_above_or_local_MAY (e n a : Bool) :
    oldColdExact e n a = (e && !a && !n) ∧
    proposedColdExact e n a = (e && !a && !n) := by
  cases e <;> cases n <;> cases a <;> decide

theorem cold_MAY_restore_is_the_only_changed_slot :
    oldColdMay true true = false ∧ proposedColdMay true true = true ∧
    oldColdExact true true true = proposedColdExact true true true := by decide

/-- Both paths propagate the ORIGINAL local MAY bit, before subtracting A.
This is a source-adapter obligation, not permission to propagate a new header. -/
def nextAbove (ancestor originalLocalMay : Bool) : Bool := ancestor || originalLocalMay

theorem next_ABOVE_uses_original_local_mask (ancestor originalLocalMay : Bool) :
    nextAbove ancestor originalLocalMay = (ancestor || originalLocalMay) := rfl

theorem ordinary_and_protected_cold_masks_are_independent
    (eo no ao ep np ap : Bool) :
    oldColdExact eo no ao = proposedColdExact eo no ao ∧
    oldColdExact ep np ap = proposedColdExact ep np ap :=
  ⟨cold_EXACT_boolean_mask_law _ _ _, cold_EXACT_boolean_mask_law _ _ _⟩

/-- Empty-E MAY support, at one complete owner/P/mark/channel coordinate.
This is DATA denotation only; the operational C2 image can still differ. -/
def mayDenotation (rows : List Coordinate) (point : Coordinate) : Bool :=
  anyBy (fun row => isGuide row && decide (row.original = point.original ∧
    row.owner = point.owner ∧ row.header = point.header ∧
    row.mark = point.mark ∧ row.channel = point.channel) &&
    (dropPrefix row.path point.path).isSome) rows

def sampledPaths : List (List Acc) := [[], [f], [g], [f,g], [g,f], [f,f,g]]
def sampledMayPackets : List (List Coordinate) :=
  [[root,child],
   [{ root with channel := .protectedMask },protectedChild],
   [root,child,{ rootU with channel := .protectedMask },
      { childU with channel := .protectedMask }]]

theorem finite_E0_MAY_compaction_and_restoration_same_denotation :
    sampledMayPackets.all (fun rows => sampledPaths.all (fun path => [T,U].all (fun mark =>
      [Channel.ordinary,Channel.protectedMask].all (fun channel =>
        let point := { root with path := path, mark := mark, channel := channel }
        decide (mayDenotation (currentPacket rows) point =
          mayDenotation (proposalStep [] rows) point))))) = true := by decide

def pruneExactSlot (exactBit maySupport : Bool) : Bool := exactBit && !maySupport

theorem warm_EXACT_prune_depends_only_on_unchanged_MAY_support
    (exactBit oldSupport newSupport : Bool) (same : oldSupport = newSupport) :
    pruneExactSlot exactBit oldSupport = pruneExactSlot exactBit newSupport := by
  rw [same]

theorem finite_warm_EXACT_prune_unchanged_in_both_channels :
    sampledMayPackets.all (fun rows => sampledPaths.all (fun path => [T,U].all (fun mark =>
      [Channel.ordinary,Channel.protectedMask].all (fun channel =>
        [false,true].all (fun exactBit =>
          let point := { root with path := path, mark := mark, channel := channel }
          decide (pruneExactSlot exactBit (mayDenotation (currentPacket rows) point) =
            pruneExactSlot exactBit (mayDenotation (proposalStep [] rows) point))))))) = true := by decide

theorem protected_bit_fresh_even_when_payload_already_present :
    delta (view [child]) (view [protectedChild]) protectedChild = true ∧
    nativePayloadView (view [child]) protectedChild = true := by decide

def executableWitness : Bool :=
  view (proposalStep [] [root,child]) root &&
  view (proposalStep [] [root,child]) child &&
  pairedImage (handoffRows (proposalStep [] [root,child])) rawExact .normal
    ⟨rawExact,.normal⟩ (reverseOwner producer) .zero

theorem executable_witness : executableWitness = true := by decide

#eval (if executableWitness then "CONCRETE_GUIDANCE_WITNESS=true" else "CONCRETE_GUIDANCE_WITNESS=false")

-- The checker requires one audit command for every declared theorem.
#print axioms union_membership
#print axioms union_both_orders
#print axioms union_no_origin_products
#print axioms delta_is_exact_coordinate_freshness
#print axioms duplicate_is_not_fresh
#print axioms delta_reconstructs_union
#print axioms guide_restore_keeps_supplied
#print axioms guide_restore_keeps_data
#print axioms restore_exact_set_unchanged
#print axioms restore_adds_no_nonguide
#print axioms restore_has_no_origin_product
#print axioms view_append
#print axioms view_filter
#print axioms restore_packet_view
#print axioms restore_packet_exact_set_unchanged
#print axioms captured_PZERO_current_root_then_child_loses_child
#print axioms current_child_then_root_loses_child
#print axioms current_same_packet_loses_child
#print axioms proposal_same_packet_retains_both
#print axioms proposal_root_then_child_retains_both
#print axioms proposal_child_then_root_retains_both
#print axioms child_coordinate_is_fresh_after_root
#print axioms root_coordinate_is_fresh_after_child
#print axioms same_packet_coordinates_fresh_duplicate_not_fresh
#print axioms full_marks_are_independent_no_cross_mark_coverage
#print axioms protected_channel_not_consumed_by_ordinary_ancestor
#print axioms protected_support_is_in_native_payload_without_ordinary_origin
#print axioms protected_MAY_both_orders_and_same_packet
#print axioms both_channels_and_marks_restored_without_products
#print axioms mixed_EXACT_keeps_current_pruning
#print axioms unrelated_EXACT_survives_unchanged
#print axioms mixed_masks_are_not_reclassified_by_ANY_header
#print axioms non_GUIDE_headers_are_not_selected
#print axioms ANY_E_is_empty_or_rejected
#print axioms mixed_EXACT_never_inherits_header_E
#print axioms reversing_ports_is_involutive
#print axioms handoff_keeps_whole_original_and_exact_reversed_owner
#print axioms root_guide_raw_and_cut_same_coarse_DEMAND
#print axioms child_guide_distinguishes_raw_NORMAL_from_cut_DEMAND
#print axioms mixed_EXACT_scalar_has_no_MAY_reclassification
#print axioms captured_PZERO_handoff_scope_and_exit
#print axioms current_handoff_lacks_child_normal_image
#print axioms restored_handoff_keeps_child_normal_image_both_orders
#print axioms paired_image_does_not_borrow_exit_scope_or_original
#print axioms no_new_origin_combinations
#print axioms concrete_handoff_never_creates_FLOW_mark
#print axioms mismatching_full_mark_does_not_admit
#print axioms same_head_MAY_EXACT_cell_is_not_repaired
#print axioms cold_EXACT_boolean_mask_law
#print axioms cold_EXACT_equals_original_exact_without_above_or_local_MAY
#print axioms cold_MAY_restore_is_the_only_changed_slot
#print axioms next_ABOVE_uses_original_local_mask
#print axioms ordinary_and_protected_cold_masks_are_independent
#print axioms finite_E0_MAY_compaction_and_restoration_same_denotation
#print axioms warm_EXACT_prune_depends_only_on_unchanged_MAY_support
#print axioms finite_warm_EXACT_prune_unchanged_in_both_channels
#print axioms protected_bit_fresh_even_when_payload_already_present
#print axioms executable_witness

end ConcreteGuidance
