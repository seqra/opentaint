/-
Selected local retention law. DATA admission remains arbitrary and incremental:
restoreCurrent(erase(S)) is not a second admission of S. No global DATA normal
form, confluence, commutation or idempotence law is assumed. Exact coordinates
ignore packet E/tail wrappers; spans retain their complete typed E/tail key.
-/
import Std

namespace AllProtectionRetention

inductive Layer where | normal | demand
deriving DecidableEq, Repr
inductive Span where | may | star (e : Nat) | must (e : Nat)
deriving DecidableEq, Repr
inductive Head where | exact | span (value : Span)
deriving DecidableEq, Repr
structure Context where
  original : Nat
  owner : Nat
  base : Nat
  layer : Layer
deriving DecidableEq, Repr
structure Key where
  context : Context
  path : List Nat
  fullMark : Nat
  head : Head
deriving DecidableEq, Repr

inductive Wrapper where | any | star | must
deriving DecidableEq, Repr
inductive LeafMask where | exact | anyMask
deriving DecidableEq, Repr
structure RawLeaf where
  keyContext : Context
  path : List Nat
  fullMark : Nat
  wrapper : Wrapper
  e : Nat
  mask : LeafMask
deriving DecidableEq, Repr

/-- E is a canonical opaque exclusion identity, with 0 = Empty. Only TAINT
full-mark leaves are represented. No E union/intersection semantics is assumed. -/
def effectiveKey (leaf : RawLeaf) : Option Key :=
  match leaf.mask with
  | .exact => some ⟨leaf.keyContext,leaf.path,leaf.fullMark,.exact⟩
  | .anyMask => match leaf.wrapper with
    | .any => if leaf.e = 0 then some ⟨leaf.keyContext,leaf.path,leaf.fullMark,.span .may⟩ else none
    | .star => some ⟨leaf.keyContext,leaf.path,leaf.fullMark,.span (.star leaf.e)⟩
    | .must => some ⟨leaf.keyContext,leaf.path,leaf.fullMark,.span (.must leaf.e)⟩

def isMay (key : Key) : Bool :=
  decide (key.context.layer = .demand ∧ key.head = .span .may)
abbrev Mask := Key → Bool
def zero : Mask := fun _ => false
def one (key : Key) : Mask := fun out => decide (out = key)
def join (a b : Mask) : Mask := fun key => a key || b key
def difference (a b : Mask) : Mask := fun key => a key && !(b key)
def selectedMay (mask : Mask) : Mask := fun key => mask key && isMay key
def Included (a b : Mask) : Prop := ∀ key, a key = true → b key = true

structure Snapshot where
  payload : Mask
  h : Mask
def Valid (snapshot : Snapshot) : Prop := Included snapshot.h snapshot.payload
def erase (snapshot : Snapshot) : Mask := snapshot.payload
def mayUnion (s t : Snapshot) : Mask := join (selectedMay (erase s)) (selectedMay (erase t))

/-- Embed restores literal H and requested MAY positions in the carrier before
attaching H. Physical exact-wrapper placement is left to the native adapter. -/
def embed (data h may : Mask) : Snapshot := ⟨join data (join h may),h⟩
def decodedH (snapshot : Snapshot) : Mask := fun key => snapshot.h key && snapshot.payload key

def update {Restored : Type} (restoreCurrent : Mask → Restored)
    (oldDataAdmit : Restored → Mask → Mask) (s t : Snapshot) : Snapshot :=
  embed (oldDataAdmit (restoreCurrent (erase s)) (erase t)) (join s.h t.h) (mayUnion s t)

theorem H_is_literal_union {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (key : Key) :
    (update restoreCurrent oldDataAdmit s t).h key = (s.h key || t.h key) := rfl

theorem H_old_is_preserved {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) :
    Included s.h (update restoreCurrent oldDataAdmit s t).h := by
  intro key present
  simp [update,embed,join,present]

theorem H_incoming_is_preserved {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) :
    Included t.h (update restoreCurrent oldDataAdmit s t).h := by
  intro key present
  simp [update,embed,join,present]

theorem H_no_invention {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (key : Key)
    (oldAbsent : s.h key = false) (incomingAbsent : t.h key = false) :
    (update restoreCurrent oldDataAdmit s t).h key = false := by
  simp [update,embed,join,oldAbsent,incomingAbsent]

theorem H_monotone_union (a b c d : Mask) (ac : Included a c) (bd : Included b d) :
    Included (join a b) (join c d) := by
  intro key present
  cases ha : a key <;> cases hb : b key
  · simp [join,ha,hb] at present
  · have hd := bd key hb; simp [join,hd]
  · have hc := ac key ha; simp [join,hc]
  · have hc := ac key ha; simp [join,hc]

theorem H_union_order_independent (s t : Snapshot) (key : Key) :
    join s.h t.h key = join t.h s.h key := Bool.or_comm _ _

theorem MAY_requested_union_order_independent (s t : Snapshot) (key : Key) :
    mayUnion s t key = mayUnion t s key := Bool.or_comm _ _

theorem H_two_incremental_orders_agree {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s a b : Snapshot) (key : Key) :
    (update restoreCurrent oldDataAdmit (update restoreCurrent oldDataAdmit s a) b).h key =
    (update restoreCurrent oldDataAdmit (update restoreCurrent oldDataAdmit s b) a).h key := by
  change ((s.h key || a.h key) || b.h key) = ((s.h key || b.h key) || a.h key)
  cases s.h key <;> cases a.h key <;> cases b.h key <;> rfl

theorem carrier_contains_H (data h may : Mask) : Included h (embed data h may).payload := by
  intro key present
  simp [embed,join,present]

theorem carrier_contains_requested_MAY (data h may : Mask) :
    Included may (embed data h may).payload := by
  intro key present
  simp [embed,join,present]

theorem every_update_has_valid_H {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) :
    Valid (update restoreCurrent oldDataAdmit s t) := carrier_contains_H _ _ _

theorem native_style_mask_clip_does_not_lose_embedded_H (data h may : Mask) (key : Key) :
    decodedH (embed data h may) key = h key := by
  cases hh : h key <;> simp [decodedH,embed,join,hh]

theorem old_and_incoming_MAY_positions_are_in_carrier {R : Type}
    (restoreCurrent : Mask → R) (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) :
    Included (mayUnion s t) (update restoreCurrent oldDataAdmit s t).payload :=
  carrier_contains_requested_MAY _ _ _

theorem exact_fresh_H_delta {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (key : Key) :
    difference (update restoreCurrent oldDataAdmit s t).h s.h key = difference t.h s.h key := by
  change ((s.h key || t.h key) && !(s.h key)) = (t.h key && !(s.h key))
  cases s.h key <;> cases t.h key <;> rfl

/-- Only needed to identify the entire physical MAY view with the requested
union. Arbitrary DATA admission is otherwise allowed to create extra MAY keys. -/
def DataCreatesNoExtraMay {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) : Prop :=
  Included (selectedMay (oldDataAdmit (restoreCurrent (erase s)) (erase t))) (mayUnion s t)

theorem boolean_carrier_bridge (d hs ht rs rt : Bool)
    (dataBound : d = true → (rs || rt) = true)
    (hsBound : hs = true → rs = true) (htBound : ht = true → rt = true) :
    (d || ((hs || ht) || (rs || rt))) = (rs || rt) := by
  cases d <;> cases hs <;> cases ht <;> cases rs <;> cases rt <;> simp_all

theorem physical_MAY_equals_union_only_with_explicit_DATA_bridge {R : Type}
    (restoreCurrent : Mask → R) (oldDataAdmit : R → Mask → Mask) (s t : Snapshot)
    (validS : Valid s) (validT : Valid t)
    (noExtra : DataCreatesNoExtraMay restoreCurrent oldDataAdmit s t) (key : Key) :
    selectedMay (update restoreCurrent oldDataAdmit s t).payload key = mayUnion s t key := by
  cases hm : isMay key with
  | false => simp [selectedMay,mayUnion,join,hm]
  | true =>
    have dataBound : oldDataAdmit (restoreCurrent (erase s)) (erase t) key = true →
        (s.payload key || t.payload key) = true := by
      intro present
      have candidate : selectedMay (oldDataAdmit (restoreCurrent (erase s)) (erase t)) key = true := by
        simp [selectedMay,hm,present]
      have bounded := noExtra key candidate
      simpa [mayUnion,selectedMay,erase,join,hm] using bounded
    simpa [selectedMay,update,embed,mayUnion,erase,join,hm] using
      boolean_carrier_bridge
        (oldDataAdmit (restoreCurrent (erase s)) (erase t) key)
        (s.h key) (t.h key) (s.payload key) (t.payload key)
        dataBound (validS key) (validT key)

/-- The native DATA gate may reject an ordinary prefix-covered fact without
its literal payload coordinate. Only selected MAY and exact H need the extra
retention precheck here. This is not a native DATA-freshness classifier. -/
inductive AdmissionPrecheck (s t : Snapshot) where
  | duplicate (mayCovered : Included (selectedMay t.payload) (selectedMay s.payload))
      (flagsCovered : Included t.h s.h)
  | proceed

def checkedUpdate {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (check : AdmissionPrecheck s t) : Snapshot :=
  match check with | .duplicate _ _ => s | .proceed => update restoreCurrent oldDataAdmit s t

theorem duplicate_precheck_is_noop_for_arbitrary_DATA {R : Type}
    (restoreCurrent : Mask → R) (oldDataAdmit : R → Mask → Mask) (s t : Snapshot)
    (mayCovered : Included (selectedMay t.payload) (selectedMay s.payload))
    (flagsCovered : Included t.h s.h) :
    checkedUpdate restoreCurrent oldDataAdmit s t (.duplicate mayCovered flagsCovered) = s := rfl

theorem union_absorbs_included (old incoming : Mask) (covered : Included incoming old) (key : Key) :
    join old incoming key = old key := by
  have pointwise := covered key
  cases ho : old key <;> cases hi : incoming key <;> simp_all [join]

theorem checkedUpdate_H_union {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot)
    (check : AdmissionPrecheck s t) (key : Key) :
    (checkedUpdate restoreCurrent oldDataAdmit s t check).h key = (s.h key || t.h key) := by
  cases check with
  | duplicate mayCovered flagsCovered =>
    change s.h key = join s.h t.h key
    exact (union_absorbs_included _ _ flagsCovered key).symm
  | proceed => rfl

theorem checkedUpdate_preserves_old_H {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (check : AdmissionPrecheck s t) :
    Included s.h (checkedUpdate restoreCurrent oldDataAdmit s t check).h := by
  intro key present
  rw [checkedUpdate_H_union]
  simp [present]

theorem checkedUpdate_preserves_incoming_H {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s t : Snapshot) (check : AdmissionPrecheck s t) :
    Included t.h (checkedUpdate restoreCurrent oldDataAdmit s t check).h := by
  intro key present
  rw [checkedUpdate_H_union]
  simp [present]

theorem duplicate_MAY_union_stable (s t : Snapshot)
    (mayCovered : Included (selectedMay t.payload) (selectedMay s.payload)) (key : Key) :
    mayUnion s t key = selectedMay s.payload key := union_absorbs_included _ _ mayCovered key

theorem fresh_MAY_cannot_use_duplicate_precheck (s t : Snapshot) (key : Key)
    (absent : selectedMay s.payload key = false)
    (fresh : selectedMay t.payload key = true) :
    ¬ Included (selectedMay t.payload) (selectedMay s.payload) := by
  intro covered
  have impossible := covered key fresh
  rw [absent] at impossible
  cases impossible

def sameSnapshotPrecheck (s : Snapshot) : AdmissionPrecheck s s :=
  .duplicate (fun _ present => present) (fun _ present => present)

theorem same_snapshot_duplicate_noop {R : Type} (restoreCurrent : Mask → R)
    (oldDataAdmit : R → Mask → Mask) (s : Snapshot) :
    checkedUpdate restoreCurrent oldDataAdmit s s (sameSnapshotPrecheck s) = s := rfl

theorem fresh_flag_cannot_use_duplicate_precheck (s t : Snapshot) (key : Key)
    (absent : s.h key = false) (fresh : t.h key = true) : ¬ Included t.h s.h := by
  intro covered
  have impossible := covered key fresh
  rw [absent] at impossible
  cases impossible

def context : Context := ⟨17,3,0,.demand⟩
def rootMay : Key := ⟨context,[],11,.span .may⟩
def childMay : Key := { rootMay with path := [7] }
def exactX : Key := { rootMay with head := .exact }
def exactY : Key := { exactX with path := [7] }
def plain (payload : Mask) : Snapshot := ⟨payload,zero⟩
def flagged (key : Key) : Snapshot := ⟨one key,one key⟩
def lastDATA (_current incoming : Mask) : Mask := incoming
def pruneAllDATA (_current _incoming : Mask) : Mask := zero
def restoreIdentity (mask : Mask) : Mask := mask

theorem typed_duplicate_flag_wins_even_if_DATA_prunes_it :
    (update restoreIdentity pruneAllDATA (plain (one exactX)) (flagged exactX)).h exactX = true ∧
    (update restoreIdentity pruneAllDATA (plain (one exactX)) (flagged exactX)).payload exactX = true ∧
    difference (update restoreIdentity pruneAllDATA (plain (one exactX)) (flagged exactX)).h
      (plain (one exactX)).h exactX = true := by decide

theorem broad_DATA_does_not_subsume_protected_child :
    (update restoreIdentity lastDATA (flagged childMay) (plain (one rootMay))).h childMay = true ∧
    (update restoreIdentity lastDATA (flagged childMay) (plain (one rootMay))).payload childMay = true ∧
    (update restoreIdentity lastDATA (flagged childMay) (plain (one rootMay))).h rootMay = false := by decide

theorem same_packet_selected_MAY_and_full_mark_coordinates_remain_literal :
    let incoming := plain (join (one rootMay) (one childMay))
    (update restoreIdentity pruneAllDATA (plain zero) incoming).payload rootMay = true ∧
    (update restoreIdentity pruneAllDATA (plain zero) incoming).payload childMay = true ∧
    (update restoreIdentity pruneAllDATA (plain zero) incoming).payload
      { childMay with fullMark := 12 } = false := by decide

theorem effective_EXACT_ignores_packet_wrapper_and_E :
    effectiveKey ⟨context,[7],11,.any,0,.exact⟩ = some exactY ∧
    effectiveKey ⟨context,[7],11,.star,4,.exact⟩ = some exactY ∧
    effectiveKey ⟨context,[7],11,.must,9,.exact⟩ = some exactY := by decide

theorem spans_keep_exact_typed_E_and_ANY_requires_empty_E :
    effectiveKey ⟨context,[7],11,.any,0,.anyMask⟩ = some childMay ∧
    effectiveKey ⟨context,[7],11,.any,4,.anyMask⟩ = none ∧
    effectiveKey ⟨context,[7],11,.star,4,.anyMask⟩ ≠
      effectiveKey ⟨context,[7],11,.star,9,.anyMask⟩ ∧
    effectiveKey ⟨context,[7],11,.must,4,.anyMask⟩ ≠
      effectiveKey ⟨context,[7],11,.star,4,.anyMask⟩ := by decide

theorem all_H_includes_NORMAL_STAR_and_MUST_E_coordinates :
    let normalStar : Key := ⟨{ context with layer := .normal },[7],11,.span (.star 4)⟩
    let mustE : Key := ⟨context,[7],11,.span (.must 9)⟩
    (update restoreIdentity pruneAllDATA (flagged normalStar) (flagged mustE)).h normalStar = true ∧
    (update restoreIdentity pruneAllDATA (flagged normalStar) (flagged mustE)).h mustE = true ∧
    isMay normalStar = false ∧ isMay mustE = false := by decide

theorem no_flags_inferred_from_derived_E_carrier :
    let derived : Key := { childMay with head := .span (.star 9) }
    (embed (one derived) zero zero).payload derived = true ∧
    (embed (one derived) zero zero).h derived = false := by decide

theorem complete_typed_owner_original_mark_are_not_crossed :
    let state := update restoreIdentity pruneAllDATA (flagged exactX) (plain zero)
    state.h { exactX with context := { context with original := 18 } } = false ∧
    state.h { exactX with context := { context with owner := 4 } } = false ∧
    state.h { exactX with fullMark := 12 } = false := by decide

/-- Counterexample to deriving full DATA order independence from H/MAY laws.
This arbitrary admission is not asserted to be the native old DATA algorithm. -/
theorem full_DATA_order_independence_is_not_assumed :
    let s := plain zero
    let a := plain (one exactX)
    let b := plain (one exactY)
    (update restoreIdentity lastDATA (update restoreIdentity lastDATA s a) b).payload exactX = false ∧
    (update restoreIdentity lastDATA (update restoreIdentity lastDATA s b) a).payload exactX = true := by decide

def witness : Bool :=
  (update restoreIdentity pruneAllDATA (plain (one exactX)) (flagged exactX)).h exactX &&
  (update restoreIdentity lastDATA (flagged childMay) (plain (one rootMay))).payload childMay

theorem executable_all_H_witness : witness = true := by decide
#eval (if witness then "ALL_H_RETENTION=true" else "ALL_H_RETENTION=false")

-- One audit command per theorem.
#print axioms H_is_literal_union
#print axioms H_old_is_preserved
#print axioms H_incoming_is_preserved
#print axioms H_no_invention
#print axioms H_monotone_union
#print axioms H_union_order_independent
#print axioms MAY_requested_union_order_independent
#print axioms H_two_incremental_orders_agree
#print axioms carrier_contains_H
#print axioms carrier_contains_requested_MAY
#print axioms every_update_has_valid_H
#print axioms native_style_mask_clip_does_not_lose_embedded_H
#print axioms old_and_incoming_MAY_positions_are_in_carrier
#print axioms exact_fresh_H_delta
#print axioms boolean_carrier_bridge
#print axioms physical_MAY_equals_union_only_with_explicit_DATA_bridge
#print axioms duplicate_precheck_is_noop_for_arbitrary_DATA
#print axioms union_absorbs_included
#print axioms checkedUpdate_H_union
#print axioms checkedUpdate_preserves_old_H
#print axioms checkedUpdate_preserves_incoming_H
#print axioms duplicate_MAY_union_stable
#print axioms fresh_MAY_cannot_use_duplicate_precheck
#print axioms same_snapshot_duplicate_noop
#print axioms fresh_flag_cannot_use_duplicate_precheck
#print axioms typed_duplicate_flag_wins_even_if_DATA_prunes_it
#print axioms broad_DATA_does_not_subsume_protected_child
#print axioms same_packet_selected_MAY_and_full_mark_coordinates_remain_literal
#print axioms effective_EXACT_ignores_packet_wrapper_and_E
#print axioms spans_keep_exact_typed_E_and_ANY_requires_empty_E
#print axioms all_H_includes_NORMAL_STAR_and_MUST_E_coordinates
#print axioms no_flags_inferred_from_derived_E_carrier
#print axioms complete_typed_owner_original_mark_are_not_crossed
#print axioms full_DATA_order_independence_is_not_assumed
#print axioms executable_all_H_witness

end AllProtectionRetention
