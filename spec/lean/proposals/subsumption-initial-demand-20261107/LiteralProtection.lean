/-
Literal H projection of the selected store contract. DATA admission is a
parameter with no assumed confluence law. This model restores only H; it
does not restore discarded ordinary MAY coordinates or guide history.
Typed keys are abstract native coordinates. Span E is a canonical identity;
EXACT keys deliberately have no wrapper/E coordinate. Native key encoding
and ordinary DATA soundness are separate adapter obligations.
-/
import Std

namespace LiteralProtection

inductive Layer where | normal | demand
  deriving DecidableEq, Repr
inductive Head where
  | exact
  | star (exclusionIdentity : Nat)
  | may
  | must (exclusionIdentity : Nat)
  deriving DecidableEq, Repr
structure Coordinate where
  owner : Nat
  original : Nat
  scope : Nat
  entryPort : Nat
  outputPort : Nat
  base : Nat
  path : List Nat
  mark : Nat
  layer : Layer
  head : Head
  deriving DecidableEq, Repr

abbrev Mask := Coordinate → Bool
def empty : Mask := fun _ => false
def union (a b : Mask) : Mask := fun key => a key || b key
def difference (a b : Mask) : Mask := fun key => a key && !(b key)
def Included (a b : Mask) : Prop := ∀ key, a key = true → b key = true
structure Snapshot where
  payload : Mask
  h : Mask
def Valid (s : Snapshot) : Prop := Included s.h s.payload

def embed (data h : Mask) : Snapshot := ⟨union data h, h⟩
def update (oldDataAdmit : Mask → Mask → Mask) (s t : Snapshot) : Snapshot :=
  embed (oldDataAdmit s.payload t.payload) (union s.h t.h)

theorem H_is_exact_literal_union (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) (key : Coordinate) :
    (update dataAdmit s t).h key = (s.h key || t.h key) := rfl

theorem H_cannot_be_created_by_DATA (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) (key : Coordinate) (a : s.h key = false) (b : t.h key = false) :
    (update dataAdmit s t).h key = false := by simp [update, embed, union, a, b]

theorem old_H_survives (dataAdmit : Mask → Mask → Mask) (s t : Snapshot) :
    Included s.h (update dataAdmit s t).h := by
  intro key present
  simp [update, embed, union, present]

theorem incoming_H_survives (dataAdmit : Mask → Mask → Mask) (s t : Snapshot) :
    Included t.h (update dataAdmit s t).h := by
  intro key present
  simp [update, embed, union, present]

theorem H_always_has_a_carrier (data h : Mask) : Valid (embed data h) := by
  intro key present
  change h key = true at present
  simp [embed, union, present]

theorem arbitrary_DATA_update_keeps_valid_H (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) : Valid (update dataAdmit s t) := H_always_has_a_carrier _ _

theorem DATA_rejection_cannot_remove_H (s t : Snapshot) (key : Coordinate) :
    (update (fun _ _ => empty) s t).payload key = (s.h key || t.h key) := by
  simp [update, embed, union, empty]

theorem H_arrival_orders_agree (dataAdmit : Mask → Mask → Mask)
    (s a b : Snapshot) (key : Coordinate) :
    (update dataAdmit (update dataAdmit s a) b).h key =
      (update dataAdmit (update dataAdmit s b) a).h key := by
  change ((s.h key || a.h key) || b.h key) = ((s.h key || b.h key) || a.h key)
  cases s.h key <;> cases a.h key <;> cases b.h key <;> rfl

theorem repeated_H_is_idempotent (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) (key : Coordinate) :
    (update dataAdmit (update dataAdmit s t) t).h key = (update dataAdmit s t).h key := by
  change ((s.h key || t.h key) || t.h key) = (s.h key || t.h key)
  cases s.h key <;> cases t.h key <;> rfl

theorem exact_fresh_flag_delta (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) (key : Coordinate) :
    difference (update dataAdmit s t).h s.h key = difference t.h s.h key := by
  change ((s.h key || t.h key) && !(s.h key)) = (t.h key && !(s.h key))
  cases s.h key <;> cases t.h key <;> rfl

theorem repeated_flag_has_no_new_flag_delta (dataAdmit : Mask → Mask → Mask)
    (s t : Snapshot) (key : Coordinate) :
    difference (update dataAdmit (update dataAdmit s t) t).h
      (update dataAdmit s t).h key = false := by
  unfold difference
  rw [repeated_H_is_idempotent]
  simp

def singleton (key : Coordinate) : Mask := fun out => decide (out = key)

theorem singleton_has_no_different_coordinate (key other : Coordinate)
    (different : other ≠ key) : singleton key other = false := by
  simp [singleton, different]

theorem marked_key_does_not_flag_another_mark (key : Coordinate) (mark : Nat)
    (different : mark ≠ key.mark) : singleton key { key with mark := mark } = false := by
  apply singleton_has_no_different_coordinate
  intro same
  have sameMark := congrArg Coordinate.mark same
  exact different sameMark

theorem changed_span_E_is_a_distinct_flag (key : Coordinate) (a b : Nat)
    (different : a ≠ b) :
    singleton { key with head := .star a } { key with head := .star b } = false := by
  apply singleton_has_no_different_coordinate
  intro same
  have heads := congrArg Coordinate.head same
  simp only at heads
  cases heads
  exact different rfl

/-- Pass uses its existing directed coordinate map for both payload and H. -/
def transport (fromOutput : Coordinate → Option Coordinate) (mask : Mask) : Mask :=
  fun key => ((fromOutput key).map mask).getD false
def pass (fromOutput : Coordinate → Option Coordinate) (s : Snapshot) : Snapshot :=
  ⟨transport fromOutput s.payload, transport fromOutput s.h⟩

theorem pass_H_is_exact_transport (mapping : Coordinate → Option Coordinate)
    (s : Snapshot) : (pass mapping s).h = transport mapping s.h := rfl

theorem pass_plain_input_stays_plain (mapping : Coordinate → Option Coordinate)
    (data : Mask) (key : Coordinate) : (pass mapping ⟨data, empty⟩).h key = false := by
  simp only [pass, transport]
  cases mapping key <;> rfl

theorem pass_unmapped_output_has_no_H (mapping : Coordinate → Option Coordinate)
    (s : Snapshot) (key : Coordinate) (unmapped : mapping key = none) :
    (pass mapping s).h key = false := by simp [pass, transport, unmapped]

theorem pass_preserves_validity (mapping : Coordinate → Option Coordinate)
    (s : Snapshot) (valid : Valid s) : Valid (pass mapping s) := by
  intro key present
  cases atKey : mapping key with
  | none => simp [pass, transport, atKey] at present
  | some source =>
      have sourceH : s.h source = true := by simpa [pass, transport, atKey] using present
      simpa [pass, transport, atKey] using valid source sourceH

theorem pass_reversal_needs_no_introduction_policy
    (forward backward : Coordinate → Option Coordinate) (data : Mask) (key : Coordinate) :
    (pass forward ⟨data, empty⟩).h key = false ∧
    (pass backward ⟨data, empty⟩).h key = false :=
  ⟨pass_plain_input_stays_plain _ _ _, pass_plain_input_stays_plain _ _ _⟩

end LiteralProtection
