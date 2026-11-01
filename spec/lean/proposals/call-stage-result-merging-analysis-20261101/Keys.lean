import Std

/-!
Finite executable reference keys for a future exact call-result merger.
An original ID names the complete original, including any ND membership.
The model does not replace a complete original with one of its members.
Scope and ordinary payload are semantic keys; protection is a joined value.
-/
namespace CallStageMerge
set_option autoImplicit false

inductive Slot where | s0 | s1 | s2 | s3 deriving DecidableEq, Repr
inductive Identity where | unknown | yes | no deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr
inductive FullMark where | t | u | v deriving DecidableEq, Repr
inductive FactsKind where | reach | flow | taint deriving DecidableEq, Repr
inductive MarkSymbol where
  | zero
  | flow
  | full (mark : FullMark)
  deriving DecidableEq, Repr

structure Bits where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  deriving DecidableEq, Repr

def Bits.zero : Bits := ⟨false, false, false, false⟩
def Bits.test (bits : Bits) : Slot → Bool
  | .s0 => bits.b0
  | .s1 => bits.b1
  | .s2 => bits.b2
  | .s3 => bits.b3

def Bits.join (left right : Bits) : Bits :=
  ⟨left.b0 || right.b0, left.b1 || right.b1,
   left.b2 || right.b2, left.b3 || right.b3⟩

theorem Bits.zero_test (slot : Slot) : Bits.zero.test slot = false := by
  cases slot <;> rfl

theorem Bits.join_test (left right : Bits) (slot : Slot) :
    (left.join right).test slot = (left.test slot || right.test slot) := by
  cases slot <;> rfl

structure Scope where
  actorRun : Fin 4
  callSite : Fin 8
  programPoint : Fin 16 -- includes stage and cleaner step/phase in this finite scope
  original : Fin 8     -- opaque complete original key, not a contributing member
  identity : Identity
  layer : Layer
  callerLayer : Layer
  pendingDemotion : Bool
  deriving DecidableEq, Repr

structure Payload where
  kind : FactsKind
  base : Fin 4
  geometry : Fin 8
  tail : Tail
  fieldExclusion : Bits
  markExclusion : Bits
  mark : MarkSymbol
  members : Bits
  deriving DecidableEq, Repr

structure Key where
  scope : Scope
  payload : Payload
  deriving DecidableEq, Repr

structure Row where
  key : Key
  protection : Bits
  deriving DecidableEq, Repr

structure Observation where
  key : Key
  slot : Slot
  isProtected : Bool
  deriving DecidableEq, Repr

/-- Out-of-payload protection bits carry no protected membership. -/
def rowObservation (row : Row) (observation : Observation) : Bool :=
  if row.key = observation.key then
    row.key.payload.members.test observation.slot &&
      (!observation.isProtected || row.protection.test observation.slot)
  else false

/-- Call only on equal ordinary keys. The theorem below states that premise. -/
def joinRows (old incoming : Row) : Row :=
  ⟨old.key, old.protection.join incoming.protection⟩

theorem bool_associate (a b c : Bool) :
    (a || (b || c)) = ((a || b) || c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_shuffle_right (a b c : Bool) :
    ((a || b) || c) = ((a || c) || b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bool_protection_join (member required left right : Bool) :
    (member && (!required || (left || right))) =
      ((member && (!required || left)) || (member && (!required || right))) := by
  cases member <;> cases required <;> cases left <;> cases right <;> rfl

theorem joined_equal_key (old incoming : Row) : (joinRows old incoming).key = old.key := rfl

theorem joined_observation (old incoming : Row) (same : old.key = incoming.key)
    (observation : Observation) :
    rowObservation (joinRows old incoming) observation =
      (rowObservation old observation || rowObservation incoming observation) := by
  rcases old with ⟨key, flags⟩
  rcases incoming with ⟨other, more⟩
  change key = other at same
  subst other
  by_cases selected : key = observation.key
  · simp only [rowObservation, joinRows, selected, if_pos, Bits.join_test]
    exact bool_protection_join _ _ _ _
  · simp [rowObservation, joinRows, selected]

end CallStageMerge
