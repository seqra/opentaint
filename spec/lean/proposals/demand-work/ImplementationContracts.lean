/-
  Small implementation contracts for the two work-removal changes.
  No analyzer code or demand-emission policy is changed by this file.

  P1 assumes eligibility denotes a fixed graph/method/view relation. Moving
  the pure keep predicate before that relation preserves accepted row order.
  It need not preserve private incremental scratch after rejected rows.

  P2 represents a query-local Option Bool table as UInt8 slots:
  UNKNOWN=0, FALSE=1, TRUE=2. Family IDs are immutable Fin n indices.
  The logical result/scratch theorem is in DemandWorkPruning.lean; the byte
  read/write refinement here supplies its implementation representation.
  Mutable allocation, concurrent ownership and cancellation need source tests.
-/
import Std

namespace DemandImplementationContracts

def ownersThenKeep {A : Type} (eligible keep : A → Bool) (rows : List A) : List A :=
  (rows.filter eligible).filter keep

def keepThenOwners {A : Type} (eligible keep : A → Bool) (rows : List A) : List A :=
  (rows.filter keep).filter eligible

/-- Same rows, in the same order; this does not assert the same calls to a
    mutable graph scratch. Its Boolean result must denote fixed eligibility. -/
theorem early_filter_preserves_rows {A : Type} (eligible keep : A → Bool) (rows : List A) :
    ownersThenKeep eligible keep rows = keepThenOwners eligible keep rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases he : eligible row <;> cases hk : keep row <;>
      simp [ownersThenKeep, keepThenOwners, he, hk] at ih ⊢ <;>
      first | exact ih | exact congrArg (List.cons row) ih

theorem early_filter_preserves_decoded_outputs {A B : Type}
    (eligible keep : A → Bool) (decode : A → B) (rows : List A) :
    (ownersThenKeep eligible keep rows).map decode =
      (keepThenOwners eligible keep rows).map decode :=
  congrArg (List.map decode) (early_filter_preserves_rows eligible keep rows)

theorem early_filter_owner_calls_never_increase {A : Type} (keep : A → Bool) (rows : List A) :
    (rows.filter keep).length ≤ rows.length := List.length_filter_le keep rows

def encode (answer : Option Bool) : UInt8 :=
  match answer with
  | none => 0
  | some false => 1
  | some true => 2

def decode (slot : UInt8) : Option (Option Bool) :=
  if slot == 0 then some none else
  if slot == 1 then some (some false) else
  if slot == 2 then some (some true) else none

theorem slot_round_trip (answer : Option Bool) : decode (encode answer) = some answer := by
  cases answer with
  | none => decide
  | some value => cases value <;> decide

def ByteTable (n : Nat) := Fin n → UInt8
def AnswerTable (n : Nat) := Fin n → Option Bool

def Represents {n : Nat} (bytes : ByteTable n) (answers : AnswerTable n) : Prop :=
  ∀ family, decode (bytes family) = some (answers family)

def write {A : Type} {n : Nat} (table : Fin n → A) (family : Fin n) (value : A) : Fin n → A :=
  fun other => if other = family then value else table other

theorem zero_array_represents_empty {n : Nat} :
    Represents (fun _ : Fin n => 0) (fun _ => none) := by
  intro family
  rfl

theorem write_preserves_representation {n : Nat} (bytes : ByteTable n)
    (answers : AnswerTable n) (valid : Represents bytes answers)
    (family : Fin n) (answer : Bool) :
    Represents (write bytes family (encode (some answer)))
      (write answers family (some answer)) := by
  intro other
  by_cases same : other = family
  · subst other
    simp only [write, if_true]
    exact slot_round_trip (some answer)
  · simp only [write, if_neg same]
    exact valid other

structure StepResult (Scratch Table : Type) where
  answer : Bool
  scratch : Scratch
  table : Table

def logicalStep {n : Nat} {S : Type} (run : Fin n → S → Bool × S)
    (family : Fin n) (scratch : S) (answers : AnswerTable n) : StepResult S (AnswerTable n) :=
  match answers family with
  | some answer => ⟨answer, scratch, answers⟩
  | none =>
    let result := run family scratch
    ⟨result.1, result.2, write answers family (some result.1)⟩

def byteStep {n : Nat} {S : Type} (run : Fin n → S → Bool × S)
    (family : Fin n) (scratch : S) (bytes : ByteTable n) : Option (StepResult S (ByteTable n)) :=
  match decode (bytes family) with
  | none => none
  | some (some answer) => some ⟨answer, scratch, bytes⟩
  | some none =>
    let result := run family scratch
    some ⟨result.1, result.2, write bytes family (encode (some result.1))⟩

/-- Valid slots choose exactly the logical memo branch, preserve answer and
    scratch, and keep the representation invariant after a first miss. -/
theorem byte_step_refines_logical_step {n : Nat} {S : Type}
    (run : Fin n → S → Bool × S) (family : Fin n) (scratch : S)
    (bytes : ByteTable n) (answers : AnswerTable n) (valid : Represents bytes answers) :
    ∃ physical, byteStep run family scratch bytes = some physical ∧
      physical.answer = (logicalStep run family scratch answers).answer ∧
      physical.scratch = (logicalStep run family scratch answers).scratch ∧
      Represents physical.table (logicalStep run family scratch answers).table := by
  cases ha : answers family with
  | some answer =>
    refine ⟨⟨answer, scratch, bytes⟩, ?_, ?_, ?_, ?_⟩
    · simp only [byteStep, valid family, ha]
    · simp only [logicalStep, ha]
    · simp only [logicalStep, ha]
    · simpa only [logicalStep, ha] using valid
  | none =>
    let result := run family scratch
    refine ⟨⟨result.1, result.2, write bytes family (encode (some result.1))⟩, ?_, ?_, ?_, ?_⟩
    · simp only [byteStep, valid family, ha, result]
    · simp only [logicalStep, ha, result]
    · simp only [logicalStep, ha, result]
    · simpa only [logicalStep, ha, result] using
        write_preserves_representation bytes answers valid family result.1

/-- Family IDs are freeze-array indices, not payload equality or method IDs.
    Equal payloads may have different IDs; indexing introduces no equality or
    hash definition for Owners or any analyzer fact. -/
def ownerAt {n : Nat} {Payload : Type} (payload : Fin n → Payload) (id : Fin n) :
    Fin n × Payload := (id, payload id)

theorem owner_id_injective {n : Nat} {Payload : Type} (payload : Fin n → Payload)
    (a b : Fin n) (same : (ownerAt payload a).1 = (ownerAt payload b).1) : a = b := same

theorem owner_payload_unchanged {n : Nat} {Payload : Type}
    (payload : Fin n → Payload) (id : Fin n) : (ownerAt payload id).2 = payload id := rfl

theorem invalid_slot_is_not_cached_false : decode 3 = none := by decide

def check : Bool :=
  ownersThenKeep (fun x : Nat => x % 2 == 0) (fun x => x < 4) [0, 1, 2, 3, 4, 5] ==
    keepThenOwners (fun x : Nat => x % 2 == 0) (fun x => x < 4) [0, 1, 2, 3, 4, 5] &&
  decode (encode (some false)) == some (some false) &&
  decode (encode (some true)) == some (some true)

theorem checked : check = true := by decide

#eval check
#print axioms early_filter_preserves_rows
#print axioms early_filter_preserves_decoded_outputs
#print axioms slot_round_trip
#print axioms write_preserves_representation
#print axioms byte_step_refines_logical_step
#print axioms owner_id_injective

end DemandImplementationContracts
