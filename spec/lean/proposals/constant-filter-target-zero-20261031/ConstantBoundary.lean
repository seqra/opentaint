import Init

/-!
Constant-base exclusion for the selected bidirectional engine, 2026-10-31.

This is a constructive boundary model, not a proof that removing constant AP
facts preserves all old findings. Raw AP/rule/binding evaluation is a parameter.
Every executable intermediate, callback and stored value must cross `admit`.
The same gate is used at arrivals and emissions. In particular a source-hit
callback is an emission, rather than an observation allowed before this gate.

The arbitrary payload stands for fields, tails, marks, exclusions, layers and
protection. No payload is rewritten. A whole ND key is rejected if any member
has a Constant base; filtering members would weaken a condition and is absent.
Production cardinality, K6, canonical ZERO and AP geometry laws are separate.

Target constructors have no AP base. This module proves only that constant
exclusion preserves them for a valid premise. Their selected paired C5 and
label/layer/report rules are specified independently in TargetZeroKernel.lean.
-/
namespace ConstantBoundary
set_option autoImplicit false

inductive Base where
  | local (id : Nat)
  | argument (id : Nat)
  | thisRef
  | returnValue
  | staticField (id : Nat)
  | constant (id : Nat)
  deriving DecidableEq, Repr

def Base.allowed : Base → Bool
  | .constant _ => false
  | _ => true

structure DataFact where
  base : Base
  payload : List Nat
  deriving DecidableEq, Repr

def DataFact.allowed (f : DataFact) : Bool := f.base.allowed

inductive Premise where
  | zero
  | one (member : DataFact)
  | nd (members : List DataFact)
  deriving DecidableEq, Repr

def Premise.members : Premise → List DataFact
  | .zero => []
  | .one member => [member]
  | .nd members => members

def Premise.allowed (p : Premise) : Bool := p.members.all DataFact.allowed

inductive Fact where
  | zero
  | data (value : DataFact)
  | normalTarget (reportId : Nat)
  | demandTarget
  deriving DecidableEq, Repr

def Fact.allowed : Fact → Bool
  | .data f => f.allowed
  | _ => true

structure Packet where
  owner : Nat
  premise : Premise
  conclusion : Fact
  metadata : List Nat
  deriving DecidableEq, Repr

def Packet.allowed (p : Packet) : Bool := p.premise.allowed && p.conclusion.allowed

/-- Each producer/arrival returns either its original whole packet or nothing. -/
def admit (p : Packet) : Option Packet := if p.allowed then some p else none

theorem admitted_iff (p q : Packet) :
    admit p = some q ↔ p.allowed = true ∧ p = q := by
  by_cases permitted : p.allowed = true
  · simp [admit, permitted]
  · simp [admit, permitted]

theorem admitted_allowed {p q : Packet} (accepted : admit p = some q) :
    q.allowed = true := by
  obtain ⟨permitted, same⟩ := (admitted_iff p q).mp accepted
  rw [← same]
  exact permitted

theorem admitted_unchanged {p q : Packet} (accepted : admit p = some q) : q = p :=
  ((admitted_iff p q).mp accepted).2.symm

theorem allowed_admitted (p : Packet) (permitted : p.allowed = true) :
    admit p = some p := by
  exact (admitted_iff p p).mpr ⟨permitted, rfl⟩

theorem constant_base_disallowed (id : Nat) : Base.allowed (.constant id) = false := rfl

theorem constant_conclusion_rejected (owner : Nat) (premise : Premise)
    (id : Nat) (payload metadata : List Nat) :
    admit ⟨owner, premise, .data ⟨.constant id, payload⟩, metadata⟩ = none := by
  simp [admit, Packet.allowed, Fact.allowed, DataFact.allowed, Base.allowed]

theorem admitted_data_base_not_constant {p q : Packet} (accepted : admit p = some q)
    (f : DataFact) (dataConclusion : q.conclusion = .data f) (id : Nat) :
    f.base ≠ .constant id := by
  intro forbidden
  have allowed := admitted_allowed accepted
  simp [Packet.allowed, dataConclusion, Fact.allowed, DataFact.allowed, forbidden,
    Base.allowed] at allowed

theorem premise_member_allowed {p : Premise} (permitted : p.allowed = true)
    (f : DataFact) (member : f ∈ p.members) : f.allowed = true := by
  exact List.all_eq_true.mp permitted f member

theorem admitted_premise_member_not_constant {p q : Packet}
    (accepted : admit p = some q) (f : DataFact) (member : f ∈ q.premise.members)
    (id : Nat) : f.base ≠ .constant id := by
  have permitted := admitted_allowed accepted
  have both : q.premise.allowed = true ∧ q.conclusion.allowed = true := by
    simpa only [Packet.allowed, Bool.and_eq_true] using permitted
  have premiseAllowed := both.1
  have factAllowed := premise_member_allowed premiseAllowed f member
  intro forbidden
  simp [DataFact.allowed, forbidden, Base.allowed] at factAllowed

/-- One disallowed conjunct rejects the entire key; no smaller key is emitted. -/
theorem nd_with_constant_rejected (owner : Nat) (members : List DataFact)
    (conclusion : Fact) (metadata : List Nat) (f : DataFact)
    (member : f ∈ members) (id : Nat) (forbidden : f.base = .constant id) :
    admit ⟨owner, .nd members, conclusion, metadata⟩ = none := by
  have invalid : Premise.allowed (.nd members) ≠ true := by
    intro permitted
    have factAllowed := premise_member_allowed permitted f member
    simp [DataFact.allowed, forbidden, Base.allowed] at factAllowed
  simp [admit, Packet.allowed, invalid]

theorem nd_not_weakened {owner : Nat} {members : List DataFact}
    {conclusion : Fact} {metadata : List Nat} {out : Packet}
    (accepted : admit ⟨owner, .nd members, conclusion, metadata⟩ = some out) :
    out.premise = .nd members ∧ out.conclusion = conclusion ∧
      out.owner = owner ∧ out.metadata = metadata := by
  have same := admitted_unchanged accepted
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem static_final_field_allowed (id : Nat) : Base.allowed (.staticField id) = true := rfl

theorem zero_with_valid_premise_preserved (owner : Nat) (premise : Premise)
    (metadata : List Nat) (permitted : premise.allowed = true) :
    admit ⟨owner, premise, .zero, metadata⟩ =
      some ⟨owner, premise, .zero, metadata⟩ := by
  apply allowed_admitted
  simp [Packet.allowed, permitted, Fact.allowed]

theorem targets_with_valid_premise_preserved (owner : Nat) (premise : Premise)
    (metadata : List Nat) (reportId : Nat) (permitted : premise.allowed = true) :
    admit ⟨owner, premise, .normalTarget reportId, metadata⟩ =
      some ⟨owner, premise, .normalTarget reportId, metadata⟩ ∧
    admit ⟨owner, premise, .demandTarget, metadata⟩ =
      some ⟨owner, premise, .demandTarget, metadata⟩ := by
  constructor <;> apply allowed_admitted <;>
    simp [Packet.allowed, permitted, Fact.allowed]

/-- A callback has no authority to observe a rejected packet. -/
inductive CallbackKind where
  | sourceHit | sinkWitness | markRequest | callInput | pointInput | store | handoff
  deriving DecidableEq, Repr

structure Callback where
  kind : CallbackKind
  packet : Packet
  deriving DecidableEq, Repr

def emit (c : Callback) : Option Callback := (admit c.packet).map fun p => {c with packet := p}

theorem emission_iff (c out : Callback) :
    emit c = some out ↔ c.packet.allowed = true ∧ c = out := by
  by_cases permitted : c.packet.allowed = true
  · simp [emit, admit, permitted]
  · simp [emit, admit, permitted]

theorem emitted_allowed {c out : Callback} (emitted : emit c = some out) :
    out.packet.allowed = true := by
  obtain ⟨permitted, same⟩ := (emission_iff c out).mp emitted
  rw [← same]
  exact permitted

theorem rejected_has_no_callback (kind : CallbackKind) (p : Packet)
    (rejected : admit p = none) : emit ⟨kind, p⟩ = none := by
  simp [emit, rejected]

/-- Stores retain emitted packets only. This boundary has no ND member filter. -/
def save (p : Packet) (state : List Packet) : List Packet :=
  match admit p with
  | none => state
  | some admitted => admitted :: state

def ConstantFreeState (state : List Packet) : Prop :=
  ∀ p, p ∈ state → p.allowed = true

theorem save_preserves_constant_free (p : Packet) (state : List Packet)
    (safe : ConstantFreeState state) : ConstantFreeState (save p state) := by
  intro q member
  unfold save at member
  cases accepted : admit p with
  | none =>
      simp only [accepted] at member
      exact safe q member
  | some admitted =>
      simp only [accepted, List.mem_cons] at member
      rcases member with same | old
      · rw [same]
        exact admitted_allowed accepted
      · exact safe q old

/-- Raw evaluation is unchanged; only whole input/output admission is selected. -/
def step (raw : Packet → List Packet) (input : Packet) : List Packet :=
  if input.allowed then (raw input).filter Packet.allowed else []

theorem conditional_nonconstant_step_preservation (raw : Packet → List Packet)
    (input output : Packet) (inputAllowed : input.allowed = true)
    (oldStep : output ∈ raw input) (outputAllowed : output.allowed = true) :
    output ∈ step raw input := by
  simp only [step, inputAllowed, ↓reduceIte, List.mem_filter]
  exact ⟨oldStep, outputAllowed⟩

theorem selected_step_is_old_step (raw : Packet → List Packet)
    (input output : Packet) (selected : output ∈ step raw input) :
    input.allowed = true ∧ output ∈ raw input ∧ output.allowed = true := by
  by_cases permitted : input.allowed = true
  · simp only [step, permitted, ↓reduceIte, List.mem_filter] at selected
    exact ⟨permitted, selected⟩
  · simp [step, permitted] at selected

inductive RawRoute (raw : Packet → List Packet) : Packet → Packet → Prop where
  | refl (p : Packet) : RawRoute raw p p
  | next {start middle finish : Packet} :
      middle ∈ raw start → RawRoute raw middle finish → RawRoute raw start finish

/-- This evidence requires EVERY executable intermediate to be nonconstant. -/
inductive SafeRoute (raw : Packet → List Packet) : Packet → Packet → Prop where
  | refl (p : Packet) (safe : p.allowed = true) : SafeRoute raw p p
  | next {start middle finish : Packet} :
      start.allowed = true → middle.allowed = true → middle ∈ raw start →
      SafeRoute raw middle finish → SafeRoute raw start finish

theorem safe_route_preserved {raw : Packet → List Packet} {start finish : Packet}
    (route : SafeRoute raw start finish) : RawRoute (step raw) start finish := by
  induction route with
  | refl p _ => exact .refl p
  | next firstSafe nextSafe oldStep _ induction =>
      exact .next (conditional_nonconstant_step_preservation raw _ _ firstSafe oldStep nextSafe) induction

/-- The instruction stream is an independent input. Literal operands survive. -/
inductive Instruction where
  | literalAssignment (localId literalId : Nat)
  | literalArgument (callId position literalId : Nat)
  | staticFinalRead (localId fieldId : Nat)
  | other (id : Nat)
  deriving DecidableEq, Repr

def selectedInstructions (instructions : List Instruction) : List Instruction := instructions

theorem literal_ir_preserved (instructions : List Instruction) :
    selectedInstructions instructions = instructions := rfl

namespace Controls

def ordinary : DataFact := ⟨.argument 0, [7, 8, 9]⟩
def forbidden : DataFact := ⟨.constant 1, [2, 3, 4]⟩
def statik : DataFact := ⟨.staticField 11, [5, 6]⟩
def ordinaryPacket : Packet := ⟨0, .one ordinary, .data ordinary, [15]⟩
def finishPacket : Packet := ⟨0, .one ordinary, .data ordinary, [16]⟩
def forbiddenPacket : Packet := ⟨0, .zero, .data forbidden, [15]⟩
def mixedNdPacket : Packet := ⟨0, .nd [ordinary, forbidden], .data ordinary, [15]⟩

example : admit ordinaryPacket = some ordinaryPacket := rfl
example : admit forbiddenPacket = none := rfl
example : admit mixedNdPacket = none := rfl
example : admit ⟨0, .one ordinary, .data statik, []⟩ =
    some ⟨0, .one ordinary, .data statik, []⟩ := rfl
example : emit ⟨.sourceHit, forbiddenPacket⟩ = none := rfl
example : emit ⟨.sinkWitness, forbiddenPacket⟩ = none := rfl

/-- A nonconstant endpoint alone is insufficient: a constant intermediate is
    intentionally removed, so no full old-program no-FN claim follows. -/
def bridgeThroughConstant (p : Packet) : List Packet :=
  if p == ordinaryPacket then [forbiddenPacket]
  else if p == forbiddenPacket then [finishPacket] else []

theorem old_constant_intermediate_exists :
    RawRoute bridgeThroughConstant ordinaryPacket finishPacket := by
  apply RawRoute.next (middle := forbiddenPacket)
  · decide
  · apply RawRoute.next (middle := finishPacket)
    · decide
    · exact .refl finishPacket

theorem selected_first_constant_step_removed :
    step bridgeThroughConstant ordinaryPacket = [] := by decide

theorem no_route_from_empty_step (raw : Packet → List Packet) (start finish : Packet)
    (empty : raw start = []) (different : start ≠ finish) :
    ¬ RawRoute raw start finish := by
  intro route
  cases route with
  | refl _ => exact different rfl
  | next member _ => simp [empty] at member

theorem lost_route_is_intentional :
    ¬ RawRoute (step bridgeThroughConstant) ordinaryPacket finishPacket := by
  exact no_route_from_empty_step _ _ _ selected_first_constant_step_removed (by decide)

theorem all_controls :
    admit ordinaryPacket = some ordinaryPacket ∧
    admit forbiddenPacket = none ∧ admit mixedNdPacket = none ∧
    emit ⟨.sourceHit, forbiddenPacket⟩ = none ∧
    step bridgeThroughConstant ordinaryPacket = [] := by decide

end Controls

#print axioms admitted_allowed
#print axioms admitted_unchanged
#print axioms constant_conclusion_rejected
#print axioms admitted_data_base_not_constant
#print axioms admitted_premise_member_not_constant
#print axioms nd_with_constant_rejected
#print axioms nd_not_weakened
#print axioms zero_with_valid_premise_preserved
#print axioms targets_with_valid_premise_preserved
#print axioms emitted_allowed
#print axioms rejected_has_no_callback
#print axioms save_preserves_constant_free
#print axioms conditional_nonconstant_step_preservation
#print axioms selected_step_is_old_step
#print axioms safe_route_preserved
#print axioms literal_ir_preserved
#print axioms Controls.old_constant_intermediate_exists
#print axioms Controls.lost_route_is_intentional
#print axioms Controls.all_controls

end ConstantBoundary
