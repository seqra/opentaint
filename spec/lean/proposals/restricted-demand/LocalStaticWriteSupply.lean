/-
Selected local supply contract, 2026-10-28.
Scope: production concrete-entry admission and already permitted local writes.
Actual AP matching, complete rule/ND permissions and actor fairness remain
adapter obligations. These finite witnesses are proof data, never runtime state.
This deliberately does not preserve the obsolete outward-rebinding requirement.
-/
import Init

namespace RestrictedDemand.LocalStaticWriteSupply
set_option autoImplicit false

structure Value where
  method : Nat
  geometry : Nat
  mark : Option Nat
  deriving DecidableEq

structure StaticValue where
  region : Nat
  mark : Nat
  deriving DecidableEq

structure FlowWriter where
  originalGeometry : Nat
  outputRegion : Nat
  deriving DecidableEq

abbrev Entered := Nat → Prop
abbrev PermittedStep := Value → Value → Prop
abbrev Requested := Value → Prop
abbrev AnswerMatches := Value → Value → Prop
abbrev CompletedWrite := Value → StaticValue → Prop
abbrev ReadMatches := StaticValue → Value → Prop

/- Structural FLOW policy initials cannot seed concrete production. A concrete
entry needs an actual same-mark input and a matching request. Existing permitted
steps include complete local guards; genuine ZERO starts need real entry. -/
mutual
  inductive Current (entered : Entered) (step : PermittedStep)
      (requested : Requested) (answerMatches : AnswerMatches)
      (write : CompletedWrite) (readMatches : ReadMatches) : Value → Type
    | zero (method geometry : Nat) : entered method →
        Current entered step requested answerMatches write readMatches ⟨method, geometry, none⟩
    | transfer {a b : Value} : Current entered step requested answerMatches write readMatches a →
        step a b → Current entered step requested answerMatches write readMatches b
    | answer {actual initial : Value} (mark : Nat) :
        Current entered step requested answerMatches write readMatches actual →
        actual.mark = some mark → initial.mark = some mark →
        requested initial → answerMatches actual initial →
        Current entered step requested answerMatches write readMatches initial
    | read {s : StaticValue} {result : Value} :
        Supplied entered step requested answerMatches write readMatches s → readMatches s result →
        Current entered step requested answerMatches write readMatches result
  inductive Supplied (entered : Entered) (step : PermittedStep)
      (requested : Requested) (answerMatches : AnswerMatches)
      (write : CompletedWrite) (readMatches : ReadMatches) : StaticValue → Type
    | local {input : Value} {output : StaticValue} :
        Current entered step requested answerMatches write readMatches input → write input output →
        Supplied entered step requested answerMatches write readMatches output
end

structure RootWitness (entered : Entered) where
  method : Nat
  actualEntry : entered method

mutual
  def currentRoot {entered : Entered} {step : PermittedStep}
      {requested : Requested} {answerMatches : AnswerMatches}
      {write : CompletedWrite} {readMatches : ReadMatches} {v : Value}
      (h : Current entered step requested answerMatches write readMatches v) : RootWitness entered :=
    match h with
    | .zero method _ actualEntry => ⟨method, actualEntry⟩
    | .transfer before _ => currentRoot before
    | .answer _ before _ _ _ _ => currentRoot before
    | .read supplied _ => supplyRoot supplied
  def supplyRoot {entered : Entered} {step : PermittedStep}
      {requested : Requested} {answerMatches : AnswerMatches}
      {write : CompletedWrite} {readMatches : ReadMatches} {v : StaticValue}
      (h : Supplied entered step requested answerMatches write readMatches v) : RootWitness entered :=
    match h with
    | .local input _ => currentRoot input
end

theorem no_unentered_supply {entered : Entered} {step : PermittedStep}
    {requested : Requested} {answerMatches : AnswerMatches}
    {write : CompletedWrite} {readMatches : ReadMatches} {v : StaticValue}
    (noEntry : ∀ m, ¬ entered m)
    (h : Supplied entered step requested answerMatches write readMatches v) : False :=
  noEntry (supplyRoot h).method (supplyRoot h).actualEntry

/-- No outgoing summary or additional outward caller binding is required. -/
def supplyAtWrite {entered : Entered} {step : PermittedStep}
    {requested : Requested} {answerMatches : AnswerMatches}
    {write : CompletedWrite} {readMatches : ReadMatches} {input : Value} {output : StaticValue}
    (actual : Current entered step requested answerMatches write readMatches input)
    (executed : write input output) :
    Supplied entered step requested answerMatches write readMatches output := .local actual executed

structure State where
  flowWriters : List FlowWriter
  pool : List StaticValue
  deriving DecidableEq

def insertOnce {α : Type} [DecidableEq α] (value : α) (values : List α) : List α :=
  if value ∈ values then values else value :: values

def onFlowWrite (state : State) (writer : FlowWriter) : State :=
  { state with flowWriters := insertOnce writer state.flowWriters }

def onConcreteWrite (state : State) (value : StaticValue) : State :=
  { state with pool := insertOnce value state.pool }

theorem flow_writer_retained (state : State) (writer : FlowWriter) :
    writer ∈ (onFlowWrite state writer).flowWriters := by
  by_cases h : writer ∈ state.flowWriters <;> simp [onFlowWrite, insertOnce, h]

theorem concrete_write_keeps_flow_writers (state : State) (value : StaticValue) :
    (onConcreteWrite state value).flowWriters = state.flowWriters := rfl

theorem concrete_write_supplies (state : State) (value : StaticValue) :
    value ∈ (onConcreteWrite state value).pool := by
  by_cases h : value ∈ state.pool <;> simp [onConcreteWrite, insertOnce, h]

theorem repeated_write_idempotent (state : State) (value : StaticValue) :
    onConcreteWrite (onConcreteWrite state value) value = onConcreteWrite state value := by
  by_cases h : value ∈ state.pool <;> simp [onConcreteWrite, insertOnce, h]

structure Boundary where
  state : State
  outgoing : Option StaticValue
  normalRecord : Option StaticValue

def executeLocalWrite (state : State) (value : StaticValue)
    (afterExit : Option StaticValue) : Boundary := ⟨onConcreteWrite state value, afterExit, none⟩

theorem exit_independent (state : State) (value : StaticValue)
    (left right : Option StaticValue) :
    (executeLocalWrite state value left).state = (executeLocalWrite state value right).state := rfl

theorem killed_exit_keeps_supply (state : State) (value : StaticValue) :
    value ∈ (executeLocalWrite state value none).state.pool := concrete_write_supplies state value

theorem no_new_normal_record (state : State) (value : StaticValue) (afterExit : Option StaticValue) :
    (executeLocalWrite state value afterExit).normalRecord = none := rfl

inductive MarkMode where
  | full | group
  deriving DecidableEq

def runtimeMark (mode : MarkMode) (groupOf : Nat → Nat) (full : Nat) : Nat :=
  match mode with | .full => full | .group => groupOf full

def outputAtWrite (mode : MarkMode) (groupOf : Nat → Nat) (region outputFullMark : Nat) : StaticValue :=
  ⟨region, runtimeMark mode groupOf outputFullMark⟩

theorem full_keeps_output_mark (groupOf : Nat → Nat) (region output : Nat) :
    (outputAtWrite .full groupOf region output).mark = output := rfl

theorem group_keeps_output_group (groupOf : Nat → Nat) (region output : Nat) :
    (outputAtWrite .group groupOf region output).mark = groupOf output := rfl

/-- A T-to-U action supplies U, not T; it does not assume mark preservation. -/
theorem color_change_output (state : State) (region input output : Nat) (_ : input ≠ output) :
    (⟨region, output⟩ : StaticValue) ∈ (onConcreteWrite state ⟨region, output⟩).pool :=
  concrete_write_supplies state ⟨region, output⟩

#print axioms currentRoot
#print axioms supplyRoot
#print axioms no_unentered_supply
#print axioms supplyAtWrite
#print axioms flow_writer_retained
#print axioms concrete_write_keeps_flow_writers
#print axioms concrete_write_supplies
#print axioms repeated_write_idempotent
#print axioms exit_independent
#print axioms killed_exit_keeps_supply
#print axioms no_new_normal_record
#print axioms full_keeps_output_mark
#print axioms group_keeps_output_group
#print axioms color_change_output
end RestrictedDemand.LocalStaticWriteSupply
