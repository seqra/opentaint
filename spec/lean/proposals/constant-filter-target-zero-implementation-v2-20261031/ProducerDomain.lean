import SelectedCore

/-! Selected typed-producer adapter laws. The production obligations are the
existing K6 kind relation and sink-held REACH/TAINT restriction; this file does
not add a static routing algorithm or relax AP/native-summary applicability. -/
namespace ProducerDomain
open SelectedCore
set_option autoImplicit false

inductive Kind where | reach | taint | flow deriving DecidableEq, Repr
def SinkHeld (kind : Kind) : Prop := kind = .reach ∨ kind = .taint
theorem sink_held_not_flow (kind : Kind) (held : SinkHeld kind) : kind ≠ .flow := by
  rcases held with same | same <;> subst kind <;> intro impossible <;> cases impossible
theorem target_premise_not_flow (premise conclusion : Kind)
    (k6 : conclusion = .flow ↔ premise = .flow) (held : SinkHeld conclusion) : premise ≠ .flow := by
  intro flow
  exact sink_held_not_flow conclusion held (k6.mpr flow)
theorem actual_gen_premise_not_flow (premise : Kind)
    (k6 : Kind.taint = .flow ↔ premise = .flow) : premise ≠ .flow := by
  exact target_premise_not_flow premise .taint k6 (.inr rfl)

structure StaticOrigin where
  owner : Nat
  field : Nat
  mark : Nat
  deriving DecidableEq, Repr
def forceRun1StaticLayer (run1 : Bool) (layer : Layer) : Layer := if run1 then .demand else layer
structure StaticTerminal where
  origin : StaticOrigin
  target : Target
  deriving DecidableEq, Repr
def emitStaticTerminal (run1 : Bool) (origin : StaticOrigin) (layer : Layer) (id : Nat) : StaticTerminal :=
  ⟨origin,Target.fromLayer (forceRun1StaticLayer run1 layer) id⟩
theorem run1_static_is_demand (origin : StaticOrigin) (layer : Layer) (id : Nat) :
    (emitStaticTerminal true origin layer id).target = .demandTarget := rfl
theorem static_descriptor_preserved (run1 : Bool) (origin : StaticOrigin) (layer : Layer) (id : Nat) :
    (emitStaticTerminal run1 origin layer id).origin = origin := rfl

end ProducerDomain
