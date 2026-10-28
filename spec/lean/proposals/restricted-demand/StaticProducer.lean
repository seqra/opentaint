/-
  The selected producer-immediacy interface. Actual AP satisfaction and application
  supply the binding relation below. The two channels use those same bindings.
  This proves route equivalence, not the interpreter's AP contracts or fairness.
-/
import Init

namespace RestrictedDemand.StaticProducer
set_option autoImplicit false

/-- A bound static effect retains its current method original and full geometry. -/
structure Effect where
  owner : Nat
  original : Nat
  staticValue : Nat
  deriving DecidableEq

/-- The caller's stored actual input satisfies the callee's complete original,
    and ordinary AP summary application gives this caller-bound effect. -/
abbrev Binding := Effect → Effect → Prop

/-- A ZERO or globally supplied static original can use the existing pool reducer. -/
abbrev Rooted := Effect → Prop

/-- The previous early-W path: publish the writer, bind it through real callers,
    then add its rooted static value to the pool. -/
inductive EarlySupply (binding : Binding) (rooted : Rooted) : Effect → Prop
  | root {e : Effect} : rooted e → EarlySupply binding rooted e
  | caller {callee caller : Effect} : binding callee caller →
      EarlySupply binding rooted caller → EarlySupply binding rooted callee

/-- The separate producer channel uses the identical actual-input binders. It
    never needs the outgoing post-exit summary to exist. -/
inductive ProducerSupply (binding : Binding) (rooted : Rooted) : Effect → Prop
  | root {e : Effect} : rooted e → ProducerSupply binding rooted e
  | caller {callee caller : Effect} : binding callee caller →
      ProducerSupply binding rooted caller → ProducerSupply binding rooted callee

def earlyToProducer {binding : Binding} {rooted : Rooted} {e : Effect}
    (h : EarlySupply binding rooted e) : ProducerSupply binding rooted e :=
  match h with
  | .root hr => .root hr
  | .caller hb tail => .caller hb (earlyToProducer tail)

def producerToEarly {binding : Binding} {rooted : Rooted} {e : Effect}
    (h : ProducerSupply binding rooted e) : EarlySupply binding rooted e :=
  match h with
  | .root hr => .root hr
  | .caller hb tail => .caller hb (producerToEarly tail)

theorem supply_equivalent {binding : Binding} {rooted : Rooted} {e : Effect} :
    EarlySupply binding rooted e ↔ ProducerSupply binding rooted e :=
  ⟨earlyToProducer, producerToEarly⟩

inductive Channel where
  | exitSummary | producer
  deriving DecidableEq

/-- Producer delivery has no ordinary-summary, record, or CFG route. -/
def executableSummary (channel : Channel) (postExit : Option Effect) : Option Effect :=
  match channel with
  | .exitSummary => postExit
  | .producer => none

def normalRecord (channel : Channel) (postExit : Option Effect) : Option Effect :=
  executableSummary channel postExit

def cfgResult (channel : Channel) (value : Effect) : Option Effect :=
  match channel with
  | .exitSummary => some value
  | .producer => none

theorem producer_has_no_summary (postExit : Option Effect) :
    executableSummary .producer postExit = none := rfl

theorem producer_has_no_record (postExit : Option Effect) :
    normalRecord .producer postExit = none := rfl

theorem producer_has_no_cfg (value : Effect) : cfgResult .producer value = none := rfl

/-- A kill at normal exit cannot cancel an already derived producer supply. -/
theorem exit_kill_keeps_supply {binding : Binding} {rooted : Rooted} {e : Effect}
    (h : EarlySupply binding rooted e) :
    ProducerSupply binding rooted e ∧ executableSummary .exitSummary none = none :=
  ⟨earlyToProducer h, rfl⟩

#check earlyToProducer
#print axioms earlyToProducer
#print axioms producerToEarly
#print axioms supply_equivalent
#print axioms producer_has_no_summary
#print axioms producer_has_no_record
#print axioms producer_has_no_cfg
#print axioms exit_kill_keeps_supply
end RestrictedDemand.StaticProducer
