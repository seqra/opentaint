/- Scope review witness only. It is not another runtime policy.
   Static permission composition keeps the outer endpoint patterns. Applying
   ordinary AP binding to such a permission product need not commute as exact
   header equality with binding the primitive writer first. The selected
   implementation binds writer SEEDS before the separate static closure.
-/
import ApSpec.Run1CorrelatedConcreteInitials

namespace RestrictedDemand.WriterBindingScope
open ApSpec ApSpec.Run1CorrelatedConcreteInitials
set_option autoImplicit false

/-- 99 is the uncounted class tag. The named fields and h are counted. -/
def counted (a : Acc) : Bool := !(Nat.beq a 99)

def input : AFact := ⟨⟨3,[12],.exact,.conc 7⟩,true⟩
def writerFrom : PFact := ⟨3,[],.star Excl.empty,.conc 7⟩
def writerTo : PFact := ⟨4,[99,10],.exact,.conc 8⟩
def bridgeFrom : PFact := ⟨4,[99,10],.star Excl.empty,.star⟩
def bridgeTo : PFact := ⟨4,[99,11],.star Excl.empty,.star⟩

/-- The mapped writer followed by a FLOW bridge keeps the outer STAR target
    and the mapped output mark U. This is a guidance key, not a body summary. -/
def composedTo : PFact := { bridgeTo with mark := .conc 8 }

def bindThenBound (target : PFact) : List AFact :=
  (rawApply input writerFrom target).facts.map (limitF counted 1)

/-- STATIC-MIDDLE keeps the right outer target and transports the actual
    mapped output mark. It does not apply the bridge as a program operation. -/
def outerPermission (boundWriter : AFact) : AFact :=
  ⟨{ bridgeTo with mark := boundWriter.fact.mark },boundWriter.demand⟩

def composedThenBound : List AFact := bindThenBound composedTo
def boundThenCompose : List AFact := (bindThenBound writerTo).map outerPermission

/-- The middle is a real compatible static field/mark point, not a divergent path. -/
theorem compatible_static_middle :
    writerTo.covers ⟨4,[99,10],8⟩ ∧ bridgeFrom.covers ⟨4,[99,10],8⟩ := by
  exact ⟨⟨rfl,⟨[],rfl,rfl⟩,rfl⟩,⟨rfl,⟨[],rfl,rfl⟩,trivial⟩⟩

theorem actual_primitive_writer_binding :
    bindThenBound writerTo = [⟨writerTo,true⟩] := rfl

theorem actual_binding_of_composed_permission_before_limit :
    (rawApply input writerFrom composedTo).facts =
      [⟨⟨4,[99,11,12],.exact,.conc 8⟩,true⟩] := rfl

theorem composed_binding_is_ANY_after_limit :
    composedThenBound = [⟨⟨4,[99,11],.any,.conc 8⟩,true⟩] := rfl

theorem primitive_binding_then_permission_is_STAR :
    boundThenCompose = [⟨⟨4,[99,11],.star Excl.empty,.conc 8⟩,true⟩] := rfl

/-- Exact header commutation is false. This does not assert a missed concrete
    demanded path, nor does it compare whole program observations. -/
theorem no_exact_header_commutation : composedThenBound ≠ boundThenCompose := by
  intro same
  have kinds := congrArg (List.map (fun f : AFact => f.fact.kind)) same
  change [Kind.any] = [Kind.star Excl.empty] at kinds
  cases kinds

#print axioms compatible_static_middle
#print axioms actual_primitive_writer_binding
#print axioms actual_binding_of_composed_permission_before_limit
#print axioms composed_binding_is_ANY_after_limit
#print axioms primitive_binding_then_permission_is_STAR
#print axioms no_exact_header_commutation
end RestrictedDemand.WriterBindingScope
