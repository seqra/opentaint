/-
  Current forward alias selection (interpreter AC3--AC5).

  Origin records the route that produced a result. Each result group has one
  layer; the alias guard also reads that current layer, including demotion by
  cleaners after an identity route. This finite local model proves selection,
  not alias micro-edge application or a complete call-plan traversal.
-/
import Std

namespace ApSpec.CurrentAliasGuard

inductive Origin where
  | source | endFact | pass | summaryEffect | identity
deriving DecidableEq, BEq, Repr

inductive Layer where
  | normal | demand
deriving DecidableEq, BEq, Repr

def oldAdmits (o : Origin) : Bool := o != .identity

def admits (o : Origin) (layer : Layer) : Bool := layer == .demand || o != .identity

theorem demand_passes (o : Origin) : admits o .demand = true := by
  cases o <;> rfl

theorem normal_identity_skips : admits .identity .normal = false := rfl

theorem normal_origin_rule (o : Origin) : admits o .normal = oldAdmits o := rfl

theorem selection_iff (o : Origin) (layer : Layer) :
    admits o layer = true ↔ layer = .demand ∨ o ≠ .identity := by
  cases o <;> cases layer <;> decide

structure Result where
  origin : Origin
  layer : Layer
deriving DecidableEq, BEq, Repr

def aliasInputs (xs : List Result) : List Result :=
  xs.filter fun x => admits x.origin x.layer

theorem demand_retained (xs : List Result) (x : Result) (hx : x ∈ xs)
    (hd : x.layer = .demand) : x ∈ aliasInputs xs := by
  apply List.mem_filter.mpr
  exact ⟨hx, by rw [hd]; exact demand_passes x.origin⟩

namespace Certificate

/-- Default identity, constructor pass-over, and a demoted identity route have
    the same guard inputs: identity origin and the demand layer. -/
def demandIdentity : Result := ⟨.identity, .demand⟩
def normalIdentity : Result := ⟨.identity, .normal⟩
def normalEffect : Result := ⟨.summaryEffect, .normal⟩

theorem old_skips_demand_identity : oldAdmits demandIdentity.origin = false := rfl
theorem current_keeps_demand_identity :
    aliasInputs [demandIdentity] = [demandIdentity] := rfl

def check : Bool := !oldAdmits demandIdentity.origin &&
  aliasInputs [normalIdentity, demandIdentity, normalEffect] == [demandIdentity, normalEffect]

theorem checked : check = true := rfl

end Certificate
end ApSpec.CurrentAliasGuard
