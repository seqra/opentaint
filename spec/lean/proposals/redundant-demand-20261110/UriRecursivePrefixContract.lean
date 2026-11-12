import Std

namespace UriRecursivePrefixContract
/- Effects have arbitrary metadata. One complete native-scope adapter must
   identify the finite recursive dependencies used in each genuine local
   derivation. The local postfixed check is not a historical snapshot claim. -/
mutual
inductive Derivation {Effect : Type} (body : List Effect → Effect → Prop) : Effect → Prop
  | bodyStep (uses : List Effect) (out : Effect)
      (dependencies : Dependencies body uses) (execution : body uses out) : Derivation body out
inductive Dependencies {Effect : Type} (body : List Effect → Effect → Prop) : List Effect → Prop
  | none : Dependencies body []
  | more (head : Effect) (tail : List Effect) (one : Derivation body head)
      (others : Dependencies body tail) : Dependencies body (head :: tail)
end

def Postfixed {Effect : Type} (body : List Effect → Effect → Prop) (keep : Effect → Prop) : Prop :=
  ∀ uses out, (∀ input, input ∈ uses → keep input) → body uses out → keep out

private theorem keep_cons {Effect : Type} {keep : Effect → Prop}
    (head : Effect) (tail : List Effect) (first : keep head)
    (rest : ∀ e, e ∈ tail → keep e) : ∀ out, out ∈ head :: tail → keep out := by
  intro out member
  rcases List.mem_cons.mp member with equal | inner
  · subst out
    exact first
  · exact rest out inner

theorem derivation_is_covered {Effect : Type} {body : List Effect → Effect → Prop}
    {keep : Effect → Prop} (closed : Postfixed body keep) (out : Effect)
    (run : Derivation body out) : keep out :=
  Derivation.rec (motive_1 := fun effect _ => keep effect)
    (motive_2 := fun effects _ => ∀ e, e ∈ effects → keep e)
    (fun uses out _ execution ih => closed uses out ih execution)
    (by simp)
    (fun head tail _ _ first rest => keep_cons head tail first rest) run

theorem dependencies_are_covered {Effect : Type} {body : List Effect → Effect → Prop}
    {keep : Effect → Prop} (closed : Postfixed body keep) (uses : List Effect)
    (run : Dependencies body uses) : ∀ out, out ∈ uses → keep out :=
  Dependencies.rec (motive_1 := fun effect _ => keep effect)
    (motive_2 := fun effects _ => ∀ e, e ∈ effects → keep e)
    (fun uses out _ execution ih => closed uses out ih execution)
    (by simp)
    (fun head tail _ _ first rest => keep_cons head tail first rest) run

/- Tag any genuine derivation by the mark tested at the boundary. A second
   checked postfixed body with the full mask event disabled proves that a
   marked witness excluded by that event cannot add a return prefix. -/
structure Effect where
  inputBase : Nat
  outputBase : Nat
  inputPrefix : List Nat
  outputPrefix : List Nat
  mark : Nat
  deriving DecidableEq

def keepsCopy (ordinary allowedWithoutMask : Effect → Prop) (mask : List Nat) (effect : Effect) : Prop :=
  ordinary effect ∧ (effect.mark ∈ mask → allowedWithoutMask effect)

theorem dual_postfixed {body : List Effect → Effect → Prop}
    {ordinary allowedWithoutMask : Effect → Prop} {mask : List Nat}
    (geom : Postfixed body ordinary)
    (without : ∀ uses out, (∀ e, e ∈ uses → keepsCopy ordinary allowedWithoutMask mask e) →
      body uses out → out.mark ∈ mask → allowedWithoutMask out) :
    Postfixed body (keepsCopy ordinary allowedWithoutMask mask) := by
  intro uses out children execution
  exact ⟨geom uses out (fun e member => (children e member).1) execution,
    without uses out children execution⟩

theorem masked_derivation_has_root {body : List Effect → Effect → Prop}
    {ordinary allowedWithoutMask : Effect → Prop} {mask : List Nat}
    (closed : Postfixed body (keepsCopy ordinary allowedWithoutMask mask))
    (root : ∀ e, allowedWithoutMask e → e.outputPrefix = [])
    (effect : Effect) (run : Derivation body effect) (masked : effect.mark ∈ mask) :
    effect.outputPrefix = [] :=
  root effect ((derivation_is_covered closed effect run).2 masked)

end UriRecursivePrefixContract
#print axioms UriRecursivePrefixContract.derivation_is_covered
#print axioms UriRecursivePrefixContract.dependencies_are_covered
#print axioms UriRecursivePrefixContract.dual_postfixed
#print axioms UriRecursivePrefixContract.masked_derivation_has_root
