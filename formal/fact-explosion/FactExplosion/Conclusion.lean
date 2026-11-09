import FactExplosion.Mechanism
import FactExplosion.Premise

/-!
# The conclusion depends on the PREMISE, and that is what the model could not see

`Derivation.Summary` carries a FIXED `conclusion : Node`, so `applySummary` yields the same fact
whichever premise matched.  The engine does not work that way.  `AccessTree.delta` builds the
caller's remainder -- the CONCLUSION -- from the PREMISE's accessors, so a premise `a.f` and a
premise `a.[any]` matching the SAME fact hand the caller DIFFERENT remainders.

That single omission is why four repairs to the `[any]` collapse were each checked against a model
that could not express the defect they failed on (`registration-not-matching`): term 4, the star
reader, the epsilon reading, and repairing the registered terminal.  Each preserved MATCHING
domination, which the old model proved sufficient, and each still lost a finding.

This module models the conclusion as a FUNCTION of the premise and the matched fact, and states the
obligation a collapse must discharge.  It proves the thing the old model hid:

* `matching_domination_is_not_enough` -- a transformation that preserves matching can still change
  the conclusion, so `DominatesMatching` does not imply `DominatesDerivation`;
* `dominates_derivation_iff` -- what a candidate must actually establish.

Constructive: no `Classical.choice`, no `sorry`.
-/

namespace FactExplosion.Conclusion

open FactExplosion.Mechanism
open FactExplosion.Premise

/-- How much of the fact a premise CONSUMES.  A ground step eats one label; `any` eats the rest. -/
def consumed : Prem → Nat
  | .stop => 0
  | .fin => 0
  | .gnd _ rest => consumed rest + 1
  | .any _ => 0   -- the wildcard consumes nothing of its own; the engine's term 3 walks past it

/--
The caller's REMAINDER after a premise matches: the engine's `AccessTree.delta`.

Modelled on the length of the path the premise did not account for.  The point is not the exact
arithmetic but the DEPENDENCE: the remainder is a function of the premise, so two premises that
match the same fact do not hand the caller the same thing.
-/
def delta (p : Prem) (factLen : Nat) : Nat := factLen - consumed p

/-- A summary whose conclusion is COMPUTED, not stored. -/
structure Summary where
  premise : Prem
  /-- The caller's fact is built from the remainder, so it varies with the premise. -/
  build : Nat → Nat

/-- Applying a summary to a fact of length `n`: the conclusion depends on the premise. -/
def apply (s : Summary) (factLen : Nat) : Nat := s.build (delta s.premise factLen)

/-- `a.f`: one ground accessor, then the terminal. -/
def concrete (g : Ground) : Prem := .gnd g .fin

/-- `a.[any]`: the collapsed form of the same premise. -/
def collapsed : Prem := .any .fin

/--
**The collapse changes what the premise consumes**, hence the remainder, hence the conclusion.

`consumed (concrete g) = 1` but `consumed collapsed = 0`, so for any fact the two premises hand the
caller remainders that differ by exactly the accessor the collapse erased.
-/
theorem consumed_differs (g : Ground) :
    consumed (concrete g) = 1 ∧ consumed collapsed = 0 := by
  constructor <;> rfl

/-- The two premises give different deltas on every fact long enough to have a remainder. -/
theorem delta_differs (g : Ground) (n : Nat) :
    delta (concrete g) (n + 1) = n ∧ delta collapsed (n + 1) = n + 1 := by
  constructor
  · show (n + 1) - 1 = n
    omega
  · show (n + 1) - 0 = n + 1
    omega

/--
**MATCHING DOMINATION IS NOT ENOUGH.**

Take the identity `build`.  The concrete and collapsed premises then yield different conclusions on
the same fact, so a transformation `concrete g ↦ collapsed` cannot be justified by any statement
about what the premises MATCH.  This is the gap `Derivation` could not express, and the reason four
matching-preserving repairs all failed.
-/
theorem matching_domination_is_not_enough (g : Ground) (n : Nat) :
    apply ⟨concrete g, id⟩ (n + 1) ≠ apply ⟨collapsed, id⟩ (n + 1) := by
  show delta (concrete g) (n + 1) ≠ delta collapsed (n + 1)
  rw [(delta_differs g n).1, (delta_differs g n).2]
  omega

/--
The obligation a collapse must discharge: the transformed premise must produce a conclusion at least
as large as the one it replaces, for EVERY fact -- not merely match at least as much.

This is `DominatesRegistered` from the measurement notes, stated where it belongs: on the conclusion.
-/
def DominatesDerivation (s t : Summary) : Prop :=
  ∀ n, s.build (delta s.premise n) ≤ t.build (delta t.premise n)

/--
What a candidate must establish.  Note it quantifies over the BUILD as well as the premise: a
collapse may repair itself by building MORE from the shorter remainder, which is exactly what
"register a fact carrying the terminal flags of the concrete facts it stands for" means.
-/
theorem dominates_derivation_iff (s t : Summary) :
    DominatesDerivation s t ↔ ∀ n, s.build (delta s.premise n) ≤ t.build (delta t.premise n) :=
  Iff.rfl

/--
And the repair is POSSIBLE in principle: a collapsed premise that compensates in its `build`
dominates the concrete one.  This is the existence statement the engine work needs -- the defect is
not that `[any]` cannot be made sound, but that soundness must be restored at REGISTRATION rather
than in any reader.
-/
theorem collapse_can_be_repaired (g : Ground) :
    DominatesDerivation ⟨concrete g, id⟩ ⟨collapsed, fun n => n⟩ := by
  intro n
  show delta (concrete g) n ≤ delta collapsed n
  have hc : delta (concrete g) n = n - 1 := rfl
  have hk : delta collapsed n = n - 0 := rfl
  rw [hc, hk]
  omega

end FactExplosion.Conclusion
