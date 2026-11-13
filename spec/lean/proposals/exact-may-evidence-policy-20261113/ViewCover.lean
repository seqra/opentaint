import Emission

namespace ExactMayViewCover
open ExactMayEmission

-- Ordinary code:
-- choose(x) { if (b) return x.f; else return x.f.g; }
-- f=1, g=2, h=3. Paths below are concrete marked locations.
def transfer (read : Path) (input : Path) : List Path :=
  match dropPrefix read input with | none => [] | some suffix => [suffix]
def code (input : Path) : List Path := transfer [1] input ++ transfer [1,2] input
def retainedNormal (input : Path) : List Path := transfer [1] input

theorem exact_probe_sees_only_first_branch :
    code [1] = [[]] ∧ transfer [1,2] [1] = [] := by decide

theorem both_first_field_starts_are_present :
    emit 3 rootGuide ⟨[1,2,3],.may,fullT,true⟩ =
      [⟨[1],.exact,.flow,false⟩,⟨[1],.may,.flow,true⟩,⟨[],.exact,.flow,false⟩] := by decide

theorem projected_exact_input_has_a_real_missing_root :
    [] ∈ code [1,2] ∧ [] ∉ retainedNormal [1,2] := by decide

-- The user's longer MAY example also has a concrete valid binding with
-- a missing output. Keeping a MAY query at f is material to this binding.
theorem longer_submitted_may_has_a_real_missing_binding :
    [3] ∈ code [1,2,3] ∧ [3] ∉ retainedNormal [1,2,3] := by decide

-- A normalized correlated summary is not a complete method model merely
-- because a MAY probe has the same output head. Both branches must remain
-- represented, by another retained relation or unresolved guidance.
theorem shape_only_provider_is_not_complete :
    ∃ input output, output ∈ code input ∧ output ∉ retainedNormal input :=
  ⟨[1,2],[],projected_exact_input_has_a_real_missing_root⟩

#print axioms exact_probe_sees_only_first_branch
#print axioms both_first_field_starts_are_present
#print axioms projected_exact_input_has_a_real_missing_root
#print axioms longer_submitted_may_has_a_real_missing_binding
#print axioms shape_only_provider_is_not_complete
end ExactMayViewCover
