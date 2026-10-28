/- A restriction transports the existing protected memberships through the
   same partial operation as the ordinary value. It creates no new flag. -/
import ApSpec.AbsDefs

namespace RestrictedProtection
set_option autoImplicit false

variable {Input Output : Type}

def transport (operation : Input → Option Output) (flaggedInputs : List Input) : List Output :=
  flaggedInputs.filterMap operation

theorem protected_output_iff (operation : Input → Option Output)
    (flaggedInputs : List Input) (out : Output) :
    out ∈ transport operation flaggedInputs ↔
      ∃ input ∈ flaggedInputs, operation input = some out := by
  simp only [transport, List.mem_filterMap]

/-- A surviving protected leaf keeps its flag at its reduced coordinates. -/
theorem surviving_protection (operation : Input → Option Output)
    (flaggedInputs : List Input) (input : Input) (out : Output)
    (member : input ∈ flaggedInputs) (survives : operation input = some out) :
    out ∈ transport operation flaggedInputs :=
  (protected_output_iff operation flaggedInputs out).mpr ⟨input, member, survives⟩

/-- A flag in the result has an input witness. No unrelated leaf is flagged. -/
theorem no_new_protection (operation : Input → Option Output)
    (flaggedInputs : List Input) (out : Output)
    (flagged : out ∈ transport operation flaggedInputs) :
    ∃ input ∈ flaggedInputs, operation input = some out :=
  (protected_output_iff operation flaggedInputs out).mp flagged

/-- A protected output is ordinary whenever its protected input was ordinary. -/
theorem protected_stays_ordinary (operation : Input → Option Output)
    (ordinary flaggedInputs : List Input)
    (subset : ∀ input, input ∈ flaggedInputs → input ∈ ordinary) (out : Output)
    (flagged : out ∈ transport operation flaggedInputs) :
    out ∈ transport operation ordinary := by
  obtain ⟨input, member, survives⟩ := no_new_protection operation flaggedInputs out flagged
  exact surviving_protection operation ordinary input out (subset input member) survives

#print axioms protected_output_iff
#print axioms surviving_protection
#print axioms no_new_protection
#print axioms protected_stays_ordinary
end RestrictedProtection
