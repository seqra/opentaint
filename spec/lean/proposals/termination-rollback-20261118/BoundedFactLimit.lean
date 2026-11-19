/- A coordinate includes the field path, mark and the leaf kind. -/

def limitMember (member : Bool) (depth budget : Nat) : Bool :=
  member && decide (depth ≤ budget)

def overflowMember (member : Bool) (depth budget : Nat) : Bool :=
  member && !(decide (depth ≤ budget))

theorem boundedRetainsAll (member : Bool) (depth budget : Nat)
    (within : member = true → depth ≤ budget) :
    limitMember member depth budget = member ∧
    overflowMember member depth budget = false := by
  cases member
  · exact ⟨rfl, rfl⟩
  · simp [limitMember, overflowMember, within rfl]

def restoreProtection (member ordinary transported exact : Bool) : Bool :=
  (ordinary || ((transported && exact) || (transported && !exact))) && member

theorem boundedProtectionIsIdentity (member mask exact : Bool)
    (subset : mask = true → member = true) :
    restoreProtection member mask mask exact = mask := by
  cases mask
  · cases member <;> cases exact <;> rfl
  · have yes := subset rfl
    subst member
    cases exact <;> rfl

theorem fullyProtectedBoundedPacket {Location : Type}
    (depth : Location → Nat) (member exact : Location → Bool) (budget : Nat)
    (within : ∀ i, member i = true → depth i ≤ budget) :
    ∀ i, limitMember (member i) (depth i) budget = member i ∧
      overflowMember (member i) (depth i) budget = false ∧
      restoreProtection (member i) (member i)
        (limitMember (member i) (depth i) budget) (exact i) = member i := by
  intro i
  obtain ⟨keep, cut⟩ := boundedRetainsAll (member i) (depth i) budget (within i)
  refine ⟨keep, cut, ?_⟩
  rw [keep]
  exact boundedProtectionIsIdentity (member i) (member i) (exact i) id
