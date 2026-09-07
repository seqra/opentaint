import FactExplosion.Canonical

namespace FactExplosion

def excludesFieldZero : AccessTree :=
  .node true false (some ⟨[0], []⟩) .nil

def excludesFieldOne : AccessTree :=
  .node true false (some ⟨[1], []⟩) .nil

def keyWithoutExclusion : AccessTree -> Bool × Bool × Branches
  | .node abstract final _ children => (abstract, final, children)

theorem exclusion_changes_semantics :
    accepts 1 excludesFieldZero [.field 0] = false ∧
    accepts 1 excludesFieldOne [.field 0] = true := by
  simp [accepts, acceptsBranches, abstractAccepts, DeepExclusion.contains,
    excludesFieldZero, excludesFieldOne]

theorem key_without_exclusion_collides :
    keyWithoutExclusion excludesFieldZero = keyWithoutExclusion excludesFieldOne := by
  rfl

theorem exclusion_must_be_in_key :
    keyWithoutExclusion excludesFieldZero = keyWithoutExclusion excludesFieldOne ∧
    accepts 1 excludesFieldZero [.field 0] ≠ accepts 1 excludesFieldOne [.field 0] := by
  have semantics := exclusion_changes_semantics
  exact ⟨key_without_exclusion_collides, by simp [semantics.1, semantics.2]⟩

theorem full_key_distinguishes_exclusion : excludesFieldZero ≠ excludesFieldOne := by
  decide

end FactExplosion
