import DirectedAlias.Sound.HavocRecency.Examples

/-!
# The writer's check with depth limit `K = 1`, for recency with per-cell havoc

The same queries as `strict_answersHR`, with `K = 1`. This file is separate because the
`decide +kernel` check is slow.
-/

namespace DirectedAlias.Sound.HavocRecency.Examples

open DirectedAlias DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

/-- With `K = 1`, recency with per-cell havoc answers false for `a ~ b`, `a ~ z.f`, `a ~ w.g`,
and true for `a ~ x.f`. -/
theorem strict_answersHR_K1 :
    mayProgHR true 1 fr pHv va [] vb [] = false ∧
      mayProgHR true 1 fr pHv va [] vz [.fld ff] = false ∧
      mayProgHR true 1 fr pHv va [] vw [.fld fg] = false ∧
      mayProgHR true 1 fr pHv va [] vx [.fld ff] = true := by decide +kernel

end DirectedAlias.Sound.HavocRecency.Examples
