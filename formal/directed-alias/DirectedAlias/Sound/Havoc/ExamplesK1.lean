import DirectedAlias.Sound.Havoc.Examples

/-!
# The writer's check with depth limit `K = 1`

The same queries as `strict_answers`, with `K = 1` (416 universe origins). This file is
separate because the `decide +kernel` check takes about 90 s.
-/

namespace DirectedAlias.Sound.Havoc.Examples

open DirectedAlias DirectedAlias.Examples DirectedAlias.Sound.Havoc

/-- With `K = 1`, per-cell havoc answers false for `a ~ b`, `a ~ z.f`, `a ~ w.g`, and true for
`a ~ x.f` (concept C answers true for the first three, `havoc_spread`). -/
theorem strict_answers_K1 :
    mayProgH true 1 fr pHv va [] vb [] = false ∧
      mayProgH true 1 fr pHv va [] vz [.fld ff] = false ∧
      mayProgH true 1 fr pHv va [] vw [.fld fg] = false ∧
      mayProgH true 1 fr pHv va [] vx [.fld ff] = true := by decide +kernel

end DirectedAlias.Sound.Havoc.Examples
