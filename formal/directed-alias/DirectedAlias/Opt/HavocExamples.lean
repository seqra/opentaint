import DirectedAlias.Opt.Havoc
import DirectedAlias.Sound.Havoc.Examples

/-!
# Runs of O with per-cell havoc

A check of `mayProgHO` on a small program. The universe has 28 origins. Larger universes are
slow under `decide +kernel`, because each call interns one node for each universe cell of each
reachable origin (see `addHv_work`).
-/

namespace DirectedAlias.Opt.Hv

open DirectedAlias DirectedAlias.Examples DirectedAlias.Sound.Havoc
  DirectedAlias.Sound.Havoc.Examples

/-- O with per-cell havoc on `b = new@7; m(b); a = b.f; z = b.g`: `a ~ z` is false,
`a ~ b.f` is true, as in the concept (`new_answers`). -/
theorem o_new_answers :
    mayProgHO true 0 frE pNew va [] vz [] = false ∧
      mayProgHO true 0 frE pNew va [] vb [.fld ff] = true := by decide +kernel

end DirectedAlias.Opt.Hv
