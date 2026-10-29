import DirectedAlias.Opt.Equiv
import DirectedAlias.Examples

/-!
# Examples of optimization O

The O analysis runs on the examples of `Examples.lean`. Each `decide` check runs the O code
(node table, memo, maps). `mayProgO_eq` proves that the answers are the C answers; these checks
only show that the O code runs.
-/

namespace DirectedAlias.Opt.Examples

open DirectedAlias DirectedAlias.Examples DirectedAlias.Opt

/-- O: after the join, `a` may alias `x`. -/
theorem o_join_a_x : mayProgO 2 fr pJoin va [] vx [] = true := by decide +kernel
/-- O: after the join, `x` does not alias `y`. -/
theorem o_join_x_y : mayProgO 2 fr pJoin vx [] vy [] = false := by decide +kernel
/-- O: after `a.f = z; a = w`, `x.f` and `y.f` both may alias `z`, and `a` does not alias `x`. -/
theorem o_field : mayProgO 2 fr pField vx [.fld ff] vz [] = true ∧
    mayProgO 2 fr pField vy [.fld ff] vz [] = true ∧
    mayProgO 2 fr pField va [] vx [] = false := by decide +kernel
/-- O: the strong update removes `x` from `b.f`. -/
theorem o_strong_bf_x : mayProgO 1 fr pStrong vb [.fld ff] vx [] = false := by decide +kernel
/-- O: in the loop the stores are weak. -/
theorem o_loop_bf_x : mayProgO 1 fr pLoop vb [.fld ff] vx [] = true := by decide +kernel
/-- O: after the call, `w` may still alias `x.f`. -/
theorem o_call_w_xf : mayProgO 1 fr pCall vw [] vx [.fld ff] = true := by decide +kernel

end DirectedAlias.Opt.Examples
