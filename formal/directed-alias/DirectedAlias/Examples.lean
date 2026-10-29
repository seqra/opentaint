import DirectedAlias.Concept

/-!
# Examples

The task example (brief §0) and the field example, checked by `decide`.
Concrete witnesses come from `run` and `runAliasB_sound`.
-/

namespace DirectedAlias.Examples

open DirectedAlias

/-- Variable `x`. -/
abbrev vx : Var := 0
/-- Variable `y`. -/
abbrev vy : Var := 1
/-- Variable `a`. -/
abbrev va : Var := 2
/-- Variable `z`. -/
abbrev vz : Var := 3
/-- Variable `w`. -/
abbrev vw : Var := 4
/-- Variable `b`. -/
abbrev vb : Var := 5
/-- Field `f`. -/
abbrev ff : Field := 0

/-- The entry frame: `x`, `y`, `z`, `w` hold the distinct roots 0, 1, 2, 3. -/
def fr : Frame := ⟨[(vx, 0), (vy, 1), (vz, 2), (vw, 3)]⟩

/-- The task example: `if (*) a = x else a = y`. -/
def pJoin : Prog := .choice (.stmt (.copy va vx)) (.stmt (.copy va vy))

/-- The field example: the join, then `a.f = z`, then `a = w`. -/
def pField : Prog := .seq pJoin (.seq (.stmt (.store va ff vz)) (.stmt (.copy va vw)))

/-! ## Task example -/

/-- After the join, `a` may alias `x`. -/
theorem join_a_x : mayProg 2 fr pJoin va [] vx [] = true := by decide
/-- After the join, `a` may alias `y`. -/
theorem join_a_y : mayProg 2 fr pJoin va [] vy [] = true := by decide
/-- After the join, `x` does not alias `y`: the relation keeps the direction. -/
theorem join_x_y : mayProg 2 fr pJoin vx [] vy [] = false := by decide

/-- The relation `may` is not transitive: `x ~ a` and `a ~ y`, but not `x ~ y`. -/
theorem may_not_transitive :
    mayProg 2 fr pJoin vx [] va [] = true ∧ mayProg 2 fr pJoin va [] vy [] = true ∧
      mayProg 2 fr pJoin vx [] vy [] = false := by decide

/-- One execution (left branch) makes `a` and `x` the same object. -/
theorem join_a_x_witness : CAlias fr pJoin va [] vx [] :=
  runAliasB_sound (cs := [.left]) (by decide)

/-- One execution (right branch) makes `a` and `y` the same object. -/
theorem join_a_y_witness : CAlias fr pJoin va [] vy [] :=
  runAliasB_sound (cs := [.right]) (by decide)

/-- No execution makes `x` and `y` the same object. -/
theorem join_x_y_none : ¬ CAlias fr pJoin vx [] vy [] := by
  rintro ⟨st, hex, hal⟩
  have hb := aliasInB_iff.mpr hal
  cases hex with
  | choiceL h =>
    cases h with
    | stmt h => cases h; revert hb; decide
  | choiceR h =>
    cases h with
    | stmt h => cases h; revert hb; decide

/-! ## Field example -/

/-- After `a.f = z` and `a = w`, `x.f` may alias `z`. -/
theorem field_xf_z : mayProg 2 fr pField vx [.fld ff] vz [] = true := by decide
/-- After `a.f = z` and `a = w`, `y.f` may alias `z`. -/
theorem field_yf_z : mayProg 2 fr pField vy [.fld ff] vz [] = true := by decide
/-- After `a = w`, `x` does not alias `y`. -/
theorem field_x_y : mayProg 2 fr pField vx [] vy [] = false := by decide
/-- After `a = w`, `a` does not alias `x`. -/
theorem field_a_x : mayProg 2 fr pField va [] vx [] = false := by decide
/-- After `a = w`, `a` aliases `w`. -/
theorem field_a_w : mayProg 2 fr pField va [] vw [] = true := by decide
/-- `x.f` and `y.f` may alias: each may hold `z`. -/
theorem field_xf_yf : mayProg 2 fr pField vx [.fld ff] vy [.fld ff] = true := by decide

/-- The left execution makes `x.f` and `z` the same object. -/
theorem field_xf_z_witness : CAlias fr pField vx [.fld ff] vz [] :=
  runAliasB_sound (cs := [.left]) (by decide)

/-- The right execution makes `y.f` and `z` the same object. -/
theorem field_yf_z_witness : CAlias fr pField vy [.fld ff] vz [] :=
  runAliasB_sound (cs := [.right]) (by decide)

/-! ## Strong and weak updates -/

/-- `b = new; b.f = x; b.f = y`: the allocation runs once, so the second store is strong. -/
def pStrong : Prog :=
  .seq (.stmt (.new vb 7)) (.seq (.stmt (.store vb ff vx)) (.stmt (.store vb ff vy)))

/-- The strong update removes `x` from `b.f`. -/
theorem strong_bf_x : mayProg 1 fr pStrong vb [.fld ff] vx [] = false := by decide
/-- The strong update puts `y` into `b.f`. -/
theorem strong_bf_y : mayProg 1 fr pStrong vb [.fld ff] vy [] = true := by decide

/-- The same body in a loop: the allocation site runs many times, so each store is weak. -/
def pLoop : Prog := .loop pStrong

/-- In the loop, the stores are weak, so `b.f` keeps `x`. This is sound but not exact. -/
theorem loop_bf_x : mayProg 1 fr pLoop vb [.fld ff] vx [] = true := by decide

/-! ## Calls -/

/-- `w = x.f; m(x)`: the callee may keep or overwrite `x.f`. -/
def pCall : Prog := .seq (.stmt (.load vw vx ff)) (.stmt (.call none 9 [vx]))

/-- After the call, `w` may still alias `x.f` (the callee may keep the cell). -/
theorem call_w_xf : mayProg 1 fr pCall vw [] vx [.fld ff] = true := by decide

/-- The execution where the callee keeps the cell makes `w` and `x.f` the same object. -/
theorem call_w_xf_witness : CAlias fr pCall vw [] vx [.fld ff] :=
  runAliasB_sound (cs := [.havoc []]) (by decide)

/-- The execution where the callee overwrites `x.f` gives no alias of `w` and `x.f`. -/
theorem call_w_xf_overwrite :
    runAliasB fr pCall [.havoc [⟨.arg vx, [], .fld ff, 0⟩]] vw [] vx [.fld ff] = false := by
  decide

end DirectedAlias.Examples
