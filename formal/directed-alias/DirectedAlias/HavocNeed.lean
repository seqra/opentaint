import DirectedAlias.Concept
import DirectedAlias.Sound.HavocRecency.Concept

/-!
# Why an unresolved call needs a havoc origin

The weak havoc keeps the old content of each reachable cell and adds a havoc origin. This file
shows that both parts are necessary. An analysis that keeps the old content and adds nothing
(modelled here by the same program with the call removed) is unsound in two ways:

1. A later strong update through a value loaded after the call writes the old object, although
   the call can have put a new object into the cell (`strong_after_call_*`).
2. A cell whose old content is empty (a field of a new object) stays empty, so two loads of
   the cell after the call do not alias, although the call can have written one new object into
   it (`empty_cell_*`).

The analysis of the design (`mayProg`, and `mayProgHR` with recency and per-cell havoc) answers
true in both cases.
-/

namespace DirectedAlias.HavocNeed

open DirectedAlias DirectedAlias.Sound.HavocRecency

/-- Variable `x` (root 0). -/
abbrev vx : Var := 0
/-- Variable `z` (root 1). -/
abbrev vz : Var := 1
/-- Variable `w`. -/
abbrev vw : Var := 2
/-- Variable `e`. -/
abbrev ve : Var := 3
/-- Variable `t`. -/
abbrev vt : Var := 4
/-- Variable `n`. -/
abbrev vn : Var := 5
/-- Variable `a`. -/
abbrev va : Var := 6
/-- Variable `b`. -/
abbrev vb : Var := 7
/-- Field `f`. -/
abbrev ff : Field := 0
/-- Field `g`. -/
abbrev fg : Field := 1

/-- The entry frame: `x` and `z` hold the distinct roots 0 and 1. -/
def fr : Frame := ⟨[(vx, 0), (vz, 1)]⟩

/-- `w = x.f; e = w.g; m(x); t = x.f; t.g = z`. -/
def pStrong : Prog :=
  .seq (.stmt (.load vw vx ff)) <| .seq (.stmt (.load ve vw fg)) <|
  .seq (.stmt (.call none 9 [vx])) <| .seq (.stmt (.load vt vx ff)) (.stmt (.store vt fg vz))

/-- The same program without the call: the analysis of an engine that ignores the call. -/
def pStrongNoCall : Prog :=
  .seq (.stmt (.load vw vx ff)) <| .seq (.stmt (.load ve vw fg)) <|
  .seq (.stmt (.load vt vx ff)) (.stmt (.store vt fg vz))

/-- If the callee writes a new object into `x.f`, then `t` is that new object, and `w.g` is
still `e`. -/
theorem strong_after_call_real : CAlias fr pStrong vw [.fld fg] ve [] :=
  runAliasB_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- Without havoc, `t` holds only the old object of `x.f`; the store `t.g = z` is strong and
removes `e` from `w.g`. The answer is false, so this analysis is unsound. -/
theorem strong_after_call_nohavoc : mayProg 1 fr pStrongNoCall vw [.fld fg] ve [] = false := by
  decide

/-- With the havoc origin, `t` holds two origins, the store is weak, and `w.g ~ e` stays. -/
theorem strong_after_call_havoc : mayProg 1 fr pStrong vw [.fld fg] ve [] = true := by
  decide

/-- The same with recency and per-cell havoc. -/
theorem strong_after_call_havocHR : mayProgHR true 0 fr pStrong vw [.fld fg] ve [] = true := by
  decide +kernel

/-- `n = new@5; m(n); a = n.f; b = n.f`. -/
def pEmpty : Prog :=
  .seq (.stmt (.new vn 5)) <| .seq (.stmt (.call none 9 [vn])) <|
  .seq (.stmt (.load va vn ff)) (.stmt (.load vb vn ff))

/-- The same program without the call. -/
def pEmptyNoCall : Prog :=
  .seq (.stmt (.new vn 5)) <| .seq (.stmt (.load va vn ff)) (.stmt (.load vb vn ff))

/-- If the callee writes a new object into `n.f`, then `a` and `b` are that object. -/
theorem empty_cell_real : CAlias fr pEmpty va [] vb [] :=
  runAliasB_sound (cs := [.havoc [⟨.arg vn, [], .fld ff, 0⟩]]) (by decide)

/-- Without havoc, the cell of the new object stays null, so `a` and `b` do not alias. The
answer is false, so this analysis is unsound. -/
theorem empty_cell_nohavoc : mayProg 1 fr pEmptyNoCall va [] vb [] = false := by
  decide

/-- With the havoc origin, both loads hold it, and `a ~ b`. -/
theorem empty_cell_havoc : mayProg 1 fr pEmpty va [] vb [] = true := by
  decide

/-- The same with recency and per-cell havoc. -/
theorem empty_cell_havocHR : mayProgHR true 0 fr pEmpty va [] vb [] = true := by
  decide +kernel

end DirectedAlias.HavocNeed
