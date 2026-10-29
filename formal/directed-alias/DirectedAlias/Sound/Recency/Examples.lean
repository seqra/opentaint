import DirectedAlias.Sound.Recency.Soundness
import DirectedAlias.Sound.Boundary

/-!
# Examples of the recency refinement

The recency refinement removes the false answer of `loop_bf_x` (counterexample B7).
The answer is then exact and equal to the answer of the DSU model
(`loop_dsu_more_precise` in the DSU report). The other examples keep their answers.
-/

namespace DirectedAlias.Sound.Recency.Examples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency
open DirectedAlias.Examples

/-- With recency, `b.f` does not alias `x` after the loop: the stores are strong on `rNew 7`. -/
theorem loop_bf_x_fixed : mayProgR true 1 fr pLoop vb [.fld ff] vx [] = false := by decide

/-- With recency, `b.f` still may alias `y` after the loop. -/
theorem loop_bf_y : mayProgR true 1 fr pLoop vb [.fld ff] vy [] = true := by decide

/-- One loop iteration makes `b.f` and `y` the same object. -/
theorem loop_bf_y_witness : CAlias fr pLoop vb [.fld ff] vy [] :=
  runAliasB_sound (cs := [.iter 1]) (by decide)

/-- The recency answer for `b.f` and `x` is exact: no two executions alias them. -/
theorem loop_bf_x_exact :
    mayProgR true 1 fr pLoop vb [.fld ff] vx [] = false ∧
      Boundary.NoCrossAlias fr pLoop vb [.fld ff] vx [] :=
  ⟨loop_bf_x_fixed, Boundary.loop_none⟩

/-- Concept C without recency gives the false answer on the same query. -/
theorem loop_bf_x_without_recency : mayProg 1 fr pLoop vb [.fld ff] vx [] = true := loop_bf_x

/-- With recency and the weak policy for symbolic origins, the loop answer is also exact. -/
theorem loop_bf_x_fixed_weak : mayProgR false 1 fr pLoop vb [.fld ff] vx [] = false := by decide

/-- The task example keeps its answers with recency. -/
theorem join_answers :
    mayProgR true 2 fr pJoin va [] vx [] = true ∧ mayProgR true 2 fr pJoin va [] vy [] = true ∧
      mayProgR true 2 fr pJoin vx [] vy [] = false := by decide

/-- The field example keeps its answers with recency. -/
theorem field_answers :
    mayProgR true 2 fr pField vx [.fld ff] vz [] = true ∧
      mayProgR true 2 fr pField vy [.fld ff] vz [] = true ∧
      mayProgR true 2 fr pField vx [] vy [] = false ∧
      mayProgR true 2 fr pField va [] vw [] = true := by decide

/-- The strong-update example keeps its answers with recency. -/
theorem strong_answers :
    mayProgR true 1 fr pStrong vb [.fld ff] vx [] = false ∧
      mayProgR true 1 fr pStrong vb [.fld ff] vy [] = true := by decide

/-- The call example keeps its answer with recency. -/
theorem call_answer : mayProgR true 1 fr pCall vw [] vx [.fld ff] = true := by decide

/-- A list built in a loop: `loop { n = new@7; n.f = h; h = n }`. -/
def pList : Prog :=
  .loop (.seq (.stmt (.new va 7)) (.seq (.stmt (.store va ff vb)) (.stmt (.copy vb va))))

/-- The frame of the list example: `b` holds the root 0. -/
def frL : Frame := ⟨[(vb, 0)]⟩

/-- The Boolean check of a cross-execution alias for two choice lists. -/
def crossB (fr : Frame) (p : Prog) (c1 c2 : List Choice) (x : Var) (cx : List Cell) (y : Var)
    (cy : List Cell) : Bool :=
  match runFrom fr p c1, runFrom fr p c2 with
  | some s1, some s2 => Boundary.sameB (evalPath s1 x cx) (evalPath s2 y cy)
  | _, _ => false

/-- A successful `crossB` check proves a cross-execution alias (an executable witness). -/
theorem crossB_sound {fr : Frame} {p : Prog} {c1 c2 : List Choice} {x y : Var}
    {cx cy : List Cell} (h : crossB fr p c1 c2 x cx y cy = true) : CAliasX fr p x cx y cy := by
  unfold crossB at h
  cases e1 : runFrom fr p c1 with
  | none => rw [e1] at h; cases h
  | some s1 =>
    cases e2 : runFrom fr p c2 with
    | none => rw [e1, e2] at h; cases h
    | some s2 =>
      rw [e1, e2] at h
      simp only [Boundary.sameB] at h
      cases ev : evalPath s1 x cx with
      | none => rw [ev] at h; cases h
      | some o =>
        rw [ev] at h
        exact ⟨s1, s2, o, runFrom_sound e1, runFrom_sound e2, ev, of_decide_eq_true h⟩

/-- After the list loop, the next node of the head may alias the head. -/
theorem list_may : mayProgR true 2 frL pList vb [.fld ff] vb [] = true := by decide

/-- The answer is exact across executions: the next node after two iterations is the head
after one iteration. -/
theorem list_cross : CAliasX frL pList vb [.fld ff] vb [] :=
  crossB_sound (c1 := [.iter 2]) (c2 := [.iter 1]) (by decide)

end DirectedAlias.Sound.Recency.Examples
