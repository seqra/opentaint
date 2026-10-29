import DirectedAlias.Sound.Boundary

/-!
# Small facts for the design document

* `may` is symmetric (`may_comm`, in `Concept.lean`).
* `may` is not transitive (`Examples.may_not_transitive`). Here: the concrete side of it.
* A partition (or any transitive relation) that is sound for the task example must relate
  `x` and `y`. Concept C does not relate them, and no two executions alias them.
  So a DSU (a partition) cannot be exact on the task example. Concept C is exact on it.
-/

namespace DirectedAlias.Sound.Facts

open DirectedAlias DirectedAlias.Sound
open DirectedAlias.Sound.Boundary (NoCrossAlias noCrossB_sound)
open DirectedAlias.Examples (vx vy va fr pJoin)

/-- `may` is symmetric on each abstract state. -/
theorem may_symm (X : AState) (x : Var) (px : List ACell) (y : Var) (py : List ACell) :
    may X x px y py = may X y py x px :=
  may_comm X x px y py

/-- After the task example, `x` and `a` alias in one execution (the left branch). -/
theorem x_a_alias : CAlias fr pJoin vx [] va [] := runAliasB_sound (cs := [.left]) (by decide)

/-- After the task example, `a` and `y` alias in one execution (the right branch). -/
theorem a_y_alias : CAlias fr pJoin va [] vy [] := runAliasB_sound (cs := [.right]) (by decide)

/-- After the task example, no two executions make `x` and `y` the same object. -/
theorem x_y_none : NoCrossAlias fr pJoin vx [] vy [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-- The alias facts are not transitive: `x ~ a` and `a ~ y` hold in executions,
but `x ~ y` holds in no pair of executions. -/
theorem alias_not_transitive :
    CAlias fr pJoin vx [] va [] ∧ CAlias fr pJoin va [] vy [] ∧ NoCrossAlias fr pJoin vx [] vy [] :=
  ⟨x_a_alias, a_y_alias, x_y_none⟩

/-- Each transitive relation that contains all one-execution aliases of the task example
relates `x` and `y`. Concept C does not relate them, and this is exact. -/
theorem transitive_sound_relates_x_y (R : Var → List Cell → Var → List Cell → Prop)
    (hsound : ∀ x px y py, CAlias fr pJoin x px y py → R x px y py)
    (htrans : ∀ a pa b pb c pc, R a pa b pb → R b pb c pc → R a pa c pc) :
    R vx [] vy [] ∧ mayProg 2 fr pJoin vx [] vy [] = false ∧ NoCrossAlias fr pJoin vx [] vy [] :=
  ⟨htrans _ _ _ _ _ _ (hsound _ _ _ _ x_a_alias) (hsound _ _ _ _ a_y_alias),
    Examples.join_x_y, x_y_none⟩

/-- A partition of the variables (a class for each variable) that is sound for the task
example puts `x` and `y` in one class. This is the DSU case of the theorem above. -/
theorem partition_sound_merges_x_y (cls : Var → Nat)
    (hsound : ∀ x y, CAlias fr pJoin x [] y [] → cls x = cls y) : cls vx = cls vy :=
  (hsound _ _ x_a_alias).trans (hsound _ _ a_y_alias)

end DirectedAlias.Sound.Facts
