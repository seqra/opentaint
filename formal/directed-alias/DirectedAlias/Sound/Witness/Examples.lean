import DirectedAlias.Sound.Witness.Search
import DirectedAlias.Sound.StoreExamples

/-!
# Examples of the executable witness search

Each `decide` proof runs `crossWitness` (or `oneWitness`) in the kernel.
* In scope: the task example `pJoin` and the store examples `pInit`, `pPre` give a witness.
  The theorems `witness_core` and `witness_store` also give the witness from `mayProg = true`.
* Out of scope: the counterexamples B2-B6 give `none`. By `crossWitness_none_iff`, `none`
  proves `NoCrossAlias` again (an independent check of `Boundary.lean`).
* Arrays: the search finds witnesses that use array index choices.
-/

namespace DirectedAlias.Sound.Witness.Examples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Witness
open DirectedAlias.Sound.Boundary (vx vy vz va vt ve vu ff fg fr3 pTwice pBlock pCorr pStrongTwo
  pStrongTwoG pWeak pJoin_in_scope)
open DirectedAlias.Sound.StoreExamples (pInit pPre init_in_scope init_answers pre_in_scope
  pre_answers)

/-! ## The task example (core scope) -/

/-- `a ~ x` after the join: both runs take the left branch. -/
theorem pJoin_a_x :
    crossWitness DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.va [] DirectedAlias.Examples.vx [] =
      some ⟨[.left], [.left], [], []⟩ := by decide

/-- `a ~ y` after the join: the first run takes the right branch. The second run does not
change `y`, so the search takes its first choice list (the left branch). -/
theorem pJoin_a_y :
    crossWitness DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.va [] DirectedAlias.Examples.vy [] =
      some ⟨[.right], [.left], [], []⟩ := by decide

/-- `x ~ y` has no witness. -/
theorem pJoin_x_y :
    crossWitness DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.vx [] DirectedAlias.Examples.vy [] = none := by decide

/-- The same witness from the completeness theorem: scope check, then `mayProg = true`. -/
theorem pJoin_a_x_by_scope :
    (crossWitness DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.va [] DirectedAlias.Examples.vx []).isSome = true :=
  witness_core pJoin_in_scope DirectedAlias.Examples.join_a_x

-- The extracted value runs the search: it prints the witness of `a ~ x`.
#eval coreWitness pJoin_in_scope DirectedAlias.Examples.join_a_x

/-! ## The store scope -/

/-- `t ~ x` in `pInit`: both runs take the left branch (the new object stores `x`). -/
theorem init_t_x : crossWitness fr3 pInit vt [] vx [] = some ⟨[.left], [.left], [], []⟩ := by
  decide

/-- `t ~ y.f` in `pInit`: the first run takes the right branch. -/
theorem init_t_yf :
    crossWitness fr3 pInit vt [] vy [.fld ff] = some ⟨[.right], [.left], [], [.fld ff]⟩ := by
  decide

/-- `t ~ y` in `pInit` has no witness. -/
theorem init_t_y : crossWitness fr3 pInit vt [] vy [] = none := by decide

/-- The query `t ~ y.f` of `pInit` is in the certified scope. -/
theorem init_in_scope_f : storeScopeB 2 fr3 pInit [] [.fld ff] = true := by decide

/-- The witnesses of `pInit` from the completeness theorem. -/
theorem init_by_scope :
    (crossWitness fr3 pInit vt [] vx []).isSome = true ∧
      (crossWitness fr3 pInit vt [] vy [.fld ff]).isSome = true :=
  ⟨witness_store init_in_scope init_answers.1, witness_store init_in_scope_f init_answers.2.1⟩

/-- `t ~ z` in `pPre`. -/
theorem pre_t_z : (crossWitness fr3 pPre vt [] vz []).isSome = true := by decide

/-- `t ~ y.f` in `pPre`, also from the completeness theorem. -/
theorem pre_by_scope : (crossWitness fr3 pPre vt [] vy [.fld ff]).isSome = true :=
  witness_store pre_in_scope pre_answers.2.1

-- The extracted value runs the search: it prints the witness of `t ~ x` in `pInit`.
#eval storeWitness init_in_scope init_answers.1

/-! ## Counterexamples B2-B6: no witness -/

/-- B2: no witness. -/
theorem twice_no : crossWitness fr3 pTwice vx [] vy [] = none := by decide

/-- B3: no witness. -/
theorem block_no : crossWitness fr3 pBlock vu [] vz [] = none := by decide

/-- B4: no witness. -/
theorem corr_no : crossWitness fr3 pCorr vt [] ve [] = none := by decide

/-- B5: no witness. -/
theorem strongTwo_no : crossWitness fr3 pStrongTwo vx [.fld ff, .fld ff] vy [] = none := by
  decide

/-- B5 without a cycle: no witness. -/
theorem strongTwoG_no : crossWitness fr3 pStrongTwoG vx [.fld ff, .fld fg] vy [] = none := by
  decide

/-- B6: no witness. -/
theorem weak_no : crossWitness fr3 pWeak vx [.fld ff, .fld ff] vy [] = none := by decide

/-- B4 again: `none` proves that no two executions alias. -/
theorem corr_none' : Boundary.NoCrossAlias fr3 pCorr vt [] ve [] :=
  (crossWitness_none_iff rfl).mp corr_no

/-- B5 again: `none` proves that no two executions alias. -/
theorem strongTwo_none' : Boundary.NoCrossAlias fr3 pStrongTwo vx [.fld ff, .fld ff] vy [] :=
  (crossWitness_none_iff rfl).mp strongTwo_no

/-! ## Arrays -/

/-- `a = x[i]; t = x[j]`. -/
def pArr : Prog := .seq (.stmt (.aload va vx)) (.stmt (.aload vt vx))

/-- The program is in the core scope (`aload` is a core statement). -/
theorem arr_in_scope : coreScopeB 2 fr3 pArr [] [] = true := by decide

/-- `a ~ t`: both runs use index 0 two times. -/
theorem arr_a_t :
    crossWitness fr3 pArr va [] vt [] = some ⟨[.idx 0, .idx 0], [.idx 0, .idx 0], [], []⟩ := by
  decide

/-- `a ~ x[*]`: the second path uses the concrete cell `elem 0`. -/
theorem arr_a_xe :
    crossWitness fr3 pArr va [] vx [.elem] =
      some ⟨[.idx 0, .idx 0], [.idx 0, .idx 0], [], [.elem 0]⟩ := by decide

/-- `a ~ x` has no witness: `a` is an element of `x`, never `x`. -/
theorem arr_a_x : crossWitness fr3 pArr va [] vx [] = none := by decide

/-! ## The one-execution search (soundness direction) -/

/-- `a ~ y` after the join in one execution: the right branch. -/
theorem one_pJoin_a_y :
    oneWitness DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.va [] DirectedAlias.Examples.vy [] = some ⟨[.right], [], []⟩ := by
  decide

/-- `a ~ t` in one execution of `pArr`. -/
theorem one_arr_a_t : oneWitness fr3 pArr va [] vt [] = some ⟨[.idx 0, .idx 0], [], []⟩ := by
  decide

/-- The one-execution result proves `CAlias`. -/
theorem one_pJoin_a_y_alias :
    CAlias DirectedAlias.Examples.fr DirectedAlias.Examples.pJoin
      DirectedAlias.Examples.va [] DirectedAlias.Examples.vy [] :=
  (oneWitness_sound one_pJoin_a_y).2.2

end DirectedAlias.Sound.Witness.Examples
