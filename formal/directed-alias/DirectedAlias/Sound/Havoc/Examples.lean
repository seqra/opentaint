import DirectedAlias.Sound.Havoc.Soundness
import DirectedAlias.Examples
import DirectedAlias.DSU.Model

/-!
# The shared havoc spread and its fix (strict A2)

Program `pHv`: `m(x); a = x.f; b = y.g` (call site 9, `f = 0`, `g = 1`), frame `fr` of
`Examples.lean` (`x, y, z, w` are four distinct roots).

* Concept C (one origin `havoc 9`): `a ~ b`, `a ~ z.f` and `a ~ w.g` are true (`havoc_spread`).
* Under the generous semantics `Exec`, these aliases are REAL: the callee can write one new
  object into `x.f`, `y.g`, `z.f` and `w.g` (`spread_real_ab`, `spread_real_az`).
* Per-cell havoc answers false for all three, and true for `a ~ x.f` (`strict_answers`).
  Under strict A2 no execution aliases `a` and `b` (`strict_ab_none`).
  Both answers of `a ~ x.f` are realized by strict executions: the callee keeps `x.f`
  (`strict_axf_keep`) or writes a new object into `x.f` (`strict_axf_new`).
* So per-cell havoc is NOT sound for `Exec` (`generous_breaks_strict`). The refinement depends
  on strict A2.
* Today's DSU also answers false for `a ~ b` (`dsu_ab`): per-cell havoc does not regress there.

The `mayProgH` checks use `K = 0` (77 universe origins), because `decide +kernel` takes about
90 s with `K = 1` (416 universe origins). Soundness (`csoundH`) holds for each `K`.
-/

namespace DirectedAlias.Sound.Havoc.Examples

open DirectedAlias DirectedAlias.Examples DirectedAlias.Sound.Havoc

/-- The field `g`. -/
abbrev fg : Field := 1

/-- `m(x); a = x.f; b = y.g`. -/
def pHv : Prog :=
  .seq (.stmt (.call none 9 [vx])) (.seq (.stmt (.load va vx ff)) (.stmt (.load vb vy fg)))

/-! ## Concept C: the spread -/

/-- Concept C spreads the shared havoc origin: after the call, `a` may alias `b`, `z.f` and `w.g`. -/
theorem havoc_spread :
    mayProg 1 fr pHv va [] vb [] = true ∧ mayProg 1 fr pHv va [] vz [.fld ff] = true ∧
      mayProg 1 fr pHv va [] vw [.fld fg] = true := by decide +kernel

/-- Under the generous semantics, `a` and `b` can alias: the callee writes one object into
`x.f` and `y.g`. -/
theorem spread_real_ab : CAlias fr pHv va [] vb [] :=
  runAliasB_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩,
    ⟨.outer (.sym (.root 1) []), [], .fld fg, 0⟩]]) (by decide)

/-- Under the generous semantics, `a` and `z.f` can alias. -/
theorem spread_real_az : CAlias fr pHv va [] vz [.fld ff] :=
  runAliasB_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩,
    ⟨.outer (.sym (.root 2) []), [], .fld ff, 0⟩]]) (by decide)

/-- Concept C is exact on `a ~ b` for the generous semantics. -/
theorem havoc_spread_exact :
    mayProg 1 fr pHv va [] vb [] = true ∧ CAlias fr pHv va [] vb [] :=
  ⟨havoc_spread.1, spread_real_ab⟩

/-! ## Per-cell havoc: the spread is gone -/

/-- Per-cell havoc answers false for `a ~ b`, `a ~ z.f`, `a ~ w.g`, and true for `a ~ x.f`
(both strong-update policies). -/
theorem strict_answers :
    mayProgH true 0 fr pHv va [] vb [] = false ∧
      mayProgH true 0 fr pHv va [] vz [.fld ff] = false ∧
      mayProgH true 0 fr pHv va [] vw [.fld fg] = false ∧
      mayProgH true 0 fr pHv va [] vx [.fld ff] = true ∧
      mayProgH false 0 fr pHv va [] vb [] = false ∧
      mayProgH false 0 fr pHv va [] vx [.fld ff] = true := by decide +kernel

/-- Under strict A2, no execution aliases `a` and `b`, for each naming `src`. -/
theorem strict_ab_none (src : Nat → Obj × Cell) : ¬ CAliasS src fr pHv va [] vb [] :=
  no_alias_of_mayProgH src true 0 fr pHv va [] vb [] strict_answers.1

/-- Under strict A2, no execution aliases `a` and `z.f`. -/
theorem strict_az_none (src : Nat → Obj × Cell) : ¬ CAliasS src fr pHv va [] vz [.fld ff] :=
  no_alias_of_mayProgH src true 0 fr pHv va [] vz [.fld ff] strict_answers.2.1

/-- Per-cell havoc is not sound for the generous semantics: `a ~ b` is a real alias there,
and per-cell havoc answers false. The refinement depends on strict A2. -/
theorem generous_breaks_strict :
    CAlias fr pHv va [] vb [] ∧ mayProgH true 0 fr pHv va [] vb [] = false :=
  ⟨spread_real_ab, strict_answers.1⟩

/-! ## Strict witnesses for `a ~ x.f` -/

/-- A naming that decodes tag 0 to the cell `f` of the root object of `x`. -/
def src1 : Nat → Obj × Cell := fun _ => (.sym (.root 0) [], .fld ff)

/-- The strict havoc that keeps every cell. -/
theorem havocS_keep (src : Nat → Obj × Cell) (st : CState) (args : List Var) (s n : Nat) :
    HavocS src st args s n st.heap := fun _ _ => Or.inl rfl

/-- The heap after the callee writes a new object into `x.f`. -/
def hNew : Heap :=
  fupd2 (CState.init fr).heap (.sym (.root 0) []) (.fld ff) (some (.sym (.havoc 9 0 0) []))

/-- Writing a new object into `x.f` is a strict havoc for the naming `src1`. -/
theorem havocS_new : HavocS src1 (CState.init fr) [vx] 9 0 hNew := by
  intro o c
  by_cases e : o = .sym (.root 0) [] ∧ c = .fld ff
  · obtain ⟨rfl, rfl⟩ := e
    refine Or.inr ⟨Reach.arg (x := vx) (List.mem_singleton.mpr rfl) rfl, 0, rfl, ?_⟩
    exact fupd2_same _ _ _ _
  · exact Or.inl (fupd2_ne _ _ e)

/-- The strict execution of `pHv` from a call heap `h'`. -/
theorem execS_pHv {src : Nat → Obj × Cell} {h' : Heap}
    (hh : HavocS src (CState.init fr) [vx] 9 0 h') :
    ExecS src pHv (CState.init fr)
      (((({ CState.init fr with heap := h' }.setRet none
        (some (.sym (.fresh 9 0) []))).bump 9).setVar va
          (h' (.sym (.root 0) []) (.fld ff))).setVar vb
          (h' (.sym (.root 1) []) (.fld fg))) := by
  exact .seq (.stmt (.call hh)) (.seq (.stmt (.load rfl)) (.stmt (.load rfl)))

/-- A strict execution where the callee keeps `x.f`: `a` aliases `x.f`. -/
theorem strict_axf_keep (src : Nat → Obj × Cell) : CAliasS src fr pHv va [] vx [.fld ff] :=
  ⟨_, execS_pHv (havocS_keep src _ _ _ _), aliasInB_iff.mp (by decide)⟩

/-- A strict execution where the callee writes a new object into `x.f`: `a` holds the new
object and aliases `x.f`. -/
theorem strict_axf_new : CAliasS src1 fr pHv va [] vx [.fld ff] :=
  ⟨_, execS_pHv havocS_new, aliasInB_iff.mp (by decide)⟩

/-- In the second witness, `a` holds the new havoc object, not the entry object of `x.f`. -/
theorem strict_axf_new_value :
    hNew (.sym (.root 0) []) (.fld ff) = some (.sym (.havoc 9 0 0) []) := by decide

/-! ## Today's DSU -/

/-- Today's DSU also answers false for `a ~ b` and `a ~ z.f` after the call. -/
theorem dsu_ab :
    DSU.dsuMay DSU.kotlin fr pHv va [] vb [] = false ∧
      DSU.dsuMay DSU.kotlin fr pHv va [] vz [.fld ff] = false := by decide +kernel

/-! ## More shapes -/

/-- `b = new@7; m(b); a = b.f; z = b.g`: the call writes the cells of an argument allocation. -/
def pNew : Prog :=
  .seq (.stmt (.new vb 7)) (.seq (.stmt (.call none 9 [vb]))
    (.seq (.stmt (.load va vb ff)) (.stmt (.load vz vb fg))))

/-- The frame with no roots. -/
def frE : Frame := ⟨[]⟩

/-- Two cells of one argument allocation: C gives a spurious alias, per-cell havoc does not.
`a ~ b.f` stays true. -/
theorem new_answers :
    mayProg 0 frE pNew va [] vz [] = true ∧ mayProgH true 0 frE pNew va [] vz [] = false ∧
      mayProgH true 0 frE pNew va [] vb [.fld ff] = true := by decide +kernel

/-- Under strict A2, the two cells of the allocation never hold one object after the call. -/
theorem new_none (src : Nat → Obj × Cell) : ¬ CAliasS src frE pNew va [] vz [] :=
  no_alias_of_mayProgH src true 0 frE pNew va [] vz [] new_answers.2.1

/-- Under the generous semantics, the callee can write one object into both cells. -/
theorem new_real : CAlias frE pNew va [] vz [] :=
  runAliasB_sound (cs := [.havoc [⟨.arg vb, [], .fld ff, 0⟩, ⟨.arg vb, [], .fld fg, 0⟩]])
    (by decide)

/-- `loop { m(x); a = x.f }; b = y.g`: the loop fixpoint keeps the per-cell origins apart. -/
def pLoopHv : Prog :=
  .seq (.loop (.seq (.stmt (.call none 9 [vx])) (.stmt (.load va vx ff)))) (.stmt (.load vb vy fg))

/-- In a loop, C gives the spurious alias and per-cell havoc does not. -/
theorem loop_answers :
    mayProg 0 fr pLoopHv va [] vb [] = true ∧ mayProgH true 0 fr pLoopHv va [] vb [] = false ∧
      mayProgH true 0 fr pLoopHv va [] vx [.fld ff] = true := by decide +kernel

/-- Under strict A2, no execution of the loop program aliases `a` and `b`. -/
theorem loop_none (src : Nat → Obj × Cell) : ¬ CAliasS src fr pLoopHv va [] vb [] :=
  no_alias_of_mayProgH src true 0 fr pLoopHv va [] vb [] loop_answers.2.1

end DirectedAlias.Sound.Havoc.Examples
