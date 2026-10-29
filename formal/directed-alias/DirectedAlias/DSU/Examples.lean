import DirectedAlias.Examples
import DirectedAlias.DSU.Model
import DirectedAlias.DSU.ConcreteFacts

/-!
# DSU examples and counterexamples

Each counterexample is a whole program of the IR, the DSU answer (by `decide`), the concept
answer (by `decide`), and an execution (by `run` and `runAliasB_sound`), or a proof that no
execution gives the alias.
-/

namespace DirectedAlias.DSU.Examples

open DirectedAlias DirectedAlias.DSU DirectedAlias.Examples

/-! ## 1. Precision loss on the task example -/

/-- After the join, the DSU puts `x` and `y` in one group. -/
theorem dsu_join_x_y : dsuMay kotlin fr pJoin vx [] vy [] = true := by decide +kernel

/-- After the join, the DSU puts `a` and `x` in one group (sound). -/
theorem dsu_join_a_x : dsuMay kotlin fr pJoin va [] vx [] = true := by decide +kernel

/-- On the task example, the DSU says alias, the concept says no alias, and no execution aliases. -/
theorem join_precision_loss :
    dsuMay kotlin fr pJoin vx [] vy [] = true ∧ mayProg 2 fr pJoin vx [] vy [] = false ∧
      ¬ CAlias fr pJoin vx [] vy [] :=
  ⟨by decide +kernel, by decide +kernel, join_x_y_none⟩

/-- No execution of the field example makes `x` and `y` the same object. -/
theorem field_x_y_none : ¬ CAlias fr pField vx [] vy [] := by
  rintro ⟨st, hex, o, h1, h2⟩
  have hx := exec_env_keep (x := vx) hex (by decide +kernel)
  have hy := exec_env_keep (x := vy) hex (by decide +kernel)
  simp only [evalPath, readPath, hx, hy, CState.init] at h1 h2
  rw [← h2] at h1
  revert h1; decide +kernel

/-- After `a.f = z; a = w`, the DSU still puts `x` and `y` in one group. -/
theorem field_precision_loss :
    dsuMay kotlin fr pField vx [] vy [] = true ∧ mayProg 2 fr pField vx [] vy [] = false ∧
      ¬ CAlias fr pField vx [] vy [] :=
  ⟨by decide +kernel, by decide +kernel, field_x_y_none⟩

/-- After `a = w`, the DSU still puts `a`'s old partners `x.f` and `y.f` with `z` (sound, same as C). -/
theorem dsu_field_xf_z :
    dsuMay kotlin fr pField vx [.fld ff] vz [] = true ∧ dsuMay kotlin fr pField vy [.fld ff] vz [] = true :=
  by decide +kernel

/-! ## 2. Bug (a): strong update on a group with one concrete element and two objects -/

/-- Variable `h`. -/
abbrev vh : Var := 0
/-- Variable `w` (bug (a) programs). -/
abbrev vw' : Var := 1
/-- Variable `v`. -/
abbrev vv : Var := 2
/-- Variable `prev`. -/
abbrev vprev : Var := 3
/-- Variable `cur`. -/
abbrev vcur : Var := 4
/-- Variable `n` (the join variable). -/
abbrev vn : Var := 5
/-- Field `box`. -/
abbrev fbox : Field := 0
/-- Field `value`. -/
abbrev fval : Field := 1

/-- The frame of bug (a): `h`, `w`, `v` hold the roots 0, 1, 2. -/
def frA : Frame := ⟨[(vh, 0), (vw', 1), (vv, 2)]⟩

/-- `prev = h.box; touch(h); cur = new; cur.value = w; if (*) n = prev else n = cur; n.value = v`. -/
def pA1 : Prog :=
  .seq (.stmt (.load vprev vh fbox)) <| .seq (.stmt (.call none 10 [vh])) <|
  .seq (.stmt (.new vcur 20)) <| .seq (.stmt (.store vcur fval vw')) <|
  .seq (.choice (.stmt (.copy vn vprev)) (.stmt (.copy vn vcur))) (.stmt (.store vn fval vv))

/-- In `pA1`, the execution with the left branch keeps `cur.value == w`. -/
theorem a1_witness : CAlias frA pA1 vcur [.fld fval] vw' [] :=
  runAliasB_sound (cs := [.havoc [], .left]) (by decide +kernel)

/-- Bug (a), no loop: the DSU loses `cur.value ~ w`, which an execution has. UNSOUND. -/
theorem a1_unsound :
    CAlias frA pA1 vcur [.fld fval] vw' [] ∧ dsuMay kotlin frA pA1 vcur [.fld fval] vw' [] = false :=
  ⟨a1_witness, by decide +kernel⟩

/-- In `pA1`, the concept keeps `cur.value ~ w` (the store through `n` is weak). -/
theorem a1_concept : mayProg 2 frA pA1 vcur [.fld fval] vw' [] = true := by decide +kernel

/-- `cur = h.box; touch(h); loop { prev = cur; cur = new@20; cur.value = w; prev.value = v }`. -/
def pA2 : Prog :=
  .seq (.stmt (.load vcur vh fbox)) <| .seq (.stmt (.call none 10 [vh])) <|
  .loop (.seq (.stmt (.copy vprev vcur)) <| .seq (.stmt (.new vcur 20)) <|
    .seq (.stmt (.store vcur fval vw')) (.stmt (.store vprev fval vv)))

/-- In `pA2`, two loop iterations make `prev` and `cur` two objects of site 20, and `cur.value == w`. -/
theorem a2_witness : CAlias frA pA2 vcur [.fld fval] vw' [] :=
  runAliasB_sound (cs := [.havoc [], .iter 2]) (by decide +kernel)

/-- Bug (a), loop with a summary site: the group `{prev, cur, Alloc 20}` gets a strong update. UNSOUND. -/
theorem a2_unsound :
    CAlias frA pA2 vcur [.fld fval] vw' [] ∧ dsuMay kotlin frA pA2 vcur [.fld fval] vw' [] = false :=
  ⟨a2_witness, by decide +kernel⟩

/-- In `pA2`, the concept keeps `cur.value ~ w`. -/
theorem a2_concept : mayProg 2 frA pA2 vcur [.fld fval] vw' [] = true := by decide +kernel

/-- `pA2` with `cur = new@19` before the loop: the loop head join adds a second `Alloc`. -/
def pA2new : Prog :=
  .seq (.stmt (.new vcur 19)) <|
  .loop (.seq (.stmt (.copy vprev vcur)) <| .seq (.stmt (.new vcur 20)) <|
    .seq (.stmt (.store vcur fval vw')) (.stmt (.store vprev fval vv)))

/-- With an allocation before the loop, the guard blocks the strong update. -/
theorem a2new_blocked : dsuMay kotlin frA pA2new vcur [.fld fval] vw' [] = true := by decide +kernel

/-- `pA2` with `cur = h` before the loop: the root is outer. -/
def pA2arg : Prog :=
  .seq (.stmt (.copy vcur vh)) <|
  .loop (.seq (.stmt (.copy vprev vcur)) <| .seq (.stmt (.new vcur 20)) <|
    .seq (.stmt (.store vcur fval vw')) (.stmt (.store vprev fval vv)))

/-- With a root before the loop, the guard blocks the strong update. -/
theorem a2arg_blocked : dsuMay kotlin frA pA2arg vcur [.fld fval] vw' [] = true := by decide +kernel

/-- `pA2` with `cur = null` before the loop: the `null` constant is an `Alloc`. -/
def pA2null : Prog :=
  .seq (.stmt (.null vcur)) <|
  .loop (.seq (.stmt (.copy vprev vcur)) <| .seq (.stmt (.new vcur 20)) <|
    .seq (.stmt (.store vcur fval vw')) (.stmt (.store vprev fval vv)))

/-- With `null` before the loop, the guard blocks the strong update. -/
theorem a2null_blocked : dsuMay kotlin frA pA2null vcur [.fld fval] vw' [] = true := by decide +kernel

/-- The loop body of bug (a): `prev = cur; cur = new@20; cur.value = w; prev.value = v`. -/
def bodyA : Prog :=
  .seq (.stmt (.copy vprev vcur)) <| .seq (.stmt (.new vcur 20)) <|
    .seq (.stmt (.store vcur fval vw')) (.stmt (.store vprev fval vv))

/-- The IR loop with `cur` unbound (null, no DSU element) at the loop entry. -/
def pA2u : Prog := .loop bodyA

/-- With `cur` unbound, the DSU strong update fires on `{prev, cur, Alloc 20}`. -/
theorem a2u_strong : dsuMay kotlin frA pA2u vcur [.fld fval] vw' [] = false := by decide +kernel

/-- With `cur` unbound, no execution runs the body (the first `prev.value = v` reads null),
so `cur` stays null and no execution aliases `cur.value` and `w`: no counterexample. -/
theorem a2u_no_alias : ¬ CAlias frA pA2u vcur [.fld fval] vw' [] := by
  rintro ⟨st, hex, o, h1, _⟩
  have hb : ∀ s t, s.env vcur = none → Exec bodyA s t → t.env vcur = none := by
    intro s t hq he
    cases he with
    | seq e1 e2 =>
      cases e1 with
      | stmt e1 =>
        cases e1
        cases e2 with
        | seq e3 e4 =>
          cases e3 with
          | stmt e3 =>
            cases e3
            cases e4 with
            | seq e5 e6 =>
              cases e5 with
              | stmt e5 =>
                cases e5 with
                | store e5 =>
                  cases e6 with
                  | stmt e6 =>
                    cases e6 with
                    | store e6 =>
                      have hne : vprev ≠ vcur := by decide
                      simp [CState.setCell, CState.setVar, CState.bump, fupd, hne, hq] at e6
  have hc := exec_loop_inv (fun u => u.env vcur = none) hb hex rfl rfl
  simp [evalPath, hc] at h1

/-- The configuration of a constructor: root 0 is `this` with `isOuter = false`. -/
def ctor : DCfg := { inner := [0] }

/-- In a constructor: `cur = new; cur.value = w; if (*) n = this else n = cur; n.value = v`. -/
def pA3 : Prog :=
  .seq (.stmt (.new vcur 20)) <| .seq (.stmt (.store vcur fval vw')) <|
  .seq (.choice (.stmt (.copy vn vh)) (.stmt (.copy vn vcur))) (.stmt (.store vn fval vv))

/-- In `pA3`, the execution with the left branch keeps `cur.value == w`. -/
theorem a3_witness : CAlias frA pA3 vcur [.fld fval] vw' [] :=
  runAliasB_sound (cs := [.left]) (by decide +kernel)

/-- Bug (a) in a constructor: `this` is not outer and not concrete. UNSOUND. -/
theorem a3_unsound :
    CAlias frA pA3 vcur [.fld fval] vw' [] ∧ dsuMay ctor frA pA3 vcur [.fld fval] vw' [] = false :=
  ⟨a3_witness, by decide +kernel⟩

/-- The same program in a method (`this` outer): the guard blocks the strong update. -/
theorem a3_method_blocked : dsuMay kotlin frA pA3 vcur [.fld fval] vw' [] = true := by decide +kernel


/-- Variable `seen`. -/
abbrev vseen : Var := 6

/-- The loop body of the probe S3.2: `seen = prev.value; cur = new@20; cur.value = w;
cur.value = v; prev = cur`. -/
def bodyC : Prog :=
  .seq (.stmt (.load vseen vprev fval)) <| .seq (.stmt (.new vcur 20)) <|
  .seq (.stmt (.store vcur fval vw')) <| .seq (.stmt (.store vcur fval vv)) (.stmt (.copy vprev vcur))

/-- The first part of the body, up to the probe point. -/
def bodyC1 : Prog :=
  .seq (.stmt (.load vseen vprev fval)) <| .seq (.stmt (.new vcur 20)) (.stmt (.store vcur fval vw'))

/-- In a constructor: `this.value = v; prev = this; loop { bodyC }; bodyC1`. The program end is
the probe point inside the loop body. -/
def pA4 : Prog :=
  .seq (.stmt (.store vh fval vv)) <| .seq (.stmt (.copy vprev vh)) <| .seq (.loop bodyC) bodyC1

/-- In `pA4`, zero loop iterations keep `seen == prev.value`. -/
theorem a4_witness : CAlias frA pA4 vseen [] vprev [.fld fval] :=
  runAliasB_sound (cs := [.iter 0]) (by decide +kernel)

/-- Bug (a), loop in a constructor (probe S3.2). UNSOUND. -/
theorem a4_unsound :
    CAlias frA pA4 vseen [] vprev [.fld fval] ∧ dsuMay ctor frA pA4 vseen [] vprev [.fld fval] = false :=
  ⟨a4_witness, by decide +kernel⟩

/-! ## 3. Bug (b): an unresolved call removes heap aliases -/

/-- Bug (b): `w = x.f; m(x)`: the DSU removes `x.f`, but the callee can keep the cell. UNSOUND. -/
theorem b_unsound :
    CAlias fr pCall vw [] vx [.fld ff] ∧ dsuMay kotlin fr pCall vw [] vx [.fld ff] = false ∧
      mayProg 1 fr pCall vw [] vx [.fld ff] = true :=
  ⟨call_w_xf_witness, by decide +kernel, by decide +kernel⟩

/-- `b = new; b.f = z; w = b.f; m(b)`: a local allocation as the argument. -/
def pCallLocal : Prog :=
  .seq (.stmt (.new vb 7)) <| .seq (.stmt (.store vb ff vz)) <|
  .seq (.stmt (.load vw vb ff)) (.stmt (.call none 9 [vb]))

/-- Bug (b) on a local allocation. UNSOUND. -/
theorem b_local_unsound :
    CAlias fr pCallLocal vw [] vb [.fld ff] ∧ dsuMay kotlin fr pCallLocal vw [] vb [.fld ff] = false :=
  ⟨runAliasB_sound (cs := [.havoc []]) (by decide +kernel), by decide +kernel⟩

/-! ## 4. Static field write -/

/-- Variable `sC`: it holds the class object of the static fields. -/
abbrev vsc : Var := 0
/-- Variable `v` (static example). -/
abbrev vsv : Var := 1
/-- Variable `t` (static example). -/
abbrev vst : Var := 2

/-- The frame of the static example: `sC` and `v` hold the roots 0 and 1. -/
def frS : Frame := ⟨[(vsc, 0), (vsv, 1)]⟩

/-- `C.f = v; t = C.f`, with `C` the static holder `sC`. -/
def pStatic : Prog := .seq (.stmt (.store vsc ff vsv)) (.stmt (.load vst vsc ff))

/-- The configuration where `sC` is the static holder: a store through it is `WriteStatic`. -/
def statCfg : DCfg := { statics := [vsc] }

/-- Static write ignored: `t == v` in the execution, the DSU says no alias. UNSOUND. -/
theorem static_unsound :
    CAlias frS pStatic vst [] vsv [] ∧ dsuMay statCfg frS pStatic vst [] vsv [] = false ∧
      mayProg 1 frS pStatic vst [] vsv [] = true :=
  ⟨runAliasB_sound (cs := []) (by decide +kernel), by decide +kernel, by decide +kernel⟩

/-- With an ordinary field store (not static), the DSU keeps `t ~ v`. -/
theorem static_as_field : dsuMay kotlin frS pStatic vst [] vsv [] = true := by decide +kernel

/-! ## 5. Extra findings of the model -/

/-- `z = x; x = x`: a self copy. -/
def pSelf : Prog := .seq (.stmt (.copy vz vx)) (.stmt (.copy vx vx))

/-- Self copy: `removeOldAndMergeWith(x, x)` removes `x` and merges a one-element set. UNSOUND. -/
theorem self_copy_unsound :
    CAlias fr pSelf vx [] vz [] ∧ dsuMay kotlin fr pSelf vx [] vz [] = false :=
  ⟨runAliasB_sound (cs := []) (by decide +kernel), by decide +kernel⟩

/-- Variable `x` (representative example). It is the smallest local. -/
abbrev rx : Var := 0
/-- Variable `p` (representative example). -/
abbrev rp : Var := 1
/-- Variable `w` (representative example). -/
abbrev rw : Var := 2

/-- The frame of the representative example: `p` holds root 0. -/
def frR : Frame := ⟨[(rp, 0)]⟩

/-- `x = p; w = p.f; x = x.f`. `x` is the representative of the group `{x, p, Arg 0}`. -/
def pRepr : Prog :=
  .seq (.stmt (.copy rx rp)) <| .seq (.stmt (.load rw rp ff)) (.stmt (.load rx rx ff))

/-- Representative quirk: after `x = x.f`, `x` is in a new self-loop group, not with `w`. UNSOUND. -/
theorem repr_unsound :
    CAlias frR pRepr rx [] rw [] ∧ dsuMay kotlin frR pRepr rx [] rw [] = false :=
  ⟨runAliasB_sound (cs := []) (by decide +kernel), by decide +kernel⟩

/-- Without the representative quirk (pure partition semantics), the DSU keeps `x ~ w`. -/
theorem repr_partition_ok : dsuMay { quirk := false } frR pRepr rx [] rw [] = true := by decide +kernel

/-- With the quirk, the DSU also says `x ~ x.f` (a spurious self loop). -/
theorem repr_self_loop : dsuMay kotlin frR pRepr rx [] rx [.fld ff] = true := by decide +kernel

/-! ## 6. Dominance boundary: where the DSU is more precise than the concept -/

/-- The loop `pLoop` keeps `b.f == y` after each iteration: no execution aliases `b.f` and `x`. -/
theorem loop_bf_x_none : ¬ CAlias fr pLoop vb [.fld ff] vx [] := by
  rintro ⟨st, hex, o, h1, h2⟩
  let Q : CState → Prop := fun s =>
    s.env vx = some (.sym (.root 0) []) ∧ s.env vy = some (.sym (.root 1) []) ∧
      (s.env vb = none ∨ ∃ ob, s.env vb = some ob ∧ s.heap ob (.fld ff) = s.env vy)
  have hb : ∀ s t, Q s → Exec pStrong s t → Q t := by
    intro s t hq he
    obtain ⟨hx, hy, _⟩ := hq
    cases he with
    | seq h1 h2 =>
      cases h1 with
      | stmt h1 =>
        cases h1
        cases h2 with
        | seq h3 h4 =>
          cases h3 with
          | stmt h3 =>
            cases h3 with
            | store e3 =>
              cases h4 with
              | stmt h4 =>
                cases h4 with
                | store e4 =>
                  simp only [CState.setCell, CState.setVar, CState.bump] at e3 e4 ⊢
                  have e3' := e3; have e4' := e4
                  simp [fupd] at e3' e4'
                  subst e3' e4'
                  refine ⟨?_, ?_, Or.inr ⟨.alloc 7 (s.cnt 7), by simp [fupd], ?_⟩⟩
                  · have hne : vx ≠ vb := by decide
                    simpa [fupd, hne] using hx
                  · have hne : vy ≠ vb := by decide
                    simpa [fupd, hne] using hy
                  · have hne : vy ≠ vb := by decide
                    simp [fupd, fupd2, hy, hne]
  have hq := exec_loop_inv Q hb hex rfl ⟨rfl, rfl, Or.inl rfl⟩
  obtain ⟨hx, hy, hbq⟩ := hq
  simp only [evalPath, readPath, hx] at h2
  cases hbq with
  | inl hn => simp [evalPath, hn] at h1
  | inr hs =>
    obtain ⟨ob, hob, hf⟩ := hs
    simp only [evalPath, readPath, hob, hf, hy, Option.bind_some] at h1
    rw [← h2] at h1
    revert h1; decide +kernel

/-- In a loop, the DSU strong update on `{b, Alloc 7}` is sound and more precise than the concept. -/
theorem loop_dsu_more_precise :
    mayProg 1 fr pLoop vb [.fld ff] vx [] = true ∧ dsuMay kotlin fr pLoop vb [.fld ff] vx [] = false ∧
      ¬ CAlias fr pLoop vb [.fld ff] vx [] :=
  ⟨by decide +kernel, by decide +kernel, loop_bf_x_none⟩

/-- `x.f.f` and `x.f.f.f` evaluate to two different objects in the only execution of `skip`. -/
theorem deep_none : ¬ CAlias fr .skip vx [.fld ff, .fld ff] vx [.fld ff, .fld ff, .fld ff] := by
  rintro ⟨st, hex, o, h1, h2⟩
  cases hex
  have e1 : evalPath (CState.init fr) vx [.fld ff, .fld ff] =
      some (.sym (.root 0) [.fld ff, .fld ff]) := by decide +kernel
  have e2 : evalPath (CState.init fr) vx [.fld ff, .fld ff, .fld ff] =
      some (.sym (.root 0) [.fld ff, .fld ff, .fld ff]) := by decide +kernel
  rw [e1] at h1; rw [e2] at h2; rw [← h2] at h1
  exact absurd h1 (by decide +kernel)

/-- With `K = 1` the concept merges deep paths, the DSU does not. Dominance fails here, soundly. -/
theorem deep_concept_imprecise :
    mayProg 1 fr .skip vx [.fld ff, .fld ff] vx [.fld ff, .fld ff, .fld ff] = true ∧
      dsuMay kotlin fr .skip vx [.fld ff, .fld ff] vx [.fld ff, .fld ff, .fld ff] = false :=
  by decide +kernel

/-- `x.f = y; x.f = z` on a root: the concept does a strong update, the DSU a weak one. -/
def pRootStrong : Prog := .seq (.stmt (.store vx ff vy)) (.stmt (.store vx ff vz))

/-- On a root, the concept is more precise than the DSU (dominance holds here). -/
theorem root_concept_more_precise :
    mayProg 1 fr pRootStrong vx [.fld ff] vy [] = false ∧
      dsuMay kotlin fr pRootStrong vx [.fld ff] vy [] = true :=
  by decide +kernel

end DirectedAlias.DSU.Examples
