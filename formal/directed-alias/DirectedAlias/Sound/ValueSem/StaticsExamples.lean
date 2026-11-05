import DirectedAlias.Sound.ValueSem.Statics
import DirectedAlias.Sound.ValueSem.Run
import DirectedAlias.Opt.ValueSemStatics

/-!
# Examples of design VSS (static fields)

The frame binds the static holder `C` (variable `vc`) to the static root 0; `v`, `z`, `w`, `a`
are arguments (roots 1 to 4). The list of static roots is `[0]`.

* §6.8 of the specification: `C.f = v; t = C.f; u = C.f; t.g = z; m(); u.g = w`.
  `t ~ u` is true and real under A5; `t ~ v` is false and exact under A5. Each static read
  gives exactly `{⟨C.f⟩}`. The store `t.g = z` is strong (a value read before it no longer
  aliases `t.g`); the store `u.g = w` after the call is weak (`u.g ~ z` stays), and the weak
  update is needed: if `u` is read after the call, the callee can replace `C.f`, and
  `t.g ~ z` is real.
* GAP (a), against the unrestricted semantics (`ExecV` of the program itself):
  `C.f = v; t = C.f`. Design VSS answers `t ~ v` false; an unrestricted execution aliases them.
* GAP (b): `C.f = a; e = a.h; d = e.g; m(); n = a.h; n.g = z`. The callee reaches `a` only
  through the static field. Design VSS makes `n.g = z` strong and answers `e.g ~ d` false; an
  unrestricted execution where the callee writes a new object into `a.h` aliases them.
  A strong update through the stored variable itself (`C.f = n; m(); n.g = z` with `n` an
  argument or a new object) cannot lose an alias: `n` denotes one object. The gap needs a
  value that the method reads below the stored value after the call.
* THE RECORDED OPTION (not applied): a static write `C.f = v` keeps `v` in a ghost variable,
  and each call gets the ghost variables as extra arguments, so `pts(v)` is in the start set
  of each later call and its closure goes into `Etree` and `Eval` (`stripStaticG`). It closes
  gap (b) (`e.g ~ d` true) and keeps the answers of §6.8; gap (a) stays.
-/

namespace DirectedAlias.Sound.ValueSem.StaticsExamples

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed DirectedAlias.Sound.ValueSem
open DirectedAlias.Opt.ValueSem

/-! ## Variables, fields, frame -/

/-- The static holder `C`. -/
abbrev vc : Var := 0
/-- Variable `v`. -/
abbrev vv : Var := 1
/-- Variable `t`. -/
abbrev vt : Var := 2
/-- Variable `u`. -/
abbrev vu : Var := 3
/-- Variable `z`. -/
abbrev vz : Var := 4
/-- Variable `w`. -/
abbrev vw : Var := 5
/-- Variable `e`. -/
abbrev ve : Var := 6
/-- Variable `d`. -/
abbrev vd : Var := 7
/-- Variable `n`. -/
abbrev vn : Var := 8
/-- Variable `a`. -/
abbrev va : Var := 9
/-- Field `f`. -/
abbrev ff : Field := 0
/-- Field `g`. -/
abbrev fg : Field := 1
/-- Field `h`. -/
abbrev fh : Field := 2

/-- The frame: `C` holds the static root 0; `v`, `z`, `w`, `a` hold the roots 1 to 4. -/
def fr : Frame := ⟨[(vc, 0), (vv, 1), (vz, 2), (vw, 3), (va, 4)]⟩

/-- The static roots. -/
def sts : List Root := [0]

/-- The callee writes one new object into `C.f` (tag 0). -/
def wCf : HavocW := ⟨.outer (.sym (.root 0) []), [], .fld ff, 0⟩

/-! ## §6.8 -/

/-- `C.f = v; t = C.f; u = C.f`. -/
def pre68 : Prog :=
  .seq (.stmt (.store vc ff vv)) (.seq (.stmt (.load vt vc ff)) (.stmt (.load vu vc ff)))

/-- `C.f = v; t = C.f; u = C.f; t.g = z`. -/
def pre68s : Prog := .seq pre68 (.stmt (.store vt fg vz))

/-- §6.8: `C.f = v; t = C.f; u = C.f; t.g = z; m()@9; u.g = w`. -/
def p68 : Prog :=
  .seq pre68 <| .seq (.stmt (.store vt fg vz)) <|
  .seq (.stmt (.call none 9 [])) (.stmt (.store vu fg vw))

/-- §6.8 with a read before the strong store: `...; e = u.g; t.g = z; m()@9; u.g = w`. -/
def p68e : Prog :=
  .seq pre68 <| .seq (.stmt (.load ve vu fg)) <| .seq (.stmt (.store vt fg vz)) <|
  .seq (.stmt (.call none 9 [])) (.stmt (.store vu fg vw))

/-- The same with the call before the store: `...; e = u.g; m()@9; t.g = z`. -/
def p68w : Prog :=
  .seq pre68 <| .seq (.stmt (.load ve vu fg)) <|
  .seq (.stmt (.call none 9 [])) (.stmt (.store vt fg vz))

/-- §6.8 with `u` read after the call: `C.f = v; t = C.f; t.g = z; m()@9; u = C.f; u.g = w`. -/
def p68r : Prog :=
  .seq (.stmt (.store vc ff vv)) <| .seq (.stmt (.load vt vc ff)) <|
  .seq (.stmt (.store vt fg vz)) <| .seq (.stmt (.call none 9 [])) <|
  .seq (.stmt (.load vu vc ff)) (.stmt (.store vu fg vw))

/-- The programs of §6.8 use the static holder only as a base, and they have no loop. -/
theorem wf68 :
    StaticWF (shB sts fr) p68 ∧ StaticWF (shB sts fr) p68e ∧ StaticWF (shB sts fr) p68r ∧
      p68.loopFreeB = true := by decide

/-- §6.8: `t ~ u` is true and `t ~ v` is false (both policies); the unrestricted design VS
follows the static write and answers `t ~ v` true. -/
theorem answers68 :
    mayProgVSS true 1 sts fr p68 vt [] vu [] = true ∧
      mayProgVSS true 1 sts fr p68 vt [] vv [] = false ∧
      mayProgVSS false 1 sts fr p68 vt [] vu [] = true ∧
      mayProgVSS false 1 sts fr p68 vt [] vv [] = false ∧
      mayProgVSS true 2 sts fr p68 vt [] vv [] = false ∧
      mayProgVS true 1 sts fr p68 vt [] vv [] = true := by decide +kernel

/-- `t ~ u` of §6.8 is real under A5: both read the entry object of `C.f`. -/
theorem real68 : CAliasA5 (srcL []) sts fr p68 vt [] vu [] :=
  CAliasA5_iff.mpr (runAliasV_sound (cs := [.havoc []]) (by decide))

/-- `t ~ v` of §6.8 is exact under A5: no A5 execution gives `t` and `v` the same value. -/
theorem exact68 (src : Nat → Obj × Cell) : ¬ CAliasA5 src sts fr p68 vt [] vv [] :=
  no_alias_of_mayProgVSS src sts true 1 fr p68 vt [] vv [] answers68.2.1

/-- THE STATIC READS GIVE EXACTLY `{⟨C.f⟩}`: after `C.f = v; t = C.f; u = C.f`, `t` and `u`
hold exactly `⟨C.f⟩`; after all of §6.8 the cell `⟨C⟩.f` still holds exactly `⟨C.f⟩`. -/
theorem reads68 :
    (analyzeProgVSS true 1 sts fr pre68 []).env vt = [.sym (.root 0) [.fld ff]] ∧
      (analyzeProgVSS true 1 sts fr pre68 []).env vu = [.sym (.root 0) [.fld ff]] ∧
      (analyzeProgVSS true 1 sts fr p68 []).heap (.sym (.root 0) []) (.fld ff) =
        [.sym (.root 0) [.fld ff]] := by decide +kernel

/-- `static_cells_default` applies to §6.8: each cell of `⟨C⟩` keeps its default content. -/
theorem cells68 (eu : Bool) (K : Nat) (qf : List Field) (c : ACell) :
    (analyzeProgVSS eu K sts fr p68 qf).heap (.sym (.root 0) []) c =
      [childCN K (.sym (.root 0) []) c] :=
  static_cells_default eu K sts fr p68 qf wf68.1
    (noTopB_of_loopFree _ _ 0 _ (by decide)) (List.mem_singleton.mpr rfl) c

/-- THE STORE `t.g = z` IS STRONG: `⟨C.f⟩.g` holds only `⟨z⟩`, so `e ~ t.g` is false; after a
call it is weak (`e ~ t.g` true). -/
theorem strong68 :
    (analyzeProgVSS true 1 sts fr pre68s []).heap (.sym (.root 0) [.fld ff]) (.fld fg) =
        [.sym (.root 2) []] ∧
      mayProgVSS true 1 sts fr p68e ve [] vt [.fld fg] = false ∧
      mayProgVSS true 1 sts fr p68w ve [] vt [.fld fg] = true := by decide +kernel

/-- The false answer `e ~ t.g` after the strong store is exact under A5. -/
theorem strong68_exact (src : Nat → Obj × Cell) : ¬ CAliasA5 src sts fr p68e ve [] vt [.fld fg] :=
  no_alias_of_mayProgVSS src sts true 1 fr p68e ve [] vt [.fld fg] strong68.2.1

/-- THE STORE `u.g = w` AFTER THE CALL IS WEAK: `u.g` may alias both `z` and `w`; the same with
`u` read after the call. -/
theorem weak68 :
    mayProgVSS true 1 sts fr p68 vu [.fld fg] vz [] = true ∧
      mayProgVSS true 1 sts fr p68 vu [.fld fg] vw [] = true ∧
      mayProgVSS true 1 sts fr p68r vt [.fld fg] vz [] = true ∧
      mayProgVSS true 1 sts fr p68r vu [.fld fg] vw [] = true := by decide +kernel

/-- THE WEAK UPDATE IS NEEDED: if the callee writes a new object into `C.f` and `u` reads it
after the call, then `u.g = w` writes the new object, and `t.g ~ z` is real under A5. -/
theorem weak68_real : CAliasA5 (srcL [(.sym (.root 0) [], .fld ff)]) sts fr p68r vt [.fld fg] vz [] :=
  CAliasA5_iff.mpr (runAliasV_sound (cs := [.havoc [wCf]]) (by decide))

/-! ## Gap (a): the static write is invisible to the method -/

/-- `C.f = v; t = C.f`. -/
def pGapA : Prog := .seq (.stmt (.store vc ff vv)) (.stmt (.load vt vc ff))

/-- GAP (a): design VSS answers `t ~ v` false (exact under A5); an unrestricted execution
makes `t` and `v` the same object. -/
theorem gapA :
    mayProgVSS true 1 sts fr pGapA vt [] vv [] = false ∧
      (∀ src, ¬ CAliasA5 src sts fr pGapA vt [] vv []) ∧
      CAliasV (srcL []) sts fr pGapA vt [] vv [] ∧
      mayProgVS true 1 sts fr pGapA vt [] vv [] = true :=
  ⟨by decide +kernel,
    fun src => no_alias_of_mayProgVSS src sts true 1 fr pGapA vt [] vv [] (by decide +kernel),
    runAliasV_sound (cs := []) (by decide), by decide +kernel⟩

/-! ## Gap (b): the callee reaches a value through the static field -/

/-- `C.f = a; e = a.h; d = e.g; m()@9; n = a.h; n.g = z`. -/
def pGapB : Prog :=
  .seq (.stmt (.store vc ff va)) <| .seq (.stmt (.load ve va fh)) <|
  .seq (.stmt (.load vd ve fg)) <| .seq (.stmt (.call none 9 [])) <|
  .seq (.stmt (.load vn va fh)) (.stmt (.store vn fg vz))

/-- The callee follows `C.f` to `a` and writes one new object into `a.h` (tag 0). -/
def wAh : HavocW := ⟨.outer (.sym (.root 0) []), [.fld ff], .fld fh, 0⟩

/-- GAP (b): design VSS answers `e.g ~ d` false (exact under A5); an unrestricted execution
where the callee writes `a.h` through `C.f` aliases them. -/
theorem gapB :
    mayProgVSS true 1 sts fr pGapB ve [.fld fg] vd [] = false ∧
      mayProgVSS true 2 sts fr pGapB ve [.fld fg] vd [] = false ∧
      (∀ src, ¬ CAliasA5 src sts fr pGapB ve [.fld fg] vd []) ∧
      CAliasV (srcL [(.sym (.root 4) [], .fld fh)]) sts fr pGapB ve [.fld fg] vd [] ∧
      mayProgVS true 1 sts fr pGapB ve [.fld fg] vd [] = true :=
  ⟨by decide +kernel, by decide +kernel,
    fun src => no_alias_of_mayProgVSS src sts true 1 fr pGapB ve [.fld fg] vd [] (by decide +kernel),
    runAliasV_sound (cs := [.havoc [wAh]]) (by decide), by decide +kernel⟩

/-! ## The recorded option: statically stored values join the start set of each call -/

/-- The program for the recorded option: a static write `C.f = y` becomes `gv C f = y` (a ghost
variable keeps the stored value), an array store through a static holder becomes `skip`, and
each call gets the ghost variables `gs` as extra arguments. -/
def stripStaticG (sh : Var → Bool) (gv : Var → Field → Var) (gs : List Var) : Prog → Prog
  | .skip => .skip
  | .stmt (.store x f y) => if sh x then .stmt (.copy (gv x f) y) else .stmt (.store x f y)
  | .stmt (.astore x y) => if sh x then .skip else .stmt (.astore x y)
  | .stmt (.call ret s args) => .stmt (.call ret s (args ++ gs))
  | .stmt st => .stmt st
  | .seq p q => .seq (stripStaticG sh gv gs p) (stripStaticG sh gv gs q)
  | .choice p q => .choice (stripStaticG sh gv gs p) (stripStaticG sh gv gs q)
  | .loop p => .loop (stripStaticG sh gv gs p)

/-- May-alias of the recorded option: design VS on `stripStaticG`. -/
def mayProgVSG (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (gv : Var → Field → Var)
    (gs : List Var) (p : Prog) (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  mayProgVS eu K statics fr (stripStaticG (shB statics fr) gv gs p) x px y py

/-- THE RECORDED OPTION CLOSES GAP (b) ONLY: with one ghost variable (20) for `C.f`, `e.g ~ d`
is true, the answers of §6.8 stay (`t ~ u` true, `t ~ v` false), and gap (a) stays. -/
theorem option_answers :
    mayProgVSG true 1 sts fr (fun _ _ => 20) [20] pGapB ve [.fld fg] vd [] = true ∧
      mayProgVSG true 1 sts fr (fun _ _ => 20) [20] p68 vt [] vu [] = true ∧
      mayProgVSG true 1 sts fr (fun _ _ => 20) [20] p68 vt [] vv [] = false ∧
      mayProgVSG true 1 sts fr (fun _ _ => 20) [20] pGapA vt [] vv [] = false := by
  decide +kernel

/-! ## The optimized machine -/

/-- O of design VSS gives the answers of the concept on §6.8 and on the two gaps. -/
theorem o_answersVSS :
    mayProgVSSO true 1 sts fr p68 vt [] vu [] = true ∧
      mayProgVSSO true 1 sts fr p68 vt [] vv [] = false ∧
      mayProgVSSO true 1 sts fr pGapA vt [] vv [] = false ∧
      mayProgVSSO true 1 sts fr pGapB ve [.fld fg] vd [] = false := by decide +kernel

end DirectedAlias.Sound.ValueSem.StaticsExamples
