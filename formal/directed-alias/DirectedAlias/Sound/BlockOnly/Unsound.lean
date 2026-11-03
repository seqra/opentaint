import DirectedAlias.Sound.BlockOnly.Concept
import DirectedAlias.Sound.CellNamed.Run

/-!
# The read rule of the first statement of design BO is unsound

The first statement of design BO (`BO0` here) does not change the heap at a call. A read of a
cell `(o, c)` gives the cell name `childCN o c` if the content is EMPTY and `o` is covered by
`Etree` (the READ RULE); otherwise it gives the content.

The rule is not monotone. A covered cell that is empty at the call can get content later
without a strong update: from the other branch of a join, from a loop head (the body can run
zero times), or from a weak store. Then a read gives only the new content, but the object that
the callee wrote into the cell is still there, and an earlier read named it by the cell name.

Counterexamples (all real under strict narrow A2, all answered false by `BO0`):
* JOIN: `x = new@5; if (*) { m(x); t = x.f } else { x.f = y }`, query `t ~ x.f`.
* LOOP: `x = new@5; m(x); t = x.f; while (*) { x.f = y }`, query `t ~ x.f`.
* SYMBOLIC: `x.f = null; if (*) { m(x); t = x.f } else { x.f = y }` with `x` an entry root.

The fix (`Concept.lean`): the call writes the cell name into each covered universe cell whose
content is empty. The fixed design answers true on both programs.
-/

namespace DirectedAlias.Sound.BlockOnly.Unsound

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly

/-- The call of `BO0`: the two sets grow, and the heap does not change. -/
def callBO0 (cb : CtxB) (X : AState) (args : List Var) : AState :=
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => ⟨fupd (fupd X.env cb.cn.xe (uni R (X.env cb.cn.xe))) cb.xv
      (uni (succsN cb.cn X R) (X.env cb.xv)), X.heap⟩
  | none => ⟨fupd (fupd X.env cb.cn.xe (uni cb.cn.ctx.origins (X.env cb.cn.xe)))
      cb.xv (uni cb.cn.ctx.origins (X.env cb.xv)), X.heap⟩

/-- The READ RULE of `BO0`: an empty cell of an origin that `Etree` covers gives its cell
name. -/
def readBO0 (cb : CtxB) (X : AState) (o : Origin) (c : ACell) : List Origin :=
  if (X.heap o c).isEmpty = true ∧ coveredB (X.env cb.cn.xe) o = true then
    [childCN cb.cn.ctx.K o c] else X.heap o c

/-- The read of cell `c` of the origins `S` with the read rule. -/
def areadBO0 (cb : CtxB) (X : AState) (S : List Origin) (c : ACell) : List Origin :=
  uniMap (fun o => readBO0 cb X o c) S

/-- The abstract transfer of `BO0`. -/
def astepBO0 (cb : CtxB) : Stmt → AState → AState
  | .new x s, X => (retire s X).setVar x [rNew s]
  | .unknown x s, X => (retire s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (retire s (callBO0 cb X args)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeBO cb X x (.fld f) (X.env y)
  | .load x y f, X => X.setVar x (areadBO0 cb X (X.env y) (.fld f))
  | .aload x y, X => X.setVar x (areadBO0 cb X (X.env y) .elem)
  | st, X => astep cb.cn.ctx st X

/-- The abstract analysis of `BO0`. -/
def analyzeBO0 (cb : CtxB) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepBO0 cb s X
  | .seq p q, X => analyzeBO0 cb q (analyzeBO0 cb p X)
  | .choice p q, X => join (analyzeBO0 cb p X) (analyzeBO0 cb q X)
  | .loop p, X => loopIter cb.cn.ctx (analyzeBO0 cb p) cb.cn.ctx.fuel X

/-- The path evaluation of `BO0` (with the read rule). -/
def aevalBO0 (cb : CtxB) (X : AState) : List Origin → List ACell → List Origin
  | S, [] => S
  | S, c :: cs => aevalBO0 cb X (areadBO0 cb X S c) cs

/-- May-alias at the end of `p` in `BO0`. -/
def mayProgBO0 (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  let cb := ctxBO eu K statics fr p (afields px ++ afields py)
  let X := analyzeBO0 cb p (ainit K fr)
  meetB (aevalBO0 cb X (X.env x) px) (aevalBO0 cb X (X.env y) py)

/-! ## The counterexamples -/

/-- Variable `x` (a local). -/
abbrev vx : Var := 0
/-- Variable `y` (root 0). -/
abbrev vy : Var := 1
/-- Variable `t`. -/
abbrev vt : Var := 2
/-- Field `f`. -/
abbrev ff : Field := 0

/-- The frame: `y` holds root 0. -/
def frU : Frame := ⟨[(vy, 0)]⟩

/-- JOIN: `x = new@5; if (*) { m(x)@9; t = x.f } else { x.f = y }`. -/
def pJoinBug : Prog :=
  .seq (.stmt (.new vx 5)) <|
  .choice (.seq (.stmt (.call none 9 [vx])) (.stmt (.load vt vx ff))) (.stmt (.store vx ff vy))

/-- LOOP: `x = new@5; m(x)@9; t = x.f; while (*) { x.f = y }`. -/
def pLoopBug : Prog :=
  .seq (.stmt (.new vx 5)) <| .seq (.stmt (.call none 9 [vx])) <|
  .seq (.stmt (.load vt vx ff)) (.loop (.stmt (.store vx ff vy)))

/-- `BO0` answers `t ~ x.f` false on both programs (both policies, K = 0 and 1). -/
theorem bo0_answers :
    mayProgBO0 true 0 [] frU pJoinBug vt [] vx [.fld ff] = false ∧
      mayProgBO0 true 1 [] frU pJoinBug vt [] vx [.fld ff] = false ∧
      mayProgBO0 false 0 [] frU pJoinBug vt [] vx [.fld ff] = false ∧
      mayProgBO0 true 0 [] frU pLoopBug vt [] vx [.fld ff] = false ∧
      mayProgBO0 true 1 [] frU pLoopBug vt [] vx [.fld ff] = false ∧
      mayProgBO0 false 0 [] frU pLoopBug vt [] vx [.fld ff] = false := by decide +kernel

/-- JOIN is real under strict narrow A2: the left branch runs, and the callee writes one new
object into `x.f`; `t` is that object. -/
theorem joinBug_real :
    CAliasN (srcL [(.alloc 5 0, .fld ff)]) [] frU pJoinBug vt [] vx [.fld ff] :=
  runAliasBN_sound (cs := [.left, .havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- LOOP is real under strict narrow A2: the callee writes one new object into `x.f`, and the
loop runs zero times. -/
theorem loopBug_real :
    CAliasN (srcL [(.alloc 5 0, .fld ff)]) [] frU pLoopBug vt [] vx [.fld ff] :=
  runAliasBN_sound (cs := [.havoc [⟨.arg vx, [], .fld ff, 0⟩], .iter 0]) (by decide)

/-- Variable `n` (null). -/
abbrev vn : Var := 3

/-- The frame of the symbolic case: `x` holds root 1 and `y` holds root 0. -/
def frS : Frame := ⟨[(vx, 1), (vy, 0)]⟩

/-- SYMBOLIC: `n = null; x.f = n; if (*) { m(x)@9; t = x.f } else { x.f = y }` with `x` an
entry root. The strong store of null makes the cell of a symbolic origin empty. -/
def pSymBug : Prog :=
  .seq (.stmt (.null vn)) <| .seq (.stmt (.store vx ff vn)) <|
  .choice (.seq (.stmt (.call none 9 [vx])) (.stmt (.load vt vx ff))) (.stmt (.store vx ff vy))

/-- `BO0` answers `t ~ x.f` false on the symbolic case; the fixed design answers true. -/
theorem symBug_answers :
    mayProgBO0 true 1 [] frS pSymBug vt [] vx [.fld ff] = false ∧
      mayProgBO true 1 [] frS pSymBug vt [] vx [.fld ff] = true := by decide +kernel

/-- The symbolic case is real under strict narrow A2: the left branch runs, and the callee
writes one new object into `x.f`. -/
theorem symBug_real :
    CAliasN (srcL [(.sym (.root 1) [], .fld ff)]) [] frS pSymBug vt [] vx [.fld ff] :=
  runAliasBN_sound (cs := [.left, .havoc [⟨.arg vx, [], .fld ff, 0⟩]]) (by decide)

/-- THE READ RULE IS UNSOUND: there is a strict narrow one-execution alias that `BO0` answers
false. -/
theorem bo0_unsound :
    ∃ (src : Nat → Obj × Cell) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell),
      CAliasN src [] frU p x px y py ∧
      mayProgBO0 true 0 [] frU p x (px.map Cell.abs) y (py.map Cell.abs) = false :=
  ⟨_, pJoinBug, vt, [], vx, [.fld ff], joinBug_real, bo0_answers.1⟩

/-- The fixed design answers true on both programs (the cell name is in the cell). -/
theorem fixed_answers :
    mayProgBO true 0 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgBO true 1 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgBO false 0 [] frU pJoinBug vt [] vx [.fld ff] = true ∧
      mayProgBO true 0 [] frU pLoopBug vt [] vx [.fld ff] = true ∧
      mayProgBO true 1 [] frU pLoopBug vt [] vx [.fld ff] = true ∧
      mayProgBO false 0 [] frU pLoopBug vt [] vx [.fld ff] = true := by decide +kernel

end DirectedAlias.Sound.BlockOnly.Unsound
