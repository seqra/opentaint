import DirectedAlias.Sound.BlockOnly.Soundness

/-!
# Value semantics for reads and passive calls (design VS)

The user's rule: `x = new X(); a = x.f` gives `findAlias(a) = {x.f}`, with or without a call.
A field read makes the reader alias the cell, whatever value the cell holds, null included.
So the rule is a property of the FIELD READ. Consequence: a call only blocks strong updates;
it never changes the alias graph.

## The abstract design

* Every cell holds a non-empty named value:
  - a symbolic origin: the default `{⟨b.q.c⟩}` (as before);
  - an allocation origin `new(s)` or `old(s)`: the default `{⟨@s.c⟩}` (the allocation child
    `childCN`, encoded `hsym 0 (rOld s) c []`), not `{}` (`ainitV`, `retireV`);
  - a null assignment at null site `i` gives `{null(i)}` (`nullO i`): one origin for each null
    site. It is never unique and it is not an allocation origin. Its cells have their own
    default names (`hsym 1 (havoc i) elem q`); a load through null blocks concretely.
* NULL SITES. The IR statement `Stmt.null x` has no site. Design VS numbers the null
  statements of a program in syntax order (`Prog.stmts` order): the null site of a statement
  is the number of null statements before it. The analysis and the semantics carry the number
  of the first null statement of the current sub-program (`analyzeVS cb i`, `ExecV i`). No
  existing file changes.
* Load: `pts(x) := ⋃ H(o, f)` (unchanged).
* Store: as design BO (`storeBO`): strong iff one origin and `uniqueBO`.
* Call `x = m(args)` at `s`: the closure `R` of design BO; `Etree ∪= R`; `Eval ∪= succ(R)`;
  `env[x] := {⟨s⟩}` (with `retire`). The heap and every other variable are UNCHANGED
  (`callVS`).
* Join and loop: as design BO.

## The concrete design (instrumented values)

A value is an object or a NULL INSTANCE (`VVal`). A null instance has a tag (`NTag`): the
default null of cell `c` of an object `O` (`dflt O c`), or the `n`-th execution of null site
`i` (`site i n`). A read copies the value with its tag; a store copies it. A load or store
through a null instance blocks. A variable that no statement assigned has no value: a copy or
a store of it blocks (DEFINITE ASSIGNMENT; the JVM verifier gives it). The callee of a call
keeps a reachable cell or writes a new object (strict narrow A2, `HavocN`); it does not write
a new null instance (see the report: the case is argued).

The instrumented state is a foundation state (`CState`) with ghost null tags (`VState`):
`nv x` is the tag of the null in variable `x`, `nh o c` the tag of the null in cell `(o, c)`.
So each instrumented execution projects to a strict narrow execution (`ExecV.toN`).
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly

/-! ## Null sites -/

/-- The number of null statements in a statement: one for `null`, else zero. -/
def _root_.DirectedAlias.Stmt.nullN : Stmt → Nat
  | .null _ => 1
  | _ => 0

/-- The number of null statements of a program (the null sites that it uses). -/
def _root_.DirectedAlias.Prog.nulls : Prog → Nat
  | .skip => 0
  | .stmt st => st.nullN
  | .seq p q => p.nulls + q.nulls
  | .choice p q => p.nulls + q.nulls
  | .loop p => p.nulls

/-- The origin `null(i)` of null site `i`: a heap-child origin of call key `havoc i` and site
tag 1. It is never unique and it is not an allocation origin. -/
def nullO (i : Nat) : Origin := .hsym 1 (.havoc i) .elem []

/-- The null origins of the null sites `0 .. n-1` and their default children (paths up to `K`
and the deep summary). -/
def nullKids (K : Nat) (n : Nat) (cells : List ACell) : List Origin :=
  (List.range n).flatMap (fun i =>
    (pathsUpTo cells K).map (Origin.hsym 1 (.havoc i) .elem) ++ [Origin.hdeep 1 (.havoc i) .elem])

/-! ## The abstract state operations -/

/-- The default content of each cell in design VS: the cell name. For a non-allocation origin it
is `adefault`; for an allocation origin it is the allocation child. -/
def adefaultV (K : Nat) (o : Origin) (c : ACell) : List Origin := [childCN K o c]

/-- The entry abstract state of design VS: the variables of `ainit`, and each cell holds its
cell name. -/
def ainitV (K : Nat) (fr : Frame) : AState where
  env := (ainit K fr).env
  heap := adefaultV K

/-- `retire` of design VS: the recency retire, and the cells of the new most recent object get
their cell names (the default nulls of the new object). -/
def retireV (K : Nat) (s : Site) (X : AState) : AState where
  env := (retire s X).env
  heap := fun o c => if o = rNew s then [childCN K (rNew s) c] else (retire s X).heap o c

/-- Add `E` to `Etree` and `V` to `Eval`. The heap does not change. -/
def setSets (cb : CtxB) (X : AState) (E V : List Origin) : AState where
  env := fupd (fupd X.env cb.cn.xe (uni E (X.env cb.cn.xe))) cb.xv (uni V (X.env cb.xv))
  heap := X.heap

/-- The PASSIVE CALL of design VS: the closure `R` of design BO, `Etree ∪= R`,
`Eval ∪= succ(R)`. No heap write. If the closure fails, both sets get every universe origin. -/
def callVS (cb : CtxB) (X : AState) (args : List Var) : AState :=
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => setSets cb X R (succsN cb.cn X R)
  | none => setSets cb X cb.cn.ctx.origins cb.cn.ctx.origins

/-- The abstract transfer of design VS; `i` is the null site of a null statement. -/
def astepVS (cb : CtxB) (i : Nat) : Stmt → AState → AState
  | .new x s, X => (retireV cb.cn.ctx.K s X).setVar x [rNew s]
  | .unknown x s, X => (retireV cb.cn.ctx.K s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X =>
    (retireV cb.cn.ctx.K s (callVS cb X args)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeBO cb X x (.fld f) (X.env y)
  | .null x, X => X.setVar x [nullO i]
  | st, X => astep cb.cn.ctx st X

/-- The abstract analysis of design VS; `i` is the null site of the first null statement. -/
def analyzeVS (cb : CtxB) : Nat → Prog → AState → AState
  | _, .skip, X => X
  | i, .stmt s, X => astepVS cb i s X
  | i, .seq p q, X => analyzeVS cb (i + p.nulls) q (analyzeVS cb i p X)
  | i, .choice p q, X => join (analyzeVS cb i p X) (analyzeVS cb (i + p.nulls) q X)
  | i, .loop p, X => loopIter cb.cn.ctx (analyzeVS cb i p) cb.cn.ctx.fuel X

/-- The context of a program in design VS: the context of design BO, with the null origins of
the null sites of the program in the universe. -/
def ctxVS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxB :=
  let cb0 := ctxBO eu K statics fr p qf
  let c0 := cb0.cn.ctx
  let origins := c0.origins ++ nullKids K p.nulls c0.cells
  let fuel := (c0.vars.length + origins.length * c0.cells.length) * origins.length + 1
  ⟨⟨{ c0 with origins := origins, fuel := fuel }, statics, cb0.cn.xe⟩, cb0.xv⟩

/-- The final abstract state of program `p` in design VS. -/
def analyzeProgVS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : AState :=
  analyzeVS (ctxVS eu K statics fr p qf) 0 p (ainitV K fr)

/-- May-alias at the end of `p` in design VS. -/
def mayProgVS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgVS eu K statics fr p (afields px ++ afields py)) x px y py

/-! ## Instrumented concrete values -/

/-- The tag of a null instance: the default null of cell `c` of object `o`, the `n`-th
execution of null site `i`, or the null that the `n`-th execution of call site `s` writes with
tag `k` (only in the extended semantics of `CalleeNull.lean`). -/
inductive NTag where
  | dflt (o : Obj) (c : Cell)
  | site (i n : Nat)
  | callee (s n k : Nat)
  deriving DecidableEq, Repr

/-- An instrumented value: an object, or a null instance with its tag. -/
inductive VVal where
  | obj (o : Obj)
  | nul (t : NTag)
  deriving DecidableEq, Repr

/-- The foundation value of an instrumented value: a null instance is null. -/
def VVal.toVal : VVal → Val
  | .obj o => some o
  | .nul _ => none

/-- An instrumented state: a foundation state, the null tags of the variables and of the cells,
and the execution counters of the null sites. -/
structure VState where
  cs : CState
  nv : Var → Option NTag
  nh : Obj → Cell → NTag
  nc : Nat → Nat

/-- The entry instrumented state: the entry state of the frame; no variable has a null tag
(an unbound variable has no value); each cell has its default null tag. -/
def VState.init (fr : Frame) : VState :=
  ⟨CState.init fr, fun _ => none, fun o c => .dflt o c, fun _ => 0⟩

/-- The value of variable `x`: its object, or its null instance, or none if no statement
assigned it. -/
def VState.val (vs : VState) (x : Var) : Option VVal :=
  match vs.cs.env x with
  | some o => some (.obj o)
  | none => (vs.nv x).map VVal.nul

/-- The value of cell `(o, c)`: its object, or its null instance. -/
def VState.cell (vs : VState) (o : Obj) (c : Cell) : VVal :=
  match vs.cs.heap o c with
  | some o' => .obj o'
  | none => .nul (vs.nh o c)

/-- Set variable `x` to value `v`. -/
def VState.setVarV (vs : VState) (x : Var) : VVal → VState
  | .obj o => { vs with cs := vs.cs.setVar x (some o) }
  | .nul t => { vs with cs := vs.cs.setVar x none, nv := fupd vs.nv x (some t) }

/-- Set cell `(o, c)` to value `v`. -/
def VState.setCellV (vs : VState) (o : Obj) (c : Cell) : VVal → VState
  | .obj o' => { vs with cs := vs.cs.setCell o c (some o') }
  | .nul t => { vs with cs := vs.cs.setCell o c none, nh := fupd2 vs.nh o c t }

/-- One instrumented step with the strict narrow call; `i` is the null site of a null
statement. A load through null blocks; a copy or store of an unassigned variable blocks. -/
inductive SStepV (src : Nat → Obj × Cell) (statics : List Root) (i : Nat) :
    Stmt → VState → VState → Prop where
  | new {x s vs} :
      SStepV src statics i (.new x s) vs
        { vs with cs := (vs.cs.setVar x (some (.alloc s (vs.cs.cnt s)))).bump s }
  | null {x vs} :
      SStepV src statics i (.null x) vs
        { vs.setVarV x (.nul (.site i (vs.nc i))) with nc := fupd vs.nc i (vs.nc i + 1) }
  | copy {x y vs v} : vs.val y = some v → SStepV src statics i (.copy x y) vs (vs.setVarV x v)
  | load {x y f vs o} : vs.cs.env y = some o →
      SStepV src statics i (.load x y f) vs (vs.setVarV x (vs.cell o (.fld f)))
  | store {x f y vs o v} : vs.cs.env x = some o → vs.val y = some v →
      SStepV src statics i (.store x f y) vs (vs.setCellV o (.fld f) v)
  | aload {x y vs o} (j : Nat) : vs.cs.env y = some o →
      SStepV src statics i (.aload x y) vs (vs.setVarV x (vs.cell o (.elem j)))
  | astore {x y vs o v} (j : Nat) : vs.cs.env x = some o → vs.val y = some v →
      SStepV src statics i (.astore x y) vs (vs.setCellV o (.elem j) v)
  | unknown {x s vs} :
      SStepV src statics i (.unknown x s) vs
        { vs with cs := (vs.cs.setVar x (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s }
  | call {ret s args vs h'} : HavocN src statics vs.cs args s (vs.cs.cnt s) h' →
      SStepV src statics i (.call ret s args) vs
        { vs with cs := ({ vs.cs with heap := h' }.setRet ret
            (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s }

/-- Big-step instrumented execution; `i` is the null site of the first null statement. -/
inductive ExecV (src : Nat → Obj × Cell) (statics : List Root) :
    Nat → Prog → VState → VState → Prop where
  | skip {i s} : ExecV src statics i .skip s s
  | stmt {i st s s'} : SStepV src statics i st s s' → ExecV src statics i (.stmt st) s s'
  | seq {i p q s t u} : ExecV src statics i p s t → ExecV src statics (i + p.nulls) q t u →
      ExecV src statics i (.seq p q) s u
  | choiceL {i p q s t} : ExecV src statics i p s t → ExecV src statics i (.choice p q) s t
  | choiceR {i p q s t} : ExecV src statics (i + p.nulls) q s t →
      ExecV src statics i (.choice p q) s t
  | loopZero {i p s} : ExecV src statics i (.loop p) s s
  | loopMore {i p s t u} : ExecV src statics i p s t → ExecV src statics i (.loop p) t u →
      ExecV src statics i (.loop p) s u

/-- Follow path `p` from value `v`. A step through a null instance gives none. -/
def VState.readV (vs : VState) : VVal → List Cell → Option VVal
  | v, [] => some v
  | .obj o, c :: cs => vs.readV (vs.cell o c) cs
  | .nul _, _ :: _ => none

/-- The value of access path `x.p`. -/
def VState.evalV (vs : VState) (x : Var) (p : List Cell) : Option VVal :=
  (vs.val x).bind (fun v => vs.readV v p)

/-- In state `vs`, the paths `x.px` and `y.py` evaluate to the same value instance (the same
object or the same null instance). -/
def AliasInV (vs : VState) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ v, vs.evalV x px = some v ∧ vs.evalV y py = some v

/-- VALUE ALIAS IN ONE EXECUTION: one instrumented strict narrow execution of `p` from the
frame entry makes `x.px` and `y.py` the same value instance. -/
def CAliasV (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ vs, ExecV src statics 0 p (VState.init fr) vs ∧ AliasInV vs x px y py

/-! ## Projection to the foundation semantics -/

/-- The foundation part of `setVarV`. -/
theorem setVarV_cs (vs : VState) (x : Var) (v : VVal) :
    (vs.setVarV x v).cs = vs.cs.setVar x v.toVal := by
  cases v <;> rfl

/-- The foundation part of `setCellV`. -/
theorem setCellV_cs (vs : VState) (o : Obj) (c : Cell) (v : VVal) :
    (vs.setCellV o c v).cs = vs.cs.setCell o c v.toVal := by
  cases v <;> rfl

/-- The foundation value of the value of a variable is its foundation value. -/
theorem val_toVal {vs : VState} {x : Var} {v : VVal} (h : vs.val x = some v) :
    v.toVal = vs.cs.env x := by
  unfold VState.val at h
  cases e : vs.cs.env x with
  | some o => rw [e] at h; cases h; rfl
  | none =>
    rw [e] at h
    cases e2 : vs.nv x with
    | none => rw [e2] at h; cases h
    | some t => rw [e2] at h; cases h; rfl

/-- The foundation value of the value of a cell is its foundation value. -/
theorem cell_toVal (vs : VState) (o : Obj) (c : Cell) : (vs.cell o c).toVal = vs.cs.heap o c := by
  unfold VState.cell
  cases vs.cs.heap o c <;> rfl

/-- An instrumented step projects to a strict narrow step. -/
theorem SStepV.toN {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {st : Stmt}
    {s s' : VState} (h : SStepV src statics i st s s') : SStepN src statics st s.cs s'.cs := by
  cases h with
  | new => exact .new
  | null => show SStepN src statics _ _ (s.setVarV _ _).cs; rw [setVarV_cs]; exact .null
  | copy hv => rw [setVarV_cs, val_toVal hv]; exact .copy
  | load he => rw [setVarV_cs, cell_toVal]; exact .load he
  | store he hv => rw [setCellV_cs, val_toVal hv]; exact .store he
  | aload j he => rw [setVarV_cs, cell_toVal]; exact .aload j he
  | astore j he hv => rw [setCellV_cs, val_toVal hv]; exact .astore j he
  | unknown => exact .unknown
  | call hh => exact .call hh

/-- An instrumented execution projects to a strict narrow execution. -/
theorem ExecV.toN {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {p : Prog}
    {s s' : VState} (h : ExecV src statics i p s s') : ExecN src statics p s.cs s'.cs := by
  induction h with
  | skip => exact .skip
  | stmt hs => exact .stmt hs.toN
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | choiceL _ ih => exact .choiceL ih
  | choiceR _ ih => exact .choiceR ih
  | loopZero => exact .loopZero
  | loopMore _ _ ih1 ih2 => exact .loopMore ih1 ih2

/-- A path from an object gives an object if and only if the foundation path gives it. -/
theorem readV_obj (vs : VState) : ∀ (o : Obj) (p : List Cell) (o' : Obj),
    vs.readV (.obj o) p = some (.obj o') ↔ readPath vs.cs.heap o p = some o'
  | o, [], o' => by
    simp only [VState.readV, readPath, Option.some.injEq, VVal.obj.injEq]
  | o, c :: cs, o' => by
    simp only [VState.readV, readPath]
    unfold VState.cell
    cases e : vs.cs.heap o c with
    | some o1 => simp only [Option.bind_some]; exact readV_obj vs o1 cs o'
    | none =>
      simp only [Option.bind_none, reduceCtorEq, iff_false]
      cases cs with
      | nil => simp [VState.readV]
      | cons d ds => simp [VState.readV]

/-- An access path gives an object if and only if the foundation access path gives it. -/
theorem evalV_obj (vs : VState) (x : Var) (p : List Cell) (o : Obj) :
    vs.evalV x p = some (.obj o) ↔ evalPath vs.cs x p = some o := by
  unfold VState.evalV evalPath VState.val
  cases e : vs.cs.env x with
  | some o0 => simp only [Option.bind_some]; exact readV_obj vs o0 p o
  | none =>
    simp only [Option.bind_none, reduceCtorEq, iff_false]
    cases e2 : vs.nv x with
    | none => simp
    | some t =>
      cases p with
      | nil => simp [VState.readV]
      | cons c cs => simp [VState.readV]

/-- A path from an object that gives a null instance ends in a null cell: the path is `q ++ [c]`,
`q` gives an object `o'`, and the cell `(o', c)` holds null with this tag. -/
theorem readV_nul (vs : VState) : ∀ (o : Obj) (p : List Cell) (t : NTag),
    vs.readV (.obj o) p = some (.nul t) →
      ∃ q c o', p = q ++ [c] ∧ readPath vs.cs.heap o q = some o' ∧ vs.cs.heap o' c = none ∧
        vs.nh o' c = t
  | o, [], t, h => by simp [VState.readV] at h
  | o, c :: cs, t, h => by
    simp only [VState.readV] at h
    unfold VState.cell at h
    cases e : vs.cs.heap o c with
    | some o1 =>
      rw [e] at h
      obtain ⟨q, d, o', rfl, h1, h2, h3⟩ := readV_nul vs o1 cs t h
      refine ⟨c :: q, d, o', rfl, ?_, h2, h3⟩
      simp only [readPath, e, Option.bind_some]; exact h1
    | none =>
      rw [e] at h
      cases cs with
      | nil =>
        simp only [VState.readV, Option.some.injEq, VVal.nul.injEq] at h
        exact ⟨[], c, o, rfl, rfl, e, h⟩
      | cons d ds => simp [VState.readV] at h

/-- An access path that gives a null instance: the variable holds it (empty path), or the path
is `q ++ [c]`, `x.q` gives an object `o'`, and the cell `(o', c)` holds null with this tag. -/
theorem evalV_nul {vs : VState} {x : Var} {p : List Cell} {t : NTag}
    (h : vs.evalV x p = some (.nul t)) :
    (p = [] ∧ vs.cs.env x = none ∧ vs.nv x = some t) ∨
      ∃ q c o', p = q ++ [c] ∧ evalPath vs.cs x q = some o' ∧ vs.cs.heap o' c = none ∧
        vs.nh o' c = t := by
  unfold VState.evalV VState.val at h
  cases e : vs.cs.env x with
  | some o0 =>
    rw [e] at h
    simp only [Option.bind_some] at h
    obtain ⟨q, c, o', rfl, h1, h2, h3⟩ := readV_nul vs o0 p t h
    refine Or.inr ⟨q, c, o', rfl, ?_, h2, h3⟩
    simp only [evalPath, e, Option.bind_some]; exact h1
  | none =>
    rw [e] at h
    cases e2 : vs.nv x with
    | none => rw [e2] at h; simp at h
    | some t0 =>
      rw [e2] at h
      cases p with
      | nil =>
        simp only [Option.map_some, Option.bind_some, VState.readV, Option.some.injEq,
          VVal.nul.injEq] at h
        exact Or.inl ⟨rfl, rfl, h ▸ rfl⟩
      | cons c cs => simp [VState.readV] at h

/-- SAME OBJECT, SAME VALUE: an object alias of the projected foundation state is a value
alias. -/
theorem aliasInV_of_aliasIn {vs : VState} {x y : Var} {px py : List Cell}
    (h : AliasIn vs.cs x px y py) : AliasInV vs x px y py := by
  obtain ⟨o, h1, h2⟩ := h
  exact ⟨.obj o, (evalV_obj vs x px o).mpr h1, (evalV_obj vs y py o).mpr h2⟩

/-- A value alias is an object alias of the projected state, or a null-instance alias. -/
theorem aliasInV_cases {vs : VState} {x y : Var} {px py : List Cell}
    (h : AliasInV vs x px y py) :
    AliasIn vs.cs x px y py ∨
      ∃ t, vs.evalV x px = some (.nul t) ∧ vs.evalV y py = some (.nul t) := by
  obtain ⟨v, h1, h2⟩ := h
  cases v with
  | obj o => exact Or.inl ⟨o, (evalV_obj vs x px o).mp h1, (evalV_obj vs y py o).mp h2⟩
  | nul t => exact Or.inr ⟨t, h1, h2⟩

/-- THE VALUE RELATION IS WIDER ONLY BY NULL INSTANCES: a one-execution value alias is a strict
narrow one-execution alias (same object), or two paths of one instrumented execution give the
same null instance. -/
theorem CAliasV.cases {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame} {p : Prog}
    {x y : Var} {px py : List Cell} (h : CAliasV src statics fr p x px y py) :
    CAliasN src statics fr p x px y py ∨
      ∃ vs t, ExecV src statics 0 p (VState.init fr) vs ∧ vs.evalV x px = some (.nul t) ∧
        vs.evalV y py = some (.nul t) := by
  obtain ⟨vs, hx, ha⟩ := h
  rcases aliasInV_cases ha with h1 | ⟨t, h1, h2⟩
  · exact Or.inl ⟨vs.cs, hx.toN, h1⟩
  · exact Or.inr ⟨vs, t, hx, h1, h2⟩

/-- A value alias with an object value is a strict narrow alias. -/
theorem CAliasV.toN_obj {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame} {p : Prog}
    {x y : Var} {px py : List Cell} {vs : VState} {o : Obj}
    (hx : ExecV src statics 0 p (VState.init fr) vs) (h1 : vs.evalV x px = some (.obj o))
    (h2 : vs.evalV y py = some (.obj o)) : CAliasN src statics fr p x px y py :=
  ⟨vs.cs, hx.toN, o, (evalV_obj vs x px o).mp h1, (evalV_obj vs y py o).mp h2⟩

/-- The projection of the entry instrumented state is the entry state. -/
theorem VState.init_cs (fr : Frame) : (VState.init fr).cs = CState.init fr := rfl

end DirectedAlias.Sound.ValueSem
