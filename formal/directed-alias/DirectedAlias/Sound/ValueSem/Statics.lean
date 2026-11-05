import DirectedAlias.Sound.ValueSem.Soundness

/-!
# Static fields (design VSS: design VS with ignored static writes)

User decision (2026-11-05): ignore static writes; a static read always gives the reference to
the static field, as if the field was not initialized.

## Static holders

The model has no class objects. A STATIC HOLDER is a frame variable that the frame binds to a
static root (a root in the `statics` list of design VS): `shB statics fr x`. In JIR a static
holder is not a variable at all, so a well-formed program uses a static holder only as the
base of a field access (`StaticWF`): it never assigns it, never copies it, and never stores it
as a value. A call can name it as an argument (the callee reaches the static roots anyway).

* A STATIC WRITE is `store x f y` with `x` a static holder. An `astore x y` through a static
  holder (impossible in JIR) is treated as a static write too, so no cell of a static holder is
  ever written (`Stmt.staticWriteB`).
* A STATIC READ is `load t x f` with `x` a static holder; `aload t x` is treated the same way.

## The analysis

`analyzeVSS` is design VS where a static write does not change the state (`astepVSS`). It is
design VS on the program with the static writes replaced by `skip` (`analyzeVSS_eq`,
`stripStatic`). Under `StaticWF`, the cells of the static roots keep their default content in
each state that the analysis computes (`SCInv_analyze`, `static_cells_default`), because the
calls of design VS are passive. So a static read gives exactly `{⟨C.f⟩}` (`static_read`,
`static_read_end`). The exception is a loop whose fuel runs out (the top state); `noTopB` tests
it, and it is true for loop-free programs (`noTopB_of_loopFree`).

## Assumption A5 and soundness

A5 is the concrete semantics `ExecA5`: an instrumented strict narrow execution where a static
write of the method has no effect. It is `ExecV` of `stripStatic p` (`execA5_iff`).
`csoundVSS`: each A5 value alias is a may-alias of design VSS (each `K`, each policy, each list
of static roots, recency on). It needs no well-formedness.
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly

/-! ## Static holders and static writes -/

/-- Variable `x` is a static holder: the frame binds it to a static root. -/
def shB (statics : List Root) (fr : Frame) (x : Var) : Bool :=
  match fr.root? x with
  | some r => statics.contains r
  | none => false

/-- A statement is a static write: a store (or an array store) through a static holder. -/
def _root_.DirectedAlias.Stmt.staticWriteB (sh : Var → Bool) : Stmt → Bool
  | .store x _ _ => sh x
  | .astore x _ => sh x
  | _ => false

/-- A statement uses static holders only as the base of a field access: it does not assign,
copy or store a static holder. -/
def _root_.DirectedAlias.Stmt.shOK (sh : Var → Bool) : Stmt → Bool
  | .new x _ => !sh x
  | .null x => !sh x
  | .copy x y => !sh x && !sh y
  | .load x _ _ => !sh x
  | .store _ _ y => !sh y
  | .aload x _ => !sh x
  | .astore _ y => !sh y
  | .unknown x _ => !sh x
  | .call ret _ _ => match ret with
    | some x => !sh x
    | none => true

/-- STATIC WELL-FORMEDNESS: each statement of the program uses static holders only as bases. -/
def StaticWF (sh : Var → Bool) (p : Prog) : Prop := p.stmts.all (Stmt.shOK sh) = true

instance (sh : Var → Bool) (p : Prog) : Decidable (StaticWF sh p) :=
  inferInstanceAs (Decidable (_ = true))

/-- The program with each static write replaced by `skip`. -/
def stripStatic (sh : Var → Bool) : Prog → Prog
  | .skip => .skip
  | .stmt st => match st.staticWriteB sh with
    | true => .skip
    | false => .stmt st
  | .seq p q => .seq (stripStatic sh p) (stripStatic sh q)
  | .choice p q => .choice (stripStatic sh p) (stripStatic sh q)
  | .loop p => .loop (stripStatic sh p)

/-- A static holder has a static root. -/
theorem shB_iff {statics : List Root} {fr : Frame} {x : Var} :
    shB statics fr x = true ↔ ∃ r, fr.root? x = some r ∧ r ∈ statics := by
  unfold shB
  cases fr.root? x with
  | none =>
    refine ⟨fun h => ?_, fun ⟨_, h, _⟩ => ?_⟩
    · cases h
    · cases h
  | some r =>
    refine ⟨fun h => ⟨r, rfl, List.contains_iff_mem.mp h⟩, fun ⟨r', h, hr⟩ => ?_⟩
    cases h
    exact List.contains_iff_mem.mpr hr

/-- Stripping keeps the null statements, so it keeps the null sites. -/
theorem nulls_strip (sh : Var → Bool) : ∀ p : Prog, (stripStatic sh p).nulls = p.nulls
  | .skip => rfl
  | .stmt st => by
    cases h : st.staticWriteB sh with
    | true =>
      show (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st).nulls = _
      rw [h]
      show 0 = st.nullN
      cases st <;> first | rfl | exact absurd h Bool.false_ne_true
    | false =>
      show (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st).nulls = _
      rw [h]
  | .seq p q => by
    show (stripStatic sh p).nulls + (stripStatic sh q).nulls = p.nulls + q.nulls
    rw [nulls_strip sh p, nulls_strip sh q]
  | .choice p q => by
    show (stripStatic sh p).nulls + (stripStatic sh q).nulls = p.nulls + q.nulls
    rw [nulls_strip sh p, nulls_strip sh q]
  | .loop p => nulls_strip sh p

/-- A statement of the stripped program is a statement of the program and not a static write. -/
theorem stmts_strip (sh : Var → Bool) : ∀ (p : Prog) (st : Stmt),
    st ∈ (stripStatic sh p).stmts → st ∈ p.stmts ∧ st.staticWriteB sh = false
  | .skip, _, h => by cases h
  | .stmt s, st, h => by
    cases e : s.staticWriteB sh with
    | true =>
      change st ∈ (match s.staticWriteB sh with | true => Prog.skip | false => .stmt s).stmts at h
      rw [e] at h; cases h
    | false =>
      change st ∈ (match s.staticWriteB sh with | true => Prog.skip | false => .stmt s).stmts at h
      rw [e] at h
      have : st = s := List.mem_singleton.mp h
      subst this
      exact ⟨List.mem_singleton.mpr rfl, e⟩
  | .seq p q, st, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨h1, h2⟩ := stmts_strip sh p st h; exact ⟨List.mem_append.mpr (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := stmts_strip sh q st h; exact ⟨List.mem_append.mpr (Or.inr h1), h2⟩
  | .choice p q, st, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨h1, h2⟩ := stmts_strip sh p st h; exact ⟨List.mem_append.mpr (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := stmts_strip sh q st h; exact ⟨List.mem_append.mpr (Or.inr h1), h2⟩
  | .loop p, st, h => stmts_strip sh p st h

/-! ## Design VSS -/

/-- The transfer of design VSS: a static write does not change the state; every other
statement is the transfer of design VS. -/
def astepVSS (cb : CtxB) (sh : Var → Bool) (i : Nat) (st : Stmt) (X : AState) : AState :=
  match st.staticWriteB sh with
  | true => X
  | false => astepVS cb i st X

/-- The abstract analysis of design VSS; `i` is the null site of the first null statement. -/
def analyzeVSS (cb : CtxB) (sh : Var → Bool) : Nat → Prog → AState → AState
  | _, .skip, X => X
  | i, .stmt s, X => astepVSS cb sh i s X
  | i, .seq p q, X => analyzeVSS cb sh (i + p.nulls) q (analyzeVSS cb sh i p X)
  | i, .choice p q, X => join (analyzeVSS cb sh i p X) (analyzeVSS cb sh (i + p.nulls) q X)
  | i, .loop p, X => loopIter cb.cn.ctx (analyzeVSS cb sh i p) cb.cn.ctx.fuel X

/-- THE TWO FORMS AGREE: design VSS is design VS on the program without its static writes. -/
theorem analyzeVSS_eq (cb : CtxB) (sh : Var → Bool) :
    ∀ (p : Prog) (i : Nat) (X : AState),
      analyzeVSS cb sh i p X = analyzeVS cb i (stripStatic sh p) X
  | .skip, _, _ => rfl
  | .stmt st, i, X => by
    cases h : st.staticWriteB sh with
    | true =>
      show (match st.staticWriteB sh with | true => X | false => astepVS cb i st X) =
        analyzeVS cb i (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st) X
      rw [h]; rfl
    | false =>
      show (match st.staticWriteB sh with | true => X | false => astepVS cb i st X) =
        analyzeVS cb i (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st) X
      rw [h]; rfl
  | .seq p q, i, X => by
    show analyzeVSS cb sh (i + p.nulls) q (analyzeVSS cb sh i p X) =
      analyzeVS cb (i + (stripStatic sh p).nulls) (stripStatic sh q)
        (analyzeVS cb i (stripStatic sh p) X)
    rw [analyzeVSS_eq cb sh p, analyzeVSS_eq cb sh q, nulls_strip]
  | .choice p q, i, X => by
    show join (analyzeVSS cb sh i p X) (analyzeVSS cb sh (i + p.nulls) q X) =
      join (analyzeVS cb i (stripStatic sh p) X)
        (analyzeVS cb (i + (stripStatic sh p).nulls) (stripStatic sh q) X)
    rw [analyzeVSS_eq cb sh p, analyzeVSS_eq cb sh q, nulls_strip]
  | .loop p, i, X => by
    show loopIter cb.cn.ctx (analyzeVSS cb sh i p) cb.cn.ctx.fuel X =
      loopIter cb.cn.ctx (analyzeVS cb i (stripStatic sh p)) cb.cn.ctx.fuel X
    have : analyzeVSS cb sh i p = analyzeVS cb i (stripStatic sh p) :=
      funext (fun Y => analyzeVSS_eq cb sh p i Y)
    rw [this]

/-- The final abstract state of program `p` in design VSS (the context of the stripped
program). -/
def analyzeProgVSS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : AState :=
  analyzeVSS (ctxVS eu K statics fr (stripStatic (shB statics fr) p) qf) (shB statics fr) 0 p
    (ainitV K fr)

/-- May-alias at the end of `p` in design VSS. -/
def mayProgVSS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgVSS eu K statics fr p (afields px ++ afields py)) x px y py

/-- The final state of design VSS is the final state of design VS on the stripped program. -/
theorem analyzeProgVSS_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    analyzeProgVSS eu K statics fr p qf =
      analyzeProgVS eu K statics fr (stripStatic (shB statics fr) p) qf :=
  analyzeVSS_eq _ _ p 0 _

/-- The may-alias of design VSS is the may-alias of design VS on the stripped program. -/
theorem mayProgVSS_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) :
    mayProgVSS eu K statics fr p x px y py =
      mayProgVS eu K statics fr (stripStatic (shB statics fr) p) x px y py := by
  unfold mayProgVSS mayProgVS
  rw [analyzeProgVSS_eq]

/-! ## Assumption A5 -/

/-- A5: an execution where the static writes of the method have no effect on it or its callees. -/
inductive ExecA5 (src : Nat → Obj × Cell) (statics : List Root) (sh : Var → Bool) :
    Nat → Prog → VState → VState → Prop where
  | skip {i s} : ExecA5 src statics sh i .skip s s
  | stmt {i st s s'} : st.staticWriteB sh = false → SStepV src statics i st s s' →
      ExecA5 src statics sh i (.stmt st) s s'
  | static {i st s} : st.staticWriteB sh = true → ExecA5 src statics sh i (.stmt st) s s
  | seq {i p q s t u} : ExecA5 src statics sh i p s t →
      ExecA5 src statics sh (i + p.nulls) q t u → ExecA5 src statics sh i (.seq p q) s u
  | choiceL {i p q s t} : ExecA5 src statics sh i p s t →
      ExecA5 src statics sh i (.choice p q) s t
  | choiceR {i p q s t} : ExecA5 src statics sh (i + p.nulls) q s t →
      ExecA5 src statics sh i (.choice p q) s t
  | loopZero {i p s} : ExecA5 src statics sh i (.loop p) s s
  | loopMore {i p s t u} : ExecA5 src statics sh i p s t →
      ExecA5 src statics sh i (.loop p) t u → ExecA5 src statics sh i (.loop p) s u

/-- An A5 execution is an execution of the stripped program. -/
theorem ExecA5.toStrip {src : Nat → Obj × Cell} {statics : List Root} {sh : Var → Bool}
    {i : Nat} {p : Prog} {s t : VState} (h : ExecA5 src statics sh i p s t) :
    ExecV src statics i (stripStatic sh p) s t := by
  induction h with
  | skip => exact .skip
  | @stmt i st s s' hw hs =>
    show ExecV src statics i (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st) s s'
    rw [hw]; exact .stmt hs
  | @static i st s hw =>
    show ExecV src statics i (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st) s s
    rw [hw]; exact .skip
  | @seq i p q s t u _ _ ih1 ih2 =>
    refine .seq ih1 ?_
    rw [nulls_strip]; exact ih2
  | choiceL _ ih => exact .choiceL ih
  | @choiceR i p q s t _ ih =>
    refine .choiceR ?_
    rw [nulls_strip]; exact ih
  | loopZero => exact .loopZero
  | loopMore _ _ ih1 ih2 => exact .loopMore ih1 ih2

/-- An execution of the stripped program is an A5 execution. -/
theorem ExecA5.ofStrip {src : Nat → Obj × Cell} {statics : List Root} {sh : Var → Bool}
    {i : Nat} {q : Prog} {s t : VState} (h : ExecV src statics i q s t) :
    ∀ p, q = stripStatic sh p → ExecA5 src statics sh i p s t := by
  induction h with
  | @skip i s =>
    intro p hp
    cases p with
    | skip => exact .skip
    | stmt st =>
      cases e : st.staticWriteB sh with
      | true => exact .static e
      | false =>
        change Prog.skip = (match st.staticWriteB sh with | true => Prog.skip | false => .stmt st) at hp
        rw [e] at hp; cases hp
    | seq _ _ => cases hp
    | choice _ _ => cases hp
    | loop _ => cases hp
  | @stmt i st s s' hs =>
    intro p hp
    cases p with
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change Prog.stmt st = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change Prog.stmt st = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
        exact .stmt e hs
    | skip => cases hp
    | seq _ _ => cases hp
    | choice _ _ => cases hp
    | loop _ => cases hp
  | @seq i p q s t u _ _ ih1 ih2 =>
    intro p' hp
    cases p' with
    | seq a b =>
      cases hp
      refine .seq (ih1 a rfl) ?_
      have := ih2 b rfl
      rw [nulls_strip] at this; exact this
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
    | skip => cases hp
    | choice _ _ => cases hp
    | loop _ => cases hp
  | @choiceL i p q s t _ ih =>
    intro p' hp
    cases p' with
    | choice a b => cases hp; exact .choiceL (ih a rfl)
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
    | skip => cases hp
    | seq _ _ => cases hp
    | loop _ => cases hp
  | @choiceR i p q s t _ ih =>
    intro p' hp
    cases p' with
    | choice a b =>
      cases hp
      have := ih b rfl
      rw [nulls_strip] at this; exact .choiceR this
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
    | skip => cases hp
    | seq _ _ => cases hp
    | loop _ => cases hp
  | @loopZero i p s =>
    intro p' hp
    cases p' with
    | loop a => exact .loopZero
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
    | skip => cases hp
    | seq _ _ => cases hp
    | choice _ _ => cases hp
  | @loopMore i p s t u _ _ ih1 ih2 =>
    intro p' hp
    cases p' with
    | loop a =>
      cases hp
      exact .loopMore (ih1 a rfl) (ih2 (.loop a) rfl)
    | stmt st' =>
      cases e : st'.staticWriteB sh with
      | true =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
      | false =>
        change _ = (match st'.staticWriteB sh with | true => Prog.skip | false => .stmt st') at hp
        rw [e] at hp; cases hp
    | skip => cases hp
    | seq _ _ => cases hp
    | choice _ _ => cases hp

/-- A5 IS THE STRIPPED PROGRAM: an A5 execution of `p` is an execution of `stripStatic p`. -/
theorem execA5_iff {src : Nat → Obj × Cell} {statics : List Root} {sh : Var → Bool}
    {i : Nat} {p : Prog} {s t : VState} :
    ExecA5 src statics sh i p s t ↔ ExecV src statics i (stripStatic sh p) s t :=
  ⟨ExecA5.toStrip, fun h => ExecA5.ofStrip h p rfl⟩

/-- VALUE ALIAS UNDER A5: one A5 execution of `p` from the frame entry makes `x.px` and `y.py`
the same value instance. -/
def CAliasA5 (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ vs, ExecA5 src statics (shB statics fr) 0 p (VState.init fr) vs ∧ AliasInV vs x px y py

/-- An A5 value alias is a value alias of the stripped program, and back. -/
theorem CAliasA5_iff {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame} {p : Prog}
    {x y : Var} {px py : List Cell} :
    CAliasA5 src statics fr p x px y py ↔
      CAliasV src statics fr (stripStatic (shB statics fr) p) x px y py :=
  ⟨fun ⟨vs, h1, h2⟩ => ⟨vs, execA5_iff.mp h1, h2⟩,
    fun ⟨vs, h1, h2⟩ => ⟨vs, execA5_iff.mpr h1, h2⟩⟩

/-! ## Soundness -/

/-- SOUNDNESS OF DESIGN VSS: for each naming, each list of static roots, each depth limit and
both strong-update policies, each A5 value alias is a may-alias of `mayProgVSS`. -/
theorem csoundVSS (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : CAliasA5 src statics fr p x px y py) :
    mayProgVSS eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rw [mayProgVSS_eq]
  exact csoundVS src statics eu K fr _ x px y py (CAliasA5_iff.mp h)

/-- No A5 execution gives two paths the same value instance if `mayProgVSS` answers false. -/
theorem no_alias_of_mayProgVSS (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool)
    (K : Nat) (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : mayProgVSS eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = false) :
    ¬ CAliasA5 src statics fr p x px y py := by
  intro ha
  have := csoundVSS src statics eu K fr p x px y py ha
  rw [h] at this; cases this

/-! ## The static cells keep their default content -/

/-- The origin of the entry object of a static root. -/
def statO (statics : List Root) : Origin → Bool
  | .sym (.root r) [] => statics.contains r
  | _ => false

/-- A cell name is never the origin of a static root. -/
theorem statO_childCN (statics : List Root) (K : Nat) (o : Origin) (c : ACell) :
    statO statics (childCN K o c) = false := by
  cases o with
  | sym b q =>
    show statO statics (symOrDeep K b (q ++ [c])) = false
    unfold symOrDeep
    split
    · cases b with
      | fresh s => rfl
      | root r => cases q <;> rfl
    · rfl
  | deep b => rfl
  | alloc y => rfl
  | havoc s => rfl
  | hsym s k c' q => show statO statics (if _ then _ else _) = false; split <;> rfl
  | hdeep s k c' => rfl

/-- The renaming of `retire` keeps the test `statO`. -/
theorem statO_renameO (statics : List Root) (s : Site) (o : Origin) :
    statO statics (renameO s o) = statO statics o := by
  unfold renameO
  split
  · rename_i e; subst e; rfl
  · rfl

/-- `statO` holds exactly for the entry origin of a static root. -/
theorem statO_root {statics : List Root} {r : Root} (hr : r ∈ statics) :
    statO statics (.sym (.root r) []) = true := List.contains_iff_mem.mpr hr

/-- THE STATIC INVARIANT: a static holder holds its root; no other program variable and no
cell holds a static root; each cell of a static root holds its default content (its name). -/
structure SCInv (cb : CtxB) (statics : List Root) (fr : Frame) (X : AState) : Prop where
  holder : ∀ x r, fr.root? x = some r → r ∈ statics → X.env x = [.sym (.root r) []]
  env : ∀ z, shB statics fr z = false → z ≠ cb.cn.xe → z ≠ cb.xv →
    ∀ o ∈ X.env z, statO statics o = false
  heap : ∀ o c, ∀ a ∈ X.heap o c, statO statics a = false
  cells : ∀ r ∈ statics, ∀ c,
    X.heap (.sym (.root r) []) c = [childCN cb.cn.ctx.K (.sym (.root r) []) c]

/-- A statement that keeps the static invariant: it uses static holders only as bases, it is not
a static write, and it does not name the reserved variables. -/
def StOK (cb : CtxB) (sh : Var → Bool) (st : Stmt) : Prop :=
  st.shOK sh = true ∧ st.staticWriteB sh = false ∧ ∀ v ∈ st.vars, v ≠ cb.cn.xe ∧ v ≠ cb.xv

variable {cb : CtxB} {statics : List Root} {fr : Frame}

/-- The entry state satisfies the static invariant. -/
theorem SCInv.init : SCInv cb statics fr (ainitV cb.cn.ctx.K fr) where
  holder := fun x r hx _ => by
    show (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) = _
    rw [hx]
  env := fun z hz _ _ o ho => by
    change o ∈ (match fr.root? z with | some r => [Origin.sym (.root r) []] | none => []) at ho
    unfold shB at hz
    cases e : fr.root? z with
    | none => rw [e] at ho; cases ho
    | some r =>
      rw [e] at ho hz
      rw [List.mem_singleton.mp ho]
      exact hz
  heap := fun o c a ha => by
    rw [List.mem_singleton.mp ha]; exact statO_childCN _ _ _ _
  cells := fun _ _ _ => rfl

/-- The static invariant after `setVar` of a variable that is not a static holder. -/
theorem SCInv.setVar {X : AState} (h : SCInv cb statics fr X) {x : Var}
    (hx : shB statics fr x = false) {S : List Origin} (hS : ∀ a ∈ S, statO statics a = false) :
    SCInv cb statics fr (X.setVar x S) where
  holder := fun x' r h1 h2 => by
    have hne : x' ≠ x := by
      intro e; subst e
      rw [shB_iff.mpr ⟨r, h1, h2⟩] at hx; cases hx
    show fupd X.env x S x' = _
    rw [fupd_ne _ _ hne]; exact h.holder x' r h1 h2
  env := fun z hz h1 h2 o ho => by
    change o ∈ fupd X.env x S z at ho
    by_cases e : z = x
    · subst e; rw [fupd_same] at ho; exact hS o ho
    · rw [fupd_ne _ _ e] at ho; exact h.env z hz h1 h2 o ho
  heap := h.heap
  cells := h.cells

/-- The static invariant after `setRet` of a result that is not a static holder. -/
theorem SCInv.setRet {X : AState} (h : SCInv cb statics fr X) {ret : Option Var}
    (hx : ∀ x, ret = some x → shB statics fr x = false) {S : List Origin}
    (hS : ∀ a ∈ S, statO statics a = false) : SCInv cb statics fr (X.setRet ret S) := by
  cases ret with
  | none => exact h
  | some x => exact h.setVar (hx x rfl) hS

/-- The static invariant after `retireV`. -/
theorem SCInv.retireV {X : AState} (h : SCInv cb statics fr X) (s : Site) :
    SCInv cb statics fr (ValueSem.retireV cb.cn.ctx.K s X) where
  holder := fun x r h1 h2 => by
    show renameL s (X.env x) = _
    rw [h.holder x r h1 h2]
    show [renameO s _] = _
    rw [renameO_of_ne_alloc s (fun _ e => by cases e)]
  env := fun z hz h1 h2 o ho => by
    change o ∈ renameL s (X.env z) at ho
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ho
    rw [statO_renameO]; exact h.env z hz h1 h2 b hb
  heap := fun o c a ha => by
    change a ∈ (if o = rNew s then [childCN cb.cn.ctx.K (rNew s) c] else (retire s X).heap o c)
      at ha
    split at ha
    · rw [List.mem_singleton.mp ha]; exact statO_childCN _ _ _ _
    · change a ∈ (if o = rNew s then [] else if o = rOld s then
        renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap o c)) at ha
      split at ha
      · cases ha
      · split at ha
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          rw [statO_renameO]
          rcases mem_uni.mp hb with hb | hb
          · exact h.heap _ _ b hb
          · exact h.heap _ _ b hb
        · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
          rw [statO_renameO]; exact h.heap _ _ b hb
  cells := fun r hr c => by
    have n1 : (Origin.sym (.root r) []) ≠ rNew s := fun e => by cases e
    have n2 : (Origin.sym (.root r) []) ≠ rOld s := fun e => by cases e
    change (if Origin.sym (.root r) [] = rNew s then [childCN cb.cn.ctx.K (rNew s) c]
      else (retire s X).heap (Origin.sym (.root r) []) c) = _
    rw [ite_eq_right n1]
    change (if Origin.sym (.root r) [] = rNew s then [] else if Origin.sym (.root r) [] = rOld s then
        renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c))
        else renameL s (X.heap (Origin.sym (.root r) []) c)) = _
    rw [ite_eq_right n1, ite_eq_right n2, h.cells r hr c]
    show [renameO s _] = _
    rw [renameO_of_ne_alloc s (childCN_ne_alloc _ _ _)]

/-- The static invariant after `setSets` (the reserved variables are not static holders). -/
theorem SCInv.setSets {X : AState} (h : SCInv cb statics fr X) (hxe : fr.root? cb.cn.xe = none)
    (hxv : fr.root? cb.xv = none) (E V : List Origin) :
    SCInv cb statics fr (ValueSem.setSets cb X E V) where
  holder := fun x r h1 h2 => by
    have n1 : x ≠ cb.cn.xe := fun e => by rw [e, hxe] at h1; cases h1
    have n2 : x ≠ cb.xv := fun e => by rw [e, hxv] at h1; cases h1
    show fupd (fupd X.env cb.cn.xe _) cb.xv _ x = _
    rw [fupd_ne _ _ n2, fupd_ne _ _ n1]; exact h.holder x r h1 h2
  env := fun z hz h1 h2 o ho => by
    change o ∈ fupd (fupd X.env cb.cn.xe _) cb.xv _ z at ho
    rw [fupd_ne _ _ h2, fupd_ne _ _ h1] at ho
    exact h.env z hz h1 h2 o ho
  heap := h.heap
  cells := h.cells

/-- The static invariant after the passive call. -/
theorem SCInv.callVS {X : AState} (h : SCInv cb statics fr X) (hxe : fr.root? cb.cn.xe = none)
    (hxv : fr.root? cb.xv = none) (args : List Var) :
    SCInv cb statics fr (ValueSem.callVS cb X args) := by
  unfold ValueSem.callVS
  split
  · exact h.setSets hxe hxv _ _
  · exact h.setSets hxe hxv _ _

/-- The static invariant after a weak store through origins that are not static roots. -/
theorem SCInv.weakStore {X : AState} (h : SCInv cb statics fr X) {os : List Origin}
    (hos : ∀ o ∈ os, statO statics o = false) (c : ACell) {S : List Origin}
    (hS : ∀ a ∈ S, statO statics a = false) : SCInv cb statics fr (X.weakStore os c S) where
  holder := h.holder
  env := h.env
  heap := fun o c' a ha => by
    change a ∈ (if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c') at ha
    split at ha
    · rcases mem_uni.mp ha with ha | ha
      · exact hS a ha
      · exact h.heap o c' a ha
    · exact h.heap o c' a ha
  cells := fun r hr c' => by
    have hn : ¬ (c' = c ∧ Origin.sym (.root r) [] ∈ os) := fun ⟨_, hm⟩ => by
      have := hos _ hm; rw [statO_root hr] at this; cases this
    show (if c' = c ∧ Origin.sym (.root r) [] ∈ os then _ else _) = _
    rw [ite_eq_right hn]; exact h.cells r hr c'

/-- The static invariant after a strong store into an origin that is not a static root. -/
theorem SCInv.setCell {X : AState} (h : SCInv cb statics fr X) {o : Origin}
    (ho : statO statics o = false) (c : ACell) {S : List Origin}
    (hS : ∀ a ∈ S, statO statics a = false) : SCInv cb statics fr (X.setCell o c S) where
  holder := h.holder
  env := h.env
  heap := fun o' c' a ha => by
    change a ∈ fupd2 X.heap o c S o' c' at ha
    by_cases e : o' = o ∧ c' = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same] at ha; exact hS a ha
    · rw [fupd2_ne _ _ e] at ha; exact h.heap o' c' a ha
  cells := fun r hr c' => by
    have hn : ¬ (Origin.sym (.root r) [] = o ∧ c' = c) := fun ⟨e, _⟩ => by
      rw [← e, statO_root hr] at ho; cases ho
    show fupd2 X.heap o c S _ c' = _
    rw [fupd2_ne _ _ hn]; exact h.cells r hr c'

/-- The static invariant after the store of design BO through a variable whose origins are not
static roots. -/
theorem SCInv.storeBO {X : AState} (h : SCInv cb statics fr X) {x : Var}
    (hx : ∀ o ∈ X.env x, statO statics o = false) (c : ACell) {S : List Origin}
    (hS : ∀ a ∈ S, statO statics a = false) :
    SCInv cb statics fr (BlockOnly.storeBO cb X x c S) := by
  unfold BlockOnly.storeBO
  split
  · rename_i o hs
    split
    · exact h.setCell (hx o (single?_spec hs).1) c hS
    · exact h.weakStore hx c hS
  · exact h.weakStore hx c hS

/-- The static invariant after a join. -/
theorem SCInv.join {X Y : AState} (hX : SCInv cb statics fr X) (hY : SCInv cb statics fr Y) :
    SCInv cb statics fr (DirectedAlias.join X Y) where
  holder := fun x r h1 h2 => by
    show uni (X.env x) (Y.env x) = _
    rw [hX.holder x r h1 h2, hY.holder x r h1 h2]
    exact List.insert_of_mem List.mem_cons_self
  env := fun z hz h1 h2 o ho => by
    rcases mem_uni.mp ho with ho | ho
    · exact hX.env z hz h1 h2 o ho
    · exact hY.env z hz h1 h2 o ho
  heap := fun o c a ha => by
    rcases mem_uni.mp ha with ha | ha
    · exact hX.heap o c a ha
    · exact hY.heap o c a ha
  cells := fun r hr c => by
    show uni (X.heap _ c) (Y.heap _ c) = _
    rw [hX.cells r hr c, hY.cells r hr c]
    exact List.insert_of_mem List.mem_cons_self

/-- The value of a variable that is not a static holder and not reserved has no static root. -/
theorem SCInv.var {X : AState} (h : SCInv cb statics fr X) {z : Var}
    (hz : shB statics fr z = false) (h1 : z ≠ cb.cn.xe ∧ z ≠ cb.xv) :
    ∀ o ∈ X.env z, statO statics o = false :=
  h.env z hz h1.1 h1.2

/-- A read never gives a static root. -/
theorem SCInv.aread {X : AState} (h : SCInv cb statics fr X) (S : List Origin) (c : ACell) :
    ∀ a ∈ DirectedAlias.aread X S c, statO statics a = false := by
  intro a ha
  obtain ⟨o, _, ha⟩ := mem_aread.mp ha
  exact h.heap o c a ha

/-- EACH STATEMENT THAT IS NOT A STATIC WRITE KEEPS THE STATIC INVARIANT. -/
theorem SCInv.step {X : AState} (h : SCInv cb statics fr X) (hxe : fr.root? cb.cn.xe = none)
    (hxv : fr.root? cb.xv = none) {i : Nat} {st : Stmt} (hst : StOK cb (shB statics fr) st) :
    SCInv cb statics fr (astepVS cb i st X) := by
  obtain ⟨hok, hw, hv⟩ := hst
  have nb : ∀ {b : Bool}, (!b) = true → b = false := fun {b} e => by
    cases b with
    | false => rfl
    | true => cases e
  cases st with
  | new x s =>
    exact (h.retireV s).setVar (nb hok) (fun a ha => by rw [List.mem_singleton.mp ha]; rfl)
  | null x =>
    exact h.setVar (nb hok) (fun a ha => by rw [List.mem_singleton.mp ha]; rfl)
  | copy x y =>
    simp only [Stmt.shOK, Bool.and_eq_true] at hok
    exact h.setVar (nb hok.1)
      (h.var (nb hok.2) (hv y (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
  | load x y f => exact h.setVar (nb hok) (h.aread _ _)
  | store x f y =>
    exact h.storeBO (h.var hw (hv x List.mem_cons_self)) _
      (h.var (nb hok) (hv y (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
  | aload x y => exact h.setVar (nb hok) (h.aread _ _)
  | astore x y =>
    exact h.weakStore (h.var hw (hv x List.mem_cons_self)) _
      (h.var (nb hok) (hv y (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
  | unknown x s =>
    exact (h.retireV s).setVar (nb hok) (fun a ha => by rw [List.mem_singleton.mp ha]; rfl)
  | call ret s args =>
    refine ((h.callVS hxe hxv args).retireV s).setRet (fun x e => ?_)
      (fun a ha => by rw [List.mem_singleton.mp ha]; rfl)
    subst e; exact nb hok

/-! ## Loops without fuel exhaustion -/

/-- The loop iteration reaches its post-fixpoint within `n` rounds, and each body run of the
iteration passes the test `g`. -/
def loopOKB (ctx : Ctx) (g : AState → Bool) (f : AState → AState) : Nat → AState → Bool
  | 0, _ => false
  | n + 1, Y => g Y && (leOn ctx (f Y) Y || loopOKB ctx g f n (DirectedAlias.join Y (f Y)))

/-- No loop of the analysis of design VS runs out of fuel (so no state is a top state). -/
def noTopB (cb : CtxB) : Nat → Prog → AState → Bool
  | _, .skip, _ => true
  | _, .stmt _, _ => true
  | i, .seq p q, X => noTopB cb i p X && noTopB cb (i + p.nulls) q (analyzeVS cb i p X)
  | i, .choice p q, X => noTopB cb i p X && noTopB cb (i + p.nulls) q X
  | i, .loop p, X => loopOKB cb.cn.ctx (noTopB cb i p) (analyzeVS cb i p) cb.cn.ctx.fuel X

/-- A program has no loop. -/
def _root_.DirectedAlias.Prog.loopFreeB : Prog → Bool
  | .skip => true
  | .stmt _ => true
  | .seq p q => p.loopFreeB && q.loopFreeB
  | .choice p q => p.loopFreeB && q.loopFreeB
  | .loop _ => false

/-- A loop-free program has no loop that runs out of fuel. -/
theorem noTopB_of_loopFree (cb : CtxB) : ∀ (p : Prog) (i : Nat) (X : AState),
    p.loopFreeB = true → noTopB cb i p X = true
  | .skip, _, _, _ => rfl
  | .stmt _, _, _, _ => rfl
  | .seq p q, i, X, h => by
    simp only [Prog.loopFreeB, Bool.and_eq_true] at h
    show (noTopB cb i p X && noTopB cb (i + p.nulls) q _) = true
    rw [noTopB_of_loopFree cb p i X h.1, noTopB_of_loopFree cb q _ _ h.2]; rfl
  | .choice p q, i, X, h => by
    simp only [Prog.loopFreeB, Bool.and_eq_true] at h
    show (noTopB cb i p X && noTopB cb (i + p.nulls) q X) = true
    rw [noTopB_of_loopFree cb p i X h.1, noTopB_of_loopFree cb q _ _ h.2]; rfl
  | .loop _, _, _, h => by cases h

/-- A loop iteration without fuel exhaustion keeps an invariant that the join and the body keep. -/
theorem loopIter_keeps_of_ok (ctx : Ctx) (P : AState → Prop) (g : AState → Bool)
    (f : AState → AState) (hf : ∀ Y, P Y → g Y = true → P (f Y))
    (hj : ∀ Y Z, P Y → P Z → P (DirectedAlias.join Y Z)) :
    ∀ (n : Nat) (Y : AState), P Y → loopOKB ctx g f n Y = true → P (loopIter ctx f n Y)
  | 0, _, _, h => by cases h
  | n + 1, Y, hY, h => by
    simp only [loopOKB, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hg, h2⟩ := h
    show P (if leOn ctx (f Y) Y = true then Y else loopIter ctx f n (DirectedAlias.join Y (f Y)))
    by_cases e : leOn ctx (f Y) Y = true
    · rw [ite_eq_left e]; exact hY
    · rw [ite_eq_right e]
      rcases h2 with h2 | h2
      · exact absurd h2 e
      · exact loopIter_keeps_of_ok ctx P g f hf hj n _ (hj Y _ hY (hf Y hY hg)) h2

/-- THE ANALYSIS KEEPS THE STATIC INVARIANT: on a program without static writes whose
statements keep the invariant, and without fuel exhaustion, each computed state keeps it. -/
theorem SCInv_analyze (hxe : fr.root? cb.cn.xe = none) (hxv : fr.root? cb.xv = none) :
    ∀ (q : Prog) (i : Nat) (X : AState), (∀ st ∈ q.stmts, StOK cb (shB statics fr) st) →
      SCInv cb statics fr X → noTopB cb i q X = true → SCInv cb statics fr (analyzeVS cb i q X)
  | .skip, _, _, _, h, _ => h
  | .stmt st, _, _, hs, h, _ => h.step hxe hxv (hs st (List.mem_singleton.mpr rfl))
  | .seq p q, i, X, hs, h, hn => by
    simp only [noTopB, Bool.and_eq_true] at hn
    have hp := SCInv_analyze hxe hxv p i X
      (fun st hst => hs st (List.mem_append.mpr (Or.inl hst))) h hn.1
    exact SCInv_analyze hxe hxv q _ _
      (fun st hst => hs st (List.mem_append.mpr (Or.inr hst))) hp hn.2
  | .choice p q, i, X, hs, h, hn => by
    simp only [noTopB, Bool.and_eq_true] at hn
    exact (SCInv_analyze hxe hxv p i X
      (fun st hst => hs st (List.mem_append.mpr (Or.inl hst))) h hn.1).join
      (SCInv_analyze hxe hxv q _ X
        (fun st hst => hs st (List.mem_append.mpr (Or.inr hst))) h hn.2)
  | .loop p, i, X, hs, h, hn =>
    loopIter_keeps_of_ok cb.cn.ctx (SCInv cb statics fr) (noTopB cb i p) (analyzeVS cb i p)
      (fun Y hY hg => SCInv_analyze hxe hxv p i Y hs hY hg) (fun _ _ h1 h2 => h1.join h2)
      cb.cn.ctx.fuel X h hn

/-- THE STATIC READ: in a state with the static invariant, `t = C.f` gives exactly `{⟨C.f⟩}`,
the default content of the cell of the static root. -/
theorem static_read {X : AState} (h : SCInv cb statics fr X) {i : Nat} {t x : Var} {f : Field}
    {r : Root} (hx : fr.root? x = some r) (hr : r ∈ statics) :
    (astepVS cb i (.load t x f) X).env t =
      [childCN cb.cn.ctx.K (.sym (.root r) []) (.fld f)] := by
  show fupd X.env t (DirectedAlias.aread X (X.env x) (.fld f)) t = _
  rw [fupd_same, h.holder x r hx hr]
  show uni (X.heap _ (.fld f)) [] = _
  rw [h.cells r hr]; rfl

/-- The array read through a static holder gives exactly the default content of its cell. -/
theorem static_aread {X : AState} (h : SCInv cb statics fr X) {i : Nat} {t x : Var}
    {r : Root} (hx : fr.root? x = some r) (hr : r ∈ statics) :
    (astepVS cb i (.aload t x) X).env t = [childCN cb.cn.ctx.K (.sym (.root r) []) .elem] := by
  show fupd X.env t (DirectedAlias.aread X (X.env x) .elem) t = _
  rw [fupd_same, h.holder x r hx hr]
  show uni (X.heap _ .elem) [] = _
  rw [h.cells r hr]; rfl

/-! ## Whole programs -/

/-- The reserved variables of the context of design VS have no root in the frame. -/
theorem ctxVS_res_none (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    fr.root? (ctxVS eu K statics fr p qf).cn.xe = none ∧
      fr.root? (ctxVS eu K statics fr p qf).xv = none := by
  have hpv : ∀ v ∈ fr.vars, v ∈ progVars fr p := fun v hv =>
    List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inr hv))
  have h1 : (ctxVS eu K statics fr p qf).cn.xe ∉ fr.vars := fun h =>
    Nat.lt_irrefl _ (lt_freshVar (hpv _ h))
  have h2 : (ctxVS eu K statics fr p qf).xv ∉ fr.vars := fun h =>
    Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) (lt_freshVar (hpv _ h)))
  exact ⟨Opt.lookup_none_of_not_mem fr.binds _ h1, Opt.lookup_none_of_not_mem fr.binds _ h2⟩

/-- A program variable is not a reserved variable of the context of design VS. -/
theorem ctxVS_res_prog (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) {v : Var} (hv : v ∈ p.vars) :
    v ≠ (ctxVS eu K statics fr p qf).cn.xe ∧ v ≠ (ctxVS eu K statics fr p qf).xv := by
  have hl : v < (ctxVS eu K statics fr p qf).cn.xe :=
    lt_freshVar (List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inl hv)))
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [e] at hl; exact Nat.lt_irrefl _ hl
  · have : v < (ctxVS eu K statics fr p qf).xv := Nat.lt_trans hl (Nat.lt_succ_self _)
    rw [e] at this; exact Nat.lt_irrefl _ this

/-- Each statement of the stripped program of a well-formed program keeps the static
invariant in the context of design VSS. -/
theorem stOK_strip (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) (hwf : StaticWF (shB statics fr) p) :
    ∀ st ∈ (stripStatic (shB statics fr) p).stmts,
      StOK (ctxVS eu K statics fr (stripStatic (shB statics fr) p) qf) (shB statics fr) st := by
  intro st hst
  obtain ⟨h1, h2⟩ := stmts_strip _ p st hst
  refine ⟨List.all_eq_true.mp hwf st h1, h2, fun v hv => ?_⟩
  exact ctxVS_res_prog eu K statics fr _ qf (List.mem_flatMap.mpr ⟨st, hst, hv⟩)

/-- THE STATIC CELLS KEEP THEIR DEFAULT: for a well-formed program without fuel exhaustion,
the final state of design VSS satisfies the static invariant. -/
theorem SCInv_analyzeProgVSS (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame)
    (p : Prog) (qf : List Field) (hwf : StaticWF (shB statics fr) p)
    (hnt : noTopB (ctxVS eu K statics fr (stripStatic (shB statics fr) p) qf) 0
      (stripStatic (shB statics fr) p) (ainitV K fr) = true) :
    SCInv (ctxVS eu K statics fr (stripStatic (shB statics fr) p) qf) statics fr
      (analyzeProgVSS eu K statics fr p qf) := by
  rw [analyzeProgVSS_eq]
  obtain ⟨h1, h2⟩ := ctxVS_res_none eu K statics fr (stripStatic (shB statics fr) p) qf
  exact SCInv_analyze h1 h2 _ 0 _ (stOK_strip eu K statics fr p qf hwf) SCInv.init hnt

/-- `static_cells_default`: in the final state of design VSS each cell of each static root holds
its default content `{⟨C.c⟩}`. -/
theorem static_cells_default (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame)
    (p : Prog) (qf : List Field) (hwf : StaticWF (shB statics fr) p)
    (hnt : noTopB (ctxVS eu K statics fr (stripStatic (shB statics fr) p) qf) 0
      (stripStatic (shB statics fr) p) (ainitV K fr) = true)
    {r : Root} (hr : r ∈ statics) (c : ACell) :
    (analyzeProgVSS eu K statics fr p qf).heap (.sym (.root r) []) c =
      [childCN K (.sym (.root r) []) c] :=
  (SCInv_analyzeProgVSS eu K statics fr p qf hwf hnt).cells r hr c

/-- A static read at the end of a well-formed program gives exactly `{⟨C.f⟩}`. -/
theorem static_read_end (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (pre : Prog)
    (qf : List Field) {t x : Var} {f : Field} {r : Root} (hx : fr.root? x = some r)
    (hr : r ∈ statics) (hwf : StaticWF (shB statics fr) (.seq pre (.stmt (.load t x f))))
    (hnt : noTopB (ctxVS eu K statics fr
      (stripStatic (shB statics fr) (.seq pre (.stmt (.load t x f)))) qf) 0
      (stripStatic (shB statics fr) (.seq pre (.stmt (.load t x f)))) (ainitV K fr) = true) :
    (analyzeProgVSS eu K statics fr (.seq pre (.stmt (.load t x f))) qf).env t =
      [childCN K (.sym (.root r) []) (.fld f)] := by
  let sh := shB statics fr
  let cb := ctxVS eu K statics fr (stripStatic sh (.seq pre (.stmt (.load t x f)))) qf
  obtain ⟨h1, h2⟩ := ctxVS_res_none eu K statics fr
    (stripStatic sh (.seq pre (.stmt (.load t x f)))) qf
  have hs := stOK_strip eu K statics fr _ qf hwf
  have hnt1 : noTopB cb 0 (stripStatic sh pre) (ainitV K fr) = true := by
    change (noTopB cb 0 (stripStatic sh pre) (ainitV K fr) && _) = true at hnt
    exact ((Bool.and_eq_true _ _).mp hnt).1
  have hpre : SCInv cb statics fr (analyzeVS cb 0 (stripStatic sh pre) (ainitV K fr)) :=
    SCInv_analyze h1 h2 _ 0 _ (fun st hst => hs st (List.mem_append.mpr (Or.inl hst)))
      SCInv.init hnt1
  rw [analyzeProgVSS_eq]
  show (analyzeVS cb (0 + (stripStatic sh pre).nulls)
    (stripStatic sh (.stmt (.load t x f))) (analyzeVS cb 0 (stripStatic sh pre) (ainitV K fr))).env t = _
  exact static_read hpre hx hr

end DirectedAlias.Sound.ValueSem
