import DirectedAlias.Sound.ValueSem.Soundness

/-!
# A deterministic executor for the instrumented strict narrow semantics

`runV` runs a program on instrumented states with explicit choices (branches, loop counts,
array indices, and the narrow havoc writes of each call, as `runP` of design CN). A successful
run is an `ExecV` execution (`runV_sound`), so the alias check `runAliasV` gives executable
witnesses of value aliases (`runAliasV_sound`).

`nullFree_obj`: in a program without `null` and `new` statements, every value of every
instrumented execution is an object. So a value alias is an object alias there, and a proof
that no strict narrow execution aliases two paths also shows that no instrumented execution
gives them the same value (`not_CAliasV_of_nullFree`).
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed

/-- Run one statement on an instrumented state. It uses the head choice for `aload`, `astore`
and `call`; `i` is the null site of a null statement. -/
def runStmtV (src : Nat → Obj × Cell) (statics : List Root) (i : Nat) :
    Stmt → List Choice → VState → Option (VState × List Choice)
  | .new x s, cs, vs =>
    some ({ vs with cs := (vs.cs.setVar x (some (.alloc s (vs.cs.cnt s)))).bump s }, cs)
  | .null x, cs, vs =>
    some ({ vs.setVarV x (.nul (.site i (vs.nc i))) with nc := fupd vs.nc i (vs.nc i + 1) }, cs)
  | .copy x y, cs, vs =>
    match vs.val y with
    | some v => some (vs.setVarV x v, cs)
    | none => none
  | .load x y f, cs, vs =>
    match vs.cs.env y with
    | some o => some (vs.setVarV x (vs.cell o (.fld f)), cs)
    | none => none
  | .store x f y, cs, vs =>
    match vs.cs.env x, vs.val y with
    | some o, some v => some (vs.setCellV o (.fld f) v, cs)
    | _, _ => none
  | .aload x y, .idx j :: cs, vs =>
    match vs.cs.env y with
    | some o => some (vs.setVarV x (vs.cell o (.elem j)), cs)
    | none => none
  | .astore x y, .idx j :: cs, vs =>
    match vs.cs.env x, vs.val y with
    | some o, some v => some (vs.setCellV o (.elem j) v, cs)
    | _, _ => none
  | .unknown x s, cs, vs =>
    some ({ vs with cs := (vs.cs.setVar x (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s }, cs)
  | .call ret s args, .havoc ws :: cs, vs =>
    match applyHavocN src vs.cs statics args s (vs.cs.cnt s) vs.cs.heap ws with
    | some h' =>
      some ({ vs with cs := ({ vs.cs with heap := h' }.setRet ret
        (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s }, cs)
    | none => none
  | _, _, _ => none

/-- Run `f` `n` times on instrumented states, and pass the rest of the choices along. -/
def runNV (f : List Choice → VState → Option (VState × List Choice)) :
    Nat → List Choice → VState → Option (VState × List Choice)
  | 0, cs, st => some (st, cs)
  | n + 1, cs, st =>
    match f cs st with
    | some (t, cs') => runNV f n cs' t
    | none => none

/-- Run a program on instrumented states with explicit choices; `i` is the null site of the
first null statement. -/
def runV (src : Nat → Obj × Cell) (statics : List Root) :
    Nat → Prog → List Choice → VState → Option (VState × List Choice)
  | _, .skip, cs, st => some (st, cs)
  | i, .stmt s, cs, st => runStmtV src statics i s cs st
  | i, .seq p q, cs, st =>
    match runV src statics i p cs st with
    | some (t, cs') => runV src statics (i + p.nulls) q cs' t
    | none => none
  | i, .choice p _, .left :: cs, st => runV src statics i p cs st
  | i, .choice p q, .right :: cs, st => runV src statics (i + p.nulls) q cs st
  | i, .loop p, .iter n :: cs, st => runNV (runV src statics i p) n cs st
  | _, _, _, _ => none

/-- The Boolean form of `AliasInV`. -/
def aliasInVB (vs : VState) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Bool :=
  match vs.evalV x px with
  | some v => decide (vs.evalV y py = some v)
  | none => false

/-- One-execution value alias check of an instrumented run from the frame entry. -/
def runAliasV (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (cs : List Choice) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Bool :=
  match runV src statics 0 p cs (VState.init fr) with
  | some (vs, _) => aliasInVB vs x px y py
  | none => false

/-- `aliasInVB` decides `AliasInV`. -/
theorem aliasInVB_iff {vs : VState} {x y : Var} {px py : List Cell} :
    aliasInVB vs x px y py = true ↔ AliasInV vs x px y py := by
  unfold aliasInVB AliasInV
  cases h : vs.evalV x px with
  | none => simp
  | some v => simp

/-- `runStmtV` agrees with `SStepV`. -/
theorem runStmtV_sound {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {st : Stmt}
    {cs cs' : List Choice} {s s' : VState} (h : runStmtV src statics i st cs s = some (s', cs')) :
    SStepV src statics i st s s' := by
  cases st with
  | new x a => simp only [runStmtV, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .new
  | null x => simp only [runStmtV, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .null
  | copy x y =>
    simp only [runStmtV] at h
    cases hv : s.val y with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .copy hv
  | load x y f =>
    simp only [runStmtV] at h
    cases he : s.cs.env y with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .load he
  | store x f y =>
    simp only [runStmtV] at h
    cases he : s.cs.env x with
    | none => rw [he] at h; cases h
    | some o =>
      cases hv : s.val y with
      | none => rw [he, hv] at h; cases h
      | some v =>
        rw [he, hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .store he hv
  | aload x y =>
    match cs, h with
    | .idx j :: cs, h =>
      simp only [runStmtV] at h
      cases he : s.cs.env y with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .aload j he
  | astore x y =>
    match cs, h with
    | .idx j :: cs, h =>
      simp only [runStmtV] at h
      cases he : s.cs.env x with
      | none => rw [he] at h; cases h
      | some o =>
        cases hv : s.val y with
        | none => rw [he, hv] at h; cases h
        | some v =>
          rw [he, hv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
          exact .astore j he hv
  | unknown x a =>
    simp only [runStmtV, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .unknown
  | call ret a args =>
    match cs, h with
    | .havoc ws :: cs, h =>
      simp only [runStmtV] at h
      cases ha : applyHavocN src s.cs statics args a (s.cs.cnt a) s.cs.heap ws with
      | none => rw [ha] at h; cases h
      | some h' =>
        rw [ha] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .call (applyHavocN_spec (fun _ _ => Or.inl rfl) ha)

/-- `runNV` of a sound runner gives a loop execution. -/
theorem runNV_sound {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {p : Prog}
    {f : List Choice → VState → Option (VState × List Choice)}
    (hf : ∀ {cs cs' s s'}, f cs s = some (s', cs') → ExecV src statics i p s s') :
    ∀ {n : Nat} {cs cs' : List Choice} {s s' : VState},
      runNV f n cs s = some (s', cs') → ExecV src statics i (.loop p) s s'
  | 0, cs, cs', s, s', h => by
    simp only [runNV, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .loopZero
  | n + 1, cs, cs', s, s', h => by
    simp only [runNV] at h
    cases hr : f cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .loopMore (hf hr) (runNV_sound hf h)

/-- `runV` agrees with `ExecV`: a successful run is an instrumented execution. -/
theorem runV_sound {src : Nat → Obj × Cell} {statics : List Root} :
    ∀ {i : Nat} {p : Prog} {cs cs' : List Choice} {s s' : VState},
      runV src statics i p cs s = some (s', cs') → ExecV src statics i p s s'
  | _, .skip, cs, cs', s, s', h => by
    simp only [runV, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .skip
  | _, .stmt st, cs, cs', s, s', h => by
    simp only [runV] at h; exact .stmt (runStmtV_sound h)
  | i, .seq p q, cs, cs', s, s', h => by
    simp only [runV] at h
    cases hr : runV src statics i p cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .seq (runV_sound hr) (runV_sound h)
  | _, .choice p q, .left :: cs, cs', s, s', h => by
    simp only [runV] at h; exact .choiceL (runV_sound h)
  | _, .choice p q, .right :: cs, cs', s, s', h => by
    simp only [runV] at h; exact .choiceR (runV_sound h)
  | _, .loop p, .iter n :: cs, cs', s, s', h => by
    simp only [runV] at h; exact runNV_sound (fun hr => runV_sound hr) h

/-- A successful value alias check proves a one-execution value alias. -/
theorem runAliasV_sound {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame}
    {p : Prog} {cs : List Choice} {x y : Var} {px py : List Cell}
    (h : runAliasV src statics fr p cs x px y py = true) : CAliasV src statics fr p x px y py := by
  unfold runAliasV at h
  cases hr : runV src statics 0 p cs (VState.init fr) with
  | none => rw [hr] at h; cases h
  | some r =>
    obtain ⟨vs, cs'⟩ := r
    rw [hr] at h
    exact ⟨vs, runV_sound hr, aliasInVB_iff.mp h⟩

/-! ## Programs without null and allocation statements -/

/-- A statement is neither `null` nor `new`. -/
def Stmt.nullFreeB : Stmt → Bool
  | .null _ => false
  | .new _ _ => false
  | _ => true

/-- A program has no `null` and no `new` statement. -/
def NullFree (p : Prog) : Prop := ∀ st ∈ p.stmts, Stmt.nullFreeB st = true

/-- All values of an instrumented state are objects: an unassigned variable has no tag, every
variable object and every object in a cell of a symbolic object is symbolic, and every cell of
a symbolic object holds an object. -/
structure ObjOnly (vs : VState) : Prop where
  nv : ∀ x, vs.cs.env x = none → vs.nv x = none
  env : ∀ x o, vs.cs.env x = some o → ∃ b p, o = .sym b p
  heap : ∀ b p c, ∃ b' p', vs.cs.heap (.sym b p) c = some (.sym b' p')

/-- The entry instrumented state has only object values. -/
theorem ObjOnly.init (fr : Frame) : ObjOnly (VState.init fr) where
  nv _ _ := rfl
  env x o he := by
    change (fr.root? x).map _ = some o at he
    cases e : fr.root? x with
    | none => rw [e] at he; cases he
    | some r => rw [e] at he; cases he; exact ⟨_, _, rfl⟩
  heap b p c := ⟨b, p ++ [c], rfl⟩

/-- The value of a variable of a state with only object values is an object. -/
theorem ObjOnly.val {vs : VState} (h : ObjOnly vs) {y : Var} {v : VVal} (hv : vs.val y = some v) :
    ∃ b p, v = .obj (.sym b p) := by
  unfold VState.val at hv
  cases e : vs.cs.env y with
  | some o =>
    rw [e] at hv; cases hv
    obtain ⟨b, p, rfl⟩ := h.env y o e
    exact ⟨b, p, rfl⟩
  | none => rw [e, h.nv y e] at hv; cases hv

/-- The value of a cell of a symbolic object of a state with only object values is a symbolic
object. -/
theorem ObjOnly.cell {vs : VState} (h : ObjOnly vs) (b : Base) (p : List Cell) (c : Cell) :
    ∃ b' p', vs.cell (.sym b p) c = .obj (.sym b' p') := by
  obtain ⟨b', p', e⟩ := h.heap b p c
  exact ⟨b', p', by unfold VState.cell; rw [e]⟩

/-- One step of a statement that is neither `null` nor `new` keeps only object values. -/
theorem ObjOnly.step {src : Nat → Obj × Cell} {statics : List Root} {i : Nat} {st : Stmt}
    {s s' : VState} (hf : Stmt.nullFreeB st = true) (h : ObjOnly s)
    (hs : SStepV src statics i st s s') : ObjOnly s' := by
  have setv : ∀ (vs : VState) (x : Var) (b : Base) (p : List Cell), ObjOnly vs →
      ObjOnly (vs.setVarV x (.obj (.sym b p))) := by
    intro vs x b p h
    refine ⟨fun y e => ?_, fun y o e => ?_, h.heap⟩
    · change fupd vs.cs.env x _ y = none at e
      by_cases ey : y = x
      · subst ey; rw [fupd_same] at e; cases e
      · rw [fupd_ne _ _ ey] at e; exact h.nv y e
    · change fupd vs.cs.env x _ y = some o at e
      by_cases ey : y = x
      · subst ey; rw [fupd_same] at e; cases e; exact ⟨_, _, rfl⟩
      · rw [fupd_ne _ _ ey] at e; exact h.env y o e
  have setc : ∀ (vs : VState) (o : Obj) (c : Cell) (b : Base) (p : List Cell), ObjOnly vs →
      ObjOnly (vs.setCellV o c (.obj (.sym b p))) := by
    intro vs o c b p h
    refine ⟨h.nv, h.env, fun b1 p1 c1 => ?_⟩
    show ∃ b' p', fupd2 vs.cs.heap o c (some (.sym b p)) (.sym b1 p1) c1 = some (.sym b' p')
    by_cases e : Obj.sym b1 p1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same]; exact ⟨b, p, rfl⟩
    · rw [fupd2_ne _ _ e]; exact h.heap b1 p1 c1
  cases hs with
  | new => cases hf
  | null => cases hf
  | copy hv =>
    obtain ⟨b, p, rfl⟩ := h.val hv
    exact setv _ _ b p h
  | @load x y f vs o he =>
    obtain ⟨b, p, rfl⟩ := h.env y o he
    obtain ⟨b', p', e⟩ := h.cell b p (.fld f)
    rw [e]; exact setv _ _ b' p' h
  | @aload x y vs o j he =>
    obtain ⟨b, p, rfl⟩ := h.env y o he
    obtain ⟨b', p', e⟩ := h.cell b p (.elem j)
    rw [e]; exact setv _ _ b' p' h
  | store _ hv =>
    obtain ⟨b, p, rfl⟩ := h.val hv
    exact setc _ _ _ b p h
  | astore _ _ hv =>
    obtain ⟨b, p, rfl⟩ := h.val hv
    exact setc _ _ _ b p h
  | @unknown x a =>
    refine ⟨fun y e => ?_, fun y o e => ?_, h.heap⟩
    · change fupd s.cs.env x _ y = none at e
      by_cases ey : y = x
      · subst ey; rw [fupd_same] at e; cases e
      · rw [fupd_ne _ _ ey] at e; exact h.nv y e
    · change fupd s.cs.env x _ y = some o at e
      by_cases ey : y = x
      · subst ey; rw [fupd_same] at e; cases e; exact ⟨_, _, rfl⟩
      · rw [fupd_ne _ _ ey] at e; exact h.env y o e
  | @call ret a args _ h' hh =>
    have hheap : ∀ b p c, ∃ b' p', h' (.sym b p) c = some (.sym b' p') := by
      intro b p c
      rcases hh (.sym b p) c with e | ⟨_, k, _, e⟩
      · rw [e]; exact h.heap b p c
      · exact ⟨_, _, e⟩
    cases ret with
    | none => exact ⟨h.nv, h.env, hheap⟩
    | some x =>
      refine ⟨fun y e => ?_, fun y o e => ?_, hheap⟩
      · change fupd s.cs.env x _ y = none at e
        by_cases ey : y = x
        · subst ey; rw [fupd_same] at e; cases e
        · rw [fupd_ne _ _ ey] at e; exact h.nv y e
      · change fupd s.cs.env x _ y = some o at e
        by_cases ey : y = x
        · subst ey; rw [fupd_same] at e; cases e; exact ⟨_, _, rfl⟩
        · rw [fupd_ne _ _ ey] at e; exact h.env y o e

/-- An instrumented execution of a program without `null` and `new` keeps only object values. -/
theorem ObjOnly.exec {src : Nat → Obj × Cell} {statics : List Root} :
    ∀ {i : Nat} {p : Prog} {s s' : VState}, NullFree p → ObjOnly s →
      ExecV src statics i p s s' → ObjOnly s' := by
  intro i p s s' hf h hx
  induction hx with
  | skip => exact h
  | stmt hs => exact h.step (hf _ (List.mem_singleton.mpr rfl)) hs
  | seq _ _ ih1 ih2 =>
    exact ih2 (fun st hs => hf st (List.mem_append_right _ hs))
      (ih1 (fun st hs => hf st (List.mem_append_left _ hs)) h)
  | choiceL _ ih => exact ih (fun st hs => hf st (List.mem_append_left _ hs)) h
  | choiceR _ ih => exact ih (fun st hs => hf st (List.mem_append_right _ hs)) h
  | loopZero => exact h
  | loopMore _ _ ih1 ih2 => exact ih2 hf (ih1 hf h)

/-- A path from a symbolic object in a state with only object values gives an object. -/
theorem ObjOnly.readV {vs : VState} (h : ObjOnly vs) :
    ∀ (b : Base) (p : List Cell) (q : List Cell) {v : VVal},
      vs.readV (.obj (.sym b p)) q = some v → ∃ o, v = .obj o
  | b, p, [], v, hr => by simp only [VState.readV, Option.some.injEq] at hr; exact ⟨_, hr.symm⟩
  | b, p, c :: cs, v, hr => by
    simp only [VState.readV] at hr
    obtain ⟨b', p', e⟩ := h.cell b p c
    rw [e] at hr
    exact ObjOnly.readV h b' p' cs hr

/-- In a state with only object values, each access path gives an object. -/
theorem ObjOnly.evalV {vs : VState} (h : ObjOnly vs) {x : Var} {p : List Cell} {v : VVal}
    (he : vs.evalV x p = some v) : ∃ o, v = .obj o := by
  unfold VState.evalV at he
  cases hv : vs.val x with
  | none => rw [hv] at he; cases he
  | some v0 =>
    rw [hv] at he
    obtain ⟨b, q, rfl⟩ := h.val hv
    exact h.readV b q p he

/-- IN A PROGRAM WITHOUT `null` AND `new`, A VALUE ALIAS IS AN OBJECT ALIAS: each instrumented
value alias is a strict narrow alias. -/
theorem CAliasV.toN_of_nullFree {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame}
    {p : Prog} {x y : Var} {px py : List Cell} (hf : NullFree p)
    (h : CAliasV src statics fr p x px y py) : CAliasN src statics fr p x px y py := by
  obtain ⟨vs, hx, v, h1, h2⟩ := h
  have ho := (ObjOnly.init fr).exec hf hx
  obtain ⟨o, rfl⟩ := ho.evalV h1
  exact CAliasV.toN_obj hx h1 h2

/-- In a program without `null` and `new`, no instrumented execution gives two paths the same
value if no strict narrow execution aliases them. -/
theorem not_CAliasV_of_nullFree {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame}
    {p : Prog} {x y : Var} {px py : List Cell} (hf : NullFree p)
    (h : ¬ CAliasN src statics fr p x px y py) : ¬ CAliasV src statics fr p x px y py :=
  fun ha => h (CAliasV.toN_of_nullFree hf ha)

/-- `NullFree` is decidable through its Boolean form. -/
theorem nullFree_of {p : Prog} (h : p.stmts.all Stmt.nullFreeB = true) : NullFree p :=
  fun st hs => List.all_eq_true.mp h st hs

end DirectedAlias.Sound.ValueSem
