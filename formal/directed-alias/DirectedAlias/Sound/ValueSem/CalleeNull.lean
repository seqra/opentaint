import DirectedAlias.Sound.ValueSem.Run

/-!
# A callee that writes new null instances

The instrumented semantics of `Concept.lean` lets a callee keep a reachable cell or write a NEW
OBJECT into it. This file extends it: the callee can also write a NEW NULL INSTANCE into a
reachable cell, distinct for each cell (`HavocW`; tag `callee s n k`, where `src k` is the cell).
The extended executions are `ExecW`, the extended value aliases `CAliasW`.

THE SIMULATION (`execW_sim`): replace each callee null `callee s n k` by the callee object
`sym (havoc s n k) []` (`phiV`). An extended execution becomes an execution of `ExecV`: a load
or store through the null instance would block, so the object is never read through; the
object is new and distinct for each cell, as the null instance. Each value alias of the extended
execution stays a value alias (`readV_sim`). So design VS is sound for the extended semantics
too (`csoundVS_W`), with no change to the analysis.
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed

variable {src : Nat → Obj × Cell} {statics : List Root}

/-! ## The extended semantics -/

/-- Strict narrow havoc with null writes: each cell keeps its value and its null tag, or a cell
of a narrow-reachable object gets a new object or a new null instance; the tag decodes to the
cell. -/
def HavocW (src : Nat → Obj × Cell) (statics : List Root) (vs : VState) (args : List Var)
    (s n : Nat) (h' : Heap) (nh' : Obj → Cell → NTag) : Prop :=
  ∀ o c, (h' o c = vs.cs.heap o c ∧ nh' o c = vs.nh o c) ∨
    (ReachN vs.cs statics args o ∧ ∃ k, src k = (o, c) ∧
      ((h' o c = some (.sym (.havoc s n k) []) ∧ nh' o c = vs.nh o c) ∨
        (h' o c = none ∧ nh' o c = .callee s n k)))

/-- One step of the extended semantics: a step of `SStepV`, or a call whose callee also writes
new null instances. -/
inductive SStepW (src : Nat → Obj × Cell) (statics : List Root) (i : Nat) :
    Stmt → VState → VState → Prop where
  | base {st vs vs'} : SStepV src statics i st vs vs' → SStepW src statics i st vs vs'
  | call {ret s args vs h' nh'} : HavocW src statics vs args s (vs.cs.cnt s) h' nh' →
      SStepW src statics i (.call ret s args) vs
        { vs with cs := ({ vs.cs with heap := h' }.setRet ret
            (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s, nh := nh' }

/-- Big-step execution of the extended semantics. -/
inductive ExecW (src : Nat → Obj × Cell) (statics : List Root) :
    Nat → Prog → VState → VState → Prop where
  | skip {i s} : ExecW src statics i .skip s s
  | stmt {i st s s'} : SStepW src statics i st s s' → ExecW src statics i (.stmt st) s s'
  | seq {i p q s t u} : ExecW src statics i p s t → ExecW src statics (i + p.nulls) q t u →
      ExecW src statics i (.seq p q) s u
  | choiceL {i p q s t} : ExecW src statics i p s t → ExecW src statics i (.choice p q) s t
  | choiceR {i p q s t} : ExecW src statics (i + p.nulls) q s t →
      ExecW src statics i (.choice p q) s t
  | loopZero {i p s} : ExecW src statics i (.loop p) s s
  | loopMore {i p s t u} : ExecW src statics i p s t → ExecW src statics i (.loop p) t u →
      ExecW src statics i (.loop p) s u

/-- Value alias in one execution of the extended semantics. -/
def CAliasW (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ vs, ExecW src statics 0 p (VState.init fr) vs ∧ AliasInV vs x px y py

/-! ## The simulation -/

/-- Replace a callee null instance by the callee object of the same tag. -/
def phiV : VVal → VVal
  | .nul (.callee s n k) => .obj (.sym (.havoc s n k) [])
  | v => v

/-- `phiV` keeps an object. -/
theorem phiV_obj (o : Obj) : phiV (.obj o) = .obj o := rfl

/-- The value of a variable after `setVarV`. -/
theorem val_setVarV (vs : VState) (x : Var) (v : VVal) (z : Var) :
    (vs.setVarV x v).val z = if z = x then some v else vs.val z := by
  cases v with
  | obj o =>
    unfold VState.val VState.setVarV
    show (match fupd vs.cs.env x (some o) z with
      | some o' => some (VVal.obj o') | none => (vs.nv z).map VVal.nul) = _
    by_cases e : z = x
    · subst e; rw [fupd_same, ite_eq_left rfl]
    · rw [fupd_ne _ _ e, ite_eq_right e]; rfl
  | nul t =>
    unfold VState.val VState.setVarV
    show (match fupd vs.cs.env x none z with
      | some o' => some (VVal.obj o') | none => (fupd vs.nv x (some t) z).map VVal.nul) = _
    by_cases e : z = x
    · subst e; rw [fupd_same, fupd_same, ite_eq_left rfl]; rfl
    · rw [fupd_ne _ _ e, fupd_ne _ _ e, ite_eq_right e]; rfl

/-- `setVarV` keeps the cells. -/
theorem cell_setVarV (vs : VState) (x : Var) (v : VVal) (o : Obj) (c : Cell) :
    (vs.setVarV x v).cell o c = vs.cell o c := by
  cases v <;> rfl

/-- The value of a cell after `setCellV`. -/
theorem cell_setCellV (vs : VState) (o : Obj) (c : Cell) (v : VVal) (o' : Obj) (c' : Cell) :
    (vs.setCellV o c v).cell o' c' = if o' = o ∧ c' = c then v else vs.cell o' c' := by
  cases v with
  | obj o1 =>
    unfold VState.cell VState.setCellV
    show (match fupd2 vs.cs.heap o c (some o1) o' c' with
      | some o2 => VVal.obj o2 | none => .nul (vs.nh o' c')) = _
    by_cases e : o' = o ∧ c' = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same, ite_eq_left ⟨rfl, rfl⟩]
    · rw [fupd2_ne _ _ e, ite_eq_right e]; rfl
  | nul t =>
    unfold VState.cell VState.setCellV
    show (match fupd2 vs.cs.heap o c none o' c' with
      | some o2 => VVal.obj o2 | none => .nul (fupd2 vs.nh o c t o' c')) = _
    by_cases e : o' = o ∧ c' = c
    · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same, fupd2_same, ite_eq_left ⟨rfl, rfl⟩]
    · rw [fupd2_ne _ _ e, fupd2_ne _ _ e, ite_eq_right e]; rfl

/-- `setCellV` keeps the variables. -/
theorem val_setCellV (vs : VState) (o : Obj) (c : Cell) (v : VVal) (z : Var) :
    (vs.setCellV o c v).val z = vs.val z := by
  cases v <;> rfl

/-- A variable holds an object if and only if its value is that object. -/
theorem env_of_val {vs : VState} {x : Var} {o : Obj} : vs.cs.env x = some o ↔ vs.val x = some (.obj o) := by
  unfold VState.val
  cases e : vs.cs.env x with
  | some o' => simp
  | none =>
    cases e2 : vs.nv x with
    | none => simp
    | some t => simp

/-- A cell holds an object if and only if its value is that object. -/
theorem heap_of_cell {vs : VState} {o o' : Obj} {c : Cell} :
    vs.cs.heap o c = some o' ↔ vs.cell o c = .obj o' := by
  unfold VState.cell
  cases e : vs.cs.heap o c with
  | some o1 => simp
  | none => simp

/-- THE SIMULATION RELATION: the second state has the counters of the first, and each variable
and each cell holds the image of the value of the first by `phiV`. -/
structure Sim (vs ws : VState) : Prop where
  cnt : ws.cs.cnt = vs.cs.cnt
  nc : ws.nc = vs.nc
  val : ∀ x, ws.val x = (vs.val x).map phiV
  cell : ∀ o c, ws.cell o c = phiV (vs.cell o c)

/-- A value without a callee tag is kept by `phiV`. -/
theorem phiV_of_not_callee {v : VVal} (h : ∀ s n k, v ≠ .nul (.callee s n k)) : phiV v = v := by
  cases v with
  | obj o => rfl
  | nul t =>
    cases t with
    | callee s n k => exact absurd rfl (h s n k)
    | _ => rfl

/-- The entry states are related. -/
theorem Sim.init (fr : Frame) : Sim (VState.init fr) (VState.init fr) where
  cnt := rfl
  nc := rfl
  val x := by
    unfold VState.val
    cases (VState.init fr).cs.env x with
    | some o => rfl
    | none => rfl
  cell o c := by
    symm
    apply phiV_of_not_callee
    intro s n k e
    unfold VState.cell at e
    cases h : (VState.init fr).cs.heap o c with
    | some o' => rw [h] at e; cases e
    | none => rw [h] at e; cases e

/-- A narrow-reachable object of the first state is narrow-reachable in the related state. -/
theorem Sim.reach {vs ws : VState} (h : Sim vs ws) {args : List Var} {o : Obj}
    (hr : ReachN vs.cs statics args o) : ReachN ws.cs statics args o := by
  induction hr with
  | arg hx he =>
    refine ReachN.arg hx (env_of_val.mpr ?_)
    rw [h.val, env_of_val.mp he]; rfl
  | static hr => exact ReachN.static hr
  | @step o1 o2 c _ hh ih =>
    refine ReachN.step (c := c) ih (heap_of_cell.mpr ?_)
    rw [h.cell, heap_of_cell.mp hh]; rfl

/-- Setting a variable keeps the relation. -/
theorem Sim.setVarV {vs ws : VState} (h : Sim vs ws) (x : Var) (v : VVal) :
    Sim (vs.setVarV x v) (ws.setVarV x (phiV v)) where
  cnt := by rw [setVarV_cs, setVarV_cs]; exact h.cnt
  nc := by cases v <;> cases (phiV _) <;> exact h.nc
  val z := by
    rw [val_setVarV, val_setVarV]
    split
    · rfl
    · exact h.val z
  cell o c := by rw [cell_setVarV, cell_setVarV]; exact h.cell o c

/-- Setting a cell keeps the relation. -/
theorem Sim.setCellV {vs ws : VState} (h : Sim vs ws) (o : Obj) (c : Cell) (v : VVal) :
    Sim (vs.setCellV o c v) (ws.setCellV o c (phiV v)) where
  cnt := by rw [setCellV_cs, setCellV_cs]; exact h.cnt
  nc := by cases v <;> cases (phiV _) <;> exact h.nc
  val z := by rw [val_setCellV, val_setCellV]; exact h.val z
  cell o' c' := by
    rw [cell_setCellV, cell_setCellV]
    split
    · rfl
    · exact h.cell o' c'

/-- `phiV` of the null instance of a null site is that null instance. -/
theorem phiV_site (i n : Nat) : phiV (.nul (.site i n)) = .nul (.site i n) := rfl

/-- ONE EXTENDED STEP IS SIMULATED BY ONE STEP OF `SStepV`. -/
theorem step_sim {i : Nat} {st : Stmt} {vs vs' ws : VState} (h : Sim vs ws)
    (hst : SStepW src statics i st vs vs') : ∃ ws', SStepV src statics i st ws ws' ∧ Sim vs' ws' := by
  -- the call with null writes, as a havoc of the related state
  have callCase : ∀ (ret : Option Var) (s : Site) (args : List Var) (h' : Heap)
      (nh' : Obj → Cell → NTag), HavocW src statics vs args s (vs.cs.cnt s) h' nh' →
      ∃ ws', SStepV src statics i (.call ret s args) ws ws' ∧
        Sim { vs with cs := ({ vs.cs with heap := h' }.setRet ret
          (some (.sym (.fresh s (vs.cs.cnt s)) []))).bump s, nh := nh' } ws' := by
    intro ret s args h' nh' hh
    let V' : VState := { vs with cs := { vs.cs with heap := h' }, nh := nh' }
    let hw : Heap := fun o c => (phiV (V'.cell o c)).toVal
    have hcs : ws.cs.cnt s = vs.cs.cnt s := by rw [h.cnt]
    have hH : HavocN src statics ws.cs args s (ws.cs.cnt s) hw := by
      intro o c
      rw [hcs]
      rcases hh o c with ⟨e1, e2⟩ | ⟨hr, k, hk, ⟨e1, _⟩ | ⟨e1, e2⟩⟩
      · left
        show (phiV (V'.cell o c)).toVal = ws.cs.heap o c
        have : V'.cell o c = vs.cell o c := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) =
            (match vs.cs.heap o c with | some o' => VVal.obj o' | none => .nul (vs.nh o c))
          rw [e1, e2]
        rw [this, ← h.cell, cell_toVal]
      · right
        refine ⟨h.reach hr, k, hk, ?_⟩
        show (phiV (V'.cell o c)).toVal = _
        have : V'.cell o c = .obj (.sym (.havoc s (vs.cs.cnt s) k) []) := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) = _
          rw [e1]
        rw [this]; rfl
      · right
        refine ⟨h.reach hr, k, hk, ?_⟩
        show (phiV (V'.cell o c)).toVal = _
        have : V'.cell o c = .nul (.callee s (vs.cs.cnt s) k) := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) = _
          rw [e1, e2]
        rw [this]; rfl
    refine ⟨_, .call hH, ?_⟩
    -- the cells after the call
    have hcellV : ∀ o c, ({ ws with cs := { ws.cs with heap := hw } } : VState).cell o c =
        phiV (V'.cell o c) := by
      intro o c
      show (match hw o c with | some o' => VVal.obj o' | none => .nul (ws.nh o c)) = _
      show (match (phiV (V'.cell o c)).toVal with
        | some o' => VVal.obj o' | none => .nul (ws.nh o c)) = _
      rcases hh o c with ⟨e1, e2⟩ | ⟨_, k, _, ⟨e1, _⟩ | ⟨e1, e2⟩⟩
      · have hv : V'.cell o c = vs.cell o c := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) =
            (match vs.cs.heap o c with | some o' => VVal.obj o' | none => .nul (vs.nh o c))
          rw [e1, e2]
        rw [hv, ← h.cell]
        unfold VState.cell
        cases ws.cs.heap o c <;> rfl
      · have : V'.cell o c = .obj (.sym (.havoc s (vs.cs.cnt s) k) []) := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) = _
          rw [e1]
        rw [this]; rfl
      · have : V'.cell o c = .nul (.callee s (vs.cs.cnt s) k) := by
          show (match h' o c with | some o' => VVal.obj o' | none => .nul (nh' o c)) = _
          rw [e1, e2]
        rw [this]; rfl
    cases ret with
    | none =>
      exact {
        cnt := by
          show fupd ws.cs.cnt s (ws.cs.cnt s + 1) = fupd vs.cs.cnt s (vs.cs.cnt s + 1)
          rw [h.cnt]
        nc := h.nc
        val := fun z => h.val z
        cell := fun o c => hcellV o c }
    | some x =>
      exact {
        cnt := by
          show fupd ws.cs.cnt s (ws.cs.cnt s + 1) = fupd vs.cs.cnt s (vs.cs.cnt s + 1)
          rw [h.cnt]
        nc := h.nc
        val := fun z => by
          have e := val_setVarV ({ ws with cs := { ws.cs with heap := hw } } : VState) x
            (.obj (.sym (.fresh s (ws.cs.cnt s)) [])) z
          have e' := val_setVarV V' x (.obj (.sym (.fresh s (vs.cs.cnt s)) [])) z
          change (VState.val ⟨_, _, _, _⟩ z) = _
          show (VState.setVarV { ws with cs := { ws.cs with heap := hw } } x
              (.obj (.sym (.fresh s (ws.cs.cnt s)) []))).val z =
            ((VState.setVarV V' x (.obj (.sym (.fresh s (vs.cs.cnt s)) []))).val z).map phiV
          rw [e, e', hcs]
          split
          · rfl
          · exact h.val z
        cell := fun o c => by
          show (VState.setVarV { ws with cs := { ws.cs with heap := hw } } x
              (.obj (.sym (.fresh s (ws.cs.cnt s)) []))).cell o c =
            phiV ((VState.setVarV V' x (.obj (.sym (.fresh s (vs.cs.cnt s)) []))).cell o c)
          rw [cell_setVarV, cell_setVarV]
          exact hcellV o c }
  cases hst with
  | call hh => exact callCase _ _ _ _ _ hh
  | base hb =>
    cases hb with
    | @new x a =>
      refine ⟨_, .new, ?_⟩
      have hc : ws.cs.cnt a = vs.cs.cnt a := congrFun h.cnt a
      have e := h.setVarV x (.obj (.alloc a (vs.cs.cnt a)))
      exact {
        cnt := by
          show fupd ws.cs.cnt a (ws.cs.cnt a + 1) = fupd vs.cs.cnt a (vs.cs.cnt a + 1)
          rw [h.cnt]
        nc := h.nc
        val := fun z => by
          show (ws.setVarV x (.obj (.alloc a (ws.cs.cnt a)))).val z =
            ((vs.setVarV x (.obj (.alloc a (vs.cs.cnt a)))).val z).map phiV
          rw [hc]; exact e.val z
        cell := fun o c => by
          show (ws.setVarV x (.obj (.alloc a (ws.cs.cnt a)))).cell o c =
            phiV ((vs.setVarV x (.obj (.alloc a (vs.cs.cnt a)))).cell o c)
          rw [hc]; exact e.cell o c }
    | @null x =>
      refine ⟨_, .null, ?_⟩
      have hn : ws.nc i = vs.nc i := congrFun h.nc i
      have e := h.setVarV x (.nul (.site i (vs.nc i)))
      exact {
        cnt := e.cnt
        nc := by show fupd ws.nc i (ws.nc i + 1) = fupd vs.nc i (vs.nc i + 1); rw [h.nc]
        val := fun z => by
          show (ws.setVarV x (.nul (.site i (ws.nc i)))).val z =
            ((vs.setVarV x (.nul (.site i (vs.nc i)))).val z).map phiV
          rw [hn]; exact e.val z
        cell := fun o c => by
          show (ws.setVarV x (.nul (.site i (ws.nc i)))).cell o c =
            phiV ((vs.setVarV x (.nul (.site i (vs.nc i)))).cell o c)
          rw [hn]; exact e.cell o c }
    | @copy x y _ v hv =>
      have hw : ws.val y = some (phiV v) := by rw [h.val, hv]; rfl
      exact ⟨_, .copy hw, h.setVarV x v⟩
    | @load x y f _ o he =>
      have hw : ws.cs.env y = some o := by
        apply env_of_val.mpr; rw [h.val, env_of_val.mp he]; rfl
      refine ⟨_, .load hw, ?_⟩
      have e := h.setVarV x (vs.cell o (.fld f))
      rw [← h.cell] at e
      exact e
    | @aload x y _ o j he =>
      have hw : ws.cs.env y = some o := by
        apply env_of_val.mpr; rw [h.val, env_of_val.mp he]; rfl
      refine ⟨_, .aload j hw, ?_⟩
      have e := h.setVarV x (vs.cell o (.elem j))
      rw [← h.cell] at e
      exact e
    | @store x f y _ o v he hv =>
      have hw : ws.cs.env x = some o := by
        apply env_of_val.mpr; rw [h.val, env_of_val.mp he]; rfl
      have hwv : ws.val y = some (phiV v) := by rw [h.val, hv]; rfl
      exact ⟨_, .store hw hwv, h.setCellV o (.fld f) v⟩
    | @astore x y _ o v j he hv =>
      have hw : ws.cs.env x = some o := by
        apply env_of_val.mpr; rw [h.val, env_of_val.mp he]; rfl
      have hwv : ws.val y = some (phiV v) := by rw [h.val, hv]; rfl
      exact ⟨_, .astore j hw hwv, h.setCellV o (.elem j) v⟩
    | @unknown x a =>
      refine ⟨_, .unknown, ?_⟩
      have hc : ws.cs.cnt a = vs.cs.cnt a := congrFun h.cnt a
      have e := h.setVarV x (.obj (.sym (.fresh a (vs.cs.cnt a)) []))
      exact {
        cnt := by
          show fupd ws.cs.cnt a (ws.cs.cnt a + 1) = fupd vs.cs.cnt a (vs.cs.cnt a + 1)
          rw [h.cnt]
        nc := h.nc
        val := fun z => by
          show (ws.setVarV x (.obj (.sym (.fresh a (ws.cs.cnt a)) []))).val z =
            ((vs.setVarV x (.obj (.sym (.fresh a (vs.cs.cnt a)) []))).val z).map phiV
          rw [hc]; exact e.val z
        cell := fun o c => by
          show (ws.setVarV x (.obj (.sym (.fresh a (ws.cs.cnt a)) []))).cell o c =
            phiV ((vs.setVarV x (.obj (.sym (.fresh a (vs.cs.cnt a)) []))).cell o c)
          rw [hc]; exact e.cell o c }
    | @call ret a args _ h' hh =>
      have hW : HavocW src statics vs args a (vs.cs.cnt a) h' vs.nh := by
        intro o c
        rcases hh o c with e | ⟨hr, k, hk, e⟩
        · exact Or.inl ⟨e, rfl⟩
        · exact Or.inr ⟨hr, k, hk, Or.inl ⟨e, rfl⟩⟩
      exact callCase ret a args h' vs.nh hW

/-- AN EXTENDED EXECUTION IS SIMULATED BY AN EXECUTION OF `ExecV`. -/
theorem execW_sim {i : Nat} {p : Prog} {vs vs' : VState} (hx : ExecW src statics i p vs vs') :
    ∀ {ws : VState}, Sim vs ws → ∃ ws', ExecV src statics i p ws ws' ∧ Sim vs' ws' := by
  induction hx with
  | skip => intro ws h; exact ⟨ws, .skip, h⟩
  | stmt hs =>
    intro ws h
    obtain ⟨ws', h1, h2⟩ := step_sim h hs
    exact ⟨ws', .stmt h1, h2⟩
  | seq _ _ ih1 ih2 =>
    intro ws h
    obtain ⟨t, h1, h2⟩ := ih1 h
    obtain ⟨u, h3, h4⟩ := ih2 h2
    exact ⟨u, .seq h1 h3, h4⟩
  | choiceL _ ih =>
    intro ws h
    obtain ⟨t, h1, h2⟩ := ih h
    exact ⟨t, .choiceL h1, h2⟩
  | choiceR _ ih =>
    intro ws h
    obtain ⟨t, h1, h2⟩ := ih h
    exact ⟨t, .choiceR h1, h2⟩
  | loopZero => intro ws h; exact ⟨ws, .loopZero, h⟩
  | loopMore _ _ ih1 ih2 =>
    intro ws h
    obtain ⟨t, h1, h2⟩ := ih1 h
    obtain ⟨u, h3, h4⟩ := ih2 h2
    exact ⟨u, .loopMore h1 h3, h4⟩

/-- A path that gives a value in the first state gives its image in the related state. -/
theorem readV_sim {vs ws : VState} (h : Sim vs ws) :
    ∀ (v : VVal) (p : List Cell) (r : VVal), vs.readV v p = some r → ws.readV (phiV v) p = some (phiV r)
  | v, [], r, hr => by
    simp only [VState.readV, Option.some.injEq] at hr
    subst hr; rfl
  | .obj o, c :: cs, r, hr => by
    simp only [VState.readV] at hr ⊢
    rw [phiV_obj]
    simp only [VState.readV]
    rw [h.cell]
    exact readV_sim h _ cs r hr
  | .nul t, c :: cs, r, hr => by simp [VState.readV] at hr

/-- An access path that gives a value in the first state gives its image in the related state. -/
theorem evalV_sim {vs ws : VState} (h : Sim vs ws) {x : Var} {p : List Cell} {r : VVal}
    (he : vs.evalV x p = some r) : ws.evalV x p = some (phiV r) := by
  unfold VState.evalV at he ⊢
  rw [h.val]
  cases hv : vs.val x with
  | none => rw [hv] at he; cases he
  | some v =>
    rw [hv] at he
    exact readV_sim h v p r he

/-- A value alias of the extended semantics is a value alias of `ExecV`. -/
theorem CAliasW.toV {fr : Frame} {p : Prog} {x y : Var} {px py : List Cell}
    (h : CAliasW src statics fr p x px y py) : CAliasV src statics fr p x px y py := by
  obtain ⟨vs, hx, v, h1, h2⟩ := h
  obtain ⟨ws, hw, hs⟩ := execW_sim hx (Sim.init fr)
  exact ⟨ws, hw, phiV v, evalV_sim hs h1, evalV_sim hs h2⟩

/-- SOUNDNESS OF DESIGN VS WHEN THE CALLEE ALSO WRITES NEW NULL INSTANCES: each one-execution
value alias of the extended semantics is a may-alias of `mayProgVS`, for each `K`, each policy
and each list of static roots. -/
theorem csoundVS_W (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell)
    (h : CAliasW src statics fr p x px y py) :
    mayProgVS eu K statics fr p x (px.map Cell.abs) y (py.map Cell.abs) = true :=
  csoundVS src statics eu K fr p x px y py h.toV

/-- Each execution of `ExecV` is an extended execution. -/
theorem ExecV.toW {i : Nat} {p : Prog} {s s' : VState} (h : ExecV src statics i p s s') :
    ExecW src statics i p s s' := by
  induction h with
  | skip => exact .skip
  | stmt hs => exact .stmt (.base hs)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | choiceL _ ih => exact .choiceL ih
  | choiceR _ ih => exact .choiceR ih
  | loopZero => exact .loopZero
  | loopMore _ _ ih1 ih2 => exact .loopMore ih1 ih2

/-- The extended value relation contains the value relation. -/
theorem CAliasV.toW {fr : Frame} {p : Prog} {x y : Var} {px py : List Cell}
    (h : CAliasV src statics fr p x px y py) : CAliasW src statics fr p x px y py := by
  obtain ⟨vs, hx, ha⟩ := h
  exact ⟨vs, hx.toW, ha⟩

end DirectedAlias.Sound.ValueSem
