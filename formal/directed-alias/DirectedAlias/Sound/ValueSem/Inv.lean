import DirectedAlias.Sound.ValueSem.Concept

/-!
# The invariant of design VS

The invariant `InvVS cb vs X` holds if, for some ghost naming `G` (the naming of design BO):
* the invariant of design BO holds for the projected foundation state (`InvG`, `InvXB`,
  `CntOKB`): every object of the state has its origin in the abstract set;
* `InvN`: every NULL INSTANCE of the state has its origin in the abstract set: the default
  null of cell `c` of object `O` has the cell name of `O` (`alphaN`), a null of site `i` has
  `null(i)`.

Beside it, the abstract state has no empty cell (`NE`). This is the key fact of design VS: a
call never needs to write, because each covered cell already holds a value, and a callee
object in cell `(O, c)` is named by an origin that is already in the abstract cell. With
`NE`, the passive call of design VS is the call of design BO (`callBO_eq`), so the proof of
design BO is reused for the call.
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Opt

/-! ## No empty cell -/

/-- No cell of the abstract state is empty. -/
def NE (X : AState) : Prop := ∀ o c, X.heap o c ≠ []

/-- A list with an element is not empty. -/
theorem ne_nil_of_mem {α : Type} {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  intro e; subst e; cases h

/-- No empty cell is closed upward under state inclusion. -/
theorem NE.mono {X Y : AState} (h : NE X) (hs : X.Sub Y) : NE Y := by
  intro o c e
  cases hx : X.heap o c with
  | nil => exact h o c hx
  | cons a l =>
    have hm : a ∈ X.heap o c := by rw [hx]; exact List.mem_cons_self
    have := hs.2 o c hm
    rw [e] at this; cases this

/-- The entry state of design VS has no empty cell. -/
theorem NE_ainitV (K : Nat) (fr : Frame) : NE (ainitV K fr) :=
  fun _ _ e => by cases e

/-- `retireV` keeps no empty cell. -/
theorem NE.retireV (K : Nat) (s : Site) {X : AState} (h : NE X) : NE (retireV K s X) := by
  intro o c
  show (if o = rNew s then [childCN K (rNew s) c] else (retire s X).heap o c) ≠ []
  split
  · exact fun e => by cases e
  · show (if o = rNew s then [] else if o = rOld s then
      renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap o c)) ≠ []
    rename_i hn
    rw [ite_eq_right hn]
    split
    · cases e : X.heap (rNew s) c with
      | nil => exact absurd e (h _ _)
      | cons a l =>
        exact ne_nil_of_mem (List.mem_map.mpr ⟨a, mem_uni.mpr (Or.inl List.mem_cons_self), rfl⟩)
    · cases e : X.heap o c with
      | nil => exact absurd e (h _ _)
      | cons a l => simp [renameL]

/-- `setVar` keeps no empty cell. -/
theorem NE.setVar {X : AState} (h : NE X) (x : Var) (S : List Origin) : NE (X.setVar x S) := h

/-- `setRet` keeps no empty cell. -/
theorem NE.setRet {X : AState} (h : NE X) (r : Option Var) (S : List Origin) :
    NE (X.setRet r S) := by
  cases r with
  | none => exact h
  | some x => exact h

/-- A weak store keeps no empty cell. -/
theorem NE.weakStore {X : AState} (h : NE X) (os : List Origin) (c : ACell) (S : List Origin) :
    NE (X.weakStore os c S) := by
  intro o c'
  show (if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c') ≠ []
  split
  · cases e : X.heap o c' with
    | nil => exact absurd e (h _ _)
    | cons a l => exact ne_nil_of_mem (mem_uni.mpr (Or.inr (List.mem_cons_self (a := a))))
  · exact h o c'

/-- A strong store of a non-empty set keeps no empty cell. -/
theorem NE.setCell {X : AState} (h : NE X) (o : Origin) (c : ACell) {S : List Origin}
    (hS : S ≠ []) : NE (X.setCell o c S) := by
  intro o' c'
  show fupd2 X.heap o c S o' c' ≠ []
  by_cases e : o' = o ∧ c' = c
  · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same]; exact hS
  · rw [fupd2_ne _ _ e]; exact h o' c'

/-- The store of design BO with a non-empty set keeps no empty cell. -/
theorem NE.storeBO (cb : CtxB) {X : AState} (h : NE X) (x : Var) (c : ACell) {S : List Origin}
    (hS : S ≠ []) : NE (storeBO cb X x c S) := by
  unfold BlockOnly.storeBO
  split
  · split
    · exact h.setCell _ c hS
    · exact h.weakStore _ c S
  · exact h.weakStore _ c S

/-- `setSets` does not change the heap. -/
theorem setSets_heap (cb : CtxB) (X : AState) (E V : List Origin) :
    (setSets cb X E V).heap = X.heap := rfl

/-- The passive call does not change the heap. -/
theorem callVS_heap (cb : CtxB) (X : AState) (args : List Var) :
    (callVS cb X args).heap = X.heap := by
  unfold callVS
  split <;> rfl

/-- The passive call keeps no empty cell. -/
theorem NE.callVS (cb : CtxB) {X : AState} (h : NE X) (args : List Var) :
    NE (ValueSem.callVS cb X args) := by
  intro o c; rw [callVS_heap]; exact h o c

/-- A join keeps no empty cell. -/
theorem NE.join {X : AState} (h : NE X) (Y : AState) : NE (join X Y) :=
  h.mono (sub_join_left X Y)

/-- A top state keeps no empty cell. -/
theorem NE.top (ctx : Ctx) {Y : AState} (h : NE Y) : NE (top ctx Y) :=
  h.mono (sub_top ctx Y)

/-- The loop iteration keeps no empty cell. -/
theorem NE.loopIter (ctx : Ctx) (f : AState → AState) (n : Nat) {Y : AState} (h : NE Y) :
    NE (loopIter ctx f n Y) :=
  h.mono (sub_loopIter ctx f n Y)

/-- WITHOUT EMPTY CELLS, THE PASSIVE CALL IS THE CALL OF DESIGN BO: the empty-cell writes of
design BO write nothing. -/
theorem callWith_eq_setSets (cb : CtxB) {X : AState} (h : NE X) (E V : List Origin)
    (cov : Origin → Bool) : callWith cb X E V cov = setSets cb X E V := by
  show AState.mk _ _ = AState.mk _ _
  congr 1
  funext o c
  have hne : ¬ (c ∈ cb.cn.ctx.cells ∧ cov o = true ∧ (X.heap o c).isEmpty = true) := by
    rintro ⟨_, _, h3⟩
    exact h o c (List.isEmpty_iff.mp h3)
  exact ite_eq_right hne

/-- WITHOUT EMPTY CELLS, `callBO = callVS`. -/
theorem callBO_eq (cb : CtxB) {X : AState} (h : NE X) (args : List Var) :
    callBO cb X args = callVS cb X args := by
  unfold callBO callVS
  cases closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | none => exact callWith_eq_setSets cb h _ _ _
  | some R => exact callWith_eq_setSets cb h _ _ _

/-! ## State inclusions -/

/-- `retire` is included in `retireV`. -/
theorem retire_sub_retireV (K : Nat) (s : Site) (X : AState) :
    (retire s X).Sub (retireV K s X) := by
  refine ⟨fun _ _ h => h, fun o c a h => ?_⟩
  show a ∈ (if o = rNew s then [childCN K (rNew s) c] else (retire s X).heap o c)
  split
  · rename_i e
    subst e
    change a ∈ (if rNew s = rNew s then [] else _) at h
    rw [ite_eq_left rfl] at h; cases h
  · exact h

/-- `setVar` keeps state inclusion. -/
theorem _root_.DirectedAlias.AState.Sub.setVar {X Y : AState} (h : X.Sub Y) (x : Var) (S : List Origin) :
    (X.setVar x S).Sub (Y.setVar x S) := by
  refine ⟨fun z a hz => ?_, h.2⟩
  show a ∈ fupd Y.env x S z
  change a ∈ fupd X.env x S z at hz
  by_cases e : z = x
  · subst e; rw [fupd_same] at hz ⊢; exact hz
  · rw [fupd_ne _ _ e] at hz ⊢; exact h.1 z hz

/-- `setRet` keeps state inclusion. -/
theorem _root_.DirectedAlias.AState.Sub.setRet {X Y : AState} (h : X.Sub Y) (r : Option Var) (S : List Origin) :
    (X.setRet r S).Sub (Y.setRet r S) := by
  cases r with
  | none => exact h
  | some x => exact h.setVar x S

/-- The null step of design BO is included in the null step of design VS. -/
theorem setVar_nil_sub (X : AState) (x : Var) (S : List Origin) :
    (X.setVar x []).Sub (X.setVar x S) := by
  refine ⟨fun z a hz => ?_, fun _ _ _ h => h⟩
  show a ∈ fupd X.env x S z
  change a ∈ fupd X.env x [] z at hz
  by_cases e : z = x
  · subst e; rw [fupd_same] at hz; cases hz
  · rw [fupd_ne _ _ e] at hz ⊢; exact hz

/-! ## Null tags -/

/-- The origin of a null instance: the default null of cell `c` of object `o` has the cell
name of `o`; a null of site `i` has `null(i)`. -/
def alphaN (K : Nat) : NTag → Origin
  | .dflt o c => childCN K (baseKey K o) c.abs
  | .site i _ => nullO i
  | .callee s _ _ => .havoc s

/-- The origin of a null instance is not an allocation origin. -/
theorem alphaN_ne_alloc (K : Nat) (t : NTag) (x : Nat) : alphaN K t ≠ .alloc x := by
  cases t with
  | dflt o c => exact childCN_ne_alloc K _ _ x
  | site i n => intro e; cases e
  | callee s n k => intro e; cases e

/-- The renaming of `retire` does not change an origin that is not an allocation origin. -/
theorem renameO_of_ne_alloc (s : Site) {o : Origin} (h : ∀ x, o ≠ .alloc x) : renameO s o = o := by
  unfold renameO
  split
  · rename_i e; exact absurd e (h _)
  · rfl

/-- The renaming of `retire` does not change the origin of a null instance. -/
theorem renameO_alphaN (K : Nat) (s : Site) (t : NTag) : renameO s (alphaN K t) = alphaN K t :=
  renameO_of_ne_alloc s (alphaN_ne_alloc K t)

/-- The cell name of `old(s)` is the cell name of `new(s)`. -/
theorem childCN_rOld (K : Nat) (s : Site) (c : ACell) :
    childCN K (rOld s) c = childCN K (rNew s) c := by
  have := childCN_renameO K s (rNew s) c
  unfold renameO at this
  rw [ite_eq_left rfl] at this
  exact this

/-- The default null of a cell of an allocated object has the cell name of the object. -/
theorem alphaN_dflt_alloc (cb : CtxB) (G : GNames) (cnt : Site → Nat) (s n : Nat) (c : Cell) :
    alphaN cb.cn.ctx.K (.dflt (.alloc s n) c) =
      childCN cb.cn.ctx.K (alphaBO cb G cnt (.alloc s n)) c.abs := by
  show childCN cb.cn.ctx.K (rOld s) c.abs =
    childCN cb.cn.ctx.K (if n + 1 = cnt s then rNew s else rOld s) c.abs
  split
  · exact childCN_rOld _ s _
  · rfl

/-! ## The invariant of the null instances -/

/-- Every null instance of the state has its origin in the abstract set. -/
structure InvN (cb : CtxB) (G : GNames) (vs : VState) (X : AState) : Prop where
  /-- A variable outside the universe has no null tag. -/
  nout : ∀ x, x ∉ cb.cn.ctx.vars → vs.nv x = none
  /-- A null in a variable has its origin in the abstract set of the variable. -/
  nenv : ∀ x ∈ cb.cn.ctx.vars, vs.cs.env x = none → ∀ t, vs.nv x = some t →
    alphaN cb.cn.ctx.K t ∈ X.env x
  /-- A null in a variable has a universe origin. -/
  nenvIn : ∀ x t, vs.cs.env x = none → vs.nv x = some t → alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins
  /-- A null in a universe cell of a live universe object has its origin in the abstract cell. -/
  nheap : ∀ o c, ¬ Dead cb.cn.ctx.once o → alphaBO cb G vs.cs.cnt o ∈ cb.cn.ctx.origins →
    c.abs ∈ cb.cn.ctx.cells → vs.cs.heap o c = none →
    alphaN cb.cn.ctx.K (vs.nh o c) ∈ X.heap (alphaBO cb G vs.cs.cnt o) c.abs
  /-- A null in a universe cell of a live universe object has a universe origin. -/
  nheapIn : ∀ o c, ¬ Dead cb.cn.ctx.once o → alphaBO cb G vs.cs.cnt o ∈ cb.cn.ctx.origins →
    c.abs ∈ cb.cn.ctx.cells → vs.cs.heap o c = none → alphaN cb.cn.ctx.K (vs.nh o c) ∈ cb.cn.ctx.origins
  /-- An object that no statement made has its default null tags. -/
  nfresh : ∀ s n c, vs.cs.cnt s ≤ n → vs.nh (.alloc s n) c = .dflt (.alloc s n) c

/-- The simulation invariant of design VS. -/
def InvVS (cb : CtxB) (vs : VState) (X : AState) : Prop :=
  ∃ G, InvG cb.cn.ctx (alphaBO cb G) vs.cs X ∧ InvXB cb G vs.cs X ∧ CntOKB G vs.cs.cnt ∧
    InvN cb G vs X

variable {cb : CtxB}

/-! ## Updates of the null facts -/

/-- The null facts are closed upward under state inclusion. -/
theorem InvN.mono {G : GNames} {vs : VState} {X Y : AState} (h : InvN cb G vs X) (hs : X.Sub Y) :
    InvN cb G vs Y :=
  { h with
    nenv := fun x hx he t ht => hs.1 x (h.nenv x hx he t ht)
    nheap := fun o c hd ho hc he => hs.2 _ _ (h.nheap o c hd ho hc he) }

/-- The null facts are closed upward under inclusion on the universe. -/
theorem InvN.mono_leOn {G : GNames} {vs : VState} {X Y : AState} (h : InvN cb G vs X)
    (hs : leOn cb.cn.ctx X Y = true) : InvN cb G vs Y := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp hs
  exact { h with
    nenv := fun x hx he t ht => h1 x hx (h.nenv x hx he t ht)
    nheap := fun o c hd ho hc he => h2 _ ho _ hc (h.nheap o c hd ho hc he) }

/-- The null facts hold for each top state. -/
theorem InvN.top {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X) (W : AState) :
    InvN cb G vs (top cb.cn.ctx W) :=
  { h with
    nenv := fun x _ he t ht => mem_uni.mpr (Or.inl (h.nenvIn x t he ht))
    nheap := fun o c hd ho hc he => mem_uni.mpr (Or.inl (h.nheapIn o c hd ho hc he)) }

/-- Setting a universe variable to a value keeps the null facts, if a null value has its origin
in the abstract set and in the universe. -/
theorem InvN.setVarV {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X) {x : Var}
    (hx : x ∈ cb.cn.ctx.vars) {v : VVal} {S : List Origin}
    (hv : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ S ∧ alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins) :
    InvN cb G (vs.setVarV x v) (X.setVar x S) := by
  cases v with
  | obj o =>
    exact {
      nout := h.nout
      nenv := fun y hy he t ht => by
        change fupd vs.cs.env x (some o) y = none at he
        show _ ∈ fupd X.env x S y
        by_cases e : y = x
        · subst e; rw [fupd_same] at he; cases he
        · rw [fupd_ne _ _ e] at he ⊢; exact h.nenv y hy he t ht
      nenvIn := fun y t he ht => by
        change fupd vs.cs.env x (some o) y = none at he
        by_cases e : y = x
        · subst e; rw [fupd_same] at he; cases he
        · rw [fupd_ne _ _ e] at he; exact h.nenvIn y t he ht
      nheap := h.nheap
      nheapIn := h.nheapIn
      nfresh := h.nfresh }
  | nul t0 =>
    exact {
      nout := fun y hy => by
        show fupd vs.nv x (some t0) y = none
        rw [fupd_ne _ _ (fun e => hy (by rw [e]; exact hx))]; exact h.nout y hy
      nenv := fun y hy he t ht => by
        change fupd vs.cs.env x none y = none at he
        change fupd vs.nv x (some t0) y = some t at ht
        show _ ∈ fupd X.env x S y
        by_cases e : y = x
        · subst e; rw [fupd_same] at ht ⊢; cases ht; exact (hv _ rfl).1
        · rw [fupd_ne _ _ e] at he ht ⊢; exact h.nenv y hy he t ht
      nenvIn := fun y t he ht => by
        change fupd vs.cs.env x none y = none at he
        change fupd vs.nv x (some t0) y = some t at ht
        by_cases e : y = x
        · subst e; rw [fupd_same] at ht; cases ht; exact (hv _ rfl).2
        · rw [fupd_ne _ _ e] at he ht; exact h.nenvIn y t he ht
      nheap := h.nheap
      nheapIn := h.nheapIn
      nfresh := h.nfresh }

/-- Setting the optional result variable to an object keeps the null facts. -/
theorem InvN.setRetObj {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X)
    {ret : Option Var} (hr : ∀ x, ret = some x → x ∈ cb.cn.ctx.vars) (o : Obj) (S : List Origin) :
    InvN cb G { vs with cs := vs.cs.setRet ret (some o) } (X.setRet ret S) := by
  cases ret with
  | none => exact h
  | some x => exact h.setVarV (v := .obj o) (hr x rfl) (fun _ e => by cases e)

/-- The foundation heap after `setCellV`. -/
theorem setCellV_heap (vs : VState) (o : Obj) (c : Cell) (v : VVal) :
    (vs.setCellV o c v).cs.heap = fupd2 vs.cs.heap o c v.toVal := by
  rw [setCellV_cs]; rfl

/-- `setCellV` keeps the null tags of the other cells. -/
theorem setCellV_nh_ne (vs : VState) {o o1 : Obj} {c c1 : Cell} (v : VVal)
    (h : ¬ (o1 = o ∧ c1 = c)) : (vs.setCellV o c v).nh o1 c1 = vs.nh o1 c1 := by
  cases v with
  | obj _ => rfl
  | nul t => exact fupd2_ne _ _ h

/-- After `setCellV` of a null instance, the cell has its tag. -/
theorem setCellV_nh_same (vs : VState) (o : Obj) (c : Cell) {v : VVal} (h : v.toVal = none) :
    ∃ t, v = .nul t ∧ (vs.setCellV o c v).nh o c = t := by
  cases v with
  | obj _ => cases h
  | nul t => exact ⟨t, rfl, fupd2_same _ _ _ _⟩

/-- A concrete store keeps the null facts; the caller gives the abstract heap facts. -/
theorem InvN.write {G : GNames} {vs : VState} {X Y : AState} (h : InvN cb G vs X) {o : Obj}
    {c : Cell} {v : VVal} (henv : ∀ x, Y.env x = X.env x)
    (hv : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins)
    (hnew : ¬ Dead cb.cn.ctx.once o → alphaBO cb G vs.cs.cnt o ∈ cb.cn.ctx.origins →
      c.abs ∈ cb.cn.ctx.cells → ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈
        Y.heap (alphaBO cb G vs.cs.cnt o) c.abs)
    (hold : ∀ o1 c1, ¬ (o1 = o ∧ c1 = c) → ¬ Dead cb.cn.ctx.once o1 →
      alphaBO cb G vs.cs.cnt o1 ∈ cb.cn.ctx.origins → c1.abs ∈ cb.cn.ctx.cells →
      ∀ a, a ∈ X.heap (alphaBO cb G vs.cs.cnt o1) c1.abs → a ∈ Y.heap (alphaBO cb G vs.cs.cnt o1) c1.abs)
    (hfr : ∀ s n, o = .alloc s n → n < vs.cs.cnt s) :
    InvN cb G (vs.setCellV o c v) Y where
  nout := by cases v <;> exact h.nout
  nenv := fun x hx he t ht => by
    rw [henv]
    cases v with
    | obj _ => exact h.nenv x hx he t ht
    | nul _ => exact h.nenv x hx he t ht
  nenvIn := fun x t he ht => by cases v <;> exact h.nenvIn x t he ht
  nheap := fun o1 c1 hd ho hc he => by
    have hcnt : (vs.setCellV o c v).cs.cnt = vs.cs.cnt := by rw [setCellV_cs]; rfl
    rw [hcnt] at ho ⊢
    rw [setCellV_heap] at he
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e
      rw [fupd2_same] at he
      obtain ⟨t, rfl, ht⟩ := setCellV_nh_same vs o1 c1 he
      rw [ht]; exact hnew hd ho hc t rfl
    · rw [fupd2_ne _ _ e] at he
      rw [setCellV_nh_ne vs v e]
      exact hold o1 c1 e hd ho hc _ (h.nheap o1 c1 hd ho hc he)
  nheapIn := fun o1 c1 hd ho hc he => by
    have hcnt : (vs.setCellV o c v).cs.cnt = vs.cs.cnt := by rw [setCellV_cs]; rfl
    rw [hcnt] at ho
    rw [setCellV_heap] at he
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e
      rw [fupd2_same] at he
      obtain ⟨t, rfl, ht⟩ := setCellV_nh_same vs o1 c1 he
      rw [ht]; exact hv t rfl
    · rw [fupd2_ne _ _ e] at he
      rw [setCellV_nh_ne vs v e]
      exact h.nheapIn o1 c1 hd ho hc he
  nfresh := fun s n c1 hn => by
    have hcnt : (vs.setCellV o c v).cs.cnt = vs.cs.cnt := by rw [setCellV_cs]; rfl
    rw [hcnt] at hn
    have hne : ¬ (Obj.alloc s n = o ∧ c1 = c) := by
      rintro ⟨e, _⟩
      have := hfr s n e.symm
      omega
    rw [setCellV_nh_ne vs v hne]
    exact h.nfresh s n c1 hn

/-- A weak store keeps the null facts. -/
theorem InvN.weak {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X) {o : Obj}
    {c : Cell} {v : VVal} {os S : List Origin} (hos : alphaBO cb G vs.cs.cnt o ∈ os)
    (hv : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ S ∧ alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins)
    (hfr : ∀ s n, o = .alloc s n → n < vs.cs.cnt s) :
    InvN cb G (vs.setCellV o c v) (X.weakStore os c.abs S) := by
  refine h.write (Y := X.weakStore os c.abs S) (fun _ => rfl) (fun t e => (hv t e).2) ?_ ?_ hfr
  · intro _ _ _ t e
    show _ ∈ (if c.abs = c.abs ∧ alphaBO cb G vs.cs.cnt o ∈ os then
      uni S (X.heap (alphaBO cb G vs.cs.cnt o) c.abs) else X.heap (alphaBO cb G vs.cs.cnt o) c.abs)
    rw [ite_eq_left ⟨rfl, hos⟩]
    exact mem_uni.mpr (Or.inl (hv t e).1)
  · intro o1 c1 _ _ _ _ a ha
    show a ∈ (if c1.abs = c.abs ∧ alphaBO cb G vs.cs.cnt o1 ∈ os then
      uni S (X.heap (alphaBO cb G vs.cs.cnt o1) c1.abs) else X.heap (alphaBO cb G vs.cs.cnt o1) c1.abs)
    split
    · exact mem_uni.mpr (Or.inr ha)
    · exact ha

/-- A strong store keeps the null facts if the target origin denotes one live object. -/
theorem InvN.strong {G : GNames} {vs : VState} {X : AState} (h : InvN cb G vs X) {o : Obj}
    {f : Field} {v : VVal} {S : List Origin}
    (huniq : ∀ o1, ¬ Dead cb.cn.ctx.once o1 → alphaBO cb G vs.cs.cnt o1 = alphaBO cb G vs.cs.cnt o →
      o1 = o)
    (hv : ∀ t, v = .nul t → alphaN cb.cn.ctx.K t ∈ S ∧ alphaN cb.cn.ctx.K t ∈ cb.cn.ctx.origins)
    (hfr : ∀ s n, o = .alloc s n → n < vs.cs.cnt s) :
    InvN cb G (vs.setCellV o (.fld f) v) (X.setCell (alphaBO cb G vs.cs.cnt o) (.fld f) S) := by
  refine h.write (Y := X.setCell (alphaBO cb G vs.cs.cnt o) (.fld f) S) (fun _ => rfl) (fun t e => (hv t e).2) ?_ ?_ hfr
  · intro _ _ _ t e
    show _ ∈ fupd2 X.heap (alphaBO cb G vs.cs.cnt o) (.fld f) S (alphaBO cb G vs.cs.cnt o) (Cell.fld f).abs
    exact (fupd2_same X.heap (alphaBO cb G vs.cs.cnt o) (ACell.fld f) S).symm ▸ (hv t e).1
  · intro o1 c1 hne hd _ _ a ha
    show a ∈ fupd2 X.heap (alphaBO cb G vs.cs.cnt o) (.fld f) S (alphaBO cb G vs.cs.cnt o1) c1.abs
    have e2 : ¬ (alphaBO cb G vs.cs.cnt o1 = alphaBO cb G vs.cs.cnt o ∧ c1.abs = .fld f) := by
      rintro ⟨h1, h2⟩
      apply hne
      refine ⟨huniq o1 hd h1, ?_⟩
      cases c1 with
      | fld g => simp only [Cell.abs, ACell.fld.injEq] at h2; rw [h2]
      | elem i => simp [Cell.abs] at h2
    rw [fupd2_ne _ _ e2]
    exact ha

/-- A counter bump with `retireV` keeps the null facts. -/
theorem InvN.retire (hc : CtxBOK cb) {G : GNames} {vs : VState} {X : AState} (s : Site)
    (hle : GhostLe G vs.cs.cnt) (h : InvN cb G vs X) :
    InvN cb G { vs with cs := vs.cs.bump s } (retireV cb.cn.ctx.K s X) := by
  have hb := fun {o : Obj} (ho : o ≠ .alloc s (vs.cs.cnt s)) => alphaBO_bump (cb := cb) vs.cs hle s ho
  have hcnt : ∀ a, vs.cs.cnt a ≤ (vs.cs.bump s).cnt a := by
    intro a
    show vs.cs.cnt a ≤ fupd vs.cs.cnt s (vs.cs.cnt s + 1) a
    by_cases e : a = s
    · subst e; rw [fupd_same]; exact Nat.le_succ _
    · rw [fupd_ne _ _ e]; exact Nat.le_refl _
  exact {
    nout := h.nout
    nenv := fun x hx he t ht => by
      show _ ∈ renameL s (X.env x)
      rw [← renameO_alphaN cb.cn.ctx.K s t]
      exact List.mem_map.mpr ⟨_, h.nenv x hx he t ht, rfl⟩
    nenvIn := h.nenvIn
    nheap := fun o c hd hin hc1 he => by
      change vs.cs.heap o c = none at he
      by_cases e : o = .alloc s (vs.cs.cnt s)
      · subst e
        rw [alphaBO_new]
        rw [h.nfresh s _ c (Nat.le_refl _)]
        show _ ∈ (if rNew s = rNew s then [childCN cb.cn.ctx.K (rNew s) c.abs] else _)
        rw [ite_eq_left rfl, alphaN_dflt_alloc cb G (vs.cs.bump s).cnt, alphaBO_new]
        exact List.mem_singleton.mpr rfl
      · rw [hb e] at hin ⊢
        have hold := h.nheap o c hd (mem_of_renameO hc.cn.base s hin) hc1 he
        show _ ∈ (if renameO s (alphaBO cb G vs.cs.cnt o) = rNew s then _ else
          (Recency.retire s X).heap (renameO s (alphaBO cb G vs.cs.cnt o)) c.abs)
        rw [ite_eq_right (renameO_ne_new s _)]
        show _ ∈ (if renameO s (alphaBO cb G vs.cs.cnt o) = rNew s then []
          else if renameO s (alphaBO cb G vs.cs.cnt o) = rOld s then
            renameL s (uni (X.heap (rNew s) c.abs) (X.heap (rOld s) c.abs))
          else renameL s (X.heap (renameO s (alphaBO cb G vs.cs.cnt o)) c.abs))
        rw [ite_eq_right (renameO_ne_new s _)]
        rw [← renameO_alphaN cb.cn.ctx.K s (vs.nh o c)]
        split
        · rename_i e2
          refine List.mem_map.mpr ⟨_, mem_uni.mpr ?_, rfl⟩
          unfold renameO at e2
          split at e2
          · rename_i e3; rw [e3] at hold; exact Or.inl hold
          · rw [e2] at hold; exact Or.inr hold
        · rename_i e2
          have e3 : renameO s (alphaBO cb G vs.cs.cnt o) = alphaBO cb G vs.cs.cnt o := by
            unfold renameO at e2 ⊢
            split
            · rename_i e4; rw [ite_eq_left e4] at e2; exact absurd rfl e2
            · rfl
          rw [e3]
          exact List.mem_map.mpr ⟨_, hold, rfl⟩
    nheapIn := fun o c hd hin hc1 he => by
      change vs.cs.heap o c = none at he
      by_cases e : o = .alloc s (vs.cs.cnt s)
      · subst e
        rw [alphaBO_new] at hin
        rw [h.nfresh s _ c (Nat.le_refl _), alphaN_dflt_alloc cb G (vs.cs.bump s).cnt, alphaBO_new]
        exact hc.cn.childIn _ hin _ hc1
      · rw [hb e] at hin
        exact h.nheapIn o c hd (mem_of_renameO hc.cn.base s hin) hc1 he
    nfresh := fun a n c hn => h.nfresh a n c (Nat.le_trans (hcnt a) hn) }

/-- The passive call keeps the null facts for the ghost naming after the call: a callee writes
only objects, so a null cell after the call is a null cell before it, and its holder keeps its
origin. -/
theorem InvN.call {src : Nat → Obj × Cell} {G : GNames} {vs : VState}
    {X : AState} {args : List Var} {s : Site} {h' : Heap}
    (hx : InvXB cb G vs.cs X) (hcnt : CntOKB G vs.cs.cnt) (h : InvN cb G vs X)
    (hh : HavocN src cb.cn.statics vs.cs args s (vs.cs.cnt s) h') :
    InvN cb (ghostsAfter cb G src vs.cs.cnt h' (callVS cb X args) s (vs.cs.cnt s))
      { vs with cs := { vs.cs with heap := h' } } (callVS cb X args) := by
  have hkeep : ∀ o c, h' o c = none → vs.cs.heap o c = none := by
    intro o c e
    rcases hh o c with e2 | ⟨_, _, _, e2⟩
    · rw [← e2]; exact e
    · rw [e2] at e; cases e
  have hnj : ∀ o c, vs.cs.heap o c = none → isJunk (alphaBO cb G vs.cs.cnt o) = false := by
    intro o c e
    cases hj : isJunk (alphaBO cb G vs.cs.cnt o) with
    | false => rfl
    | true =>
      exfalso
      rw [hx.junkDflt o c hj] at e
      cases o with
      | alloc a n =>
        revert hj
        show isJunk (if n + 1 = vs.cs.cnt a then rNew a else rOld a) = true → False
        split <;> intro h1 <;> cases h1
      | sym b p => cases e
  have hag : ∀ o c, vs.cs.heap o c = none →
      alphaBO cb (ghostsAfter cb G src vs.cs.cnt h' (callVS cb X args) s (vs.cs.cnt s)) vs.cs.cnt o =
        alphaBO cb G vs.cs.cnt o :=
    fun o c e => alphaBO_after hcnt (hnj o c e)
  have henv : ∀ x a, a ∈ X.env x → a ∈ (callVS cb X args).env x := by
    intro x a ha
    unfold callVS
    split <;>
    · show a ∈ fupd (fupd X.env cb.cn.xe _) cb.xv _ x
      by_cases e1 : x = cb.xv
      · subst e1; rw [fupd_same]; exact mem_uni.mpr (Or.inr ha)
      · rw [fupd_ne _ _ e1]
        by_cases e2 : x = cb.cn.xe
        · subst e2; rw [fupd_same]; exact mem_uni.mpr (Or.inr ha)
        · rw [fupd_ne _ _ e2]; exact ha
  exact {
    nout := h.nout
    nenv := fun x hx1 he t ht => henv x _ (h.nenv x hx1 he t ht)
    nenvIn := h.nenvIn
    nheap := fun o c hd hin hc1 he => by
      change h' o c = none at he
      have he0 := hkeep o c he
      change alphaBO cb _ vs.cs.cnt o ∈ _ at hin
      rw [hag o c he0] at hin
      show _ ∈ (callVS cb X args).heap (alphaBO cb _ vs.cs.cnt o) c.abs
      rw [hag o c he0, callVS_heap]
      exact h.nheap o c hd hin hc1 he0
    nheapIn := fun o c hd hin hc1 he => by
      change h' o c = none at he
      have he0 := hkeep o c he
      change alphaBO cb _ vs.cs.cnt o ∈ _ at hin
      rw [hag o c he0] at hin
      exact h.nheapIn o c hd hin hc1 he0
    nfresh := h.nfresh }

/-! ## The invariant -/

/-- The invariant of design VS is closed upward under state inclusion. -/
theorem InvVS.mono {vs : VState} {X Y : AState} (h : InvVS cb vs X) (hs : X.Sub Y) :
    InvVS cb vs Y :=
  let ⟨G, hg, hx, hn, hN⟩ := h
  ⟨G, hg.mono hs, hx.mono (fun _ ha => hs.1 _ ha) (fun _ ha => hs.1 _ ha), hn, hN.mono hs⟩

/-- The invariant of design VS is closed upward under inclusion on the universe. -/
theorem InvVS.mono_leOn (hc : CtxBOK cb) {vs : VState} {X Y : AState} (h : InvVS cb vs X)
    (hs : leOn cb.cn.ctx X Y = true) : InvVS cb vs Y :=
  let ⟨G, hg, hx, hn, hN⟩ := h
  ⟨G, hg.mono_leOn hs, hx.mono_leOn hc hs, hn, hN.mono_leOn hs⟩

/-- Each top state simulates each instrumented state of the invariant. -/
theorem InvVS.top {vs : VState} {X : AState} (h : InvVS cb vs X) (W : AState) :
    InvVS cb vs (top cb.cn.ctx W) :=
  let ⟨G, hg, hx, hn, hN⟩ := h
  ⟨G, hg.top W, hx.top W, hn, hN.top W⟩

/-! ## Queries -/

/-- A path from a live universe object in universe cells gives a live universe object. -/
theorem _root_.DirectedAlias.Sound.HavocRecency.InvG.readPath_live {ctx : Ctx} {α : Abs} {st : CState} {X : AState} (h : InvG ctx α st X) :
    ∀ {cx : List Cell} {o0 o : Obj}, (∀ c ∈ cx, c.abs ∈ ctx.cells) →
      ¬ Dead ctx.once o0 → α st.cnt o0 ∈ ctx.origins →
      readPath st.heap o0 cx = some o → ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins
  | [], o0, o, _, hd, hin, hr => by
    simp only [readPath, Option.some.injEq] at hr
    subst hr; exact ⟨hd, hin⟩
  | c :: cs, o0, o, hcs, hd, hin, hr => by
    simp only [readPath] at hr
    cases e : st.heap o0 c with
    | none => rw [e] at hr; cases hr
    | some o1 =>
      rw [e] at hr
      have hc : c.abs ∈ ctx.cells := hcs c List.mem_cons_self
      exact HavocRecency.InvG.readPath_live h (fun c' h' => hcs c' (List.mem_cons_of_mem _ h'))
        (h.heapLive o0 c o1 hd e) (h.heapIn o0 c o1 hd hin hc e) hr

/-- An access path from a universe variable in universe cells gives a live universe object. -/
theorem _root_.DirectedAlias.Sound.HavocRecency.InvG.evalPath_live {ctx : Ctx} {α : Abs} {st : CState} {X : AState} (h : InvG ctx α st X)
    {x : Var} {cx : List Cell} {o : Obj} (hcs : ∀ c ∈ cx, c.abs ∈ ctx.cells)
    (he : evalPath st x cx = some o) : ¬ Dead ctx.once o ∧ α st.cnt o ∈ ctx.origins := by
  unfold evalPath at he
  cases e : st.env x with
  | none => rw [e] at he; cases he
  | some o0 =>
    rw [e] at he
    exact h.readPath_live hcs (h.envOk x o0 e).1 (h.envOk x o0 e).2 he

/-- The abstract evaluation of a path that ends with `c`. -/
theorem aevalPath_snoc (X : AState) (x : Var) (q : List ACell) (c : ACell) :
    aevalPath X x (q ++ [c]) = aread X (aevalPath X x q) c := by
  unfold aevalPath
  generalize X.env x = S
  induction q generalizing S with
  | nil => rfl
  | cons d ds ih => exact ih _

/-- THE NULL INSTANCE CASE OF A QUERY: if an access path in universe cells gives a null instance,
its origin is in the abstract evaluation of the path. -/
theorem InvVS.evalV_nul {vs : VState} {X : AState} (h : InvVS cb vs X) {x : Var}
    {cx : List Cell} {t : NTag} (hcs : ∀ c ∈ cx, c.abs ∈ cb.cn.ctx.cells)
    (he : vs.evalV x cx = some (.nul t)) :
    alphaN cb.cn.ctx.K t ∈ aevalPath X x (cx.map Cell.abs) := by
  obtain ⟨G, hg, _, _, hN⟩ := h
  rcases ValueSem.evalV_nul he with ⟨rfl, h1, h2⟩ | ⟨q, c, o', rfl, h1, h2, h3⟩
  · have hx : x ∈ cb.cn.ctx.vars := by
      by_cases hx : x ∈ cb.cn.ctx.vars
      · exact hx
      · rw [hN.nout x hx] at h2; cases h2
    exact hN.nenv x hx h1 t h2
  · have hq : ∀ d ∈ q, d.abs ∈ cb.cn.ctx.cells :=
      fun d hd => hcs d (List.mem_append.mpr (Or.inl hd))
    have hc : c.abs ∈ cb.cn.ctx.cells := hcs c (List.mem_append.mpr (Or.inr List.mem_cons_self))
    obtain ⟨hd, hin⟩ := hg.evalPath_live hq h1
    rw [List.map_append, List.map_cons, List.map_nil, aevalPath_snoc]
    refine mem_aread.mpr ⟨_, hg.evalPath_sound hq h1, ?_⟩
    rw [← h3]
    exact hN.nheap o' c hd hin hc h2

/-- THE QUERY OF DESIGN VS: if two access paths in universe cells give the same value instance,
the abstract evaluations of the paths meet. -/
theorem InvVS.may_of_alias {vs : VState} {X : AState} (h : InvVS cb vs X) {x y : Var}
    {px py : List Cell} (hcx : ∀ c ∈ px, c.abs ∈ cb.cn.ctx.cells)
    (hcy : ∀ c ∈ py, c.abs ∈ cb.cn.ctx.cells) (ha : AliasInV vs x px y py) :
    may X x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  rcases aliasInV_cases ha with ⟨o, h1, h2⟩ | ⟨t, h1, h2⟩
  · obtain ⟨G, hg, _, _, _⟩ := h
    exact may_iff.mpr ⟨_, hg.evalPath_sound hcx h1, hg.evalPath_sound hcy h2⟩
  · exact may_iff.mpr ⟨_, h.evalV_nul hcx h1, h.evalV_nul hcy h2⟩

end DirectedAlias.Sound.ValueSem
