import DirectedAlias.Sound.BlockOnly.Ghost

/-!
# The invariant of design BO

`InvBO cb st X` holds if, for some ghost naming `G`:
* the generic invariant `InvG` (`Sound/HavocRecency/Inv.lean`) holds with the abstraction
  `alphaBO cb G`; all its update lemmas are reused;
* `InvXB`: junk and dead objects keep their default cells, a cell outside the universe holds
  an object with the cell name, each ghost has its frozen facts, and the abstraction of each
  callee object is NOT unique for the two sets of the abstract state (`BlockedAll`). This is
  the fact that makes the uniqueness rule of design BO sound;
* `CntOKB`: only calls that ran have ghosts, and the counters of a ghost are not above the
  current counters.
-/

namespace DirectedAlias.Sound.BlockOnly

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Opt

/-- A context of design BO is closed: the facts of design CN, the second reserved variable is
in the variable universe and is not the first one, and the static roots are universe
origins. -/
structure CtxBOK (cb : CtxB) : Prop where
  cn : CtxNOK cb.cn
  xvIn : cb.xv ∈ cb.cn.ctx.vars
  xvNe : cb.xv ≠ cb.cn.xe
  statics : ∀ r ∈ cb.cn.statics, Origin.sym (.root r) [] ∈ cb.cn.ctx.origins

/-- The frozen facts of a ghost: the holder origin is not junk, and the frozen state has
support. -/
structure GhostOK (cb : CtxB) (g : Ghost) : Prop where
  hold : isJunk g.hold = false
  supp : Supp cb.cn.ctx g.X

/-- Only the calls that ran have ghosts, and the counters of a ghost are not above the
current counters. -/
def CntOKB (G : GNames) (cnt : Site → Nat) : Prop :=
  (∀ s n k g, G s n k = some g → n < cnt s) ∧ GhostLe G cnt

/-- The abstraction of each callee object that is a universe origin is not unique for the
sets `E` (`Etree`) and `V` (`Eval`). -/
def BlockedAll (cb : CtxB) (G : GNames) (cnt : Site → Nat) (E V : List Origin) : Prop :=
  ∀ s n k p, alphaBO cb G cnt (.sym (.havoc s n k) p) ∈ cb.cn.ctx.origins →
    uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V
      (alphaBO cb G cnt (.sym (.havoc s n k) p)) = false

/-- The facts of design BO beyond the generic invariant. -/
structure InvXB (cb : CtxB) (G : GNames) (st : CState) (X : AState) : Prop where
  /-- A junk object (a callee object without ghost data) has its default cells. -/
  junkDflt : ∀ o c, isJunk (alphaBO cb G st.cnt o) = true → st.heap o c = cdefault o c
  /-- A dead object has its default cells. -/
  deadDflt : ∀ o c, Dead cb.cn.ctx.once o → st.heap o c = cdefault o c
  /-- A cell outside the universe holds an object with the cell name. -/
  outside : ∀ o c o', ¬ Dead cb.cn.ctx.once o → st.heap o c = some o' →
    (c.abs ∈ cb.cn.ctx.cells ∧ alphaBO cb G st.cnt o ∈ cb.cn.ctx.origins) ∨
    alphaBO cb G st.cnt o' = childCN cb.cn.ctx.K (alphaBO cb G st.cnt o) c.abs
  /-- Each ghost has its frozen facts. -/
  ghosts : ∀ s n k g, G s n k = some g → GhostOK cb g
  /-- No callee object has a unique origin. -/
  blocked : BlockedAll cb G st.cnt (X.env cb.cn.xe) (X.env cb.xv)

/-- The simulation invariant of design BO. -/
def InvBO (cb : CtxB) (st : CState) (X : AState) : Prop :=
  ∃ G, InvG cb.cn.ctx (alphaBO cb G) st X ∧ InvXB cb G st X ∧ CntOKB G st.cnt

variable {cb : CtxB}

/-! ## The uniqueness test -/

/-- The uniqueness test of design BO is false if and only if the recency test is false, a
proper prefix is in `E`, or the origin is in `V`. -/
theorem uniqueBO_false_iff {once : Site → Bool} {eu : Bool} {E V : List Origin} {u : Origin} :
    uniqueBO once eu E V u = false ↔ uniqueR once eu u = false ∨ expB E u = true ∨ u ∈ V := by
  unfold uniqueBO uniqueCN
  cases h1 : uniqueR once eu u <;> cases h2 : expB E u <;> by_cases h3 : u ∈ V <;> simp [h3]

/-- The uniqueness test is false for an origin of `V`. -/
theorem uniqueBO_false_of_mem {once : Site → Bool} {eu : Bool} {E V : List Origin} {u : Origin}
    (h : u ∈ V) : uniqueBO once eu E V u = false :=
  uniqueBO_false_iff.mpr (Or.inr (Or.inr h))

/-- A false uniqueness test stays false when the two sets grow. -/
theorem uniqueBO_false_mono {once : Site → Bool} {eu : Bool} {E V E' V' : List Origin}
    {u : Origin} (hE : ∀ a ∈ E, a ∈ E') (hV : ∀ a ∈ V, a ∈ V')
    (h : uniqueBO once eu E V u = false) : uniqueBO once eu E' V' u = false := by
  rcases uniqueBO_false_iff.mp h with h1 | h1 | h1
  · exact uniqueBO_false_iff.mpr (Or.inl h1)
  · exact uniqueBO_false_iff.mpr (Or.inr (Or.inl (expB_mono hE h1)))
  · exact uniqueBO_false_iff.mpr (Or.inr (Or.inr (hV _ h1)))

/-- The renaming of `retire` keeps a false uniqueness test, when it renames the sets too. -/
theorem uniqueBO_false_rename {once : Site → Bool} {eu : Bool} {E V : List Origin} {u : Origin}
    (s : Site) (h : uniqueBO once eu E V u = false) :
    uniqueBO once eu (renameL s E) (renameL s V) (renameO s u) = false := by
  rcases uniqueBO_false_iff.mp h with h1 | h1 | h1
  · refine uniqueBO_false_iff.mpr (Or.inl ?_)
    unfold renameO
    split
    · show ((2 * s + 1) % 2 == 0) = false
      have : @Eq Nat ((2 * s + 1) % 2) 1 := by omega
      rw [this]; rfl
    · exact h1
  · refine uniqueBO_false_iff.mpr (Or.inr (Or.inl ?_))
    cases u with
    | sym b q => rw [renameO_name s rfl]; exact expB_renameL s h1
    | _ => simp [expB] at h1
  · exact uniqueBO_false_iff.mpr (Or.inr (Or.inr (List.mem_map.mpr ⟨u, h1, rfl⟩)))

/-- The blocked facts are monotone in the two sets. -/
theorem BlockedAll.mono {G : GNames} {cnt : Site → Nat} {E V E' V' : List Origin}
    (h : BlockedAll cb G cnt E V) (hE : ∀ a ∈ E, a ∈ E') (hV : ∀ a ∈ V, a ∈ V') :
    BlockedAll cb G cnt E' V' :=
  fun s n k p hin => uniqueBO_false_mono hE hV (h s n k p hin)

/-! ## Updates of the extra facts -/

/-- The extra facts are monotone in the two sets. -/
theorem InvXB.mono {G : GNames} {st : CState} {X Y : AState} (h : InvXB cb G st X)
    (hE : ∀ a ∈ X.env cb.cn.xe, a ∈ Y.env cb.cn.xe) (hV : ∀ a ∈ X.env cb.xv, a ∈ Y.env cb.xv) :
    InvXB cb G st Y :=
  { h with blocked := h.blocked.mono hE hV }

/-- The extra facts are closed upward under inclusion on the universe. -/
theorem InvXB.mono_leOn (hc : CtxBOK cb) {G : GNames} {st : CState} {X Y : AState}
    (h : InvXB cb G st X) (hs : leOn cb.cn.ctx X Y = true) : InvXB cb G st Y :=
  h.mono ((leOn_iff.mp hs).1 _ hc.cn.xeIn) ((leOn_iff.mp hs).1 _ hc.xvIn)

/-- The extra facts hold for each top state: `Eval` then holds every universe origin. -/
theorem InvXB.top {G : GNames} {st : CState} {X : AState} (h : InvXB cb G st X) (W : AState) :
    InvXB cb G st (top cb.cn.ctx W) :=
  { h with blocked := fun _ _ _ _ hin => uniqueBO_false_of_mem (mem_uni.mpr (Or.inl hin)) }

/-- Setting a variable other than the reserved ones keeps the extra facts. -/
theorem InvXB.setVar {G : GNames} {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : InvXB cb G st X) (hx : x ≠ cb.cn.xe) (hv : x ≠ cb.xv) :
    InvXB cb G (st.setVar x v) (X.setVar x S) where
  junkDflt := h.junkDflt
  deadDflt := h.deadDflt
  outside := h.outside
  ghosts := h.ghosts
  blocked := by
    have e1 : (X.setVar x S).env cb.cn.xe = X.env cb.cn.xe := fupd_ne _ _ (Ne.symm hx)
    have e2 : (X.setVar x S).env cb.xv = X.env cb.xv := fupd_ne _ _ (Ne.symm hv)
    rw [e1, e2]; exact h.blocked

/-- Setting the optional result variable keeps the extra facts. -/
theorem InvXB.setRet {G : GNames} {st : CState} {X : AState} {ret : Option Var} {v : Val}
    {S : List Origin} (h : InvXB cb G st X) (hx : ∀ x, ret = some x → x ≠ cb.cn.xe ∧ x ≠ cb.xv) :
    InvXB cb G (st.setRet ret v) (X.setRet ret S) := by
  cases ret with
  | none => exact h
  | some x => exact h.setVar (hx x rfl).1 (hx x rfl).2

/-- A concrete store into a universe cell of a live universe object keeps the extra facts, if
the two sets do not change. -/
theorem InvXB.write (hc : CtxBOK cb) {G : GNames} {st : CState} {X Y : AState} {o : Obj}
    {c : Cell} {v : Val} (h : InvXB cb G st X)
    (ho : ¬ Dead cb.cn.ctx.once o ∧ alphaBO cb G st.cnt o ∈ cb.cn.ctx.origins)
    (hcell : c.abs ∈ cb.cn.ctx.cells) (hE : Y.env cb.cn.xe = X.env cb.cn.xe)
    (hV : Y.env cb.xv = X.env cb.xv) :
    InvXB cb G (st.setCell o c v) Y where
  junkDflt o1 c1 hj := by
    show fupd2 st.heap o c v o1 c1 = _
    change isJunk (alphaBO cb G st.cnt o1) = true at hj
    have hne : ¬ (o1 = o ∧ c1 = c) := by
      rintro ⟨rfl, rfl⟩
      rw [notJunk_of_mem hc.cn ho.2] at hj
      cases hj
    rw [fupd2_ne _ _ hne]
    exact h.junkDflt o1 c1 hj
  deadDflt o1 c1 hd := by
    show fupd2 st.heap o c v o1 c1 = _
    have hne : ¬ (o1 = o ∧ c1 = c) := by rintro ⟨rfl, rfl⟩; exact ho.1 hd
    rw [fupd2_ne _ _ hne]
    exact h.deadDflt o1 c1 hd
  outside o1 c1 o2 hd hh := by
    change fupd2 st.heap o c v o1 c1 = some o2 at hh
    by_cases e : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := e; exact Or.inl ⟨hcell, ho.2⟩
    · rw [fupd2_ne _ _ e] at hh; exact h.outside o1 c1 o2 hd hh
  ghosts := h.ghosts
  blocked := by rw [hE, hV]; exact h.blocked

/-- A counter bump with `retire` keeps the extra facts. -/
theorem InvXB.retire (hc : CtxBOK cb) {G : GNames} {st : CState} {X : AState} (s : Site)
    (hle : GhostLe G st.cnt) (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (h : InvXB cb G st X) :
    InvXB cb G (st.bump s) (retire s X) := by
  have hb := fun {o : Obj} (ho : o ≠ .alloc s (st.cnt s)) => alphaBO_bump (cb := cb) st hle s ho
  have hnext : ∀ c, st.heap (.alloc s (st.cnt s)) c = none :=
    fun c => hg.fresh s _ c (Nat.le_refl _)
  have hhv : ∀ a n k p, Obj.sym (.havoc a n k) p ≠ .alloc s (st.cnt s) := fun _ _ _ _ e => by
    cases e
  exact {
    junkDflt := fun o c hj => by
      show st.heap o c = cdefault o c
      by_cases e : o = .alloc s (st.cnt s)
      · subst e; rw [alphaBO_new] at hj; cases hj
      · rw [hb e, isJunk_renameO] at hj; exact h.junkDflt o c hj
    deadDflt := fun o c hd => h.deadDflt o c hd
    outside := fun o c o' hd hh => by
      change st.heap o c = some o' at hh
      have ho : o ≠ .alloc s (st.cnt s) := by
        intro e; subst e; rw [hnext] at hh; cases hh
      have ho' : o' ≠ .alloc s (st.cnt s) := by
        intro e; subst e; have := hg.heapCr o c s _ hh; omega
      rw [hb ho, hb ho']
      rcases h.outside o c o' hd hh with ⟨h1, h2⟩ | e
      · exact Or.inl ⟨h1, renameO_mem hc.cn.base s h2⟩
      · right; rw [e, renameO_childCN, childCN_renameO]
    ghosts := h.ghosts
    blocked := fun a n k p hin => by
      rw [hb (hhv a n k p)] at hin ⊢
      exact uniqueBO_false_rename s (h.blocked a n k p (mem_of_renameO hc.cn.base s hin)) }

/-- A counter bump keeps the counter facts of the ghosts. -/
theorem CntOKB.bump {G : GNames} {st : CState} (h : CntOKB G st.cnt) (a : Site) :
    CntOKB G (st.bump a).cnt := by
  have hle : ∀ t, st.cnt t ≤ (st.bump a).cnt t := by
    intro t
    show st.cnt t ≤ fupd st.cnt a (st.cnt a + 1) t
    by_cases e : t = a
    · subst e; rw [fupd_same]; exact Nat.le_succ _
    · rw [fupd_ne _ _ e]; exact Nat.le_refl _
  exact ⟨fun s n k g e => Nat.lt_of_lt_of_le (h.1 s n k g e) (hle s),
    fun s n k g e t => Nat.le_trans (h.2 s n k g e t) (hle t)⟩

/-! ## Uniqueness -/

/-- An object with a unique universe origin of design BO is not a callee object. -/
theorem not_havoc_of_uniqueBO {G : GNames} {cnt : Site → Nat}
    {E V : List Origin} (hb : BlockedAll cb G cnt E V) {o : Obj}
    (hin : alphaBO cb G cnt o ∈ cb.cn.ctx.origins)
    (hu : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V (alphaBO cb G cnt o) = true) :
    ∀ s n k p, o ≠ .sym (.havoc s n k) p := by
  intro s n k p e
  subst e
  rw [hb s n k p hin] at hu
  cases hu

/-- UNIQUENESS OF DESIGN BO: a unique universe origin denotes at most one object that is not
dead. No callee object has a unique origin (`BlockedAll`). -/
theorem unique_objBO {G : GNames} {cnt : Site → Nat} {E V : List Origin}
    (hb : BlockedAll cb G cnt E V) {o o' : Obj}
    (hin : alphaBO cb G cnt o ∈ cb.cn.ctx.origins)
    (hu : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V (alphaBO cb G cnt o) = true)
    (hd : ¬ Dead cb.cn.ctx.once o) (hd' : ¬ Dead cb.cn.ctx.once o')
    (ha : alphaBO cb G cnt o' = alphaBO cb G cnt o) : o' = o := by
  let st : CState := ⟨fun _ => none, fun _ _ => none, cnt⟩
  have h1 := not_havoc_of_uniqueBO hb hin hu
  have h2 := not_havoc_of_uniqueBO hb (ha ▸ hin) (ha ▸ hu)
  have e1 := alphaBO_eq_alphaR (cb := cb) G st h1
  have e2 := alphaBO_eq_alphaR (cb := cb) G st h2
  have hu2 : uniqueR cb.cn.ctx.once cb.cn.ctx.entryUnique (alphaR cb.cn.ctx.K st o) = true := by
    simp only [uniqueBO, uniqueCN, Bool.and_eq_true] at hu
    rw [← e1]; exact hu.1.1
  exact unique_objR hu2 hd hd' (by rw [← e1, ← e2]; exact ha)

end DirectedAlias.Sound.BlockOnly
