import DirectedAlias.Sound.CellNamed.Names

/-!
# The invariant of design CN

The invariant `InvCN` has three parts, for some ghost naming `N`:
* the generic invariant `InvG` (`Sound/HavocRecency/Inv.lean`) with the abstraction
  `alphaCN K N`. All its update lemmas are reused;
* `InvX`: facts about the cells outside the universe, the junk objects, the dead objects, and
  the ghost names. Each ghost name is a cell name, and a symbolic name is below an exposed
  origin (`ExpOK`). This is what makes the exposed rule of `uniqueCN` sound;
* `CntOK`: only calls that ran have names.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

/-- A context of design CN is closed: the recency facts, no junk origin in the universe, the
universe is closed under cell names and under prefixes, and the reserved variable is in the
variable universe. -/
structure CtxNOK (cn : CtxN) : Prop where
  base : CtxROK cn.ctx
  noJunk : ∀ s, Origin.havoc s ∉ cn.ctx.origins
  childIn : ∀ a ∈ cn.ctx.origins, ∀ c ∈ cn.ctx.cells, childCN cn.ctx.K a c ∈ cn.ctx.origins
  pre : ∀ b q c, Origin.sym b (q ++ [c]) ∈ cn.ctx.origins → Origin.sym b q ∈ cn.ctx.origins
  rootIn : ∀ b q, Origin.sym b q ∈ cn.ctx.origins → Origin.sym b [] ∈ cn.ctx.origins
  xeIn : cn.xe ∈ cn.ctx.vars

/-- A symbolic universe origin is below an origin of the exposed set `E`. -/
def ExpOK (ctx : Ctx) (E : List Origin) (a : Origin) : Prop :=
  a ∈ ctx.origins → ∀ b q, a = .sym b q → expB E (.sym b q) = true

/-- The facts about a ghost name: it is a cell name, it is not a root origin, and if it is a
symbolic universe origin, it is below an exposed origin. -/
structure NameOK (cn : CtxN) (E : List Origin) (a : Origin) : Prop where
  name : isName a = true
  ne : ∀ b, a ≠ .sym b []
  exp : ExpOK cn.ctx E a

/-- The facts of design CN beyond the generic invariant. -/
structure InvX (cn : CtxN) (N : Names) (st : CState) (X : AState) : Prop where
  /-- A junk object (a callee object that no call wrote) has its default cells. -/
  junkDflt : ∀ o c, isJunk (alphaCN cn.ctx.K N st.cnt o) = true → st.heap o c = cdefault o c
  /-- A dead object has its default cells. -/
  deadDflt : ∀ o c, Dead cn.ctx.once o → st.heap o c = cdefault o c
  /-- A cell outside the universe holds an object with the cell name. -/
  outside : ∀ o c o', ¬ Dead cn.ctx.once o → st.heap o c = some o' →
    (c.abs ∈ cn.ctx.cells ∧ alphaCN cn.ctx.K N st.cnt o ∈ cn.ctx.origins) ∨
    alphaCN cn.ctx.K N st.cnt o' = childCN cn.ctx.K (alphaCN cn.ctx.K N st.cnt o) c.abs
  /-- Each ghost name has the name facts for the exposed set of the abstract state. -/
  names : ∀ s n k a, N s n k = some a → NameOK cn (X.env cn.xe) a

/-- Only the calls that ran have ghost names. -/
def CntOK (N : Names) (cnt : Site → Nat) : Prop :=
  ∀ s n k a, N s n k = some a → n < cnt s

/-- The simulation invariant of design CN. -/
def InvCN (cn : CtxN) (st : CState) (X : AState) : Prop :=
  ∃ N, InvG cn.ctx (alphaCN cn.ctx.K N) st X ∧ InvX cn N st X ∧ CntOK N st.cnt

variable {cn : CtxN}

/-! ## Name facts -/

/-- The exposed facts are monotone in the exposed set. -/
theorem ExpOK.mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') {a : Origin}
    (h : ExpOK cn.ctx E a) : ExpOK cn.ctx E' a :=
  fun ha b q e => expB_mono hs (h ha b q e)

/-- The name facts are monotone in the exposed set. -/
theorem NameOK.mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') {a : Origin}
    (h : NameOK cn E a) : NameOK cn E' a :=
  ⟨h.name, h.ne, h.exp.mono hs⟩

/-- The cell name of a ghost name has the name facts. -/
theorem NameOK.child (hc : CtxNOK cn) {E : List Origin} {a : Origin} (h : NameOK cn E a)
    (c : ACell) : NameOK cn E (childCN cn.ctx.K a c) := by
  refine ⟨childCN_name _ c (isName_notJunk h.name), childCN_ne_root _ a c, ?_⟩
  intro hin b q e
  obtain ⟨q0, rfl, rfl⟩ := childCN_sym_inv e
  rw [e] at hin
  exact expB_child c (h.exp (hc.pre b q0 c hin) b q0 rfl)

/-- The names below a ghost name have the name facts. -/
theorem NameOK.extend (hc : CtxNOK cn) {E : List Origin} :
    ∀ {a : Origin} (q : List ACell), NameOK cn E a → NameOK cn E (extendCN cn.ctx.K a q)
  | _, [], h => h
  | _, d :: ds, h => NameOK.extend hc ds (h.child hc d)

/-- If the exposed set contains the universe, each origin that is not a root origin has the
exposed facts. -/
theorem ExpOK_univ (hc : CtxNOK cn) {E : List Origin} (hE : ∀ a ∈ cn.ctx.origins, a ∈ E)
    {a : Origin} (hne : ∀ b, a ≠ .sym b []) : ExpOK cn.ctx E a := by
  intro hin b q e
  subst e
  cases q with
  | nil => exact absurd rfl (hne b)
  | cons d ds =>
    refine expB_of (p := []) (hE _ (hc.rootIn b _ hin)) ?_ (by simp [preB])
    simp

/-! ## The abstraction under a counter bump -/

/-- A counter bump of site `s` renames the abstraction of each object except the next object
of `s`, if each ghost name is a cell name. -/
theorem alphaCN_bump (K : Nat) {N : Names} (hN : ∀ s n k a, N s n k = some a → isName a = true)
    (st : CState) (s : Site) {o : Obj} (h : o ≠ .alloc s (st.cnt s)) :
    alphaCN K N (st.bump s).cnt o = renameO s (alphaCN K N st.cnt o) := by
  cases o with
  | alloc a n => exact alphaR_bump K st s h
  | sym b p =>
    cases b with
    | root r => exact alphaR_bump K st s h
    | fresh a n => exact alphaR_bump K st s h
    | havoc a n k =>
      cases e : N a n k with
      | none =>
        rw [alphaCN_havoc_none K _ e, alphaCN_havoc_none K _ e, renameO_havoc]
      | some x =>
        rw [alphaCN_havoc_some K _ e, alphaCN_havoc_some K _ e,
          renameO_name s (extendCN_name K _ (hN a n k x e))]

/-- A cell name is never the most recent origin of a site. -/
theorem childCN_ne_alloc (K : Nat) (a : Origin) (c : ACell) (x : Nat) :
    childCN K a c ≠ .alloc x := by
  cases a with
  | sym b q => show symOrDeep K b (q ++ [c]) ≠ _; unfold symOrDeep; split <;> intro e <;> cases e
  | deep b => intro e; cases e
  | alloc y => intro e; cases e
  | havoc s => intro e; cases e
  | hsym s k c' q => show (if _ then _ else _) ≠ _; split <;> intro e <;> cases e
  | hdeep s k c' => intro e; cases e

/-- The renaming of `retire` does not change a cell name of any origin. -/
theorem renameO_childCN (K : Nat) (s : Site) (a : Origin) (c : ACell) :
    renameO s (childCN K a c) = childCN K a c := by
  unfold renameO
  split
  · rename_i e; exact absurd e (childCN_ne_alloc K a c _)
  · rfl

/-! ## Updates of the extra facts -/

/-- The extra facts are monotone in the exposed set. -/
theorem InvX.mono {N : Names} {st : CState} {X Y : AState} (h : InvX cn N st X)
    (hE : ∀ a ∈ X.env cn.xe, a ∈ Y.env cn.xe) : InvX cn N st Y :=
  { h with names := fun s n k a e => (h.names s n k a e).mono hE }

/-- The extra facts are closed upward under inclusion on the universe. -/
theorem InvX.mono_leOn (hc : CtxNOK cn) {N : Names} {st : CState} {X Y : AState}
    (h : InvX cn N st X) (hs : leOn cn.ctx X Y = true) : InvX cn N st Y :=
  h.mono ((leOn_iff.mp hs).1 _ hc.xeIn)

/-- The extra facts hold for each top state. -/
theorem InvX.top (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState} (h : InvX cn N st X)
    (W : AState) : InvX cn N st (top cn.ctx W) :=
  { h with names := fun s n k a e =>
      ⟨(h.names s n k a e).name, (h.names s n k a e).ne,
        ExpOK_univ hc (fun _ hm => mem_uni.mpr (Or.inl hm)) (h.names s n k a e).ne⟩ }

/-- Setting a variable other than the reserved one keeps the extra facts. -/
theorem InvX.setVar {N : Names} {st : CState} {X : AState} {x : Var} {v : Val}
    {S : List Origin} (h : InvX cn N st X) (hx : x ≠ cn.xe) :
    InvX cn N (st.setVar x v) (X.setVar x S) where
  junkDflt := h.junkDflt
  deadDflt := h.deadDflt
  outside := h.outside
  names s n k a e := by
    have := h.names s n k a e
    show NameOK cn (fupd X.env x S cn.xe) a
    rw [fupd_ne _ _ (Ne.symm hx)]
    exact this

/-- Setting the optional result variable keeps the extra facts. -/
theorem InvX.setRet {N : Names} {st : CState} {X : AState} {ret : Option Var} {v : Val}
    {S : List Origin} (h : InvX cn N st X) (hx : ∀ x, ret = some x → x ≠ cn.xe) :
    InvX cn N (st.setRet ret v) (X.setRet ret S) := by
  cases ret with
  | none => exact h
  | some x => exact h.setVar (hx x rfl)

/-- A universe origin is not junk. -/
theorem notJunk_of_mem (hc : CtxNOK cn) {a : Origin} (h : a ∈ cn.ctx.origins) :
    isJunk a = false := by
  cases a with
  | havoc s => exact absurd h (hc.noJunk s)
  | _ => rfl

/-- A concrete store into a universe cell of a live universe object keeps the extra facts. -/
theorem InvX.write (hc : CtxNOK cn) {N : Names} {st : CState} {X Y : AState} {o : Obj}
    {c : Cell} {v : Val} (h : InvX cn N st X)
    (ho : ¬ Dead cn.ctx.once o ∧ alphaCN cn.ctx.K N st.cnt o ∈ cn.ctx.origins)
    (hcell : c.abs ∈ cn.ctx.cells) (hE : Y.env cn.xe = X.env cn.xe) :
    InvX cn N (st.setCell o c v) Y where
  junkDflt o1 c1 hj := by
    show fupd2 st.heap o c v o1 c1 = _
    change isJunk (alphaCN cn.ctx.K N st.cnt o1) = true at hj
    have hne : ¬ (o1 = o ∧ c1 = c) := by
      rintro ⟨rfl, rfl⟩
      rw [notJunk_of_mem hc ho.2] at hj
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
  names s n k a e := by rw [hE]; exact h.names s n k a e

/-- A counter bump with `retire` keeps the extra facts. -/
theorem InvX.retire (hc : CtxNOK cn) {N : Names} {st : CState} {X : AState} (s : Site)
    (hg : InvG cn.ctx (alphaCN cn.ctx.K N) st X) (h : InvX cn N st X) :
    InvX cn N (st.bump s) (retire s X) := by
  have hN : ∀ s n k a, N s n k = some a → isName a = true :=
    fun s n k a e => (h.names s n k a e).name
  have hb := fun {o : Obj} (ho : o ≠ .alloc s (st.cnt s)) => alphaCN_bump cn.ctx.K hN st s ho
  have hnext : ∀ c, st.heap (.alloc s (st.cnt s)) c = none :=
    fun c => hg.fresh s _ c (Nat.le_refl _)
  exact {
    junkDflt := fun o c hj => by
      show st.heap o c = cdefault o c
      by_cases e : o = .alloc s (st.cnt s)
      · subst e; rw [alphaCN_new] at hj; cases hj
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
      · exact Or.inl ⟨h1, renameO_mem hc.base s h2⟩
      · right; rw [e, renameO_childCN, childCN_renameO]
    names := fun s' n k a e => ⟨(h.names s' n k a e).name, (h.names s' n k a e).ne,
      fun hin b q eq => expB_renameL s ((h.names s' n k a e).exp hin b q eq)⟩ }

/-! ## Uniqueness -/

/-- The abstraction of a callee object is never a unique universe origin of design CN. -/
theorem not_havoc_of_unique (hc : CtxNOK cn) {N : Names} {E : List Origin}
    (hN : ∀ s n k a, N s n k = some a → NameOK cn E a) {cnt : Site → Nat} {o : Obj}
    (hin : alphaCN cn.ctx.K N cnt o ∈ cn.ctx.origins)
    (hu : uniqueCN cn.ctx.once cn.ctx.entryUnique E (alphaCN cn.ctx.K N cnt o) = true) :
    ∀ s n k p, o ≠ .sym (.havoc s n k) p := by
  intro s n k p e
  subst e
  cases eN : N s n k with
  | none =>
    rw [alphaCN_havoc_none _ _ eN] at hin
    exact hc.noJunk s hin
  | some a =>
    rw [alphaCN_havoc_some _ _ eN] at hin hu
    have hn := (hN s n k a eN).extend hc (p.map Cell.abs)
    simp only [uniqueCN, Bool.and_eq_true, Bool.not_eq_true'] at hu
    obtain ⟨b, q, eq⟩ := uniqueR_name hn.name hu.1
    rw [eq] at hu hin
    rw [hn.exp (eq ▸ hin) b q eq] at hu
    cases hu.2

/-- UNIQUENESS OF DESIGN CN: a unique universe origin denotes at most one object that is not
dead. A callee object never has a unique origin: its name is junk, not symbolic, or below an
exposed origin. -/
theorem unique_objCN (hc : CtxNOK cn) {N : Names} {E : List Origin}
    (hN : ∀ s n k a, N s n k = some a → NameOK cn E a) {cnt : Site → Nat} {o o' : Obj}
    (hin : alphaCN cn.ctx.K N cnt o ∈ cn.ctx.origins)
    (hu : uniqueCN cn.ctx.once cn.ctx.entryUnique E (alphaCN cn.ctx.K N cnt o) = true)
    (hd : ¬ Dead cn.ctx.once o) (hd' : ¬ Dead cn.ctx.once o')
    (ha : alphaCN cn.ctx.K N cnt o' = alphaCN cn.ctx.K N cnt o) : o' = o := by
  let st : CState := ⟨fun _ => none, fun _ _ => none, cnt⟩
  have h1 := not_havoc_of_unique hc hN hin hu
  have h2 := not_havoc_of_unique hc hN (ha ▸ hin) (ha ▸ hu)
  have e1 := alphaCN_eq_alphaR cn.ctx.K N st h1
  have e2 := alphaCN_eq_alphaR cn.ctx.K N st h2
  have hu2 : uniqueR cn.ctx.once cn.ctx.entryUnique (alphaR cn.ctx.K st o) = true := by
    simp only [uniqueCN, Bool.and_eq_true] at hu
    rw [← e1]; exact hu.1
  exact unique_objR hu2 hd hd' (by rw [← e1, ← e2]; exact ha)

end DirectedAlias.Sound.CellNamed
