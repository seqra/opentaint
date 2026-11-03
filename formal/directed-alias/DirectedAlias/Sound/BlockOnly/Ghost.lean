import DirectedAlias.Sound.BlockOnly.Concept
import DirectedAlias.Opt.CellNamed

/-!
# The ghost naming of design BO

A call of design BO adds no origin. The proof names each object that the callee writes by an
origin that the abstract state already has: the object in the cell `(O, c)` gets an origin of
the abstract content of that cell AFTER the call (the old content, or the cell name if the
content was empty). An object at path `p` below it gets an origin of the content of the cell
of its parent name, one cell at a time (`stepB`, `chainB`). The proof keeps the abstract state
after the call (`Ghost.X`), so the naming is a function.

A name can be `rNew t`. When site `t` runs again, the object of `rNew t` becomes old, and so
does the callee object with that name. The ghost keeps the counters at the call, and `renB`
renames `rNew t` to `rOld t` when the counter of `t` has changed.

The analysis does not use the ghost; only the soundness proof does.
-/

namespace DirectedAlias.Sound.BlockOnly

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Opt

/-- The frozen data of a callee head object: the abstract state after the call, the origin of
the holder object at the call, the abstract cell, and the counters at the call. -/
structure Ghost where
  X : AState
  hold : Origin
  cell : ACell
  cnt0 : Site → Nat

/-- A ghost naming: the frozen data of the head object that the `n`-th execution of call site
`s` wrote with tag `k`, if a call wrote it. -/
abbrev GNames := Site → Nat → Nat → Option Ghost

variable (cb : CtxB)

/-- The name of the object in cell `c` of an object with name `a`, in the frozen state `X`:
the first origin of the content of a universe cell, else the cell name. -/
def stepB (X : AState) (a : Origin) (c : ACell) : Origin :=
  if a ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells then
    match X.heap a c with
    | v :: _ => v
    | [] => childCN cb.cn.ctx.K a c
  else childCN cb.cn.ctx.K a c

/-- The name at a path below a name, one cell at a time. -/
def chainB (X : AState) : Origin → List ACell → Origin
  | a, [] => a
  | a, c :: cs => chainB X (stepB cb X a c) cs

/-- Rename `rNew t` to `rOld t` if the counter of `t` changed since the call. -/
def renB (cnt cnt0 : Site → Nat) : Origin → Origin
  | .alloc x => if x % 2 = 0 ∧ cnt (x / 2) ≠ cnt0 (x / 2) then .alloc (x + 1) else .alloc x
  | a => a

/-- The abstraction of design BO. Entry, fresh and allocation objects have their recency
origin. A callee object with ghost data has the chain name of its path, renamed by `renB`. A
callee object without ghost data has the junk origin. -/
def alphaBO (G : GNames) (cnt : Site → Nat) : Obj → Origin
  | .sym (.root r) p => alpha cb.cn.ctx.K (.sym (.root r) p)
  | .sym (.fresh s n) p => alpha cb.cn.ctx.K (.sym (.fresh s n) p)
  | .sym (.havoc s n k) p => match G s n k with
    | some g => renB cnt g.cnt0 (chainB cb g.X g.hold (g.cell :: p.map Cell.abs))
    | none => .havoc s
  | .alloc s n => if n + 1 = cnt s then rNew s else rOld s

variable {cb}

/-! ## Unfolding -/

/-- The abstraction of a callee object with ghost data. -/
theorem alphaBO_some {G : GNames} (cnt : Site → Nat) {s n k : Nat} {g : Ghost}
    (h : G s n k = some g) (p : List Cell) :
    alphaBO cb G cnt (.sym (.havoc s n k) p) =
      renB cnt g.cnt0 (chainB cb g.X g.hold (g.cell :: p.map Cell.abs)) := by
  show (match G s n k with
    | some g => renB cnt g.cnt0 (chainB cb g.X g.hold (g.cell :: p.map Cell.abs))
    | none => .havoc s) = _
  rw [h]

/-- The abstraction of a callee object without ghost data is junk. -/
theorem alphaBO_none {G : GNames} (cnt : Site → Nat) {s n k : Nat} (h : G s n k = none)
    (p : List Cell) : alphaBO cb G cnt (.sym (.havoc s n k) p) = .havoc s := by
  show (match G s n k with
    | some g => renB cnt g.cnt0 (chainB cb g.X g.hold (g.cell :: p.map Cell.abs))
    | none => .havoc s) = _
  rw [h]

/-- The abstraction of an object that is not a callee object is its recency abstraction. -/
theorem alphaBO_eq_alphaR (G : GNames) (st : CState) {o : Obj}
    (h : ∀ s n k p, o ≠ .sym (.havoc s n k) p) : alphaBO cb G st.cnt o = alphaR cb.cn.ctx.K st o := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh s n => rfl
    | havoc s n k => exact absurd rfl (h s n k p)

/-- The abstraction of the entry object of a root is its root origin. -/
theorem alphaBO_root (G : GNames) (cnt : Site → Nat) (r : Root) :
    alphaBO cb G cnt (.sym (.root r) []) = .sym (.root r) [] := by
  show symOrDeep cb.cn.ctx.K (.root r) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le _)

/-- The abstraction of a fresh head object is its fresh origin. -/
theorem alphaBO_fresh (G : GNames) (cnt : Site → Nat) (s n : Nat) :
    alphaBO cb G cnt (.sym (.fresh s n) []) = .sym (.fresh s) [] := by
  show symOrDeep cb.cn.ctx.K (.fresh s) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le _)

/-- The next object of site `a` has the origin `rNew a` after the bump. -/
theorem alphaBO_new (G : GNames) (st : CState) (a : Site) :
    alphaBO cb G (st.bump a).cnt (.alloc a (st.cnt a)) = rNew a := by
  show (if st.cnt a + 1 = fupd st.cnt a (st.cnt a + 1) a then rNew a else rOld a) = rNew a
  rw [fupd_same, ite_eq_left rfl]

/-- The chain name of a path that ends with `c` is one step from the chain name of the
shorter path. -/
theorem chainB_append (X : AState) : ∀ (a : Origin) (q : List ACell) (c : ACell),
    chainB cb X a (q ++ [c]) = stepB cb X (chainB cb X a q) c
  | _, [], _ => rfl
  | a, d :: ds, c => chainB_append X (stepB cb X a d) ds c

/-! ## The renaming -/

/-- With the counters of the call, `renB` changes nothing. -/
theorem renB_same (cnt : Site → Nat) (a : Origin) : renB cnt cnt a = a := by
  cases a with
  | alloc x =>
    show (if x % 2 = 0 ∧ cnt (x / 2) ≠ cnt (x / 2) then Origin.alloc (x + 1) else .alloc x) = _
    exact ite_eq_right (fun h => h.2 rfl)
  | _ => rfl

/-- `renB` changes only allocation origins. -/
theorem renB_of_ne_alloc (cnt cnt0 : Site → Nat) {a : Origin} (h : ∀ x, a ≠ .alloc x) :
    renB cnt cnt0 a = a := by
  cases a with
  | alloc x => exact absurd rfl (h x)
  | _ => rfl

/-- A counter bump of site `s` renames a ghost name as `retire s` renames an origin, if the
counters of the call are not above the current counters. -/
theorem renB_bump {cnt cnt0 : Site → Nat} (hle : ∀ t, cnt0 t ≤ cnt t) (s : Site) (a : Origin) :
    renB (fupd cnt s (cnt s + 1)) cnt0 a = renameO s (renB cnt cnt0 a) := by
  cases a with
  | alloc x =>
    show (if x % 2 = 0 ∧ fupd cnt s (cnt s + 1) (x / 2) ≠ cnt0 (x / 2) then
        Origin.alloc (x + 1) else .alloc x) =
      renameO s (if x % 2 = 0 ∧ cnt (x / 2) ≠ cnt0 (x / 2) then .alloc (x + 1) else .alloc x)
    have hrn : ∀ y, renameO s (.alloc y) = if y = 2 * s then .alloc (2 * s + 1) else .alloc y := by
      intro y
      unfold renameO rNew rOld
      by_cases e : y = 2 * s
      · rw [e, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right (fun h => e (Origin.alloc.inj h)), ite_eq_right e]
    by_cases hx : x % 2 = 0
    · have hxN : @Eq Nat (x % 2) 0 := hx
      by_cases ht : x / 2 = s
      · have htN : @Eq Nat (x / 2) s := ht
        rw [ht]
        have hx2 : @Eq Nat x (2 * s) := by omega
        have h1 : fupd cnt s (cnt s + 1) s ≠ cnt0 s := by
          rw [fupd_same]; have := hle s; omega
        rw [ite_eq_left ⟨hx, h1⟩]
        by_cases h2 : cnt s ≠ cnt0 s
        · rw [ite_eq_left ⟨hx, h2⟩, hrn, ite_eq_right (show ¬ @Eq Nat (x + 1) (2 * s) by omega)]
        · rw [ite_eq_right (fun h => h2 h.2), hrn, ite_eq_left hx2, hx2]
      · have htN : ¬ @Eq Nat (x / 2) s := ht
        have h1 : fupd cnt s (cnt s + 1) (x / 2) = cnt (x / 2) := fupd_ne _ _ ht
        rw [h1]
        by_cases h2 : cnt (x / 2) ≠ cnt0 (x / 2)
        · rw [ite_eq_left ⟨hx, h2⟩, hrn,
            ite_eq_right (show ¬ @Eq Nat (x + 1) (2 * s) by omega)]
        · rw [ite_eq_right (fun h => h2 h.2), hrn,
            ite_eq_right (show ¬ @Eq Nat x (2 * s) by omega)]
    · have hxN : ¬ @Eq Nat (x % 2) 0 := hx
      rw [ite_eq_right (fun h => hx h.1), ite_eq_right (fun h => hx h.1), hrn,
        ite_eq_right (show ¬ @Eq Nat x (2 * s) by omega)]
  | sym b q => exact (renameO_name s rfl).symm
  | deep b => exact (renameO_name s rfl).symm
  | havoc t => exact (renameO_havoc s t).symm
  | hsym t k c q => exact (renameO_name s rfl).symm
  | hdeep t k c => exact (renameO_name s rfl).symm

/-- `renB` keeps the junk test. -/
theorem isJunk_renB (cnt cnt0 : Site → Nat) (a : Origin) : isJunk (renB cnt cnt0 a) = isJunk a := by
  cases a with
  | alloc x =>
    show isJunk (if _ then _ else _) = false
    split <;> rfl
  | _ => rfl

/-- The renaming of `retire` keeps a cell name. -/
theorem renameO_childCN' (K : Nat) (s : Site) (a : Origin) (c : ACell) :
    renameO s (childCN K a c) = childCN K a c :=
  renameO_childCN K s a c

/-! ## Steps and chains -/

/-- A step in a universe cell with content is the first origin of the content. -/
theorem stepB_head {X : AState} {a : Origin} {c : ACell} (ha : a ∈ cb.cn.ctx.origins)
    (hc : c ∈ cb.cn.ctx.cells) {v : Origin} {vs : List Origin} (h : X.heap a c = v :: vs) :
    stepB cb X a c = v := by
  unfold stepB
  rw [ite_eq_left ⟨ha, hc⟩, h]

/-- A step in a universe cell with content is in the content. -/
theorem stepB_mem {X : AState} {a : Origin} {c : ACell} (ha : a ∈ cb.cn.ctx.origins)
    (hc : c ∈ cb.cn.ctx.cells) (hne : X.heap a c ≠ []) : stepB cb X a c ∈ X.heap a c := by
  cases h : X.heap a c with
  | nil => exact absurd h hne
  | cons v vs => rw [stepB_head ha hc h]; exact List.mem_cons_self

/-- A step outside the universe is the cell name. -/
theorem stepB_out {X : AState} {a : Origin} {c : ACell}
    (h : ¬ (a ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells)) :
    stepB cb X a c = childCN cb.cn.ctx.K a c := by
  unfold stepB
  rw [ite_eq_right h]

/-- A step is the first origin of the content of a universe cell, or the cell name. -/
theorem stepB_cases (X : AState) (a : Origin) (c : ACell) :
    (a ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells ∧ X.heap a c ≠ [] ∧
      stepB cb X a c ∈ X.heap a c) ∨ stepB cb X a c = childCN cb.cn.ctx.K a c := by
  by_cases h : a ∈ cb.cn.ctx.origins ∧ c ∈ cb.cn.ctx.cells
  · cases e : X.heap a c with
    | nil =>
      right
      unfold stepB
      rw [ite_eq_left h, e]
    | cons v vs =>
      left
      refine ⟨h.1, h.2, by simp, ?_⟩
      rw [stepB_head h.1 h.2 e]; exact List.mem_cons_self
  · exact Or.inr (stepB_out h)

/-- A universe origin is not junk. -/
theorem notJunk_of_memB (hc : CtxNOK cb.cn) {a : Origin} (h : a ∈ cb.cn.ctx.origins) :
    isJunk a = false := notJunk_of_mem hc h

/-- A step from an origin that is not junk is not junk, if the frozen state has support. -/
theorem stepB_notJunk (hc : CtxNOK cb.cn) {X : AState} (hs : Supp cb.cn.ctx X) {a : Origin}
    (c : ACell) (h : isJunk a = false) : isJunk (stepB cb X a c) = false := by
  rcases stepB_cases (cb := cb) X a c with ⟨ha, hcc, _, hm⟩ | e
  · exact notJunk_of_memB hc (hs (.h a c) ⟨ha, hcc⟩ hm)
  · rw [e, isJunk_childCN]; exact h

/-- A chain from an origin that is not junk is not junk. -/
theorem chainB_notJunk (hc : CtxNOK cb.cn) {X : AState} (hs : Supp cb.cn.ctx X) :
    ∀ {a : Origin} (q : List ACell), isJunk a = false → isJunk (chainB cb X a q) = false
  | _, [], h => h
  | _, d :: ds, h => chainB_notJunk hc hs ds (stepB_notJunk hc hs d h)

/-- The renaming by a bump keeps the cell name. -/
theorem childCN_renB (K : Nat) (cnt cnt0 : Site → Nat) (a : Origin) (c : ACell) :
    childCN K (renB cnt cnt0 a) c = childCN K a c := by
  cases a with
  | alloc x =>
    show childCN K (if _ then _ else _) c = _
    split
    · rename_i h
      show Origin.hsym 0 (keyOfR (.alloc (x + 1))) c [] = .hsym 0 (keyOfR (.alloc x)) c []
      have hN : @Eq Nat (x % 2) 0 := h.1
      have e : @Eq Nat ((x + 1) / 2) (x / 2) := by omega
      simp only [keyOfR, e]
    · rfl
  | _ => rfl

/-- `renB` does not change a cell name. -/
theorem renB_childCN (K : Nat) (cnt cnt0 : Site → Nat) (a : Origin) (c : ACell) :
    renB cnt cnt0 (childCN K a c) = childCN K a c :=
  renB_of_ne_alloc cnt cnt0 (fun x => childCN_ne_alloc K a c x)

/-- `renB` keeps a universe origin in the universe of a recency context. -/
theorem renB_mem (hc : CtxROK cb.cn.ctx) (cnt cnt0 : Site → Nat) {a : Origin}
    (h : a ∈ cb.cn.ctx.origins) : renB cnt cnt0 a ∈ cb.cn.ctx.origins := by
  cases a with
  | alloc x =>
    show (if _ then _ else _) ∈ _
    split
    · rename_i hx
      have hN : @Eq Nat (x % 2) 0 := hx.1
      have e : Origin.alloc x = rNew (x / 2) := by
        show Origin.alloc x = .alloc (2 * (x / 2))
        exact congrArg Origin.alloc (show @Eq Nat x (2 * (x / 2)) by omega)
      have e2 : Origin.alloc (x + 1) = rOld (x / 2) := by
        show Origin.alloc (x + 1) = .alloc (2 * (x / 2) + 1)
        exact congrArg Origin.alloc (show @Eq Nat (x + 1) (2 * (x / 2) + 1) by omega)
      rw [e2]; rw [e] at h; exact hc.newOld _ h
    · exact h
  | _ => exact h

/-! ## The abstraction under a counter bump -/

/-- The counters of each ghost are not above the current counters. -/
def GhostLe (G : GNames) (cnt : Site → Nat) : Prop :=
  ∀ s n k g, G s n k = some g → ∀ t, g.cnt0 t ≤ cnt t

/-- A counter bump of site `s` renames the abstraction of each object except the next object
of `s`. -/
theorem alphaBO_bump {G : GNames} (st : CState) (hle : GhostLe G st.cnt) (s : Site) {o : Obj}
    (h : o ≠ .alloc s (st.cnt s)) :
    alphaBO cb G (st.bump s).cnt o = renameO s (alphaBO cb G st.cnt o) := by
  cases o with
  | alloc a n => exact alphaR_bump cb.cn.ctx.K st s h
  | sym b p =>
    cases b with
    | root r => exact alphaR_bump cb.cn.ctx.K st s h
    | fresh a n => exact alphaR_bump cb.cn.ctx.K st s h
    | havoc a n k =>
      cases e : G a n k with
      | none => rw [alphaBO_none _ e, alphaBO_none _ e, renameO_havoc]
      | some g =>
        rw [alphaBO_some _ e, alphaBO_some _ e]
        exact renB_bump (hle a n k g e) s _

/-! ## Default children of objects without ghost data -/

/-- The abstraction of the default child of an object that has no ghost data is the cell name
of the abstraction of the object. -/
theorem alphaBO_cdefault_plain {G : GNames} (cnt : Site → Nat) {o o' : Obj} {c : Cell}
    (hG : ∀ s n k p, o = .sym (.havoc s n k) p → G s n k = none)
    (h : cdefault o c = some o') :
    alphaBO cb G cnt o' = childCN cb.cn.ctx.K (alphaBO cb G cnt o) c.abs := by
  cases o with
  | alloc s n => cases h
  | sym b p =>
    cases h
    cases b with
    | root r => exact alpha_child _ (.root r) (fun _ _ _ e => by cases e) p c
    | fresh s n => exact alpha_child _ (.fresh s n) (fun _ _ _ e => by cases e) p c
    | havoc s n k =>
      have e := hG s n k p rfl
      rw [alphaBO_none _ e, alphaBO_none _ e]; rfl

/-- The abstraction of the default child of a callee object with ghost data is one step from
the abstraction of the object, at the counters of the call. -/
theorem alphaBO_cdefault_ghost {G : GNames} {s n k : Nat} {g : Ghost} (hG : G s n k = some g)
    (p : List Cell) (c : Cell) :
    alphaBO cb G g.cnt0 (.sym (.havoc s n k) (p ++ [c])) =
      stepB cb g.X (alphaBO cb G g.cnt0 (.sym (.havoc s n k) p)) c.abs := by
  rw [alphaBO_some _ hG, alphaBO_some _ hG, renB_same, renB_same, List.map_append,
    List.map_cons, List.map_nil, ← List.cons_append, chainB_append]

end DirectedAlias.Sound.BlockOnly
