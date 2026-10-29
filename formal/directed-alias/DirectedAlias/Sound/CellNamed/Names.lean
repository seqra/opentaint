import DirectedAlias.Sound.CellNamed.Concept

/-!
# Cell names, descendants, the exposed test, and the ghost abstraction

The soundness proof of design CN abstracts a callee object through a GHOST NAMING
`N : Names`. When the `n`-th execution of call site `s` writes the object with tag `k` into
the cell `(O, c)`, the proof sets `N s n k := childCN (alpha O) c`. An object at path `p` below
it has the name `extendCN (N s n k) p`. A callee object without a name (one that no call
wrote) has the junk origin `havoc s`, which is not in the universe.
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency

/-! ## Kinds of origins -/

/-- The junk origin of a callee object without a name. -/
def isJunk : Origin → Bool
  | .havoc _ => true
  | _ => false

/-- A cell name: a symbolic, deep or heap-child origin. -/
def isName : Origin → Bool
  | .sym _ _ => true
  | .deep _ => true
  | .hsym _ _ _ _ => true
  | .hdeep _ _ _ => true
  | _ => false

/-- A cell name is not junk. -/
theorem isName_notJunk {a : Origin} (h : isName a = true) : isJunk a = false := by
  cases a <;> simp_all [isName, isJunk]

/-- A cell name is not an allocation origin. -/
theorem isName_ne_alloc {a : Origin} (h : isName a = true) (x : Nat) : a ≠ .alloc x := by
  intro e; subst e; simp [isName] at h

/-- A cell name is never unique with recency, except a symbolic origin. -/
theorem uniqueR_name {once : Site → Bool} {eu : Bool} {a : Origin} (h : isName a = true)
    (hu : uniqueR once eu a = true) : ∃ b q, a = .sym b q := by
  cases a with
  | sym b q => exact ⟨b, q, rfl⟩
  | deep b => simp [uniqueR, Origin.uniqueB] at hu
  | hsym _ _ _ _ => simp [uniqueR, Origin.uniqueB] at hu
  | hdeep _ _ _ => simp [uniqueR, Origin.uniqueB] at hu
  | alloc _ => simp [isName] at h
  | havoc _ => simp [isName] at h

/-- The renaming of `retire` does not change a cell name. -/
theorem renameO_name (s : Site) {a : Origin} (h : isName a = true) : renameO s a = a := by
  unfold renameO
  split
  · rename_i e; exact absurd e (isName_ne_alloc h _)
  · rfl

/-- The renaming of `retire` does not change a junk origin. -/
theorem renameO_havoc (s a : Site) : renameO s (.havoc a) = .havoc a := by
  unfold renameO
  split
  · rename_i e; cases e
  · rfl

/-- The junk test is invariant under the renaming of `retire`. -/
theorem isJunk_renameO (s : Site) (a : Origin) : isJunk (renameO s a) = isJunk a := by
  unfold renameO
  split
  · rename_i e; subst e; rfl
  · rfl

/-! ## Cell names -/

/-- The name of a cell of an origin that is not junk is a cell name. -/
theorem childCN_name (K : Nat) {a : Origin} (c : ACell) (h : isJunk a = false) :
    isName (childCN K a c) = true := by
  cases a with
  | sym b q => show isName (symOrDeep K b (q ++ [c])) = true; unfold symOrDeep; split <;> rfl
  | deep b => rfl
  | alloc x => rfl
  | havoc s => simp [isJunk] at h
  | hsym s k c' q => show isName (if _ then _ else _) = true; split <;> rfl
  | hdeep s k c' => rfl

/-- The name of a cell is junk if and only if the origin is junk. -/
theorem isJunk_childCN (K : Nat) (a : Origin) (c : ACell) :
    isJunk (childCN K a c) = isJunk a := by
  cases a with
  | sym b q => show isJunk (symOrDeep K b (q ++ [c])) = false; unfold symOrDeep; split <;> rfl
  | deep b => rfl
  | alloc x => rfl
  | havoc s => rfl
  | hsym s k c' q => show isJunk (if _ then _ else _) = false; split <;> rfl
  | hdeep s k c' => rfl

/-- The name of a cell does not depend on the recency origin of an allocation site. -/
theorem childCN_renameO (K : Nat) (s : Site) (a : Origin) (c : ACell) :
    childCN K (renameO s a) c = childCN K a c := by
  unfold renameO
  split
  · rename_i e
    subst e
    show Origin.hsym 0 (keyOfR (rOld s)) c [] = Origin.hsym 0 (keyOfR (rNew s)) c []
    rw [keyOfR_rOld, keyOfR_rNew]
  · rfl

/-- The default content of an origin that is not an allocation origin is its cell name. -/
theorem adefault_childCN (K : Nat) {a : Origin} (h : ∀ x, a ≠ .alloc x) (c : ACell) :
    adefault K a c = [childCN K a c] := by
  cases a with
  | alloc x => exact absurd rfl (h x)
  | sym b q => rfl
  | deep b => rfl
  | havoc s => rfl
  | hsym s k c' q => rfl
  | hdeep s k c' => rfl

/-- A symbolic cell name is the cell name of a symbolic origin with the shorter path. -/
theorem childCN_sym_inv {K : Nat} {a : Origin} {c : ACell} {b : ABase} {q : List ACell}
    (h : childCN K a c = .sym b q) : ∃ q0, a = .sym b q0 ∧ q = q0 ++ [c] := by
  cases a with
  | sym b' q' =>
    change symOrDeep K b' (q' ++ [c]) = _ at h
    unfold symOrDeep at h
    split at h
    · cases h; exact ⟨q', rfl, rfl⟩
    · cases h
  | deep b' => cases h
  | alloc x => cases h
  | havoc s => cases h
  | hsym s k c' q' => change (if _ then _ else _) = _ at h; split at h <;> cases h
  | hdeep s k c' => cases h

/-- The cell name of a cell name is a name, and it has a nonempty symbolic path. -/
theorem childCN_ne_root (K : Nat) (a : Origin) (c : ACell) (b : ABase) :
    childCN K a c ≠ .sym b [] := by
  intro h
  obtain ⟨q0, _, e⟩ := childCN_sym_inv h
  cases q0 <;> cases e

/-- The name at a path that ends with `c` is the cell name of the name at the shorter path. -/
theorem extendCN_append (K : Nat) : ∀ (a : Origin) (q : List ACell) (c : ACell),
    extendCN K a (q ++ [c]) = childCN K (extendCN K a q) c
  | a, [], c => rfl
  | a, d :: ds, c => extendCN_append K (childCN K a d) ds c

/-- The name below a cell name is a cell name. -/
theorem extendCN_name (K : Nat) : ∀ {a : Origin} (q : List ACell), isName a = true →
    isName (extendCN K a q) = true
  | a, [], h => h
  | a, d :: ds, h => extendCN_name K ds (childCN_name K d (isName_notJunk h))

/-- The name below a name without an empty symbolic path has no empty symbolic path. -/
theorem extendCN_ne_root (K : Nat) : ∀ {a : Origin} (q : List ACell),
    (∀ b, a ≠ .sym b []) → ∀ b, extendCN K a q ≠ .sym b []
  | a, [], h => h
  | a, d :: ds, _ => extendCN_ne_root K ds (childCN_ne_root K a d)

/-! ## Prefixes and descendants -/

/-- Each path is a prefix of itself. -/
theorem preB_refl (p : List ACell) : preB p p = true := by
  simp [preB]

/-- A prefix is not longer than the path. -/
theorem preB_len {p q : List ACell} (h : preB p q = true) : p.length ≤ q.length := by
  have e : q.take p.length = p := of_decide_eq_true h
  have := congrArg List.length e
  rw [List.length_take] at this
  omega

/-- A prefix of a path is a prefix of each extension of the path. -/
theorem preB_append {p q : List ACell} (h : preB p q = true) (r : List ACell) :
    preB p (q ++ r) = true := by
  have e : q.take p.length = p := of_decide_eq_true h
  apply decide_eq_true
  rw [List.take_append_of_le_length (preB_len h), e]

/-- `descB` is equality or a proper descendant. -/
theorem descB_iff {a u : Origin} : descB a u = true ↔ a = u ∨ descM a u = true := by
  unfold descB
  rw [Bool.or_eq_true, decide_eq_true_iff]

/-- Each origin is a descendant of itself. -/
theorem descB_refl (a : Origin) : descB a a = true :=
  descB_iff.mpr (Or.inl rfl)

/-- A symbolic extension or the deep summary of a symbolic origin is a descendant. -/
theorem descM_sym (K : Nat) {b : ABase} {p q : List ACell} (h : preB p q = true) (c : ACell) :
    descM (.sym b p) (symOrDeep K b (q ++ [c])) = true := by
  unfold symOrDeep
  split
  · simp only [descM, decide_true, Bool.true_and]; exact preB_append h _
  · simp only [descM, decide_true]

/-- A heap-child extension or its deep summary is a descendant. -/
theorem descM_hsym (K : Nat) {s : Nat} {c0 : ACell} {key : Origin} {p q : List ACell}
    (h : preB p q = true) (c : ACell) :
    descM (.hsym s key c0 p) (if (q ++ [c]).length ≤ K then .hsym s key c0 (q ++ [c])
      else .hdeep s key c0) = true := by
  split
  · simp only [descM, decide_true, Bool.true_and]; exact preB_append h _
  · simp only [descM, decide_true, Bool.and_self]

/-- The heap children of an allocation origin are descendants. -/
theorem descM_alloc (K : Nat) {x : Nat} {key : Origin} {c0 : ACell} {q : List ACell}
    (hk : key = keyOfR (.alloc x)) (c : ACell) :
    descM (.alloc x) (if (q ++ [c]).length ≤ K then .hsym 0 key c0 (q ++ [c])
      else .hdeep 0 key c0) = true := by
  subst hk
  split
  · simp only [descM, decide_true, Bool.and_self]
  · simp only [descM, decide_true, Bool.and_self]

/-- The cell name of an origin is a descendant of the origin. -/
theorem descB_child_self (K : Nat) (a : Origin) (c : ACell) : descB a (childCN K a c) = true := by
  apply descB_iff.mpr
  cases a with
  | sym b p => exact Or.inr (descM_sym K (preB_refl p) c)
  | deep b => exact Or.inl rfl
  | alloc x => right; simp only [childCN, descM, decide_true, Bool.and_self]
  | havoc s => exact Or.inl rfl
  | hsym s k c' q => exact Or.inr (descM_hsym K (preB_refl q) c)
  | hdeep s k c' => exact Or.inl rfl

/-- The descendants of an origin are closed under cell names. -/
theorem descB_child (K : Nat) {a u : Origin} (c : ACell) (h : descB a u = true) :
    descB a (childCN K u c) = true := by
  rcases descB_iff.mp h with e | h'
  · subst e; exact descB_child_self K a c
  clear h
  apply descB_iff.mpr
  right
  cases a <;> cases u <;> simp only [descM, Bool.false_eq_true] at h'
  case sym.sym b p b' q =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨rfl, hp⟩ := h'
    exact descM_sym K hp c
  case sym.deep b p b' => exact h'
  case alloc.hsym x s k c' q =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨rfl, hk⟩ := h'
    exact descM_alloc K hk c
  case alloc.hdeep x s k c' => exact h'
  case hsym.hsym s k c0 p s' k' c' q =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hp⟩ := h'
    exact descM_hsym K hp c
  case hsym.hdeep s k c0 p s' k' c' => exact h'

/-- The names below a descendant are descendants. -/
theorem descB_extend (K : Nat) {a : Origin} : ∀ {u : Origin} (q : List ACell),
    descB a u = true → descB a (extendCN K u q) = true
  | u, [], h => h
  | u, d :: ds, h => descB_extend K ds (descB_child K d h)

/-- A symbolic descendant has a symbolic ancestor with a prefix path. -/
theorem descB_sym_inv {a : Origin} {b : ABase} {q : List ACell}
    (h : descB a (.sym b q) = true) : ∃ p, a = .sym b p ∧ preB p q = true := by
  rcases descB_iff.mp h with e | h'
  · exact ⟨q, e, preB_refl q⟩
  clear h
  cases a <;> simp only [descM, Bool.false_eq_true] at h'
  case sym b' p =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    obtain ⟨rfl, hp⟩ := h'
    exact ⟨p, rfl, hp⟩

/-- A covered origin is a descendant of an origin of `R`. -/
theorem coveredB_iff {R : List Origin} {u : Origin} :
    coveredB R u = true ↔ ∃ a ∈ R, descB a u = true := by
  simp [coveredB, List.any_eq_true]

/-! ## The exposed test -/

/-- An origin below an exposed origin passes the exposed test. -/
theorem expB_of {E : List Origin} {b : ABase} {p q : List ACell} (hm : Origin.sym b p ∈ E)
    (hl : p.length < q.length) (hp : preB p q = true) : expB E (.sym b q) = true := by
  apply List.any_eq_true.mpr
  refine ⟨_, hm, ?_⟩
  simp only [decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hl, hp⟩

/-- The exposed test gives an exposed origin with a proper prefix path. -/
theorem expB_inv {E : List Origin} {b : ABase} {q : List ACell}
    (h : expB E (.sym b q) = true) :
    ∃ p, Origin.sym b p ∈ E ∧ p.length < q.length ∧ preB p q = true := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.mp h
  cases e with
  | sym b' p =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hl⟩, hp⟩ := h
    exact ⟨p, he, hl, hp⟩
  | deep _ => simp at h
  | alloc _ => simp at h
  | havoc _ => simp at h
  | hsym _ _ _ _ => simp at h
  | hdeep _ _ _ => simp at h

/-- The exposed test is monotone in the exposed set. -/
theorem expB_mono {E E' : List Origin} (hs : ∀ a ∈ E, a ∈ E') {u : Origin}
    (h : expB E u = true) : expB E' u = true := by
  cases u with
  | sym b q =>
    obtain ⟨p, hm, hl, hp⟩ := expB_inv h
    exact expB_of (hs _ hm) hl hp
  | _ => simp [expB] at h

/-- The exposed test is invariant under the renaming of `retire` in the exposed set. -/
theorem expB_renameL {E : List Origin} (s : Site) {u : Origin} (h : expB E u = true) :
    expB (renameL s E) u = true := by
  cases u with
  | sym b q =>
    obtain ⟨p, hm, hl, hp⟩ := expB_inv h
    refine expB_of ?_ hl hp
    refine List.mem_map.mpr ⟨_, hm, ?_⟩
    exact renameO_name s rfl
  | _ => simp [expB] at h

/-- A proper prefix of a path is a proper prefix of each extension of the path. -/
theorem expB_child {E : List Origin} {b : ABase} {q : List ACell} (c : ACell)
    (h : expB E (.sym b q) = true) : expB E (.sym b (q ++ [c])) = true := by
  obtain ⟨p, hm, hl, hp⟩ := expB_inv h
  refine expB_of hm ?_ (preB_append hp _)
  rw [List.length_append]; omega

/-! ## The ghost abstraction -/

/-- A ghost naming of the callee objects: the name of the head object that the `n`-th
execution of call site `s` wrote with tag `k`, if a call wrote it. -/
abbrev Names := Site → Nat → Nat → Option Origin

/-- The abstraction of design CN. Entry, fresh and allocation objects have their recency
origin. A callee object at path `p` below a named head has the name below the head name.
A callee object without a name has the junk origin. -/
def alphaCN (K : Nat) (N : Names) (cnt : Site → Nat) : Obj → Origin
  | .sym (.root r) p => alpha K (.sym (.root r) p)
  | .sym (.fresh s n) p => alpha K (.sym (.fresh s n) p)
  | .sym (.havoc s n k) p => match N s n k with
    | some a => extendCN K a (p.map Cell.abs)
    | none => .havoc s
  | .alloc s n => if n + 1 = cnt s then rNew s else rOld s

/-- The abstraction of a callee object with a named head. -/
theorem alphaCN_havoc_some (K : Nat) {N : Names} (cnt : Site → Nat) {s n k : Nat} {a : Origin}
    (h : N s n k = some a) (p : List Cell) :
    alphaCN K N cnt (.sym (.havoc s n k) p) = extendCN K a (p.map Cell.abs) := by
  show (match N s n k with
    | some a => extendCN K a (p.map Cell.abs)
    | none => .havoc s) = _
  rw [h]

/-- The abstraction of a callee object without a name is junk. -/
theorem alphaCN_havoc_none (K : Nat) {N : Names} (cnt : Site → Nat) {s n k : Nat}
    (h : N s n k = none) (p : List Cell) :
    alphaCN K N cnt (.sym (.havoc s n k) p) = .havoc s := by
  show (match N s n k with
    | some a => extendCN K a (p.map Cell.abs)
    | none => .havoc s) = _
  rw [h]

/-- The abstraction of an object that is not a callee object is its recency abstraction. -/
theorem alphaCN_eq_alphaR (K : Nat) (N : Names) (st : CState) {o : Obj}
    (h : ∀ s n k p, o ≠ .sym (.havoc s n k) p) : alphaCN K N st.cnt o = alphaR K st o := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh s n => rfl
    | havoc s n k => exact absurd rfl (h s n k p)

/-- The abstraction of the entry object of a root is its root origin. -/
theorem alphaCN_root (K : Nat) (N : Names) (cnt : Site → Nat) (r : Root) :
    alphaCN K N cnt (.sym (.root r) []) = .sym (.root r) [] := by
  show symOrDeep K (.root r) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le K)

/-- The abstraction of a fresh head object is its fresh origin. -/
theorem alphaCN_fresh (K : Nat) (N : Names) (cnt : Site → Nat) (s n : Nat) :
    alphaCN K N cnt (.sym (.fresh s n) []) = .sym (.fresh s) [] := by
  show symOrDeep K (.fresh s) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le K)

/-- The next object of site `a` has the origin `rNew a` after the bump. -/
theorem alphaCN_new (K : Nat) (N : Names) (st : CState) (a : Site) :
    alphaCN K N (st.bump a).cnt (.alloc a (st.cnt a)) = rNew a := by
  show (if st.cnt a + 1 = fupd st.cnt a (st.cnt a + 1) a then rNew a else rOld a) = rNew a
  rw [fupd_same, ite_eq_left rfl]

/-- The abstraction of a symbolic entry or fresh object is the default child of its parent. -/
theorem alpha_child (K : Nat) (b : Base) (hb : ∀ s n k, b ≠ .havoc s n k) (p : List Cell)
    (c : Cell) : alpha K (.sym b (p ++ [c])) = childCN K (alpha K (.sym b p)) c.abs := by
  have h := alphaV_cdefault K (.sym b p) c
  have hna : ∀ x, alpha K (.sym b p) ≠ .alloc x := by
    intro x e
    cases b with
    | root r => simp only [alpha, symOrDeep] at e; split at e <;> cases e
    | fresh s n => simp only [alpha, symOrDeep] at e; split at e <;> cases e
    | havoc s n k => exact hb s n k rfl
  rw [adefault_childCN K hna] at h
  simp only [cdefault, alphaV, List.cons.injEq, and_true] at h
  exact h

/-- The abstraction of the default child of an object is the cell name of the abstraction. -/
theorem alphaCN_cdefault (K : Nat) (N : Names) (cnt : Site → Nat) {o o' : Obj} {c : Cell}
    (h : cdefault o c = some o') : alphaCN K N cnt o' = childCN K (alphaCN K N cnt o) c.abs := by
  cases o with
  | alloc s n => cases h
  | sym b p =>
    cases h
    cases b with
    | root r => exact alpha_child K (.root r) (fun _ _ _ e => by cases e) p c
    | fresh s n => exact alpha_child K (.fresh s n) (fun _ _ _ e => by cases e) p c
    | havoc s n k =>
      cases e : N s n k with
      | none => rw [alphaCN_havoc_none K cnt e, alphaCN_havoc_none K cnt e]; rfl
      | some a =>
        rw [alphaCN_havoc_some K cnt e, alphaCN_havoc_some K cnt e, List.map_append,
          List.map_cons, List.map_nil, extendCN_append]

/-- The abstraction of a symbolic object is not an allocation origin, if each ghost name is a
cell name. -/
theorem alphaCN_sym_ne_alloc (K : Nat) {N : Names} (cnt : Site → Nat)
    (hN : ∀ s n k a, N s n k = some a → isName a = true) (b : Base) (p : List Cell) (x : Nat) :
    alphaCN K N cnt (.sym b p) ≠ .alloc x := by
  intro e
  cases b with
  | root r => simp only [alphaCN, alpha, symOrDeep] at e; split at e <;> cases e
  | fresh s n => simp only [alphaCN, alpha, symOrDeep] at e; split at e <;> cases e
  | havoc s n k =>
    cases e2 : N s n k with
    | none => rw [alphaCN_havoc_none K cnt e2] at e; cases e
    | some a =>
      rw [alphaCN_havoc_some K cnt e2] at e
      exact isName_ne_alloc (extendCN_name K _ (hN s n k a e2)) x e

/-- The abstraction of a default child is in the abstract default content of the parent, if
each ghost name is a cell name. -/
theorem alphaCN_cdefault_mem (K : Nat) {N : Names} (cnt : Site → Nat)
    (hN : ∀ s n k a, N s n k = some a → isName a = true) {o o' : Obj} {c : Cell}
    (h : cdefault o c = some o') : alphaCN K N cnt o' ∈ adefault K (alphaCN K N cnt o) c.abs := by
  rw [alphaCN_cdefault K N cnt h]
  cases o with
  | alloc s n => cases h
  | sym b p =>
    rw [adefault_childCN K (alphaCN_sym_ne_alloc K cnt hN b p)]
    exact List.mem_singleton.mpr rfl

end DirectedAlias.Sound.CellNamed
