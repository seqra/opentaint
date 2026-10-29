import DirectedAlias.DSU.Model

/-!
# Lemmas about the DSU operations on atoms

The relation `co D a b` says that atoms `a` and `b` are in one group of `D`.
Each operation keeps `co` on the atoms it does not remove. `canon` keeps it on the universe.
-/

namespace DirectedAlias.DSU

open DirectedAlias

/-- Atoms `a` and `b` are in one group. -/
def co (D : DState) (a b : Atom) : Prop := ∃ n, nodeOf D a = some n ∧ nodeOf D b = some n

/-- `D'` keeps each `co` fact of `D`. -/
def Pres (D D' : DState) : Prop := ∀ a b, co D a b → co D' a b

/-- `co` is symmetric. -/
theorem co.symm {D : DState} {a b : Atom} (h : co D a b) : co D b a := by
  obtain ⟨n, h1, h2⟩ := h; exact ⟨n, h2, h1⟩

/-- `co` is transitive. -/
theorem co.trans {D : DState} {a b c : Atom} (h1 : co D a b) (h2 : co D b c) : co D a c := by
  obtain ⟨n, e1, e2⟩ := h1
  obtain ⟨m, f1, f2⟩ := h2
  rw [e2] at f1; cases f1
  exact ⟨n, e1, f2⟩

/-- A renaming of all groups keeps `co`. -/
theorem pres_of_map {D D' : DState} (τ : Node → Node)
    (h : ∀ a, nodeOf D' a = (nodeOf D a).map τ) : Pres D D' := by
  rintro a b ⟨n, h1, h2⟩
  exact ⟨τ n, by rw [h, h1]; rfl, by rw [h, h2]; rfl⟩

/-- Lookup in a list with renamed values. -/
theorem lk_map_snd {α : Type} [DecidableEq α] (g : Node → Node) (a : α) :
    ∀ (l : List (α × Node)), lk a (l.map (fun p => (p.1, g p.2))) = (lk a l).map g
  | [] => rfl
  | (k, v) :: l => by
    simp only [List.map_cons, lk]
    by_cases h : a = k
    · simp [h]
    · simp [h, lk_map_snd g a l]

/-- A successful lookup gives a member. -/
theorem lk_mem {α : Type} [DecidableEq α] {a : α} {n : Node} :
    ∀ {l : List (α × Node)}, lk a l = some n → (a, n) ∈ l
  | [], h => by cases h
  | (k, v) :: l, h => by
    unfold lk at h
    by_cases hk : a = k
    · rw [ite_eq_left hk] at h; cases h; subst hk; exact List.mem_cons_self
    · rw [ite_eq_right hk] at h; exact List.mem_cons_of_mem _ (lk_mem h)

/-- Lookup in an appended list. -/
theorem lk_append {α : Type} [DecidableEq α] (a : α) :
    ∀ (l m : List (α × Node)), lk a (l ++ m) = (match lk a l with | some v => some v | none => lk a m)
  | [], m => rfl
  | (k, v) :: l, m => by
    simp only [List.cons_append, lk]
    by_cases h : a = k
    · simp [h]
    · simp only [h, ite_false]; exact lk_append a l m

/-- In a list without conflicts, each member is found by lookup. -/
theorem lk_of_noconf {α : Type} [DecidableEq α] {a : α} {n : Node} :
    ∀ {l : List (α × Node)}, conflictL l = none → (a, n) ∈ l → lk a l = some n
  | [], _, h => by cases h
  | (b, m) :: rest, hc, hm => by
    have hc' : conflictL rest = none ∧ ∀ m', lk b rest = some m' → m' = m := by
      unfold conflictL at hc
      cases hl : lk b rest with
      | none => rw [hl] at hc; exact ⟨hc, fun _ h => by cases h⟩
      | some m' =>
        rw [hl] at hc
        simp only at hc
        by_cases he : m' = m
        · rw [ite_eq_left he] at hc; exact ⟨hc, fun m'' h => by cases h; exact he⟩
        · rw [ite_eq_right he] at hc; cases hc
    unfold lk
    rcases List.mem_cons.mp hm with he | hr
    · cases he; simp
    · have ih := lk_of_noconf hc'.1 hr
      by_cases hab : a = b
      · subst hab; rw [ite_eq_left rfl]; exact congrArg some (hc'.2 n ih).symm
      · rw [ite_eq_right hab]; exact ih

/-- No conflict in the state gives no conflict in its atoms. -/
theorem conflict_none {D : DState} (h : conflict D = none) : conflictL D.atoms = none := by
  unfold conflict at h
  cases hc : conflictL D.atoms with
  | none => rfl
  | some p => rw [hc] at h; cases h

/-- `normalize` renames the groups of the atoms, and its result has no atom conflict. -/
theorem normalize_spec : ∀ (k : Nat) (D D' : DState), normalize k D = some D' →
    ∃ τ : Node → Node, D'.atoms = D.atoms.map (fun p => (p.1, τ p.2)) ∧ conflictL D'.atoms = none
  | 0, D, D', h => by
    unfold normalize at h
    cases hc : conflict D with
    | none =>
      rw [hc] at h; cases h
      exact ⟨id, by simp, conflict_none hc⟩
    | some _ => rw [hc] at h; cases h
  | k + 1, D, D', h => by
    unfold normalize at h
    cases hc : conflict D with
    | none =>
      rw [hc] at h; cases h
      exact ⟨id, by simp, conflict_none hc⟩
    | some p =>
      obtain ⟨n, m⟩ := p
      rw [hc] at h
      obtain ⟨τ, h1, h2⟩ := normalize_spec k _ _ h
      refine ⟨fun x => τ (renN m n x), ?_, h2⟩
      rw [h1]; simp [ren, List.map_map, Function.comp_def]

/-- After `normalize`, the group of each atom is the renamed old group. -/
theorem normalize_nodeOf {k : Nat} {D D' : DState} (h : normalize k D = some D') :
    ∃ τ : Node → Node, (∀ a, nodeOf D' a = (nodeOf D a).map τ) ∧
      ∀ a n, (a, n) ∈ D.atoms → nodeOf D' a = some (τ n) := by
  obtain ⟨τ, h1, h2⟩ := normalize_spec k D D' h
  refine ⟨τ, fun a => by unfold nodeOf; rw [h1, lk_map_snd], fun a n hm => ?_⟩
  unfold nodeOf
  apply lk_of_noconf h2
  rw [h1]
  exact List.mem_map.mpr ⟨(a, n), hm, rfl⟩

/-- `ren` renames the groups of the atoms. -/
theorem nodeOf_ren (D : DState) (m n : Node) (a : Atom) :
    nodeOf (ren D m n) a = (nodeOf D a).map (renN m n) := by
  unfold nodeOf ren
  exact lk_map_snd (renN m n) a D.atoms

/-- `addAtom` puts the atom into the group. -/
theorem nodeOf_addAtom (D : DState) (a : Atom) (n : Node) (c : Atom) :
    nodeOf (addAtom D a n) c = if c = a then some n else nodeOf D c := rfl

/-- A fresh node does not change the groups of the atoms. -/
theorem nodeOf_fresh (D : DState) (c : Atom) : nodeOf (freshNode D).2 c = nodeOf D c := rfl

/-- `delAtom` removes only the given atom. -/
theorem nodeOf_delAtom (D : DState) (a c : Atom) :
    nodeOf (delAtom D a) c = if c = a then none else nodeOf D c := by
  unfold nodeOf delAtom
  simp only
  induction D.atoms with
  | nil => simp [lk]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : k = a
    · subst hk
      simp only [List.filter_cons, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [ih]
      by_cases hc : c = k
      · simp [hc]
      · simp [hc, lk]
    · have hk' : (!decide (k = a)) = true := by simp [hk]
      simp only [List.filter_cons, hk', ite_true, lk]
      rw [ih]
      by_cases hc : c = k
      · subst hc; simp [hk]
      · simp [hc]

/-- `unite` puts the atoms of the two groups into one group, and keeps `co`. -/
theorem unite_spec {D D' : DState} {m n : Node} (h : unite D m n = some D') :
    Pres D D' ∧ ∀ a b, nodeOf D a = some m → nodeOf D b = some n → co D' a b := by
  unfold unite at h
  obtain ⟨τ, h1, _⟩ := normalize_nodeOf h
  have hmap : ∀ a, nodeOf D' a = (nodeOf D a).map (fun x => τ (renN m n x)) := by
    intro a; rw [h1, nodeOf_ren]; cases nodeOf D a <;> rfl
  refine ⟨pres_of_map _ hmap, fun a b ha hb => ⟨τ n, ?_, ?_⟩⟩
  · rw [hmap, ha]; simp [renN]
  · rw [hmap, hb]; simp [renN]

/-- `unionAtoms` of two different atoms puts them into one group and keeps `co`. -/
theorem unionAtoms_spec {D D' : DState} {a b : Atom} (hab : a ≠ b)
    (h : unionAtoms D a b = some D') : co D' a b ∧ Pres D D' := by
  unfold unionAtoms at h
  rw [ite_eq_right hab] at h
  cases ha : nodeOf D a with
  | some n =>
    cases hb : nodeOf D b with
    | some m =>
      rw [ha, hb] at h
      obtain ⟨hp, hc⟩ := unite_spec h
      exact ⟨(hc b a hb ha).symm, hp⟩
    | none =>
      rw [ha, hb] at h
      cases h
      refine ⟨⟨n, ?_, ?_⟩, ?_⟩
      · rw [nodeOf_addAtom, ite_eq_right hab, ha]
      · rw [nodeOf_addAtom, ite_eq_left rfl]
      · rintro c d ⟨k, h1, h2⟩
        have hc : c ≠ b := fun e => by rw [e, hb] at h1; cases h1
        have hd : d ≠ b := fun e => by rw [e, hb] at h2; cases h2
        exact ⟨k, by rw [nodeOf_addAtom, ite_eq_right hc, h1], by rw [nodeOf_addAtom, ite_eq_right hd, h2]⟩
  | none =>
    cases hb : nodeOf D b with
    | some m =>
      rw [ha, hb] at h
      cases h
      refine ⟨⟨m, ?_, ?_⟩, ?_⟩
      · rw [nodeOf_addAtom, ite_eq_left rfl]
      · rw [nodeOf_addAtom, ite_eq_right (Ne.symm hab), hb]
      · rintro c d ⟨k, h1, h2⟩
        have hc : c ≠ a := fun e => by rw [e, ha] at h1; cases h1
        have hd : d ≠ a := fun e => by rw [e, ha] at h2; cases h2
        exact ⟨k, by rw [nodeOf_addAtom, ite_eq_right hc, h1], by rw [nodeOf_addAtom, ite_eq_right hd, h2]⟩
    | none =>
      rw [ha, hb] at h
      cases h
      refine ⟨⟨D.next, ?_, ?_⟩, ?_⟩
      · rw [nodeOf_addAtom, ite_eq_right hab, nodeOf_addAtom, ite_eq_left rfl]; rfl
      · rw [nodeOf_addAtom, ite_eq_left rfl]; rfl
      · rintro c d ⟨k, h1, h2⟩
        have hca : c ≠ a := fun e => by rw [e, ha] at h1; cases h1
        have hda : d ≠ a := fun e => by rw [e, ha] at h2; cases h2
        have hcb : c ≠ b := fun e => by rw [e, hb] at h1; cases h1
        have hdb : d ≠ b := fun e => by rw [e, hb] at h2; cases h2
        refine ⟨k, ?_, ?_⟩
        · rw [nodeOf_addAtom, ite_eq_right hcb, nodeOf_addAtom, ite_eq_right hca, nodeOf_fresh, h1]
        · rw [nodeOf_addAtom, ite_eq_right hdb, nodeOf_addAtom, ite_eq_right hda, nodeOf_fresh, h2]

/-- `assign D x b` puts `x` into the group of `b`, and keeps `co` of the other atoms. -/
theorem assign_spec {D D' : DState} {x : Var} {b : Atom} (hb : b ≠ .loc x)
    (h : assign D x b = some D') :
    co D' (.loc x) b ∧ ∀ a c, a ≠ .loc x → c ≠ .loc x → co D a c → co D' a c := by
  unfold assign at h
  obtain ⟨h1, h2⟩ := unionAtoms_spec (Ne.symm hb) h
  refine ⟨h1, fun a c ha hc hco => h2 a c ?_⟩
  obtain ⟨n, e1, e2⟩ := hco
  exact ⟨n, by rw [nodeOf_delAtom, ite_eq_right ha, e1], by rw [nodeOf_delAtom, ite_eq_right hc, e2]⟩

/-- Lookup in a filtered map over the universe. -/
theorem lk_filterMap (g : Atom → Option Node) (σ : Node → Nat) (a : Atom) :
    ∀ (U : List Atom), lk a (U.filterMap (fun b => (g b).map (fun n => (b, σ n)))) =
      if a ∈ U then (g a).map σ else none
  | [] => by simp [lk]
  | b :: U => by
    rw [List.filterMap_cons]
    cases hg : g b with
    | none =>
      simp only [Option.map_none]
      rw [lk_filterMap g σ a U]
      by_cases hab : a = b
      · subst hab; simp [hg]
      · simp [hab]
    | some n =>
      simp only [Option.map_some, lk]
      by_cases hab : a = b
      · subst hab; simp [hg]
      · simp only [hab, ite_false]; rw [lk_filterMap g σ a U]; simp [hab]

/-- `canon` renames the group of each universe atom. -/
theorem nodeOf_canon (cx : DCtx) (D : DState) {a : Atom} (ha : a ∈ cx.U) :
    nodeOf (canon cx D) a = (nodeOf D a).map (idxIn (canonMap cx D)) := by
  unfold canon nodeOf
  simp only
  rw [lk_filterMap (fun b => lk b D.atoms) _ a cx.U, ite_eq_left ha]

/-- `canon` keeps `co` on the universe. -/
theorem co_canon {cx : DCtx} {D : DState} {a b : Atom} (ha : a ∈ cx.U) (hb : b ∈ cx.U)
    (h : co D a b) : co (canon cx D) a b := by
  obtain ⟨n, h1, h2⟩ := h
  exact ⟨_, by rw [nodeOf_canon cx D ha, h1]; rfl, by rw [nodeOf_canon cx D hb, h2]; rfl⟩

/-- The join keeps `co` of the left state and of the right state on the universe. -/
theorem joinD_spec {cx : DCtx} {A B J : DState} (h : joinD cx A B = some J) :
    (∀ a b, a ∈ cx.U → b ∈ cx.U → co A a b → co J a b) ∧
    (∀ a b, a ∈ cx.U → b ∈ cx.U → co B a b → co J a b) := by
  unfold joinD at h
  simp only at h
  cases hn : normalize _ (⟨A.atoms ++ (shift A.next B).atoms, A.edges ++ (shift A.next B).edges,
      (shift A.next B).next⟩ : DState) with
  | none => rw [hn] at h; cases h
  | some D' =>
    rw [hn] at h
    cases h
    obtain ⟨τ, h1, h2⟩ := normalize_nodeOf hn
    constructor
    · intro a b ha hb hco
      apply co_canon ha hb
      apply pres_of_map τ h1
      obtain ⟨n, e1, e2⟩ := hco
      refine ⟨n, ?_, ?_⟩
      · show lk a (A.atoms ++ _) = some n
        rw [lk_append]; unfold nodeOf at e1; rw [e1]
      · show lk b (A.atoms ++ _) = some n
        rw [lk_append]; unfold nodeOf at e2; rw [e2]
    · intro a b ha hb hco
      apply co_canon ha hb
      obtain ⟨n, e1, e2⟩ := hco
      have m1 : (a, n + A.next) ∈ A.atoms ++ (shift A.next B).atoms :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(a, n), lk_mem e1, rfl⟩)
      have m2 : (b, n + A.next) ∈ A.atoms ++ (shift A.next B).atoms :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(b, n), lk_mem e2, rfl⟩)
      exact ⟨τ (n + A.next), h2 a _ m1, h2 b _ m2⟩

/-- The loop result `R` is a fixpoint: the join of the entry and the body result is `R`. -/
theorem loopD_spec {cx : DCtx} {body : DState → Option DState} {X : DState} :
    ∀ (k : Nat) (Y R : DState), loopD cx body X k Y = some R →
      ∃ B, body R = some B ∧ joinD cx X B = some R
  | 0, _, _, h => by cases h
  | k + 1, Y, R, h => by
    unfold loopD at h
    cases hb : body Y with
    | none => rw [hb] at h; cases h
    | some B =>
      rw [hb] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      cases hj : joinD cx X B with
      | none => rw [hj] at h; cases h
      | some J =>
        rw [hj] at h
        simp only [Option.bind_some] at h
        by_cases he : J = Y
        · rw [ite_eq_left he] at h; cases h; subst he; exact ⟨B, hb, hj⟩
        · rw [ite_eq_right he] at h; exact loopD_spec k J R h

/-- The entry state puts each bound variable into the group of its root. -/
theorem initAux_spec (fr : Frame) :
    ∀ (xs : List Var) (D D' : DState), initAux fr xs D = some D' →
      Pres D D' ∧ ∀ x ∈ xs, ∀ r, fr.root? x = some r → co D' (.loc x) (.root r)
  | [], D, D', h => by
    cases h; exact ⟨fun _ _ h => h, fun _ h => by cases h⟩
  | x :: xs, D, D', h => by
    unfold initAux at h
    cases hr : fr.root? x with
    | none =>
      rw [hr] at h
      obtain ⟨hp, hc⟩ := initAux_spec fr xs D D' h
      refine ⟨hp, fun y hy r hry => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hr] at hry; cases hry
      · exact hc y hy r hry
    | some r =>
      rw [hr] at h
      simp only at h
      cases hu : unionAtoms D (.loc x) (.root r) with
      | none => rw [hu] at h; cases h
      | some D1 =>
        rw [hu] at h
        simp only [Option.bind_some] at h
        obtain ⟨hc1, hp1⟩ := unionAtoms_spec (by intro e; cases e) hu
        obtain ⟨hp, hc⟩ := initAux_spec fr xs D1 D' h
        refine ⟨fun a b hab => hp a b (hp1 a b hab), fun y hy r' hry => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [hr] at hry; cases hry; exact hp _ _ hc1
        · exact hc y hy r' hry

end DirectedAlias.DSU
