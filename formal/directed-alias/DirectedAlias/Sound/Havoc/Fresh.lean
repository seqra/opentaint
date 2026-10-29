import DirectedAlias.Sound.Havoc.Concept

/-!
# Strict havoc objects are new

`HavocS` does not state that a new havoc object differs from each object that exists before
the call. This file proves it for each strict execution from a frame entry: the new object
`sym (havoc s n k) _` of a call has `n = cnt s`, and no variable and no written cell holds an
object with that index before the call (`fresh_at_call`).
So `HavocS` is strict A2 in full: distinct objects for distinct cells (`HavocS.inj`), and no
object that exists before the call.
-/

namespace DirectedAlias.Sound.Havoc

open DirectedAlias

/-- An object is created in a state: a havoc object has an index below the counter of its site.
Other objects are always created. -/
def Created (st : CState) : Obj → Prop
  | .sym (.havoc s n _) _ => n < st.cnt s
  | _ => True

/-- Each variable holds a created object, and each cell holds its default content or a created
object. -/
structure HInv (st : CState) : Prop where
  env : ∀ x o, st.env x = some o → Created st o
  heap : ∀ o c o', st.heap o c = some o' → st.heap o c = cdefault o c ∨ Created st o'

/-- A counter bump keeps each object created. -/
theorem Created.bump {st : CState} {o : Obj} (h : Created st o) (a : Site) :
    Created (st.bump a) o := by
  cases o with
  | alloc _ _ => trivial
  | sym b p =>
    cases b with
    | root _ => trivial
    | fresh _ _ => trivial
    | havoc s n k =>
      show n < fupd st.cnt a (st.cnt a + 1) s
      have h' : n < st.cnt s := h
      by_cases e : s = a
      · subst e; rw [fupd_same]; omega
      · rw [fupd_ne _ _ e]; exact h'

/-- The default child of a created object is created. -/
theorem Created.cdefault {st : CState} {o o' : Obj} {c : Cell} (h : Created st o)
    (hd : DirectedAlias.cdefault o c = some o') : Created st o' := by
  cases o with
  | alloc _ _ => cases hd
  | sym b p =>
    cases hd
    cases b with
    | root _ => trivial
    | fresh _ _ => trivial
    | havoc s n k => exact h

/-- The invariant depends only on the environment, the heap and the counters. -/
theorem HInv.congr {s s' : CState} (h : HInv s) (he : s'.env = s.env) (hh : s'.heap = s.heap)
    (hc : s'.cnt = s.cnt) : HInv s' := by
  have hcr : ∀ o, Created s' o ↔ Created s o := by
    intro o
    cases o with
    | alloc _ _ => exact Iff.rfl
    | sym b p =>
      cases b with
      | root _ => exact Iff.rfl
      | fresh _ _ => exact Iff.rfl
      | havoc s0 n k => show n < s'.cnt s0 ↔ n < s.cnt s0; rw [hc]
  refine ⟨fun x o e => (hcr o).mpr (h.env x o (he ▸ e)), fun o c o' e => ?_⟩
  rw [hh] at e ⊢
  rcases h.heap o c o' e with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((hcr o').mpr h1)

/-- A counter bump keeps the invariant. -/
theorem HInv.bump {st : CState} (h : HInv st) (a : Site) : HInv (st.bump a) where
  env x o e := (h.env x o e).bump a
  heap o c o' e := (h.heap o c o' e).imp id (fun h1 => h1.bump a)

/-- Setting a variable to a created object keeps the invariant. -/
theorem HInv.setVar {st : CState} (h : HInv st) (x : Var) {v : Val}
    (hv : ∀ o, v = some o → Created st o) : HInv (st.setVar x v) where
  env y o e := by
    change fupd st.env x v y = some o at e
    by_cases ey : y = x
    · subst ey; rw [fupd_same] at e; exact hv o e
    · rw [fupd_ne _ _ ey] at e; exact h.env y o e
  heap := h.heap

/-- The content of a cell of a created object is created. -/
theorem HInv.read {st : CState} (h : HInv st) {o o' : Obj} {c : Cell} (ho : Created st o)
    (e : st.heap o c = some o') : Created st o' := by
  rcases h.heap o c o' e with h1 | h1
  · rw [h1] at e; exact ho.cdefault e
  · exact h1

/-- Writing a created value into a cell keeps the invariant. -/
theorem HInv.setCell {st : CState} (h : HInv st) (o : Obj) (c : Cell) {v : Val}
    (hv : ∀ o', v = some o' → Created st o') : HInv (st.setCell o c v) where
  env := h.env
  heap o1 c1 o2 e := by
    change fupd2 st.heap o c v o1 c1 = some o2 at e
    show fupd2 st.heap o c v o1 c1 = _ ∨ _
    by_cases ec : o1 = o ∧ c1 = c
    · obtain ⟨rfl, rfl⟩ := ec; rw [fupd2_same] at e; exact Or.inr (hv o2 e)
    · rw [fupd2_ne _ _ ec] at e ⊢; exact h.heap o1 c1 o2 e

/-- The entry state satisfies the invariant. -/
theorem hinv_init (fr : Frame) : HInv (CState.init fr) where
  env x o e := by
    change (fr.root? x).map _ = some o at e
    cases hr : fr.root? x with
    | none => rw [hr] at e; cases e
    | some r => rw [hr] at e; cases e; trivial
  heap _ _ _ _ := Or.inl rfl

/-- One strict step keeps the invariant. -/
theorem SStepS.hinv {src : Nat → Obj × Cell} {st : Stmt} {s s' : CState}
    (hs : SStepS src st s s') (h : HInv s) : HInv s' := by
  cases hs with
  | new => exact (h.setVar _ (fun o e => by cases e; trivial)).bump _
  | null => exact h.setVar _ (fun o e => by cases e)
  | copy => exact h.setVar _ (fun o e => h.env _ o e)
  | load he => exact h.setVar _ (fun o' e => h.read (h.env _ _ he) e)
  | store he => exact h.setCell _ _ (fun o' e => h.env _ o' e)
  | aload i he => exact h.setVar _ (fun o' e => h.read (h.env _ _ he) e)
  | astore i he => exact h.setCell _ _ (fun o' e => h.env _ o' e)
  | unknown => exact (h.setVar _ (fun o e => by cases e; trivial)).bump _
  | @call ret a args _ h' hh =>
    have h1 : HInv ({ s with heap := h' }.bump a) := by
      refine ⟨fun x o e => (h.env x o e).bump a, fun o c o' e => ?_⟩
      change h' o c = some o' at e
      show h' o c = _ ∨ _
      rcases hh o c with e1 | ⟨_, k, _, e1⟩
      · rw [e1] at e ⊢
        exact (h.heap o c o' e).imp id (fun h2 => h2.bump a)
      · rw [e1] at e; cases e
        right
        show s.cnt a < fupd s.cnt a (s.cnt a + 1) a
        rw [fupd_same]; omega
    cases ret with
    | none => exact h1
    | some x =>
      have h2 := h1.setVar x (v := some (.sym (.fresh a (s.cnt a)) [])) (fun o e => by
        cases e; trivial)
      exact h2.congr rfl rfl rfl

/-- Each strict execution keeps the invariant. -/
theorem ExecS.hinv {src : Nat → Obj × Cell} {p : Prog} {s s' : CState}
    (hx : ExecS src p s s') (h : HInv s) : HInv s' := by
  induction hx with
  | skip => exact h
  | stmt hs => exact hs.hinv h
  | seq _ _ ih1 ih2 => exact ih2 (ih1 h)
  | choiceL _ ih => exact ih h
  | choiceR _ ih => exact ih h
  | loopZero => exact h
  | loopMore _ _ ih1 ih2 => exact ih2 (ih1 h)

/-- The new objects of a call are not created before the call. -/
theorem not_created_new (st : CState) (s k : Nat) (p : List Cell) :
    ¬ Created st (.sym (.havoc s (st.cnt s) k) p) := fun h => Nat.lt_irrefl _ h

/-- Strict A2, freshness: in each state of a strict execution from a frame entry, no variable
holds a new havoc object of the next call of site `s`, and no written cell holds one. -/
theorem fresh_at_call {src : Nat → Obj × Cell} {fr : Frame} {p : Prog} {st : CState}
    (hx : ExecS src p (CState.init fr) st) (s k : Nat) (q : List Cell) :
    (∀ x, st.env x ≠ some (.sym (.havoc s (st.cnt s) k) q)) ∧
      ∀ o c, st.heap o c ≠ cdefault o c →
        st.heap o c ≠ some (.sym (.havoc s (st.cnt s) k) q) := by
  have h := hx.hinv (hinv_init fr)
  refine ⟨fun x e => not_created_new st s k q (h.env x _ e), fun o c hd e => ?_⟩
  rcases h.heap o c _ e with h1 | h1
  · exact hd h1
  · exact not_created_new st s k q h1

/-- A default content is never the head object of a base. -/
theorem cdefault_ne_head (o : Obj) (c : Cell) (b : Base) : cdefault o c ≠ some (.sym b []) := by
  cases o with
  | alloc _ _ => intro h; cases h
  | sym b' p =>
    intro h
    simp only [cdefault, Option.some.injEq, Obj.sym.injEq] at h
    have := congrArg List.length h.2
    simp at this

/-- Strict A2, freshness of the head: in each state of a strict execution from a frame entry,
no variable and no cell holds the head object that the next call of site `s` writes. -/
theorem fresh_head {src : Nat → Obj × Cell} {fr : Frame} {p : Prog} {st : CState}
    (hx : ExecS src p (CState.init fr) st) (s k : Nat) :
    (∀ x, st.env x ≠ some (.sym (.havoc s (st.cnt s) k) [])) ∧
      ∀ o c, st.heap o c ≠ some (.sym (.havoc s (st.cnt s) k) []) := by
  obtain ⟨h1, h2⟩ := fresh_at_call hx s k []
  refine ⟨h1, fun o c e => ?_⟩
  by_cases hd : st.heap o c = cdefault o c
  · rw [hd] at e; exact cdefault_ne_head o c _ e
  · exact h2 o c hd e

end DirectedAlias.Sound.Havoc
