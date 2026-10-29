import DirectedAlias.Sound.Boundary

/-!
# Renaming of array indices

A swap `swp a b` exchanges two array indices. It renames cells, objects, values, states and
choices. A swap is an involution, so it is a bijection on objects.
The executor `run` commutes with each swap on programs without loops and calls (`arrP`).
The initial state is fixed by each swap.
The witness search (`Search.lean`) uses swaps to move the indices of an execution into a
finite range.
-/

namespace DirectedAlias.Sound.Witness

open DirectedAlias DirectedAlias.Sound

/-! ## The scope of the executor facts -/

/-- A statement that is not a call. -/
def arrS : Stmt → Bool
  | .call _ _ _ => false
  | _ => true

/-- A program without loops and calls. Array accesses are allowed. -/
def arrP : Prog → Bool
  | .skip => true
  | .stmt st => arrS st
  | .seq p q => arrP p && arrP q
  | .choice p q => arrP p && arrP q
  | .loop _ => false

/-! ## The swap -/

/-- Exchange the indices `a` and `b`. -/
def swp (a b i : Nat) : Nat := if i = a then b else if i = b then a else i

/-- A swap is an involution. -/
theorem swp_swp (a b i : Nat) : swp a b (swp a b i) = i := by
  unfold swp
  repeat (first | omega | split)

/-- A swap fixes each index that is not one of the two swapped indices. -/
theorem swp_other {a b i : Nat} (ha : i ≠ a) (hb : i ≠ b) : swp a b i = i := by
  unfold swp; rw [ite_eq_right ha, ite_eq_right hb]

/-- A swap sends `a` to `b`. -/
theorem swp_left (a b : Nat) : swp a b a = b := by unfold swp; rw [ite_eq_left rfl]

/-- Rename the index of a cell. -/
def rC (a b : Nat) : Cell → Cell
  | .fld f => .fld f
  | .elem i => .elem (swp a b i)

/-- Rename the indices in the path of an object. -/
def rO (a b : Nat) : Obj → Obj
  | .sym bs p => .sym bs (p.map (rC a b))
  | .alloc s n => .alloc s n

/-- Rename a value. -/
def rV (a b : Nat) (v : Val) : Val := v.map (rO a b)

/-- Rename a state. The counters do not change. -/
def rS (a b : Nat) (s : CState) : CState where
  env := fun x => rV a b (s.env x)
  heap := fun o c => rV a b (s.heap (rO a b o) (rC a b c))
  cnt := s.cnt

/-- Rename a choice. Only an index choice changes. -/
def rCh (a b : Nat) : Choice → Choice
  | .idx i => .idx (swp a b i)
  | c => c

/-- Cell renaming is an involution. -/
theorem rC_rC (a b : Nat) (c : Cell) : rC a b (rC a b c) = c := by
  cases c with
  | fld f => rfl
  | elem i => simp only [rC, swp_swp]

/-- Path renaming is an involution. -/
theorem rP_rP (a b : Nat) (p : List Cell) : (p.map (rC a b)).map (rC a b) = p := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id p]
  apply List.map_congr_left
  intro c _
  exact rC_rC a b c

/-- Object renaming is an involution. -/
theorem rO_rO (a b : Nat) (o : Obj) : rO a b (rO a b o) = o := by
  cases o with
  | sym bs p => simp only [rO, rP_rP]
  | alloc s n => rfl

/-- Value renaming is an involution. -/
theorem rV_rV (a b : Nat) (v : Val) : rV a b (rV a b v) = v := by
  cases v with
  | none => rfl
  | some o => simp only [rV, Option.map_some, rO_rO]

/-- Cell renaming keeps the abstraction. -/
theorem rC_abs (a b : Nat) (c : Cell) : (rC a b c).abs = c.abs := by
  cases c <;> rfl

/-- Path renaming keeps the abstraction. -/
theorem rP_abs (a b : Nat) (p : List Cell) : (p.map (rC a b)).map Cell.abs = p.map Cell.abs := by
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  exact rC_abs a b c

/-- Object renaming is injective (one direction of the involution). -/
theorem rO_eq_iff {a b : Nat} {o o' : Obj} : rO a b o = o' ↔ o = rO a b o' := by
  constructor
  · intro h; rw [← h, rO_rO]
  · intro h; rw [h, rO_rO]

/-- Cell renaming is injective (one direction of the involution). -/
theorem rC_eq_iff {a b : Nat} {c c' : Cell} : rC a b c = c' ↔ c = rC a b c' := by
  constructor
  · intro h; rw [← h, rC_rC]
  · intro h; rw [h, rC_rC]

/-! ## Renaming commutes with the state operations -/

/-- Renaming commutes with the default heap content. -/
theorem rV_cdefault (a b : Nat) (o : Obj) (c : Cell) :
    rV a b (cdefault (rO a b o) (rC a b c)) = cdefault o c := by
  cases o with
  | sym bs p =>
    simp only [rO, cdefault, rV, Option.map_some, List.map_append, List.map_cons, List.map_nil,
      rP_rP, rC_rC]
  | alloc s n => rfl

/-- Each swap fixes the entry state. -/
theorem rS_init (a b : Nat) (fr : Frame) : rS a b (CState.init fr) = CState.init fr := by
  simp only [rS, CState.init]
  congr
  · funext x
    cases fr.root? x with
    | none => rfl
    | some r => rfl
  · funext o c
    exact rV_cdefault a b o c

/-- Renaming commutes with a variable update. -/
theorem rS_setVar (a b : Nat) (s : CState) (x : Var) (v : Val) :
    rS a b (s.setVar x v) = (rS a b s).setVar x (rV a b v) := by
  simp only [rS, CState.setVar]
  congr
  funext x'
  unfold fupd
  split <;> rfl

/-- Renaming commutes with a cell update. -/
theorem rS_setCell (a b : Nat) (s : CState) (o : Obj) (c : Cell) (v : Val) :
    rS a b (s.setCell o c v) = (rS a b s).setCell (rO a b o) (rC a b c) (rV a b v) := by
  simp only [rS, CState.setCell]
  congr
  funext o' c'
  unfold fupd2
  by_cases h : o' = rO a b o ∧ c' = rC a b c
  · rw [ite_eq_left h, ite_eq_left ⟨rO_eq_iff.mpr h.1, rC_eq_iff.mpr h.2⟩]
  · have h' : ¬ (rO a b o' = o ∧ rC a b c' = c) :=
      fun ⟨h1, h2⟩ => h ⟨rO_eq_iff.mp h1, rC_eq_iff.mp h2⟩
    rw [ite_eq_right h, ite_eq_right h']

/-- Renaming commutes with a counter bump. -/
theorem rS_bump (a b : Nat) (s : CState) (st : Site) : rS a b (s.bump st) = (rS a b s).bump st :=
  rfl

/-- The renamed heap at renamed arguments is the renamed content. -/
theorem rS_heap (a b : Nat) (s : CState) (o : Obj) (c : Cell) :
    (rS a b s).heap (rO a b o) (rC a b c) = rV a b (s.heap o c) := by
  simp only [rS, rO_rO, rC_rC]

/-- Renaming commutes with a path walk. -/
theorem readPath_r (a b : Nat) (s : CState) :
    ∀ (o : Obj) (p : List Cell),
      readPath (rS a b s).heap (rO a b o) (p.map (rC a b)) = rV a b (readPath s.heap o p)
  | o, [] => rfl
  | o, c :: cs => by
    simp only [List.map_cons, readPath, rS_heap]
    cases s.heap o c with
    | none => rfl
    | some o' =>
      simp only [rV, Option.map_some, Option.bind_some]
      exact readPath_r a b s o' cs

/-- Renaming commutes with the evaluation of an access path. -/
theorem evalPath_r (a b : Nat) (s : CState) (x : Var) (p : List Cell) :
    evalPath (rS a b s) x (p.map (rC a b)) = rV a b (evalPath s x p) := by
  unfold evalPath
  show (rV a b (s.env x)).bind _ = _
  cases s.env x with
  | none => rfl
  | some o =>
    simp only [rV, Option.map_some, Option.bind_some]
    exact readPath_r a b s o p

/-! ## Renaming commutes with the executor -/

/-- A statement run commutes with renaming (statements that are not calls). -/
theorem runStmt_r (a b : Nat) {st : Stmt} (hs : arrS st = true) {cs cs' : List Choice}
    {s u : CState} (h : runStmt st cs s = some (u, cs')) :
    runStmt st (cs.map (rCh a b)) (rS a b s) = some (rS a b u, cs'.map (rCh a b)) := by
  cases st with
  | new x t =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [rS_bump, rS_setVar]; rfl, rfl⟩
  | null x =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [rS_setVar]; rfl, rfl⟩
  | copy x y =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [rS_setVar]; rfl, rfl⟩
  | unknown x t =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [rS_bump, rS_setVar]; rfl, rfl⟩
  | load x y f =>
    simp only [runStmt] at h ⊢
    cases he : s.env y with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have he' : (rS a b s).env y = some (rO a b o) := by
        show rV a b (s.env y) = _; rw [he]; rfl
      rw [he']
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [rS_setVar]
      have := rS_heap a b s o (.fld f)
      simp only [rC] at this
      rw [this]
  | store x f y =>
    simp only [runStmt] at h ⊢
    cases he : s.env x with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have he' : (rS a b s).env x = some (rO a b o) := by
        show rV a b (s.env x) = _; rw [he]; rfl
      rw [he']
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [rS_setCell]
      rfl
  | aload x y =>
    match cs, h with
    | .idx i :: cs, h =>
      simp only [runStmt] at h
      simp only [List.map_cons, rCh, runStmt]
      cases he : s.env y with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have he' : (rS a b s).env y = some (rO a b o) := by
          show rV a b (s.env y) = _; rw [he]; rfl
        rw [he']
        simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        rw [rS_setVar]
        have := rS_heap a b s o (.elem i)
        simp only [rC] at this
        rw [this]
  | astore x y =>
    match cs, h with
    | .idx i :: cs, h =>
      simp only [runStmt] at h
      simp only [List.map_cons, rCh, runStmt]
      cases he : s.env x with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have he' : (rS a b s).env x = some (rO a b o) := by
          show rV a b (s.env x) = _; rw [he]; rfl
        rw [he']
        simp only [Option.some.injEq, Prod.mk.injEq, and_true]
        rw [rS_setCell]
        rfl
  | call _ _ _ => simp [arrS] at hs

/-- A run of a program without loops and calls commutes with renaming. -/
theorem run_r (a b : Nat) : ∀ {p : Prog}, arrP p = true → ∀ {cs cs' : List Choice} {s u : CState},
    run p cs s = some (u, cs') →
      run p (cs.map (rCh a b)) (rS a b s) = some (rS a b u, cs'.map (rCh a b))
  | .skip, _, cs, cs', s, u, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | .stmt st, hp, cs, cs', s, u, h => by
    simp only [run] at h ⊢
    exact runStmt_r a b hp h
  | .seq p q, hp, cs, cs', s, u, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h ⊢
    cases hr : run p cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      rw [run_r a b hp.1 hr]
      exact run_r a b hp.2 h
  | .choice p q, hp, .left :: cs, cs', s, u, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h
    simp only [List.map_cons, rCh, run]
    exact run_r a b hp.1 h
  | .choice p q, hp, .right :: cs, cs', s, u, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h
    simp only [List.map_cons, rCh, run]
    exact run_r a b hp.2 h
  | .loop _, hp, _, _, _, _, _ => by simp [arrP] at hp

end DirectedAlias.Sound.Witness
