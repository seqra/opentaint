import DirectedAlias.Sound.Witness.Compact
import DirectedAlias.Sound.StoreScope

/-!
# Executable witness search

`crossWitness` is a computable search for a cross-execution alias. It gives a `Witness`:
two choice lists for the executor `run` and two concrete access paths.
It enumerates a finite set of candidates:
* the choice lists of the program (`choicesOfN`), with array indices below a bound `N`;
* the concrete paths that abstract to the query paths, with array indices below `N`.
The bound `N = 2 * arrN p + elemN px + elemN py` depends only on the query.

Theorems:
* `crossWitness_sound`: a result of the search is a cross-execution alias (`CAliasX`).
  This holds for each program.
* `crossWitness_complete`: for a program without loops and calls (`arrP`), each cross-execution
  alias gives a result. The proof renames the array indices of the two executions and the two
  paths into the range `[0, N)` (`compact`), and shows that the renamed candidate is in the
  enumeration (`run_split`).
* `witness_core`, `witness_store`: in the completeness scopes, `mayProg = true` makes the search
  succeed. `coreWitness` and `storeWitness` give the witness as a value.
* `oneWitness`: the same search for a one-execution alias (`CAlias`).
-/

namespace DirectedAlias.Sound.Witness

open DirectedAlias DirectedAlias.Sound

/-! ## Index lists -/

/-- The index of an index choice. -/
def chIdx : Choice → List Nat
  | .idx i => [i]
  | _ => []

/-- The array indices of a choice list. -/
def idxs : List Choice → List Nat
  | [] => []
  | c :: r => chIdx c ++ idxs r

/-- The index of an array cell. -/
def cellIdx : Cell → List Nat
  | .elem i => [i]
  | .fld _ => []

/-- The array indices of a concrete path. -/
def pidx : List Cell → List Nat
  | [] => []
  | c :: r => cellIdx c ++ pidx r

/-- The number of array cells of an abstract path. -/
def elemN : List ACell → Nat
  | [] => 0
  | .elem :: q => elemN q + 1
  | .fld _ :: q => elemN q

/-- `idxs` distributes over append. -/
theorem idxs_append : ∀ (a b : List Choice), idxs (a ++ b) = idxs a ++ idxs b
  | [], _ => rfl
  | c :: a, b => by simp only [List.cons_append, idxs, idxs_append a b, List.append_assoc]

/-- A swap renames the indices of a choice list. -/
theorem idxs_r (a b : Nat) : ∀ (cs : List Choice), idxs (cs.map (rCh a b)) = (idxs cs).map (swp a b)
  | [] => rfl
  | c :: cs => by
    simp only [List.map_cons, idxs, List.map_append, idxs_r a b cs]
    cases c <;> rfl

/-- A swap renames the indices of a path. -/
theorem pidx_r (a b : Nat) : ∀ (p : List Cell), pidx (p.map (rC a b)) = (pidx p).map (swp a b)
  | [] => rfl
  | c :: p => by
    simp only [List.map_cons, pidx, List.map_append, pidx_r a b p]
    cases c <;> rfl

/-- A concrete path has one index for each array cell of its abstraction. -/
theorem pidx_length : ∀ (p : List Cell), (pidx p).length = elemN (p.map Cell.abs)
  | [] => rfl
  | .fld f :: p => by
    simp only [pidx, cellIdx, List.nil_append, List.map_cons, Cell.abs, elemN, pidx_length p]
  | .elem i :: p => by
    simp only [pidx, cellIdx, List.map_cons, Cell.abs, elemN, List.length_append,
      List.length_singleton, pidx_length p]
    omega

/-! ## The enumeration of choice lists -/

/-- The number of array statements of a statement. -/
def arrNS : Stmt → Nat
  | .aload _ _ => 1
  | .astore _ _ => 1
  | _ => 0

/-- The number of array statements of a program. -/
def arrN : Prog → Nat
  | .skip => 0
  | .stmt st => arrNS st
  | .seq p q => arrN p + arrN q
  | .choice p q => arrN p + arrN q
  | .loop p => arrN p

/-- The index choices below `N`. -/
def idxChoices (N : Nat) : List (List Choice) := (List.range N).map (fun i => [Choice.idx i])

/-- The choice lists of one statement, with indices below `N`. A call has none. -/
def choicesS (N : Nat) : Stmt → List (List Choice)
  | .aload _ _ => idxChoices N
  | .astore _ _ => idxChoices N
  | .call _ _ _ => []
  | _ => [[]]

/-- The choice lists of a program without loops and calls, with indices below `N`. -/
def choicesOfN (N : Nat) : Prog → List (List Choice)
  | .skip => [[]]
  | .stmt st => choicesS N st
  | .seq p q => (choicesOfN N p).flatMap (fun c1 => (choicesOfN N q).map (c1 ++ ·))
  | .choice p q =>
    (choicesOfN N p).map (Choice.left :: ·) ++ (choicesOfN N q).map (Choice.right :: ·)
  | .loop _ => []

/-- The property of a used choice prefix: few indices, and in the enumeration for each bound
above its indices. -/
def Listed (N0 : Nat) (cs : List Choice) (en : Nat → List (List Choice)) : Prop :=
  (idxs cs).length ≤ N0 ∧ ∀ N, (∀ i ∈ idxs cs, i < N) → cs ∈ en N

/-- A statement run uses a prefix of the choices, and the prefix is listed. -/
theorem runStmt_split {st : Stmt} (hs : arrS st = true) {l l' : List Choice} {s t : CState}
    (h : runStmt st l s = some (t, l')) :
    ∃ c, l = c ++ l' ∧ Listed (arrNS st) c (fun N => choicesS N st) := by
  have nil_ok : ∀ st', (∀ N, choicesS N st' = [[]]) → arrNS st' = 0 →
      Listed (arrNS st') [] (fun N => choicesS N st') := by
    intro st' h1 _
    exact ⟨Nat.zero_le _, fun N _ => by show [] ∈ choicesS N st'; rw [h1 N]; exact List.mem_singleton.mpr rfl⟩
  cases st with
  | new x a =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | null x =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | copy x y =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | unknown x a =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | load x y f =>
    simp only [runStmt] at h
    cases he : s.env y with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | store x f y =>
    simp only [runStmt] at h
    cases he : s.env x with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨[], rfl, nil_ok _ (fun _ => rfl) rfl⟩
  | aload x y =>
    match l, h with
    | .idx i :: l0, h =>
      simp only [runStmt] at h
      have hl : l0 = l' := by
        cases he : s.env y with
        | none => rw [he] at h; cases h
        | some o =>
          rw [he] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2
      subst hl
      refine ⟨[.idx i], rfl, Nat.le_refl _, fun N hN => ?_⟩
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr (hN i (List.mem_singleton.mpr rfl)), rfl⟩
  | astore x y =>
    match l, h with
    | .idx i :: l0, h =>
      simp only [runStmt] at h
      have hl : l0 = l' := by
        cases he : s.env x with
        | none => rw [he] at h; cases h
        | some o =>
          rw [he] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact h.2
      subst hl
      refine ⟨[.idx i], rfl, Nat.le_refl _, fun N hN => ?_⟩
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr (hN i (List.mem_singleton.mpr rfl)), rfl⟩
  | call _ _ _ => simp [arrS] at hs

/-- A run of a program without loops and calls uses a prefix of the choices, and the prefix is
in the enumeration for each bound above its indices. -/
theorem run_split : ∀ {p : Prog}, arrP p = true → ∀ {l l' : List Choice} {s t : CState},
    run p l s = some (t, l') → ∃ c, l = c ++ l' ∧ Listed (arrN p) c (fun N => choicesOfN N p)
  | .skip, _, l, l', s, t, h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], rfl, Nat.le_refl _, fun _ _ => List.mem_singleton.mpr rfl⟩
  | .stmt st, hp, l, l', s, t, h => by
    simp only [run] at h
    exact runStmt_split hp h
  | .seq p q, hp, l, l', s, u, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h
    cases hr : run p l s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, l1⟩ := r
      rw [hr] at h
      obtain ⟨c1, e1, n1, m1⟩ := run_split hp.1 hr
      obtain ⟨c2, e2, n2, m2⟩ := run_split hp.2 h
      refine ⟨c1 ++ c2, by rw [e1, e2, List.append_assoc], ?_, fun N hN => ?_⟩
      · simp only [arrN, idxs_append, List.length_append]; omega
      · have h1 : ∀ i ∈ idxs c1, i < N :=
          fun i hi => hN i (by rw [idxs_append]; exact List.mem_append_left _ hi)
        have h2 : ∀ i ∈ idxs c2, i < N :=
          fun i hi => hN i (by rw [idxs_append]; exact List.mem_append_right _ hi)
        exact List.mem_flatMap.mpr ⟨c1, m1 N h1, List.mem_map.mpr ⟨c2, m2 N h2, rfl⟩⟩
  | .choice p q, hp, .left :: l, l', s, t, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h
    obtain ⟨c, e, n, m⟩ := run_split hp.1 h
    refine ⟨.left :: c, by rw [e]; rfl, ?_, fun N hN => ?_⟩
    · simp only [idxs, chIdx, List.nil_append, arrN]; omega
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨c, m N hN, rfl⟩)
  | .choice p q, hp, .right :: l, l', s, t, h => by
    simp only [arrP, Bool.and_eq_true] at hp
    simp only [run] at h
    obtain ⟨c, e, n, m⟩ := run_split hp.2 h
    refine ⟨.right :: c, by rw [e]; rfl, ?_, fun N hN => ?_⟩
    · simp only [idxs, chIdx, List.nil_append, arrN]; omega
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨c, m N hN, rfl⟩)
  | .loop _, hp, _, _, _, _, _ => by simp [arrP] at hp

/-- A complete run of a choice list: the list is listed. -/
theorem run_listed {p : Prog} (hp : arrP p = true) {cs : List Choice} {s u : CState}
    (h : run p cs s = some (u, [])) : Listed (arrN p) cs (fun N => choicesOfN N p) := by
  obtain ⟨c, e, hl⟩ := run_split hp h
  rw [List.append_nil] at e
  exact e ▸ hl

/-- A statement step without a call is a run of a choice list of at most one index. -/
theorem runStmt_completeA {st : Stmt} {s u : CState} (hp : arrS st = true) (h : SStep st s u) :
    ∃ c, ∀ r, runStmt st (c ++ r) s = some (u, r) := by
  cases h with
  | new => exact ⟨[], fun _ => rfl⟩
  | null => exact ⟨[], fun _ => rfl⟩
  | copy => exact ⟨[], fun _ => rfl⟩
  | load he => exact ⟨[], fun _ => by simp only [List.nil_append, runStmt, he]⟩
  | store he => exact ⟨[], fun _ => by simp only [List.nil_append, runStmt, he]⟩
  | unknown => exact ⟨[], fun _ => rfl⟩
  | aload i he => exact ⟨[.idx i], fun _ => by simp only [List.cons_append, List.nil_append,
      runStmt, he]⟩
  | astore i he => exact ⟨[.idx i], fun _ => by simp only [List.cons_append, List.nil_append,
      runStmt, he]⟩
  | call _ => simp [arrS] at hp

/-- Each execution of a program without loops and calls is a run of some choice list. -/
theorem run_completeA {p : Prog} {s u : CState} (h : Exec p s u) :
    arrP p = true → ∀ r, ∃ cs, run p (cs ++ r) s = some (u, r) := by
  induction h with
  | skip => intro _ r; exact ⟨[], rfl⟩
  | stmt hs =>
    intro hp r
    obtain ⟨c, hc⟩ := runStmt_completeA hp hs
    exact ⟨c, hc r⟩
  | seq _ _ ih1 ih2 =>
    intro hp r
    simp only [arrP, Bool.and_eq_true] at hp
    obtain ⟨c2, hr2⟩ := ih2 hp.2 r
    obtain ⟨c1, hr1⟩ := ih1 hp.1 (c2 ++ r)
    exact ⟨c1 ++ c2, by simp only [run, List.append_assoc, hr1, hr2]⟩
  | choiceL _ ih =>
    intro hp r
    simp only [arrP, Bool.and_eq_true] at hp
    obtain ⟨c, hr⟩ := ih hp.1 r
    exact ⟨Choice.left :: c, hr⟩
  | choiceR _ ih =>
    intro hp r
    simp only [arrP, Bool.and_eq_true] at hp
    obtain ⟨c, hr⟩ := ih hp.2 r
    exact ⟨Choice.right :: c, hr⟩
  | loopZero => intro hp; simp [arrP] at hp
  | loopMore _ _ _ _ => intro hp; simp [arrP] at hp

/-! ## The enumeration of concrete paths -/

/-- The concrete paths that abstract to `q`, with array indices below `N`. -/
def pathsOf (N : Nat) : List ACell → List (List Cell)
  | [] => [[]]
  | .fld f :: q => (pathsOf N q).map (Cell.fld f :: ·)
  | .elem :: q => (List.range N).flatMap (fun i => (pathsOf N q).map (Cell.elem i :: ·))

/-- Each enumerated path abstracts to the abstract path. -/
theorem pathsOf_abs (N : Nat) : ∀ (q : List ACell) (p : List Cell), p ∈ pathsOf N q →
    p.map Cell.abs = q
  | [], p, h => by rw [List.mem_singleton.mp h]; rfl
  | .fld f :: q, p, h => by
    obtain ⟨p', h', rfl⟩ := List.mem_map.mp h
    simp only [List.map_cons, Cell.abs, pathsOf_abs N q p' h']
  | .elem :: q, p, h => by
    obtain ⟨i, _, h1⟩ := List.mem_flatMap.mp h
    obtain ⟨p', h', rfl⟩ := List.mem_map.mp h1
    simp only [List.map_cons, Cell.abs, pathsOf_abs N q p' h']

/-- Each concrete path with indices below `N` is enumerated. -/
theorem mem_pathsOf (N : Nat) : ∀ (p : List Cell), (∀ i ∈ pidx p, i < N) →
    p ∈ pathsOf N (p.map Cell.abs)
  | [], _ => List.mem_singleton.mpr rfl
  | .fld f :: p, h => by
    simp only [List.map_cons, Cell.abs, pathsOf]
    exact List.mem_map.mpr ⟨p, mem_pathsOf N p (fun i hi => h i (by
      simp only [pidx, cellIdx, List.nil_append]; exact hi)), rfl⟩
  | .elem i :: p, h => by
    simp only [List.map_cons, Cell.abs, pathsOf]
    have hi : i < N := h i (by simp only [pidx, cellIdx]; exact List.mem_cons_self)
    refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨p, ?_, rfl⟩⟩
    exact mem_pathsOf N p (fun j hj => h j (by
      simp only [pidx, cellIdx]; exact List.mem_cons_of_mem _ hj))

/-! ## The cross-execution witness -/

/-- A cross-execution witness: two choice lists for `run` and two concrete paths. -/
structure Witness where
  /-- The choices of the first execution. -/
  c1 : List Choice
  /-- The choices of the second execution. -/
  c2 : List Choice
  /-- The concrete path of the first variable. -/
  cx : List Cell
  /-- The concrete path of the second variable. -/
  cy : List Cell
  deriving DecidableEq, Repr

/-- Executable check of a witness: both runs succeed, and `x.cx` at the end of the first run
is the same object as `y.cy` at the end of the second run. -/
def checkW (fr : Frame) (p : Prog) (x y : Var) (w : Witness) : Bool :=
  match runFrom fr p w.c1, runFrom fr p w.c2 with
  | some s1, some s2 => Boundary.sameB (evalPath s1 x w.cx) (evalPath s2 y w.cy)
  | _, _ => false

/-- The index bound of the search. It depends only on the program and the query paths. -/
def bound (p : Prog) (px py : List ACell) : Nat := 2 * arrN p + elemN px + elemN py

/-- The finite candidate list. -/
def candidates (N : Nat) (p : Prog) (px py : List ACell) : List Witness :=
  (pathsOf N px).flatMap fun cx => (pathsOf N py).flatMap fun cy =>
    (choicesOfN N p).flatMap fun c1 => (choicesOfN N p).map fun c2 => ⟨c1, c2, cx, cy⟩

/-- The executable cross-execution witness search. -/
def crossWitness (fr : Frame) (p : Prog) (x : Var) (px : List ACell) (y : Var)
    (py : List ACell) : Option Witness :=
  (candidates (bound p px py) p px py).find? (checkW fr p x y)

/-- `sameB` is true only for the same object. -/
theorem sameB_true {v w : Val} (h : Boundary.sameB v w = true) : ∃ o, v = some o ∧ w = some o := by
  cases v with
  | none => simp only [Boundary.sameB] at h; cases h
  | some o => exact ⟨o, rfl, of_decide_eq_true h⟩

/-- `sameB` is true for the same object. -/
theorem sameB_of {o : Obj} {v w : Val} (hv : v = some o) (hw : w = some o) :
    Boundary.sameB v w = true := by
  subst hv; subst hw; exact decide_eq_true rfl

/-- A successful check proves a cross-execution alias. -/
theorem checkW_sound {fr : Frame} {p : Prog} {x y : Var} {w : Witness}
    (h : checkW fr p x y w = true) : CAliasX fr p x w.cx y w.cy := by
  unfold checkW at h
  cases h1 : runFrom fr p w.c1 with
  | none =>
    cases h2 : runFrom fr p w.c2 with
    | none => rw [h1, h2] at h; cases h
    | some s2 => rw [h1, h2] at h; cases h
  | some s1 =>
    cases h2 : runFrom fr p w.c2 with
    | none => rw [h1, h2] at h; cases h
    | some s2 =>
      rw [h1, h2] at h
      obtain ⟨o, e1, e2⟩ := sameB_true h
      exact ⟨s1, s2, o, runFrom_sound h1, runFrom_sound h2, e1, e2⟩

/-- A candidate has paths that abstract to the query paths. -/
theorem candidates_abs {N : Nat} {p : Prog} {px py : List ACell} {w : Witness}
    (h : w ∈ candidates N p px py) : w.cx.map Cell.abs = px ∧ w.cy.map Cell.abs = py := by
  obtain ⟨cx, hx, h⟩ := List.mem_flatMap.mp h
  obtain ⟨cy, hy, h⟩ := List.mem_flatMap.mp h
  obtain ⟨c1, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨c2, _, rfl⟩ := List.mem_map.mp h
  exact ⟨pathsOf_abs N px cx hx, pathsOf_abs N py cy hy⟩

/-- Witness soundness: a result of the search is a cross-execution alias of concrete paths that
abstract to the query paths. This holds for each program. -/
theorem crossWitness_sound {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell} {w : Witness}
    (h : crossWitness fr p x px y py = some w) :
    w.cx.map Cell.abs = px ∧ w.cy.map Cell.abs = py ∧ CAliasX fr p x w.cx y w.cy := by
  have hm := candidates_abs (List.mem_of_find?_eq_some h)
  exact ⟨hm.1, hm.2, checkW_sound (List.find?_some h)⟩

/-! ## Completeness of the search -/

/-- A candidate that runs and aliases (the `Prop` form of a successful check). -/
def Good (fr : Frame) (p : Prog) (x y : Var) (px py : List ACell) (w : Witness) : Prop :=
  ∃ s1 s2 o, run p w.c1 (CState.init fr) = some (s1, []) ∧
    run p w.c2 (CState.init fr) = some (s2, []) ∧
    evalPath s1 x w.cx = some o ∧ evalPath s2 y w.cy = some o ∧
    w.cx.map Cell.abs = px ∧ w.cy.map Cell.abs = py

/-- All indices of a witness. -/
def wU (w : Witness) : List Nat := idxs w.c1 ++ idxs w.c2 ++ pidx w.cx ++ pidx w.cy

/-- Rename a witness with a swap. -/
def wR (a b : Nat) (w : Witness) : Witness :=
  ⟨w.c1.map (rCh a b), w.c2.map (rCh a b), w.cx.map (rC a b), w.cy.map (rC a b)⟩

/-- A swap renames the indices of a witness. -/
theorem wU_R (a b : Nat) (w : Witness) : wU (wR a b w) = (wU w).map (swp a b) := by
  simp only [wU, wR, idxs_r, pidx_r, List.map_append]

/-- A swap keeps a good witness good. -/
theorem good_R {fr : Frame} {p : Prog} (hp : arrP p = true) {x y : Var} {px py : List ACell}
    (a b : Nat) (w : Witness) (h : Good fr p x y px py w) : Good fr p x y px py (wR a b w) := by
  obtain ⟨s1, s2, o, r1, r2, e1, e2, hx, hy⟩ := h
  have r1' := run_r a b hp r1
  have r2' := run_r a b hp r2
  rw [rS_init] at r1' r2'
  refine ⟨rS a b s1, rS a b s2, rO a b o, r1', r2', ?_, ?_, ?_, ?_⟩
  · show evalPath _ x (w.cx.map (rC a b)) = _
    rw [evalPath_r, e1]; rfl
  · show evalPath _ y (w.cy.map (rC a b)) = _
    rw [evalPath_r, e2]; rfl
  · show (w.cx.map (rC a b)).map Cell.abs = px
    rw [rP_abs]; exact hx
  · show (w.cy.map (rC a b)).map Cell.abs = py
    rw [rP_abs]; exact hy

/-- A good witness with indices below the bound is a candidate that passes the check. -/
theorem good_found {fr : Frame} {p : Prog} (hp : arrP p = true) {x y : Var} {px py : List ACell}
    {N : Nat} {w : Witness} (h : Good fr p x y px py w) (hN : ∀ i ∈ wU w, i < N) :
    w ∈ candidates N p px py ∧ checkW fr p x y w = true := by
  obtain ⟨s1, s2, o, r1, r2, e1, e2, hx, hy⟩ := h
  have b1 : ∀ i ∈ idxs w.c1, i < N := fun i hi => hN i (by
    simp only [wU, List.mem_append]; exact Or.inl (Or.inl (Or.inl hi)))
  have b2 : ∀ i ∈ idxs w.c2, i < N := fun i hi => hN i (by
    simp only [wU, List.mem_append]; exact Or.inl (Or.inl (Or.inr hi)))
  have b3 : ∀ i ∈ pidx w.cx, i < N := fun i hi => hN i (by
    simp only [wU, List.mem_append]; exact Or.inl (Or.inr hi))
  have b4 : ∀ i ∈ pidx w.cy, i < N := fun i hi => hN i (by
    simp only [wU, List.mem_append]; exact Or.inr hi)
  have m1 := (run_listed hp r1).2 N b1
  have m2 := (run_listed hp r2).2 N b2
  have m3 := mem_pathsOf N w.cx b3
  have m4 := mem_pathsOf N w.cy b4
  rw [hx] at m3
  rw [hy] at m4
  refine ⟨?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨w.cx, m3, List.mem_flatMap.mpr ⟨w.cy, m4,
      List.mem_flatMap.mpr ⟨w.c1, m1, List.mem_map.mpr ⟨w.c2, m2, rfl⟩⟩⟩⟩
  · have f1 : runFrom fr p w.c1 = some s1 := by simp only [runFrom, r1, Option.map_some]
    have f2 : runFrom fr p w.c2 = some s2 := by simp only [runFrom, r2, Option.map_some]
    simp only [checkW, f1, f2]
    exact sameB_of e1 e2

/-- Witness completeness: for a program without loops and calls, each cross-execution alias of
concrete paths that abstract to the query paths makes the search succeed. -/
theorem crossWitness_complete {fr : Frame} {p : Prog} (hp : arrP p = true) {x y : Var}
    {px py : List ACell} {cx cy : List Cell} (hx : cx.map Cell.abs = px)
    (hy : cy.map Cell.abs = py) (h : CAliasX fr p x cx y cy) :
    (crossWitness fr p x px y py).isSome = true := by
  obtain ⟨s1, s2, o, h1, h2, e1, e2⟩ := h
  obtain ⟨c1, r1⟩ := run_completeA h1 hp []
  obtain ⟨c2, r2⟩ := run_completeA h2 hp []
  rw [List.append_nil] at r1 r2
  have hg : Good fr p x y px py ⟨c1, c2, cx, cy⟩ := ⟨s1, s2, o, r1, r2, e1, e2, hx, hy⟩
  have hlen : (wU ⟨c1, c2, cx, cy⟩).length ≤ bound p px py := by
    have l1 := (run_listed hp r1).1
    have l2 := (run_listed hp r2).1
    have l3 := pidx_length cx
    have l4 := pidx_length cy
    rw [hx] at l3
    rw [hy] at l4
    simp only [wU, List.length_append, bound]
    omega
  obtain ⟨w', hg', _, hlt⟩ := compact wU wR wU_R (Good fr p x y px py)
    (fun a b d hd => good_R hp a b d hd) _ _ (Nat.le_refl _) hg
  obtain ⟨hm, hc⟩ := good_found hp hg' (fun i hi => Nat.lt_of_lt_of_le (hlt i hi) hlen)
  exact List.find?_isSome.mpr ⟨w', hm, hc⟩

/-- For a program without loops and calls, the search fails exactly when no cross-execution
alias exists. So `crossWitness` decides `NoCrossAlias` (also with arrays). -/
theorem crossWitness_none_iff {fr : Frame} {p : Prog} (hp : arrP p = true) {x y : Var}
    {px py : List ACell} :
    crossWitness fr p x px y py = none ↔ Boundary.NoCrossAlias fr p x px y py := by
  constructor
  · intro hn ⟨cx, cy, hx, hy, h⟩
    have := crossWitness_complete hp hx hy h
    rw [hn] at this
    cases this
  · intro hno
    cases hc : crossWitness fr p x px y py with
    | none => rfl
    | some w =>
      obtain ⟨hx, hy, h⟩ := crossWitness_sound hc
      exact absurd ⟨w.cx, w.cy, hx, hy, h⟩ hno

/-! ## The completeness scopes give witnesses -/

/-- A core program has no loop and no call. -/
theorem arr_of_core : ∀ {p : Prog}, coreP p = true → arrP p = true
  | .skip, _ => rfl
  | .stmt st, h => by
    cases st with
    | call _ _ _ => simp [coreP, coreS] at h
    | _ => rfl
  | .seq p q, h => by
    simp only [coreP, Bool.and_eq_true] at h
    show (arrP p && arrP q) = true
    rw [arr_of_core h.1, arr_of_core h.2]; rfl
  | .choice p q, h => by
    simp only [coreP, Bool.and_eq_true] at h
    show (arrP p && arrP q) = true
    rw [arr_of_core h.1, arr_of_core h.2]; rfl
  | .loop _, h => by simp [coreP] at h

/-- A certified program has no loop and no call. -/
theorem arr_of_bcert {ctx : Ctx} : ∀ {p : Prog} {k k' : Var → NK} {Y : AState},
    bcert ctx p k Y = some k' → arrP p = true
  | .skip, _, _, _, _ => rfl
  | .stmt st, k, k', Y, h => by
    cases st with
    | call r a args =>
      have : bcert ctx (.stmt (.call r a args)) k Y = none := rfl
      rw [this] at h; cases h
    | _ => rfl
  | .seq p q, k, k', Y, h => by
    cases hp : bcert ctx p k Y with
    | none =>
      have : bcert ctx (.seq p q) k Y = none := by simp only [bcert, hp, Option.bind_none]
      rw [this] at h; cases h
    | some k1 =>
      have hq : bcert ctx q k1 (analyze ctx p Y) = some k' := by
        have : bcert ctx (.seq p q) k Y = bcert ctx q k1 (analyze ctx p Y) := by
          simp only [bcert, hp, Option.bind_some]
        rw [← this]; exact h
      show (arrP p && arrP q) = true
      rw [arr_of_bcert hp, arr_of_bcert hq]; rfl
  | .choice p q, k, k', Y, h => by
    cases hp : bcert ctx p k Y with
    | none =>
      have : bcert ctx (.choice p q) k Y = none := by simp only [bcert, hp]
      rw [this] at h; cases h
    | some k1 =>
      cases hq : bcert ctx q k Y with
      | none =>
        have : bcert ctx (.choice p q) k Y = none := by simp only [bcert, hp, hq]
        rw [this] at h; cases h
      | some k2 =>
        show (arrP p && arrP q) = true
        rw [arr_of_bcert hp, arr_of_bcert hq]; rfl
  | .loop _, _, _, _, h => by cases h

/-- A program in the certified store scope has no loop and no call. -/
theorem arr_of_store {K : Nat} {fr : Frame} {p : Prog} {px py : List ACell}
    (h : storeScopeB K fr p px py = true) : arrP p = true := by
  simp only [storeScopeB, Bool.and_eq_true] at h
  obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp h.2
  exact arr_of_bcert hk

/-- In the checkable core scope, a may-alias makes the witness search succeed. -/
theorem witness_core {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : coreScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) :
    (crossWitness fr p x px y py).isSome = true := by
  obtain ⟨cx, cy, hx, hy, h⟩ := ccomplete_coreB K fr p x px y py hs hm
  exact crossWitness_complete (arr_of_core (coreScopeB_sound hs).1) hx hy h

/-- In the certified store scope, a may-alias makes the witness search succeed. -/
theorem witness_store {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : storeScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) :
    (crossWitness fr p x px y py).isSome = true := by
  obtain ⟨cx, cy, hx, hy, h⟩ := ccomplete_store K fr p x px y py hs hm
  exact crossWitness_complete (arr_of_store hs) hx hy h

/-- The witness of a may-alias in the core scope, as a value. It runs `crossWitness`. -/
def coreWitness {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : coreScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) : Witness :=
  (crossWitness fr p x px y py).get (witness_core hs hm)

/-- The witness of a may-alias in the store scope, as a value. It runs `crossWitness`. -/
def storeWitness {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : storeScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) : Witness :=
  (crossWitness fr p x px y py).get (witness_store hs hm)

/-- The core witness is a cross-execution alias of paths that abstract to the query paths. -/
theorem coreWitness_spec {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : coreScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) :
    (coreWitness hs hm).cx.map Cell.abs = px ∧ (coreWitness hs hm).cy.map Cell.abs = py ∧
      CAliasX fr p x (coreWitness hs hm).cx y (coreWitness hs hm).cy :=
  crossWitness_sound (Option.some_get _).symm

/-- The store witness is a cross-execution alias of paths that abstract to the query paths. -/
theorem storeWitness_spec {K : Nat} {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hs : storeScopeB K fr p px py = true) (hm : mayProg K fr p x px y py = true) :
    (storeWitness hs hm).cx.map Cell.abs = px ∧ (storeWitness hs hm).cy.map Cell.abs = py ∧
      CAliasX fr p x (storeWitness hs hm).cx y (storeWitness hs hm).cy :=
  crossWitness_sound (Option.some_get _).symm

/-! ## The one-execution witness (soundness direction) -/

/-- A one-execution witness: one choice list and two concrete paths. -/
structure Witness1 where
  /-- The choices of the execution. -/
  c : List Choice
  /-- The concrete path of the first variable. -/
  cx : List Cell
  /-- The concrete path of the second variable. -/
  cy : List Cell
  deriving DecidableEq, Repr

/-- The index bound of the one-execution search. -/
def bound1 (p : Prog) (px py : List ACell) : Nat := arrN p + elemN px + elemN py

/-- The finite candidate list of the one-execution search. -/
def candidates1 (N : Nat) (p : Prog) (px py : List ACell) : List Witness1 :=
  (pathsOf N px).flatMap fun cx => (pathsOf N py).flatMap fun cy =>
    (choicesOfN N p).map fun c => ⟨c, cx, cy⟩

/-- The executable one-execution witness search. It uses `runAliasB` as the check. -/
def oneWitness (fr : Frame) (p : Prog) (x : Var) (px : List ACell) (y : Var)
    (py : List ACell) : Option Witness1 :=
  (candidates1 (bound1 p px py) p px py).find? (fun w => runAliasB fr p w.c x w.cx y w.cy)

/-- A result of the one-execution search is a one-execution alias. This holds for each program. -/
theorem oneWitness_sound {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell} {w : Witness1}
    (h : oneWitness fr p x px y py = some w) :
    w.cx.map Cell.abs = px ∧ w.cy.map Cell.abs = py ∧ CAlias fr p x w.cx y w.cy := by
  have hc0 : runAliasB fr p w.c x w.cx y w.cy = true :=
    @List.find?_some _ (fun w : Witness1 => runAliasB fr p w.c x w.cx y w.cy) w _ h
  have hc := runAliasB_sound hc0
  have hm := List.mem_of_find?_eq_some h
  obtain ⟨cx, hx, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨cy, hy, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hm
  exact ⟨pathsOf_abs _ px cx hx, pathsOf_abs _ py cy hy, hc⟩

/-- A one-execution candidate that runs and aliases. -/
def Good1 (fr : Frame) (p : Prog) (x y : Var) (px py : List ACell) (w : Witness1) : Prop :=
  ∃ s o, run p w.c (CState.init fr) = some (s, []) ∧
    evalPath s x w.cx = some o ∧ evalPath s y w.cy = some o ∧
    w.cx.map Cell.abs = px ∧ w.cy.map Cell.abs = py

/-- All indices of a one-execution witness. -/
def wU1 (w : Witness1) : List Nat := idxs w.c ++ pidx w.cx ++ pidx w.cy

/-- Rename a one-execution witness with a swap. -/
def wR1 (a b : Nat) (w : Witness1) : Witness1 :=
  ⟨w.c.map (rCh a b), w.cx.map (rC a b), w.cy.map (rC a b)⟩

/-- Completeness of the one-execution search: for a program without loops and calls, each
one-execution alias makes the search succeed. -/
theorem oneWitness_complete {fr : Frame} {p : Prog} (hp : arrP p = true) {x y : Var}
    {px py : List ACell} {cx cy : List Cell} (hx : cx.map Cell.abs = px)
    (hy : cy.map Cell.abs = py) (h : CAlias fr p x cx y cy) :
    (oneWitness fr p x px y py).isSome = true := by
  obtain ⟨s, hex, o, e1, e2⟩ := h
  obtain ⟨c, r⟩ := run_completeA hex hp []
  rw [List.append_nil] at r
  have hg : Good1 fr p x y px py ⟨c, cx, cy⟩ := ⟨s, o, r, e1, e2, hx, hy⟩
  have hlen : (wU1 ⟨c, cx, cy⟩).length ≤ bound1 p px py := by
    have l1 := (run_listed hp r).1
    have l3 := pidx_length cx
    have l4 := pidx_length cy
    rw [hx] at l3
    rw [hy] at l4
    simp only [wU1, List.length_append, bound1]
    omega
  have hU : ∀ a b d, wU1 (wR1 a b d) = (wU1 d).map (swp a b) := by
    intro a b d; simp only [wU1, wR1, idxs_r, pidx_r, List.map_append]
  have hP : ∀ a b d, Good1 fr p x y px py d → Good1 fr p x y px py (wR1 a b d) := by
    intro a b d ⟨s, o, r, e1, e2, hx, hy⟩
    have r' := run_r a b hp r
    rw [rS_init] at r'
    refine ⟨rS a b s, rO a b o, r', ?_, ?_, ?_, ?_⟩
    · show evalPath _ x (d.cx.map (rC a b)) = _
      rw [evalPath_r, e1]; rfl
    · show evalPath _ y (d.cy.map (rC a b)) = _
      rw [evalPath_r, e2]; rfl
    · show (d.cx.map (rC a b)).map Cell.abs = px
      rw [rP_abs]; exact hx
    · show (d.cy.map (rC a b)).map Cell.abs = py
      rw [rP_abs]; exact hy
  obtain ⟨w', hg', _, hlt⟩ := compact wU1 wR1 hU (Good1 fr p x y px py) hP _ _ (Nat.le_refl _) hg
  obtain ⟨s', o', r', e1', e2', hx', hy'⟩ := hg'
  have hN : ∀ i ∈ wU1 w', i < bound1 p px py := fun i hi => Nat.lt_of_lt_of_le (hlt i hi) hlen
  have m1 := (run_listed hp r').2 _ (fun i hi => hN i (by
    simp only [wU1, List.mem_append]; exact Or.inl (Or.inl hi)))
  have m3 := mem_pathsOf _ w'.cx (fun i hi => hN i (by
    simp only [wU1, List.mem_append]; exact Or.inl (Or.inr hi)))
  have m4 := mem_pathsOf _ w'.cy (fun i hi => hN i (by
    simp only [wU1, List.mem_append]; exact Or.inr hi))
  rw [hx'] at m3
  rw [hy'] at m4
  have hmem : w' ∈ candidates1 (bound1 p px py) p px py :=
    List.mem_flatMap.mpr ⟨w'.cx, m3, List.mem_flatMap.mpr ⟨w'.cy, m4,
      List.mem_map.mpr ⟨w'.c, m1, rfl⟩⟩⟩
  have hf : runFrom fr p w'.c = some s' := by simp only [runFrom, r', Option.map_some]
  have hc : runAliasB fr p w'.c x w'.cx y w'.cy = true := by
    simp only [runAliasB, hf]
    exact aliasInB_iff.mpr ⟨o', e1', e2'⟩
  exact List.find?_isSome.mpr ⟨w', hmem, hc⟩

end DirectedAlias.Sound.Witness
