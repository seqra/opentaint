import DirectedAlias.Impl.EngineCall

/-!
# The cost of the engine call closure and of the change test (obligation 4)

The work counters are explicit functions with the recursion of the algorithms.

* ENGINE CLOSURE (`closeWork`): one unit for each pop of the worklist (the membership test in
  `R`), two units for each new origin (its two index buckets: the origin itself and its base),
  `K + 2` units for each activated written entry (it leaves its at most `K + 2` index buckets:
  the prefixes of a path of length at most `K`, and the base), and one unit at the end. The
  filter of the pending entries by the descendant test is the lookup of the index buckets of the
  new origin; the index itself is argued, not modelled. `closeWork_le`: the work is at most
  `3 · (|W| + Σ |content of a pending cell|) + (K + 2) · |P| + 1`. At a call
  (`callWork_le`): at most `3 · (|start set| + Σ_{written} |content|) + (K + 2) · |written| + 1`.
* MODEL CLOSURE (`closeNWork`): each iteration tests the cover of each universe origin, so it
  costs at least `|U|`; the model closure costs at least `|U|` (`closeNWork_ge`), and exactly
  `|U|` for each iteration (`closeNWork_eq`).
* SEPARATION (`separation`): the program `m(x)@1` with `x` bound to a root, and the query field
  `0`: for each `K`, the engine closure at the entry state costs 4 units; the model closure costs
  at least `2^K` (`|cells| = 2`, and the universe has the `2^K` symbolic paths of length `K`).
* THE CHANGE TEST (`mapEqBW_eq`): one comparison for each key of either map (with hash-consed
  nodes, each comparison is one integer comparison: `Opt/Table.lean`). The model check `leOn`
  compares each universe variable and each universe cell (`leOnWork`).
-/

namespace DirectedAlias.Impl.Engine

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## The engine closure -/

/-- The work of the engine closure, with the recursion of `closeE`. -/
def closeWork (K : Nat) (E : EState) :
    Nat → List Origin → List Origin → List (Origin × ACell) → Nat
  | 0, _, _, _ => 0
  | _ + 1, [], _, _ => 1
  | n + 1, a :: W, R, P =>
    if a ∈ R then 1 + closeWork K E n W R P
    else 3 + (K + 2) * (P.filter (fun k => descB a k.1)).length +
      closeWork K E n (uniMap (getH K E) (P.filter (fun k => descB a k.1)) ++ W) (a :: R)
        (P.filter (fun k => !descB a k.1))

/-- THE WORK BOUND OF THE ENGINE CLOSURE: three units for each element of the worklist or of a
pending cell content, `K + 2` units for each pending written entry, and one unit. -/
theorem closeWork_le (K : Nat) (E : EState) :
    ∀ (n : Nat) (W R : List Origin) (P : List (Origin × ACell)),
      closeWork K E n W R P ≤ 3 * cmeas K E W P + (K + 2) * P.length + 1
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, [], _, _ => by unfold closeWork; omega
  | n + 1, a :: W, R, P => by
    unfold closeWork
    by_cases ha : a ∈ R
    · rw [ite_eq_left ha]
      have ih := closeWork_le K E n W R P
      unfold cmeas at ih ⊢
      simp only [List.length_cons]
      omega
    · rw [ite_eq_right ha]
      have ih := closeWork_le K E n (uniMap (getH K E) (P.filter (fun k => descB a k.1)) ++ W)
        (a :: R) (P.filter (fun k => !descB a k.1))
      have h1 := len_uniMap_le (getH K E) (P.filter (fun k => descB a k.1))
      have h2 := sum_filter_split (fun k => (getH K E k).length) (fun k => descB a k.1) P
      have h3 := length_filter_split (fun k => descB a k.1) P
      unfold cmeas at ih ⊢
      simp only [List.length_append, List.length_cons] at ih ⊢
      have hm : (K + 2) * (P.filter (fun k => descB a k.1)).length +
          (K + 2) * (P.filter (fun k => !descB a k.1)).length = (K + 2) * P.length := by
        rw [← Nat.mul_add, h3]
      omega

/-- THE WORK OF THE ENGINE CALL CLOSURE: at most three units for each start origin and each
origin in a written cell, `K + 2` units for each written entry, and one unit. -/
theorem callWork_le (cb : CtxB) (E : EState) (n : Nat) (args : List Var) :
    closeWork cb.cn.ctx.K E n (startE cb E args) [] (keys E.heap) ≤
      3 * ((startE cb E args).length +
        ((keys E.heap).map (fun k => (getH cb.cn.ctx.K E k).length)).sum) +
      (cb.cn.ctx.K + 2) * E.heap.length + 1 := by
  have h := closeWork_le cb.cn.ctx.K E n (startE cb E args) [] (keys E.heap)
  have hl : (keys E.heap).length = E.heap.length := List.length_map _
  unfold cmeas at h
  rw [hl] at h
  exact h

/-! ## The model closure -/

/-- The work of the model closure: each iteration tests the cover of each universe origin. -/
def closeNWork (cn : CtxN) (X : AState) : Nat → List Origin → Nat
  | 0, _ => 0
  | n + 1, R => cn.ctx.origins.length +
    if subB (succsN cn X R) R then 0 else closeNWork cn X n (uni (succsN cn X R) R)

/-- The number of iterations of the model closure. -/
def closeNIter (cn : CtxN) (X : AState) : Nat → List Origin → Nat
  | 0, _ => 0
  | n + 1, R => 1 + if subB (succsN cn X R) R then 0 else closeNIter cn X n (uni (succsN cn X R) R)

/-- THE MODEL CLOSURE COSTS `|U|` FOR EACH ITERATION. -/
theorem closeNWork_eq (cn : CtxN) (X : AState) :
    ∀ (n : Nat) (R : List Origin), closeNWork cn X n R = cn.ctx.origins.length * closeNIter cn X n R
  | 0, _ => rfl
  | n + 1, R => by
    unfold closeNWork closeNIter
    by_cases h : subB (succsN cn X R) R = true
    · rw [ite_eq_left h, ite_eq_left h]; simp
    · rw [ite_eq_right h, ite_eq_right h, closeNWork_eq cn X n, Nat.mul_add, Nat.mul_one]

/-- THE MODEL CLOSURE COSTS AT LEAST `|U|`. -/
theorem closeNWork_ge (cn : CtxN) (X : AState) (n : Nat) (R : List Origin) :
    cn.ctx.origins.length ≤ closeNWork cn X (n + 1) R := by
  unfold closeNWork
  omega

/-! ## The separation family -/

/-- The number of paths of length at most `n` is at least `|cells|^n`. -/
theorem pathsUpTo_length (cells : List ACell) :
    ∀ n : Nat, cells.length ^ n ≤ (pathsUpTo cells n).length
  | 0 => by simp [pathsUpTo]
  | n + 1 => by
    have ih := pathsUpTo_length cells n
    have hf : ∀ l : List ACell,
        (l.flatMap (fun c => (pathsUpTo cells n).map (c :: ·))).length =
          l.length * (pathsUpTo cells n).length := by
      intro l
      induction l with
      | nil => simp
      | cons c l ihl =>
        rw [List.flatMap_cons, List.length_append, List.length_map, ihl, List.length_cons,
          Nat.succ_mul]
        omega
    show cells.length ^ (n + 1) ≤
      ([] :: cells.flatMap (fun c => (pathsUpTo cells n).map (c :: ·))).length
    rw [List.length_cons, hf, Nat.pow_succ, Nat.mul_comm (cells.length ^ n)]
    have := Nat.mul_le_mul_left cells.length ih
    omega

/-- The frame of the family: variable 0 holds root 0. -/
def frF : Frame := ⟨[(0, 0)]⟩

/-- The program of the family: the call `m(x)@1` with `x` the variable 0. -/
def pF : Prog := .stmt (.call none 1 [0])

/-- The context of the family with depth limit `K`. -/
def cbF (eu : Bool) (K : Nat) : CtxB := ctxVS eu K [] frF pF [0]

/-- The universe of the family has each symbolic path of length at most `K` below root 0. -/
theorem cbF_origins (eu : Bool) (K : Nat) :
    (pathsUpTo (cellsOf [0]) K).length ≤ (cbF eu K).cn.ctx.origins.length := by
  show (pathsUpTo (cellsOf [0]) K).length ≤
    ((ABase.root 0 :: ([] : List Root).map ABase.root ++ [ABase.fresh 1]).flatMap
      (fun b => (pathsUpTo (cellsOf [0]) K).map (Origin.sym b) ++ [Origin.deep b]) ++
      ([] : List Site).flatMap (fun s => [rNew s, rOld s]) ++
      heapKids K [] (cellsOf [0]) ++ nullKids K 0 (cellsOf [0])).length
  rw [List.cons_append, List.flatMap_cons]
  simp only [List.length_append, List.length_map]
  omega

/-- The cell universe of the family has two cells. -/
theorem cellsF_length : (cellsOf [0]).length = 2 := rfl

/-- The model call closure of the family at an entry denotation costs at least `2^K`. -/
theorem model_work_family (eu : Bool) (K : Nat) (X : AState) (R : List Origin) :
    2 ^ K ≤ closeNWork (cbF eu K).cn X ((cbF eu K).cn.ctx.origins.length + 1) R := by
  have h1 := pathsUpTo_length (cellsOf [0]) K
  rw [cellsF_length] at h1
  have h2 := cbF_origins eu K
  have h3 := closeNWork_ge (cbF eu K).cn X ((cbF eu K).cn.ctx.origins.length) R
  omega

/-- The start set of the family at the engine entry state: root 0. -/
theorem startF (eu : Bool) (K : Nat) : startE (cbF eu K) (initE frF) [0] = [.sym (.root 0) []] :=
  rfl

/-- The engine call closure of the family at the entry state costs 4 units, for each `K`. -/
theorem engine_work_family (eu : Bool) (K n : Nat) :
    closeWork (cbF eu K).cn.ctx.K (initE frF) (n + 2) (startE (cbF eu K) (initE frF) [0]) []
      (keys (initE frF).heap) = 4 := by
  rw [startF]
  rfl

/-- THE SEPARATION: on the fixed program `m(x)@1`, for each depth limit `K`, the engine call
closure costs 4 units and the model call closure costs at least `2^K` units. -/
theorem separation (eu : Bool) (K : Nat) :
    closeWork (cbF eu K).cn.ctx.K (initE frF) ((cbF eu K).cn.ctx.origins.length + 2)
        (startE (cbF eu K) (initE frF) [0]) [] (keys (initE frF).heap) = 4 ∧
      2 ^ K ≤ closeNWork (cbF eu K).cn (den (cbF eu K).cn.ctx.K (initE frF))
        ((cbF eu K).cn.ctx.origins.length + 1)
        (callRoots (cbF eu K).cn (den (cbF eu K).cn.ctx.K (initE frF)) [0]) :=
  ⟨engine_work_family eu K _, model_work_family eu K _ _⟩

/-! ## The change test -/

/-- `all` with a counter: one unit for each element. -/
def allW {α : Type} (p : α → Bool) : List α → Bool × Nat
  | [] => (true, 0)
  | a :: l => (p a && (allW p l).1, (allW p l).2 + 1)

/-- The Boolean of `allW` is `all`. -/
theorem allW_fst {α : Type} (p : α → Bool) : ∀ l : List α, (allW p l).1 = l.all p
  | [] => rfl
  | a :: l => by
    show (p a && (allW p l).1) = (a :: l).all p
    rw [allW_fst p l]; rfl

/-- The counter of `allW` is the length. -/
theorem allW_snd {α : Type} (p : α → Bool) : ∀ l : List α, (allW p l).2 = l.length
  | [] => rfl
  | a :: l => by
    show (allW p l).2 + 1 = (a :: l).length
    rw [allW_snd p l]; rfl

/-- The map equality test of one map with a counter of key comparisons. -/
def entEqBW {κ : Type} [DecidableEq κ] (l1 l2 : List (κ × List Origin)) : Bool × Nat :=
  let a := allW (fun p => match look l1 p.1, look l2 p.1 with
    | some S1, some S2 => setEqB S1 S2
    | _, _ => false) l1
  let b := allW (fun p => (look l1 p.1).isSome) l2
  (a.1 && b.1, a.2 + b.2)

/-- The change test of two engine states with a counter of key comparisons. -/
def mapEqBW (E1 E2 : EState) : Bool × Nat :=
  ((entEqBW E1.env E2.env).1 && (entEqBW E1.heap E2.heap).1,
    (entEqBW E1.env E2.env).2 + (entEqBW E1.heap E2.heap).2)

/-- THE COST OF THE CHANGE TEST: the counted test is `mapEqB`, with one comparison for each key
of either map (at most; the Boolean test can stop early). -/
theorem mapEqBW_eq (E1 E2 : EState) :
    (mapEqBW E1 E2).1 = mapEqB E1 E2 ∧
      (mapEqBW E1 E2).2 = E1.env.length + E2.env.length + E1.heap.length + E2.heap.length := by
  refine ⟨?_, ?_⟩
  · show (((allW _ E1.env).1 && (allW _ E2.env).1) &&
      ((allW _ E1.heap).1 && (allW _ E2.heap).1)) = mapEqB E1 E2
    rw [allW_fst, allW_fst, allW_fst, allW_fst]
    rfl
  · show ((allW _ E1.env).2 + (allW _ E2.env).2) + ((allW _ E1.heap).2 + (allW _ E2.heap).2) = _
    rw [allW_snd, allW_snd, allW_snd, allW_snd]
    omega

/-- The comparisons of the model check `leOn`: each universe variable and each universe cell. -/
def leOnWork (ctx : Ctx) : Nat := ctx.vars.length + ctx.origins.length * ctx.cells.length

/-- An NF state with universe keys has at most one visible entry for each universe key; the
change test of two such states costs at most the comparisons of their maps. For the entry state
of the family the change test costs two comparisons, and the model check at least `2^K`. -/
theorem change_family (eu : Bool) (K : Nat) :
    (mapEqBW (initE frF) (initE frF)).2 = 2 ∧ 2 ^ K ≤ leOnWork (cbF eu K).cn.ctx := by
  refine ⟨rfl, ?_⟩
  have h1 := pathsUpTo_length (cellsOf [0]) K
  rw [cellsF_length] at h1
  have h2 := cbF_origins eu K
  have hc : (cbF eu K).cn.ctx.cells = cellsOf [0] := rfl
  unfold leOnWork
  rw [hc, cellsF_length]
  omega

end DirectedAlias.Impl.Engine
