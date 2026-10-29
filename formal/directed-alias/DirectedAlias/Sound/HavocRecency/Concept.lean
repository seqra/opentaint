import DirectedAlias.Sound.HavocRecency.Inv

/-!
# Recency with per-cell havoc origins (the production configuration)

This file combines the two refinements of concept C:
* recency (`Sound/Recency`): each allocation site has the origins `rNew s` and `rOld s`, and a
  site that runs again retires its most recent object;
* per-cell havoc under strict A2 (`Sound/Havoc`): a call writes into the cell `c` of an object
  with key `key` a new object with the origin `hsym s key c []`.

The key of an allocation holder is `rOld s'` for BOTH recency origins of its site (`baseKey`,
`keyOfR`). Thus the abstraction of a havoc object does not read the counters, and `retire`
does not touch per-cell havoc origins. The cost: the havoc objects in the cells of the most
recent object and of the older objects of one site share their per-cell origins.
-/

namespace DirectedAlias.Sound.HavocRecency

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc

/-! ## The abstraction -/

/-- The key of a concrete holder object. It does not read the counters: an allocation of
site `s` has the key `rOld s`, a havoc object has its site origin, other objects have their
foundation origin. -/
def baseKey (K : Nat) : Obj → Origin
  | .sym (.root r) p => alpha K (.sym (.root r) p)
  | .sym (.fresh s n) p => alpha K (.sym (.fresh s n) p)
  | .sym (.havoc s _ _) _ => .havoc s
  | .alloc s _ => rOld s

/-- The recency abstraction with per-cell havoc origins. Allocations read the counter. A
havoc object at path `p` below the head that call `s` wrote into cell `src k` gets the
per-cell origin with the key of the holder. -/
def alphaRS (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) : Obj → Origin
  | .sym (.root r) p => alpha K (.sym (.root r) p)
  | .sym (.fresh s n) p => alpha K (.sym (.fresh s n) p)
  | .sym (.havoc s _ k) p => hsymOrDeep K s (baseKey K (src k).1) (src k).2.abs (p.map Cell.abs)
  | .alloc s n => if n + 1 = cnt s then rNew s else rOld s

/-- The key of an abstract holder origin: both recency origins of a site give `rOld s`,
a per-cell havoc origin gives its site origin, other origins are their own key. -/
def keyOfR : Origin → Origin
  | .sym b q => .sym b q
  | .deep b => .deep b
  | .alloc a => .alloc (2 * (a / 2) + 1)
  | .havoc s => .havoc s
  | .hsym s _ _ _ => .havoc s
  | .hdeep s _ _ => .havoc s

/-- Both recency origins of a site have the key `rOld s`. -/
theorem keyOfR_rNew (s : Site) : keyOfR (rNew s) = rOld s := by
  show Origin.alloc (2 * (2 * s / 2) + 1) = .alloc (2 * s + 1)
  have : @Eq Nat (2 * s / 2) s := by omega
  rw [this]

/-- The key of `rOld s` is `rOld s`. -/
theorem keyOfR_rOld (s : Site) : keyOfR (rOld s) = rOld s := by
  show Origin.alloc (2 * ((2 * s + 1) / 2) + 1) = .alloc (2 * s + 1)
  have : @Eq Nat ((2 * s + 1) / 2) s := by omega
  rw [this]

/-- The key of the abstraction of an object is its state-independent key. -/
theorem keyOfR_alphaRS (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) (o : Obj) :
    keyOfR (alphaRS K src cnt o) = baseKey K o := by
  cases o with
  | alloc s n =>
    show keyOfR (if n + 1 = cnt s then rNew s else rOld s) = rOld s
    split
    · exact keyOfR_rNew s
    · exact keyOfR_rOld s
  | sym b p =>
    cases b with
    | root r =>
      show keyOfR (symOrDeep K _ _) = symOrDeep K _ _
      unfold symOrDeep; split <;> rfl
    | fresh s n =>
      show keyOfR (symOrDeep K _ _) = symOrDeep K _ _
      unfold symOrDeep; split <;> rfl
    | havoc s n k =>
      show keyOfR (hsymOrDeep K _ _ _ _) = .havoc s
      unfold hsymOrDeep; split <;> rfl

/-- The origin of the head object that a strict havoc writes into cell `(o, c)`. -/
theorem alphaRS_head (K : Nat) {src : Nat → Obj × Cell} (cnt : Site → Nat) {s n k : Nat}
    {o : Obj} {c : Cell} (hk : src k = (o, c)) :
    alphaRS K src cnt (.sym (.havoc s n k) []) = .hsym s (keyOfR (alphaRS K src cnt o)) c.abs [] := by
  show hsymOrDeep K s (baseKey K (src k).1) (src k).2.abs (List.map Cell.abs ([] : List Cell)) = _
  rw [hk, keyOfR_alphaRS]
  exact ite_eq_left (Nat.zero_le K)

/-- The abstraction of an object that is not a havoc object is its recency abstraction. -/
theorem alphaRS_eq_alphaR (K : Nat) (src : Nat → Obj × Cell) (st : CState) {o : Obj}
    (h : ∀ s n k p, o ≠ .sym (.havoc s n k) p) : alphaRS K src st.cnt o = alphaR K st o := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | root r => rfl
    | fresh s n => rfl
    | havoc s n k => exact absurd rfl (h s n k p)

/-- The abstraction of a havoc object is never unique. -/
theorem alphaRS_havoc_not_unique (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat)
    (once : Site → Bool) (eu : Bool) (s n k : Nat) (p : List Cell) :
    uniqueR once eu (alphaRS K src cnt (.sym (.havoc s n k) p)) = false := by
  show uniqueR once eu (hsymOrDeep K _ _ _ _) = false
  unfold hsymOrDeep; split <;> rfl

/-- A counter bump of site `s` renames the abstraction of every object except the next
object of `s`. Havoc objects keep their origin. -/
theorem alphaRS_bump (K : Nat) (src : Nat → Obj × Cell) (st : CState) (s : Site) {o : Obj}
    (h : o ≠ .alloc s (st.cnt s)) :
    alphaRS K src (st.bump s).cnt o = renameO s (alphaRS K src st.cnt o) := by
  cases o with
  | alloc a n => exact alphaR_bump K st s h
  | sym b p =>
    cases b with
    | root r => exact alphaR_bump K st s h
    | fresh a n => exact alphaR_bump K st s h
    | havoc a n k =>
      show hsymOrDeep K _ _ _ _ = renameO s (hsymOrDeep K _ _ _ _)
      unfold renameO hsymOrDeep
      split <;> simp [rNew]

/-- The next object of site `a` has the origin `rNew a` after the bump. -/
theorem alphaRS_new (K : Nat) (src : Nat → Obj × Cell) (st : CState) (a : Site) :
    alphaRS K src (st.bump a).cnt (.alloc a (st.cnt a)) = rNew a := by
  show (if st.cnt a + 1 = fupd st.cnt a (st.cnt a + 1) a then rNew a else rOld a) = rNew a
  rw [fupd_same, ite_eq_left rfl]

/-- The abstraction of a symbolic object is an outer origin. -/
theorem alphaRS_sym_outer (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) (b : Base)
    (p : List Cell) : (alphaRS K src cnt (.sym b p)).outer = true := by
  cases b with
  | root r => exact alpha_sym_outer K (.root r) p
  | fresh s n => exact alpha_sym_outer K (.fresh s n) p
  | havoc s n k =>
    show (hsymOrDeep K s _ _ _).outer = true
    unfold hsymOrDeep; split <;> rfl

/-- The abstraction of a fresh head object is its fresh origin. -/
theorem alphaRS_fresh (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) (s n : Nat) :
    alphaRS K src cnt (.sym (.fresh s n) []) = .sym (.fresh s) [] := by
  show symOrDeep K (.fresh s) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le K)

/-- The abstraction of an entry root object is its root origin. -/
theorem alphaRS_root (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) (r : Root) :
    alphaRS K src cnt (.sym (.root r) []) = .sym (.root r) [] := by
  show symOrDeep K (.root r) (([] : List Cell).map Cell.abs) = _
  exact ite_eq_left (Nat.zero_le K)

/-- The abstraction of a default child is in the abstract default content of the parent. -/
theorem alphaRS_cdefault (K : Nat) (src : Nat → Obj × Cell) (cnt : Site → Nat) {o o' : Obj}
    {c : Cell} (h : cdefault o c = some o') :
    alphaRS K src cnt o' ∈ adefault K (alphaRS K src cnt o) c.abs := by
  cases o with
  | alloc s n => cases h
  | sym b p =>
    cases h
    cases b with
    | root r =>
      show alpha K (.sym (.root r) (p ++ [c])) ∈ adefault K (alpha K (.sym (.root r) p)) c.abs
      rw [← alphaV_cdefault]; exact List.mem_singleton.mpr rfl
    | fresh s n =>
      show alpha K (.sym (.fresh s n) (p ++ [c])) ∈ adefault K (alpha K (.sym (.fresh s n) p)) c.abs
      rw [← alphaV_cdefault]; exact List.mem_singleton.mpr rfl
    | havoc s n k =>
      show hsymOrDeep K s _ _ ((p ++ [c]).map Cell.abs) ∈
        adefault K (hsymOrDeep K s _ _ (p.map Cell.abs)) c.abs
      unfold hsymOrDeep
      rw [List.map_append, List.map_cons, List.map_nil]
      by_cases h1 : (p.map Cell.abs).length ≤ K
      · rw [ite_eq_left h1]
        exact List.mem_singleton.mpr rfl
      · have h2 : ¬ (p.map Cell.abs ++ [c.abs]).length ≤ K := by
          rw [List.length_append]; omega
        rw [ite_eq_right h1, ite_eq_right h2]
        exact List.mem_singleton.mpr rfl

/-- A unique origin denotes at most one object that is not dead. -/
theorem unique_objRS {K : Nat} {src : Nat → Obj × Cell} {once : Site → Bool} {eu : Bool}
    {cnt : Site → Nat} {o o' : Obj}
    (hu : uniqueR once eu (alphaRS K src cnt o) = true) (hd : ¬ Dead once o)
    (hd' : ¬ Dead once o') (ha : alphaRS K src cnt o' = alphaRS K src cnt o) : o' = o := by
  let st : CState := ⟨fun _ => none, fun _ _ => none, cnt⟩
  have nh : ∀ o1 : Obj, uniqueR once eu (alphaRS K src cnt o1) = true →
      ∀ s n k p, o1 ≠ .sym (.havoc s n k) p := by
    intro o1 h1 s n k p e
    subst e
    rw [alphaRS_havoc_not_unique] at h1
    cases h1
  have hu' : uniqueR once eu (alphaRS K src cnt o') = true := by rw [ha]; exact hu
  have e1 := alphaRS_eq_alphaR K src st (nh o hu)
  have e2 := alphaRS_eq_alphaR K src st (nh o' hu')
  have hu2 : uniqueR once eu (alphaR K st o) = true := by rw [← e1]; exact hu
  exact unique_objR hu2 hd hd' (by rw [← e1, ← e2]; exact ha)

/-! ## The abstract call -/

/-- Weak havoc of call site `s` with per-cell origins and recency keys: each universe cell
`c` of each reachable origin `o` keeps its content and gets `hsym s (keyOfR o) c []`. -/
def havocHR (ctx : Ctx) (X : AState) (args : List Var) (s : Site) : AState :=
  let r := reachB ctx X args
  { X with heap := fun o c =>
      if c ∈ ctx.cells ∧ r o = true then uni [.hsym s (keyOfR o) c []] (X.heap o c)
      else X.heap o c }

/-- The abstract transfer with recency and per-cell havoc. -/
def astepHR (ctx : Ctx) : Stmt → AState → AState
  | .new x s, X => (retire s X).setVar x [rNew s]
  | .unknown x s, X => (retire s X).setVar x [.sym (.fresh s) []]
  | .call ret s args, X => (retire s (havocHR ctx X args s)).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeR ctx X x (.fld f) (X.env y)
  | st, X => astep ctx st X

/-- The abstract analysis with recency and per-cell havoc. -/
def analyzeHR (ctx : Ctx) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepHR ctx s X
  | .seq p q, X => analyzeHR ctx q (analyzeHR ctx p X)
  | .choice p q, X => join (analyzeHR ctx p X) (analyzeHR ctx q X)
  | .loop p, X => loopIter ctx (analyzeHR ctx p) ctx.fuel X

/-! ## The universe -/

/-- The keys of the recency universe: the recency universe without the `rNew` origins. -/
def keysR (K : Nat) (fr : Frame) (p : Prog) (cells : List ACell) : List Origin :=
  let bases := fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh
  bases.flatMap (fun b => (pathsUpTo cells K).map (Origin.sym b) ++ [Origin.deep b]) ++
    p.newSites.map rOld ++ p.callSites.map Origin.havoc

/-- The origin universe with recency and per-cell havoc. -/
def originsHR (K : Nat) (fr : Frame) (p : Prog) (cells : List ACell) : List Origin :=
  originsR K fr p cells ++ havocCells K (keysR K fr p cells) cells p.callSites

/-- The context of a program with recency, per-cell havoc and the policy `eu`. -/
def ctxHR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  let cells := cellsOf (p.fields ++ qf)
  let vars := (p.vars ++ fr.vars).eraseDups
  let origins := originsHR K fr p cells
  { K := K, once := p.onceB, cells := cells, vars := vars, origins := origins,
    fuel := (vars.length + origins.length * cells.length) * origins.length + 1,
    entryUnique := eu }

/-- The final abstract state of program `p` with recency and per-cell havoc. -/
def analyzeProgHR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : AState :=
  analyzeHR (ctxHR eu K fr p qf) p (ainit K fr)

/-- May-alias at the end of `p`, with recency and per-cell havoc. -/
def mayProgHR (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgHR eu K fr p (afields px ++ afields py)) x px y py

end DirectedAlias.Sound.HavocRecency
