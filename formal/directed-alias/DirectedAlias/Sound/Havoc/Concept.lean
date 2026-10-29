import DirectedAlias.Sound.Soundness

/-!
# Strict A2 and per-cell havoc origins (CEGAR step for the shared havoc spread)

The foundation havoc (`Havoc`) is generous: one call can write the SAME new object into many
cells. Concept C models this with one origin `havoc s` for each call site. Under the generous
semantics, the spread of `havoc s` into every reachable cell is real.

The intended scope A2 is stricter: callee-made aliasing is out of scope. This file states the
strict semantics and the refined concept:

* `HavocS src`: the object that a call writes into cell `(o, c)` is `sym (havoc s n k) []`,
  and the tag `k` decodes to that cell: `src k = (o, c)`. So two cells never get the same new
  object (`HavocS.inj`). `src` is a free naming function. Each strict havoc is also a
  generous havoc (`HavocS.toHavoc`), so `ExecS` is a subset of `Exec` (`ExecS.toExec`).
* `alphaS K src`: a havoc object at path `p` below the head that call `s` wrote into cell
  `(o, c)` has the origin `hsym s (alpha K o) c.abs (p.map abs)` (k-limited, `hdeep` beyond `K`).
  The key `alpha K o` uses the foundation abstraction, so the key of a havoc holder is the
  site origin `havoc s0`. This keeps the universe finite.
* `AState.havocH`: weak havoc with one origin for each cell: the cell `c` of each reachable
  origin `o` keeps its content and gets `hsym s (keyOf o) c []`.
-/

namespace DirectedAlias.Sound.Havoc

open DirectedAlias DirectedAlias.Sound

/-! ## Strict concrete semantics -/

/-- Strict havoc of the `n`-th execution of call site `s` (strict A2): each cell keeps its value,
or a cell of a reachable object gets a new havoc object whose tag decodes to that cell. -/
def HavocS (src : Nat → Obj × Cell) (st : CState) (args : List Var) (s n : Nat) (h' : Heap) :
    Prop :=
  ∀ o c, h' o c = st.heap o c ∨
    (Reach st args o ∧ ∃ k, src k = (o, c) ∧ h' o c = some (.sym (.havoc s n k) []))

/-- One statement step with the strict call semantics. The other statements are as in `SStep`. -/
inductive SStepS (src : Nat → Obj × Cell) : Stmt → CState → CState → Prop where
  | new {x s st} :
      SStepS src (.new x s) st ((st.setVar x (some (.alloc s (st.cnt s)))).bump s)
  | null {x st} : SStepS src (.null x) st (st.setVar x none)
  | copy {x y st} : SStepS src (.copy x y) st (st.setVar x (st.env y))
  | load {x y f st o} : st.env y = some o →
      SStepS src (.load x y f) st (st.setVar x (st.heap o (.fld f)))
  | store {x f y st o} : st.env x = some o →
      SStepS src (.store x f y) st (st.setCell o (.fld f) (st.env y))
  | aload {x y st o} (i : Nat) : st.env y = some o →
      SStepS src (.aload x y) st (st.setVar x (st.heap o (.elem i)))
  | astore {x y st o} (i : Nat) : st.env x = some o →
      SStepS src (.astore x y) st (st.setCell o (.elem i) (st.env y))
  | unknown {x s st} :
      SStepS src (.unknown x s) st ((st.setVar x (some (.sym (.fresh s (st.cnt s)) []))).bump s)
  | call {ret s args st h'} : HavocS src st args s (st.cnt s) h' →
      SStepS src (.call ret s args) st
        (({ st with heap := h' }.setRet ret (some (.sym (.fresh s (st.cnt s)) []))).bump s)

/-- Big-step execution with the strict call semantics. -/
inductive ExecS (src : Nat → Obj × Cell) : Prog → CState → CState → Prop where
  | skip {s} : ExecS src .skip s s
  | stmt {st s s'} : SStepS src st s s' → ExecS src (.stmt st) s s'
  | seq {p q s t u} : ExecS src p s t → ExecS src q t u → ExecS src (.seq p q) s u
  | choiceL {p q s t} : ExecS src p s t → ExecS src (.choice p q) s t
  | choiceR {p q s t} : ExecS src q s t → ExecS src (.choice p q) s t
  | loopZero {p s} : ExecS src (.loop p) s s
  | loopMore {p s t u} : ExecS src p s t → ExecS src (.loop p) t u → ExecS src (.loop p) s u

/-- One-execution alias under the strict call semantics. -/
def CAliasS (src : Nat → Obj × Cell) (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var)
    (py : List Cell) : Prop :=
  ∃ st, ExecS src p (CState.init fr) st ∧ AliasIn st x px y py

/-- A strict havoc is a generous havoc. -/
theorem HavocS.toHavoc {src : Nat → Obj × Cell} {st : CState} {args : List Var} {s n : Nat}
    {h' : Heap} (h : HavocS src st args s n h') : Havoc st args s n h' := by
  intro o c
  rcases h o c with e | ⟨hr, k, _, e⟩
  · exact Or.inl e
  · exact Or.inr ⟨hr, k, e⟩

/-- Strictness: if a strict havoc writes new objects into two cells and the objects are equal,
then the two cells are the same cell. -/
theorem HavocS.inj {src : Nat → Obj × Cell} {s n : Nat} {o o' : Obj} {c c' : Cell} {k k' : Nat}
    (hk : src k = (o, c)) (hk' : src k' = (o', c'))
    (e : (Obj.sym (.havoc s n k) [] : Obj) = .sym (.havoc s n k') []) : o = o' ∧ c = c' := by
  simp only [Obj.sym.injEq, Base.havoc.injEq] at e
  rw [e.1.2.2] at hk
  rw [hk] at hk'
  simp only [Prod.mk.injEq] at hk'
  exact hk'

/-- A strict step is a step of the foundation semantics. -/
theorem SStepS.toSStep {src : Nat → Obj × Cell} {st : Stmt} {s s' : CState}
    (h : SStepS src st s s') : SStep st s s' := by
  cases h with
  | new => exact .new
  | null => exact .null
  | copy => exact .copy
  | load he => exact .load he
  | store he => exact .store he
  | aload i he => exact .aload i he
  | astore i he => exact .astore i he
  | unknown => exact .unknown
  | call hh => exact .call hh.toHavoc

/-- A strict execution is an execution of the foundation semantics. -/
theorem ExecS.toExec {src : Nat → Obj × Cell} {p : Prog} {s s' : CState}
    (h : ExecS src p s s') : Exec p s s' := by
  induction h with
  | skip => exact .skip
  | stmt hs => exact .stmt hs.toSStep
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | choiceL _ ih => exact .choiceL ih
  | choiceR _ ih => exact .choiceR ih
  | loopZero => exact .loopZero
  | loopMore _ _ ih1 ih2 => exact .loopMore ih1 ih2

/-- A strict one-execution alias is a one-execution alias of the foundation semantics. -/
theorem CAliasS.toCAlias {src : Nat → Obj × Cell} {fr : Frame} {p : Prog} {x y : Var}
    {px py : List Cell} (h : CAliasS src fr p x px y py) : CAlias fr p x px y py := by
  obtain ⟨st, hx, ha⟩ := h
  exact ⟨st, hx.toExec, ha⟩

/-! ## The abstraction with per-cell havoc origins -/

/-- A per-cell havoc origin at path `q`, or its deep summary if `q` is longer than `K`. -/
def hsymOrDeep (K : Nat) (s : Site) (key : Origin) (c : ACell) (q : List ACell) : Origin :=
  if q.length ≤ K then .hsym s key c q else .hdeep s key c

/-- The strict abstraction. A havoc object at path `p` below the head that call `s` wrote into
cell `src k` gets the per-cell origin of that cell. The key of the holder is its foundation
origin `alpha K`. Other objects keep their foundation origin. -/
def alphaS (K : Nat) (src : Nat → Obj × Cell) : Obj → Origin
  | .sym (.root r) p => alpha K (.sym (.root r) p)
  | .sym (.fresh s n) p => alpha K (.sym (.fresh s n) p)
  | .sym (.havoc s _ k) p => hsymOrDeep K s (alpha K (src k).1) (src k).2.abs (p.map Cell.abs)
  | .alloc s _ => .alloc s

/-- The key of an origin when it holds a cell that a call writes: a per-cell havoc origin
gives its site origin `havoc s`. Other origins are their own key. -/
def keyOf : Origin → Origin
  | .sym b q => .sym b q
  | .deep b => .deep b
  | .alloc s => .alloc s
  | .havoc s => .havoc s
  | .hsym s _ _ _ => .havoc s
  | .hdeep s _ _ => .havoc s

/-- The key of the strict origin of an object is its foundation origin. -/
theorem keyOf_alphaS (K : Nat) (src : Nat → Obj × Cell) (o : Obj) :
    keyOf (alphaS K src o) = alpha K o := by
  cases o with
  | alloc s n => rfl
  | sym b p =>
    cases b with
    | root r =>
      show keyOf (symOrDeep K _ _) = symOrDeep K _ _
      unfold symOrDeep; split <;> rfl
    | fresh s n =>
      show keyOf (symOrDeep K _ _) = symOrDeep K _ _
      unfold symOrDeep; split <;> rfl
    | havoc s n k =>
      show keyOf (hsymOrDeep K _ _ _ _) = .havoc s
      unfold hsymOrDeep; split <;> rfl

/-- The strict origin of an object that is not a havoc object is its foundation origin. -/
theorem alphaS_of_root (K : Nat) (src : Nat → Obj × Cell) (r : Root) (p : List Cell) :
    alphaS K src (.sym (.root r) p) = alpha K (.sym (.root r) p) := rfl

/-- The strict origin of a fresh object is its foundation origin. -/
theorem alphaS_of_fresh (K : Nat) (src : Nat → Obj × Cell) (s n : Nat) (p : List Cell) :
    alphaS K src (.sym (.fresh s n) p) = alpha K (.sym (.fresh s n) p) := rfl

/-- The strict origin of the head object that a strict havoc writes into cell `(o, c)`. -/
theorem alphaS_head (K : Nat) {src : Nat → Obj × Cell} {s n k : Nat} {o : Obj} {c : Cell}
    (hk : src k = (o, c)) :
    alphaS K src (.sym (.havoc s n k) []) = .hsym s (keyOf (alphaS K src o)) c.abs [] := by
  show hsymOrDeep K s (alpha K (src k).1) (src k).2.abs (List.map Cell.abs ([] : List Cell)) = _
  rw [hk, keyOf_alphaS]
  exact ite_eq_left (Nat.zero_le K)

/-! ## The refined abstract call -/

/-- Weak havoc of call site `s` with per-cell origins: each universe cell `c` of each
reachable origin `o` keeps its content and gets `hsym s (keyOf o) c []`. -/
def _root_.DirectedAlias.AState.havocH (ctx : Ctx) (X : AState) (args : List Var) (s : Site) : AState :=
  let r := reachB ctx X args
  { X with heap := fun o c =>
      if c ∈ ctx.cells ∧ r o = true then uni [.hsym s (keyOf o) c []] (X.heap o c)
      else X.heap o c }

/-- The abstract transfer with per-cell havoc. Only the call differs from `astep`. -/
def astepH (ctx : Ctx) : Stmt → AState → AState
  | .call ret s args, X => (X.havocH ctx args s).setRet ret [.sym (.fresh s) []]
  | st, X => astep ctx st X

/-- The abstract analysis with per-cell havoc. -/
def analyzeH (ctx : Ctx) : Prog → AState → AState
  | .skip, X => X
  | .stmt s, X => astepH ctx s X
  | .seq p q, X => analyzeH ctx q (analyzeH ctx p X)
  | .choice p q, X => join (analyzeH ctx p X) (analyzeH ctx q X)
  | .loop p, X => loopIter ctx (analyzeH ctx p) ctx.fuel X

/-! ## The universe -/

/-- The per-cell havoc origins of the call sites `calls`, for each key and each cell:
the paths up to `K` and the deep summary. -/
def havocCells (K : Nat) (keys : List Origin) (cells : List ACell) (calls : List Site) :
    List Origin :=
  calls.flatMap (fun s => keys.flatMap (fun a => cells.flatMap (fun c =>
    (pathsUpTo cells K).map (Origin.hsym s a c) ++ [Origin.hdeep s a c])))

/-- The origin universe with per-cell havoc: the foundation universe, and the per-cell havoc
origins with a foundation key. -/
def originsH (K : Nat) (fr : Frame) (p : Prog) (cells : List ACell) : List Origin :=
  originsOf K fr p cells ++ havocCells K (originsOf K fr p cells) cells p.callSites

/-- The context of a program with per-cell havoc and the strong-update policy `eu`. -/
def ctxH (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : Ctx :=
  let cells := cellsOf (p.fields ++ qf)
  let vars := (p.vars ++ fr.vars).eraseDups
  let origins := originsH K fr p cells
  { K := K, once := p.onceB, cells := cells, vars := vars, origins := origins,
    fuel := (vars.length + origins.length * cells.length) * origins.length + 1,
    entryUnique := eu }

/-- The final abstract state of program `p` with per-cell havoc. -/
def analyzeProgH (eu : Bool) (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) : AState :=
  analyzeH (ctxH eu K fr p qf) p (ainit K fr)

/-- May-alias at the end of `p`, with per-cell havoc. -/
def mayProgH (eu : Bool) (K : Nat) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeProgH eu K fr p (afields px ++ afields py)) x px y py

end DirectedAlias.Sound.Havoc
