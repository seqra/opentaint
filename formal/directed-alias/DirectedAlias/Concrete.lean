import DirectedAlias.Syntax

/-!
# Concrete semantics

Objects have symbolic names, so that two executions can name the same object.
The entry heap is a tree (A1): each cell of a symbolic object holds its own child object.
The heap is a total function. The entry heap is the default content `cdefault`.
The big-step relation `Exec` is nondeterministic (choice, loop, array index, call havoc).
The function `run` is a deterministic executor with explicit choices. It gives executable witnesses.
-/

namespace DirectedAlias

/-- The base of a symbolic object. -/
inductive Base where
  /-- The entry object of root `r`. -/
  | root (r : Root)
  /-- The object that the `n`-th execution of site `s` returns (unknown expression or call). -/
  | fresh (s : Site) (n : Nat)
  /-- An object that the `n`-th execution of call site `s` writes into a cell (A2).
  The tag `k` lets one call write different objects. -/
  | havoc (s : Site) (n : Nat) (k : Nat)
  deriving DecidableEq, Repr

/-- A concrete object. -/
inductive Obj where
  /-- The object at path `p` below the base object of `b`, in the entry tree. -/
  | sym (b : Base) (p : List Cell)
  /-- The object that the `n`-th execution of allocation site `s` makes. -/
  | alloc (s : Site) (n : Nat)
  deriving DecidableEq, Repr

/-- A concrete value. `none` is null. -/
abbrev Val := Option Obj

/-- An object is outer when code outside the method can know it. All symbolic objects are outer. -/
def Obj.isOuter : Obj → Bool
  | .sym _ _ => true
  | .alloc _ _ => false

/-- The default content of a cell: a symbolic child for a symbolic object, null for an allocation. -/
def cdefault : Obj → Cell → Val
  | .sym b p, c => some (.sym b (p ++ [c]))
  | .alloc _ _, _ => none

/-- A concrete variable environment. -/
abbrev Env := Var → Val
/-- A concrete heap. It is total: a cell that no statement wrote holds its default content. -/
abbrev Heap := Obj → Cell → Val

/-- A concrete state: environment, heap, and the execution counter of each site. -/
structure CState where
  env : Env
  heap : Heap
  cnt : Site → Nat

/-- The entry state of a frame: bound variables hold their root objects, the heap is the default. -/
def CState.init (fr : Frame) : CState where
  env := fun x => (fr.root? x).map (fun r => .sym (.root r) [])
  heap := cdefault
  cnt := fun _ => 0

/-- Set variable `x` to `v`. -/
def CState.setVar (st : CState) (x : Var) (v : Val) : CState :=
  { st with env := fupd st.env x v }

/-- Set cell `c` of object `o` to `v`. -/
def CState.setCell (st : CState) (o : Obj) (c : Cell) (v : Val) : CState :=
  { st with heap := fupd2 st.heap o c v }

/-- Add one to the counter of site `s`. -/
def CState.bump (st : CState) (s : Site) : CState :=
  { st with cnt := fupd st.cnt s (st.cnt s + 1) }

/-- Set the optional result variable `ret` to `v`. -/
def CState.setRet (st : CState) (ret : Option Var) (v : Val) : CState :=
  match ret with
  | none => st
  | some x => st.setVar x v

/-- Follow path `p` from object `o` in heap `h`. The result is `none` if a step reads null. -/
def readPath (h : Heap) (o : Obj) : List Cell → Val
  | [] => some o
  | c :: cs => (h o c).bind (fun o' => readPath h o' cs)

/-- The value of access path `x.p` in state `st`. The result is `none` for null. -/
def evalPath (st : CState) (x : Var) (p : List Cell) : Val :=
  (st.env x).bind (fun o => readPath st.heap o p)

/-- Object `o` is reachable for a call with arguments `args`:
it is outer, or an argument holds it, or a cell of a reachable object holds it. -/
inductive Reach (st : CState) (args : List Var) : Obj → Prop where
  | outer {b : Base} {p : List Cell} : Reach st args (.sym b p)
  | arg {x : Var} {o : Obj} : x ∈ args → st.env x = some o → Reach st args o
  | step {o o' : Obj} {c : Cell} : Reach st args o → st.heap o c = some o' → Reach st args o'

/-- The heap `h'` is a possible result of the `n`-th execution of call site `s` (A2):
each cell keeps its value, or a cell of a reachable object gets a fresh havoc object. -/
def Havoc (st : CState) (args : List Var) (s : Site) (n : Nat) (h' : Heap) : Prop :=
  ∀ o c, h' o c = st.heap o c ∨
    (Reach st args o ∧ ∃ k, h' o c = some (.sym (.havoc s n k) []))

/-- One statement step. A dereference of null blocks (exceptions are out of scope). -/
inductive SStep : Stmt → CState → CState → Prop where
  | new {x s st} :
      SStep (.new x s) st ((st.setVar x (some (.alloc s (st.cnt s)))).bump s)
  | null {x st} : SStep (.null x) st (st.setVar x none)
  | copy {x y st} : SStep (.copy x y) st (st.setVar x (st.env y))
  | load {x y f st o} : st.env y = some o →
      SStep (.load x y f) st (st.setVar x (st.heap o (.fld f)))
  | store {x f y st o} : st.env x = some o →
      SStep (.store x f y) st (st.setCell o (.fld f) (st.env y))
  | aload {x y st o} (i : Nat) : st.env y = some o →
      SStep (.aload x y) st (st.setVar x (st.heap o (.elem i)))
  | astore {x y st o} (i : Nat) : st.env x = some o →
      SStep (.astore x y) st (st.setCell o (.elem i) (st.env y))
  | unknown {x s st} :
      SStep (.unknown x s) st ((st.setVar x (some (.sym (.fresh s (st.cnt s)) []))).bump s)
  | call {ret s args st h'} : Havoc st args s (st.cnt s) h' →
      SStep (.call ret s args) st
        (({ st with heap := h' }.setRet ret (some (.sym (.fresh s (st.cnt s)) []))).bump s)

/-- Big-step execution of a program. -/
inductive Exec : Prog → CState → CState → Prop where
  | skip {s} : Exec .skip s s
  | stmt {st s s'} : SStep st s s' → Exec (.stmt st) s s'
  | seq {p q s t u} : Exec p s t → Exec q t u → Exec (.seq p q) s u
  | choiceL {p q s t} : Exec p s t → Exec (.choice p q) s t
  | choiceR {p q s t} : Exec q s t → Exec (.choice p q) s t
  | loopZero {p s} : Exec (.loop p) s s
  | loopMore {p s t u} : Exec p s t → Exec (.loop p) t u → Exec (.loop p) s u

/-! ## Alias predicates -/

/-- In state `st`, the paths `x.px` and `y.py` evaluate to the same object. -/
def AliasIn (st : CState) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ o, evalPath st x px = some o ∧ evalPath st y py = some o

/-- The Boolean form of `AliasIn`. -/
def aliasInB (st : CState) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Bool :=
  match evalPath st x px with
  | some o => decide (evalPath st y py = some o)
  | none => false

/-- `aliasInB` decides `AliasIn`. -/
theorem aliasInB_iff {st : CState} {x y : Var} {px py : List Cell} :
    aliasInB st x px y py = true ↔ AliasIn st x px y py := by
  unfold aliasInB AliasIn
  cases h : evalPath st x px with
  | none => simp
  | some o => simp

/-- One-execution alias: one execution of `p` from the frame entry makes `x.px` and `y.py`
the same object at the end. -/
def CAlias (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ st, Exec p (CState.init fr) st ∧ AliasIn st x px y py

/-- Cross-execution alias: `x.px` at the end of one execution and `y.py` at the end of a
second execution are the same object. -/
def CAliasX (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Prop :=
  ∃ s1 s2 o, Exec p (CState.init fr) s1 ∧ Exec p (CState.init fr) s2 ∧
    evalPath s1 x px = some o ∧ evalPath s2 y py = some o

/-- A one-execution alias is also a cross-execution alias. -/
theorem CAlias.toX {fr : Frame} {p : Prog} {x y : Var} {px py : List Cell}
    (h : CAlias fr p x px y py) : CAliasX fr p x px y py := by
  obtain ⟨st, hex, o, h1, h2⟩ := h
  exact ⟨st, st, o, hex, hex, h1, h2⟩

/-! ## Deterministic executor with explicit choices -/

/-- The start object of a havoc write: an argument variable, or an outer object. -/
inductive HStart where
  | arg (x : Var)
  | outer (o : Obj)
  deriving DecidableEq, Repr

/-- One havoc write of a call: follow `path` from `start`, then write a fresh havoc object
with tag `k` into `cell`. The start and the path prove that the target is reachable. -/
structure HavocW where
  start : HStart
  path : List Cell
  cell : Cell
  k : Nat
  deriving DecidableEq, Repr

/-- One explicit choice for `run`. -/
inductive Choice where
  /-- Take the left branch of a `choice`. -/
  | left
  /-- Take the right branch of a `choice`. -/
  | right
  /-- Run a loop body `n` times. -/
  | iter (n : Nat)
  /-- Use array index `i` for `aload` or `astore`. -/
  | idx (i : Nat)
  /-- Do these havoc writes at a call. -/
  | havoc (ws : List HavocW)
  deriving DecidableEq, Repr

/-- The start object of a havoc write in the pre-call state, if it is valid. -/
def HStart.obj (st : CState) (args : List Var) : HStart → Val
  | .arg x => if x ∈ args then st.env x else none
  | .outer o => if o.isOuter then some o else none

/-- The target object of a havoc write in the pre-call state. -/
def HavocW.target (st : CState) (args : List Var) (w : HavocW) : Val :=
  (w.start.obj st args).bind (fun o => readPath st.heap o w.path)

/-- Apply havoc writes to heap `h`. The targets come from the pre-call state `st`. -/
def applyHavoc (st : CState) (args : List Var) (s n : Nat) (h : Heap) : List HavocW → Option Heap
  | [] => some h
  | w :: ws =>
    match w.target st args with
    | some o => applyHavoc st args s n (fupd2 h o w.cell (some (.sym (.havoc s n w.k) []))) ws
    | none => none

/-- Run one statement. It uses the head choice for `aload`, `astore` and `call`. -/
def runStmt : Stmt → List Choice → CState → Option (CState × List Choice)
  | .new x s, cs, st => some ((st.setVar x (some (.alloc s (st.cnt s)))).bump s, cs)
  | .null x, cs, st => some (st.setVar x none, cs)
  | .copy x y, cs, st => some (st.setVar x (st.env y), cs)
  | .load x y f, cs, st =>
    match st.env y with
    | some o => some (st.setVar x (st.heap o (.fld f)), cs)
    | none => none
  | .store x f y, cs, st =>
    match st.env x with
    | some o => some (st.setCell o (.fld f) (st.env y), cs)
    | none => none
  | .aload x y, .idx i :: cs, st =>
    match st.env y with
    | some o => some (st.setVar x (st.heap o (.elem i)), cs)
    | none => none
  | .astore x y, .idx i :: cs, st =>
    match st.env x with
    | some o => some (st.setCell o (.elem i) (st.env y), cs)
    | none => none
  | .unknown x s, cs, st =>
    some ((st.setVar x (some (.sym (.fresh s (st.cnt s)) []))).bump s, cs)
  | .call ret s args, .havoc ws :: cs, st =>
    match applyHavoc st args s (st.cnt s) st.heap ws with
    | some h' =>
      some ((({ st with heap := h' }.setRet ret (some (.sym (.fresh s (st.cnt s)) []))).bump s), cs)
    | none => none
  | _, _, _ => none

/-- Run `f` `n` times, and pass the rest of the choices along. -/
def runN (f : List Choice → CState → Option (CState × List Choice)) :
    Nat → List Choice → CState → Option (CState × List Choice)
  | 0, cs, st => some (st, cs)
  | n + 1, cs, st =>
    match f cs st with
    | some (t, cs') => runN f n cs' t
    | none => none

/-- Run a program with explicit choices. It gives the final state and the unused choices. -/
def run : Prog → List Choice → CState → Option (CState × List Choice)
  | .skip, cs, st => some (st, cs)
  | .stmt s, cs, st => runStmt s cs st
  | .seq p q, cs, st =>
    match run p cs st with
    | some (t, cs') => run q cs' t
    | none => none
  | .choice p _, .left :: cs, st => run p cs st
  | .choice _ q, .right :: cs, st => run q cs st
  | .loop p, .iter n :: cs, st => runN (run p) n cs st
  | _, _, _ => none

/-- Run a program from the frame entry, and give the final state if the run succeeds. -/
def runFrom (fr : Frame) (p : Prog) (cs : List Choice) : Option CState :=
  (run p cs (CState.init fr)).map Prod.fst

/-- One-execution alias check of a run: the run succeeds and the two paths are the same object. -/
def runAliasB (fr : Frame) (p : Prog) (cs : List Choice)
    (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Bool :=
  match runFrom fr p cs with
  | some st => aliasInB st x px y py
  | none => false

/-! ## The executor agrees with `Exec` -/

/-- A reachable object stays reachable along a path. -/
theorem Reach.readPath {st : CState} {args : List Var} {o o' : Obj} :
    ∀ {p : List Cell}, Reach st args o → DirectedAlias.readPath st.heap o p = some o' →
      Reach st args o'
  | [], h, hp => by
    simp only [DirectedAlias.readPath, Option.some.injEq] at hp; exact hp ▸ h
  | c :: cs, h, hp => by
    simp only [DirectedAlias.readPath] at hp
    cases hc : st.heap o c with
    | none => rw [hc] at hp; cases hp
    | some o1 =>
      rw [hc] at hp
      exact Reach.readPath (Reach.step h hc) hp

/-- The target of a valid havoc write is reachable. -/
theorem HavocW.target_reach {st : CState} {args : List Var} {w : HavocW} {o : Obj}
    (h : w.target st args = some o) : Reach st args o := by
  unfold HavocW.target at h
  cases hs : w.start.obj st args with
  | none => rw [hs] at h; cases h
  | some o0 =>
    rw [hs] at h
    apply Reach.readPath _ h
    cases hw : w.start with
    | arg x =>
      rw [hw] at hs; simp only [HStart.obj] at hs
      split at hs
      · exact Reach.arg (by assumption) hs
      · cases hs
    | outer o1 =>
      rw [hw] at hs; simp only [HStart.obj] at hs
      split at hs
      · rename_i hout
        cases hs
        cases o0 with
        | sym b p => exact Reach.outer
        | alloc _ _ => simp [Obj.isOuter] at hout
      · cases hs

/-- `applyHavoc` keeps the havoc invariant. -/
theorem applyHavoc_spec {st : CState} {args : List Var} {s n : Nat} :
    ∀ {ws : List HavocW} {h h' : Heap},
      (∀ o c, h o c = st.heap o c ∨
        (Reach st args o ∧ ∃ k, h o c = some (.sym (.havoc s n k) []))) →
      applyHavoc st args s n h ws = some h' → Havoc st args s n h'
  | [], h, h', hinv, hr => by
    simp only [applyHavoc, Option.some.injEq] at hr; exact hr ▸ hinv
  | w :: ws, h, h', hinv, hr => by
    simp only [applyHavoc] at hr
    cases ht : w.target st args with
    | none => rw [ht] at hr; cases hr
    | some o =>
      rw [ht] at hr
      apply applyHavoc_spec _ hr
      intro o' c'
      by_cases he : o' = o ∧ c' = w.cell
      · obtain ⟨rfl, rfl⟩ := he
        right
        exact ⟨HavocW.target_reach ht, w.k, by simp⟩
      · rw [fupd2_ne _ _ he]; exact hinv o' c'

/-- `runStmt` agrees with `SStep`. -/
theorem runStmt_sound {st : Stmt} {cs cs' : List Choice} {s s' : CState}
    (h : runStmt st cs s = some (s', cs')) : SStep st s s' := by
  cases st with
  | new x a => simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .new
  | null x => simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .null
  | copy x y => simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .copy
  | load x y f =>
    simp only [runStmt] at h
    cases he : s.env y with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .load he
  | store x f y =>
    simp only [runStmt] at h
    cases he : s.env x with
    | none => rw [he] at h; cases h
    | some o =>
      rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .store he
  | aload x y =>
    match cs, h with
    | .idx i :: cs, h =>
      simp only [runStmt] at h
      cases he : s.env y with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .aload i he
  | astore x y =>
    match cs, h with
    | .idx i :: cs, h =>
      simp only [runStmt] at h
      cases he : s.env x with
      | none => rw [he] at h; cases h
      | some o =>
        rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .astore i he
  | unknown x a =>
    simp only [runStmt, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .unknown
  | call ret a args =>
    match cs, h with
    | .havoc ws :: cs, h =>
      simp only [runStmt] at h
      cases ha : applyHavoc s args a (s.cnt a) s.heap ws with
      | none => rw [ha] at h; cases h
      | some h' =>
        rw [ha] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .call (applyHavoc_spec (fun _ _ => Or.inl rfl) ha)

/-- `runN` of a sound runner gives a loop execution. -/
theorem runN_sound {p : Prog} {f : List Choice → CState → Option (CState × List Choice)}
    (hf : ∀ {cs cs' s s'}, f cs s = some (s', cs') → Exec p s s') :
    ∀ {n : Nat} {cs cs' : List Choice} {s s' : CState},
      runN f n cs s = some (s', cs') → Exec (.loop p) s s'
  | 0, cs, cs', s, s', h => by
    simp only [runN, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .loopZero
  | n + 1, cs, cs', s, s', h => by
    simp only [runN] at h
    cases hr : f cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .loopMore (hf hr) (runN_sound hf h)

/-- `run` agrees with `Exec`: a successful run is an execution. -/
theorem run_sound : ∀ {p : Prog} {cs cs' : List Choice} {s s' : CState},
    run p cs s = some (s', cs') → Exec p s s'
  | .skip, cs, cs', s, s', h => by
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .skip
  | .stmt st, cs, cs', s, s', h => by
    simp only [run] at h; exact .stmt (runStmt_sound h)
  | .seq p q, cs, cs', s, s', h => by
    simp only [run] at h
    cases hr : run p cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .seq (run_sound hr) (run_sound h)
  | .choice p q, .left :: cs, cs', s, s', h => by
    simp only [run] at h; exact .choiceL (run_sound h)
  | .choice p q, .right :: cs, cs', s, s', h => by
    simp only [run] at h; exact .choiceR (run_sound h)
  | .loop p, .iter n :: cs, cs', s, s', h => by
    simp only [run] at h; exact runN_sound (fun hr => run_sound hr) h

/-- A run from the frame entry is an execution from the frame entry. -/
theorem runFrom_sound {fr : Frame} {p : Prog} {cs : List Choice} {st : CState}
    (h : runFrom fr p cs = some st) : Exec p (CState.init fr) st := by
  unfold runFrom at h
  cases hr : run p cs (CState.init fr) with
  | none => rw [hr] at h; cases h
  | some r =>
    obtain ⟨t, cs'⟩ := r
    rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
    exact h ▸ run_sound hr

/-- A successful alias check of a run proves a one-execution alias. -/
theorem runAliasB_sound {fr : Frame} {p : Prog} {cs : List Choice}
    {x y : Var} {px py : List Cell} (h : runAliasB fr p cs x px y py = true) :
    CAlias fr p x px y py := by
  unfold runAliasB at h
  cases hr : runFrom fr p cs with
  | none => rw [hr] at h; cases h
  | some st =>
    rw [hr] at h
    exact ⟨st, runFrom_sound hr, aliasInB_iff.mp h⟩

end DirectedAlias
