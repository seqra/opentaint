import DirectedAlias.Sound.CellNamed.Concept

/-!
# A deterministic executor for the strict narrow semantics

`runN` is `run` (`Concrete.lean`) with a narrow call: a havoc write starts at an argument or
at the entry object of a static root, and the tag of the write must decode to its target cell
(`src k = (o, c)`). A successful run is an `ExecN` execution (`runN_sound`), so the alias
check `runAliasBN` gives executable witnesses (`runAliasBN_sound`).
-/

namespace DirectedAlias.Sound.CellNamed

open DirectedAlias

/-- The start object of a narrow havoc write: an argument value, or the entry object of a
static root. -/
def startN (st : CState) (statics : List Root) (args : List Var) : HStart → Val
  | .arg x => if x ∈ args then st.env x else none
  | .outer (.sym (.root r) []) => if r ∈ statics then some (.sym (.root r) []) else none
  | .outer _ => none

/-- The target object of a narrow havoc write in the pre-call state. -/
def targetN (st : CState) (statics : List Root) (args : List Var) (w : HavocW) : Val :=
  (startN st statics args w.start).bind (fun o => readPath st.heap o w.path)

/-- Apply narrow havoc writes to heap `h`. The targets come from the pre-call state `st`.
The tag of each write must decode to its target cell. -/
def applyHavocN (src : Nat → Obj × Cell) (st : CState) (statics : List Root) (args : List Var)
    (s n : Nat) (h : Heap) : List HavocW → Option Heap
  | [] => some h
  | w :: ws =>
    match targetN st statics args w with
    | some o =>
      if src w.k = (o, w.cell) then
        applyHavocN src st statics args s n (fupd2 h o w.cell (some (.sym (.havoc s n w.k) []))) ws
      else none
    | none => none

/-- Run one statement with the narrow call. -/
def runStmtN (src : Nat → Obj × Cell) (statics : List Root) :
    Stmt → List Choice → CState → Option (CState × List Choice)
  | .call ret s args, .havoc ws :: cs, st =>
    match applyHavocN src st statics args s (st.cnt s) st.heap ws with
    | some h' =>
      some ((({ st with heap := h' }.setRet ret (some (.sym (.fresh s (st.cnt s)) []))).bump s), cs)
    | none => none
  | .call _ _ _, _, _ => none
  | st, cs, s => runStmt st cs s

/-- Run a program with explicit choices and the narrow call. -/
def runP (src : Nat → Obj × Cell) (statics : List Root) :
    Prog → List Choice → CState → Option (CState × List Choice)
  | .skip, cs, st => some (st, cs)
  | .stmt s, cs, st => runStmtN src statics s cs st
  | .seq p q, cs, st =>
    match runP src statics p cs st with
    | some (t, cs') => runP src statics q cs' t
    | none => none
  | .choice p _, .left :: cs, st => runP src statics p cs st
  | .choice _ q, .right :: cs, st => runP src statics q cs st
  | .loop p, .iter n :: cs, st => runN (runP src statics p) n cs st
  | _, _, _ => none

/-- One-execution alias check of a narrow run from the frame entry. -/
def runAliasBN (src : Nat → Obj × Cell) (statics : List Root) (fr : Frame) (p : Prog)
    (cs : List Choice) (x : Var) (px : List Cell) (y : Var) (py : List Cell) : Bool :=
  match runP src statics p cs (CState.init fr) with
  | some (st, _) => aliasInB st x px y py
  | none => false

/-- A narrow-reachable object stays narrow-reachable along a path. -/
theorem ReachN.readPath {st : CState} {statics : List Root} {args : List Var} {o o' : Obj} :
    ∀ {p : List Cell}, ReachN st statics args o → DirectedAlias.readPath st.heap o p = some o' →
      ReachN st statics args o'
  | [], h, hp => by
    simp only [DirectedAlias.readPath, Option.some.injEq] at hp; exact hp ▸ h
  | c :: cs, h, hp => by
    simp only [DirectedAlias.readPath] at hp
    cases hc : st.heap o c with
    | none => rw [hc] at hp; cases hp
    | some o1 =>
      rw [hc] at hp
      exact ReachN.readPath (ReachN.step h hc) hp

/-- The target of a valid narrow havoc write is narrow-reachable. -/
theorem targetN_reach {st : CState} {statics : List Root} {args : List Var} {w : HavocW}
    {o : Obj} (h : targetN st statics args w = some o) : ReachN st statics args o := by
  unfold targetN at h
  cases hs : startN st statics args w.start with
  | none => rw [hs] at h; cases h
  | some o0 =>
    rw [hs] at h
    apply ReachN.readPath _ h
    cases hw : w.start with
    | arg x =>
      rw [hw] at hs; simp only [startN] at hs
      split at hs
      · exact ReachN.arg (by assumption) hs
      · cases hs
    | outer o1 =>
      rw [hw] at hs
      match o1, hs with
      | .sym (.root r) [], hs =>
        simp only [startN] at hs
        split at hs
        · cases hs; exact ReachN.static (by assumption)
        · cases hs

/-- `applyHavocN` gives a strict narrow havoc. -/
theorem applyHavocN_spec {src : Nat → Obj × Cell} {st : CState} {statics : List Root}
    {args : List Var} {s n : Nat} :
    ∀ {ws : List HavocW} {h h' : Heap},
      (∀ o c, h o c = st.heap o c ∨ (ReachN st statics args o ∧
        ∃ k, src k = (o, c) ∧ h o c = some (.sym (.havoc s n k) []))) →
      applyHavocN src st statics args s n h ws = some h' → HavocN src statics st args s n h'
  | [], h, h', hinv, hr => by
    simp only [applyHavocN, Option.some.injEq] at hr; exact hr ▸ hinv
  | w :: ws, h, h', hinv, hr => by
    simp only [applyHavocN] at hr
    cases ht : targetN st statics args w with
    | none => rw [ht] at hr; cases hr
    | some o =>
      rw [ht] at hr
      simp only at hr
      split at hr
      · rename_i hk
        apply applyHavocN_spec _ hr
        intro o' c'
        by_cases he : o' = o ∧ c' = w.cell
        · obtain ⟨rfl, rfl⟩ := he
          right
          exact ⟨targetN_reach ht, w.k, hk, by simp⟩
        · rw [fupd2_ne _ _ he]; exact hinv o' c'
      · cases hr

/-- `runStmtN` agrees with `SStepN`. -/
theorem runStmtN_sound {src : Nat → Obj × Cell} {statics : List Root} {st : Stmt}
    {cs cs' : List Choice} {s s' : CState} (h : runStmtN src statics st cs s = some (s', cs')) :
    SStepN src statics st s s' := by
  cases st with
  | call ret a args =>
    match cs, h with
    | .havoc ws :: cs, h =>
      simp only [runStmtN] at h
      cases ha : applyHavocN src s statics args a (s.cnt a) s.heap ws with
      | none => rw [ha] at h; cases h
      | some h' =>
        rw [ha] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        exact .call (applyHavocN_spec (fun _ _ => Or.inl rfl) ha)
  | new x a =>
    have := runStmt_sound (st := .new x a) h
    cases this; exact .new
  | null x => have := runStmt_sound (st := .null x) h; cases this; exact .null
  | copy x y => have := runStmt_sound (st := .copy x y) h; cases this; exact .copy
  | load x y f => have := runStmt_sound (st := .load x y f) h; cases this; exact .load (by assumption)
  | store x f y => have := runStmt_sound (st := .store x f y) h; cases this; exact .store (by assumption)
  | aload x y =>
    have := runStmt_sound (st := .aload x y) h
    cases this with | aload i he => exact .aload i he
  | astore x y =>
    have := runStmt_sound (st := .astore x y) h
    cases this with | astore i he => exact .astore i he
  | unknown x a => have := runStmt_sound (st := .unknown x a) h; cases this; exact .unknown

/-- `runN` of a sound narrow runner gives a narrow loop execution. -/
theorem runN_soundN {src : Nat → Obj × Cell} {statics : List Root} {p : Prog}
    {f : List Choice → CState → Option (CState × List Choice)}
    (hf : ∀ {cs cs' s s'}, f cs s = some (s', cs') → ExecN src statics p s s') :
    ∀ {n : Nat} {cs cs' : List Choice} {s s' : CState},
      runN f n cs s = some (s', cs') → ExecN src statics (.loop p) s s'
  | 0, cs, cs', s, s', h => by
    simp only [runN, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .loopZero
  | n + 1, cs, cs', s, s', h => by
    simp only [runN] at h
    cases hr : f cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .loopMore (hf hr) (runN_soundN hf h)

/-- `runP` agrees with `ExecN`: a successful narrow run is a narrow execution. -/
theorem runP_sound {src : Nat → Obj × Cell} {statics : List Root} :
    ∀ {p : Prog} {cs cs' : List Choice} {s s' : CState},
      runP src statics p cs s = some (s', cs') → ExecN src statics p s s'
  | .skip, cs, cs', s, s', h => by
    simp only [runP, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact .skip
  | .stmt st, cs, cs', s, s', h => by
    simp only [runP] at h; exact .stmt (runStmtN_sound h)
  | .seq p q, cs, cs', s, s', h => by
    simp only [runP] at h
    cases hr : runP src statics p cs s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨t, cs1⟩ := r
      rw [hr] at h
      exact .seq (runP_sound hr) (runP_sound h)
  | .choice p q, .left :: cs, cs', s, s', h => by
    simp only [runP] at h; exact .choiceL (runP_sound h)
  | .choice p q, .right :: cs, cs', s, s', h => by
    simp only [runP] at h; exact .choiceR (runP_sound h)
  | .loop p, .iter n :: cs, cs', s, s', h => by
    simp only [runP] at h; exact runN_soundN (fun hr => runP_sound hr) h

/-- A successful narrow alias check proves a strict narrow one-execution alias. -/
theorem runAliasBN_sound {src : Nat → Obj × Cell} {statics : List Root} {fr : Frame}
    {p : Prog} {cs : List Choice} {x y : Var} {px py : List Cell}
    (h : runAliasBN src statics fr p cs x px y py = true) : CAliasN src statics fr p x px y py := by
  unfold runAliasBN at h
  cases hr : runP src statics p cs (CState.init fr) with
  | none => rw [hr] at h; cases h
  | some r =>
    obtain ⟨st, cs'⟩ := r
    rw [hr] at h
    exact ⟨st, runP_sound hr, aliasInB_iff.mp h⟩

/-- A naming of tags from a list: tag `k` decodes to the `k`-th cell of the list. -/
def srcL (l : List (Obj × Cell)) (k : Nat) : Obj × Cell :=
  l.getD k (.sym (.root 0) [], .fld 0)

end DirectedAlias.Sound.CellNamed
