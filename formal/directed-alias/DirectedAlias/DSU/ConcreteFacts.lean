import DirectedAlias.Concrete

/-!
# Facts about the concrete semantics

Generic invariant lemmas for `Exec`. The DSU examples use them to prove that NO execution
gives an alias.
-/

namespace DirectedAlias.DSU

open DirectedAlias

/-- The variables that a statement writes. -/
def stmtDefs : Stmt → List Var
  | .new x _ => [x]
  | .null x => [x]
  | .copy x _ => [x]
  | .load x _ _ => [x]
  | .aload x _ => [x]
  | .unknown x _ => [x]
  | .call ret _ _ => ret.toList
  | _ => []

/-- A state property that each statement of `p` keeps is kept by each execution of `p`. -/
theorem exec_preserve (Q : CState → Prop) :
    ∀ {p : Prog} {s t : CState}, Exec p s t →
      (∀ st ∈ p.stmts, ∀ s1 t1, SStep st s1 t1 → Q s1 → Q t1) → Q s → Q t := by
  intro p s t h
  induction h with
  | skip => intro _ hq; exact hq
  | stmt hs => intro hst hq; exact hst _ (by simp [Prog.stmts]) _ _ hs hq
  | seq _ _ ih1 ih2 =>
    intro hst hq
    exact ih2 (fun st m => hst st (by simp [Prog.stmts, m])) (ih1 (fun st m => hst st (by simp [Prog.stmts, m])) hq)
  | choiceL _ ih => intro hst hq; exact ih (fun st m => hst st (by simp [Prog.stmts, m])) hq
  | choiceR _ ih => intro hst hq; exact ih (fun st m => hst st (by simp [Prog.stmts, m])) hq
  | loopZero => intro _ hq; exact hq
  | loopMore _ _ ih1 ih2 =>
    intro hst hq
    exact ih2 hst (ih1 (fun st m => hst st (by simpa [Prog.stmts] using m)) hq)

/-- A loop keeps each property that one run of its body keeps. -/
theorem exec_loop_inv (Q : CState → Prop) {p : Prog}
    (hb : ∀ s t, Q s → Exec p s t → Q t) :
    ∀ {q : Prog} {s u : CState}, Exec q s u → q = .loop p → Q s → Q u := by
  intro q s u h
  induction h with
  | loopZero => intro _ hq; exact hq
  | loopMore h1 _ _ ih2 =>
    intro heq hq
    cases heq
    exact ih2 rfl (hb _ _ hq h1)
  | _ => intro heq; cases heq

/-- A statement that does not write `x` keeps the value of `x`. -/
theorem sstep_env_keep {st : Stmt} {s t : CState} {x : Var} (h : SStep st s t)
    (hx : x ∉ stmtDefs st) : t.env x = s.env x := by
  cases h <;> simp_all [stmtDefs, CState.setVar, CState.bump, CState.setCell, CState.setRet, fupd]
  case call ret _ _ _ _ =>
    cases ret with
    | none => rfl
    | some r =>
      have : x ≠ r := fun he => hx (by rw [he])
      simp [fupd, this]

/-- A program that does not write `x` keeps the value of `x`. -/
theorem exec_env_keep {p : Prog} {s t : CState} {x : Var} (h : Exec p s t)
    (hx : ∀ st ∈ p.stmts, x ∉ stmtDefs st) : t.env x = s.env x := by
  have := exec_preserve (fun u => u.env x = s.env x) h
    (fun st m s1 t1 hs hq => (sstep_env_keep hs (hx st m)).trans hq) rfl
  exact this

end DirectedAlias.DSU
