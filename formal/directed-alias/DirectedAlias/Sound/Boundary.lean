import DirectedAlias.Sound.NullSafe
import DirectedAlias.Examples

/-!
# The boundary of the completeness scope

Each counterexample is a program outside the scope `CoreScope`, a `decide` proof that `mayProg`
is true, and a proof that no two executions make the two concrete paths the same object
(`NoCrossAlias`). Each one breaks exactly one condition of the scope.

For loop-free programs without arrays and calls, `noCrossB` decides `NoCrossAlias`:
it runs every choice list of the program (`choicesOf`), and `run_complete` proves that these
runs cover every execution.
-/

namespace DirectedAlias.Sound.Boundary

open DirectedAlias DirectedAlias.Sound

/-- No two executions make concrete paths, which abstract to the query paths, the same object. -/
def NoCrossAlias (fr : Frame) (p : Prog) (x : Var) (px : List ACell) (y : Var)
    (py : List ACell) : Prop :=
  ¬ ∃ cx cy, cx.map Cell.abs = px ∧ cy.map Cell.abs = py ∧ CAliasX fr p x cx y cy

/-- A concrete path that abstracts to a path without array elements is its canonical path. -/
theorem path_of_abs {cx : List Cell} {q : List ACell} (h : cx.map Cell.abs = q)
    (hq : ACell.elem ∉ q) : cx = q.map canon := by
  apply map_abs_inj
  · rw [h, canon_abs]
  · rw [h]; exact hq

/-- An invariant of each run of the loop body is an invariant of the loop. -/
theorem loop_inv {body : Prog} (P : CState → Prop) (hstep : ∀ s t, P s → Exec body s t → P t) :
    ∀ {s u : CState}, Exec (.loop body) s u → P s → P u := by
  intro s u hx
  generalize hq : Prog.loop body = q at hx
  induction hx with
  | skip => intro h; exact h
  | stmt _ => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopZero => intro h; exact h
  | loopMore h1 _ _ ih2 => cases hq; intro hp; exact ih2 rfl (hstep _ _ hp h1)


/-! ## A decision procedure for loop-free programs without arrays and calls -/

/-- A statement that uses no choice: no array access and no call. -/
def plainS : Stmt → Bool
  | .aload _ _ => false
  | .astore _ _ => false
  | .call _ _ _ => false
  | _ => true

/-- A loop-free program whose statements use no choice. -/
def plainP : Prog → Bool
  | .skip => true
  | .stmt st => plainS st
  | .seq p q => plainP p && plainP q
  | .choice p q => plainP p && plainP q
  | .loop _ => false

/-- All choice lists of a loop-free program without arrays and calls. -/
def choicesOf : Prog → List (List Choice)
  | .skip => [[]]
  | .stmt _ => [[]]
  | .seq p q => (choicesOf p).flatMap (fun c1 => (choicesOf q).map (c1 ++ ·))
  | .choice p q => (choicesOf p).map (Choice.left :: ·) ++ (choicesOf q).map (Choice.right :: ·)
  | .loop _ => []

/-- A step of a statement without choices is a run that uses no choice. -/
theorem runStmt_complete {st : Stmt} {s u : CState} (hp : plainS st = true) (h : SStep st s u)
    (r : List Choice) : runStmt st r s = some (u, r) := by
  cases h with
  | new => rfl
  | null => rfl
  | copy => rfl
  | load he => simp only [runStmt, he]
  | store he => simp only [runStmt, he]
  | unknown => rfl
  | aload _ _ => simp [plainS] at hp
  | astore _ _ => simp [plainS] at hp
  | call _ => simp [plainS] at hp

/-- Each execution of a loop-free program without arrays and calls is a run of one of its
choice lists. -/
theorem run_complete {p : Prog} {s u : CState} (h : Exec p s u) :
    plainP p = true → ∀ r, ∃ cs ∈ choicesOf p, run p (cs ++ r) s = some (u, r) := by
  induction h with
  | skip => intro _ r; exact ⟨[], List.mem_singleton.mpr rfl, rfl⟩
  | stmt hs =>
    intro hp r
    exact ⟨[], List.mem_singleton.mpr rfl, runStmt_complete hp hs r⟩
  | seq _ _ ih1 ih2 =>
    intro hp r
    simp only [plainP, Bool.and_eq_true] at hp
    obtain ⟨c2, hc2, hr2⟩ := ih2 hp.2 r
    obtain ⟨c1, hc1, hr1⟩ := ih1 hp.1 (c2 ++ r)
    refine ⟨c1 ++ c2, List.mem_flatMap.mpr ⟨c1, hc1, List.mem_map.mpr ⟨c2, hc2, rfl⟩⟩, ?_⟩
    simp only [run, List.append_assoc, hr1, hr2]
  | choiceL _ ih =>
    intro hp r
    simp only [plainP, Bool.and_eq_true] at hp
    obtain ⟨c, hc, hr⟩ := ih hp.1 r
    exact ⟨Choice.left :: c, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨c, hc, rfl⟩)), hr⟩
  | choiceR _ ih =>
    intro hp r
    simp only [plainP, Bool.and_eq_true] at hp
    obtain ⟨c, hc, hr⟩ := ih hp.2 r
    exact ⟨Choice.right :: c, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c, hc, rfl⟩)), hr⟩
  | loopZero => intro hp; simp [plainP] at hp
  | loopMore _ _ _ _ => intro hp; simp [plainP] at hp

/-- Boolean test: both values are the same object. -/
def sameB (v w : Val) : Bool :=
  match v with
  | some o => decide (w = some o)
  | none => false

/-- Boolean test over all pairs of runs: no pair makes the two paths the same object. -/
def noCrossB (fr : Frame) (p : Prog) (x : Var) (cx : List Cell) (y : Var) (cy : List Cell) : Bool :=
  (choicesOf p).all fun c1 => (choicesOf p).all fun c2 =>
    match runFrom fr p c1, runFrom fr p c2 with
    | some s1, some s2 => !sameB (evalPath s1 x cx) (evalPath s2 y cy)
    | _, _ => true

/-- `noCrossB` proves `NoCrossAlias` for loop-free programs without arrays and calls. -/
theorem noCrossB_sound {fr : Frame} {p : Prog} {x y : Var} {px py : List ACell}
    (hp : plainP p = true) (hx : ACell.elem ∉ px) (hy : ACell.elem ∉ py)
    (h : noCrossB fr p x (px.map canon) y (py.map canon) = true) : NoCrossAlias fr p x px y py := by
  rintro ⟨cx, cy, hcx, hcy, s1, s2, o, h1, h2, e1, e2⟩
  rw [path_of_abs hcx hx] at e1
  rw [path_of_abs hcy hy] at e2
  obtain ⟨c1, hc1, hr1⟩ := run_complete h1 hp []
  obtain ⟨c2, hc2, hr2⟩ := run_complete h2 hp []
  rw [List.append_nil] at hr1 hr2
  have hf1 : runFrom fr p c1 = some s1 := by simp [runFrom, hr1]
  have hf2 : runFrom fr p c2 = some s2 := by simp [runFrom, hr2]
  have := List.all_eq_true.mp (List.all_eq_true.mp h c1 hc1) c2 hc2
  rw [hf1, hf2] at this
  simp only [e1, e2, sameB, decide_true, Bool.not_true] at this
  cases this

/-- Variable `x`. -/
abbrev vx : Var := 0
/-- Variable `y`. -/
abbrev vy : Var := 1
/-- Variable `z`. -/
abbrev vz : Var := 2
/-- Variable `a`. -/
abbrev va : Var := 3
/-- Variable `t`. -/
abbrev vt : Var := 4
/-- Variable `e`. -/
abbrev ve : Var := 5
/-- Variable `u`. -/
abbrev vu : Var := 6
/-- Field `f`. -/
abbrev ff : Field := 0
/-- Field `g`. -/
abbrev fg : Field := 1

/-- The frame: `x`, `y`, `z` hold the roots 0, 1, 2. -/
def fr3 : Frame := ⟨[(vx, 0), (vy, 1), (vz, 2)]⟩

/-! ## B1: the depth limit -/

/-- With `K = 1`, `x.f.f` and `x.f.f.f` share the deep origin. -/
theorem deep_may :
    mayProg 1 fr3 .skip vx [.fld ff, .fld ff] vx [.fld ff, .fld ff, .fld ff] = true := by
  decide

/-- No execution makes `x.f.f` and `x.f.f.f` the same object. -/
theorem deep_none :
    NoCrossAlias fr3 .skip vx [.fld ff, .fld ff] vx [.fld ff, .fld ff, .fld ff] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-! ## B2: a site that runs two times -/

/-- `x = new@7; y = new@7`. -/
def pTwice : Prog := .seq (.stmt (.new vx 7)) (.stmt (.new vy 7))

/-- Both objects of site 7 share the origin `alloc 7`. -/
theorem twice_may : mayProg 1 fr3 pTwice vx [] vy [] = true := by decide

/-- The two objects of site 7 are different in each execution. -/
theorem twice_none : NoCrossAlias fr3 pTwice vx [] vy [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-! ## B3: a null dereference that blocks one branch -/

/-- `if (*) { y = x; u = null } else { y = null; u = z }; t = y.f`. The right branch blocks. -/
def pBlock : Prog :=
  .seq (.choice (.seq (.stmt (.copy vy vx)) (.stmt (.null vu)))
                (.seq (.stmt (.null vy)) (.stmt (.copy vu vz))))
       (.stmt (.load vt vy ff))

/-- The analysis keeps `u = z` from the right branch. -/
theorem block_may : mayProg 2 fr3 pBlock vu [] vz [] = true := by decide

/-- Each complete execution takes the left branch, so `u` is null. -/
theorem block_none : NoCrossAlias fr3 pBlock vu [] vz [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-- The null check rejects this program. -/
theorem block_unsafe : nullSafeB fr3 pBlock = false := by decide

/-! ## B4: a strong store in one branch (correlated heap and control) -/

/-- `e = x.f; if (*) { x.f = z; a = x } else { a = y }; t = a.f`. -/
def pCorr : Prog :=
  .seq (.stmt (.load ve vx ff))
    (.seq (.choice (.seq (.stmt (.store vx ff vz)) (.stmt (.copy va vx))) (.stmt (.copy va vy)))
      (.stmt (.load vt va ff)))

/-- The analysis combines `a = x` from the left branch with the old `x.f` from the right branch. -/
theorem corr_may : mayProg 2 fr3 pCorr vt [] ve [] = true := by decide

/-- No execution makes `t` the entry value of `x.f`. -/
theorem corr_none : NoCrossAlias fr3 pCorr vt [] ve [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-! ## B5: a strong store, outside the branches, of a value with two origins -/

/-- `if (*) a = x else a = y; x.f = a`. The store is strong. -/
def pStrongTwo : Prog :=
  .seq (.choice (.stmt (.copy va vx)) (.stmt (.copy va vy))) (.stmt (.store vx ff va))

/-- The path `x.f.f` uses the cell `x.f` two times with two different values. -/
theorem strongTwo_may : mayProg 2 fr3 pStrongTwo vx [.fld ff, .fld ff] vy [] = true := by decide

/-- No execution makes `x.f.f` the object `y`. -/
theorem strongTwo_none : NoCrossAlias fr3 pStrongTwo vx [.fld ff, .fld ff] vy [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-- `if (*) a = x else a = y; x.f = a; x.g = a`: no cycle is necessary. -/
def pStrongTwoG : Prog :=
  .seq (.choice (.stmt (.copy va vx)) (.stmt (.copy va vy)))
    (.seq (.stmt (.store vx ff va)) (.stmt (.store vx fg va)))

/-- The path `x.f.g` combines `a = x` (for `x.f`) with `a = y` (for `x.g`). -/
theorem strongTwoG_may : mayProg 2 fr3 pStrongTwoG vx [.fld ff, .fld fg] vy [] = true := by decide

/-- No execution makes `x.f.g` the object `y`. -/
theorem strongTwoG_none : NoCrossAlias fr3 pStrongTwoG vx [.fld ff, .fld fg] vy [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-! ## B6: a weak store -/

/-- `if (*) a = x else a = y; a.f = y`. The store is weak. -/
def pWeak : Prog :=
  .seq (.choice (.stmt (.copy va vx)) (.stmt (.copy va vy))) (.stmt (.store va ff vy))

/-- The path `x.f.f` combines the write to `x.f` with the write to `y.f`. -/
theorem weak_may : mayProg 2 fr3 pWeak vx [.fld ff, .fld ff] vy [] = true := by decide

/-- No execution makes `x.f.f` the object `y`. -/
theorem weak_none : NoCrossAlias fr3 pWeak vx [.fld ff, .fld ff] vy [] :=
  noCrossB_sound rfl (by decide) (by decide) (by decide)

/-! ## B7: a loop (weak update of a summary allocation) -/

/-- The loop invariant of `loop { b = new@7; b.f = x; b.f = y }`. -/
def loopI (s : CState) : Prop :=
  s.env Examples.vx = some (.sym (.root 0) []) ∧ s.env Examples.vy = some (.sym (.root 1) []) ∧
    (s.env Examples.vb = none ∨
      ∃ n, s.env Examples.vb = some (.alloc 7 n) ∧
        s.heap (.alloc 7 n) (.fld Examples.ff) = some (.sym (.root 1) []))

/-- One run of the loop body keeps the loop invariant. -/
theorem loopI_step (s t : CState) (h : loopI s) (hx : Exec Examples.pStrong s t) : loopI t := by
  obtain ⟨hx0, hy0, _⟩ := h
  cases hx with
  | seq ha hb =>
    cases ha with
    | stmt ha =>
      cases ha
      cases hb with
      | seq hb1 hb2 =>
        cases hb1 with
        | stmt hb1 =>
          cases hb1 with
          | store he1 =>
            cases he1
            cases hb2 with
            | stmt hb2 =>
              cases hb2 with
              | store he2 =>
                cases he2
                refine ⟨hx0, hy0, Or.inr ⟨s.cnt 7, rfl, ?_⟩⟩
                show fupd2 _ _ _ _ _ _ = _
                rw [fupd2_same]
                exact hy0

/-- After the loop, `b.f` holds `y` (or `b` is null), so it is never the object `x`. -/
theorem loop_none : NoCrossAlias Examples.fr Examples.pLoop Examples.vb [.fld Examples.ff]
    Examples.vx [] := by
  rintro ⟨cx, cy, hcx, hcy, s1, s2, o, h1, h2, e1, e2⟩
  rw [path_of_abs hcx (by decide)] at e1
  rw [path_of_abs hcy (by decide)] at e2
  have hi : loopI (CState.init Examples.fr) := ⟨rfl, rfl, Or.inl rfl⟩
  obtain ⟨_, _, hb1⟩ := loop_inv loopI loopI_step h1 hi
  obtain ⟨hx2, _, _⟩ := loop_inv loopI loopI_step h2 hi
  have ho : o = .sym (.root 0) [] := by
    simp only [evalPath, hx2, List.map_nil, readPath, Option.bind_some, Option.some.injEq] at e2
    exact e2.symm
  subst ho
  rcases hb1 with hn | ⟨n, hn, hf⟩
  · simp [evalPath, hn] at e1
  · simp only [evalPath, hn, List.map_cons, List.map_nil, canon, readPath, Option.bind_some,
      hf] at e1
    cases e1

/-! ## The task examples are in the scope -/

/-- The task example is in the checkable core scope. -/
theorem pJoin_in_scope : coreScopeB 2 Examples.fr Examples.pJoin [] [] = true := by decide

/-- The task example is cross-execution exact: `may(x, y)` is false, and each true answer
has two executions (by `ccomplete_coreB`). -/
theorem pJoin_exact (x y : Var) (h : mayProg 2 Examples.fr Examples.pJoin x [] y [] = true) :
    ∃ cx cy, cx.map Cell.abs = [] ∧ cy.map Cell.abs = [] ∧
      CAliasX Examples.fr Examples.pJoin x cx y cy :=
  ccomplete_coreB 2 _ _ x [] y [] pJoin_in_scope h

end DirectedAlias.Sound.Boundary
