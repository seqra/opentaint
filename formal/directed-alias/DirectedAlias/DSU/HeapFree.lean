import DirectedAlias.DSU.Lemmas
import DirectedAlias.DSU.Props
import DirectedAlias.DSU.ConcreteFacts

/-!
# Soundness and dominance of the DSU in the heap-free fragment

The heap-free fragment has `new`, `null`, `unknown`, and `copy x y` with `x ≠ y`, and any
`seq`, `choice` and `loop`. It has no load, store, array access or call.
In this fragment:
- the DSU is sound: each one-execution alias is a DSU alias (`dsu_sound_heapFree`);
- the DSU dominates the concept on variables: each concept alias of two variables is a DSU
  alias (`dsu_dominates_heapFree`).
The self copy `x = x` is excluded: it is unsound (`self_copy_unsound` in `DSU.Examples`).
-/

namespace DirectedAlias.DSU

open DirectedAlias

/-- A statement of the heap-free fragment. -/
def hfStmt : Stmt → Bool
  | .new _ _ => true
  | .null _ => true
  | .unknown _ _ => true
  | .copy x y => !decide (x = y)
  | _ => false

/-- A program of the heap-free fragment. -/
def hfProg (p : Prog) : Bool := p.stmts.all hfStmt

/-- The DSU atom of a concrete object. -/
def atomOf : Obj → Atom
  | .sym (.root r) _ => .root r
  | .sym (.fresh s _) _ => .unk s
  | .sym (.havoc s _ _) _ => .unk s
  | .alloc s _ => .alloc s

/-- The atom of an object is never a local. -/
theorem atomOf_ne_loc (o : Obj) (x : Var) : atomOf o ≠ .loc x := by
  cases o with
  | sym b p => cases b <;> simp [atomOf]
  | alloc s n => simp [atomOf]

/-- A heap-free statement with its atoms in the universe. -/
def okS (cx : DCtx) (st : Stmt) : Prop :=
  hfStmt st = true ∧ (∀ v ∈ st.vars, Atom.loc v ∈ cx.U) ∧
    (∀ x s, st = .new x s → Atom.alloc s ∈ cx.U) ∧ (∀ x s, st = .unknown x s → Atom.unk s ∈ cx.U)

/-- The simulation invariant: each variable with an object is in the group of the object's atom. -/
def Inv (cx : DCtx) (st : CState) (D : DState) : Prop :=
  ∀ x o, st.env x = some o → Atom.loc x ∈ cx.U ∧ atomOf o ∈ cx.U ∧ co D (.loc x) (atomOf o)

/-- `assign` keeps the invariant when the new value of `x` is in the group of `b`. -/
theorem inv_assign {cx : DCtx} {s t : CState} {D D1 : DState} {x : Var} {b : Atom}
    (hb : b ≠ .loc x) (hD : assign D x b = some D1) (hxU : Atom.loc x ∈ cx.U)
    (henv : ∀ z, z ≠ x → t.env z = s.env z)
    (hx : ∀ o, t.env x = some o → atomOf o ∈ cx.U ∧ (atomOf o = b ∨ co D b (atomOf o)))
    (hI : Inv cx s D) : Inv cx t (canon cx D1) := by
  obtain ⟨hco, hpres⟩ := assign_spec hb hD
  intro z o hz
  by_cases hzx : z = x
  · subst hzx
    obtain ⟨hoU, hor⟩ := hx o hz
    refine ⟨hxU, hoU, co_canon hxU hoU ?_⟩
    rcases hor with he | hc
    · rw [he]; exact hco
    · exact hco.trans (hpres _ _ hb (atomOf_ne_loc o z) hc)
  · rw [henv z hzx] at hz
    obtain ⟨h1, h2, h3⟩ := hI z o hz
    refine ⟨h1, h2, co_canon h1 h2 ?_⟩
    exact hpres _ _ (by intro e; cases e; exact hzx rfl) (atomOf_ne_loc o x) h3

/-- One heap-free statement keeps the invariant. -/
theorem inv_step {cx : DCtx} {pos : Nat} {st : Stmt} {D D' : DState} {s t : CState}
    (hok : okS cx st) (hD : stepD cx pos st D = some D') (hs : SStep st s t) (hI : Inv cx s D) :
    Inv cx t D' := by
  obtain ⟨hhf, hvars, hnew, hunk⟩ := hok
  unfold stepD at hD
  cases hr : stepRaw cx pos st D with
  | none => rw [hr] at hD; cases hD
  | some D1 =>
    rw [hr] at hD; cases hD
    cases hs with
    | new =>
      rename_i x s0
      refine inv_assign (b := .alloc s0) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        (fun z hz => by simp [CState.bump, CState.setVar, fupd, hz]) ?_ hI
      intro o ho
      simp [CState.bump, CState.setVar, fupd] at ho
      subst ho
      exact ⟨hnew x s0 rfl, Or.inl rfl⟩
    | null =>
      rename_i x
      refine inv_assign (b := .nul pos) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        (fun z hz => by simp [CState.setVar, fupd, hz]) ?_ hI
      intro o ho
      simp [CState.setVar, fupd] at ho
    | copy =>
      rename_i x y
      have hxy : x ≠ y := by simpa [hfStmt] using hhf
      refine inv_assign (b := .loc y) (by intro e; cases e; exact hxy rfl) hr
        (hvars x (by simp [Stmt.vars])) (fun z hz => by simp [CState.setVar, fupd, hz]) ?_ hI
      intro o ho
      simp [CState.setVar, fupd] at ho
      obtain ⟨_, h2, h3⟩ := hI y o ho
      exact ⟨h2, Or.inr h3⟩
    | unknown =>
      rename_i x s0
      refine inv_assign (b := .unk s0) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        (fun z hz => by simp [CState.bump, CState.setVar, fupd, hz]) ?_ hI
      intro o ho
      simp [CState.bump, CState.setVar, fupd] at ho
      subst ho
      exact ⟨hunk x s0 rfl, Or.inl rfl⟩
    | load => simp [hfStmt] at hhf
    | store => simp [hfStmt] at hhf
    | aload => simp [hfStmt] at hhf
    | astore => simp [hfStmt] at hhf
    | call => simp [hfStmt] at hhf

/-- The DSU analysis of a heap-free program keeps the invariant along each execution. -/
theorem inv_sim (cx : DCtx) :
    ∀ (p : Prog) (pos : Nat) (D D' : DState) (s t : CState), (∀ st ∈ p.stmts, okS cx st) →
      analyzeD cx pos p D = some D' → Exec p s t → Inv cx s D → Inv cx t D' := by
  intro p
  induction p with
  | skip =>
    intro pos D D' s t _ hD hex hI
    cases hD; cases hex; exact hI
  | stmt st =>
    intro pos D D' s t hok hD hex hI
    cases hex with
    | stmt hs => exact inv_step (hok st (by simp [Prog.stmts])) hD hs hI
  | seq p q ihp ihq =>
    intro pos D D' s t hok hD hex hI
    unfold analyzeD at hD
    cases h1 : analyzeD cx pos p D with
    | none => rw [h1] at hD; cases hD
    | some D1 =>
      rw [h1] at hD
      simp only [Option.bind_eq_bind, Option.bind_some] at hD
      cases hex with
      | seq e1 e2 =>
        exact ihq _ D1 D' _ _ (fun st m => hok st (by simp [Prog.stmts, m])) hD e2
          (ihp pos D D1 _ _ (fun st m => hok st (by simp [Prog.stmts, m])) h1 e1 hI)
  | choice p q ihp ihq =>
    intro pos D D' s t hok hD hex hI
    unfold analyzeD at hD
    cases h1 : analyzeD cx pos p D with
    | none => rw [h1] at hD; cases hD
    | some A =>
      rw [h1] at hD
      simp only [Option.bind_eq_bind, Option.bind_some] at hD
      cases h2 : analyzeD cx (pos + p.stmts.length) q D with
      | none => rw [h2] at hD; cases hD
      | some B =>
        rw [h2] at hD
        simp only [Option.bind_some] at hD
        obtain ⟨hjA, hjB⟩ := joinD_spec hD
        cases hex with
        | choiceL e =>
          have hA := ihp pos D A _ _ (fun st m => hok st (by simp [Prog.stmts, m])) h1 e hI
          intro z o hz
          obtain ⟨u1, u2, u3⟩ := hA z o hz
          exact ⟨u1, u2, hjA _ _ u1 u2 u3⟩
        | choiceR e =>
          have hB := ihq _ D B _ _ (fun st m => hok st (by simp [Prog.stmts, m])) h2 e hI
          intro z o hz
          obtain ⟨u1, u2, u3⟩ := hB z o hz
          exact ⟨u1, u2, hjB _ _ u1 u2 u3⟩
  | loop p ihp =>
    intro pos D D' s t hok hD hex hI
    unfold analyzeD at hD
    obtain ⟨B, hB, hJ⟩ := loopD_spec _ _ _ hD
    obtain ⟨hjA, hjB⟩ := joinD_spec hJ
    have hok' : ∀ st ∈ p.stmts, okS cx st := fun st m => hok st (by simpa [Prog.stmts] using m)
    have hI' : Inv cx s D' := by
      intro z o hz
      obtain ⟨u1, u2, u3⟩ := hI z o hz
      exact ⟨u1, u2, hjA _ _ u1 u2 u3⟩
    refine exec_loop_inv (fun u => Inv cx u D') ?_ hex rfl hI'
    intro s1 t1 h1 e1
    have := ihp pos D' B s1 t1 hok' hB e1 h1
    intro z o hz
    obtain ⟨u1, u2, u3⟩ := this z o hz
    exact ⟨u1, u2, hjB _ _ u1 u2 u3⟩

/-! ## The concrete side of the fragment -/

/-- A basic object: an entry root, a fresh object, or an allocation. -/
def Basic (o : Obj) : Prop :=
  (∃ r, o = .sym (.root r) []) ∨ (∃ s n, o = .sym (.fresh s n) []) ∨ ∃ s n, o = .alloc s n

/-- A state of the fragment: the heap is the entry heap, and each variable holds a basic object. -/
def Good (st : CState) : Prop := st.heap = cdefault ∧ ∀ z o, st.env z = some o → Basic o

/-- Each heap-free statement keeps `Good`. -/
theorem good_step {st : Stmt} {s t : CState} (hhf : hfStmt st = true) (hs : SStep st s t)
    (hg : Good s) : Good t := by
  obtain ⟨hh, he⟩ := hg
  cases hs with
  | new =>
    refine ⟨hh, fun z o hz => ?_⟩
    simp only [CState.bump, CState.setVar, fupd] at hz
    split at hz
    · cases hz; exact Or.inr (Or.inr ⟨_, _, rfl⟩)
    · exact he z o hz
  | null =>
    refine ⟨hh, fun z o hz => ?_⟩
    simp only [CState.setVar, fupd] at hz
    split at hz
    · cases hz
    · exact he z o hz
  | copy =>
    refine ⟨hh, fun z o hz => ?_⟩
    simp only [CState.setVar, fupd] at hz
    split at hz
    · exact he _ o hz
    · exact he z o hz
  | unknown =>
    refine ⟨hh, fun z o hz => ?_⟩
    simp only [CState.bump, CState.setVar, fupd] at hz
    split at hz
    · cases hz; exact Or.inr (Or.inl ⟨_, _, rfl⟩)
    · exact he z o hz
  | load => simp [hfStmt] at hhf
  | store => simp [hfStmt] at hhf
  | aload => simp [hfStmt] at hhf
  | astore => simp [hfStmt] at hhf
  | call => simp [hfStmt] at hhf

/-- A path from a symbolic object in the entry heap gives the symbolic object at the longer path. -/
theorem readPath_sym (b : Base) : ∀ (q p : List Cell),
    readPath cdefault (.sym b q) p = some (.sym b (q ++ p))
  | q, [] => by simp [readPath]
  | q, c :: cs => by
    simp only [readPath, cdefault, Option.bind_some]
    rw [readPath_sym b (q ++ [c]) cs]
    simp

/-- A non-empty path from an allocation in the entry heap reads null. -/
theorem readPath_alloc (s n : Nat) (c : Cell) (cs : List Cell) :
    readPath cdefault (.alloc s n) (c :: cs) = none := by
  simp [readPath, cdefault]

/-- The value of a path from a basic object in the entry heap. -/
theorem eval_basic {o o' : Obj} {p : List Cell} (hb : Basic o)
    (h : readPath cdefault o p = some o') :
    (∃ b, o = .sym b [] ∧ o' = .sym b p) ∨ (p = [] ∧ o' = o ∧ ∃ s n, o = .alloc s n) := by
  rcases hb with ⟨r, rfl⟩ | ⟨s, n, rfl⟩ | ⟨s, n, rfl⟩
  · left; rw [readPath_sym] at h; cases h; exact ⟨_, rfl, by simp⟩
  · left; rw [readPath_sym] at h; cases h; exact ⟨_, rfl, by simp⟩
  · right
    cases p with
    | nil => simp [readPath] at h; exact ⟨rfl, h.symm, s, n, rfl⟩
    | cons c cs => rw [readPath_alloc] at h; cases h

/-- In a state of the fragment, two aliased paths are the same path from one object. -/
theorem alias_good {st : CState} {x y : Var} {px py : List Cell} (hg : Good st)
    (h : AliasIn st x px y py) : px = py ∧ ∃ o, st.env x = some o ∧ st.env y = some o := by
  obtain ⟨hh, he⟩ := hg
  obtain ⟨o, h1, h2⟩ := h
  unfold evalPath at h1 h2
  rw [hh] at h1 h2
  cases hx : st.env x with
  | none => rw [hx] at h1; cases h1
  | some ox =>
    cases hy : st.env y with
    | none => rw [hy] at h2; cases h2
    | some oy =>
      rw [hx] at h1; rw [hy] at h2
      simp only [Option.bind_some] at h1 h2
      rcases eval_basic (he x ox hx) h1 with ⟨b, rfl, rfl⟩ | ⟨rfl, rfl, s, n, rfl⟩ <;>
        rcases eval_basic (he y oy hy) h2 with ⟨b', rfl, e⟩ | ⟨rfl, e, s', n', rfl⟩
      · cases e; exact ⟨rfl, _, rfl, rfl⟩
      · cases e
      · cases e
      · cases e; exact ⟨rfl, _, rfl, rfl⟩

/-! ## The universe of a program -/

/-- A local of the program or the frame is in the universe. -/
theorem loc_mem_univ {fr : Frame} {p : Prog} {v : Var} (h : v ∈ p.vars ∨ v ∈ fr.vars) :
    Atom.loc v ∈ univ fr p := by
  unfold univ
  simp only [List.mem_append, List.mem_map]
  left; left; left; left; left
  exact ⟨v, List.mem_eraseDups.mpr (List.mem_append.mpr h), rfl⟩

/-- A root of the frame is in the universe. -/
theorem root_mem_univ {fr : Frame} {p : Prog} {r : Root} (h : r ∈ fr.roots) :
    Atom.root r ∈ univ fr p := by
  unfold univ
  simp only [List.mem_append, List.mem_map]
  left; left; left; left; right
  exact ⟨r, List.mem_eraseDups.mpr h, rfl⟩

/-- Each statement of a heap-free program satisfies `okS` in the program context. -/
theorem okS_all (cfg : DCfg) (fr : Frame) (p : Prog) (hp : hfProg p = true) :
    ∀ st ∈ p.stmts, okS (DCtx.ofProg cfg fr p) st := by
  intro st hst
  refine ⟨List.all_eq_true.mp hp st hst, fun v hv => ?_, fun x s he => ?_, fun x s he => ?_⟩
  · exact loc_mem_univ (Or.inl (List.mem_flatMap.mpr ⟨st, hst, hv⟩))
  · show Atom.alloc s ∈ univ fr p
    unfold univ
    simp only [List.mem_append, List.mem_map]
    left; left; left; right
    refine ⟨s, List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨st, hst, ?_⟩), rfl⟩
    subst he; rfl
  · show Atom.unk s ∈ univ fr p
    unfold univ
    simp only [List.mem_append, List.mem_map]
    right
    refine ⟨s, List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨st, hst, ?_⟩), rfl⟩
    subst he; rfl

/-- A bound variable and its root are in the frame lists. -/
theorem root?_mem {fr : Frame} {x : Var} {r : Root} (h : fr.root? x = some r) :
    x ∈ fr.vars ∧ r ∈ fr.roots := by
  unfold Frame.root? at h
  obtain ⟨l1, l2, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hm : (x, r) ∈ fr.binds := by rw [he]; simp
  exact ⟨List.mem_map.mpr ⟨_, hm, rfl⟩, List.mem_map.mpr ⟨_, hm, rfl⟩⟩

/-- The DSU entry state satisfies the invariant for the entry concrete state. -/
theorem inv_init {cfg : DCfg} {fr : Frame} {p : Prog} {D0 : DState}
    (h : initAux fr fr.vars.eraseDups DState.empty = some D0) :
    Inv (DCtx.ofProg cfg fr p) (CState.init fr) (canon (DCtx.ofProg cfg fr p) D0) := by
  obtain ⟨_, hc⟩ := initAux_spec fr _ _ _ h
  intro x o hx
  simp only [CState.init] at hx
  cases hr : fr.root? x with
  | none => rw [hr] at hx; cases hx
  | some r =>
    rw [hr] at hx; cases hx
    obtain ⟨hxv, hrr⟩ := root?_mem hr
    have hxU : Atom.loc x ∈ univ fr p := loc_mem_univ (Or.inr hxv)
    have hrU : Atom.root r ∈ univ fr p := root_mem_univ hrr
    exact ⟨hxU, hrU, co_canon hxU hrU (hc x (List.mem_eraseDups.mpr hxv) r hr)⟩

/-- Two variables in one group are DSU aliases on each common path. -/
theorem dmay_of_co {D : DState} {x y : Var} {a : Atom} (h1 : co D (.loc x) a)
    (h2 : co D (.loc y) a) (p : List Acc) : dsuMayD D x p y p = true := by
  obtain ⟨n, e1, e2⟩ := h1
  obtain ⟨m, f1, f2⟩ := h2
  rw [e2] at f2; cases f2
  exact dsuMayD_iff.mpr ⟨[], [], p, n, rfl, rfl, by simp [matD, e1, follow], by simp [matD, f1, follow]⟩

/-- Soundness in the heap-free fragment: each one-execution alias is a DSU alias. -/
theorem dsu_sound_heapFree {cfg : DCfg} {fr : Frame} {p : Prog} {x y : Var}
    {px py : List Cell} (hp : hfProg p = true) (hc : (dsuProg cfg fr p).isSome = true)
    (h : CAlias fr p x px y py) :
    dsuMay cfg fr p x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  unfold dsuMay
  cases hd : dsuProg cfg fr p with
  | none => rw [hd] at hc; cases hc
  | some D =>
    simp only
    unfold dsuProg at hd
    simp only at hd
    cases h0 : initAux fr fr.vars.eraseDups DState.empty with
    | none => rw [h0] at hd; cases hd
    | some D0 =>
      rw [h0] at hd
      simp only [Option.bind_some] at hd
      obtain ⟨st, hex, hal⟩ := h
      have hI := inv_sim _ p 0 _ D _ st (okS_all cfg fr p hp) hd hex (inv_init h0)
      have hg : Good st := exec_preserve Good hex
        (fun s' m s1 t1 hs hq => good_step (List.all_eq_true.mp hp s' m) hs hq)
        ⟨rfl, fun z o hz => by
          simp only [CState.init] at hz
          cases hr : fr.root? z with
          | none => rw [hr] at hz; cases hz
          | some r => rw [hr] at hz; cases hz; exact Or.inl ⟨r, rfl⟩⟩
      obtain ⟨rfl, o, hx, hy⟩ := alias_good hg hal
      exact dmay_of_co (hI x o hx).2.2 (hI y o hy).2.2 _

/-! ## Dominance over the concept -/

/-- The DSU atom of an origin of the heap-free fragment. -/
def atomO : Origin → Option Atom
  | .sym (.root r) [] => some (.root r)
  | .sym (.fresh s) [] => some (.unk s)
  | .alloc s => some (.alloc s)
  | _ => none

/-- The relation of a concept state and a DSU state: each origin of a variable has an atom, and the
variable is in the group of that atom. -/
def Rel (cx : DCtx) (X : AState) (D : DState) : Prop :=
  ∀ x o, o ∈ X.env x → ∃ a, atomO o = some a ∧ Atom.loc x ∈ cx.U ∧ a ∈ cx.U ∧ co D (.loc x) a

/-- The concept loop iteration reaches a post-fixpoint before the fuel ends, and the body check
holds at each iterate. -/
def loopOk (ctx : Ctx) (f : AState → AState) (g : AState → Bool) : Nat → AState → Bool
  | 0, _ => false
  | n + 1, Y => g Y && (leOn ctx (f Y) Y || loopOk ctx f g n (join Y (f Y)))

/-- The concept analysis never uses the top state (each loop converges). -/
def aOk (ctx : Ctx) : Prog → AState → Bool
  | .skip, _ => true
  | .stmt _, _ => true
  | .seq p q, X => aOk ctx p X && aOk ctx q (analyze ctx p X)
  | .choice p q, X => aOk ctx p X && aOk ctx q X
  | .loop p, X => loopOk ctx (analyze ctx p) (aOk ctx p) ctx.fuel X

/-- An atom of an origin is never a local. -/
theorem atomO_ne_loc {o : Origin} {a : Atom} (h : atomO o = some a) (x : Var) : a ≠ .loc x := by
  intro e; subst e
  unfold atomO at h
  split at h <;> cases h

/-- The relation moves to a later DSU state that keeps `co` on the universe. -/
theorem rel_mono {cx : DCtx} {X : AState} {D D' : DState}
    (hp : ∀ a b, a ∈ cx.U → b ∈ cx.U → co D a b → co D' a b) (h : Rel cx X D) : Rel cx X D' := by
  intro x o ho
  obtain ⟨a, h1, h2, h3, h4⟩ := h x o ho
  exact ⟨a, h1, h2, h3, hp _ _ h2 h3 h4⟩

/-- The relation for `setVar` after `assign`. -/
theorem rel_assign {cx : DCtx} {X : AState} {D D1 : DState} {x : Var} {b : Atom} {S : List Origin}
    (hb : b ≠ .loc x) (hD : assign D x b = some D1) (hxU : Atom.loc x ∈ cx.U)
    (hS : ∀ o ∈ S, ∃ a, atomO o = some a ∧ a ∈ cx.U ∧ (a = b ∨ co D b a))
    (h : Rel cx X D) : Rel cx (X.setVar x S) (canon cx D1) := by
  obtain ⟨hco, hpres⟩ := assign_spec hb hD
  intro z o ho
  by_cases hzx : z = x
  · subst hzx
    simp only [AState.setVar, fupd_same] at ho
    obtain ⟨a, h1, h2, h3⟩ := hS o ho
    refine ⟨a, h1, hxU, h2, co_canon hxU h2 ?_⟩
    rcases h3 with rfl | hc
    · exact hco
    · exact hco.trans (hpres _ _ hb (atomO_ne_loc h1 z) hc)
  · simp only [AState.setVar, fupd_ne _ _ hzx] at ho
    obtain ⟨a, h1, h2, h3, h4⟩ := h z o ho
    exact ⟨a, h1, h2, h3, co_canon h2 h3
      (hpres _ _ (by intro e; cases e; exact hzx rfl) (atomO_ne_loc h1 x) h4)⟩

/-- One heap-free statement keeps the relation. -/
theorem rel_step {cx : DCtx} {ctx : Ctx} {pos : Nat} {st : Stmt} {X : AState} {D D' : DState}
    (hok : okS cx st) (hD : stepD cx pos st D = some D') (h : Rel cx X D) :
    Rel cx (astep ctx st X) D' := by
  obtain ⟨hhf, hvars, hnew, hunk⟩ := hok
  unfold stepD at hD
  cases hr : stepRaw cx pos st D with
  | none => rw [hr] at hD; cases hD
  | some D1 =>
    rw [hr] at hD; cases hD
    cases st with
    | new x s0 =>
      refine rel_assign (b := .alloc s0) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        ?_ h
      intro o ho
      simp at ho; subst ho
      exact ⟨_, rfl, hnew x s0 rfl, Or.inl rfl⟩
    | null x =>
      refine rel_assign (b := .nul pos) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        ?_ h
      intro o ho; simp at ho
    | copy x y =>
      have hxy : x ≠ y := by simpa [hfStmt] using hhf
      refine rel_assign (b := .loc y) (by intro e; cases e; exact hxy rfl) hr
        (hvars x (by simp [Stmt.vars])) ?_ h
      intro o ho
      obtain ⟨a, h1, _, h3, h4⟩ := h y o ho
      exact ⟨a, h1, h3, Or.inr h4⟩
    | unknown x s0 =>
      refine rel_assign (b := .unk s0) (by intro e; cases e) hr (hvars x (by simp [Stmt.vars]))
        ?_ h
      intro o ho
      simp at ho; subst ho
      exact ⟨_, rfl, hunk x s0 rfl, Or.inl rfl⟩
    | load => simp [hfStmt] at hhf
    | store => simp [hfStmt] at hhf
    | aload => simp [hfStmt] at hhf
    | astore => simp [hfStmt] at hhf
    | call => simp [hfStmt] at hhf

/-- The relation of the two joins. -/
theorem rel_join {cx : DCtx} {A B : AState} {DA DB J : DState} (hJ : joinD cx DA DB = some J)
    (hA : Rel cx A DA) (hB : Rel cx B DB) : Rel cx (join A B) J := by
  obtain ⟨hjA, hjB⟩ := joinD_spec hJ
  intro x o ho
  rcases mem_uni.mp ho with h | h
  · obtain ⟨a, h1, h2, h3, h4⟩ := hA x o h; exact ⟨a, h1, h2, h3, hjA _ _ h2 h3 h4⟩
  · obtain ⟨a, h1, h2, h3, h4⟩ := hB x o h; exact ⟨a, h1, h2, h3, hjB _ _ h2 h3 h4⟩

/-- The DSU analysis of a heap-free program dominates the concept analysis. -/
theorem rel_sim (cx : DCtx) (ctx : Ctx) :
    ∀ (p : Prog) (pos : Nat) (X : AState) (D D' : DState), (∀ st ∈ p.stmts, okS cx st) →
      analyzeD cx pos p D = some D' → aOk ctx p X = true → Rel cx X D →
        Rel cx (analyze ctx p X) D' := by
  intro p
  induction p with
  | skip => intro pos X D D' _ hD _ h; cases hD; exact h
  | stmt st => intro pos X D D' hok hD _ h; exact rel_step (hok st (by simp [Prog.stmts])) hD h
  | seq p q ihp ihq =>
    intro pos X D D' hok hD ha h
    unfold analyzeD at hD
    simp only [aOk, Bool.and_eq_true] at ha
    cases h1 : analyzeD cx pos p D with
    | none => rw [h1] at hD; cases hD
    | some D1 =>
      rw [h1] at hD
      simp only [Option.bind_eq_bind, Option.bind_some] at hD
      exact ihq _ _ D1 D' (fun st m => hok st (by simp [Prog.stmts, m])) hD ha.2
        (ihp pos X D D1 (fun st m => hok st (by simp [Prog.stmts, m])) h1 ha.1 h)
  | choice p q ihp ihq =>
    intro pos X D D' hok hD ha h
    unfold analyzeD at hD
    simp only [aOk, Bool.and_eq_true] at ha
    cases h1 : analyzeD cx pos p D with
    | none => rw [h1] at hD; cases hD
    | some A =>
      rw [h1] at hD
      simp only [Option.bind_eq_bind, Option.bind_some] at hD
      cases h2 : analyzeD cx (pos + p.stmts.length) q D with
      | none => rw [h2] at hD; cases hD
      | some B =>
        rw [h2] at hD
        simp only [Option.bind_some] at hD
        exact rel_join hD (ihp pos X D A (fun st m => hok st (by simp [Prog.stmts, m])) h1 ha.1 h)
          (ihq _ X D B (fun st m => hok st (by simp [Prog.stmts, m])) h2 ha.2 h)
  | loop p ihp =>
    intro pos X D D' hok hD ha h
    unfold analyzeD at hD
    simp only [aOk] at ha
    obtain ⟨B, hB, hJ⟩ := loopD_spec _ _ _ hD
    obtain ⟨hjA, hjB⟩ := joinD_spec hJ
    have hok' : ∀ st ∈ p.stmts, okS cx st := fun st m => hok st (by simpa [Prog.stmts] using m)
    simp only [analyze]
    have key : ∀ (n : Nat) (Y : AState), loopOk ctx (analyze ctx p) (aOk ctx p) n Y = true →
        Rel cx Y D' → Rel cx (loopIter ctx (analyze ctx p) n Y) D' := by
      intro n
      induction n with
      | zero => intro Y hl; simp [loopOk] at hl
      | succ n ihn =>
        intro Y hl hY
        simp only [loopOk, Bool.and_eq_true, Bool.or_eq_true] at hl
        have hfY : Rel cx (analyze ctx p Y) D' :=
          rel_mono hjB (ihp pos Y D' B hok' hB hl.1 hY)
        simp only [loopIter]
        split
        · exact hY
        · rename_i hle
          rcases hl.2 with hl2 | hl2
          · exact absurd hl2 hle
          · refine ihn _ hl2 ?_
            intro x o ho
            rcases mem_uni.mp ho with h' | h'
            · exact hY x o h'
            · exact hfY x o h'
    exact key _ X ha (rel_mono hjA h)

/-- The concept entry state relates to the DSU entry state. -/
theorem rel_init {cfg : DCfg} {fr : Frame} {p : Prog} {D0 : DState} (K : Nat)
    (h : initAux fr fr.vars.eraseDups DState.empty = some D0) :
    Rel (DCtx.ofProg cfg fr p) (ainit K fr) (canon (DCtx.ofProg cfg fr p) D0) := by
  obtain ⟨_, hc⟩ := initAux_spec fr _ _ _ h
  intro x o ho
  simp only [ainit] at ho
  cases hr : fr.root? x with
  | none => rw [hr] at ho; cases ho
  | some r =>
    rw [hr] at ho
    simp at ho; subst ho
    obtain ⟨hxv, hrr⟩ := root?_mem hr
    have hxU : Atom.loc x ∈ univ fr p := loc_mem_univ (Or.inr hxv)
    have hrU : Atom.root r ∈ univ fr p := root_mem_univ hrr
    exact ⟨_, rfl, hxU, hrU, co_canon hxU hrU (hc x (List.mem_eraseDups.mpr hxv) r hr)⟩

/-- Dominance in the heap-free fragment: each concept alias of two variables is a DSU alias. -/
theorem dsu_dominates_heapFree {cfg : DCfg} {fr : Frame} {p : Prog} {x y : Var} (K : Nat)
    (hp : hfProg p = true) (hc : (dsuProg cfg fr p).isSome = true)
    (hok : aOk (progCtx K fr p []) p (ainit K fr) = true)
    (h : mayProg K fr p x [] y [] = true) : dsuMay cfg fr p x [] y [] = true := by
  unfold dsuMay
  cases hd : dsuProg cfg fr p with
  | none => rw [hd] at hc; cases hc
  | some D =>
    simp only
    unfold dsuProg at hd
    simp only at hd
    cases h0 : initAux fr fr.vars.eraseDups DState.empty with
    | none => rw [h0] at hd; cases hd
    | some D0 =>
      rw [h0] at hd
      simp only [Option.bind_some] at hd
      have hR := rel_sim _ (progCtx K fr p []) p 0 (ainit K fr) _ D (okS_all cfg fr p hp) hd hok
        (rel_init K h0)
      unfold mayProg at h
      obtain ⟨o, h1, h2⟩ := may_iff.mp h
      simp only [aevalPath, aevalFrom, afields, List.filterMap_nil, List.append_nil] at h1 h2
      unfold analyzeProg at h1 h2
      obtain ⟨a, ha, _, _, hx⟩ := hR x o h1
      obtain ⟨a', ha', _, _, hy⟩ := hR y o h2
      rw [ha] at ha'; cases ha'
      exact dmay_of_co hx hy []

/-- A program without a loop. -/
def loopFree : Prog → Bool
  | .skip => true
  | .stmt _ => true
  | .seq p q => loopFree p && loopFree q
  | .choice p q => loopFree p && loopFree q
  | .loop _ => false

/-- For a loop-free program, the concept check `aOk` holds. -/
theorem aOk_loopFree (ctx : Ctx) : ∀ (p : Prog) (X : AState), loopFree p = true → aOk ctx p X = true
  | .skip, _, _ => rfl
  | .stmt _, _, _ => rfl
  | .seq p q, X, h => by
    simp only [loopFree, Bool.and_eq_true] at h
    simp only [aOk, aOk_loopFree ctx p X h.1, aOk_loopFree ctx q _ h.2, Bool.and_self]
  | .choice p q, X, h => by
    simp only [loopFree, Bool.and_eq_true] at h
    simp only [aOk, aOk_loopFree ctx p X h.1, aOk_loopFree ctx q _ h.2, Bool.and_self]
  | .loop _, _, h => by cases h

end DirectedAlias.DSU
