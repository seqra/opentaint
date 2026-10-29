import DirectedAlias.Opt.Table

/-!
# Optimization O, part 2: keys, the universe, and the support invariant of C

A key is a variable or a heap cell (origin, cell). Both C and O give each key an origin set.
The universe keys are the variables of the context and the cells of the universe origins.

The support invariant says that every universe key of a C state holds only universe origins.
O stores canonical sets over the universe, so O can only be equal to C if C has this property.
This file proves that `analyze` keeps the support invariant when the context covers the program
(`ProgOK`) and is closed under default content (`CtxClosed`). It also proves that the program
context `progCtx` has these properties.
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-- A key: a variable, or a cell of an origin. -/
inductive Key where
  | v (x : Var)
  | h (o : Origin) (c : ACell)
  deriving DecidableEq, Repr

/-- The origin set of a key in a C state. -/
def cval (X : AState) : Key → List Origin
  | .v x => X.env x
  | .h o c => X.heap o c

/-- A key is in the universe of the context. -/
def InU (ctx : Ctx) : Key → Prop
  | .v x => x ∈ ctx.vars
  | .h o c => o ∈ ctx.origins ∧ c ∈ ctx.cells

/-- The list of universe keys. -/
def ukeys (ctx : Ctx) : List Key :=
  ctx.vars.map Key.v ++ ctx.origins.flatMap (fun o => ctx.cells.map (Key.h o))

/-- A key is in `ukeys` if and only if it is in the universe. -/
theorem mem_ukeys {ctx : Ctx} {k : Key} : k ∈ ukeys ctx ↔ InU ctx k := by
  cases k with
  | v x => simp [ukeys, InU, List.mem_flatMap]
  | h o c => simp [ukeys, InU, List.mem_flatMap]

/-- Every universe key of `X` holds only universe origins. -/
def Supp (ctx : Ctx) (X : AState) : Prop :=
  ∀ k, InU ctx k → cval X k ⊆ ctx.origins

/-- The default content of each universe cell holds only universe origins, and `elem` is a
universe cell. -/
structure CtxClosed (ctx : Ctx) : Prop where
  dflt : ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, adefault ctx.K o c ⊆ ctx.origins
  elem : ACell.elem ∈ ctx.cells

/-- The context covers the statement: its variables, fields and site origins are in the
universe. -/
structure StmtOK (ctx : Ctx) (st : Stmt) : Prop where
  vars : ∀ x ∈ st.vars, x ∈ ctx.vars
  fields : ∀ f ∈ st.fields, ACell.fld f ∈ ctx.cells
  new : ∀ s, st.newSite? = some s → Origin.alloc s ∈ ctx.origins
  fresh : ∀ s, st.freshSite? = some s → Origin.sym (.fresh s) [] ∈ ctx.origins
  call : ∀ s, st.callSite? = some s → Origin.havoc s ∈ ctx.origins

/-- The context covers every statement of the program. -/
def ProgOK (ctx : Ctx) (q : Prog) : Prop := ∀ st ∈ q.stmts, StmtOK ctx st

/-! ## C operations on keys -/

/-- The key values after `setVar`. -/
theorem cval_setVar (X : AState) (x : Var) (S : List Origin) (k : Key) :
    cval (X.setVar x S) k = if k = .v x then S else cval X k := by
  cases k with
  | v y => by_cases h : y = x <;> simp [cval, AState.setVar, fupd, h]
  | h o c => simp [cval, AState.setVar]

/-- The key values after `setCell`. -/
theorem cval_setCell (X : AState) (o : Origin) (c : ACell) (S : List Origin) (k : Key) :
    cval (X.setCell o c S) k = if k = .h o c then S else cval X k := by
  cases k with
  | v y => simp [cval, AState.setCell]
  | h o' c' =>
    by_cases h : o' = o ∧ c' = c
    · obtain ⟨rfl, rfl⟩ := h; simp [cval, AState.setCell]
    · have : ¬ (Key.h o' c' = Key.h o c) := by
        intro he; cases he; exact h ⟨rfl, rfl⟩
      simp only [cval, AState.setCell, fupd2_ne _ _ h, this, ite_false]

/-- The key values after `weakStore`. -/
theorem cval_weakStore (X : AState) (os : List Origin) (c : ACell) (S : List Origin) (k : Key) :
    cval (X.weakStore os c S) k =
      if k ∈ os.map (fun o => Key.h o c) then uni S (cval X k) else cval X k := by
  cases k with
  | v y => simp [cval, AState.weakStore]
  | h o' c' =>
    simp only [cval, AState.weakStore, List.mem_map, Key.h.injEq]
    by_cases h1 : c' = c ∧ o' ∈ os
    · obtain ⟨rfl, h2⟩ := h1
      simp [h2]
    · have h3 : ¬ ∃ a, a ∈ os ∧ a = o' ∧ c = c' := by
        rintro ⟨o, ho, rfl, rfl⟩
        exact h1 ⟨rfl, ho⟩
      simp only [h1, h3, ite_false]

/-- The key values after `store`. -/
theorem cval_store (once : Site → Bool) (X : AState) (x : Var) (c : ACell) (S : List Origin)
    (eu : Bool) :
    X.store once x c S eu =
      match single? (X.env x) with
      | some o => if o.uniqueB once eu then X.setCell o c S else X.weakStore (X.env x) c S
      | none => X.weakStore (X.env x) c S := rfl

/-- The key values after a havoc. -/
theorem cval_havoc (ctx : Ctx) (X : AState) (args : List Var) (s : Site) (k : Key) :
    cval (X.havoc ctx args s) k =
      match k with
      | .v x => X.env x
      | .h o c => if c ∈ ctx.cells ∧ reachB ctx X args o = true then
          uni [.havoc s] (X.heap o c) else X.heap o c := by
  cases k <;> rfl

/-- The key values after `join`. -/
theorem cval_join (X Y : AState) (k : Key) : cval (join X Y) k = uni (cval X k) (cval Y k) := by
  cases k <;> rfl

/-- The key values after `top`. -/
theorem cval_top (ctx : Ctx) (Y : AState) (k : Key) :
    cval (top ctx Y) k = uni ctx.origins (cval Y k) := by
  cases k <;> rfl

/-- `leOn` is true if and only if inclusion holds on every universe key. -/
theorem leOn_iff_keys {ctx : Ctx} {X Y : AState} :
    leOn ctx X Y = true ↔ ∀ k, InU ctx k → cval X k ⊆ cval Y k := by
  rw [leOn_iff]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    cases k with
    | v x => exact h1 x hk
    | h o c => exact h2 o hk.1 c hk.2
  · intro h
    exact ⟨fun x hx => h (.v x) hx, fun o ho c hc => h (.h o c) ⟨ho, hc⟩⟩

/-! ## The support invariant -/

/-- A union of two subsets of a set is a subset of the set. -/
theorem uni_sub {α : Type} [DecidableEq α] {l m n : List α} (h1 : l ⊆ n) (h2 : m ⊆ n) :
    uni l m ⊆ n := by
  intro a ha
  cases mem_uni.mp ha with
  | inl h => exact h1 h
  | inr h => exact h2 h

/-- If `X` has support, then `aread` from universe origins at a universe cell has support. -/
theorem aread_sub {ctx : Ctx} {X : AState} (hs : Supp ctx X) {S : List Origin}
    (hS : S ⊆ ctx.origins) {c : ACell} (hc : c ∈ ctx.cells) : aread X S c ⊆ ctx.origins := by
  intro o' ho'
  obtain ⟨o, ho, h⟩ := mem_aread.mp ho'
  exact hs (.h o c) ⟨hS ho, hc⟩ h

/-- The env value of a universe variable has support. -/
theorem Supp.env {ctx : Ctx} {X : AState} (hs : Supp ctx X) {x : Var} (hx : x ∈ ctx.vars) :
    X.env x ⊆ ctx.origins := hs (.v x) hx

/-- `setVar` with a universe set keeps support. -/
theorem Supp.setVar {ctx : Ctx} {X : AState} (hs : Supp ctx X) (x : Var) {S : List Origin}
    (hS : S ⊆ ctx.origins) : Supp ctx (X.setVar x S) := by
  intro k hk
  rw [cval_setVar]
  split
  · exact hS
  · exact hs k hk

/-- `setRet` with a universe set keeps support. -/
theorem Supp.setRet {ctx : Ctx} {X : AState} (hs : Supp ctx X) (r : Option Var)
    {S : List Origin} (hS : S ⊆ ctx.origins) : Supp ctx (X.setRet r S) := by
  cases r with
  | none => exact hs
  | some x => exact hs.setVar x hS

/-- `weakStore` with a universe set keeps support. -/
theorem Supp.weakStore {ctx : Ctx} {X : AState} (hs : Supp ctx X) (os : List Origin)
    (c : ACell) {S : List Origin} (hS : S ⊆ ctx.origins) : Supp ctx (X.weakStore os c S) := by
  intro k hk
  rw [cval_weakStore]
  split
  · exact uni_sub hS (hs k hk)
  · exact hs k hk

/-- `store` with a universe set keeps support. -/
theorem Supp.store {ctx : Ctx} {X : AState} (hs : Supp ctx X) (once : Site → Bool) (x : Var)
    (c : ACell) {S : List Origin} (hS : S ⊆ ctx.origins) (eu : Bool) :
    Supp ctx (X.store once x c S eu) := by
  rw [cval_store]
  split
  · split
    · intro k hk
      rw [cval_setCell]
      split
      · exact hS
      · exact hs k hk
    · exact hs.weakStore _ c hS
  · exact hs.weakStore _ c hS

/-- A havoc of a universe call site keeps support. -/
theorem Supp.havoc {ctx : Ctx} {X : AState} (hs : Supp ctx X) (args : List Var) {s : Site}
    (h : Origin.havoc s ∈ ctx.origins) : Supp ctx (X.havoc ctx args s) := by
  intro k hk
  rw [cval_havoc]
  cases k with
  | v x => exact hs (.v x) hk
  | h o c =>
    simp only
    split
    · exact uni_sub (by intro a ha; simp at ha; subst ha; exact h) (hs (.h o c) hk)
    · exact hs (.h o c) hk

/-- `join` keeps support. -/
theorem Supp.join {ctx : Ctx} {X Y : AState} (h1 : Supp ctx X) (h2 : Supp ctx Y) :
    Supp ctx (join X Y) := by
  intro k hk; rw [cval_join]; exact uni_sub (h1 k hk) (h2 k hk)

/-- `top` keeps support. -/
theorem Supp.top {ctx : Ctx} {Y : AState} (h : Supp ctx Y) : Supp ctx (top ctx Y) := by
  intro k hk; rw [cval_top]; exact uni_sub (fun _ h => h) (h k hk)

/-- One statement that the context covers keeps support. -/
theorem Supp.astep {ctx : Ctx} (cc : CtxClosed ctx) {X : AState} (hs : Supp ctx X) {st : Stmt}
    (ok : StmtOK ctx st) :
    Supp ctx (astep ctx st X) := by
  cases st with
  | new x s =>
    exact hs.setVar x (by intro a ha; simp at ha; subst ha; exact ok.new s rfl)
  | null x => exact hs.setVar x (by intro a ha; cases ha)
  | copy x y => exact hs.setVar x (hs.env (ok.vars y (by simp [Stmt.vars])))
  | load x y f =>
    exact hs.setVar x (aread_sub hs (hs.env (ok.vars y (by simp [Stmt.vars])))
      (ok.fields f (by simp [Stmt.fields])))
  | store x f y => exact hs.store _ x _ (hs.env (ok.vars y (by simp [Stmt.vars]))) _
  | aload x y =>
    exact hs.setVar x (aread_sub hs (hs.env (ok.vars y (by simp [Stmt.vars]))) cc.elem)
  | astore x y => exact hs.weakStore _ _ (hs.env (ok.vars y (by simp [Stmt.vars])))
  | unknown x s =>
    exact hs.setVar x (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)
  | call r s args =>
    exact (hs.havoc args (ok.call s rfl)).setRet r
      (by intro a ha; simp at ha; subst ha; exact ok.fresh s rfl)

/-- The loop iteration keeps support if the body keeps support. -/
theorem Supp.loopIter {ctx : Ctx} {f : AState → AState}
    (hf : ∀ Y, Supp ctx Y → Supp ctx (f Y)) :
    ∀ (n : Nat) (Y : AState), Supp ctx Y → Supp ctx (DirectedAlias.loopIter ctx f n Y)
  | 0, _, h => h.top
  | n + 1, Y, h => by
    simp only [DirectedAlias.loopIter]
    split
    · exact h
    · exact Supp.loopIter hf n _ (h.join (hf Y h))

/-- The left part of a sequence is covered. -/
theorem ProgOK.left {ctx : Ctx} {p q : Prog} (h : ∀ st ∈ p.stmts ++ q.stmts, StmtOK ctx st) :
    ProgOK ctx p := fun st hs => h st (List.mem_append_left _ hs)

/-- The right part of a sequence is covered. -/
theorem ProgOK.right {ctx : Ctx} {p q : Prog} (h : ∀ st ∈ p.stmts ++ q.stmts, StmtOK ctx st) :
    ProgOK ctx q := fun st hs => h st (List.mem_append_right _ hs)

/-- The analysis of a covered program keeps support. -/
theorem Supp.analyze {ctx : Ctx} (cc : CtxClosed ctx) :
    ∀ (q : Prog) (X : AState), ProgOK ctx q → Supp ctx X → Supp ctx (DirectedAlias.analyze ctx q X)
  | .skip, _, _, h => h
  | .stmt st, _, ok, h => h.astep cc (ok st (by simp [Prog.stmts]))
  | .seq p q, X, ok, h =>
    Supp.analyze cc q _ (ProgOK.right ok) (Supp.analyze cc p X (ProgOK.left ok) h)
  | .choice p q, X, ok, h =>
    (Supp.analyze cc p X (ProgOK.left ok) h).join (Supp.analyze cc q X (ProgOK.right ok) h)
  | .loop p, X, ok, h =>
    Supp.loopIter (fun Y hY => Supp.analyze cc p Y ok hY) _ X h

/-! ## The program context -/

/-- A root of a lookup in the bindings is a root of the bindings. -/
theorem lookup_mem_roots : ∀ (l : List (Var × Root)) (x : Var) (r : Root),
    l.lookup x = some r → r ∈ l.map Prod.snd
  | [], _, _, h => by simp at h
  | (k, b) :: l, x, r, h => by
    rw [List.lookup_cons] at h
    split at h
    · cases h; simp
    · exact List.mem_cons_of_mem _ (lookup_mem_roots l x r h)

/-- A variable that the bindings do not bind has no root. -/
theorem lookup_none_of_not_mem : ∀ (l : List (Var × Root)) (x : Var),
    x ∉ l.map Prod.fst → l.lookup x = none
  | [], _, _ => rfl
  | (k, b) :: l, x, h => by
    rw [List.lookup_cons]
    split
    · rename_i he
      exact absurd (by simp at he; simp [he]) h
    · exact lookup_none_of_not_mem l x (fun h' => h (List.mem_cons_of_mem _ h'))

/-- Membership in the origin universe of a program. -/
theorem mem_originsOf {K : Nat} {fr : Frame} {p : Prog} {cells : List ACell} {o : Origin} :
    o ∈ originsOf K fr p cells ↔
      (∃ b ∈ fr.roots.map ABase.root ++ p.freshSites.map ABase.fresh,
        (∃ q ∈ pathsUpTo cells K, o = .sym b q) ∨ o = .deep b) ∨
      (∃ s ∈ p.newSites, o = .alloc s) ∨ (∃ s ∈ p.callSites, o = .havoc s) := by
  simp only [originsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false]
  constructor
  · rintro ((⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩
    · exact Or.inl ⟨b, hb, Or.inr rfl⟩
    · exact Or.inr (Or.inl ⟨s, hs, rfl⟩)
    · exact Or.inr (Or.inr ⟨s, hs, rfl⟩)
  · rintro (⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inl ⟨q, hq, rfl⟩⟩)
    · exact Or.inl (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
    · exact Or.inr ⟨s, hs, rfl⟩

/-- The program context is closed under default content. -/
theorem ctxClosed_ofProg (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    CtxClosed (Ctx.ofProg K fr p qf) := by
  constructor
  · intro o ho c hc
    simp only [Ctx.ofProg] at ho hc ⊢
    rcases mem_originsOf.mp ho with ⟨b, hb, ⟨q, hq, rfl⟩ | rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      apply mem_originsOf.mpr
      refine Or.inl ⟨b, hb, ?_⟩
      unfold symOrDeep
      split
      · rename_i hl
        obtain ⟨_, hq2⟩ := mem_pathsUpTo.mp hq
        refine Or.inl ⟨q ++ [c], mem_pathsUpTo.mpr ⟨hl, ?_⟩, rfl⟩
        intro d hd
        cases List.mem_append.mp hd with
        | inl h => exact hq2 d h
        | inr h => simp at h; subst h; exact hc
      · exact Or.inr rfl
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      exact mem_originsOf.mpr (Or.inl ⟨b, hb, Or.inr rfl⟩)
    · intro o' ho'; simp [adefault] at ho'
    · intro o' ho'
      simp only [adefault, List.mem_singleton] at ho'
      subst ho'
      exact mem_originsOf.mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩))
  · simp [Ctx.ofProg, cellsOf]

/-- The program context covers every statement of the program. -/
theorem progOK_ofProg (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    ProgOK (Ctx.ofProg K fr p qf) p := by
  intro st hst
  constructor
  · intro x hx
    simp only [Ctx.ofProg]
    rw [List.mem_eraseDups]
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨st, hst, hx⟩)
  · intro f hf
    simp only [Ctx.ofProg, cellsOf]
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨f, ?_, rfl⟩
    rw [List.mem_eraseDups]
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨st, hst, hf⟩)
  · intro s hs
    simp only [Ctx.ofProg]
    exact mem_originsOf.mpr (Or.inr (Or.inl ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩))
  · intro s hs
    simp only [Ctx.ofProg]
    apply mem_originsOf.mpr
    refine Or.inl ⟨.fresh s, ?_, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨by simp, by simp⟩, rfl⟩⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩)
  · intro s hs
    simp only [Ctx.ofProg]
    exact mem_originsOf.mpr (Or.inr (Or.inr ⟨s, List.mem_filterMap.mpr ⟨st, hst, hs⟩, rfl⟩))

/-- The entry state of the frame has support in the program context. -/
theorem supp_ainit (K : Nat) (fr : Frame) (p : Prog) (qf : List Field) :
    Supp (Ctx.ofProg K fr p qf) (ainit K fr) := by
  intro k hk
  cases k with
  | v x =>
    simp only [cval, ainit]
    cases hr : fr.root? x with
    | none => intro _ h; cases h
    | some r =>
      intro o ho
      simp only [List.mem_singleton] at ho
      subst ho
      simp only [Ctx.ofProg]
      apply mem_originsOf.mpr
      refine Or.inl ⟨.root r, ?_, Or.inl ⟨[], mem_pathsUpTo.mpr ⟨by simp, by simp⟩, rfl⟩⟩
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨r, lookup_mem_roots fr.binds x r hr, rfl⟩)
  | h o c => exact (ctxClosed_ofProg K fr p qf).dflt o hk.1 c hk.2

end DirectedAlias.Opt
