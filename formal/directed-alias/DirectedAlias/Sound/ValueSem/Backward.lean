import DirectedAlias.Sound.ValueSem.Soundness

/-!
# Backward search for the uniqueness test (design VS without the reserved keys)

The planned implementation does not keep `Etree` and `Eval` in the state. At a store it searches
backward for the UPSTREAM CALLS and computes their contributions from the states before them:

  `E(P) = ⋃ { R(c) | c upstream of P }`,  `V(P) = ⋃ { succ(R(c)) | c upstream of P }`,

where `(R(c), succ(R(c))) = contrib(c, state before c)` is the closure of design BO (`contrib`).

UPSTREAM (syntactic, structured programs): the calls of `p` are upstream of each point of `q` in
`p; q`; a choice does not see the calls of the other branch; in `loop p` every call of `p` is
upstream of every point of `p` (later calls of the body ran in earlier iterations). The analysis
`analyzeBW` threads the list of upstream calls `up` (site and arguments) by this rule.

THE STATE BEFORE A CALL comes from an ORACLE `ora : Site → AState` (the state that the
implementation stores at the call node). `analyzeBW` never computes a contribution from its own
state; it reads it from the oracle.

This file proves SOUNDNESS FOR EACH CONSISTENT ORACLE (`csoundBW`): if the oracle state of each
call site dominates (on the universe, outside the reserved keys) each state at which the analysis
reaches a call of that site (`ConsBW`), the analysis is sound for value aliases. The final states
of the implementation's fixpoint iteration are such an oracle (argued: at the fixpoint, the state
of a call node is the join of all states that reach it). `BackwardEq.lean` proves that for
loop-free programs the test is the forward test of design VS.

The on-demand sets are NOT renamed by `retire`. This is sound: a renamed name is `old(t)`, which
is never unique (`BlockedAll.unrename`).
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Opt DirectedAlias.Opt.Rec

variable {src : Nat → Obj × Cell} {cb : CtxB}

/-! ## Contributions and upstream calls -/

/-- The contribution of a call with arguments `args` at the state `X`: the closure `R` (for
`Etree`) and the contents of the covered universe cells (for `Eval`). If the closure fails,
every universe origin. -/
def contrib (cb : CtxB) (X : AState) (args : List Var) : List Origin × List Origin :=
  match closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) with
  | some R => (R, succsN cb.cn X R)
  | none => (cb.cn.ctx.origins, cb.cn.ctx.origins)

/-- The passive call adds the contribution of the call to the two sets. -/
theorem callVS_contrib (cb : CtxB) (X : AState) (args : List Var) :
    callVS cb X args = setSets cb X (contrib cb X args).1 (contrib cb X args).2 := by
  unfold callVS contrib
  cases closeN cb.cn X (cb.cn.ctx.origins.length + 1) (callRoots cb.cn X args) <;> rfl

/-- The call site and the arguments of a call statement. -/
def _root_.DirectedAlias.Stmt.callArgs? : Stmt → Option (Site × List Var)
  | .call _ s args => some (s, args)
  | _ => none

/-- The call statements of a program (site and arguments), in syntax order. -/
def _root_.DirectedAlias.Prog.calls (p : Prog) : List (Site × List Var) :=
  p.stmts.filterMap Stmt.callArgs?

/-- An oracle: the state before the calls of each call site. -/
abbrev Oracle := Site → AState

/-- The on-demand `Etree` of a list of upstream calls. -/
def upE (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) : List Origin :=
  uniMap (fun c => (contrib cb (ora c.1) c.2).1) up

/-- The on-demand `Eval` of a list of upstream calls. -/
def upV (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) : List Origin :=
  uniMap (fun c => (contrib cb (ora c.1) c.2).2) up

/-- The store with the uniqueness test on the given sets `E` and `V`. -/
def storeT (cb : CtxB) (E V : List Origin) (X : AState) (x : Var) (c : ACell) (S : List Origin) :
    AState :=
  match single? (X.env x) with
  | some o =>
    if uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V o then X.setCell o c S
    else X.weakStore (X.env x) c S
  | none => X.weakStore (X.env x) c S

/-- The transfer of the backward design: the call changes no set (only `retire` and the
result); the store tests the on-demand sets of the upstream calls; the other statements are as
in design VS. -/
def astepBW (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (i : Nat) :
    Stmt → AState → AState
  | .call ret s _, X => (retireV cb.cn.ctx.K s X).setRet ret [.sym (.fresh s) []]
  | .store x f y, X => storeT cb (upE cb ora up) (upV cb ora up) X x (.fld f) (X.env y)
  | st, X => astepVS cb i st X

/-- The analysis of the backward design, with the list `up` of upstream calls. -/
def analyzeBW (cb : CtxB) (ora : Oracle) :
    List (Site × List Var) → Nat → Prog → AState → AState
  | _, _, .skip, X => X
  | up, i, .stmt s, X => astepBW cb ora up i s X
  | up, i, .seq p q, X => analyzeBW cb ora (up ++ p.calls) (i + p.nulls) q (analyzeBW cb ora up i p X)
  | up, i, .choice p q, X =>
    join (analyzeBW cb ora up i p X) (analyzeBW cb ora up (i + p.nulls) q X)
  | up, i, .loop p, X =>
    loopIter cb.cn.ctx (analyzeBW cb ora (up ++ p.calls) i p) cb.cn.ctx.fuel X

/-- May-alias at the end of `p` in the backward design with the oracle `ora`. -/
def mayProgBW (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog) (ora : Oracle)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : Bool :=
  may (analyzeBW (ctxVS eu K statics fr p (afields px ++ afields py)) ora [] 0 p (ainitV K fr))
    x px y py

/-! ## Consistent oracles -/

/-- The state `X` is below the state `Y` on the universe, outside the reserved variables. -/
def LeMain (cb : CtxB) (X Y : AState) : Prop :=
  (∀ x ∈ cb.cn.ctx.vars, x ≠ cb.cn.xe → x ≠ cb.xv → X.env x ⊆ Y.env x) ∧
    ∀ o ∈ cb.cn.ctx.origins, ∀ c ∈ cb.cn.ctx.cells, X.heap o c ⊆ Y.heap o c

/-- A CONSISTENT ORACLE: at each call that the backward analysis reaches (in the final pass of
each loop), the oracle state of the site dominates the analysis state. -/
def ConsBW (cb : CtxB) (ora : Oracle) : List (Site × List Var) → Nat → Prog → AState → Prop
  | _, _, .skip, _ => True
  | _, _, .stmt (.call _ s _), X => LeMain cb X (ora s)
  | _, _, .stmt _, _ => True
  | up, i, .seq p q, X =>
    ConsBW cb ora up i p X ∧ ConsBW cb ora (up ++ p.calls) (i + p.nulls) q (analyzeBW cb ora up i p X)
  | up, i, .choice p q, X => ConsBW cb ora up i p X ∧ ConsBW cb ora up (i + p.nulls) q X
  | up, i, .loop p, X => ConsBW cb ora (up ++ p.calls) i p (analyzeBW cb ora up i (.loop p) X)

/-! ## Lemmas on the sets -/

/-- Membership in the on-demand `Etree`. -/
theorem mem_upE {ora : Oracle} {up : List (Site × List Var)} {a : Origin} :
    a ∈ upE cb ora up ↔ ∃ c ∈ up, a ∈ (contrib cb (ora c.1) c.2).1 := by
  simp [upE, mem_uniMap]

/-- Membership in the on-demand `Eval`. -/
theorem mem_upV {ora : Oracle} {up : List (Site × List Var)} {a : Origin} :
    a ∈ upV cb ora up ↔ ∃ c ∈ up, a ∈ (contrib cb (ora c.1) c.2).2 := by
  simp [upV, mem_uniMap]

/-- More upstream calls give larger sets. -/
theorem upE_mono {ora : Oracle} {up up' : List (Site × List Var)} (h : ∀ c ∈ up, c ∈ up')
    {a : Origin} (ha : a ∈ upE cb ora up) : a ∈ upE cb ora up' := by
  obtain ⟨c, hc, h1⟩ := mem_upE.mp ha
  exact mem_upE.mpr ⟨c, h c hc, h1⟩

/-- More upstream calls give larger sets. -/
theorem upV_mono {ora : Oracle} {up up' : List (Site × List Var)} (h : ∀ c ∈ up, c ∈ up')
    {a : Origin} (ha : a ∈ upV cb ora up) : a ∈ upV cb ora up' := by
  obtain ⟨c, hc, h1⟩ := mem_upV.mp ha
  exact mem_upV.mpr ⟨c, h c hc, h1⟩

/-- The contribution of a supported state is in the universe. -/
theorem contrib_sub (hc : CtxBOK cb) {X : AState} (hs : Supp cb.cn.ctx X) {args : List Var}
    (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) :
    (contrib cb X args).1 ⊆ cb.cn.ctx.origins ∧ (contrib cb X args).2 ⊆ cb.cn.ctx.origins := by
  have hroots := callRoots_sub hc hs hargs
  unfold contrib
  split
  · rename_i R hR
    exact ⟨Opt.CellNamed.closeN_sub hs hroots hR, Opt.CellNamed.succsN_sub hs R⟩
  · exact ⟨fun _ h => h, fun _ h => h⟩

/-- The arguments of the upstream calls are universe variables. -/
def UpOK (cb : CtxB) (up : List (Site × List Var)) : Prop :=
  ∀ c ∈ up, ∀ a ∈ c.2, a ∈ cb.cn.ctx.vars

/-- The on-demand sets of supported oracle states are in the universe. -/
theorem up_sub (hc : CtxBOK cb) {ora : Oracle} (hora : ∀ s, Supp cb.cn.ctx (ora s))
    {up : List (Site × List Var)} (hup : UpOK cb up) :
    upE cb ora up ⊆ cb.cn.ctx.origins ∧ upV cb ora up ⊆ cb.cn.ctx.origins := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, hc1, h1⟩ := mem_upE.mp ha
    exact (contrib_sub hc (hora c.1) (hup c hc1)).1 h1
  · obtain ⟨c, hc1, h1⟩ := mem_upV.mp ha
    exact (contrib_sub hc (hora c.1) (hup c hc1)).2 h1

/-- The calls of a sequence. -/
theorem calls_seq (p q : Prog) : (Prog.seq p q).calls = p.calls ++ q.calls := by
  simp [Prog.calls, Prog.stmts, List.filterMap_append]

/-- The calls of a choice. -/
theorem calls_choice (p q : Prog) : (Prog.choice p q).calls = p.calls ++ q.calls := by
  simp [Prog.calls, Prog.stmts, List.filterMap_append]

/-- The calls of a loop are the calls of its body. -/
theorem calls_loop (p : Prog) : (Prog.loop p).calls = p.calls := rfl

/-- The arguments of the calls of a program are universe variables. -/
theorem upOK_calls {q : Prog} (hok : ∀ st ∈ q.stmts, StmtOKB cb st) : UpOK cb q.calls := by
  intro c hc a ha
  obtain ⟨st, hst, e⟩ := List.mem_filterMap.mp hc
  cases st with
  | call ret s args =>
    cases e
    exact (hok _ hst).vars a (by simp [Stmt.vars, ha])
  | _ => cases e

/-- `UpOK` of an append. -/
theorem UpOK.append {up up' : List (Site × List Var)} (h1 : UpOK cb up) (h2 : UpOK cb up') :
    UpOK cb (up ++ up') := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact h1 c h
  · exact h2 c h

/-! ## Renaming of the sets -/

/-- The renaming of a symbolic origin by `retire` is the origin. -/
theorem renameO_sym_inv {s : Site} {a : Origin} {b : ABase} {q : List ACell}
    (h : renameO s a = .sym b q) : a = .sym b q := by
  unfold renameO at h
  split at h
  · cases h
  · exact h

/-- AN UNRENAMED SET BLOCKS EACH RENAMED NAME: if a name is not unique for the renamed sets, it is
not unique for the sets (the only change is `new(s)` to `old(s)`, and `old(s)` is never unique). -/
theorem uniqueBO_false_unrename {once : Site → Bool} {eu : Bool} {E V : List Origin} {u : Origin}
    (s : Site) (h : uniqueBO once eu (renameL s E) (renameL s V) u = false) :
    uniqueBO once eu E V u = false := by
  rcases uniqueBO_false_iff.mp h with h1 | h1 | h1
  · exact uniqueBO_false_iff.mpr (Or.inl h1)
  · cases u with
    | sym b q =>
      obtain ⟨p, hm, hl, hp⟩ := expB_inv h1
      obtain ⟨a, ha, e⟩ := List.mem_map.mp hm
      rw [renameO_sym_inv e] at ha
      exact uniqueBO_false_iff.mpr (Or.inr (Or.inl (expB_of ha hl hp)))
    | _ => simp [expB] at h1
  · obtain ⟨a, ha, e⟩ := List.mem_map.mp h1
    unfold renameO at e
    split at e
    · subst e
      refine uniqueBO_false_iff.mpr (Or.inl ?_)
      show ((2 * s + 1) % 2 == 0) = false
      have : @Eq Nat ((2 * s + 1) % 2) 1 := by omega
      rw [this]; rfl
    · subst e; exact uniqueBO_false_iff.mpr (Or.inr (Or.inr ha))

/-- The blocked facts for renamed sets give the blocked facts for the sets. -/
theorem BlockedAll.unrename {G : GNames} {cnt : Site → Nat} {E V : List Origin} (s : Site)
    (h : BlockedAll cb G cnt (renameL s E) (renameL s V)) : BlockedAll cb G cnt E V :=
  fun a n k p hin => uniqueBO_false_unrename s (h a n k p hin)

/-! ## The sets as reserved variables -/

/-- The state `X` with the reserved variables set to `E` (`Etree`) and `V` (`Eval`). -/
def withSets (cb : CtxB) (X : AState) (E V : List Origin) : AState where
  env := fupd (fupd X.env cb.cn.xe E) cb.xv V
  heap := X.heap

/-- `Etree` of `withSets`. -/
theorem withSets_xe (hc : CtxBOK cb) (X : AState) (E V : List Origin) :
    (withSets cb X E V).env cb.cn.xe = E := by
  show fupd (fupd X.env cb.cn.xe E) cb.xv V cb.cn.xe = E
  rw [fupd_ne _ _ (Ne.symm hc.xvNe), fupd_same]

/-- `Eval` of `withSets`. -/
theorem withSets_xv (X : AState) (E V : List Origin) : (withSets cb X E V).env cb.xv = V := by
  show fupd (fupd X.env cb.cn.xe E) cb.xv V cb.xv = V
  rw [fupd_same]

/-- `withSets` keeps the other variables. -/
theorem withSets_env (X : AState) (E V : List Origin) {x : Var} (h1 : x ≠ cb.cn.xe)
    (h2 : x ≠ cb.xv) : (withSets cb X E V).env x = X.env x := by
  show fupd (fupd X.env cb.cn.xe E) cb.xv V x = _
  rw [fupd_ne _ _ h2, fupd_ne _ _ h1]

/-- The reserved variables have no value and no null tag. -/
def Res (cb : CtxB) (vs : VState) : Prop :=
  vs.cs.env cb.cn.xe = none ∧ vs.cs.env cb.xv = none ∧ vs.nv cb.cn.xe = none ∧ vs.nv cb.xv = none

/-- TRANSFER OF THE INVARIANT: the invariant of design VS moves to a state with larger
non-reserved variables and cells, and with sets that block at least the same names. -/
theorem InvVS.transfer {vs : VState} {Y Z : AState} (h : InvVS cb vs Y) (hres : Res cb vs)
    (henv : ∀ x, x ≠ cb.cn.xe → x ≠ cb.xv → ∀ a, a ∈ Y.env x → a ∈ Z.env x)
    (hheap : ∀ o c a, a ∈ Y.heap o c → a ∈ Z.heap o c)
    (hblk : ∀ G cnt, BlockedAll cb G cnt (Y.env cb.cn.xe) (Y.env cb.xv) →
      BlockedAll cb G cnt (Z.env cb.cn.xe) (Z.env cb.xv)) : InvVS cb vs Z := by
  obtain ⟨G, hg, hx, hn, hN⟩ := h
  have nres : ∀ x o, vs.cs.env x = some o → x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
    intro x o e
    refine ⟨fun e1 => ?_, fun e2 => ?_⟩
    · subst e1; rw [hres.1] at e; cases e
    · subst e2; rw [hres.2.1] at e; cases e
  have nresN : ∀ x t, vs.nv x = some t → x ≠ cb.cn.xe ∧ x ≠ cb.xv := by
    intro x t e
    refine ⟨fun e1 => ?_, fun e2 => ?_⟩
    · subst e1; rw [hres.2.2.1] at e; cases e
    · subst e2; rw [hres.2.2.2] at e; cases e
  refine ⟨G, { hg with
      env := fun x hx1 o he => henv x (nres x o he).1 (nres x o he).2 _ (hg.env x hx1 o he)
      heap := fun o c o' hd hin hc hh => hheap _ _ _ (hg.heap o c o' hd hin hc hh) },
    { hx with blocked := hblk G _ hx.blocked }, hn,
    { hN with
      nenv := fun x hx1 he t ht => henv x (nresN x t ht).1 (nresN x t ht).2 _ (hN.nenv x hx1 he t ht)
      nheap := fun o c hd hin hc he => hheap _ _ _ (hN.nheap o c hd hin hc he) }⟩

/-- No empty cell moves to a state with larger cells. -/
theorem NE.transfer {Y Z : AState} (h : NE Y) (hheap : ∀ o c a, a ∈ Y.heap o c → a ∈ Z.heap o c) :
    NE Z := by
  intro o c e
  cases hy : Y.heap o c with
  | nil => exact h o c hy
  | cons a l =>
    have := hheap o c a (by rw [hy]; exact List.mem_cons_self)
    rw [e] at this; cases this

/-! ## The call with an oracle -/

section call

variable (hc : CtxBOK cb) {G : GNames} {st : CState} {X O : AState} {args : List Var} {s : Site}
  {h' : Heap} (hg : InvG cb.cn.ctx (alphaBO cb G) st X) (hx : InvXB cb G st X)
  (hcnt : CntOKB G st.cnt) (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars)
  (hh : HavocN src cb.cn.statics st args s (st.cnt s) h') (hs : Supp cb.cn.ctx X)
  (hsO : Supp cb.cn.ctx O) (hne : NE X)
  (hle : ∀ a ∈ args, X.env a ⊆ O.env a)
  (hleh : ∀ o ∈ cb.cn.ctx.origins, ∀ c ∈ cb.cn.ctx.cells, X.heap o c ⊆ O.heap o c)

include hc hg hx hcnt hargs hh hs hsO hne hle hleh

/-- LOCAL SOUNDNESS OF THE CALL WITH AN ORACLE: the passive call that adds the contribution of
the call computed at a DOMINATING oracle state keeps the generic invariant and the blocked facts
for the ghost naming after the call. -/
theorem callOra_sound :
    InvG cb.cn.ctx (alphaBO cb (ghostsAfter cb G src st.cnt h'
        (setSets cb X (contrib cb O args).1 (contrib cb O args).2) s (st.cnt s)))
      { st with heap := h' } (setSets cb X (contrib cb O args).1 (contrib cb O args).2) ∧
    InvXB cb (ghostsAfter cb G src st.cnt h'
        (setSets cb X (contrib cb O args).1 (contrib cb O args).2) s (st.cnt s))
      { st with heap := h' } (setSets cb X (contrib cb O args).1 (contrib cb O args).2) := by
  have hrootsO := callRoots_sub hc hsO hargs
  have hroots : ∀ a ∈ callRoots cb.cn X args, a ∈ callRoots cb.cn O args := by
    intro a ha
    rcases mem_uni.mp ha with h1 | h1
    · obtain ⟨x, hx1, h2⟩ := mem_uniMap.mp h1
      exact mem_uni.mpr (Or.inl (mem_uniMap.mpr ⟨x, hx1, hle x hx1 h2⟩))
    · exact mem_uni.mpr (Or.inr h1)
  unfold contrib
  split
  · rename_i R hR
    obtain ⟨h0, hcl⟩ := closeN_spec hR
    have hRU : R ⊆ cb.cn.ctx.origins := Opt.CellNamed.closeN_sub hsO hrootsO hR
    have hVU := Opt.CellNamed.succsN_sub hsO R
    have hsub : ∀ v ∈ succsN cb.cn X R, v ∈ succsN cb.cn O R := by
      intro v hv
      obtain ⟨u, hu, hcu, c, hc1, h1⟩ := mem_succsN.mp hv
      exact mem_succsN.mpr ⟨u, hu, hcu, c, hc1, hleh u hu c hc1 h1⟩
    have hcov := fun o (hr : ReachN st cb.cn.statics args o) =>
      reach_coverB hc hg hx hargs (fun a ha => h0 a (hroots a ha)) (fun v hv => hcl v (hsub v hv)) hr
    have hcovc : ∀ u c, coveredB R u = true → coveredB R (childCN cb.cn.ctx.K u c) = true := by
      intro u c h
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp h
      exact coveredB_iff.mpr ⟨a, ha, descB_child _ _ hd⟩
    have hVc : ∀ u ∈ cb.cn.ctx.origins, coveredB R u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, v ∈ succsN cb.cn O R :=
      fun u hu hcu c hc1 v hv => mem_succsN.mpr ⟨u, hu, hcu, c, hc1, hleh u hu c hc1 hv⟩
    have hcovS : ∀ u ∈ cb.cn.ctx.origins, coveredB R u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, coveredB R v = true :=
      fun u hu hcu c hc1 v hv =>
        coveredB_iff.mpr ⟨v, hcl v (hVc u hu hcu c hc1 v hv), descB_refl v⟩
    have hEc : ∀ u, coveredB R u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
        Origin.sym b q ∈ cb.cn.ctx.origins → expB R (.sym b q) = true := by
      intro u hu c b q e _
      obtain ⟨q0, rfl, rfl⟩ := childCN_sym_inv e
      obtain ⟨a, ha, hd⟩ := coveredB_iff.mp hu
      obtain ⟨p, rfl, hp⟩ := descB_sym_inv hd
      refine expB_of ha ?_ (preB_append hp _)
      have := preB_len hp
      rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega
    have e := callWith_eq_setSets cb hne R (succsN cb.cn O R) (coveredB R)
    have h1 := InvG.callW hc hg hx hcnt hh hs hRU hVU hcov hcovc hcovS
    have h2 := InvXB.callW hc hg hx hcnt hh hs hRU hVU hcov hcovc hcovS hVc hEc
    rw [e] at h1 h2
    exact ⟨h1, h2⟩
  · have hEc : ∀ u, (fun _ => true) u = true → ∀ c b q, childCN cb.cn.ctx.K u c = .sym b q →
        Origin.sym b q ∈ cb.cn.ctx.origins → expB cb.cn.ctx.origins (.sym b q) = true := by
      intro u _ c b q e hin
      cases q with
      | nil => exact absurd e (childCN_ne_root _ u c b)
      | cons d ds =>
        exact expB_of (p := []) (hc.cn.rootIn b _ hin) (by simp) (by simp [preB])
    have hVc : ∀ u ∈ cb.cn.ctx.origins, (fun _ => true) u = true → ∀ c ∈ cb.cn.ctx.cells,
        ∀ v ∈ X.heap u c, v ∈ cb.cn.ctx.origins :=
      fun u hu _ c hc1 v hv => hs (.h u c) ⟨hu, hc1⟩ hv
    have e := callWith_eq_setSets cb hne cb.cn.ctx.origins cb.cn.ctx.origins (fun _ => true)
    have h1 := InvG.callW hc hg hx hcnt hh hs (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    have h2 := InvXB.callW hc hg hx hcnt hh hs (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) hVc hEc
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

end call

/-- The null facts after a passive call into any state with the same heap and larger
variables. -/
theorem InvN.callGen {G : GNames} {vs : VState} {X Y : AState} {args : List Var} {s : Site}
    {h' : Heap} (hx : InvXB cb G vs.cs X) (hcnt : CntOKB G vs.cs.cnt) (h : InvN cb G vs X)
    (hh : HavocN src cb.cn.statics vs.cs args s (vs.cs.cnt s) h') (hY : Y.heap = X.heap)
    (hE : ∀ x a, a ∈ X.env x → a ∈ Y.env x) :
    InvN cb (ghostsAfter cb G src vs.cs.cnt h' Y s (vs.cs.cnt s))
      { vs with cs := { vs.cs with heap := h' } } Y := by
  have hkeep : ∀ o c, h' o c = none → vs.cs.heap o c = none := by
    intro o c e
    rcases hh o c with e2 | ⟨_, _, _, e2⟩
    · rw [← e2]; exact e
    · rw [e2] at e; cases e
  have hnj : ∀ o c, vs.cs.heap o c = none → isJunk (alphaBO cb G vs.cs.cnt o) = false := by
    intro o c e
    cases hj : isJunk (alphaBO cb G vs.cs.cnt o) with
    | false => rfl
    | true =>
      exfalso
      rw [hx.junkDflt o c hj] at e
      cases o with
      | alloc a n =>
        revert hj
        show isJunk (if n + 1 = vs.cs.cnt a then rNew a else rOld a) = true → False
        split <;> intro h1 <;> cases h1
      | sym b p => cases e
  have hag : ∀ o c, vs.cs.heap o c = none →
      alphaBO cb (ghostsAfter cb G src vs.cs.cnt h' Y s (vs.cs.cnt s)) vs.cs.cnt o =
        alphaBO cb G vs.cs.cnt o :=
    fun o c e => alphaBO_after hcnt (hnj o c e)
  exact {
    nout := h.nout
    nenv := fun x hx1 he t ht => hE x _ (h.nenv x hx1 he t ht)
    nenvIn := h.nenvIn
    nheap := fun o c hd hin hc1 he => by
      change h' o c = none at he
      have he0 := hkeep o c he
      change alphaBO cb _ vs.cs.cnt o ∈ _ at hin
      rw [hag o c he0] at hin
      show _ ∈ Y.heap (alphaBO cb _ vs.cs.cnt o) c.abs
      rw [hag o c he0, hY]
      exact h.nheap o c hd hin hc1 he0
    nheapIn := fun o c hd hin hc1 he => by
      change h' o c = none at he
      have he0 := hkeep o c he
      change alphaBO cb _ vs.cs.cnt o ∈ _ at hin
      rw [hag o c he0] at hin
      exact h.nheapIn o c hd hin hc1 he0
    nfresh := h.nfresh }

/-! ## One statement -/

/-- An instrumented step of a statement without the reserved variables keeps them empty. -/
theorem Res.step {i : Nat} {st : Stmt} {s s' : VState} (hok : StmtOKB cb st) (h : Res cb s)
    (hst : SStepV src cb.cn.statics i st s s') : Res cb s' := by
  have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
  have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
  have setv : ∀ (vs : VState) (x : Var) (v : VVal), x ≠ cb.cn.xe → x ≠ cb.xv → Res cb vs →
      Res cb (vs.setVarV x v) := by
    intro vs x v h1 h2 h
    cases v with
    | obj o =>
      exact ⟨by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.1,
        by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.1, h.2.2.1, h.2.2.2⟩
    | nul t =>
      exact ⟨by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.1,
        by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.1,
        by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.2.2.1,
        by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.2.2⟩
  have setc : ∀ (vs : VState) (o : Obj) (c : Cell) (v : VVal), Res cb vs →
      Res cb (vs.setCellV o c v) := by
    intro vs o c v h
    cases v <;> exact h
  cases hst with
  | @new x a =>
    have h1 := nx x (by simp [Stmt.vars]); have h2 := nv x (by simp [Stmt.vars])
    exact ⟨by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.1,
      by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.1, h.2.2.1, h.2.2.2⟩
  | @null x => exact setv _ x _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])) h
  | @copy x y _ v _ => exact setv _ x _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])) h
  | @load x y f _ o _ =>
    exact setv _ x _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])) h
  | @aload x y _ o j _ =>
    exact setv _ x _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])) h
  | store _ _ => exact setc _ _ _ _ h
  | astore _ _ _ => exact setc _ _ _ _ h
  | @unknown x a =>
    have h1 := nx x (by simp [Stmt.vars]); have h2 := nv x (by simp [Stmt.vars])
    exact ⟨by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.1,
      by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.1, h.2.2.1, h.2.2.2⟩
  | @call ret a args _ h' _ =>
    cases ret with
    | none => exact h
    | some x =>
      have h1 := nx x (by simp [Stmt.vars]); have h2 := nv x (by simp [Stmt.vars])
      exact ⟨by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h1)]; exact h.1,
        by show fupd _ x _ _ = _; rw [fupd_ne _ _ (Ne.symm h2)]; exact h.2.1, h.2.2.1, h.2.2.2⟩

/-- The heap of the store of design BO on `withSets` is the heap of the store with the given
sets. -/
theorem storeBO_withSets_heap (hc : CtxBOK cb) (X : AState) (E V : List Origin) {x : Var}
    (h1 : x ≠ cb.cn.xe) (h2 : x ≠ cb.xv) (c : ACell) (S : List Origin) :
    (BlockOnly.storeBO cb (withSets cb X E V) x c S).heap = (storeT cb E V X x c S).heap := by
  unfold BlockOnly.storeBO storeT
  rw [withSets_env X E V h1 h2, withSets_xe hc, withSets_xv]
  cases single? (X.env x) with
  | none => rfl
  | some o =>
    simp only
    by_cases hu : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique E V o = true
    · rw [ite_eq_left hu, ite_eq_left hu]; rfl
    · rw [ite_eq_right hu, ite_eq_right hu]; rfl

/-- The variables of the store of design BO are the variables before it. -/
theorem storeBO_env' (X : AState) (x : Var) (c : ACell) (S : List Origin) :
    (BlockOnly.storeBO cb X x c S).env = X.env := by
  unfold BlockOnly.storeBO
  split
  · split <;> rfl
  · rfl

/-- The variables of `storeT` are the variables before it. -/
theorem storeT_env (E V : List Origin) (X : AState) (x : Var) (c : ACell) (S : List Origin) :
    (storeT cb E V X x c S).env = X.env := by
  unfold storeT
  split
  · split <;> rfl
  · rfl

/-- A statement that is not a call, a store, `new` or `unknown`. -/
def _root_.DirectedAlias.Stmt.plainB : Stmt → Bool
  | .null _ => true
  | .copy _ _ => true
  | .load _ _ _ => true
  | .aload _ _ => true
  | .astore _ _ => true
  | _ => false

/-- For a plain statement, design VS on `withSets` changes the non-reserved variables and the
heap as on the state, and keeps the two sets. -/
theorem astepVS_withSets (hc : CtxBOK cb) {i : Nat} {st : Stmt} (hp : st.plainB = true)
    (hok : StmtOKB cb st) (X : AState) (E V : List Origin) :
    (∀ z, z ≠ cb.cn.xe → z ≠ cb.xv →
      (astepVS cb i st (withSets cb X E V)).env z = (astepVS cb i st X).env z) ∧
    (astepVS cb i st (withSets cb X E V)).heap = (astepVS cb i st X).heap ∧
    (astepVS cb i st (withSets cb X E V)).env cb.cn.xe = E ∧
    (astepVS cb i st (withSets cb X E V)).env cb.xv = V := by
  have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
  have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
  have setv : ∀ (x : Var) (S S' : List Origin), x ≠ cb.cn.xe → x ≠ cb.xv → S' = S →
      (∀ z, z ≠ cb.cn.xe → z ≠ cb.xv →
        ((withSets cb X E V).setVar x S').env z = (X.setVar x S).env z) ∧
      ((withSets cb X E V).setVar x S').heap = (X.setVar x S).heap ∧
      ((withSets cb X E V).setVar x S').env cb.cn.xe = E ∧
      ((withSets cb X E V).setVar x S').env cb.xv = V := by
    intro x S S' h1 h2 e
    subst e
    refine ⟨fun z hz1 hz2 => ?_, rfl, ?_, ?_⟩
    · show fupd _ x _ z = fupd _ x _ z
      by_cases ez : z = x
      · subst ez; rw [fupd_same, fupd_same]
      · rw [fupd_ne _ _ ez, fupd_ne _ _ ez]; exact withSets_env X E V hz1 hz2
    · show fupd _ x _ cb.cn.xe = E
      rw [fupd_ne _ _ (Ne.symm h1)]; exact withSets_xe hc X E V
    · show fupd _ x _ cb.xv = V
      rw [fupd_ne _ _ (Ne.symm h2)]; exact withSets_xv X E V
  cases st with
  | null x => exact setv x _ _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars])) rfl
  | copy x y =>
    exact setv x _ _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
      (withSets_env X E V (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars])))
  | load x y f =>
    exact setv x _ _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
      (by show aread (withSets cb X E V) ((withSets cb X E V).env y) _ = aread X (X.env y) _
          rw [withSets_env X E V (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))]; rfl)
  | aload x y =>
    exact setv x _ _ (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
      (by show aread (withSets cb X E V) ((withSets cb X E V).env y) _ = aread X (X.env y) _
          rw [withSets_env X E V (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))]; rfl)
  | astore x y =>
    have ex := withSets_env X E V (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
    have ey := withSets_env X E V (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))
    refine ⟨fun z hz1 hz2 => withSets_env X E V hz1 hz2, ?_, withSets_xe hc X E V,
      withSets_xv X E V⟩
    show ((withSets cb X E V).weakStore ((withSets cb X E V).env x) .elem
      ((withSets cb X E V).env y)).heap = (X.weakStore (X.env x) .elem (X.env y)).heap
    rw [ex, ey]; rfl
  | new _ _ => cases hp
  | unknown _ _ => cases hp
  | call _ _ _ => cases hp
  | store _ _ _ => cases hp

/-- The invariant of the backward design: the invariant of design VS for the state with the
on-demand sets of the upstream calls in the reserved variables. -/
def InvBW (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (vs : VState) (X : AState) :
    Prop :=
  InvVS cb vs (withSets cb X (upE cb ora up) (upV cb ora up))

/-- LOCAL SOUNDNESS OF THE BACKWARD DESIGN: one instrumented step keeps the invariant with the
upstream calls of the statement added. -/
theorem step_soundBW (hc : CtxBOK cb) {ora : Oracle} (hora : ∀ s, Supp cb.cn.ctx (ora s))
    {up : List (Site × List Var)} (hup : UpOK cb up) {i : Nat} {st : Stmt} {s s' : VState}
    {X : AState} (hok : StmtOKB cb st) (hnull : st.nullN = 1 → nullO i ∈ cb.cn.ctx.origins)
    (hb : Budget cb.cn.ctx (.stmt st) s.cs) (hs : Supp cb.cn.ctx X) (hne : NE X)
    (hres : Res cb s) (h : InvBW cb ora up s X) (hcons : ConsBW cb ora up i (.stmt st) X)
    (hst : SStepV src cb.cn.statics i st s s') :
    NE (astepBW cb ora up i st X) ∧ InvBW cb ora (up ++ (Prog.stmt st).calls) s'
      (astepBW cb ora up i st X) := by
  have hU := up_sub hc hora hup
  have hsH : Supp cb.cn.ctx (withSets cb X (upE cb ora up) (upV cb ora up)) := by
    intro k hk
    cases k with
    | v x =>
      show (withSets cb X _ _).env x ⊆ _
      by_cases e1 : x = cb.cn.xe
      · subst e1; rw [withSets_xe hc]; exact hU.1
      · by_cases e2 : x = cb.xv
        · subst e2; rw [withSets_xv]; exact hU.2
        · rw [withSets_env X _ _ e1 e2]; exact hs (.v x) hk
    | h o c => exact hs (.h o c) hk
  have hneH : NE (withSets cb X (upE cb ora up) (upV cb ora up)) := hne
  have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
  have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
  have hres' := hres.step hok hst
  -- the upstream calls of a statement that is not a call are the old ones
  have hnc : st.callArgs? = none → up ++ (Prog.stmt st).calls = up := by
    intro e
    show up ++ [st].filterMap Stmt.callArgs? = up
    simp [e]
  -- the generic transfer for statements other than store and call
  have tr : ∀ (Y Z : AState), NE Y → InvVS cb s' Y →
      (∀ x, x ≠ cb.cn.xe → x ≠ cb.xv → ∀ a, a ∈ Y.env x → a ∈ Z.env x) →
      (∀ o c a, a ∈ Y.heap o c → a ∈ Z.heap o c) →
      (∀ G cnt, BlockedAll cb G cnt (Y.env cb.cn.xe) (Y.env cb.xv) →
        BlockedAll cb G cnt (upE cb ora up) (upV cb ora up)) →
      NE Z ∧ InvBW cb ora up s' Z := by
    intro Y Z hY hI henv hheap hblk
    refine ⟨hY.transfer hheap, hI.transfer hres' ?_ hheap ?_⟩
    · intro x h1 h2 a ha
      rw [withSets_env Z _ _ h1 h2]; exact henv x h1 h2 a ha
    · intro G cnt hb'
      rw [withSets_xe hc, withSets_xv]; exact hblk G cnt hb'
  have plainCase : st.plainB = true → NE (astepBW cb ora up i st X) ∧
      InvBW cb ora (up ++ (Prog.stmt st).calls) s' (astepBW cb ora up i st X) := by
    intro hp
    have hcall : st.callArgs? = none := by cases st <;> first | rfl | cases hp
    rw [hnc hcall]
    have hab : astepBW cb ora up i st X = astepVS cb i st X := by
      cases st <;> first | rfl | cases hp
    rw [hab]
    obtain ⟨hne1, hI⟩ := step_soundVS hc hok hnull hb hsH hneH h hst
    obtain ⟨m1, m2, m3, m4⟩ := astepVS_withSets hc (i := i) hp hok X (upE cb ora up) (upV cb ora up)
    refine tr _ _ hne1 hI ?_ ?_ ?_
    · intro z h1 h2 a ha; rw [m1 z h1 h2] at ha; exact ha
    · intro o c a ha; rw [m2] at ha; exact ha
    · intro G cnt hb'; rw [m3, m4] at hb'; exact hb'
  cases st with
  | call ret a args =>
    have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
    have hargsR : ∀ v ∈ args, v ≠ cb.cn.xe ∧ v ≠ cb.xv :=
      fun v hv => ⟨nx v (by simp [Stmt.vars, hv]), nv v (by simp [Stmt.vars, hv])⟩
    have hcons' : LeMain cb X (ora a) := hcons
    obtain ⟨h', hh, rfl⟩ : ∃ h', HavocN src cb.cn.statics s.cs args a (s.cs.cnt a) h' ∧
        s' = { s with cs := ({ s.cs with heap := h' }.setRet ret
          (some (.sym (.fresh a (s.cs.cnt a)) []))).bump a } := by
      cases hst with
      | call hh => exact ⟨_, hh, rfl⟩
    obtain ⟨G, hg, hx, hn, hN⟩ := h
    generalize hXH : withSets cb X (upE cb ora up) (upV cb ora up) = XH at hg hx hn hN hsH hneH
    have hle : ∀ v ∈ args, XH.env v ⊆ (ora a).env v := by
      intro v hv
      rw [← hXH, withSets_env X _ _ (hargsR v hv).1 (hargsR v hv).2]
      exact hcons'.1 v (hargs v hv) (hargsR v hv).1 (hargsR v hv).2
    obtain ⟨hg1, hx1⟩ := callOra_sound (src := src) hc hg hx hn hargs hh hsH (hora a) hneH hle
      (by rw [← hXH]; exact hcons'.2)
    have hN1 := InvN.callGen (Y := setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2) hx hn hN hh rfl (by
      intro x b hb
      show b ∈ fupd (fupd XH.env cb.cn.xe _) cb.xv _ x
      by_cases e1 : x = cb.xv
      · subst e1; rw [fupd_same]; exact mem_uni.mpr (Or.inr hb)
      · rw [fupd_ne _ _ e1]
        by_cases e2 : x = cb.cn.xe
        · subst e2; rw [fupd_same]; exact mem_uni.mpr (Or.inr hb)
        · rw [fupd_ne _ _ e2]; exact hb)
    have hle1 : GhostLe (ghostsAfter cb G src s.cs.cnt h' (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2) a (s.cs.cnt a)) s.cs.cnt := ghostLe_after hn.2
    have h2 := InvG.retire hc.cn.base a
      (fun o ho => alphaBO_bump (cb := cb) { s.cs with heap := h' } hle1 a ho) hg1
    have hx2 := InvXB.retire (st := { s.cs with heap := h' }) hc a hle1 hg1 hx1
    have hn2 : CntOKB (ghostsAfter cb G src s.cs.cnt h' (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2) a (s.cs.cnt a)) ({ s.cs with heap := h' }.bump a).cnt := cnt_afterB hn
    have hN2 := InvN.retire (vs := { s with cs := { s.cs with heap := h' } }) hc a hle1 hN1
    -- the post-call abstract state with the sets, before the result
    have hpre : InvVS cb { s with cs := ({ s.cs with heap := h' }).bump a }
        (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)) :=
      ⟨(ghostsAfter cb G src s.cs.cnt h' (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2) a (s.cs.cnt a)), h2.mono (retire_sub_retireV _ a _), hx2.mono (fun _ h => h) (fun _ h => h), hn2, hN2⟩
    have hneR : NE (retireV cb.cn.ctx.K a X) := hne.retireV _ a
    -- the sets after the call: the old sets and the contribution, renamed
    have hblk : ∀ G' cnt, BlockedAll cb G' cnt
        ((retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.cn.xe)
        ((retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.xv) →
        BlockedAll cb G' cnt (upE cb ora (up ++ (Prog.stmt (.call ret a args)).calls))
          (upV cb ora (up ++ (Prog.stmt (.call ret a args)).calls)) := by
      intro G' cnt hb'
      have e1 : (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.cn.xe =
          renameL a (uni (contrib cb (ora a) args).1 (upE cb ora up)) := by
        show renameL a (fupd (fupd XH.env cb.cn.xe _) cb.xv _ cb.cn.xe) = _
        rw [fupd_ne _ _ (Ne.symm hc.xvNe), fupd_same, ← hXH, withSets_xe hc]
      have e2 : (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.xv =
          renameL a (uni (contrib cb (ora a) args).2 (upV cb ora up)) := by
        show renameL a (fupd (fupd XH.env cb.cn.xe _) cb.xv _ cb.xv) = _
        rw [fupd_same, ← hXH, withSets_xv]
      rw [e1, e2] at hb'
      have hlast : (a, args) ∈ up ++ (Prog.stmt (.call ret a args)).calls :=
        List.mem_append_right _ (by simp [Prog.calls, Prog.stmts, Stmt.callArgs?])
      refine (BlockedAll.unrename a hb').mono ?_ ?_
      · intro b hb
        rcases mem_uni.mp hb with h1 | h1
        · exact mem_upE.mpr ⟨(a, args), hlast, h1⟩
        · exact upE_mono (fun c hc => List.mem_append_left _ hc) h1
      · intro b hb
        rcases mem_uni.mp hb with h1 | h1
        · exact mem_upV.mpr ⟨(a, args), hlast, h1⟩
        · exact upV_mono (fun c hc => List.mem_append_left _ hc) h1
    have hmain : ∀ x, x ≠ cb.cn.xe → x ≠ cb.xv →
        (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env x = (retireV cb.cn.ctx.K a X).env x := by
      intro x h1 h2
      show renameL a (fupd (fupd XH.env cb.cn.xe _) cb.xv _ x) = renameL a (X.env x)
      rw [fupd_ne _ _ h2, fupd_ne _ _ h1, ← hXH, withSets_env X _ _ h1 h2]
    have hheapEq : ∀ o c, (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).heap o c =
        (retireV cb.cn.ctx.K a X).heap o c := by
      intro o c; rw [← hXH]; rfl
    refine ⟨hneR.setRet ret _, ?_⟩
    show InvVS cb _ (withSets cb ((retireV cb.cn.ctx.K a X).setRet ret [.sym (.fresh a) []]) _ _)
    cases ret with
    | none =>
      refine hpre.transfer hres' ?_ ?_ ?_
      · intro x h1 h2 b hb
        rw [withSets_env _ _ _ h1 h2]
        change b ∈ (retireV cb.cn.ctx.K a X).env x
        rw [← hmain x h1 h2]; exact hb
      · intro o c b hb; rw [hheapEq] at hb; exact hb
      · intro G' cnt hb'; rw [withSets_xe hc, withSets_xv]; exact hblk G' cnt hb'
    | some x =>
      have hxv := hok.vars x (by simp [Stmt.vars])
      have hx1 := nx x (by simp [Stmt.vars])
      have hx2' := nv x (by simp [Stmt.vars])
      obtain ⟨G2, hg3, hx3, hn3, hN3⟩ := hpre
      have hpost : InvVS cb { s with cs := ({ s.cs with heap := h' }.setRet (some x)
            (some (.sym (.fresh a (s.cs.cnt a)) []))).bump a }
          ((retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).setVar x [.sym (.fresh a) []]) := by
        refine ⟨G2, ?_, hx3.setVar (S := [.sym (.fresh a) []])
          (v := some (.sym (.fresh a (s.cs.cnt a)) [])) hx1 hx2', hn3,
          hN3.setVarV (v := .obj (.sym (.fresh a (s.cs.cnt a)) [])) hxv (fun t e => by cases e)⟩
        refine InvG.setVar hg3 hxv ?_ (fun _ _ e => by cases e)
        intro o e
        cases e
        rw [alphaBO_fresh]
        refine ⟨?_, hok.freshS a rfl, List.mem_singleton.mpr rfl⟩
        rintro ⟨ho, hn'⟩
        have := Budget.stmt_site hb rfl ho
        omega
      refine hpost.transfer hres' ?_ ?_ ?_
      · intro z h1 h2 b hb
        rw [withSets_env _ _ _ h1 h2]
        change b ∈ fupd _ x _ z at hb
        show b ∈ fupd _ x _ z
        by_cases e : z = x
        · subst e; rw [fupd_same] at hb ⊢; exact hb
        · rw [fupd_ne _ _ e] at hb ⊢; rw [← hmain z h1 h2]; exact hb
      · intro o c b hb
        have := hheapEq o c
        change b ∈ (retireV cb.cn.ctx.K a (setSets cb XH _ _)).heap o c at hb
        rw [this] at hb; exact hb
      · intro G' cnt hb'
        rw [withSets_xe hc, withSets_xv]
        have e1 : ((retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).setVar x
            [.sym (.fresh a) []]).env cb.cn.xe =
            (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.cn.xe := fupd_ne _ _ (Ne.symm hx1)
        have e2 : ((retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).setVar x
            [.sym (.fresh a) []]).env cb.xv =
            (retireV cb.cn.ctx.K a (setSets cb XH (contrib cb (ora a) args).1 (contrib cb (ora a) args).2)).env cb.xv := fupd_ne _ _ (Ne.symm hx2')
        rw [e1, e2] at hb'
        exact hblk G' cnt hb'
  | store x f y =>
    rw [hnc rfl]
    have hx1 := nx x (by simp [Stmt.vars]); have hx2 := nv x (by simp [Stmt.vars])
    have hy1 := nx y (by simp [Stmt.vars]); have hy2 := nv y (by simp [Stmt.vars])
    obtain ⟨hne1, hI⟩ := step_soundVS hc hok hnull hb hsH hneH h hst
    have e : astepVS cb i (.store x f y) (withSets cb X (upE cb ora up) (upV cb ora up)) =
        BlockOnly.storeBO cb (withSets cb X (upE cb ora up) (upV cb ora up)) x (.fld f)
          (X.env y) := by
      show BlockOnly.storeBO cb _ x (.fld f) ((withSets cb X _ _).env y) = _
      rw [withSets_env X _ _ hy1 hy2]
    rw [e] at hne1 hI
    have hheap := storeBO_withSets_heap hc X (upE cb ora up) (upV cb ora up) hx1 hx2 (.fld f) (X.env y)
    refine tr _ _ hne1 hI ?_ ?_ ?_
    · intro z h1 h2 a ha
      rw [storeBO_env', withSets_env X _ _ h1 h2] at ha
      show a ∈ (storeT cb _ _ X x (.fld f) (X.env y)).env z
      rw [storeT_env]; exact ha
    · intro o c a ha
      rw [hheap] at ha; exact ha
    · intro G cnt hb'
      rw [storeBO_env', withSets_xe hc, withSets_xv] at hb'; exact hb'
  | new x a =>
    rw [hnc rfl]
    have hx1 := nx x (by simp [Stmt.vars]); have hx2 := nv x (by simp [Stmt.vars])
    obtain ⟨hne1, hI⟩ := step_soundVS hc hok hnull hb hsH hneH h hst
    refine tr _ _ hne1 hI ?_ (fun o c a ha => ha) ?_
    · intro z h1 h2 a' ha
      change a' ∈ fupd _ x _ z at ha
      show a' ∈ fupd _ x _ z
      by_cases e : z = x
      · subst e; rw [fupd_same] at ha ⊢; exact ha
      · rw [fupd_ne _ _ e] at ha ⊢
        change a' ∈ renameL a ((withSets cb X _ _).env z) at ha
        rw [withSets_env X _ _ h1 h2] at ha; exact ha
    · intro G cnt hb'
      have e1 : ((retireV cb.cn.ctx.K a (withSets cb X (upE cb ora up) (upV cb ora up))).setVar x
          [rNew a]).env cb.cn.xe = renameL a (upE cb ora up) := by
        show fupd _ x _ cb.cn.xe = _
        rw [fupd_ne _ _ (Ne.symm hx1)]
        show renameL a ((withSets cb X _ _).env cb.cn.xe) = _
        rw [withSets_xe hc]
      have e2 : ((retireV cb.cn.ctx.K a (withSets cb X (upE cb ora up) (upV cb ora up))).setVar x
          [rNew a]).env cb.xv = renameL a (upV cb ora up) := by
        show fupd _ x _ cb.xv = _
        rw [fupd_ne _ _ (Ne.symm hx2)]
        show renameL a ((withSets cb X _ _).env cb.xv) = _
        rw [withSets_xv]
      change BlockedAll cb G cnt (((retireV cb.cn.ctx.K a _).setVar x [rNew a]).env cb.cn.xe)
        (((retireV cb.cn.ctx.K a _).setVar x [rNew a]).env cb.xv) at hb'
      rw [e1, e2] at hb'
      exact BlockedAll.unrename a hb'
  | unknown x a =>
    rw [hnc rfl]
    have hx1 := nx x (by simp [Stmt.vars]); have hx2 := nv x (by simp [Stmt.vars])
    obtain ⟨hne1, hI⟩ := step_soundVS hc hok hnull hb hsH hneH h hst
    refine tr _ _ hne1 hI ?_ (fun o c a ha => ha) ?_
    · intro z h1 h2 a' ha
      change a' ∈ fupd _ x _ z at ha
      show a' ∈ fupd _ x _ z
      by_cases e : z = x
      · subst e; rw [fupd_same] at ha ⊢; exact ha
      · rw [fupd_ne _ _ e] at ha ⊢
        change a' ∈ renameL a ((withSets cb X _ _).env z) at ha
        rw [withSets_env X _ _ h1 h2] at ha; exact ha
    · intro G cnt hb'
      have e1 : ((retireV cb.cn.ctx.K a (withSets cb X (upE cb ora up) (upV cb ora up))).setVar x
          [.sym (.fresh a) []]).env cb.cn.xe = renameL a (upE cb ora up) := by
        show fupd _ x _ cb.cn.xe = _
        rw [fupd_ne _ _ (Ne.symm hx1)]
        show renameL a ((withSets cb X _ _).env cb.cn.xe) = _
        rw [withSets_xe hc]
      have e2 : ((retireV cb.cn.ctx.K a (withSets cb X (upE cb ora up) (upV cb ora up))).setVar x
          [.sym (.fresh a) []]).env cb.xv = renameL a (upV cb ora up) := by
        show fupd _ x _ cb.xv = _
        rw [fupd_ne _ _ (Ne.symm hx2)]
        show renameL a ((withSets cb X _ _).env cb.xv) = _
        rw [withSets_xv]
      change BlockedAll cb G cnt
        (((retireV cb.cn.ctx.K a _).setVar x [.sym (.fresh a) []]).env cb.cn.xe)
        (((retireV cb.cn.ctx.K a _).setVar x [.sym (.fresh a) []]).env cb.xv) at hb'
      rw [e1, e2] at hb'
      exact BlockedAll.unrename a hb'
  | null x => exact plainCase rfl
  | copy x y => exact plainCase rfl
  | load x y f => exact plainCase rfl
  | aload x y => exact plainCase rfl
  | astore x y => exact plainCase rfl

/-! ## Programs -/

/-- The store with given sets keeps support. -/
theorem supp_storeT {X : AState} (hs : Supp cb.cn.ctx X) (E V : List Origin) (x : Var) (c : ACell)
    {S : List Origin} (hS : S ⊆ cb.cn.ctx.origins) : Supp cb.cn.ctx (storeT cb E V X x c S) := by
  unfold storeT
  split
  · split
    · intro k hk
      rw [cval_setCell]
      split
      · exact hS
      · exact hs k hk
    · exact hs.weakStore _ c hS
  · exact hs.weakStore _ c hS

/-- One statement of the backward design keeps support. -/
theorem supp_astepBW (hc : CtxBOK cb) {ora : Oracle} {up : List (Site × List Var)} {X : AState}
    (hs : Supp cb.cn.ctx X) {i : Nat} {st : Stmt} (ok : StmtOKB cb st)
    (hnull : st.nullN = 1 → nullO i ∈ cb.cn.ctx.origins) :
    Supp cb.cn.ctx (astepBW cb ora up i st X) := by
  cases st with
  | call ret a args =>
    exact (supp_retireV hc hs a).setRet ret
      (by intro o ho; simp at ho; subst ho; exact ok.freshS a rfl)
  | store x f y => exact supp_storeT hs _ _ x _ (hs.env (ok.vars y (by simp [Stmt.vars])))
  | new x a => exact supp_astepVS hc hs ok hnull
  | unknown x a => exact supp_astepVS hc hs ok hnull
  | null x => exact supp_astepVS hc hs ok hnull
  | copy x y => exact supp_astepVS hc hs ok hnull
  | load x y f => exact supp_astepVS hc hs ok hnull
  | aload x y => exact supp_astepVS hc hs ok hnull
  | astore x y => exact supp_astepVS hc hs ok hnull

/-- The backward analysis keeps support. -/
theorem supp_analyzeBW (hc : CtxBOK cb) {ora : Oracle} :
    ∀ (q : Prog) (up : List (Site × List Var)) (i : Nat) (X : AState),
      (∀ st ∈ q.stmts, StmtOKB cb st) → NullsIn cb i q.nulls →
      Supp cb.cn.ctx X → Supp cb.cn.ctx (analyzeBW cb ora up i q X)
  | .skip, _, _, _, _, _, h => h
  | .stmt st, _, i, _, ok, hn, h =>
    supp_astepBW hc h (ok st (by simp [Prog.stmts]))
      (fun e => hn i (Nat.le_refl _) (by show i < i + st.nullN; rw [e]; exact Nat.lt_succ_self _))
  | .seq p q, up, i, X, ok, hn, h =>
    supp_analyzeBW hc q _ _ _ (fun st hs => ok st (List.mem_append_right _ hs)) hn.right
      (supp_analyzeBW hc p up i X (fun st hs => ok st (List.mem_append_left _ hs)) hn.left h)
  | .choice p q, up, i, X, ok, hn, h =>
    (supp_analyzeBW hc p up i X (fun st hs => ok st (List.mem_append_left _ hs)) hn.left h).join
      (supp_analyzeBW hc q up _ X (fun st hs => ok st (List.mem_append_right _ hs)) hn.right h)
  | .loop p, up, i, X, ok, hn, h =>
    Supp.loopIter (fun Y hY => supp_analyzeBW (ora := ora) hc p (up ++ p.calls) i Y ok hn hY) _ X h

/-- The invariant of the backward design moves to more upstream calls with the same sets or
larger ones. -/
theorem InvBW.sets {ora : Oracle} {up up' : List (Site × List Var)} {vs : VState} {X : AState}
    (hc : CtxBOK cb) (h : InvBW cb ora up vs X) (hres : Res cb vs)
    (hE : ∀ a ∈ upE cb ora up, a ∈ upE cb ora up') (hV : ∀ a ∈ upV cb ora up, a ∈ upV cb ora up') :
    InvBW cb ora up' vs X := by
  refine InvVS.transfer h hres ?_ (fun _ _ _ h => h) ?_
  · intro x h1 h2 a ha
    rw [withSets_env X _ _ h1 h2] at ha ⊢; exact ha
  · intro G cnt hb
    rw [withSets_xe hc, withSets_xv] at hb ⊢
    exact hb.mono hE hV

/-- A supported state is below each top state on the universe. -/
theorem leOn_top_of_supp {ctx : Ctx} {Z : AState} (hs : Supp ctx Z) (W : AState) :
    leOn ctx Z (top ctx W) = true := by
  refine leOn_iff.mpr ⟨fun x hx a ha => mem_uni.mpr (Or.inl (hs (.v x) hx ha)),
    fun o ho c hc a ha => mem_uni.mpr (Or.inl (hs (.h o c) ⟨ho, hc⟩ ha))⟩

/-- `withSets` keeps the inclusion on the universe. -/
theorem leOn_withSets (hc : CtxBOK cb) {A B : AState} (h : leOn cb.cn.ctx A B = true)
    (E V : List Origin) : leOn cb.cn.ctx (withSets cb A E V) (withSets cb B E V) = true := by
  obtain ⟨h1, h2⟩ := leOn_iff.mp h
  refine leOn_iff.mpr ⟨fun x hx a ha => ?_, fun o ho c hc1 a ha => h2 o ho c hc1 ha⟩
  by_cases e1 : x = cb.cn.xe
  · subst e1; rw [withSets_xe hc] at ha ⊢; exact ha
  · by_cases e2 : x = cb.xv
    · subst e2; rw [withSets_xv] at ha ⊢; exact ha
    · rw [withSets_env A E V e1 e2] at ha; rw [withSets_env B E V e1 e2]; exact h1 x hx ha

/-- A loop keeps an invariant state `Y` of the backward design if one run of the body keeps it. -/
theorem loop_keepsBW {ora : Oracle} {up : List (Site × List Var)} {i : Nat} {body : Prog}
    {Y : AState} (P : VState → Prop)
    (hstep : ∀ s t, P s → InvBW cb ora up s Y → ExecV src cb.cn.statics i body s t →
      P t ∧ InvBW cb ora up t Y) :
    ∀ {s u : VState}, ExecV src cb.cn.statics i (.loop body) s u → P s → InvBW cb ora up s Y →
      P u ∧ InvBW cb ora up u Y := by
  intro s u hx
  generalize hq : Prog.loop body = q at hx
  generalize hj : i = j at hx
  induction hx with
  | skip => intro hp h; exact ⟨hp, h⟩
  | stmt _ => cases hq
  | seq _ _ _ _ => cases hq
  | choiceL _ _ => cases hq
  | choiceR _ _ => cases hq
  | loopZero => intro hp h; exact ⟨hp, h⟩
  | loopMore h1 _ _ ih2 =>
    cases hq
    subst hj
    intro hp hi
    obtain ⟨hp', hi'⟩ := hstep _ _ hp hi h1
    exact ih2 rfl rfl hp' hi'

/-- The calls of `skip` are none. -/
theorem calls_skip : Prog.skip.calls = [] := rfl

/-- SOUNDNESS OF THE BACKWARD ANALYSIS: for a consistent oracle, each instrumented execution ends
in a state that the backward analysis result simulates, with the on-demand sets of all calls of
the program. -/
theorem analyze_soundBW (hc : CtxBOK cb) {ora : Oracle} (hora : ∀ s, Supp cb.cn.ctx (ora s)) :
    ∀ (q : Prog) (up : List (Site × List Var)) (i : Nat) {s s' : VState} {X : AState},
      (∀ st ∈ q.stmts, StmtOKB cb st) → UpOK cb up → NullsIn cb i q.nulls →
      Budget cb.cn.ctx q s.cs → Supp cb.cn.ctx X → NE X → Res cb s →
      InvBW cb ora up s X → ConsBW cb ora up i q X → ExecV src cb.cn.statics i q s s' →
      NE (analyzeBW cb ora up i q X) ∧ Res cb s' ∧
        InvBW cb ora (up ++ q.calls) s' (analyzeBW cb ora up i q X) := by
  intro q
  induction q with
  | skip =>
    intro up i s s' X _ _ _ _ _ hne hres h _ hx
    cases hx
    exact ⟨hne, hres, by rw [calls_skip, List.append_nil]; exact h⟩
  | stmt st =>
    intro up i s s' X hok hup hn hb hs hne hres h hcons hx
    cases hx with
    | stmt hst =>
      have hok1 := hok st (List.mem_singleton.mpr rfl)
      obtain ⟨h1, h2⟩ := step_soundBW hc hora hup hok1
        (fun e => hn i (Nat.le_refl _) (by show i < i + st.nullN; rw [e]; exact Nat.lt_succ_self _))
        hb hs hne hres h hcons hst
      exact ⟨h1, hres.step hok1 hst, h2⟩
  | seq p q ihp ihq =>
    intro up i s s' X hok hup hn hb hs hne hres h hcons hx
    cases hx with
    | seq h1 h2 =>
      have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
      have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
        fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
      obtain ⟨hne1, hres1, h1'⟩ := ihp up i hokp hup hn.left (Budget.seqL hb) hs hne hres h
        hcons.1 h1
      obtain ⟨hne2, hres2, h2'⟩ := ihq _ _ hokq (hup.append (upOK_calls hokp)) hn.right
        (Budget.seqR hb h1.toN.toExec) (supp_analyzeBW hc p up i X hokp hn.left hs) hne1 hres1 h1'
        hcons.2 h2
      refine ⟨hne2, hres2, ?_⟩
      show InvBW cb ora (up ++ (Prog.seq p q).calls) s' _
      rw [calls_seq, ← List.append_assoc]; exact h2'
  | choice p q ihp ihq =>
    intro up i s s' X hok hup hn hb hs hne hres h hcons hx
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inl hs))
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st :=
      fun st hs => hok st (List.mem_append.mpr (Or.inr hs))
    have fin : ∀ (A : AState) (l : List (Site × List Var)), (∀ c ∈ l, c ∈ p.calls ++ q.calls) →
        A.Sub (analyzeBW cb ora up i (.choice p q) X) → ∀ t, Res cb t →
        InvBW cb ora (up ++ l) t A →
        InvBW cb ora (up ++ (Prog.choice p q).calls) t (analyzeBW cb ora up i (.choice p q) X) := by
      intro A l hl hsub t hres' hI
      rw [calls_choice]
      have hmem : ∀ c ∈ up ++ l, c ∈ up ++ (p.calls ++ q.calls) := by
        intro c hc1
        rcases List.mem_append.mp hc1 with h1 | h1
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (hl c h1)
      refine InvVS.transfer hI hres' ?_ ?_ ?_
      · intro x h1 h2 a ha
        rw [withSets_env _ _ _ h1 h2] at ha ⊢; exact hsub.1 x ha
      · intro o c a ha; exact hsub.2 o c ha
      · intro G cnt hb'
        rw [withSets_xe hc, withSets_xv] at hb' ⊢
        exact hb'.mono (fun a ha => upE_mono hmem ha) (fun a ha => upV_mono hmem ha)
    cases hx with
    | choiceL h1 =>
      obtain ⟨hne1, hres1, h1'⟩ := ihp up i hokp hup hn.left (Budget.choiceL hb) hs hne hres h
        hcons.1 h1
      exact ⟨hne1.join _, hres1, fin _ p.calls (fun c hc1 => List.mem_append_left _ hc1)
        (sub_join_left _ _) _ hres1 h1'⟩
    | choiceR h1 =>
      obtain ⟨hne1, hres1, h1'⟩ := ihq up _ hokq hup hn.right (Budget.choiceR hb) hs hne hres h
        hcons.2 h1
      exact ⟨hne1.mono (sub_join_right _ _), hres1, fin _ q.calls
        (fun c hc1 => List.mem_append_right _ hc1) (sub_join_right _ _) _ hres1 h1'⟩
  | loop body ih =>
    intro up i s s' X hok hup hn hb hs hne hres h hcons hx
    show NE (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) ∧
      Res cb s' ∧ InvBW cb ora (up ++ body.calls) s'
        (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X)
    have hup' : UpOK cb (up ++ body.calls) := hup.append (upOK_calls hok)
    have hsY := Supp.loopIter (f := analyzeBW cb ora (up ++ body.calls) i body)
      (fun Y hY => supp_analyzeBW (ora := ora) hc body (up ++ body.calls) i Y hok hn hY)
      cb.cn.ctx.fuel X hs
    have hneY := hne.loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel
    have hsubY := sub_loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body)
      cb.cn.ctx.fuel X
    have hY : InvBW cb ora (up ++ body.calls) s
        (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) := by
      refine InvVS.transfer h hres ?_ ?_ ?_
      · intro x h1 h2 a ha
        rw [withSets_env _ _ _ h1 h2] at ha ⊢; exact hsubY.1 x ha
      · intro o c a ha; exact hsubY.2 o c ha
      · intro G cnt hb'
        rw [withSets_xe hc, withSets_xv] at hb' ⊢
        exact hb'.mono (fun a ha => upE_mono (fun c hc1 => List.mem_append_left _ hc1) ha)
          (fun a ha => upV_mono (fun c hc1 => List.mem_append_left _ hc1) ha)
    have hcons' : ConsBW cb ora (up ++ body.calls) i body
        (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) := hcons
    have hstep : ∀ s1 t, (Budget cb.cn.ctx (.loop body) s1.cs ∧ Res cb s1) →
        InvBW cb ora (up ++ body.calls) s1
          (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) →
        ExecV src cb.cn.statics i body s1 t →
        (Budget cb.cn.ctx (.loop body) t.cs ∧ Res cb t) ∧ InvBW cb ora (up ++ body.calls) t
          (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) := by
      intro s1 t ⟨hb1, hres1⟩ hi1 hx1
      obtain ⟨_, hres3, hf⟩ := ih (up ++ body.calls) i hok hup' hn (Budget.body hb1) hsY hneY hres1
        hi1 hcons' hx1
      refine ⟨⟨Budget.again hb1 hx1.toN.toExec, hres3⟩, ?_⟩
      have hf' := hf.sets hc hres3
        (fun a ha => upE_mono (fun c hc1 => by
          rcases List.mem_append.mp hc1 with h1 | h1
          · exact h1
          · exact List.mem_append_right _ h1) ha)
        (fun a ha => upV_mono (fun c hc1 => by
          rcases List.mem_append.mp hc1 with h1 | h1
          · exact h1
          · exact List.mem_append_right _ h1) ha)
      have hle : leOn cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body
          (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X))
          (loopIter cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X) = true := by
        rcases loopIter_post cb.cn.ctx (analyzeBW cb ora (up ++ body.calls) i body) cb.cn.ctx.fuel X
          with hpost | ⟨W, hW⟩
        · exact hpost
        · rw [hW]
          exact leOn_top_of_supp (supp_analyzeBW (ora := ora) hc body (up ++ body.calls) i _ hok hn
            (hW ▸ hsY)) W
      exact hf'.mono_leOn hc (leOn_withSets hc hle _ _)
    obtain ⟨⟨_, hres2⟩, hfin⟩ := loop_keepsBW
      (fun t => Budget cb.cn.ctx (.loop body) t.cs ∧ Res cb t) hstep hx ⟨hb, hres⟩ hY
    exact ⟨hneY, hres2, hfin⟩

/-! ## Whole programs -/

/-- The reserved variables of the context of design VS are not frame variables. -/
theorem ctxVS_res_frame (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) :
    (ctxVS eu K statics fr p qf).cn.xe ∉ fr.vars ∧ (ctxVS eu K statics fr p qf).xv ∉ fr.vars := by
  have hpv : ∀ v ∈ fr.vars, v ∈ progVars fr p := fun v hv =>
    List.mem_eraseDups.mpr (List.mem_append.mpr (Or.inr hv))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := lt_freshVar (hpv _ h)
    exact Nat.lt_irrefl _ this
  · have := lt_freshVar (hpv _ h)
    exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) this)

/-- The entry state has empty reserved variables. -/
theorem res_init (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) : Res (ctxVS eu K statics fr p qf) (VState.init fr) := by
  obtain ⟨h1, h2⟩ := ctxVS_res_frame eu K statics fr p qf
  have n1 : fr.root? (ctxVS eu K statics fr p qf).cn.xe = none :=
    lookup_none_of_not_mem fr.binds _ h1
  have n2 : fr.root? (ctxVS eu K statics fr p qf).xv = none :=
    lookup_none_of_not_mem fr.binds _ h2
  refine ⟨?_, ?_, rfl, rfl⟩
  · show (fr.root? _).map _ = none; rw [n1]; rfl
  · show (fr.root? _).map _ = none; rw [n2]; rfl

/-- The entry state satisfies the invariant of the backward design with no upstream call. -/
theorem inv_initBW (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (qf : List Field) (ora : Oracle) :
    InvBW (ctxVS eu K statics fr p qf) ora [] (VState.init fr) (ainitV K fr) := by
  have hc := ctxVS_ok eu K statics fr p qf
  obtain ⟨h1, h2⟩ := ctxVS_res_frame eu K statics fr p qf
  have n1 : fr.root? (ctxVS eu K statics fr p qf).cn.xe = none :=
    lookup_none_of_not_mem fr.binds _ h1
  have n2 : fr.root? (ctxVS eu K statics fr p qf).xv = none :=
    lookup_none_of_not_mem fr.binds _ h2
  have e1 : (ainitV K fr).env (ctxVS eu K statics fr p qf).cn.xe = [] := by
    show (match fr.root? _ with | some r => [Origin.sym (.root r) []] | none => []) = []
    rw [n1]
  have e2 : (ainitV K fr).env (ctxVS eu K statics fr p qf).xv = [] := by
    show (match fr.root? _ with | some r => [Origin.sym (.root r) []] | none => []) = []
    rw [n2]
  refine InvVS.transfer (inv_initVS hc (ctxVS_frame eu K statics fr p qf))
    (res_init eu K statics fr p qf) ?_ (fun _ _ _ h => h) ?_
  · intro x h1 h2 a ha; rw [withSets_env _ _ _ h1 h2]; exact ha
  · intro G cnt hb
    rw [withSets_xe hc, withSets_xv]
    have e1' : (ainitV (ctxVS eu K statics fr p qf).cn.ctx.K fr).env
        (ctxVS eu K statics fr p qf).cn.xe = [] := e1
    have e2' : (ainitV (ctxVS eu K statics fr p qf).cn.ctx.K fr).env
        (ctxVS eu K statics fr p qf).xv = [] := e2
    rw [e1', e2'] at hb
    exact hb

/-- The path evaluation does not read the variables. -/
theorem aevalFrom_withSets (X : AState) (E V : List Origin) :
    ∀ (S : List Origin) (q : List ACell), aevalFrom (withSets cb X E V) S q = aevalFrom X S q
  | _, [] => rfl
  | S, c :: cs => aevalFrom_withSets X E V (aread X S c) cs

/-- SOUNDNESS OF THE BACKWARD DESIGN (programs with loops): for each oracle whose states are
supported and dominate the state at each call that the backward analysis reaches (`ConsBW`),
each one-execution value alias of the instrumented strict narrow semantics is a may-alias of
the backward analysis. -/
theorem csoundBW (src : Nat → Obj × Cell) (statics : List Root) (eu : Bool) (K : Nat)
    (fr : Frame) (p : Prog) (x : Var) (px : List Cell) (y : Var) (py : List Cell) (ora : Oracle)
    (hora : ∀ s, Supp (ctxVS eu K statics fr p
      (afields (px.map Cell.abs) ++ afields (py.map Cell.abs))).cn.ctx (ora s))
    (hcons : ConsBW (ctxVS eu K statics fr p
      (afields (px.map Cell.abs) ++ afields (py.map Cell.abs))) ora [] 0 p (ainitV K fr))
    (h : CAliasV src statics fr p x px y py) :
    mayProgBW eu K statics fr p ora x (px.map Cell.abs) y (py.map Cell.abs) = true := by
  obtain ⟨vs, hx, ha⟩ := h
  let qf := afields (px.map Cell.abs) ++ afields (py.map Cell.abs)
  have hc := ctxVS_ok eu K statics fr p qf
  obtain ⟨_, hres, hinv⟩ := analyze_soundBW (src := src) hc hora p [] 0
    (ctxVS_stmts eu K statics fr p qf) (fun _ h => by cases h)
    (fun j _ hj => ctxVS_nulls eu K statics fr p qf (by omega))
    (ctxVS_budget eu K statics fr p qf) (supp_ainitVS eu K statics fr p qf) (NE_ainitV K fr)
    (res_init eu K statics fr p qf) (inv_initBW eu K statics fr p qf ora) hcons hx
  have hcx := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inl ha))
  have hcy := query_cells (cells := p.fields) qf (fun a ha => List.mem_append.mpr (Or.inr ha))
  have hm := hinv.may_of_alias hcx hcy ha
  -- a reserved variable has no value
  have nres : ∀ z, z = (ctxVS eu K statics fr p qf).cn.xe ∨ z = (ctxVS eu K statics fr p qf).xv →
      vs.val z = none := by
    rintro z (rfl | rfl)
    · unfold VState.val; rw [hres.1, hres.2.2.1]; rfl
    · unfold VState.val; rw [hres.2.1, hres.2.2.2]; rfl
  have nv : ∀ z (pz : List Cell) v, vs.evalV z pz = some v →
      z ≠ (ctxVS eu K statics fr p qf).cn.xe ∧ z ≠ (ctxVS eu K statics fr p qf).xv := by
    intro z pz v he
    refine ⟨fun e => ?_, fun e => ?_⟩
    · unfold VState.evalV at he; rw [nres z (Or.inl e)] at he; cases he
    · unfold VState.evalV at he; rw [nres z (Or.inr e)] at he; cases he
  obtain ⟨v, h1, h2⟩ := ha
  obtain ⟨ex1, ex2⟩ := nv x px v h1
  obtain ⟨ey1, ey2⟩ := nv y py v h2
  unfold mayProgBW
  unfold may aevalPath at hm ⊢
  rw [withSets_env _ _ _ ex1 ex2, withSets_env _ _ _ ey1 ey2, aevalFrom_withSets,
    aevalFrom_withSets] at hm
  exact hm

end DirectedAlias.Sound.ValueSem
