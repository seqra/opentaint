import DirectedAlias.Sound.ValueSem.Backward

/-!
# Backward search equals the forward test on loop-free programs

For a LOOP-FREE program whose sites are pairwise different (each statement has its own site,
as program points do), the backward analysis with the oracle of the forward pre-states computes
the same states and the same uniqueness answers as design VS, outside the reserved keys
(`bw_eq`, `mayProgBW_eq`). So the two reserved keys can be dropped there.

The proof has three parts.
* `Corr`: the forward state and the backward state agree outside the reserved keys, and the
  forward `Etree`/`Eval` hold exactly the on-demand sets of the upstream calls.
* `NoHit`: the forward `retire` of a site does not rename the sets (the most recent object of a
  site is not in a contribution before the site runs). This follows from FRESHNESS: before site
  `t` runs, no abstract set holds `new(t)` (`Fresh`, `fresh_analyzeVS`), and a closure never
  falls back to the universe (`closeN_some`: the closure of a supported state ends within
  `|U| + 1` steps).
* `OraEq`: the oracle gives the forward pre-state of each call; `oraOf` builds it when the call
  sites are pairwise different.
-/

namespace DirectedAlias.Sound.ValueSem

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.Recency DirectedAlias.Sound.Havoc
open DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Opt DirectedAlias.Opt.Rec

variable {cb : CtxB}

/-! ## The closure ends -/

/-- A filter with a weaker test is not longer. -/
theorem length_filter_le_of {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | b :: l, h => by
    have ih := length_filter_le_of p q l (fun a ha => h a (List.mem_cons_of_mem _ ha))
    cases hp : p b with
    | true =>
      have hq := h b List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      exact Nat.succ_le_succ ih
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      cases hq : q b with
      | true => rw [List.filter_cons_of_pos hq]; exact Nat.le_succ_of_le ih
      | false => rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]; exact ih

/-- A filter with a weaker test and one more element is shorter. -/
theorem length_filter_lt {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → (∃ a ∈ l, q a = true ∧ p a = false) →
      (l.filter p).length < (l.filter q).length
  | [], _, ⟨a, ha, _⟩ => by cases ha
  | b :: l, h, ⟨a, ha, hqa, hpa⟩ => by
    have hle := length_filter_le_of p q l (fun a ha => h a (List.mem_cons_of_mem _ ha))
    cases hp : p b with
    | true =>
      have hq := h b List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      refine Nat.succ_lt_succ (length_filter_lt p q l (fun a ha => h a (List.mem_cons_of_mem _ ha))
        ⟨a, ?_, hqa, hpa⟩)
      rcases List.mem_cons.mp ha with e | e
      · subst e; rw [hp] at hpa; cases hpa
      · exact e
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      cases hq : q b with
      | true => rw [List.filter_cons_of_pos hq]; exact Nat.lt_succ_of_le hle
      | false =>
        rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]
        refine length_filter_lt p q l (fun a ha => h a (List.mem_cons_of_mem _ ha)) ⟨a, ?_, hqa, hpa⟩
        rcases List.mem_cons.mp ha with e | e
        · subst e; rw [hq] at hqa; cases hqa
        · exact e

/-- A failed subset test gives an element outside. -/
theorem not_subB {α : Type} [DecidableEq α] : ∀ {l m : List α}, subB l m = false → ∃ a ∈ l, a ∉ m
  | [], _, h => by simp [subB] at h
  | b :: l, m, h => by
    by_cases hb : b ∈ m
    · have h' : subB l m = false := by
        unfold subB at h ⊢
        rw [List.all_cons, decide_eq_true hb, Bool.true_and] at h
        exact h
      obtain ⟨a, ha, hn⟩ := not_subB h'
      exact ⟨a, List.mem_cons_of_mem _ ha, hn⟩
    · exact ⟨b, List.mem_cons_self, hb⟩

/-- THE CLOSURE ENDS: from a universe start set of a supported state, the closure of design BO
succeeds with each fuel above the number of universe origins outside the start set. -/
theorem closeN_some {X : AState} (hs : Supp cb.cn.ctx X) :
    ∀ (n : Nat) (R : List Origin), R ⊆ cb.cn.ctx.origins →
      (cb.cn.ctx.origins.filter (fun a => !decide (a ∈ R))).length < n →
      ∃ R', closeN cb.cn X n R = some R'
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, R, hR, h => by
    simp only [closeN]
    cases hsb : subB (succsN cb.cn X R) R with
    | true => exact ⟨R, rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      obtain ⟨a, ha, hn⟩ := not_subB hsb
      have hS := Opt.CellNamed.succsN_sub hs R
      apply closeN_some hs n _ (uni_sub hS hR)
      have hlt := length_filter_lt (fun b => !decide (b ∈ uni (succsN cb.cn X R) R))
        (fun b => !decide (b ∈ R)) cb.cn.ctx.origins
        (by
          intro b _ hb
          cases hm : decide (b ∈ R) with
          | false => rfl
          | true =>
            have : b ∈ uni (succsN cb.cn X R) R := mem_uni.mpr (Or.inr (of_decide_eq_true hm))
            rw [decide_eq_true this] at hb; cases hb)
        ⟨a, hS ha, by rw [decide_eq_false hn]; rfl,
          by rw [decide_eq_true (mem_uni.mpr (Or.inl ha))]; rfl⟩
      omega

/-- The closure of a supported state from a universe start set succeeds. -/
theorem closeN_some_top {X : AState} (hs : Supp cb.cn.ctx X) {R : List Origin}
    (hR : R ⊆ cb.cn.ctx.origins) :
    ∃ R', closeN cb.cn X (cb.cn.ctx.origins.length + 1) R = some R' :=
  closeN_some hs _ R hR (Nat.lt_succ_of_le (List.length_filter_le _ _))

/-- Each origin of a closure is in the start set or in a universe cell. -/
theorem closeN_mem {X : AState} :
    ∀ {n : Nat} {R0 R : List Origin}, closeN cb.cn X n R0 = some R → ∀ a ∈ R,
      a ∈ R0 ∨ ∃ u c, a ∈ X.heap u c
  | 0, _, _, h => by simp [closeN] at h
  | n + 1, R0, R, h => by
    simp only [closeN] at h
    split at h
    · cases h; exact fun a ha => Or.inl ha
    · intro a ha
      rcases closeN_mem h a ha with h1 | h1
      · rcases mem_uni.mp h1 with h2 | h2
        · obtain ⟨u, _, _, c, _, h3⟩ := mem_succsN.mp h2
          exact Or.inr ⟨u, c, h3⟩
        · exact Or.inl h2
      · exact Or.inr h1

/-! ## Freshness -/

/-- No abstract set of the state holds `new(t)`: the site `t` did not run. -/
def Fresh (t : Site) (X : AState) : Prop :=
  (∀ x, rNew t ∉ X.env x) ∧ ∀ o c, rNew t ∉ X.heap o c

/-- The entry state of design VS is fresh for each site. -/
theorem fresh_ainitV (K : Nat) (fr : Frame) (t : Site) : Fresh t (ainitV K fr) := by
  refine ⟨fun x h => ?_, fun o c h => ?_⟩
  · change rNew t ∈ (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => []) at h
    cases e : fr.root? x with
    | none => rw [e] at h; cases h
    | some r => rw [e, List.mem_singleton] at h; cases h
  · change rNew t ∈ [childCN K o c] at h
    rw [List.mem_singleton] at h
    exact childCN_ne_alloc K o c _ h.symm

/-- The renaming of a site keeps freshness of a list. -/
theorem not_mem_renameL {s t : Site} {l : List Origin} (h : rNew t ∉ l) :
    rNew t ∉ renameL s l := by
  intro hm
  obtain ⟨a, ha, e⟩ := List.mem_map.mp hm
  unfold renameO at e
  split at e
  · exact rOld_ne_rNew s t e
  · subst e; exact h ha

/-- `retireV` keeps freshness (the new most recent object gets only cell names). -/
theorem Fresh.retireV {t : Site} (s : Site) (K : Nat) {X : AState} (h : Fresh t X) :
    Fresh t (retireV K s X) := by
  refine ⟨fun x => not_mem_renameL (h.1 x), fun o c hm => ?_⟩
  change rNew t ∈ (if o = rNew s then [childCN K (rNew s) c] else (retire s X).heap o c) at hm
  split at hm
  · rw [List.mem_singleton] at hm; exact childCN_ne_alloc K _ c _ hm.symm
  · change rNew t ∈ (if o = rNew s then [] else if o = rOld s then
      renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap o c)) at hm
    split at hm
    · cases hm
    · split at hm
      · refine not_mem_renameL ?_ hm
        intro h2
        rcases mem_uni.mp h2 with h3 | h3
        · exact h.2 _ _ h3
        · exact h.2 _ _ h3
      · exact not_mem_renameL (h.2 o c) hm

/-- Setting a variable to a fresh set keeps freshness. -/
theorem Fresh.setVar {t : Site} {X : AState} (h : Fresh t X) (x : Var) {S : List Origin}
    (hS : rNew t ∉ S) : Fresh t (X.setVar x S) := by
  refine ⟨fun z hm => ?_, h.2⟩
  change rNew t ∈ fupd X.env x S z at hm
  by_cases e : z = x
  · subst e; rw [fupd_same] at hm; exact hS hm
  · rw [fupd_ne _ _ e] at hm; exact h.1 z hm

/-- A read of a fresh state is fresh. -/
theorem Fresh.aread {t : Site} {X : AState} (h : Fresh t X) (S : List Origin) (c : ACell) :
    rNew t ∉ aread X S c := by
  intro hm
  obtain ⟨o, _, h1⟩ := mem_aread.mp hm
  exact h.2 _ _ h1

/-- The contribution of a call at a fresh supported state is fresh. -/
theorem fresh_contrib (hc : CtxBOK cb) {t : Site} {X : AState} (h : Fresh t X)
    (hs : Supp cb.cn.ctx X) {args : List Var} (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) :
    rNew t ∉ (contrib cb X args).1 ∧ rNew t ∉ (contrib cb X args).2 := by
  obtain ⟨R, hR⟩ := closeN_some_top hs (callRoots_sub hc hs hargs)
  unfold contrib
  rw [hR]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rcases closeN_mem hR _ hm with h1 | ⟨u, c, h1⟩
    · rcases mem_uni.mp h1 with h2 | h2
      · obtain ⟨x, _, h3⟩ := mem_uniMap.mp h2
        exact h.1 x h3
      · obtain ⟨r, _, e⟩ := List.mem_map.mp h2
        cases e
    · exact h.2 _ _ h1
  · obtain ⟨u, _, _, c, _, h1⟩ := mem_succsN.mp hm
    exact h.2 _ _ h1

/-- The passive call at a fresh supported state is fresh. -/
theorem Fresh.callVS (hc : CtxBOK cb) {t : Site} {X : AState} (h : Fresh t X)
    (hs : Supp cb.cn.ctx X) {args : List Var} (hargs : ∀ a ∈ args, a ∈ cb.cn.ctx.vars) :
    Fresh t (callVS cb X args) := by
  rw [callVS_contrib]
  have hf := fresh_contrib hc h hs hargs
  refine ⟨fun x hm => ?_, h.2⟩
  change rNew t ∈ fupd (fupd X.env cb.cn.xe _) cb.xv _ x at hm
  by_cases e1 : x = cb.xv
  · subst e1; rw [fupd_same] at hm
    rcases mem_uni.mp hm with h1 | h1
    · exact hf.2 h1
    · exact h.1 _ h1
  · rw [fupd_ne _ _ e1] at hm
    by_cases e2 : x = cb.cn.xe
    · subst e2; rw [fupd_same] at hm
      rcases mem_uni.mp hm with h1 | h1
      · exact hf.1 h1
      · exact h.1 _ h1
    · rw [fupd_ne _ _ e2] at hm; exact h.1 x hm

/-- A store of design BO of a fresh set keeps freshness. -/
theorem Fresh.storeBO {t : Site} {X : AState} (h : Fresh t X) (x : Var) (c : ACell)
    {S : List Origin} (hS : rNew t ∉ S) : Fresh t (BlockOnly.storeBO cb X x c S) := by
  have hw : ∀ (os : List Origin), Fresh t (X.weakStore os c S) := by
    intro os
    refine ⟨h.1, fun o c' hm => ?_⟩
    change rNew t ∈ (if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c') at hm
    split at hm
    · rcases mem_uni.mp hm with h1 | h1
      · exact hS h1
      · exact h.2 _ _ h1
    · exact h.2 _ _ hm
  unfold BlockOnly.storeBO
  split
  · rename_i _ o0 _
    split
    · refine ⟨h.1, fun o c' hm => ?_⟩
      change rNew t ∈ fupd2 X.heap o0 c S o c' at hm
      by_cases e : o = o0 ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same] at hm; exact hS hm
      · rw [fupd2_ne _ _ e] at hm; exact h.2 _ _ hm
    · exact hw _
  · exact hw _

/-- A program without loops. -/
def LoopFree : Prog → Prop
  | .skip => True
  | .stmt _ => True
  | .seq p q => LoopFree p ∧ LoopFree q
  | .choice p q => LoopFree p ∧ LoopFree q
  | .loop _ => False

/-- FRESHNESS IS KEPT: a loop-free program that has no statement of site `t` keeps the state
fresh for `t`. -/
theorem fresh_analyzeVS (hc : CtxBOK cb) {t : Site} :
    ∀ (q : Prog) (i : Nat) (X : AState), LoopFree q → t ∉ q.sites →
      (∀ st ∈ q.stmts, StmtOKB cb st) → NullsIn cb i q.nulls → Supp cb.cn.ctx X → Fresh t X →
      Fresh t (analyzeVS cb i q X)
  | .skip, _, _, _, _, _, _, _, h => h
  | .stmt st, i, X, _, ht, ok, _, hs, h => by
    have hok := ok st (List.mem_singleton.mpr rfl)
    have hsite : ∀ s, st.site? = some s → s ≠ t := by
      intro s hs1 e
      subst e
      apply ht
      show s ∈ [st].filterMap Stmt.site?
      simp [hs1]
    cases st with
    | new x a =>
      exact (h.retireV a _).setVar x (by
        intro hm; rw [List.mem_singleton] at hm; exact hsite a rfl (rNew_inj hm).symm)
    | unknown x a =>
      exact (h.retireV a _).setVar x (by
        intro hm; rw [List.mem_singleton] at hm; cases hm)
    | call ret a args =>
      have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
      have h1 := (h.callVS hc hs hargs).retireV a cb.cn.ctx.K
      cases ret with
      | none => exact h1
      | some x => exact h1.setVar x (by intro hm; rw [List.mem_singleton] at hm; cases hm)
    | store x f y => exact h.storeBO x _ (h.1 y)
    | null x => exact h.setVar x (by intro hm; rw [List.mem_singleton] at hm; cases hm)
    | copy x y => exact h.setVar x (h.1 y)
    | load x y f => exact h.setVar x (h.aread _ _)
    | aload x y => exact h.setVar x (h.aread _ _)
    | astore x y =>
      refine ⟨h.1, fun o c' hm => ?_⟩
      change rNew t ∈ (if c' = .elem ∧ o ∈ X.env x then uni (X.env y) (X.heap o c')
        else X.heap o c') at hm
      split at hm
      · rcases mem_uni.mp hm with h1 | h1
        · exact h.1 y h1
        · exact h.2 _ _ h1
      · exact h.2 _ _ hm
  | .seq p q, i, X, ⟨lp, lq⟩, ht, ok, hn, hs, h => by
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    have htp : t ∉ p.sites := fun h1 => ht (by
      show t ∈ (p.stmts ++ q.stmts).filterMap Stmt.site?
      rw [List.filterMap_append]; exact List.mem_append_left _ h1)
    have htq : t ∉ q.sites := fun h1 => ht (by
      show t ∈ (p.stmts ++ q.stmts).filterMap Stmt.site?
      rw [List.filterMap_append]; exact List.mem_append_right _ h1)
    exact fresh_analyzeVS hc q _ _ lq htq hokq hn.right (supp_analyzeVS hc p i X hokp hn.left hs)
      (fresh_analyzeVS hc p i X lp htp hokp hn.left hs h)
  | .choice p q, i, X, ⟨lp, lq⟩, ht, ok, hn, hs, h => by
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    have htp : t ∉ p.sites := fun h1 => ht (by
      show t ∈ (p.stmts ++ q.stmts).filterMap Stmt.site?
      rw [List.filterMap_append]; exact List.mem_append_left _ h1)
    have htq : t ∉ q.sites := fun h1 => ht (by
      show t ∈ (p.stmts ++ q.stmts).filterMap Stmt.site?
      rw [List.filterMap_append]; exact List.mem_append_right _ h1)
    have h1 := fresh_analyzeVS hc p i X lp htp hokp hn.left hs h
    have h2 := fresh_analyzeVS hc q _ X lq htq hokq hn.right hs h
    refine ⟨fun x hm => ?_, fun o c hm => ?_⟩
    · rcases mem_uni.mp hm with h3 | h3
      · exact h1.1 x h3
      · exact h2.1 x h3
    · rcases mem_uni.mp hm with h3 | h3
      · exact h1.2 o c h3
      · exact h2.2 o c h3
  | .loop _, _, _, hl, _, _, _, _, _ => absurd hl id

/-! ## The forward run -/

/-- The forward `retire` of each site does not rename the two sets: at `new`, `unknown` and a
call of site `s`, the two sets of the forward state do not hold `new(s)`. -/
def NoHit (cb : CtxB) : Nat → Prog → AState → Prop
  | _, .skip, _ => True
  | _, .stmt (.new _ s), X => rNew s ∉ X.env cb.cn.xe ∧ rNew s ∉ X.env cb.xv
  | _, .stmt (.unknown _ s), X => rNew s ∉ X.env cb.cn.xe ∧ rNew s ∉ X.env cb.xv
  | _, .stmt (.call _ s args), X =>
    rNew s ∉ (callVS cb X args).env cb.cn.xe ∧ rNew s ∉ (callVS cb X args).env cb.xv
  | _, .stmt _, _ => True
  | i, .seq p q, X => NoHit cb i p X ∧ NoHit cb (i + p.nulls) q (analyzeVS cb i p X)
  | i, .choice p q, X => NoHit cb i p X ∧ NoHit cb (i + p.nulls) q X
  | _, .loop _, _ => True

/-- The oracle gives the forward pre-state of each call (through its contribution). -/
def OraEq (cb : CtxB) (ora : Oracle) : Nat → Prog → AState → Prop
  | _, .skip, _ => True
  | _, .stmt (.call _ s args), X => contrib cb (ora s) args = contrib cb X args
  | _, .stmt _, _ => True
  | i, .seq p q, X => OraEq cb ora i p X ∧ OraEq cb ora (i + p.nulls) q (analyzeVS cb i p X)
  | i, .choice p q, X => OraEq cb ora i p X ∧ OraEq cb ora (i + p.nulls) q X
  | _, .loop _, _ => True

/-- The sites of a sequence. -/
theorem sites_seq' (p q : Prog) : (Prog.seq p q).sites = p.sites ++ q.sites := by
  show (p.stmts ++ q.stmts).filterMap Stmt.site? = _
  rw [List.filterMap_append]; rfl

/-- The sites of a choice. -/
theorem sites_choice' (p q : Prog) : (Prog.choice p q).sites = p.sites ++ q.sites := by
  show (p.stmts ++ q.stmts).filterMap Stmt.site? = _
  rw [List.filterMap_append]; rfl

/-- NO RENAMING HIT: in a loop-free program with pairwise different sites, from a state that is
fresh for each site of the program, the forward `retire` never renames the two sets. -/
theorem noHit_of_fresh (hc : CtxBOK cb) :
    ∀ (q : Prog) (i : Nat) (X : AState), LoopFree q → q.sites.Nodup →
      (∀ st ∈ q.stmts, StmtOKB cb st) → NullsIn cb i q.nulls → Supp cb.cn.ctx X →
      (∀ s ∈ q.sites, Fresh s X) → NoHit cb i q X
  | .skip, _, _, _, _, _, _, _, _ => trivial
  | .stmt st, _, X, _, _, ok, _, hs, hf => by
    have hok := ok st (List.mem_singleton.mpr rfl)
    have hin : ∀ s, st.site? = some s → s ∈ (Prog.stmt st).sites := by
      intro s hs1; show s ∈ [st].filterMap Stmt.site?; simp [hs1]
    cases st with
    | new x a => exact ⟨(hf a (hin a rfl)).1 _, (hf a (hin a rfl)).1 _⟩
    | unknown x a => exact ⟨(hf a (hin a rfl)).1 _, (hf a (hin a rfl)).1 _⟩
    | call ret a args =>
      have hargs : ∀ v ∈ args, v ∈ cb.cn.ctx.vars := fun v hv => hok.vars v (by simp [Stmt.vars, hv])
      have h1 := (hf a (hin a rfl)).callVS hc hs hargs
      exact ⟨h1.1 _, h1.1 _⟩
    | store _ _ _ => trivial
    | null _ => trivial
    | copy _ _ => trivial
    | load _ _ _ => trivial
    | aload _ _ => trivial
    | astore _ _ => trivial
  | .seq p q, i, X, ⟨lp, lq⟩, hnd, ok, hn, hs, hf => by
    rw [sites_seq'] at hnd
    obtain ⟨n1, n2, n3⟩ := List.nodup_append.mp hnd
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    refine ⟨noHit_of_fresh hc p i X lp n1 hokp hn.left hs (fun s h1 => hf s (by
      rw [sites_seq']; exact List.mem_append_left _ h1)), ?_⟩
    refine noHit_of_fresh hc q _ _ lq n2 hokq hn.right (supp_analyzeVS hc p i X hokp hn.left hs) ?_
    intro s h1
    exact fresh_analyzeVS hc p i X lp (fun h2 => n3 s h2 s h1 rfl) hokp hn.left hs
      (hf s (by rw [sites_seq']; exact List.mem_append_right _ h1))
  | .choice p q, i, X, ⟨lp, lq⟩, hnd, ok, hn, hs, hf => by
    rw [sites_choice'] at hnd
    obtain ⟨n1, n2, _⟩ := List.nodup_append.mp hnd
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    exact ⟨noHit_of_fresh hc p i X lp n1 hokp hn.left hs (fun s h1 => hf s (by
        rw [sites_choice']; exact List.mem_append_left _ h1)),
      noHit_of_fresh hc q _ X lq n2 hokq hn.right hs (fun s h1 => hf s (by
        rw [sites_choice']; exact List.mem_append_right _ h1))⟩
  | .loop _, _, _, hl, _, _, _, _, _ => absurd hl id

/-! ## Equality of the forward and the backward analysis -/

/-- The forward state `F` and the backward state `B` agree outside the reserved keys, and the
forward sets are the on-demand sets of the upstream calls `up`. -/
def Corr (cb : CtxB) (ora : Oracle) (up : List (Site × List Var)) (F B : AState) : Prop :=
  (∀ x, x ≠ cb.cn.xe → x ≠ cb.xv → F.env x = B.env x) ∧ F.heap = B.heap ∧
    SetEq (F.env cb.cn.xe) (upE cb ora up) ∧ SetEq (F.env cb.xv) (upV cb ora up)

/-- The upstream sets of an append. -/
theorem upE_append (ora : Oracle) (u v : List (Site × List Var)) :
    SetEq (upE cb ora (u ++ v)) (uni (upE cb ora u) (upE cb ora v)) := by
  intro a
  rw [mem_uni, mem_upE, mem_upE, mem_upE]
  constructor
  · rintro ⟨c, hc, h⟩
    rcases List.mem_append.mp hc with h1 | h1
    · exact Or.inl ⟨c, h1, h⟩
    · exact Or.inr ⟨c, h1, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · exact ⟨c, List.mem_append_left _ hc, h⟩
    · exact ⟨c, List.mem_append_right _ hc, h⟩

/-- The upstream sets of an append. -/
theorem upV_append (ora : Oracle) (u v : List (Site × List Var)) :
    SetEq (upV cb ora (u ++ v)) (uni (upV cb ora u) (upV cb ora v)) := by
  intro a
  rw [mem_uni, mem_upV, mem_upV, mem_upV]
  constructor
  · rintro ⟨c, hc, h⟩
    rcases List.mem_append.mp hc with h1 | h1
    · exact Or.inl ⟨c, h1, h⟩
    · exact Or.inr ⟨c, h1, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · exact ⟨c, List.mem_append_left _ hc, h⟩
    · exact ⟨c, List.mem_append_right _ hc, h⟩

/-- The upstream calls of a statement that is not a call are none. -/
theorem calls_stmt_none {st : Stmt} (h : st.callArgs? = none) : (Prog.stmt st).calls = [] := by
  show [st].filterMap Stmt.callArgs? = []
  simp [h]

/-- The heap of `retireV` depends only on the heap. -/
theorem retireV_heap_congr (K : Nat) (s : Site) {F B : AState} (h : F.heap = B.heap) :
    (retireV K s F).heap = (retireV K s B).heap := by
  show (fun o c => if o = rNew s then _ else (retire s F).heap o c) =
    (fun o c => if o = rNew s then _ else (retire s B).heap o c)
  have : (retire s F).heap = (retire s B).heap := by
    show (fun o c => if o = rNew s then [] else if o = rOld s then
      renameL s (uni (F.heap (rNew s) c) (F.heap (rOld s) c)) else renameL s (F.heap o c)) =
      (fun o c => if o = rNew s then [] else if o = rOld s then
      renameL s (uni (B.heap (rNew s) c) (B.heap (rOld s) c)) else renameL s (B.heap o c))
    rw [h]
  rw [this]

/-- `retireV` keeps the correspondence outside the reserved keys. -/
theorem Corr.retireV {ora : Oracle} {up : List (Site × List Var)} {F B : AState}
    (h : Corr cb ora up F B) (K : Nat) (s : Site) :
    (∀ x, x ≠ cb.cn.xe → x ≠ cb.xv → (retireV K s F).env x = (retireV K s B).env x) ∧
      (retireV K s F).heap = (retireV K s B).heap := by
  refine ⟨fun x h1 h2 => ?_, retireV_heap_congr K s h.2.1⟩
  show renameL s (F.env x) = renameL s (B.env x)
  rw [h.1 x h1 h2]

/-- A set with no `new(s)` is kept by the renaming of `s`. -/
theorem renameL_id {s : Site} {l : List Origin} (h : rNew s ∉ l) : renameL s l = l :=
  renameL_of_not_mem h

/-- The path evaluation reads only the heap. -/
theorem aevalFrom_heap {X Y : AState} (h : X.heap = Y.heap) :
    ∀ (S : List Origin) (q : List ACell), aevalFrom X S q = aevalFrom Y S q
  | _, [] => rfl
  | S, c :: cs => by
    show aevalFrom X (aread X S c) cs = aevalFrom Y (aread Y S c) cs
    have : aread X S c = aread Y S c := by
      show uniMap (fun o => X.heap o c) S = uniMap (fun o => Y.heap o c) S
      rw [h]
    rw [this]; exact aevalFrom_heap h _ cs

/-- The uniqueness test of design BO depends only on the members of the two sets. -/
theorem uniqueBO_congr' {once : Site → Bool} {eu : Bool} {E E' V V' : List Origin}
    (hE : SetEq E E') (hV : SetEq V V') (o : Origin) :
    uniqueBO once eu E V o = uniqueBO once eu E' V' o := by
  unfold uniqueBO uniqueCN
  rw [Opt.CellNamed.expB_congr hE o]
  by_cases h : o ∈ V
  · rw [decide_eq_true h, decide_eq_true ((hV o).mp h)]
  · rw [decide_eq_false h, decide_eq_false (fun h' => h ((hV o).mpr h'))]

/-- FORWARD = BACKWARD ON LOOP-FREE PROGRAMS: if the forward retire never renames the sets
(`NoHit`) and the oracle gives the forward pre-states (`OraEq`), the backward analysis keeps the
correspondence: the same variables outside the reserved keys, the same heap, and forward sets that
are the on-demand sets of the upstream calls. -/
theorem bw_eq (hc : CtxBOK cb) {ora : Oracle} :
    ∀ (q : Prog) (up : List (Site × List Var)) (i : Nat) (F B : AState), LoopFree q →
      (∀ st ∈ q.stmts, StmtOKB cb st) → OraEq cb ora i q F → NoHit cb i q F →
      Corr cb ora up F B →
      Corr cb ora (up ++ q.calls) (analyzeVS cb i q F) (analyzeBW cb ora up i q B)
  | .skip, up, _, _, _, _, _, _, _, h => by rw [calls_skip, List.append_nil]; exact h
  | .stmt st, up, i, F, B, _, ok, ho, hh, h => by
    have hok := ok st (List.mem_singleton.mpr rfl)
    have nx : ∀ v ∈ st.vars, v ≠ cb.cn.xe := hok.noXe
    have nv : ∀ v ∈ st.vars, v ≠ cb.xv := hok.noXv
    -- setting a non-reserved variable to the same set
    have setv : ∀ (F' B' : AState) (x : Var) (S : List Origin), x ≠ cb.cn.xe → x ≠ cb.xv →
        (∀ z, z ≠ cb.cn.xe → z ≠ cb.xv → F'.env z = B'.env z) → F'.heap = B'.heap →
        (∀ z, z ≠ cb.cn.xe → z ≠ cb.xv → (F'.setVar x S).env z = (B'.setVar x S).env z) ∧
          (F'.setVar x S).heap = (B'.setVar x S).heap ∧
          (F'.setVar x S).env cb.cn.xe = F'.env cb.cn.xe ∧
          (F'.setVar x S).env cb.xv = F'.env cb.xv := by
      intro F' B' x S h1 h2 he hhp
      refine ⟨fun z hz1 hz2 => ?_, hhp, fupd_ne _ _ (Ne.symm h1), fupd_ne _ _ (Ne.symm h2)⟩
      show fupd F'.env x S z = fupd B'.env x S z
      by_cases e : z = x
      · subst e; rw [fupd_same, fupd_same]
      · rw [fupd_ne _ _ e, fupd_ne _ _ e]; exact he z hz1 hz2
    cases st with
    | new x a =>
      rw [calls_stmt_none rfl, List.append_nil]
      obtain ⟨r1, r2⟩ := h.retireV cb.cn.ctx.K a
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x [rNew a] (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) r1 r2
      refine ⟨s1, s2, ?_, ?_⟩
      · show SetEq (((retireV cb.cn.ctx.K a F).setVar x [rNew a]).env cb.cn.xe) _
        rw [s3]; show SetEq (renameL a (F.env cb.cn.xe)) _; rw [renameL_id hh.1]; exact h.2.2.1
      · show SetEq (((retireV cb.cn.ctx.K a F).setVar x [rNew a]).env cb.xv) _
        rw [s4]; show SetEq (renameL a (F.env cb.xv)) _; rw [renameL_id hh.2]; exact h.2.2.2
    | unknown x a =>
      rw [calls_stmt_none rfl, List.append_nil]
      obtain ⟨r1, r2⟩ := h.retireV cb.cn.ctx.K a
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x [.sym (.fresh a) []] (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) r1 r2
      refine ⟨s1, s2, ?_, ?_⟩
      · show SetEq (((retireV cb.cn.ctx.K a F).setVar x _).env cb.cn.xe) _
        rw [s3]; show SetEq (renameL a (F.env cb.cn.xe)) _; rw [renameL_id hh.1]; exact h.2.2.1
      · show SetEq (((retireV cb.cn.ctx.K a F).setVar x _).env cb.xv) _
        rw [s4]; show SetEq (renameL a (F.env cb.xv)) _; rw [renameL_id hh.2]; exact h.2.2.2
    | call ret a args =>
      have ho' : contrib cb (ora a) args = contrib cb F args := ho
      have hcall : (Prog.stmt (.call ret a args)).calls = [(a, args)] := rfl
      rw [hcall]
      -- the forward state after the passive call
      have hC : Corr cb ora (up ++ [(a, args)]) (callVS cb F args) B := by
        rw [callVS_contrib]
        refine ⟨fun x h1 h2 => ?_, h.2.1, ?_, ?_⟩
        · show fupd (fupd F.env cb.cn.xe _) cb.xv _ x = _
          rw [fupd_ne _ _ h2, fupd_ne _ _ h1]; exact h.1 x h1 h2
        · show SetEq (fupd (fupd F.env cb.cn.xe _) cb.xv _ cb.cn.xe) _
          rw [fupd_ne _ _ (Ne.symm hc.xvNe), fupd_same]
          refine (SetEq.trans (uni_comm_set _ _) (SetEq.uni h.2.2.1 ?_)).trans (upE_append ora up _).symm
          intro b
          rw [mem_upE, ← ho']
          constructor
          · intro hb; exact ⟨(a, args), List.mem_singleton.mpr rfl, hb⟩
          · rintro ⟨c, hc1, hb⟩; rw [List.mem_singleton.mp hc1] at hb; exact hb
        · show SetEq (fupd (fupd F.env cb.cn.xe _) cb.xv _ cb.xv) _
          rw [fupd_same]
          refine (SetEq.trans (uni_comm_set _ _) (SetEq.uni h.2.2.2 ?_)).trans (upV_append ora up _).symm
          intro b
          rw [mem_upV, ← ho']
          constructor
          · intro hb; exact ⟨(a, args), List.mem_singleton.mpr rfl, hb⟩
          · rintro ⟨c, hc1, hb⟩; rw [List.mem_singleton.mp hc1] at hb; exact hb
      obtain ⟨r1, r2⟩ := hC.retireV cb.cn.ctx.K a
      have hx3 : SetEq ((retireV cb.cn.ctx.K a (callVS cb F args)).env cb.cn.xe) (upE cb ora (up ++ [(a, args)])) := by
        show SetEq (renameL a ((callVS cb F args).env cb.cn.xe)) _
        rw [renameL_id hh.1]; exact hC.2.2.1
      have hx4 : SetEq ((retireV cb.cn.ctx.K a (callVS cb F args)).env cb.xv) (upV cb ora (up ++ [(a, args)])) := by
        show SetEq (renameL a ((callVS cb F args).env cb.xv)) _
        rw [renameL_id hh.2]; exact hC.2.2.2
      cases ret with
      | none => exact ⟨r1, r2, hx3, hx4⟩
      | some x =>
        obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x [.sym (.fresh a) []] (nx x (by simp [Stmt.vars]))
          (nv x (by simp [Stmt.vars])) r1 r2
        exact ⟨s1, s2, by rw [← s3] at hx3; exact hx3, by rw [← s4] at hx4; exact hx4⟩
    | store x f y =>
      rw [calls_stmt_none rfl, List.append_nil]
      have hx1 := nx x (by simp [Stmt.vars]); have hx2 := nv x (by simp [Stmt.vars])
      have hy1 := nx y (by simp [Stmt.vars]); have hy2 := nv y (by simp [Stmt.vars])
      have hu : ∀ o, uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (F.env cb.cn.xe) (F.env cb.xv) o =
          uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (upE cb ora up) (upV cb ora up) o :=
        uniqueBO_congr' h.2.2.1 h.2.2.2
      refine ⟨fun z h1 h2 => ?_, ?_, ?_, ?_⟩
      · show (BlockOnly.storeBO cb F x (.fld f) (F.env y)).env z =
          (storeT cb _ _ B x (.fld f) (B.env y)).env z
        rw [storeBO_env', storeT_env]; exact h.1 z h1 h2
      · show (BlockOnly.storeBO cb F x (.fld f) (F.env y)).heap =
          (storeT cb _ _ B x (.fld f) (B.env y)).heap
        unfold BlockOnly.storeBO storeT
        rw [h.1 x hx1 hx2, h.1 y hy1 hy2]
        cases single? (B.env x) with
        | none => show (F.weakStore _ _ _).heap = (B.weakStore _ _ _).heap; unfold AState.weakStore; rw [h.2.1]
        | some o =>
          simp only
          rw [hu o]
          by_cases hq : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (upE cb ora up) (upV cb ora up) o = true
          · rw [ite_eq_left hq, ite_eq_left hq]
            show fupd2 F.heap o _ _ = fupd2 B.heap o _ _; rw [h.2.1]
          · rw [ite_eq_right hq, ite_eq_right hq]
            show (F.weakStore _ _ _).heap = (B.weakStore _ _ _).heap; unfold AState.weakStore; rw [h.2.1]
      · show SetEq ((BlockOnly.storeBO cb F x (.fld f) (F.env y)).env cb.cn.xe) _
        rw [storeBO_env']; exact h.2.2.1
      · show SetEq ((BlockOnly.storeBO cb F x (.fld f) (F.env y)).env cb.xv) _
        rw [storeBO_env']; exact h.2.2.2
    | null x =>
      rw [calls_stmt_none rfl, List.append_nil]
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x [nullO i] (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) h.1 h.2.1
      exact ⟨s1, s2, by have := h.2.2.1; rw [← s3] at this; exact this,
        by have := h.2.2.2; rw [← s4] at this; exact this⟩
    | copy x y =>
      rw [calls_stmt_none rfl, List.append_nil]
      have e : F.env y = B.env y := h.1 y (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x (F.env y) (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) h.1 h.2.1
      refine ⟨fun z h1 h2 => ?_, s2, by have := h.2.2.1; rw [← s3] at this; exact this,
        by have := h.2.2.2; rw [← s4] at this; exact this⟩
      show (F.setVar x (F.env y)).env z = (B.setVar x (B.env y)).env z
      rw [← e]; exact s1 z h1 h2
    | load x y f =>
      rw [calls_stmt_none rfl, List.append_nil]
      have e : aread F (F.env y) (.fld f) = aread B (B.env y) (.fld f) := by
        rw [h.1 y (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))]
        show uniMap (fun o => F.heap o _) _ = uniMap (fun o => B.heap o _) _
        rw [h.2.1]
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x (aread F (F.env y) (.fld f)) (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) h.1 h.2.1
      refine ⟨fun z h1 h2 => ?_, s2, by have := h.2.2.1; rw [← s3] at this; exact this,
        by have := h.2.2.2; rw [← s4] at this; exact this⟩
      show (F.setVar x (aread F (F.env y) (.fld f))).env z = (B.setVar x (aread B (B.env y) (.fld f))).env z
      rw [← e]; exact s1 z h1 h2
    | aload x y =>
      rw [calls_stmt_none rfl, List.append_nil]
      have e : aread F (F.env y) .elem = aread B (B.env y) .elem := by
        rw [h.1 y (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))]
        show uniMap (fun o => F.heap o _) _ = uniMap (fun o => B.heap o _) _
        rw [h.2.1]
      obtain ⟨s1, s2, s3, s4⟩ := setv _ _ x (aread F (F.env y) .elem) (nx x (by simp [Stmt.vars]))
        (nv x (by simp [Stmt.vars])) h.1 h.2.1
      refine ⟨fun z h1 h2 => ?_, s2, by have := h.2.2.1; rw [← s3] at this; exact this,
        by have := h.2.2.2; rw [← s4] at this; exact this⟩
      show (F.setVar x (aread F (F.env y) .elem)).env z = (B.setVar x (aread B (B.env y) .elem)).env z
      rw [← e]; exact s1 z h1 h2
    | astore x y =>
      rw [calls_stmt_none rfl, List.append_nil]
      have ex := h.1 x (nx x (by simp [Stmt.vars])) (nv x (by simp [Stmt.vars]))
      have ey := h.1 y (nx y (by simp [Stmt.vars])) (nv y (by simp [Stmt.vars]))
      refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
      show (F.weakStore (F.env x) .elem (F.env y)).heap = (B.weakStore (B.env x) .elem (B.env y)).heap
      rw [ex, ey]; unfold AState.weakStore; rw [h.2.1]
  | .seq p q, up, i, F, B, ⟨lp, lq⟩, ok, ⟨op, oq⟩, ⟨np, nq⟩, h => by
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    have h1 := bw_eq hc p up i F B lp hokp op np h
    have h2 := bw_eq hc q _ _ _ _ lq hokq oq nq h1
    show Corr cb ora (up ++ (Prog.seq p q).calls) _ _
    rw [calls_seq, ← List.append_assoc]; exact h2
  | .choice p q, up, i, F, B, ⟨lp, lq⟩, ok, ⟨op, oq⟩, ⟨np, nq⟩, h => by
    have hokp : ∀ st ∈ p.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_left _ hs)
    have hokq : ∀ st ∈ q.stmts, StmtOKB cb st := fun st hs => ok st (List.mem_append_right _ hs)
    have h1 := bw_eq hc p up i F B lp hokp op np h
    have h2 := bw_eq hc q up _ F B lq hokq oq nq h
    show Corr cb ora (up ++ (Prog.choice p q).calls) (join _ _) (join _ _)
    rw [calls_choice]
    have hE : SetEq (uni (upE cb ora (up ++ p.calls)) (upE cb ora (up ++ q.calls)))
        (upE cb ora (up ++ (p.calls ++ q.calls))) := by
      intro a
      rw [mem_uni, mem_upE, mem_upE, mem_upE]
      constructor
      · rintro (⟨c, hc1, hb⟩ | ⟨c, hc1, hb⟩)
        · refine ⟨c, ?_, hb⟩
          rcases List.mem_append.mp hc1 with h3 | h3
          · exact List.mem_append_left _ h3
          · exact List.mem_append_right _ (List.mem_append_left _ h3)
        · refine ⟨c, ?_, hb⟩
          rcases List.mem_append.mp hc1 with h3 | h3
          · exact List.mem_append_left _ h3
          · exact List.mem_append_right _ (List.mem_append_right _ h3)
      · rintro ⟨c, hc1, hb⟩
        rcases List.mem_append.mp hc1 with h3 | h3
        · exact Or.inl ⟨c, List.mem_append_left _ h3, hb⟩
        · rcases List.mem_append.mp h3 with h4 | h4
          · exact Or.inl ⟨c, List.mem_append_right _ h4, hb⟩
          · exact Or.inr ⟨c, List.mem_append_right _ h4, hb⟩
    have hV : SetEq (uni (upV cb ora (up ++ p.calls)) (upV cb ora (up ++ q.calls)))
        (upV cb ora (up ++ (p.calls ++ q.calls))) := by
      intro a
      rw [mem_uni, mem_upV, mem_upV, mem_upV]
      constructor
      · rintro (⟨c, hc1, hb⟩ | ⟨c, hc1, hb⟩)
        · refine ⟨c, ?_, hb⟩
          rcases List.mem_append.mp hc1 with h3 | h3
          · exact List.mem_append_left _ h3
          · exact List.mem_append_right _ (List.mem_append_left _ h3)
        · refine ⟨c, ?_, hb⟩
          rcases List.mem_append.mp hc1 with h3 | h3
          · exact List.mem_append_left _ h3
          · exact List.mem_append_right _ (List.mem_append_right _ h3)
      · rintro ⟨c, hc1, hb⟩
        rcases List.mem_append.mp hc1 with h3 | h3
        · exact Or.inl ⟨c, List.mem_append_left _ h3, hb⟩
        · rcases List.mem_append.mp h3 with h4 | h4
          · exact Or.inl ⟨c, List.mem_append_right _ h4, hb⟩
          · exact Or.inr ⟨c, List.mem_append_right _ h4, hb⟩
    refine ⟨fun x h3 h4 => ?_, ?_, (SetEq.uni h1.2.2.1 h2.2.2.1).trans hE,
      (SetEq.uni h1.2.2.2 h2.2.2.2).trans hV⟩
    · show uni _ _ = uni _ _
      rw [h1.1 x h3 h4, h2.1 x h3 h4]
    · show (fun o c => uni _ _) = (fun o c => uni _ _)
      rw [h1.2.1, h2.2.1]
  | .loop _, _, _, _, _, hl, _, _, _, _ => absurd hl id

/-! ## The oracle of the forward pre-states -/

/-- The call sites of a program, as a list of sites. -/
theorem callSites_eq (p : Prog) : p.callSites = p.calls.map Prod.fst := by
  unfold Prog.callSites Prog.calls
  induction p.stmts with
  | nil => rfl
  | cons st l ih =>
    cases st <;> simp [List.filterMap_cons, Stmt.callSite?, Stmt.callArgs?, ih]

/-- The oracle of the forward pre-states of a loop-free program: each call site gives the
forward state before its call (the first one in syntax order). -/
def oraOf (cb : CtxB) : Nat → Prog → AState → Oracle
  | _, .skip, X => fun _ => X
  | _, .stmt _, X => fun _ => X
  | i, .seq p q, X => fun t =>
    if t ∈ p.callSites then oraOf cb i p X t else oraOf cb (i + p.nulls) q (analyzeVS cb i p X) t
  | i, .choice p q, X => fun t =>
    if t ∈ p.callSites then oraOf cb i p X t else oraOf cb (i + p.nulls) q X t
  | _, .loop _, X => fun _ => X

/-- `OraEq` depends only on the oracle states of the call sites of the program. -/
theorem OraEq.congr {ora ora' : Oracle} :
    ∀ (q : Prog) (i : Nat) (X : AState), (∀ t ∈ q.callSites, ora t = ora' t) →
      OraEq cb ora i q X → OraEq cb ora' i q X
  | .skip, _, _, _, h => h
  | .stmt st, _, X, he, h => by
    cases st with
    | call ret a args =>
      show contrib cb (ora' a) args = contrib cb X args
      rw [← he a (by show a ∈ [Stmt.call ret a args].filterMap Stmt.callSite?; simp [Stmt.callSite?])]
      exact h
    | _ => exact h
  | .seq p q, i, X, he, ⟨h1, h2⟩ => by
    have hs : (Prog.seq p q).callSites = p.callSites ++ q.callSites := by
      show (p.stmts ++ q.stmts).filterMap Stmt.callSite? = _
      rw [List.filterMap_append]; rfl
    rw [hs] at he
    exact ⟨OraEq.congr p i X (fun t ht => he t (List.mem_append_left _ ht)) h1,
      OraEq.congr q _ _ (fun t ht => he t (List.mem_append_right _ ht)) h2⟩
  | .choice p q, i, X, he, ⟨h1, h2⟩ => by
    have hs : (Prog.choice p q).callSites = p.callSites ++ q.callSites := by
      show (p.stmts ++ q.stmts).filterMap Stmt.callSite? = _
      rw [List.filterMap_append]; rfl
    rw [hs] at he
    exact ⟨OraEq.congr p i X (fun t ht => he t (List.mem_append_left _ ht)) h1,
      OraEq.congr q _ _ (fun t ht => he t (List.mem_append_right _ ht)) h2⟩
  | .loop _, _, _, _, h => h

/-- THE ORACLE OF THE FORWARD PRE-STATES EXISTS: if the call sites of a loop-free program are
pairwise different, `oraOf` gives the forward pre-state of each call. -/
theorem oraEq_oraOf :
    ∀ (q : Prog) (i : Nat) (X : AState), LoopFree q → q.callSites.Nodup →
      OraEq cb (oraOf cb i q X) i q X
  | .skip, _, _, _, _ => trivial
  | .stmt st, _, X, _, _ => by
    cases st with
    | call ret a args => rfl
    | _ => trivial
  | .seq p q, i, X, ⟨lp, lq⟩, hnd => by
    have hs : (Prog.seq p q).callSites = p.callSites ++ q.callSites := by
      show (p.stmts ++ q.stmts).filterMap Stmt.callSite? = _
      rw [List.filterMap_append]; rfl
    rw [hs] at hnd
    obtain ⟨n1, n2, n3⟩ := List.nodup_append.mp hnd
    refine ⟨OraEq.congr p i X (fun t ht => ?_) (oraEq_oraOf p i X lp n1),
      OraEq.congr q _ _ (fun t ht => ?_) (oraEq_oraOf q _ _ lq n2)⟩
    · show oraOf cb i p X t = (if t ∈ p.callSites then _ else _)
      rw [ite_eq_left ht]
    · show _ = (if t ∈ p.callSites then oraOf cb i p X t else _)
      rw [ite_eq_right (fun h1 => n3 t h1 t ht rfl)]
  | .choice p q, i, X, ⟨lp, lq⟩, hnd => by
    have hs : (Prog.choice p q).callSites = p.callSites ++ q.callSites := by
      show (p.stmts ++ q.stmts).filterMap Stmt.callSite? = _
      rw [List.filterMap_append]; rfl
    rw [hs] at hnd
    obtain ⟨n1, n2, n3⟩ := List.nodup_append.mp hnd
    refine ⟨OraEq.congr p i X (fun t ht => ?_) (oraEq_oraOf p i X lp n1),
      OraEq.congr q _ _ (fun t ht => ?_) (oraEq_oraOf q _ _ lq n2)⟩
    · show oraOf cb i p X t = (if t ∈ p.callSites then _ else _)
      rw [ite_eq_left ht]
    · show _ = (if t ∈ p.callSites then oraOf cb i p X t else _)
      rw [ite_eq_right (fun h1 => n3 t h1 t ht rfl)]
  | .loop _, _, _, hl, _ => absurd hl id

/-- The call sites are among the sites. -/
theorem callSites_sub (p : Prog) : ∀ s ∈ p.callSites, s ∈ p.sites := by
  intro s hs
  obtain ⟨st, hst, e⟩ := List.mem_filterMap.mp hs
  refine List.mem_filterMap.mpr ⟨st, hst, ?_⟩
  cases st <;> (try cases e) <;> rfl

/-- The call sites of a program with pairwise different sites are pairwise different. -/
theorem callSites_nodup : ∀ (p : Prog), p.sites.Nodup → p.callSites.Nodup := by
  intro p h
  unfold Prog.sites at h
  unfold Prog.callSites
  generalize p.stmts = l at h
  induction l with
  | nil => exact List.nodup_nil
  | cons st l ih =>
    cases st with
    | call ret a args =>
      simp only [List.filterMap_cons, Stmt.site?, Stmt.callSite?] at h ⊢
      rw [List.nodup_cons] at h ⊢
      refine ⟨fun hm => h.1 ?_, ih h.2⟩
      obtain ⟨st', hst', e⟩ := List.mem_filterMap.mp hm
      refine List.mem_filterMap.mpr ⟨st', hst', ?_⟩
      cases st' <;> (try cases e) <;> rfl
    | new x a =>
      simp only [List.filterMap_cons, Stmt.site?, Stmt.callSite?] at h ⊢
      exact ih (List.nodup_cons.mp h).2
    | unknown x a =>
      simp only [List.filterMap_cons, Stmt.site?, Stmt.callSite?] at h ⊢
      exact ih (List.nodup_cons.mp h).2
    | _ =>
      simp only [List.filterMap_cons, Stmt.site?, Stmt.callSite?] at h ⊢
      exact ih h

/-! ## Whole programs -/

/-- BACKWARD SEARCH = FORWARD TEST ON LOOP-FREE PROGRAMS: for a loop-free program with pairwise
different sites, the backward analysis with the oracle of the forward pre-states gives the same
may-alias answer as design VS, for each query on non-reserved variables (in particular on the
program and frame variables). So the reserved keys `Etree` and `Eval` can be dropped there. -/
theorem mayProgBW_eq (eu : Bool) (K : Nat) (statics : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) (hl : LoopFree p) (hnd : p.sites.Nodup)
    (hx : x ∈ p.vars ++ fr.vars) (hy : y ∈ p.vars ++ fr.vars) :
    mayProgBW eu K statics fr p
      (oraOf (ctxVS eu K statics fr p (afields px ++ afields py)) 0 p (ainitV K fr)) x px y py =
    mayProgVS eu K statics fr p x px y py := by
  let qf := afields px ++ afields py
  let cb := ctxVS eu K statics fr p qf
  have hc : CtxBOK cb := ctxVS_ok eu K statics fr p qf
  have hok := ctxVS_stmts eu K statics fr p qf
  have hn : NullsIn cb 0 p.nulls := fun j _ hj => ctxVS_nulls eu K statics fr p qf (by omega)
  have hs := supp_ainitVS eu K statics fr p qf
  obtain ⟨h1, h2⟩ := ctxVS_res_frame eu K statics fr p qf
  have n1 : fr.root? cb.cn.xe = none := lookup_none_of_not_mem fr.binds _ h1
  have n2 : fr.root? cb.xv = none := lookup_none_of_not_mem fr.binds _ h2
  have e1 : (ainitV K fr).env cb.cn.xe = [] := by
    show (match fr.root? _ with | some r => [Origin.sym (.root r) []] | none => []) = []
    rw [n1]
  have e2 : (ainitV K fr).env cb.xv = [] := by
    show (match fr.root? _ with | some r => [Origin.sym (.root r) []] | none => []) = []
    rw [n2]
  have h0 : Corr cb (oraOf cb 0 p (ainitV K fr)) [] (ainitV K fr) (ainitV K fr) :=
    ⟨fun _ _ _ => rfl, rfl, by rw [e1]; exact SetEq.refl _, by rw [e2]; exact SetEq.refl _⟩
  have hnh : NoHit cb 0 p (ainitV K fr) :=
    noHit_of_fresh hc p 0 _ hl hnd hok hn hs (fun s _ => fresh_ainitV K fr s)
  have heq := bw_eq hc p [] 0 _ _ hl hok (oraEq_oraOf p 0 _ hl (callSites_nodup p hnd)) hnh h0
  have hv : ∀ z, z ∈ p.vars ++ fr.vars → z ≠ cb.cn.xe ∧ z ≠ cb.xv := by
    intro z hz
    have hpv : z ∈ progVars fr p := List.mem_eraseDups.mpr hz
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := lt_freshVar hpv
      have e' : z = freshVar (progVars fr p) := e
      rw [e'] at this; exact Nat.lt_irrefl _ this
    · have := lt_freshVar hpv
      have e' : z = freshVar (progVars fr p) + 1 := e
      rw [e'] at this; exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) this)
  unfold mayProgBW mayProgVS analyzeProgVS may aevalPath
  rw [← heq.1 x (hv x hx).1 (hv x hx).2, ← heq.1 y (hv y hy).1 (hv y hy).2,
    aevalFrom_heap heq.2.1.symm, aevalFrom_heap heq.2.1.symm]

/-! ## Repeated allocation sites -/

namespace BWExamples

/-- Variable `h` (root 0). -/
abbrev vh : Var := 0
/-- Variable `y` (root 1). -/
abbrev vy : Var := 1
/-- Variable `x`. -/
abbrev vx : Var := 2
/-- Variable `t`. -/
abbrev vt : Var := 3
/-- Field `f`. -/
abbrev ff : Field := 0
/-- Field `g`. -/
abbrev fg : Field := 1

/-- The frame: `h` and `y` hold roots 0 and 1. -/
def frR : Frame := ⟨[(vh, 0), (vy, 1)]⟩

/-- `x = new@1; h.f = x; m(h)@9; x = new@1; t = x.g; x.g = y`: the allocation site 1 occurs two
times. -/
def pRep : Prog :=
  .seq (.stmt (.new vx 1)) <| .seq (.stmt (.store vh ff vx)) <| .seq (.stmt (.call none 9 [vh])) <|
  .seq (.stmt (.new vx 1)) <| .seq (.stmt (.load vt vx fg)) (.stmt (.store vx fg vy))

/-- WHY THE SITES MUST BE DIFFERENT: with a repeated allocation site, the forward test renames
`new(1)` in `Eval` at the second `new`, so the store `x.g = y` is strong and `t ~ x.g` is false
(exact, by `csoundVS`); the backward test does not rename, the store is weak, and it answers
true (sound, not exact). -/
theorem bw_needs_distinct_sites :
    mayProgVS true 1 [] frR pRep vt [] vx [.fld fg] = false ∧
      mayProgBW true 1 [] frR pRep
        (oraOf (ctxVS true 1 [] frR pRep ([] ++ [fg])) 0 pRep (ainitV 1 frR)) vt [] vx [.fld fg] =
        true := by decide +kernel

end BWExamples

end DirectedAlias.Sound.ValueSem
