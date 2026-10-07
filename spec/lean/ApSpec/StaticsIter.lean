/-
  ApSpec.StaticsIter — statics on the NON-FIRST iterations: no request and no static rule.

  The claim: run 1 handles statics with the position request (`Statics.DS` with `Statics.Design`,
  under `Statics.SWF`); every later forward run is the unchanged restricted closure `DR` (no
  request of any kind, no static rule), and every backward run is the unchanged `Backward.DB`.

  Part 1. THE STATIC INVARIANT OF A RESTRICTED RUN (`rinv_all`, `no_any_above_R`). Under the
    construction rules of `Statics.SWF` that concern the program (`SWFR`: identity restrictions or
    field-to-field edges on `S`, writes into `S` at or below a position or exact above one,
    `S.* → S.*` bindings, a field limit that never cuts above a position), in `DR` with the spec
    rules (`emitM`, `satI`, `restrictU`) no static fact with a `*` or `[any]` tail lies strictly
    above a static position (initial facts, edges, added facts). Positions are truncated to the
    static field (`Statics.PosIn`), so "above a position" means the root or a class. NO HYPOTHESIS
    ON THE DEMAND is needed: `emitM` emits the added fact, its meet at its own path, or the demand
    pattern BELOW it; `restrictU` moves a conclusion only DOWN; and a fact strictly above a position
    is exact, so its tail admits no longer path. Persisted records must keep the run-1 invariant
    (`RecOK`), which the exit edges of `DS` (`recOK_of_DS`, from `Statics.cinv_all`) and of `DR`
    (`recOK_of_DR`) do.
    Consequences: every static read, write keep edge or copy whose premise is at most a static
    field and that gives a fact in a restricted run is the case at-or-below of delta-concat
    (`static_step_below`: the case `above`, the one that makes `[any]` from a `*` target, gives
    nothing), every static sink at most a static field that a fact triggers or requests is at or
    above it (`static_sink_below`), and a restricted run has no request (`no_request`). Below a
    static field the ordinary rules apply, as for an instance field.
  Part 2. THE ITERATION FROM `DS`. Run 1 (`DS`, projected to `Obj` by `projS`) carries every real
    witness in the den-aware sense (`reach_strongDSD`: `Statics.coverageD`/`reachD` with the pair
    relation of the summaries kept), so `Backward.B_general` applies to it; with every later
    forward run the plain `DR` and every backward run the plain `DB`, every forward run reports
    every real vulnerability (`iteration_sound_DS`, `iteration_general_DS`), and every run after
    run 1 satisfies the static invariant and has no request (`no_static_rule_after_run1`).
  Part 3. END-TO-END EVIDENCE on the four programs of `Statics.lean` (`ExampleIter`, `WideIter`,
    `AboveIter`, `CleanIter`): run 1 = `DS` (final design) reports the vulnerability; backward run
    2 = `DB` restricted by the reversed summaries of run 1 and seeded at the reported sink; the
    hand-off `demOf`; forward run 3 = the plain `DR`. Run 3 reports the vulnerability through a
    NORMAL-layer sink edge (`run3_vuln_normal`), it is CONFIRMED (`run3_confirmed`,
    `RExact.ConfirmedM`), and it has no request. The hand-off of `Example` is computed exactly
    (`demE_exact`: the exact static field `(S, <C1>.f, $, 7)` and the zero demand); on `CexWide`
    every hypothesis of the general theorems is discharged (`wide_iteration`,
    `wide_no_static_rule`).

  Only `propext` and `Quot.sound` are used.
-/
import ApSpec.Statics
import ApSpec.Backward

namespace ApSpec.StaticsIter
open ApSpec ApSpec.Statics

/-! ## Part 1. The static invariant of a restricted run -/

/-- THE CONSTRUCTION RULES that a restricted run needs: the parts of `Statics.SWF` about the
    program (the context `X` gives the program, its sinks, the static base and the run's field
    limit and counted accessors). Not needed: `S ≠ zero`, the cleaner rule, the run-1 abstraction. -/
structure SWFR (X : SCtx) : Prop where
  /-- a statement micro edge from `S` to `S` is an identity restriction or a field-to-field edge
      (premise and target paths not above a position; `Statics.SWF.ss`) -/
  ss : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ X.P.edges → ∀ e, e ∈ s.edges →
    e.1.base = X.sB → e.2.base = X.sB →
    (∃ q E1 E2, e.1 = ⟨X.sB, q, .star E1, .star⟩ ∧ e.2 = ⟨X.sB, q, .star E2, .star⟩) ∨
    (¬ AbovePos X e.1.path ∧ ¬ AbovePos X e.2.path)
  /-- a write into `S` from another base above a position is exact from an exact concrete premise -/
  write : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ X.P.edges → ∀ e, e ∈ s.edges →
    e.1.base ≠ X.sB → e.2.base = X.sB → AbovePos X e.2.path →
    e.2.kind = .exact ∧ e.1.kind = .exact ∧ ∃ t, e.1.mark = .conc t
  /-- a call binds `S` only by `S.* → S.*` -/
  toC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.toCallee →
    (e.1.base = X.sB ∨ e.2.base = X.sB) →
    ∃ E1 E2, e.1 = ⟨X.sB, [], .star E1, .star⟩ ∧ e.2 = ⟨X.sB, [], .star E2, .star⟩
  fromC : ∀ M n c n', (M, n, Instr.call c, n') ∈ X.P.edges → ∀ e, e ∈ c.fromCallee →
    (e.1.base = X.sB ∨ e.2.base = X.sB) →
    ∃ E1 E2, e.1 = ⟨X.sB, [], .star E1, .star⟩ ∧ e.2 = ⟨X.sB, [], .star E2, .star⟩
  /-- the field limit of THIS run never cuts a path to a path above a position -/
  cut : ∀ q r, cutPath X.counted X.FL q = some r → ¬ AbovePos X r

theorem swfr_of_swf {X : SCtx} (hs : SWF X) : SWFR X :=
  ⟨hs.ss, hs.write, hs.toC, hs.fromC, hs.cut⟩

/-- The same program with another field limit (a later run): only `cut` is new. -/
theorem swfr_limit {X : SCtx} (hs : SWF X) {L : Nat}
    (hcut : ∀ q r, cutPath X.counted L q = some r → ¬ AbovePos X r) :
    SWFR { X with FL := L } :=
  ⟨hs.ss, hs.write, hs.toC, hs.fromC, hcut⟩

/-- THE STATIC INVARIANT OF A RESTRICTED RUN: no static initial fact, edge fact or added fact with a
    `*` or `[any]` tail lies strictly above a position (`AboveNE`); W2 on edges. -/
def RInv (X : SCtx) : Obj → Prop
  | .init _ i => ¬ AboveNE X i
  | .edge _ _ _ f => W2A f ∧ ¬ AboveNE X f.fact
  | .added _ a => ¬ AboveNE X a
  | _ => True

/-- A persisted record keeps the static invariant of run 1 (`Statics.CInv` on edges): a static
    conclusion with a `*` or `[any]` tail above a position is an identity static `*` record. -/
def RecOK (X : SCtx) (j : PFact) (g : AFact) : Prop :=
  W2A g ∧ (AboveNE X g.fact →
    (∃ E0, j = ⟨X.sB, g.fact.path, .star E0, .star⟩) ∧ ∃ E, g.fact.kind = .star E)

theorem recOK_of {X : SCtx} {j : PFact} {g : AFact} (hw : W2A g) (h : ¬ AboveNE X g.fact) :
    RecOK X j g :=
  ⟨hw, fun hab => absurd hab h⟩

/-! ### Local lemmas -/

theorem startFact_kind_exact {i : PFact} (h : (startFact i).fact.kind = .exact) :
    i.kind = .exact := by
  obtain ⟨b, p, k, m⟩ := i
  cases k <;> cases m <;> first | rfl | cases h

theorem aboveNE_start {X : SCtx} {i : PFact} (h : AboveNE X (startFact i).fact) : AboveNE X i :=
  ⟨by rw [← Example.startFact_base i]; exact h.1,
   by rw [← Example.startFact_path i]; exact h.2.1,
   fun hk => h.2.2 (by
     obtain ⟨b, p, k, m⟩ := i
     simp only at hk
     subst hk
     cases m <;> rfl)⟩

theorem limitF_keepR {X : SCtx} (hs : SWFR X) {y : AFact}
    (h : AbovePos X (limitF X.counted X.FL y).fact.path) : limitF X.counted X.FL y = y := by
  unfold limitF at h ⊢
  cases hc : cutPath X.counted X.FL y.fact.path with
  | none => rfl
  | some r =>
    rw [hc] at h
    exact absurd h (hs.cut _ _ hc)

/-- The result of delta-concat is on the target base. -/
theorem apply_base {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    r.fact.base = to.base := by
  obtain ⟨_, _, _, _, _, _, _, hrr, _⟩ := apply_shape h
  rw [hrr, norm_base]

/-- A non-exact normal form comes from a non-exact fact. -/
theorem norm_ne_exact {x : AFact} (h : x.norm.fact.kind ≠ .exact) : x.fact.kind ≠ .exact :=
  fun hk => h (norm_exact hk)

theorem aboveNE_norm {X : SCtx} {x : AFact} (h : AboveNE X x.norm.fact) : AboveNE X x.fact :=
  ⟨by rw [← norm_base]; exact h.1, by rw [← norm_path]; exact h.2.1, norm_ne_exact h.2.2⟩

theorem admits_ne_exact {k : Kind} {r : List Acc} (hne : r ≠ []) (h : admitsTailB k r = true) :
    k ≠ .exact := by
  intro hk
  rw [hk, admits_exact_nil hne] at h
  cases h

/-- A write from another base into `S` gives no non-exact fact above a position (`write_inv` with
    the minimal construction rules). -/
theorem write_invR {X : SCtx} (hs : SWFR X) {M : MethodId} {n n' : Node} {s : Stmt}
    {e : MicroEdge} {f y : AFact} (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges) (he : e ∈ s.edges)
    (h1 : e.1.base ≠ X.sB) (h2 : e.2.base = X.sB) (hw : W2A f)
    (hy : y ∈ (applyEdge f e.1 e.2).facts) : ¬ AboveNE X y.fact := by
  intro hab
  obtain ⟨p, k, ap, m, -, hgate, -, hrr, hgeo⟩ := apply_shape hy
  have hyp : y.fact.path = p := by rw [hrr, norm_path]
  have hyk : k = .exact → y.fact.kind = .exact := fun hk => by rw [hrr]; exact norm_exact hk
  have hapos : AbovePos X p := by rw [← hyp]; exact hab.2.1
  have hwr := hs.write _ _ _ _ hE e he h1 h2
  rcases hgeo with ⟨rr, -, hb⟩ | ⟨rr, -, -, ha⟩
  · cases htk : e.2.kind with
    | star et =>
      rw [htk] at hb
      obtain ⟨hp, -, -⟩ := below_star_tk hb
      rw [hp] at hapos
      have := (hwr (abovePos_prefix hapos)).1
      rw [htk] at this; cases this
    | any =>
      rw [htk] at hb
      obtain ⟨hp, -⟩ := below_any_tk hb
      rw [hp] at hapos
      have := (hwr hapos).1
      rw [htk] at this; cases this
    | exact =>
      rw [htk] at hb
      obtain ⟨hp, hk | ⟨⟨ec, hck⟩, -, -⟩⟩ := below_exact_tk hb
      · exact hab.2.2 (hyk hk)
      · rw [hp] at hapos
        obtain ⟨-, -, t, hmt⟩ := hwr hapos
        rw [hmt] at hgate
        have := (hw ec hck).1
        rw [gate_conc_abs hgate] at this
        cases this
  · obtain ⟨hp, -, -, hex⟩ := above_tk ha
    rw [hp] at hapos
    exact hab.2.2 (hyk (hex (hwr hapos).1))

/-- THE STEP keeps the invariant. -/
theorem rinv_step {X : SCtx} (hs : SWFR X) {M : MethodId} {n n' : Node} {s : Stmt} {f f' : AFact}
    (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges) (hw : W2A f) (hn : ¬ AboveNE X f.fact)
    (hf : f' ∈ (transfer X.counted X.FL s f).facts) : W2A f' ∧ ¬ AboveNE X f'.fact := by
  rcases Invariant.transfer_mem hf with rfl | ⟨x, e, he, hx, rfl⟩
  · exact ⟨hw, hn⟩
  · refine ⟨limitF_w2 (applyEdge_w2 hx), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL x).fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    have hxb : x.fact.base = e.2.base := apply_base hx
    by_cases h2 : e.2.base = X.sB
    · by_cases h1 : e.1.base = X.sB
      · rcases hs.ss _ _ _ _ hE e he h1 h2 with ⟨q, E1, E2, he1, he2⟩ | ⟨-, hn2⟩
        rotate_left
        · exact f2f_not_above hn2 hx hab.2.1
        rw [he1, he2] at hx
        obtain ⟨-, hfb, ⟨rr, -, hxp, hex, -⟩ | ⟨rr, hq, hne, hxq, hadm⟩⟩ := id_apply hx
        · exact hn ⟨hfb, by rw [← hxp]; exact hab.2.1, fun hk => hab.2.2 (hex hk)⟩
        · have hqa : AbovePos X q := by rw [← hxq]; exact hab.2.1
          rw [hq] at hqa
          exact hn ⟨hfb, abovePos_prefix hqa, admits_ne_exact hne hadm⟩
      · exact write_invR hs hE he h1 h2 hw hx hab
    · exact h2 (hxb.symm.trans hab.1)

/-- A binding `S.* → S.*` (or a binding of another base) keeps the invariant. -/
theorem rinv_bind {X : SCtx} {e : MicroEdge} {f y : AFact}
    (hbind : (e.1.base = X.sB ∨ e.2.base = X.sB) →
      ∃ E1 E2, e.1 = ⟨X.sB, [], .star E1, .star⟩ ∧ e.2 = ⟨X.sB, [], .star E2, .star⟩)
    (hn : ¬ AboveNE X f.fact) (hy : y ∈ (applyEdge f e.1 e.2).facts) : ¬ AboveNE X y.fact := by
  intro hab
  obtain ⟨E1, E2, he1, he2⟩ := hbind (.inr ((apply_base hy).symm.trans hab.1))
  rw [he1, he2] at hy
  obtain ⟨-, hfb, hyp, hex, -⟩ := bind_apply hy
  exact hn ⟨hfb, by rw [← hyp]; exact hab.2.1, fun hk => hab.2.2 (hex hk)⟩

/-- `meetK` keeps an exact tail. -/
theorem meetK_exact (k : Kind) : meetK .exact k = .exact := by
  cases k <;> rfl

/-- THE EMISSION keeps the invariant, FOR EVERY DEMAND ENTRY PATTERN: `emitM` gives the added fact,
    its meet at its own path, or the demand pattern BELOW it (when the added fact's tail admits
    the rest, so it is not exact); a path below one that is not above a position is not above one. -/
theorem rinv_emit {X : SCtx} {d a j : PFact} (ha : ¬ AboveNE X a) (h : emitM d a = some j) :
    ¬ AboveNE X j := by
  unfold emitM at h
  split at h
  next hc =>
    have hb : d.base = a.base := by
      simp only [Bool.and_eq_true] at hc
      exact CoreAux.beq_iff.mp hc.1
    split at h
    next hrel =>
      cases h
      intro hab
      refine ha ⟨hab.1, hab.2.1, fun hk => hab.2.2 ?_⟩
      show meetK a.kind d.kind = .exact
      rw [hk, meetK_exact]
    next r hrel =>
      split at h
      · cases h; exact ha
      · cases h
    next r hrel =>
      split at h
      next hadm =>
        cases h
        intro hab
        obtain ⟨hdp, hne⟩ := CoreAux.relate_above_inv hrel
        have hap : AbovePos X a.path := by
          have h0 : AbovePos X d.path := hab.2.1
          rw [hdp] at h0
          exact abovePos_prefix h0
        exact ha ⟨hb ▸ hab.1, hap, admits_ne_exact hne hadm⟩
      next => cases h
    next => cases h
  next => cases h

/-- THE RESTRICTION keeps the invariant: `restrictU` keeps the conclusion or moves it DOWN to the
    demand exit pattern (only for an `[any]` conclusion). -/
theorem rinv_restrict {X : SCtx} {j : PFact} {g g' : AFact} {d : DemandEdge} (hw : W2A g)
    (hn : ¬ AboveNE X g.fact) (h : restrictU j g d = some g') : W2A g' ∧ ¬ AboveNE X g'.fact := by
  obtain ⟨din, dout⟩ := d
  cases dout with
  | none => cases h
  | some p =>
    have h' : (if overlapB j din = true then restrictConcU g p else none) = some g' := h
    split at h'
    · unfold restrictConcU at h'
      split at h'
      next hb =>
        split at h'
        next r hrel =>
          split at h'
          · cases h'; exact ⟨hw, hn⟩
          · cases h'
        next r hrel =>
          cases hk : g.fact.kind with
          | any =>
            rw [hk] at h'
            cases h'
            refine ⟨fun E hE => ?_, fun hab => ?_⟩
            · revert hE
              cases p.kind <;> intro hE <;> cases hE
            · obtain ⟨hpp, -⟩ := CoreAux.relate_above_inv hrel
              have hap : AbovePos X g.fact.path := by
                have h0 : AbovePos X p.path := hab.2.1
                rw [hpp] at h0
                exact abovePos_prefix h0
              exact hn ⟨hab.1, hap, by rw [hk]; intro h; cases h⟩
          | star e => rw [hk] at h'; cases h'
          | exact => rw [hk] at h'; cases h'
        next => cases h'
      next => cases h'
    · cases h'

/-- THE SUMMARY APPLICATION keeps the invariant: a callee summary (a run edge or a persisted
    record with `RecOK`) applied to a concrete added fact that satisfies the invariant. -/
theorem rinv_summary {X : SCtx} {a g r : AFact} {j : PFact} (hg : RecOK X j g)
    (ha : ¬ AboveNE X a.fact) (haw : W2A a) {t : Mark} (hat : a.fact.mark = .conc t)
    (hr : r ∈ (applySummary a j g).facts) : ¬ AboveNE X r.fact := by
  intro hab
  obtain ⟨x, hx, hrx⟩ := List.mem_map.mp hr
  rw [← hrx] at hab
  have habx := aboveNE_norm hab
  obtain ⟨p, k, ap, m, hajb, -, -, hxx, hgeo⟩ := apply_shape hx
  have hxp : x.fact.path = p := by rw [hxx, norm_path]
  have hkx : k = .exact → x.fact.kind = .exact := fun hk => by rw [hxx]; exact norm_exact hk
  have hxb : x.fact.base = g.fact.base := by rw [hxx, norm_base]
  have hgb : g.fact.base = X.sB := hxb ▸ habx.1
  have hAP : AbovePos X p := hxp ▸ habx.2.1
  have hxne := habx.2.2
  -- `a` is not a `*` fact (it is concrete and W2)
  have hans : ∀ ec, a.fact.kind ≠ .star ec := fun ec hk => by
    have := (haw ec hk).1
    rw [hat] at this
    cases this
  cases hgk : g.fact.kind with
  | star Eg =>
    rcases hgeo with ⟨rr, hrr, hb⟩ | ⟨rr, hjp', hne, ha'⟩
    · rw [hgk] at hb
      obtain ⟨hp, hex, -⟩ := below_star_tk hb
      have hgp : AbovePos X g.fact.path := by rw [hp] at hAP; exact abovePos_prefix hAP
      have hgab : AboveNE X g.fact := ⟨hgb, hgp, by rw [hgk]; intro h; cases h⟩
      obtain ⟨⟨E0, hj⟩, -⟩ := hg.2 hgab
      have hjp : j.path = g.fact.path := by rw [hj]
      have hab' : a.fact.base = X.sB := by rw [hajb, hj]
      have hap' : a.fact.path = p := by rw [hrr, hjp, hp]
      exact ha ⟨hab', by rw [hap']; exact hAP, fun hk => hxne (hkx (hex hk))⟩
    · rw [hgk] at ha'
      obtain ⟨hp, hadm, -, -⟩ := above_tk ha'
      have hgp : AbovePos X g.fact.path := by rw [hp] at hAP; exact hAP
      have hgab : AboveNE X g.fact := ⟨hgb, hgp, by rw [hgk]; intro h; cases h⟩
      obtain ⟨⟨E0, hj⟩, -⟩ := hg.2 hgab
      have hjp : j.path = g.fact.path := by rw [hj]
      have hab' : a.fact.base = X.sB := by rw [hajb, hj]
      have h0 : AbovePos X j.path := by rw [hjp]; exact hgp
      rw [hjp'] at h0
      exact ha ⟨hab', abovePos_prefix h0, admits_ne_exact hne hadm⟩
  | any =>
    have hp : p = g.fact.path := by
      rcases hgeo with ⟨rr, -, hb⟩ | ⟨rr, -, -, ha'⟩
      · rw [hgk] at hb; exact (below_any_tk hb).1
      · exact (above_tk ha').1
    obtain ⟨-, E, hE⟩ := hg.2 ⟨hgb, by rw [← hp]; exact hAP, by rw [hgk]; intro h; cases h⟩
    rw [hgk] at hE
    cases hE
  | exact =>
    rcases hgeo with ⟨rr, -, hb⟩ | ⟨rr, -, -, ha'⟩
    · rw [hgk] at hb
      obtain ⟨-, hk | ⟨⟨ec, hak⟩, -, -⟩⟩ := below_exact_tk hb
      · exact hxne (hkx hk)
      · exact hans ec hak
    · rw [hgk] at ha'
      exact hxne (hkx ((above_tk ha').2.2.2 rfl))

/-! ### The invariant -/

/-- THE STATIC INVARIANT OF A RESTRICTED RUN (the analogue of `Statics.no_any_above`). In `DR` with
    the spec rules, for EVERY demand and every record set that keeps the run-1 invariant (`RecOK`),
    no static fact with a `*` or `[any]` tail lies strictly above a static position. -/
theorem rinv_all {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {o : Obj}
    (h : DR X.P X.counted X.FL demand emitM satI restrictU recs sinks roots o) : RInv X o := by
  induction h with
  | root _ => exact fun hab => hab.2.2 rfl
  | start _ ih => exact ⟨startFact_w2 _, fun hab => ih (aboveNE_start hab)⟩
  | step _ hE hf ih => exact rinv_step hs hE ih.1 ih.2 hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | @added M i n f n' c e a _ hE he ha ih => exact rinv_bind (hs.toC _ _ _ _ hE e he) ih.2 ha
  | initR _ _ hemit ih => exact rinv_emit ih hemit
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf hE he1 ha _ _ _ hres _ hr he2 hr' ihf _ ihg =>
    obtain ⟨-, t, ht⟩ := RExact.DR_concrete RCov.emitM_copies hf
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
    have han := rinv_bind (hs.toC _ _ _ _ hE e1 he1) ihf.2 ha
    obtain ⟨hgw', hgn'⟩ := rinv_restrict ihg.1 ihg.2 hres
    have hrn := rinv_summary (recOK_of hgw' hgn') han (applyEdge_w2 ha) hta hr
    have hr'n := rinv_bind (hs.fromC _ _ _ _ hE e2 he2) hrn hr'
    refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hr'n hab
  | @retRec M i n f n' c e1 a j g r e2 r' hf hE he1 ha hrec _ hr he2 hr' ihf =>
    obtain ⟨-, t, ht⟩ := RExact.DR_concrete RCov.emitM_copies hf
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
    have han := rinv_bind (hs.toC _ _ _ _ hE e1 he1) ihf.2 ha
    have hrn := rinv_summary (hrecs _ _ _ hrec) han (applyEdge_w2 ha) hta hr
    have hr'n := rinv_bind (hs.fromC _ _ _ _ hE e2 he2) hrn hr'
    refine ⟨limitF_w2 (applyEdge_w2 hr'), fun hab => ?_⟩
    have hab0 : AbovePos X (limitF X.counted X.FL r').fact.path := hab.2.1
    rw [limitF_keepR hs hab0] at hab
    exact hr'n hab
  | reqSink => trivial
  | answer hreq _ _ _ _ _ => exact (RExact.DR_no_requestM _ _ _ hreq).elim
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    refine ⟨cleanRes_w2 ih.1 hf, fun hab => ?_⟩
    rcases cleanRes_cases hf with rfl | ⟨-, t, ha, -, rfl⟩ | ⟨t, hct, rfl⟩ | ⟨-, -, rfl⟩
    · exact ih.2 hab
    · exact ih.2 ⟨hab.1, hab.2.1, hab.2.2⟩
    · rcases Exact.concPart_cases cl f with ⟨-, -, -, hcp⟩ | hcp
      · rw [hcp] at hab
        exact hab.2.2 rfl
      · rw [hcp] at hab
        exact ih.2 hab
    · exact ih.2 (aboveNE_norm (x := ⟨f.fact, true⟩) hab)
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

#print axioms rinv_all

/-- The edge form: no static edge fact with a `*` or `[any]` tail strictly above a position; in
    particular no `(S, <C>, [any], …)` and no `(S, [], [any], …)` when `[]` is above a position. -/
theorem no_any_above_R {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR X.P X.counted X.FL demand emitM satI restrictU recs sinks roots (.edge M i n f))
    (hb : f.fact.base = X.sB) (hp : AbovePos X f.fact.path) : f.fact.kind = .exact := by
  cases hk : f.fact.kind with
  | exact => rfl
  | any => exact absurd ⟨hb, hp, by rw [hk]; intro h; cases h⟩ (rinv_all hs hrecs h).2
  | star e => exact absurd ⟨hb, hp, by rw [hk]; intro h; cases h⟩ (rinv_all hs hrecs h).2

#print axioms no_any_above_R

/-! ### Consequences: only the case at-or-below, no request -/

/-- EVERY STATIC READ, WRITE KEEP EDGE OR COPY WHOSE PREMISE IS AT MOST A STATIC FIELD AND THAT GIVES
    A FACT IN A RESTRICTED RUN IS THE CASE AT OR BELOW: the micro edge premise is at or above the
    fact. The case `above` of delta-concat (the one that makes `[any]` from a `*` target) never gives
    a fact. A deeper premise may meet a field fact in the case `above`, as for an instance field
    (`DeepReadIter.deep_read_above`). -/
theorem static_step_below {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {s : Stmt} {e : MicroEdge} {y : AFact}
    (h : DR X.P X.counted X.FL demand emitM satI restrictU recs sinks roots (.edge M i n f))
    (hE : (M, n, Instr.stmt s, n') ∈ X.P.edges) (he : e ∈ s.edges) (heb : e.1.base = X.sB)
    (hlen : e.1.path.length ≤ 2)
    (hy : y ∈ (applyEdge f e.1 e.2).facts) : ∃ rr, f.fact.path = e.1.path ++ rr := by
  obtain ⟨p, k, ap, m, hfb, -, -, -, hgeo⟩ := apply_shape hy
  rcases hgeo with ⟨rr, hrr, -⟩ | ⟨rr, hq, hne, ha⟩
  · exact ⟨rr, hrr⟩
  · exfalso
    obtain ⟨-, hadm, -, -⟩ := above_tk ha
    have hpos : PosIn X e.1.path := .inl ⟨M, n, s, n', e, hE, he, heb, List.take_of_length_le hlen⟩
    exact (rinv_all hs hrecs h).2 ⟨hfb.trans heb, ⟨_, rr, hpos, hne, hq⟩, admits_ne_exact hne hadm⟩

#print axioms static_step_below

/-- EVERY STATIC SINK AT MOST A STATIC FIELD THAT A FACT OF A RESTRICTED RUN TRIGGERS OR REQUESTS IS
    AT OR ABOVE THE FACT (the sink pattern's path is a prefix of the fact's path). A deeper sink may
    lie below a field fact (`DeepReadIter.deep_read_above`). -/
theorem static_sink_below {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact} {s : PFact}
    {T : Mark}
    (h : DR X.P X.counted X.FL demand emitM satI restrictU recs X.sinks roots (.edge M i n f))
    (hsk : (M, n, s) ∈ X.sinks) (hsb : s.base = X.sB) (hlen : s.path.length ≤ 2) (hT : s.mark = .conc T)
    (hc : check i f s ≠ .none) : ∃ rr, f.fact.path = s.path ++ rr := by
  have hov := check_overlap_of hT hc
  unfold overlapB at hov
  simp only [Bool.and_eq_true] at hov
  obtain ⟨hbeq, hrel⟩ := hov
  have hfb : f.fact.base = X.sB := (CoreAux.beq_iff.mp hbeq).trans hsb
  cases hrl : relate f.fact.path s.path with
  | below r =>
    rw [hrl] at hrel
    have hsp := CoreAux.relate_below_inv hrl
    cases r with
    | nil => exact ⟨[], by rw [hsp, List.append_nil, List.append_nil]⟩
    | cons x rs =>
      exfalso
      have hpos : PosIn X s.path := .inr ⟨M, n, s, hsk, hsb, List.take_of_length_le hlen⟩
      exact (rinv_all hs hrecs h).2 ⟨hfb, ⟨s.path, x :: rs, hpos, List.cons_ne_nil _ _, hsp⟩,
        admits_ne_exact (List.cons_ne_nil _ _) hrel⟩
  | above r =>
    obtain ⟨hfp, -⟩ := CoreAux.relate_above_inv hrl
    exact ⟨r, hfp⟩
  | apart =>
    rw [hrl] at hrel
    cases hrel

#print axioms static_sink_below

/-! Below a static field the ordinary rules apply, so the two consequences above need the premise
    (sink) path to be at most a static field. The one-method program `x.[any] = source(); C.f = x;
    y = C.f.g; sink(C.f.g)` satisfies `SWFR`; its restricted run has the edge `(S, <C>.f, [any], 7)`,
    which the deep read `S.<C>.f.g.* → y.*` reads in the case `above` and which triggers the deep sink
    `(S, <C>.f.g, $, 7)`, both strictly below it. -/
namespace DeepReadIter

def S : Base := 1
def xB : Base := 2
def yB : Base := 3
def C : Acc := 10
def fA : Acc := 11
def gA : Acc := 12
def T : Mark := 7

def xA : PFact := ⟨xB, [], .any, .conc T⟩
/-- `x.[any] = source()`. -/
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, xA)]⟩
/-- `C.f = x`. -/
def wr : Stmt :=
  ⟨[S, xB], [(⟨S, [], .star (.set [C]), .star⟩, pat S []),
    (⟨S, [C], .star (.set [fA]), .star⟩, pat S [C]), (pat xB [], pat xB []), (pat xB [], pat S [C, fA])]⟩
/-- `y = C.f.g`. -/
def rd : Stmt := readStmt S yB [C, fA, gA]
def readE : MicroEdge := (pat S [C, fA, gA], pat yB [])
def prog : Program :=
  ⟨fun _ => 0, fun _ => 3, [(0, 0, .stmt src, 1), (0, 1, .stmt wr, 2), (0, 2, .stmt rd, 3)]⟩
def sinkPat : PFact := ⟨S, [C, fA, gA], .exact, .conc T⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkPat)]
def counted (a : Acc) : Bool := !Nat.beq a C
def X : SCtx := ⟨prog, counted, 2, policy (fun _ => []), sinks, [0], S, true, true, .off, true, true⟩
/-- The field fact `(S, <C>.f, [any], 7)`. -/
def fC : AFact := ⟨⟨S, [C, fA], .any, .conc T⟩, false⟩

abbrev R : Obj → Prop :=
  DR prog counted 2 (fun _ _ => False) emitM satI restrictU (fun _ _ => False) sinks [0]

theorem m_src : (0, 0, Instr.stmt src, 1) ∈ prog.edges := by simp [prog]
theorem m_wr : (0, 1, Instr.stmt wr, 2) ∈ prog.edges := by simp [prog]
theorem m_rd : (0, 2, Instr.stmt rd, 3) ∈ prog.edges := by simp [prog]

theorem edgesR {M n n' : Nat} {ins : Instr} (h : (M, n, ins, n') ∈ prog.edges) :
    (M = 0 ∧ n = 0 ∧ ins = .stmt src ∧ n' = 1) ∨ (M = 0 ∧ n = 1 ∧ ins = .stmt wr ∧ n' = 2) ∨
    (M = 0 ∧ n = 2 ∧ ins = .stmt rd ∧ n' = 3) := by
  simp only [prog, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

theorem posIn_cases {p : List Acc} (h : PosIn X p) : p = [] ∨ p = [C] ∨ p = [C, fA] := by
  rcases h with ⟨M, n, s, n', e, hE, he, heb, rfl⟩ | ⟨M, n, s, hs, hsb, rfl⟩
  · rcases edgesR hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert heb <;> revert e <;> decide
  · have hs' : (M, n, s) = (0, 2, sinkPat) := List.mem_singleton.mp hs
    simp only [Prod.mk.injEq] at hs'
    obtain ⟨-, -, rfl⟩ := hs'
    decide

theorem abovePos_cases {q : List Acc} (h : AbovePos X q) : q = [] ∨ q = [C] := by
  obtain ⟨P, r, hP, hne, hPr⟩ := h
  rcases posIn_cases hP with rfl | rfl | rfl
  · exact (prefix_nil hne hPr).elim
  · exact .inl (prefix_one hne hPr)
  · exact prefix_two hne hPr

theorem swfr : SWFR X where
  ss := by
    intro M n s n' hE e he h1 h2
    refine .inl (ssB_sound ?_ h1 h2)
    rcases edgesR hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert h2 h1 <;> revert e <;> decide
  write := by
    intro M n s n' hE e he h1 h2 hab
    have hq := abovePos_cases hab
    clear hab
    exfalso
    rcases edgesR hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;>
      revert hq h2 h1 <;> revert e <;> decide
  toC := by
    intro M n c n' hE
    rcases edgesR hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  fromC := by
    intro M n c n' hE
    rcases edgesR hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  cut := by
    intro q r hc hab
    have h2 := cutPath_count hc
    rcases abovePos_cases hab with rfl | rfl <;> exact absurd h2 (by decide)

theorem r_e0 : R (.edge 0 zeroFact 0 ⟨zeroFact, false⟩) := DR.start (DR.root List.mem_cons_self)
theorem r_e1 : R (.edge 0 zeroFact 1 ⟨xA, false⟩) := DR.step r_e0 m_src (by decide)
/-- The field fact `(S, <C>.f, [any], 7)` in the restricted run. -/
theorem r_e2 : R (.edge 0 zeroFact 2 fC) := DR.step r_e1 m_wr (by decide)

theorem not_below (h : ∃ rr, [C, fA] = [C, fA, gA] ++ rr) : False := by
  obtain ⟨rr, h⟩ := h
  have h2 := congrArg List.length h
  simp only [List.length_append, List.length_cons, List.length_nil] at h2
  omega

/-- THE COUNTEREXAMPLE to the unrestricted forms of `static_step_below` and `static_sink_below`. -/
theorem deep_read_above :
    SWFR X ∧ R (.edge 0 zeroFact 2 fC) ∧ (0, 2, Instr.stmt rd, 3) ∈ X.P.edges ∧ readE ∈ rd.edges ∧
    readE.1.base = X.sB ∧ (∃ y, y ∈ (applyEdge fC readE.1 readE.2).facts) ∧
    ¬ (∃ rr, fC.fact.path = readE.1.path ++ rr) ∧
    (0, 2, sinkPat) ∈ X.sinks ∧ sinkPat.base = X.sB ∧ check zeroFact fC sinkPat = .triggered ∧
    ¬ (∃ rr, fC.fact.path = sinkPat.path ++ rr) :=
  ⟨swfr, r_e2, m_rd, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
    ⟨_, List.mem_singleton.mpr rfl⟩, not_below, List.mem_cons_self, rfl, rfl,
    not_below⟩

#print axioms deep_read_above

end DeepReadIter

/-- A restricted run of the spec rules raises no request (mark or position): it has no request
    object at all, so it needs no answer rule. -/
theorem no_request {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} :
    ∀ M i t, ¬ DR P counted L demand emitM satI restrictU recs sinks roots (.req M i t) :=
  RExact.DR_no_requestM

/-! ### The records of every run keep the invariant -/

/-- The exit edges of run 1 (`DS`, the final design) are good records (`Statics.cinv_all`). -/
theorem recOK_of_DS {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {j : PFact}
    {n : Node} {g : AFact} (h : DS X (.edge M j n g)) : RecOK X j g := by
  obtain ⟨hw, hid⟩ := (cinv_all hs hd.gen hd.deep hd.fb h :
    W2A g ∧ (AboveNE X g.fact → (∃ E0, j = ⟨X.sB, g.fact.path, .star E0, .star⟩) ∧
      (∃ E, g.fact.kind = .star E) ∧ Exact.absB g.fact.mark = true ∧ g.demand = false))
  exact ⟨hw, fun hab => ⟨(hid hab).1, (hid hab).2.1⟩⟩

/-- The exit edges of a restricted run are good records. -/
theorem recOK_of_DR {X : SCtx} (hs : SWFR X) {demand : MethodId → DemandEdge → Prop}
    {recs : MethodId → PFact × AFact → Prop} (hrecs : ∀ m j g, recs m (j, g) → RecOK X j g)
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {n : Node} {g : AFact}
    (h : DR X.P X.counted X.FL demand emitM satI restrictU recs sinks roots (.edge M j n g)) :
    RecOK X j g :=
  recOK_of (rinv_all hs hrecs h).1 (rinv_all hs hrecs h).2

/-! ## Part 2. The iteration from `DS`

Run 1 is `DS` (the final design). Its objects are projected to `Obj` (`projS`: the position
requests are dropped; nothing after run 1 reads them). The first link: `DS`'s summaries carry every
real witness in the den-aware sense that `Backward.B_general` needs (`reach_strongDSD`), by the
coverage proof of `Statics.coverageD`/`Statics.reachD` with the pair relation of the summaries kept.
-/

/-- The objects of run 1 as `Obj` (the position requests are dropped). -/
def projS (R : SObj → Prop) : Obj → Prop
  | .init M i => R (.init M i)
  | .edge M i n f => R (.edge M i n f)
  | .added M a => R (.added M a)
  | .req M i t => R (.req M i t)
  | .vuln M n s b => R (.vuln M n s b)

/-- The coverage statement of the second design, with the den-aware flow on the edge. -/
abbrev CovDD (X : SCtx) (M : MethodId) (i : PFact) (n : Node) (l0 l : Loc) : Prop :=
  (∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l ∧ Backward.FlowRD X.P (projS (DS X)) M l0 n l) ∨
  DS X (.req M i l0.mark) ∨ (∃ p, DS X (.sreq M i p) ∧ (sAns X.sB p).covers l0)

theorem covDD_conc {X : SCtx} (hs : SWF X) (hd : Design X) {M : MethodId} {i : PFact} {n : Node}
    {l0 l : Loc} {t : Mark} (hc : CovDD X M i n l0 l) (ht : i.mark = .conc t) :
    ∃ f, DS X (.edge M i n f) ∧ den i f.fact l0 l ∧ Backward.FlowRD X.P (projS (DS X)) M l0 n l := by
  rcases hc with h | hr | ⟨p, hsr, -⟩
  · exact h
  · exact absurd ht (req_abstractS hr t)
  · have := (sreq_parts hs hd hsr).1
    rw [ht] at this
    cases this

/-- `Statics.call_stepD` with the den-aware flow. -/
theorem call_stepDD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    {M : MethodId} {i : PFact} {n n' : Node} {f : AFact} {c : Call} {e1 e2 : MicroEdge}
    {l0 l l1 l2 l3 : Loc}
    (hf : DS X (.edge M i n f)) (hdn : den i f.fact l0 l)
    (hfr : Backward.FlowRD X.P (projS (DS X)) M l0 n l)
    (he : (M, n, Instr.call c, n') ∈ X.P.edges) (he1 : e1 ∈ c.toCallee) (hd1 : den e1.1 e1.2 l l1)
    (ihc : ∀ j, DS X (.init c.callee j) → j.covers l1 →
      CovDD X c.callee j (X.P.exit c.callee) l1 l2)
    (he2 : e2 ∈ c.fromCallee) (hd2 : den e2.1 e2.2 l2 l3) :
    CovDD X M i n' l0 l3 := by
  obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hdn hd1
  have hadd := DS.added hf he he1 ha
  have hac : a.fact.covers l1 := den_covers_final hda
  have useRet : ∀ j g, DS X (.init c.callee j) → j.covers l1 → applicable j a.fact = true →
      DS X (.edge c.callee j (X.P.exit c.callee) g) → den j g.fact l1 l2 →
      Backward.FlowRD X.P (projS (DS X)) c.callee l1 (X.P.exit c.callee) l2 →
      ∃ f', DS X (.edge M i n' f') ∧ den i f'.fact l0 l3 ∧
        Backward.FlowRD X.P (projS (DS X)) M l0 n' l3 := by
    intro j g hj hjc hap hg hdg hfc
    obtain ⟨r, hr, hdr⟩ := summary_stepM (Exact.applicable_markSub hap) hda hdg
    obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hwf he he2 hdr hd2
    exact ⟨_, DS.ret hf he he1 ha hj hap hg hr he2 hr', limitF_sound hdr',
      Backward.FlowRD.call (R := projS (DS X)) hfr he he1 hd1 hfc hj hg hjc hdg he2 hd2⟩
  have key := strong_ind (α := PFact) (fun j => posBound X - j.path.length)
    (P := fun j => DS X (.init c.callee j) → j.covers l1 → applicable j a.fact = true →
      CovDD X M i n' l0 l3) (by
    intro j rec hj hjc hap
    rcases ihc j hj hjc with ⟨g, hg, hdg, hfc⟩ | hreq | ⟨p, hsr, hpc⟩
    · exact .inl (useRet j g hj hjc hap hg hdg hfc)
    · have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
      rcases Coverage.mark_cases a.fact.mark with ham | ⟨t, ham⟩
      · have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hov
        rw [den_mark_abs hda ham] at hup
        exact .inr (.inl hup)
      · have hmk : a.fact.mark = .conc l1.mark := Coverage.den_mark_conc hda ham
        have hans := DS.answer hreq hadd hmk hov
        have hc' := ansInit_covers (X := X) (t := l1.mark) hjc hac rfl
        have hap' := ansInit_applicable (X := X) hap hmk
        obtain ⟨g, hg, hdg, hfc⟩ := covDD_conc hs hd (ihc _ hans hc') ansInit_mark
        exact .inl (useRet _ g hans hc' hap' hg hdg hfc)
    · obtain ⟨-, -, hpos, r, hne, hpr⟩ := sreq_parts hs hd hsr
      have hov : overlapB a.fact (sAns X.sB p) = true := overlapB_of_common hac hpc
      have hab0 : a.fact.base = X.sB := by
        unfold overlapB at hov
        simp only [Bool.and_eq_true] at hov
        exact CoreAux.beq_iff.mp hov.1
      cases hbl : belowB a.fact p with
      | true =>
        have hok : X.ansOK a.fact p = true := by
          unfold SCtx.ansOK
          rw [hov, hbl, Bool.or_true]
          rfl
        have hans := DS.sanswer hsr hadd hok
        exact rec (sAns X.sB p) (measure_lt hpos hne hpr) hans hpc (sAns_applicable hab0 hbl)
      | false =>
        have habv : Statics.aboveB X.sB a.fact p = true := by
          unfold Statics.aboveB
          rw [hov, hbl]
          rfl
        have hab := aboveNE_of_above hpos habv
        obtain ⟨⟨E0, hi⟩, hak, -⟩ := bind_identity hs hd hf he he1 ha hab
        have hib : i.base = X.sB := by rw [hi]
        have hcl : X.climbOK i a.fact p = true := by
          unfold SCtx.climbOK
          rw [hd.wide, if_pos rfl, hib, Nat.beq_refl, habv]
          rfl
        have hup := DS.sreqUp hsr hf he rfl he1 ha hcl
        rw [hi] at hda
        obtain ⟨h0b, h0p⟩ := id_den hab.1 rfl hak hda
        obtain ⟨-, ⟨σ, hlp, -⟩, -⟩ := hpc
        exact .inr (.inr ⟨p, hup, sAns_covers h0b (h0p.trans hlp)⟩))
  exact key _ (DS.initA hadd) (applicable_sound (α_applicable hs c.callee a.fact) hac)
    (α_applicable hs c.callee a.fact)

#print axioms call_stepDD

/-- `Statics.coverageD` with the den-aware flow: a covered pair of a demanded flow is carried by a
    den-aware flow of `DS`'s summaries. -/
theorem coverageDD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow X.P M l0 n l) :
    ∀ i, DS X (.init M i) → i.covers l0 → CovDD X M i n l0 l := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, DS.start hi, startFact_sound hc, Backward.FlowRD.start M l0⟩
  | @step M l0 n l n' l' s _ he hst ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn, hfr⟩ | hr | hsr
    · rcases step_split (P := X.fireB i f) hst with hs' | ⟨e, hes, hfire, hde⟩
      · rcases transfer_sound (counted := X.counted) (L := X.FL)
            (sKeep_wf (hwf.stmtTouched _ _ _ _ he)) hdn hs' with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
        · exact .inl ⟨r, DS.step hf he hr, hdr, Backward.FlowRD.step hfr he hst⟩
        · exact .inr (.inl (DS.reqStmt hf he hq))
      · have hfire' := hfire
        unfold SCtx.fireB at hfire'
        rw [hd.gen, if_pos rfl] at hfire'
        obtain ⟨hid, -, -, -, -, -, -⟩ := genFire_parts hfire'
        obtain ⟨⟨E0, hi'⟩, hfb, hfp, hfk, -, -⟩ := idEdge_parts hid
        rw [hi'] at hdn
        obtain ⟨h0b, h0p⟩ := id_den hfb hfp hfk hdn
        obtain ⟨-, -, -, -, -, σ', -, hlp, -, -, -⟩ := hde
        refine .inr (.inr ⟨X.reqP e.1.path, DS.sreqStmt hf he hes hfire, ?_⟩)
        rw [reqP_gen hd.gen]
        exact sAns_covers h0b (h0p.trans (hlp.trans (by
          rw [← List.append_assoc, List.take_append_drop])))
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn, hfr⟩ | hr | hsr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hdn.2.1]
        exact hm
      exact .inl ⟨f, DS.pass hf he hb, hdn, Backward.FlowRD.pass hfr he hm⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn, hfr⟩ | hr | hsr
    · exact call_stepDD hs hd hwf hf hdn hfr he he1 hd1 ihc he2 hd2
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn, hfr⟩ | hr | hsr
    · rcases cleanRes_sound hdn hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DS.clean hf he hr, hdr, Backward.FlowRD.clean hfr he hcl⟩
      · exact .inr (.inl (DS.reqClean hf he hq))
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hdn, hfr⟩ | hr | hsr
    · exact .inl ⟨f, DS.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hdn hl), hdn,
        Backward.FlowRD.filt hfr he hl⟩
    · exact .inr (.inl hr)
    · exact .inr (.inr hsr)

#print axioms coverageDD

mutual
/-- `Statics.GoodD` with the den-aware flow on the edge. -/
inductive GoodDD (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : PFact → Prop where
  | mk {j : PFact} : DS X (.init M j) → j.covers l0 →
      (∃ f, DS X (.edge M j n f) ∧ den j f.fact l0 l ∧
        Backward.FlowRD X.P (projS (DS X)) M l0 n l) →
      (DS X (.req M j l0.mark) → GoodCD X M n l0 l) →
      (∀ p, DS X (.sreq M j p) → (sAns X.sB p).covers l0 → GoodPD X M n l0 l p) →
      GoodDD X M n l0 l j
inductive GoodCD (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : Prop where
  | mk {j : PFact} {t : Mark} : GoodDD X M n l0 l j → j.mark = .conc t → GoodCD X M n l0 l
inductive GoodPD (X : SCtx) (M : MethodId) (n : Node) (l0 l : Loc) : List Acc → Prop where
  | mk {j : PFact} {p r : List Acc} : GoodDD X M n l0 l j → j.path = p ++ r → GoodPD X M n l0 l p
end

theorem good_concDD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF) {M : MethodId}
    {n : Node} {l0 l : Loc} {j : PFact} {t : Mark} (hfl : Flow X.P M l0 n l)
    (hj : DS X (.init M j)) (hc : j.covers l0) (ht : j.mark = .conc t) : GoodDD X M n l0 l j :=
  .mk hj hc (covDD_conc hs hd (coverageDD hs hd hwf hfl j hj hc) ht)
    (fun hr => absurd ht (req_abstractS hr t))
    (fun _ hsr _ => by
      have h1 := (sreq_parts hs hd hsr).1
      rw [ht] at h1
      cases h1)

/-- THE FIRST LINK: run 1 (`DS`, the final design) makes every real witness a den-aware witness of
    its own summaries (`Statics.reachD` with the pair relation kept). -/
theorem reach_strongDSD {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF) {M : MethodId}
    {n : Node} {l : Loc} (hR : Reach X.P X.roots M n l) :
    (∃ l0 j, GoodDD X M n l0 l j) ∧ Backward.ReachRD X.P (projS (DS X)) X.roots M n l := by
  induction hR with
  | root hM hfl =>
    have hg := good_concDD hs hd hwf hfl (DS.root hM) Coverage.zeroFact_covers rfl
    refine ⟨⟨zeroLoc, zeroFact, hg⟩, ?_⟩
    cases hg with
    | mk _ _ hedge _ _ =>
      obtain ⟨_, _, _, hfr⟩ := hedge
      exact Backward.ReachRD.root hM hfr
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨⟨l0, i, hgi⟩, hRR⟩ := ih
    cases hgi with
    | mk hi hic hedge hmark hpos =>
    obtain ⟨f, hf, hdn, -⟩ := hedge
    obtain ⟨a, ha, hda⟩ := Coverage.bind_in hwf he he1 hdn hd1
    have hadd := DS.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    have markRes : ∀ j, DS X (.init c.callee j) → j.covers l1 → DS X (.req c.callee j l1.mark) →
        ∃ j', GoodDD X c.callee n2 l1 l2 j' ∧ (∃ t, j'.mark = .conc t) ∧
          ∃ r, j'.path = j.path ++ r := by
      intro j hj hjc hreq
      have hconc : ∃ a', DS X (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases Coverage.mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := DS.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapB_of_common hac hjc)
          rw [den_mark_abs hda ham] at hup
          obtain ⟨hg', ht⟩ := hmark hup
          cases hg' with
          | mk hj' hjc' hedge' _ _ =>
          obtain ⟨f', hf', hdn', -⟩ := hedge'
          obtain ⟨a', ha', hda'⟩ := Coverage.bind_in hwf he he1 hdn' hd1
          obtain ⟨t1, h1⟩ := edge_concS hf' ht
          obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
          exact ⟨a'.fact, DS.added hf' he he1 ha', den_covers_final hda',
            Coverage.den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, Coverage.den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := DS.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      obtain ⟨r, hr⟩ := ansInit_path (X := X) (i := j) (a := a') (t := l1.mark)
      exact ⟨_, good_concDD hs hd hwf hfc hans (ansInit_covers hjc hac' rfl) ansInit_mark,
        ⟨_, ansInit_mark⟩, r, hr⟩
    have key := strong_ind (α := PFact) (fun j => posBound X - j.path.length)
      (P := fun j => DS X (.init c.callee j) → j.covers l1 →
        ∃ j', GoodDD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = j.path ++ r) (by
      intro j rec hj hjc
      have posRes : ∀ p, DS X (.sreq c.callee j p) → (sAns X.sB p).covers l1 →
          ∃ j', GoodDD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = p ++ r := by
        intro p hsr hpc
        obtain ⟨-, -, hpos', r, hne, hpr⟩ := sreq_parts hs hd hsr
        have hlt := measure_lt hpos' hne hpr
        have answerFrom : ∀ a', DS X (.added c.callee a') → a'.covers l1 → belowB a' p = true →
            ∃ j', GoodDD X c.callee n2 l1 l2 j' ∧ ∃ r, j'.path = p ++ r := by
          intro a' hadd' hac' hbl
          have hov := overlapB_of_common hac' hpc
          have hok : X.ansOK a' p = true := by
            unfold SCtx.ansOK
            rw [hov, hbl, Bool.or_true]
            rfl
          exact rec (sAns X.sB p) hlt (DS.sanswer hsr hadd' hok) hpc
        have hov : overlapB a.fact (sAns X.sB p) = true := overlapB_of_common hac hpc
        cases hbl : belowB a.fact p with
        | true => exact answerFrom a.fact hadd hac hbl
        | false =>
          have habv : Statics.aboveB X.sB a.fact p = true := by
            unfold Statics.aboveB
            rw [hov, hbl]
            rfl
          have hab := aboveNE_of_above hpos' habv
          obtain ⟨⟨E0, hi'⟩, hak, -⟩ := bind_identity hs hd hf he he1 ha hab
          have hib : i.base = X.sB := by rw [hi']
          have hcl : X.climbOK i a.fact p = true := by
            unfold SCtx.climbOK
            rw [hd.wide, if_pos rfl, hib, Nat.beq_refl, habv]
            rfl
          have hup := DS.sreqUp hsr hf he rfl he1 ha hcl
          have hda' := hda
          rw [hi'] at hda'
          obtain ⟨h0b, h0p⟩ := id_den hab.1 rfl hak hda'
          have hpc0 : (sAns X.sB p).covers l0 := by
            obtain ⟨-, ⟨σ, hlp, -⟩, -⟩ := hpc
            exact sAns_covers h0b (h0p.trans hlp)
          cases hpos p hup hpc0 with
          | @mk jc pp rc hgc hrc =>
          cases hgc with
          | mk hjc' _ hedge' _ _ =>
          obtain ⟨f'', hf'', hdn'', -⟩ := hedge'
          obtain ⟨a'', ha'', hda''⟩ := Coverage.bind_in hwf he he1 hdn'' hd1
          have hac'' : a''.fact.covers l1 := den_covers_final hda''
          cases hbl'' : belowB a''.fact p with
          | true => exact answerFrom a''.fact (DS.added hf'' he he1 ha'') hac'' hbl''
          | false =>
            exfalso
            have hov'' := overlapB_of_common hac'' hpc
            have habv'' : Statics.aboveB X.sB a''.fact p = true := by
              unfold Statics.aboveB
              rw [hov'', hbl'']
              rfl
            obtain ⟨⟨E1, hjc''⟩, -, -⟩ :=
              bind_identity hs hd hf'' he he1 ha'' (aboveNE_of_above hpos' habv'')
            obtain ⟨-, r3, hne3, hp3, -⟩ := above_parts habv''
            have hjp : jc.path = a''.fact.path := by rw [hjc'']
            have h0 := congrArg List.length (hrc.symm.trans hjp)
            rw [hp3, List.length_append, List.length_append] at h0
            cases r3 with
            | nil => exact hne3 rfl
            | cons x rs =>
              have h1 : (x :: rs).length + rc.length = 0 :=
                Nat.add_left_cancel ((Nat.add_assoc _ _ _).symm.trans (h0.trans (Nat.add_zero _).symm))
              rw [List.length_cons, Nat.add_right_comm] at h1
              exact Nat.succ_ne_zero _ h1
      rcases coverageDD hs hd hwf hfc j hj hjc with ⟨g, hg, hdg, hfrg⟩ | hreq | ⟨p, hsr, hpc⟩
      · refine ⟨j, .mk hj hjc ⟨g, hg, hdg, hfrg⟩ (fun hreq => ?_) (fun p hsr hpc => ?_),
          [], by rw [List.append_nil]⟩
        · obtain ⟨j', hg', ⟨t, ht⟩, -⟩ := markRes j hj hjc hreq
          exact .mk hg' ht
        · obtain ⟨j', hg', r, hr⟩ := posRes p hsr hpc
          exact .mk hg' hr
      · obtain ⟨j', hg', -, r, hr⟩ := markRes j hj hjc hreq
        exact ⟨j', hg', r, hr⟩
      · obtain ⟨-, -, -, r, -, hpr⟩ := sreq_parts hs hd hsr
        obtain ⟨j', hg', r', hr'⟩ := posRes p hsr hpc
        exact ⟨j', hg', r ++ r', by rw [hr', hpr, List.append_assoc]⟩)
    obtain ⟨j', hg', -⟩ := key _ (DS.initA hadd)
      (applicable_sound (α_applicable hs c.callee a.fact) hac)
    refine ⟨⟨l1, j', hg'⟩, ?_⟩
    cases hg' with
    | mk hj' hjc' hedge' _ _ =>
      obtain ⟨_, _, _, hfr'⟩ := hedge'
      exact Backward.ReachRD.down (R := projS (DS X)) hRR he he1 hd1 hj' hjc' hfr'

#print axioms reach_strongDSD

/-- A restricted run of the spec rules makes every demanded witness a den-aware witness of its own
    summaries (`Backward.reach_strongRD` for `restrictU`). -/
theorem reachRD_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (hwf : P.WF)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachR P demand roots M n l) :
    Backward.ReachRD P (DR P counted L demand emitM satI restrictU recs sinks roots) roots M n l := by
  rw [RMain.runU_eq_S]
  exact (Backward.reach_strongRD P counted L demand emitM satI restrictS recs sinks roots hwf
    (RCov.emitOn_of_conc P counted L demand emitM satI restrictS recs sinks roots
      RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract hRe).1

#print axioms reachRD_M

/-- The run sequence from `DS`: run 0 is `DS` with the final design (projected to `Obj`), run
    `k + 1` is the plain restricted closure `DR` with the spec rules, the demand `dem k`, the field
    limit `Ls (k + 1)` and the records `recs k`. No static rule after run 0. -/
def runSeqS (X : SCtx) (Ls : Nat → Nat) (dem : Nat → MethodId → DemandEdge → Prop)
    (recs : Nat → MethodId → PFact × AFact → Prop) : Nat → Obj → Prop
  | 0 => projS (DS X)
  | k + 1 => DR X.P X.counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) X.sinks X.roots

/-- THE ITERATION FROM `DS`, with the den-aware contract: if every backward step satisfies
    `BackwardContractD`, every run of the sequence reports every real vulnerability. -/
theorem iteration_sound_DS {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    (hB : ∀ k, Backward.BackwardContractD X.P X.roots X.sinks (runSeqS X Ls dem recs k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach X.P X.roots M n l) (hsk : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, Backward.ReachRD X.P (runSeqS X Ls dem recs k) X.roots M n l ∧
      ∃ b, runSeqS X Ls dem recs k (.vuln M n s b) := by
  intro k
  induction k with
  | zero => exact ⟨(reach_strongDSD hs hd hwf hRe).2, vulnD hs hd hwf hRe hsk hT hsc⟩
  | succ k ih =>
    have hRk := hB k M n l s T hsk hT hsc ih.1 ih.2
    exact ⟨reachRD_M hwf hRk, (RMain.vuln_found_M hwf hRk hsk hT hsc).1⟩

#print axioms iteration_sound_DS

/-- THE GENERAL ITERATION FROM `DS`, END TO END. Run 1 is `DS` with the final design (under
    `Statics.SWF`); every later forward run is the plain `DR` and every backward run the plain `DB`
    of the user's design (its backward demand contains the reversed summaries of the previous
    forward run, its seeds contain the sinks that run reported). Then every forward run reports
    every real vulnerability. The program hypotheses are those of `Backward.iteration_general`. -/
theorem iteration_general_DS {X : SCtx} (hs : SWF X) (hd : Design X) (hwf : X.P.WF)
    (hT : Reverse.BindTargetsStar X.P) (hmr : Backward.StmtsMarkRev X.P)
    (hNZB : Backward.NoZeroBack X.P) (hZ : Backward.ZeroKept X.P)
    (hX : Backward.ExitReach X.P X.roots)
    (hk : ∀ M n s, (M, n, s) ∈ X.sinks → s.kind = .exact ∨ s.kind = .any)
    {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand X.P (runSeqS X Ls dem recs k) m d → demB k m d)
    (hseeds : ∀ k M n s b, runSeqS X Ls dem recs k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev X.P) (Backward.DB (Reverse.Program.rev X.P) X.counted
      (LB k) (demB k) emitM satI restrictU (recsB k) [] X.roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach X.P X.roots M n l) (hsk : (M, n, s) ∈ X.sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqS X Ls dem recs k (.vuln M n s b) :=
  fun k => (iteration_sound_DS hs hd hwf (fun k M' n' l' s' T' hs' hT'' hc' hr' hv' =>
    RCov.reachR_mono (hdem k)
      (Backward.B_general hwf hT hmr hNZB hZ hX hk (hseeds k) (hdemB k) M' n' l' s' T' hs' hT''
        hc' hr' hv'))
    hRe hsk hT' hsc k).2

#print axioms iteration_general_DS

/-- NO STATIC RULE AFTER RUN 1, along the whole iteration: every later forward run satisfies the
    static invariant (no static `*`/`[any]` fact strictly above a position), raises no request,
    and every static read, write keep edge and sink that gives a result is the case at-or-below.
    The hypotheses: the construction rules of run 1 (`SWF X`), the field limit of every later run
    never cuts above a position, and the persisted records keep the run-1 invariant (they do when
    they are exit edges of `DS` or of a restricted run: `recOK_of_DS`, `recOK_of_DR`). -/
theorem no_static_rule_after_run1 {X : SCtx} (hs : SWF X) {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (hcut : ∀ k q r, cutPath X.counted (Ls (k + 1)) q = some r → ¬ AbovePos X r)
    (hrecs : ∀ k m j g, recs k m (j, g) → RecOK X j g) (k : Nat) :
    (∀ o, runSeqS X Ls dem recs (k + 1) o → RInv X o) ∧
    (∀ M i t, ¬ runSeqS X Ls dem recs (k + 1) (.req M i t)) := by
  refine ⟨fun o h => ?_, fun M i t h => no_request M i t h⟩
  exact rinv_all (X := { X with FL := Ls (k + 1) }) (swfr_limit hs (hcut k))
    (fun m j g h => hrecs k m j g h) h

#print axioms no_static_rule_after_run1

/-! ## Part 3. End-to-end evidence on the programs of `Statics.lean`

For each program: run 1 = `DS` with the final design (`Design`); the backward run 2 = `DB` of the
user's design on the reversed program, restricted by the reversed summaries of run 1
(`revSummaryDemand P (projS (DS X2))`), seeded at the sinks run 1 reported, field limit 2; the
hand-off `demOf`; forward run 3 = the plain `DR` (field limit 2, no record). Run 3 reports the
vulnerability through a NORMAL-layer sink edge (the `vuln` object has `demand = false`), it is
CONFIRMED (`RExact.ConfirmedM`: the support chain is the exact concrete added facts), and run 3
has no request (`no_request`). -/

/-! ### `Example` (`root: C1.f = source(); A()`, `A: B()`, `B: x = C1.f; sink(x)`) -/

namespace ExampleIter
open ApSpec.Statics.Example

/-- Run 1: the final design on the example program. -/
def X2 : SCtx := ⟨prog, counted, 2, α1, sinks, [0], S, true, true, .off, true, true⟩

theorem x2_design : Design X2 := ⟨rfl, rfl, rfl, rfl, rfl⟩

def wSF : AFact := ⟨wS, false⟩
def AnsF : AFact := ⟨Ans, false⟩
def SrootF : AFact := ⟨Sroot, false⟩
def zfF : AFact := ⟨zeroFact, false⟩
def xT : AFact := ⟨⟨xB, [], .exact, .conc T⟩, false⟩

theorem r_start : DS X2 (.edge 0 zeroFact 0 zfF) := DS.start (DS.root List.mem_cons_self)
theorem r_src : DS X2 (.edge 0 zeroFact 1 wSF) := DS.step r_start m_src (by decide)
theorem aA_w : DS X2 (.added 1 wS) := DS.added (a := wSF) r_src m_cA List.mem_cons_self (by decide)
theorem jA_root : DS X2 (.init 1 Sroot) := by
  have h : X2.α 1 wS = Sroot := by decide
  exact h ▸ DS.initA aA_w
theorem eA_root : DS X2 (.edge 1 Sroot 0 SrootF) := DS.start jA_root
theorem aB_root : DS X2 (.added 2 Sroot) :=
  DS.added (a := SrootF) eA_root m_cB List.mem_cons_self (by decide)
theorem jB_root : DS X2 (.init 2 Sroot) := by
  have h : X2.α 2 Sroot = Sroot := by decide
  exact h ▸ DS.initA aB_root
theorem eB_root : DS X2 (.edge 2 Sroot 0 SrootF) := DS.start jB_root
theorem sB_req : DS X2 (.sreq 2 Sroot [C1, fA]) :=
  DS.sreqStmt (e := readE) eB_root m_rd (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem sA_req : DS X2 (.sreq 1 Sroot [C1, fA]) :=
  DS.sreqUp (a := SrootF) (e := bindS) sB_req eA_root m_cB rfl List.mem_cons_self
    (by decide) (by decide)
theorem jA_ans : DS X2 (.init 1 Ans) := DS.sanswer sA_req aA_w (by decide)
theorem eA_ans : DS X2 (.edge 1 Ans 0 AnsF) := DS.start jA_ans
theorem aB_ans : DS X2 (.added 2 Ans) :=
  DS.added (a := AnsF) eA_ans m_cB List.mem_cons_self (by decide)
theorem jB_ans : DS X2 (.init 2 Ans) := DS.sanswer sB_req aB_ans (by decide)
theorem eB_ans0 : DS X2 (.edge 2 Ans 0 AnsF) := DS.start jB_ans
theorem eB_ans1 : DS X2 (.edge 2 Ans 1 ⟨pat xB [], false⟩) := DS.step eB_ans0 m_rd (by decide)
theorem rB_ans : DS X2 (.req 2 Ans T) := DS.reqSink eB_ans1 m_sink (by decide)
theorem rA_ans : DS X2 (.req 1 Ans T) :=
  DS.reqUp (a := AnsF) (e := bindS) rB_ans eA_ans m_cB rfl List.mem_cons_self
    (by decide) (by decide) (by decide)
theorem jA_w : DS X2 (.init 1 wS) := by
  have h : X2.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer rA_ans aA_w rfl (by decide)
theorem eA_w : DS X2 (.edge 1 wS 0 wSF) := DS.start jA_w
theorem aB_w : DS X2 (.added 2 wS) := DS.added (a := wSF) eA_w m_cB List.mem_cons_self (by decide)
theorem jB_w : DS X2 (.init 2 wS) := by
  have h : X2.ansInit Ans wS T = wS := by decide
  exact h ▸ DS.answer rB_ans aB_w rfl (by decide)
theorem eB_w0 : DS X2 (.edge 2 wS 0 wSF) := DS.start jB_w
theorem eB_w1 : DS X2 (.edge 2 wS 1 xT) := DS.step eB_w0 m_rd (by decide)
/-- Run 1 (the final design) reports the vulnerability in the normal layer: the seed. -/
theorem run1_vuln : DS X2 (.vuln 2 1 sinkPat false) := DS.vuln eB_w1 m_sink (by decide)

#print axioms run1_vuln

/-! #### Backward run 2: the complete closure (it does not depend on the backward demand) -/

def Pb : Program := Reverse.Program.rev prog

theorem Pb_edges : Pb.edges =
    [(0, 1, .stmt (Reverse.Stmt.rev src), 0), (0, 2, .call (Reverse.Call.rev cA), 1),
     (1, 1, .call (Reverse.Call.rev cB), 0), (2, 1, .stmt (Reverse.Stmt.rev rd), 0)] := rfl

/-- The backward run of the user's design (any backward demand and backward records). -/
abbrev B2 (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop) :
    Obj → Prop :=
  Backward.DB Pb counted 2 demB emitM satI restrictU recsB [] [0] sinks true

/-- The seed `(x, ., $, 7)` at the sink of `B`. -/
def Sx : AFact := ⟨⟨xB, [], .exact, .conc T⟩, false⟩

def initsBE : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (2, zeroFact)]
def edgesBE : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Backward.zeroAF), (0, zeroFact, 1, Backward.zeroAF), (0, zeroFact, 1, wSF),
   (0, zeroFact, 0, Backward.zeroAF), (0, zeroFact, 0, wSF),
   (1, zeroFact, 1, Backward.zeroAF), (1, zeroFact, 0, Backward.zeroAF), (1, zeroFact, 0, wSF),
   (2, zeroFact, 1, Backward.zeroAF), (2, zeroFact, 1, Sx), (2, zeroFact, 0, Backward.zeroAF),
   (2, zeroFact, 0, wSF)]

def InvBE : Obj → Prop
  | .init M i => (M, i) ∈ initsBE
  | .edge M i n f => (M, i, n, f) ∈ edgesBE
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBE := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBE))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBE))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

/-- THE COMPLETE BACKWARD RUN 2 OF THE EXAMPLE, for every backward demand (in particular the
    reversed summaries of run 1) and every backward record set. -/
theorem inv_bE (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    {o : Obj} (h : B2 demB recsB o) : InvBE o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBE, InvBE (.edge x.1 x.2 (Pb.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer counted 2 (Reverse.Stmt.rev src) x.2.2.2).facts,
          InvBE (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesBE, x.1 = 2 → x.2.2.1 = 1 →
              ∀ f' ∈ (transfer counted 2 (Reverse.Stmt.rev rd) x.2.2.2).facts,
                InvBE (.edge 2 x.2.1 0 f'))
              (2, i, 1, f) ih rfl rfl f' hf
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer counted 2 (Reverse.Stmt.rev src) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesBE, x.1 = 2 → x.2.2.1 = 1 →
              ∀ t ∈ (transfer counted 2 (Reverse.Stmt.rev rd) x.2.2.2).reqs, False)
              (2, i, 1, f) ih rfl rfl t ht
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Reverse.Call.rev cA).touched = false →
            InvBE (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBE, x.1 = 1 → x.2.2.1 = 1 →
            memB x.2.2.2.fact.base (Reverse.Call.rev cB).touched = false →
              InvBE (.edge 1 x.2.1 0 x.2.2.2))
            (1, i, 1, f) ih rfl rfl hm
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Reverse.Call.rev cA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBE, x.1 = 1 → x.2.2.1 = 1 →
            ∀ e ∈ (Reverse.Call.rev cB).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
            (1, i, 1, f) ih rfl rfl e he a ha
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | initR _ _ _ ih => exact ih.elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ _ _ _ _ _ ihf _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact ((by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Reverse.Call.rev cA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha).elim
      | tail _ hE => cases hE with
        | head =>
          exact ((by decide : ∀ x ∈ edgesBE, x.1 = 1 → x.2.2.1 = 1 →
            ∀ e ∈ (Reverse.Call.rev cB).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
            (1, i, 1, f) ihf rfl rfl e1 he1 a ha).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ _ _ ihf =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact ((by decide : ∀ x ∈ edgesBE, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Reverse.Call.rev cA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha).elim
      | tail _ hE => cases hE with
        | head =>
          exact ((by decide : ∀ x ∈ edgesBE, x.1 = 1 → x.2.2.1 = 1 →
            ∀ e ∈ (Reverse.Call.rev cB).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False)
            (1, i, 1, f) ihf rfl rfl e1 he1 a ha).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | head => decide
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | head => decide
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBE, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Reverse.Call.rev cA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBE (.edge 0 zeroFact 1 (limitF counted 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ y ∈ edgesBE, y.1 = 2 → y.2.1 = zeroFact → y.2.2.1 = 0 →
            ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
            ∀ e2 ∈ (Reverse.Call.rev cB).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
              InvBE (.edge 1 zeroFact 0 (limitF counted 2 r')))
            (2, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
        | tail _ hE => cases hE with
          | tail _ hE => cases hE

#print axioms inv_bE

/-! #### The hand-off, exactly -/

theorem hbE_src : (0, 1, Instr.stmt (Reverse.Stmt.rev src), 0) ∈ Pb.edges := Reverse.mem_rev_stmt m_src
theorem hbE_cA : (0, 2, Instr.call (Reverse.Call.rev cA), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cA
theorem hbE_cB : (1, 1, Instr.call (Reverse.Call.rev cB), 0) ∈ Pb.edges := Reverse.mem_rev_call m_cB
theorem hbE_rd : (2, 1, Instr.stmt (Reverse.Stmt.rev rd), 0) ∈ Pb.edges := Reverse.mem_rev_stmt m_rd

section DeriveE
variable (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)

theorem b_e02 : B2 demB recsB (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root List.mem_cons_self)
theorem b_i1 : B2 demB recsB (.init 1 zeroFact) :=
  Backward.DB.zin (c := Reverse.Call.rev cA) rfl (b_e02 demB recsB) hbE_cA
theorem b_e11 : B2 demB recsB (.edge 1 zeroFact 1 Backward.zeroAF) :=
  Backward.DB.start (b_i1 demB recsB)
theorem b_i2 : B2 demB recsB (.init 2 zeroFact) :=
  Backward.DB.zin (c := Reverse.Call.rev cB) rfl (b_e11 demB recsB) hbE_cB
theorem b_e21 : B2 demB recsB (.edge 2 zeroFact 1 Backward.zeroAF) :=
  Backward.DB.start (b_i2 demB recsB)
/-- The sink rule: the seed `(x, ., $, 7)`. -/
theorem b_s21 : B2 demB recsB (.edge 2 zeroFact 1 Sx) :=
  Backward.DB.seed (s := sinkPat) List.mem_cons_self (b_e21 demB recsB)
/-- `x = C1.f` reversed: the requirement `(S, <C1>.f, $, 7)` at the forward entry of `B`. -/
theorem b_w20 : B2 demB recsB (.edge 2 zeroFact 0 wSF) :=
  Backward.DB.step (b_s21 demB recsB) hbE_rd (by decide)
/-- The balanced return in `A`. -/
theorem b_w10 : B2 demB recsB (.edge 1 zeroFact 0 wSF) :=
  Backward.DB.zret (c := Reverse.Call.rev cB) (r := wSF) (r' := wSF) rfl (b_e11 demB recsB) hbE_cB
    (b_w20 demB recsB) (by decide) List.mem_cons_self (by decide)
/-- The balanced return in the root. -/
theorem b_w01 : B2 demB recsB (.edge 0 zeroFact 1 wSF) :=
  Backward.DB.zret (c := Reverse.Call.rev cA) (r := wSF) (r' := wSF) rfl (b_e02 demB recsB) hbE_cA
    (b_w10 demB recsB) (by decide) List.mem_cons_self (by decide)
theorem b_w00 : B2 demB recsB (.edge 0 zeroFact 0 wSF) :=
  Backward.DB.step (b_w01 demB recsB) hbE_src (by decide)

end DeriveE

def demListE : List (MethodId × DemandEdge) :=
  [(0, Backward.zeroDem), (0, ⟨wS, none⟩), (1, Backward.zeroDem), (1, ⟨wS, none⟩),
   (2, Backward.zeroDem), (2, ⟨wS, none⟩)]

/-- THE HAND-OFF OF THE EXAMPLE, EXACTLY: the zero demand and, in each method, the exact static
    field `((S, <C1>.f, $, 7), none)`; for every backward demand (in particular the reversed
    summaries of run 1) and every backward record set. The static demand pattern is exact and at a
    position. -/
theorem demE_exact (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    (m : MethodId) (d : DemandEdge) :
    Backward.demOf Pb (B2 demB recsB) m d ↔
      d = Backward.zeroDem ∨ ((m = 0 ∨ m = 1 ∨ m = 2) ∧ d = ⟨wS, none⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, _, _⟩)
    · exact .inl h
    · have hm := (by decide : ∀ x ∈ edgesBE, x.2.1 = zeroFact → x.2.2.1 = 0 →
        (x.1, (⟨x.2.2.2.fact, none⟩ : DemandEdge)) ∈ demListE)
        (m, zeroFact, 0, g) (inv_bE demB recsB hg) rfl rfl
      revert hm
      generalize (⟨g.fact, none⟩ : DemandEdge) = d'
      intro hm
      cases hm with
      | head => exact .inl rfl
      | tail _ h => cases h with
        | head => exact .inr ⟨.inl rfl, rfl⟩
        | tail _ h => cases h with
          | head => exact .inl rfl
          | tail _ h => cases h with
            | head => exact .inr ⟨.inr (.inl rfl), rfl⟩
            | tail _ h => cases h with
              | head => exact .inl rfl
              | tail _ h => cases h with
                | head => exact .inr ⟨.inr (.inr rfl), rfl⟩
                | tail _ h => cases h
    · exact absurd ((by decide : ∀ x ∈ initsBE, x.2 = zeroFact) (m, jb) (inv_bE demB recsB hjb))
        hne
  · rintro (rfl | ⟨hm, rfl⟩)
    · exact .inl rfl
    · rcases hm with rfl | rfl | rfl
      · exact .inr (.inl ⟨wSF, b_w00 demB recsB, rfl⟩)
      · exact .inr (.inl ⟨wSF, b_w10 demB recsB, rfl⟩)
      · exact .inr (.inl ⟨wSF, b_w20 demB recsB, rfl⟩)

#print axioms demE_exact

/-! #### Forward run 3: the plain `DR`, normal layer, confirmed -/

/-- The backward run of the iteration: restricted by the reversed summaries of run 1, seeded at
    the sinks run 1 reported (`sinks`, `run1_vuln`), no backward record. -/
abbrev B2run : Obj → Prop :=
  B2 (Backward.revSummaryDemand prog (projS (DS X2))) (fun _ _ => False)

/-- Forward run 3. -/
abbrev R3 : Obj → Prop :=
  DR prog counted 2 (Backward.demOf Pb B2run) emitM satI restrictU (fun _ _ => False) sinks [0]

theorem demE1 : Backward.demOf Pb B2run 1 ⟨wS, none⟩ := .inr (.inl ⟨wSF, b_w10 _ _, rfl⟩)
theorem demE2 : Backward.demOf Pb B2run 2 ⟨wS, none⟩ := .inr (.inl ⟨wSF, b_w20 _ _, rfl⟩)

theorem f_e00 : R3 (.edge 0 zeroFact 0 zfF) := DR.start (DR.root List.mem_cons_self)
theorem f_e01 : R3 (.edge 0 zeroFact 1 wSF) := DR.step f_e00 m_src (by decide)
theorem f_aA : R3 (.added 1 wS) := DR.added (a := wSF) f_e01 m_cA List.mem_cons_self (by decide)
/-- `A` emits the exact static field from the demand `((S, <C1>.f, $, 7), none)`. -/
theorem f_jA : R3 (.init 1 wS) := DR.initR (d := ⟨wS, none⟩) f_aA demE1 (by decide)
theorem f_eA0 : R3 (.edge 1 wS 0 wSF) := DR.start f_jA
theorem f_aB : R3 (.added 2 wS) := DR.added (a := wSF) f_eA0 m_cB List.mem_cons_self (by decide)
theorem f_jB : R3 (.init 2 wS) := DR.initR (d := ⟨wS, none⟩) f_aB demE2 (by decide)
theorem f_eB0 : R3 (.edge 2 wS 0 wSF) := DR.start f_jB
/-- The read `x = C1.f` is the case at the position: `(x, ., $, 7)`, normal layer. -/
theorem f_eB1 : R3 (.edge 2 wS 1 xT) := DR.step f_eB0 m_rd (by decide)

/-- FORWARD RUN 3 REPORTS THE EXAMPLE IN THE NORMAL LAYER, with no static rule. -/
theorem run3_vuln_normal : R3 (.vuln 2 1 sinkPat false) := DR.vuln f_eB1 m_sink (by decide)

#print axioms run3_vuln_normal

/-- The support of `B`'s initial fact: the exact concrete added facts. -/
theorem run3_sup : RExact.SupM prog counted 2 (Backward.demOf Pb B2run) emitM satI restrictU
    (fun _ _ => False) sinks [0] 2 wS :=
  RExact.SupM.call (RExact.SupM.call (RExact.SupM.root List.mem_cons_self) f_e01 rfl m_cA
      List.mem_cons_self (a := wSF) (by decide) rfl f_jA (.inr ⟨rfl, ⟨T, rfl⟩, rfl⟩))
    f_eA0 rfl m_cB List.mem_cons_self (a := wSF) (by decide) rfl f_jB (.inr ⟨rfl, ⟨T, rfl⟩, rfl⟩)

/-- FORWARD RUN 3 CONFIRMS THE EXAMPLE (`RExact.ConfirmedM`). -/
theorem run3_confirmed : RExact.ConfirmedM prog counted 2 (Backward.demOf Pb B2run) emitM satI
    restrictU (fun _ _ => False) sinks [0] 2 1 sinkPat :=
  ⟨wS, xT, f_eB1, run3_sup, rfl, m_sink, by decide⟩

#print axioms run3_confirmed

/-- Forward run 3 has no request. -/
theorem run3_no_request : ∀ M i t, ¬ R3 (.req M i t) := no_request

end ExampleIter

/-! ### `CexWide` (`caller: t = C.g; C.s = t; K(); r = m(); sink(r)`, `K: C.u = null`,
`m: y = C.s; return y`): calls that return, through the hand-off of backward summaries

Run 1 = `DS CexWide.X2` (`Statics.CexWide.w_vuln_normal`). The backward run enters `m` and `K`
through the reversed bindings back; the reversed summaries of run 1 (`m`: `(S, <C>.s, *) →
(ret, ., *)`, `w_jmA`/`w_emA2`; `K`: `(S, <C>, *) → (S, <C>, */{u}, *)`, `w_jKC`/`w_eKC1`) emit the
backward premises and restrict the backward summaries. The hand-off demands `caller` at
`((S, <C>.g, $, 7), none)`, `K` at `((S, <C>.s, $, 7), some (S, <C>.s, $, 7))` and `m` at
`((S, <C>.s, $, 7), some (ret, ., $, 7))`: exact static patterns at positions. -/

namespace WideIter
open ApSpec.Statics.CexWide

def Pb : Program := Reverse.Program.rev prog

/-- Run 1 (the final design), projected. -/
abbrev R1 : Obj → Prop := projS (DS X2)

/-- Backward run 2: restricted by the reversed summaries of run 1, seeded at `sinks` (the sink run
    1 reported: `w_vuln_normal`), field limit 2, no backward record. -/
abbrev B2run : Obj → Prop :=
  Backward.DB Pb counted 2 (Backward.revSummaryDemand prog R1) emitM satI restrictU
    (fun _ _ => False) [] [0] sinks true

def retTp : PFact := ⟨retB, [], .exact, .conc T⟩
def wsTp : PFact := ⟨S, [C, sA], .exact, .conc T⟩
def yT : AFact := ⟨⟨yB, [], .exact, .conc T⟩, false⟩

theorem hb_cC : (0, 2, Instr.call (Reverse.Call.rev cC), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cC
theorem hb_cm : (1, 4, Instr.call (Reverse.Call.rev cm), 3) ∈ Pb.edges := Reverse.mem_rev_call m_cm
theorem hb_cK : (1, 3, Instr.call (Reverse.Call.rev cK), 2) ∈ Pb.edges := Reverse.mem_rev_call m_cK
theorem hb_wrs : (1, 2, Instr.stmt (Reverse.Stmt.rev wrs), 1) ∈ Pb.edges :=
  Reverse.mem_rev_stmt m_wrs
theorem hb_rdg : (1, 1, Instr.stmt (Reverse.Stmt.rev rdg), 0) ∈ Pb.edges :=
  Reverse.mem_rev_stmt m_rdg
theorem hb_wru : (2, 1, Instr.stmt (Reverse.Stmt.rev wru), 0) ∈ Pb.edges :=
  Reverse.mem_rev_stmt m_wru
theorem hb_rds : (3, 1, Instr.stmt (Reverse.Stmt.rev rds), 0) ∈ Pb.edges :=
  Reverse.mem_rev_stmt m_rds
theorem hb_rt : (3, 2, Instr.stmt (Reverse.Stmt.rev rt), 1) ∈ Pb.edges := Reverse.mem_rev_stmt m_rt

/-- The reversed summary of `m` from run 1: `(D-c = (ret, ., *), D-p = (S, <C>.s, *))`. -/
theorem dem_m : Backward.revSummaryDemand prog R1 3 ⟨pat retB [], some As⟩ :=
  ⟨As, pat retB [], ⟨w_jmA, .inr ⟨⟨pat retB [], false⟩, w_emA2, rfl⟩⟩, rfl⟩
/-- The reversed summary of `K` from run 1: `(D-c = (S, <C>, */{u}), D-p = (S, <C>, *))`. -/
theorem dem_K : Backward.revSummaryDemand prog R1 2 ⟨ACu.fact, some AC⟩ :=
  ⟨AC, ACu.fact, ⟨w_jKC, .inr ⟨ACu, w_eKC1, rfl⟩⟩, rfl⟩

theorem b_e02 : B2run (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root List.mem_cons_self)
theorem b_i1 : B2run (.init 1 zeroFact) :=
  Backward.DB.zin (c := Reverse.Call.rev cC) rfl b_e02 hb_cC
theorem b_e14 : B2run (.edge 1 zeroFact 4 Backward.zeroAF) := Backward.DB.start b_i1
/-- The sink rule: the seed `(r, ., $, 7)`. -/
theorem b_s14 : B2run (.edge 1 zeroFact 4 rT) :=
  Backward.DB.seed (s := sinkPat) List.mem_cons_self b_e14
/-- The requirement enters `m` through the reversed `r = ret`. -/
theorem b_a3 : B2run (.added 3 retTp) :=
  Backward.DB.added (c := Reverse.Call.rev cm) (e := revEdge retE.1 retE.2) (a := retT) b_s14 hb_cm
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
/-- The reversed summary of `m` from run 1 emits the backward premise `(ret, ., $, 7)`. -/
theorem b_j3 : B2run (.init 3 retTp) := Backward.DB.initR b_a3 dem_m (by decide)
theorem b_e32 : B2run (.edge 3 retTp 2 retT) := Backward.DB.start b_j3
theorem b_e31 : B2run (.edge 3 retTp 1 yT) := Backward.DB.step b_e32 hb_rt (by decide)
/-- `m`'s backward summary `(ret, ., $, 7) → (S, <C>.s, $, 7)`. -/
theorem b_e30 : B2run (.edge 3 retTp 0 wsT) := Backward.DB.step b_e31 hb_rds (by decide)
/-- The restricted backward summary of `m` applied in `caller`. -/
theorem b_x13 : B2run (.edge 1 zeroFact 3 wsT) :=
  Backward.DB.ret (c := Reverse.Call.rev cm) (e1 := revEdge retE.1 retE.2) (a := retT) (j := retTp)
    (g := wsT) (d := ⟨pat retB [], some As⟩) (g' := wsT) (r := wsT) (e2 := revEdge bindS.1 bindS.2)
    (r' := wsT) b_s14 hb_cm (List.mem_cons_of_mem _ List.mem_cons_self) (by decide) b_j3 b_e30
    dem_m (by decide) (by decide) (by decide) List.mem_cons_self (by decide)
/-- The requirement enters `K` through the reversed binding `S.* → S.*`. -/
theorem b_a2 : B2run (.added 2 wsTp) :=
  Backward.DB.added (c := Reverse.Call.rev cK) (e := revEdge bindS.1 bindS.2) (a := wsT) b_x13 hb_cK
    List.mem_cons_self (by decide)
theorem b_j2 : B2run (.init 2 wsTp) := Backward.DB.initR b_a2 dem_K (by decide)
theorem b_e21 : B2run (.edge 2 wsTp 1 wsT) := Backward.DB.start b_j2
/-- `C.u = null` reversed keeps `(S, <C>.s, $, 7)`: `K`'s backward summary. -/
theorem b_e20 : B2run (.edge 2 wsTp 0 wsT) := Backward.DB.step b_e21 hb_wru (by decide)
theorem b_x12 : B2run (.edge 1 zeroFact 2 wsT) :=
  Backward.DB.ret (c := Reverse.Call.rev cK) (e1 := revEdge bindS.1 bindS.2) (a := wsT) (j := wsTp)
    (g := wsT) (d := ⟨ACu.fact, some AC⟩) (g' := wsT) (r := wsT) (e2 := revEdge bindS.1 bindS.2)
    (r' := wsT) b_x13 hb_cK List.mem_cons_self (by decide) b_j2 b_e20 dem_K (by decide)
    (by decide) (by decide) List.mem_cons_self (by decide)
/-- `C.s = t` reversed: `(t, ., $, 7)`. -/
theorem b_t11 : B2run (.edge 1 zeroFact 1 tT) := Backward.DB.step b_x12 hb_wrs (by decide)
/-- `t = C.g` reversed: `(S, <C>.g, $, 7)` at `caller`'s forward entry. -/
theorem b_g10 : B2run (.edge 1 zeroFact 0 wgF) := Backward.DB.step b_t11 hb_rdg (by decide)

/-- The hand-off: `caller` gets `((S, <C>.g, $, 7), none)`. -/
theorem dem3_1 : Backward.demOf Pb B2run 1 ⟨wg, none⟩ := .inr (.inl ⟨wgF, b_g10, rfl⟩)
/-- `K` gets its backward summary `((S, <C>.s, $, 7), some (S, <C>.s, $, 7))`. -/
theorem dem3_2 : Backward.demOf Pb B2run 2 ⟨wsTp, some wsTp⟩ :=
  .inr (.inr ⟨wsTp, wsT, b_j2, by decide, b_e20, rfl⟩)
/-- `m` gets its backward summary `((S, <C>.s, $, 7), some (ret, ., $, 7))`. -/
theorem dem3_3 : Backward.demOf Pb B2run 3 ⟨wsTp, some retTp⟩ :=
  .inr (.inr ⟨retTp, wsT, b_j3, by decide, b_e30, rfl⟩)

/-- Forward run 3: the plain `DR` with the hand-off. -/
abbrev R3 : Obj → Prop :=
  DR prog counted 2 (Backward.demOf Pb B2run) emitM satI restrictU (fun _ _ => False) sinks [0]

theorem f_e00 : R3 (.edge 0 zeroFact 0 zfF) := DR.start (DR.root List.mem_cons_self)
theorem f_e01 : R3 (.edge 0 zeroFact 1 wgF) := DR.step f_e00 m_src (by decide)
theorem f_a1 : R3 (.added 1 wg) := DR.added (a := wgF) f_e01 m_cC List.mem_cons_self (by decide)
theorem f_j1 : R3 (.init 1 wg) := DR.initR (d := ⟨wg, none⟩) f_a1 dem3_1 (by decide)
theorem f_e10 : R3 (.edge 1 wg 0 wgF) := DR.start f_j1
/-- `t = C.g` at the position: `(t, ., $, 7)`. -/
theorem f_e11 : R3 (.edge 1 wg 1 tT) := DR.step f_e10 m_rdg (by decide)
/-- `C.s = t`: the exact `(S, <C>.s, $, 7)`. -/
theorem f_e12 : R3 (.edge 1 wg 2 wsT) := DR.step f_e11 m_wrs (by decide)
theorem f_a2 : R3 (.added 2 wsTp) := DR.added (a := wsT) f_e12 m_cK List.mem_cons_self (by decide)
theorem f_j2 : R3 (.init 2 wsTp) := DR.initR (d := ⟨wsTp, some wsTp⟩) f_a2 dem3_2 (by decide)
theorem f_e20 : R3 (.edge 2 wsTp 0 wsT) := DR.start f_j2
/-- `K`'s keep edge `S.<C>.* →_{u} S.<C>.*` keeps `.s` (the case at-or-below): no static rule. -/
theorem f_e21 : R3 (.edge 2 wsTp 1 wsT) := DR.step f_e20 m_wru (by decide)
theorem f_e13 : R3 (.edge 1 wg 3 wsT) :=
  DR.ret (c := cK) (e1 := bindS) (a := wsT) (j := wsTp) (g := wsT) (d := ⟨wsTp, some wsTp⟩)
    (g' := wsT) (r := wsT) (e2 := bindS) (r' := wsT) f_e12 m_cK List.mem_cons_self (by decide) f_j2
    f_e21 dem3_2 (by decide) (by decide) (by decide) List.mem_cons_self (by decide)
theorem f_a3 : R3 (.added 3 wsTp) := DR.added (a := wsT) f_e13 m_cm List.mem_cons_self (by decide)
theorem f_j3 : R3 (.init 3 wsTp) := DR.initR (d := ⟨wsTp, some retTp⟩) f_a3 dem3_3 (by decide)
theorem f_e30 : R3 (.edge 3 wsTp 0 wsT) := DR.start f_j3
/-- `y = C.s` at the position: `(y, ., $, 7)`. -/
theorem f_e31 : R3 (.edge 3 wsTp 1 yT) := DR.step f_e30 m_rds (by decide)
theorem f_e32 : R3 (.edge 3 wsTp 2 retT) := DR.step f_e31 m_rt (by decide)
theorem f_e14 : R3 (.edge 1 wg 4 rT) :=
  DR.ret (c := cm) (e1 := bindS) (a := wsT) (j := wsTp) (g := retT) (d := ⟨wsTp, some retTp⟩)
    (g' := retT) (r := retT) (e2 := retE) (r' := rT) f_e13 m_cm List.mem_cons_self (by decide) f_j3
    f_e32 dem3_3 (by decide) (by decide) (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)

/-- FORWARD RUN 3 REPORTS `CexWide` IN THE NORMAL LAYER, with no static rule. -/
theorem run3_vuln_normal : R3 (.vuln 1 4 sinkPat false) := DR.vuln f_e14 m_sink (by decide)

#print axioms run3_vuln_normal

/-- FORWARD RUN 3 CONFIRMS `CexWide`. -/
theorem run3_confirmed : RExact.ConfirmedM prog counted 2 (Backward.demOf Pb B2run) emitM satI
    restrictU (fun _ _ => False) sinks [0] 1 4 sinkPat :=
  ⟨wg, rT, f_e14,
    RExact.SupM.call (RExact.SupM.root List.mem_cons_self) f_e01 rfl m_cC List.mem_cons_self
      (a := wgF) (by decide) rfl f_j1 (.inr ⟨rfl, ⟨T, rfl⟩, rfl⟩),
    rfl, m_sink, by decide⟩

#print axioms run3_confirmed

theorem run3_no_request : ∀ M i t, ¬ R3 (.req M i t) := no_request

end WideIter

/-! ### `CexAbove` (`caller: C.s = null; r = m(); sink(r)`, `m: y = C.f; return y`) -/

namespace AboveIter
open ApSpec.Statics.CexAbove

def Pb : Program := Reverse.Program.rev prog
abbrev R1 : Obj → Prop := projS (DS X2)
abbrev B2run : Obj → Prop :=
  Backward.DB Pb counted 2 (Backward.revSummaryDemand prog R1) emitM satI restrictU
    (fun _ _ => False) [] [0] sinks true

def retTp : PFact := ⟨retB, [], .exact, .conc T⟩
def retT : AFact := ⟨retTp, false⟩
def rT : AFact := ⟨⟨rB, [], .exact, .conc T⟩, false⟩
def yT : AFact := ⟨⟨yB, [], .exact, .conc T⟩, false⟩

theorem hb_cC : (0, 2, Instr.call (Reverse.Call.rev cC), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cC
theorem hb_cm : (1, 2, Instr.call (Reverse.Call.rev cm), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cm
theorem hb_wr : (1, 1, Instr.stmt (Reverse.Stmt.rev wr), 0) ∈ Pb.edges := Reverse.mem_rev_stmt m_wr
theorem hb_rd : (2, 1, Instr.stmt (Reverse.Stmt.rev rd), 0) ∈ Pb.edges := Reverse.mem_rev_stmt m_rd
theorem hb_rt : (2, 2, Instr.stmt (Reverse.Stmt.rev rt), 1) ∈ Pb.edges := Reverse.mem_rev_stmt m_rt

/-- The reversed summary of `m` from run 1: `(D-c = (ret, ., *), D-p = (S, <C>.f, *))`. -/
theorem dem_m : Backward.revSummaryDemand prog R1 2 ⟨pat retB [], some Ans⟩ :=
  ⟨Ans, pat retB [], ⟨y_jmA, .inr ⟨⟨pat retB [], false⟩, y_emA2, rfl⟩⟩, rfl⟩

theorem b_e02 : B2run (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root List.mem_cons_self)
theorem b_i1 : B2run (.init 1 zeroFact) :=
  Backward.DB.zin (c := Reverse.Call.rev cC) rfl b_e02 hb_cC
theorem b_e12 : B2run (.edge 1 zeroFact 2 Backward.zeroAF) := Backward.DB.start b_i1
theorem b_s12 : B2run (.edge 1 zeroFact 2 rT) :=
  Backward.DB.seed (s := sinkPat) List.mem_cons_self b_e12
theorem b_a2 : B2run (.added 2 retTp) :=
  Backward.DB.added (c := Reverse.Call.rev cm) (e := revEdge retE.1 retE.2) (a := retT) b_s12 hb_cm
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem b_j2 : B2run (.init 2 retTp) := Backward.DB.initR b_a2 dem_m (by decide)
theorem b_e22 : B2run (.edge 2 retTp 2 retT) := Backward.DB.start b_j2
theorem b_e21 : B2run (.edge 2 retTp 1 yT) := Backward.DB.step b_e22 hb_rt (by decide)
/-- `m`'s backward summary `(ret, ., $, 7) → (S, <C>.f, $, 7)`. -/
theorem b_e20 : B2run (.edge 2 retTp 0 wF) := Backward.DB.step b_e21 hb_rd (by decide)
theorem b_x11 : B2run (.edge 1 zeroFact 1 wF) :=
  Backward.DB.ret (c := Reverse.Call.rev cm) (e1 := revEdge retE.1 retE.2) (a := retT) (j := retTp)
    (g := wF) (d := ⟨pat retB [], some Ans⟩) (g' := wF) (r := wF) (e2 := revEdge bindS.1 bindS.2)
    (r' := wF) b_s12 hb_cm (List.mem_cons_of_mem _ List.mem_cons_self) (by decide) b_j2 b_e20
    dem_m (by decide) (by decide) (by decide) List.mem_cons_self (by decide)
/-- `C.s = null` reversed keeps `(S, <C>.f, $, 7)` (its keep edge `S.<C>.* →_{s}` admits `f`). -/
theorem b_x10 : B2run (.edge 1 zeroFact 0 wF) := Backward.DB.step b_x11 hb_wr (by decide)

theorem dem3_1 : Backward.demOf Pb B2run 1 ⟨wS, none⟩ := .inr (.inl ⟨wF, b_x10, rfl⟩)
theorem dem3_2 : Backward.demOf Pb B2run 2 ⟨wS, some retTp⟩ :=
  .inr (.inr ⟨retTp, wF, b_j2, by decide, b_e20, rfl⟩)

abbrev R3 : Obj → Prop :=
  DR prog counted 2 (Backward.demOf Pb B2run) emitM satI restrictU (fun _ _ => False) sinks [0]

theorem f_e00 : R3 (.edge 0 zeroFact 0 zfF) := DR.start (DR.root List.mem_cons_self)
theorem f_e01 : R3 (.edge 0 zeroFact 1 wF) := DR.step f_e00 m_src (by decide)
theorem f_a1 : R3 (.added 1 wS) := DR.added (a := wF) f_e01 m_cC List.mem_cons_self (by decide)
theorem f_j1 : R3 (.init 1 wS) := DR.initR (d := ⟨wS, none⟩) f_a1 dem3_1 (by decide)
theorem f_e10 : R3 (.edge 1 wS 0 wF) := DR.start f_j1
/-- `C.s = null`: the keep edge `S.<C>.* →_{s} S.<C>.*` keeps `(S, <C>.f, $, 7)` (at-or-below). -/
theorem f_e11 : R3 (.edge 1 wS 1 wF) := DR.step f_e10 m_wr (by decide)
theorem f_a2 : R3 (.added 2 wS) := DR.added (a := wF) f_e11 m_cm List.mem_cons_self (by decide)
theorem f_j2 : R3 (.init 2 wS) := DR.initR (d := ⟨wS, some retTp⟩) f_a2 dem3_2 (by decide)
theorem f_e20 : R3 (.edge 2 wS 0 wF) := DR.start f_j2
theorem f_e21 : R3 (.edge 2 wS 1 yT) := DR.step f_e20 m_rd (by decide)
theorem f_e22 : R3 (.edge 2 wS 2 retT) := DR.step f_e21 m_rt (by decide)
theorem f_e12 : R3 (.edge 1 wS 2 rT) :=
  DR.ret (c := cm) (e1 := bindS) (a := wF) (j := wS) (g := retT) (d := ⟨wS, some retTp⟩)
    (g' := retT) (r := retT) (e2 := retE) (r' := rT) f_e11 m_cm List.mem_cons_self (by decide) f_j2
    f_e22 dem3_2 (by decide) (by decide) (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)

/-- FORWARD RUN 3 REPORTS `CexAbove` IN THE NORMAL LAYER, with no static rule. -/
theorem run3_vuln_normal : R3 (.vuln 1 2 sinkPat false) := DR.vuln f_e12 m_sink (by decide)

#print axioms run3_vuln_normal

theorem run3_confirmed : RExact.ConfirmedM prog counted 2 (Backward.demOf Pb B2run) emitM satI
    restrictU (fun _ _ => False) sinks [0] 1 2 sinkPat :=
  ⟨wS, rT, f_e12,
    RExact.SupM.call (RExact.SupM.root List.mem_cons_self) f_e01 rfl m_cC List.mem_cons_self
      (a := wF) (by decide) rfl f_j1 (.inr ⟨rfl, ⟨T, rfl⟩, rfl⟩),
    rfl, m_sink, by decide⟩

#print axioms run3_confirmed

theorem run1_vuln : DS X2 (.vuln 1 2 sinkPat false) := y_vuln_normal

end AboveIter

/-! ### `CexClean` (`caller: K(); r = m(); sink(r)`, `K: clean_7(C.u)`, `m: y = C.s; return y`) -/

namespace CleanIter
open ApSpec.Statics.CexClean

def Pb : Program := Reverse.Program.rev prog
abbrev R1 : Obj → Prop := projS (DS Xd)
abbrev B2run : Obj → Prop :=
  Backward.DB Pb counted 2 (Backward.revSummaryDemand prog R1) emitM satI restrictU
    (fun _ _ => False) [] [0] sinks true

def retTp : PFact := ⟨retB, [], .exact, .conc T⟩
def yT : AFact := ⟨⟨yB, [], .exact, .conc T⟩, false⟩

theorem hb_cC : (0, 2, Instr.call (Reverse.Call.rev cC), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cC
theorem hb_cK : (1, 1, Instr.call (Reverse.Call.rev cK), 0) ∈ Pb.edges := Reverse.mem_rev_call m_cK
theorem hb_cm : (1, 2, Instr.call (Reverse.Call.rev cm), 1) ∈ Pb.edges := Reverse.mem_rev_call m_cm
theorem hb_clU : (2, 1, Instr.clean clU, 0) ∈ Pb.edges := Reverse.mem_rev_clean m_clU
theorem hb_rd : (3, 1, Instr.stmt (Reverse.Stmt.rev rd), 0) ∈ Pb.edges := Reverse.mem_rev_stmt m_rd
theorem hb_rt : (3, 2, Instr.stmt (Reverse.Stmt.rev rt), 1) ∈ Pb.edges := Reverse.mem_rev_stmt m_rt

/-- The reversed summary of `m` from run 1. -/
theorem dem_m : Backward.revSummaryDemand prog R1 3 ⟨pat retB [], some As⟩ :=
  ⟨As, pat retB [], ⟨x_jMA, .inr ⟨retF, x_eMA2, rfl⟩⟩, rfl⟩
/-- The reversed summary of `K` from run 1 (the deep answer `(S, <C>.s, $, 7)`). -/
theorem dem_K : Backward.revSummaryDemand prog R1 2 ⟨ws, some ws⟩ :=
  ⟨ws, ws, ⟨x_jKw, .inr ⟨wsF, x_eKw1, rfl⟩⟩, rfl⟩

theorem b_e02 : B2run (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root List.mem_cons_self)
theorem b_i1 : B2run (.init 1 zeroFact) :=
  Backward.DB.zin (c := Reverse.Call.rev cC) rfl b_e02 hb_cC
theorem b_e12 : B2run (.edge 1 zeroFact 2 Backward.zeroAF) := Backward.DB.start b_i1
theorem b_s12 : B2run (.edge 1 zeroFact 2 rT) :=
  Backward.DB.seed (s := sinkPat) List.mem_cons_self b_e12
theorem b_a3 : B2run (.added 3 retTp) :=
  Backward.DB.added (c := Reverse.Call.rev cm) (e := revEdge retE.1 retE.2) (a := retT) b_s12 hb_cm
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem b_j3 : B2run (.init 3 retTp) := Backward.DB.initR b_a3 dem_m (by decide)
theorem b_e32 : B2run (.edge 3 retTp 2 retT) := Backward.DB.start b_j3
theorem b_e31 : B2run (.edge 3 retTp 1 yT) := Backward.DB.step b_e32 hb_rt (by decide)
theorem b_e30 : B2run (.edge 3 retTp 0 wsF) := Backward.DB.step b_e31 hb_rd (by decide)
theorem b_x11 : B2run (.edge 1 zeroFact 1 wsF) :=
  Backward.DB.ret (c := Reverse.Call.rev cm) (e1 := revEdge retE.1 retE.2) (a := retT) (j := retTp)
    (g := wsF) (d := ⟨pat retB [], some As⟩) (g' := wsF) (r := wsF)
    (e2 := revEdge bindS.1 bindS.2) (r' := wsF) b_s12 hb_cm
    (List.mem_cons_of_mem _ List.mem_cons_self) (by decide) b_j3 b_e30 dem_m (by decide)
    (by decide) (by decide) List.mem_cons_self (by decide)
theorem b_a2 : B2run (.added 2 ws) :=
  Backward.DB.added (c := Reverse.Call.rev cK) (e := revEdge bindS.1 bindS.2) (a := wsF) b_x11 hb_cK
    List.mem_cons_self (by decide)
theorem b_j2 : B2run (.init 2 ws) := Backward.DB.initR b_a2 dem_K (by decide)
theorem b_e21 : B2run (.edge 2 ws 1 wsF) := Backward.DB.start b_j2
/-- The cleaner at `S.<C>.u` is apart from `S.<C>.s`: `K`'s backward summary keeps it. -/
theorem b_e20 : B2run (.edge 2 ws 0 wsF) := Backward.DB.clean b_e21 hb_clU (by decide)
theorem b_x10 : B2run (.edge 1 zeroFact 0 wsF) :=
  Backward.DB.ret (c := Reverse.Call.rev cK) (e1 := revEdge bindS.1 bindS.2) (a := wsF) (j := ws)
    (g := wsF) (d := ⟨ws, some ws⟩) (g' := wsF) (r := wsF) (e2 := revEdge bindS.1 bindS.2)
    (r' := wsF) b_x11 hb_cK List.mem_cons_self (by decide) b_j2 b_e20 dem_K (by decide)
    (by decide) (by decide) List.mem_cons_self (by decide)

theorem dem3_1 : Backward.demOf Pb B2run 1 ⟨ws, none⟩ := .inr (.inl ⟨wsF, b_x10, rfl⟩)
theorem dem3_2 : Backward.demOf Pb B2run 2 ⟨ws, some ws⟩ :=
  .inr (.inr ⟨ws, wsF, b_j2, by decide, b_e20, rfl⟩)
theorem dem3_3 : Backward.demOf Pb B2run 3 ⟨ws, some retTp⟩ :=
  .inr (.inr ⟨retTp, wsF, b_j3, by decide, b_e30, rfl⟩)

abbrev R3 : Obj → Prop :=
  DR prog counted 2 (Backward.demOf Pb B2run) emitM satI restrictU (fun _ _ => False) sinks [0]

theorem f_e00 : R3 (.edge 0 zeroFact 0 zfF) := DR.start (DR.root List.mem_cons_self)
theorem f_e01 : R3 (.edge 0 zeroFact 1 wsF) := DR.step f_e00 m_src (by decide)
theorem f_a1 : R3 (.added 1 ws) := DR.added (a := wsF) f_e01 m_cC List.mem_cons_self (by decide)
theorem f_j1 : R3 (.init 1 ws) := DR.initR (d := ⟨ws, none⟩) f_a1 dem3_1 (by decide)
theorem f_e10 : R3 (.edge 1 ws 0 wsF) := DR.start f_j1
theorem f_a2 : R3 (.added 2 ws) := DR.added (a := wsF) f_e10 m_cK List.mem_cons_self (by decide)
theorem f_j2 : R3 (.init 2 ws) := DR.initR (d := ⟨ws, some ws⟩) f_a2 dem3_2 (by decide)
theorem f_e20 : R3 (.edge 2 ws 0 wsF) := DR.start f_j2
/-- The cleaner at `S.<C>.u` on the exact `(S, <C>.s, $, 7)`: disjoint, no request. -/
theorem f_e21 : R3 (.edge 2 ws 1 wsF) := DR.clean f_e20 m_clU (by decide)
theorem f_e11 : R3 (.edge 1 ws 1 wsF) :=
  DR.ret (c := cK) (e1 := bindS) (a := wsF) (j := ws) (g := wsF) (d := ⟨ws, some ws⟩)
    (g' := wsF) (r := wsF) (e2 := bindS) (r' := wsF) f_e10 m_cK List.mem_cons_self (by decide) f_j2
    f_e21 dem3_2 (by decide) (by decide) (by decide) List.mem_cons_self (by decide)
theorem f_a3 : R3 (.added 3 ws) := DR.added (a := wsF) f_e11 m_cm List.mem_cons_self (by decide)
theorem f_j3 : R3 (.init 3 ws) := DR.initR (d := ⟨ws, some retTp⟩) f_a3 dem3_3 (by decide)
theorem f_e30 : R3 (.edge 3 ws 0 wsF) := DR.start f_j3
theorem f_e31 : R3 (.edge 3 ws 1 yT) := DR.step f_e30 m_rd (by decide)
theorem f_e32 : R3 (.edge 3 ws 2 retT) := DR.step f_e31 m_rt (by decide)
theorem f_e12 : R3 (.edge 1 ws 2 rT) :=
  DR.ret (c := cm) (e1 := bindS) (a := wsF) (j := ws) (g := retT) (d := ⟨ws, some retTp⟩)
    (g' := retT) (r := retT) (e2 := retE) (r' := rT) f_e11 m_cm List.mem_cons_self (by decide) f_j3
    f_e32 dem3_3 (by decide) (by decide) (by decide) (List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide)

/-- FORWARD RUN 3 REPORTS `CexClean` IN THE NORMAL LAYER, with no static rule and no request
    (run 1 needed the cleaner's mark request and the deep answer; run 3 needs neither). -/
theorem run3_vuln_normal : R3 (.vuln 1 2 sinkPat false) := DR.vuln f_e12 m_sink (by decide)

#print axioms run3_vuln_normal

theorem run3_confirmed : RExact.ConfirmedM prog counted 2 (Backward.demOf Pb B2run) emitM satI
    restrictU (fun _ _ => False) sinks [0] 1 2 sinkPat :=
  ⟨ws, rT, f_e12,
    RExact.SupM.call (RExact.SupM.root List.mem_cons_self) f_e01 rfl m_cC List.mem_cons_self
      (a := wsF) (by decide) rfl f_j1 (.inr ⟨rfl, ⟨T, rfl⟩, rfl⟩),
    rfl, m_sink, by decide⟩

#print axioms run3_confirmed

theorem run1_vuln : DS Xd (.vuln 1 2 sinkPat false) := deep_vuln_normal

end CleanIter

/-! ### The general theorems on `CexWide`: every hypothesis holds

`CexWide` (four methods, calls that bind `S` back and a return) satisfies the hypotheses of the
iteration from `DS` (`iteration_general_DS`) and of the restricted-run invariant
(`no_static_rule_after_run1`, for every field limit ≥ 1): the iteration reports the vulnerability in
every run (`wide_iteration`), and no run after run 1 has a static `*`/`[any]` fact above a position
or a request (`wide_no_static_rule`). -/

/-- A boolean check of `Reverse.MarkRev`. -/
def markRevB (e : MicroEdge) : Bool :=
  match e.2.mark, e.1.mark with
  | .star, _ => true
  | .starEx _, _ => true
  | _, .conc _ => true
  | _, _ => false

theorem markRevB_sound {e : MicroEdge} (h : markRevB e = true) : Reverse.MarkRev e.1 e.2 := by
  unfold markRevB at h
  unfold Reverse.MarkRev
  cases h2 : e.2.mark with
  | star => exact .inl (.inl rfl)
  | starEx x => exact .inl (.inr ⟨x, rfl⟩)
  | conc t =>
    rw [h2] at h
    cases h1 : e.1.mark with
    | conc t' => exact .inr ⟨t', rfl⟩
    | star => rw [h1] at h; cases h
    | starEx _ => rw [h1] at h; cases h

namespace WideIter
open ApSpec.Statics.CexWide

theorem wide_bindStar : Reverse.BindTargetsStar prog := by
  intro M n c n' hE
  rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
    ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> decide

theorem wide_markRev : Backward.StmtsMarkRev prog := by
  intro M n s n' hE e he
  apply markRevB_sound
  revert e
  rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
    ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> decide

theorem wide_noZeroBack : Backward.NoZeroBack prog := by
  intro M n c n' hE
  rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
    ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> decide

theorem wide_zeroKept : Backward.ZeroKept prog where
  stmt := by
    intro M n s n' hE
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h <;> decide
  clean := by
    intro M n cl n' hE
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
  filt := by
    intro M n b may n' hE
    rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h

/-- From every node of a method of `CexWide`, the exit is reached. -/
theorem wide_toExit {M n : Nat} (hM : M = 0 ∨ M = 1 ∨ M = 2 ∨ M = 3)
    (hp : Backward.CfgPath prog M 0 n) : Backward.CfgPath prog M n (prog.exit M) := by
  -- the nodes reachable in each method
  have hn : (M = 0 ∧ (n = 0 ∨ n = 1 ∨ n = 2)) ∨ (M = 1 ∧ (n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4)) ∨
      (M = 2 ∧ (n = 0 ∨ n = 1)) ∨ (M = 3 ∧ (n = 0 ∨ n = 1 ∨ n = 2)) := by
    induction hp with
    | refl =>
      rcases hM with rfl | rfl | rfl | rfl
      · exact .inl ⟨rfl, .inl rfl⟩
      · exact .inr (.inl ⟨rfl, .inl rfl⟩)
      · exact .inr (.inr (.inl ⟨rfl, .inl rfl⟩))
      · exact .inr (.inr (.inr ⟨rfl, .inl rfl⟩))
    | step _ he _ =>
      rcases edgesW he with ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ |
        ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩ |
        ⟨rfl, -, -, rfl⟩ | ⟨rfl, -, -, rfl⟩
      · exact .inl ⟨rfl, .inr (.inl rfl)⟩
      · exact .inl ⟨rfl, .inr (.inr rfl)⟩
      · exact .inr (.inl ⟨rfl, .inr (.inl rfl)⟩)
      · exact .inr (.inl ⟨rfl, .inr (.inr (.inl rfl))⟩)
      · exact .inr (.inl ⟨rfl, .inr (.inr (.inr (.inl rfl)))⟩)
      · exact .inr (.inl ⟨rfl, .inr (.inr (.inr (.inr rfl)))⟩)
      · exact .inr (.inr (.inl ⟨rfl, .inr rfl⟩))
      · exact .inr (.inr (.inr ⟨rfl, .inr (.inl rfl)⟩))
      · exact .inr (.inr (.inr ⟨rfl, .inr (.inr rfl)⟩))
  have st : ∀ {M a b : Nat} {ins : Instr}, (M, a, ins, b) ∈ prog.edges →
      Backward.CfgPath prog M b (prog.exit M) → Backward.CfgPath prog M a (prog.exit M) := by
    intro M a b ins he hp
    -- prepend an edge to a path
    have key : ∀ c, Backward.CfgPath prog M b c → Backward.CfgPath prog M a c := by
      intro c hbc
      induction hbc with
      | refl => exact Backward.CfgPath.step Backward.CfgPath.refl he
      | step _ he' ih => exact Backward.CfgPath.step ih he'
    exact key _ hp
  have e0 : Backward.CfgPath prog 0 2 (prog.exit 0) := Backward.CfgPath.refl
  have e1 : Backward.CfgPath prog 1 4 (prog.exit 1) := Backward.CfgPath.refl
  have e2 : Backward.CfgPath prog 2 1 (prog.exit 2) := Backward.CfgPath.refl
  have e3 : Backward.CfgPath prog 3 2 (prog.exit 3) := Backward.CfgPath.refl
  rcases hn with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩
  · exact st m_src (st m_cC e0)
  · exact st m_cC e0
  · exact e0
  · exact st m_rdg (st m_wrs (st m_cK (st m_cm e1)))
  · exact st m_wrs (st m_cK (st m_cm e1))
  · exact st m_cK (st m_cm e1)
  · exact st m_cm e1
  · exact e1
  · exact st m_wru e2
  · exact e2
  · exact st m_rds (st m_rt e3)
  · exact st m_rt e3
  · exact e3

theorem wide_exitReach : Backward.ExitReach prog [0] := by
  intro M n hM hp
  apply wide_toExit _ hp
  rcases hM with h | ⟨M', n0, c, n1, hE, rfl⟩
  · cases h with
    | head => exact .inl rfl
    | tail _ h => cases h
  · rcases edgesW hE with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ |
      ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> cases h
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))

#print axioms wide_exitReach

theorem wide_sinkKinds : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any := by
  intro M n s hs
  cases hs with
  | head => exact .inl rfl
  | tail _ h => cases h

/-- THE ITERATION FROM `DS` ON `CexWide`: every hypothesis of `iteration_general_DS` is discharged;
    every forward run reports the vulnerability. -/
theorem wide_iteration {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand prog (runSeqS X2 Ls dem recs k) m d → demB k m d)
    (hseeds : ∀ k M n s b, runSeqS X2 Ls dem recs k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf Pb (Backward.DB Pb counted (LB k) (demB k) emitM satI restrictU
      (recsB k) [] [0] (seeds k) true) m d → dem k m d) :
    ∀ k, ∃ b, runSeqS X2 Ls dem recs k (.vuln 1 4 sinkPat b) :=
  iteration_general_DS wide_swf ⟨rfl, rfl, rfl, rfl, rfl⟩ wf wide_bindStar wide_markRev
    wide_noZeroBack wide_zeroKept wide_exitReach wide_sinkKinds LB demB recsB seeds hdemB hseeds
    hdem wide_reach m_sink rfl wide_covers

#print axioms wide_iteration

/-- NO STATIC RULE AFTER RUN 1 ON `CexWide`, for every field limit ≥ 1 of the later runs. -/
theorem wide_no_static_rule {Ls : Nat → Nat} {dem : Nat → MethodId → DemandEdge → Prop}
    {recs : Nat → MethodId → PFact × AFact → Prop} (hL : ∀ k, 1 ≤ Ls (k + 1))
    (hrecs : ∀ k m j g, recs k m (j, g) → RecOK X2 j g) (k : Nat) :
    (∀ o, runSeqS X2 Ls dem recs (k + 1) o → RInv X2 o) ∧
    (∀ M i t, ¬ runSeqS X2 Ls dem recs (k + 1) (.req M i t)) := by
  refine no_static_rule_after_run1 wide_swf (fun k q r hc hab => ?_) hrecs k
  have h2 := cutPath_count hc
  rcases abovePos_cases hab with rfl | rfl
  · exact absurd h2 (by have := hL k; intro h; rw [← h] at this; exact absurd this (by decide))
  · exact absurd h2 (by have := hL k; intro h; rw [← h] at this; exact absurd this (by decide))

#print axioms wide_no_static_rule

end WideIter

end ApSpec.StaticsIter
