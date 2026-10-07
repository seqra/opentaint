/-
  ApSpec.W6 — rule W6 for the WHOLE RUN: "a conclusion with the `[any]` tail is in the demand
  layer" (spec §2.3, §11.2).

  The closures `D` and `DR` do not apply W6: `applyEdge` can give an `[any]` result in the normal
  layer. `Invariant.demand_of_any_ok` proves the per-fact statement. This file defines the runs
  WITH W6 and proves that they differ from the runs without it only by raised layers.

  The W6 runs. `w6 f = if f.fact.kind.isAny then ⟨f.fact, true⟩ else f` (it is
  `Invariant.normA`). `D6` (`DR6`) has the rules of `D` (`DR`), and the result of every AP
  operation passes through `w6`: the start fact, every `applyEdge` (a statement micro edge, the
  binding into the callee before the summary application, the binding back), the summary
  application, the field limit and the cleaner. (`w6` commutes with the field limit,
  `w6_limitF`, so `w6` after `transfer` is `w6` after each `applyEdge` of the statement.)

  The relation. `LE f g`: `g = f`, or `f` is not `*` and `g = ⟨f.fact, true⟩`. So `g` has the fact
  of `f` and the same or a raised layer, and a `*` fact keeps its layer. `Up R o` /
  `Down R o`: an object of `R` with the same initial fact, node and fact, in a higher / lower
  layer (initial facts, added facts and requests: the same object).

  What reads the layer. The abstraction (`α`, `policy`, `emit`), `answerInit`, `startFact`,
  `sat`, `applicable`, `check`, `climbsB`, `overlapB`, the requests (`applyEdge_LL`,
  `cleanRes_LL`) read only facts. `applyEdge`, `cleanRes`, `limitF` copy or raise it
  (`applyEdge_LL`, `cleanRes_LL`, `limitF_LE`). Two places read it:
    * the normal form `AFact.norm` (W2) turns a `*` result in the demand layer into `[any]` or `$`.
      In `applyEdge` a `*` result needs a `*` input, whose layer `LE` never raises;
    * `applySummary` ORs the layer of the summary edge into the result, BEFORE the normal form.
      A raised non-`*` summary edge changes a `*` result: a `$`-premise summary on a `*/Universe`
      caller fact (`Invariant.summary_layer_changes_univ`). That is a change of the FACT, not of
      the layer. The hypothesis `SummaryStar` excludes it; it holds if every `$` initial fact
      has a concrete mark (`ExactInitConc`: the policy, the restricted runs of the spec) or under
      the hypotheses of `Invariant.no_univ_star`. Without it the statement is FALSE
      (`Cex.cex_w6_changes_fact`, a well-formed program).
    * The restriction of a restricted run reads the layer only to copy it (`RestrictLE`, proved
      for `restrictU` and `restrictS`).

  Main results:
    * `D_le_D6`, `D6_le_D`: the simulation both ways (under `SummaryStar`), and `DR_le_DR6`,
      `DR6_le_DR` (under `ExactInitConc` and `RestrictLE`). `D6_same_shape`, `DR6_same_shape`:
      the same initial facts, added facts, requests, edge facts and reported sinks;
    * `D6_w6`, `DR6_w6`: W6 holds in the W6 runs; `complete_iff_of_w6`: with W6, `complete` is
      the normal layer;
    * soundness: `coverage6`, `vuln_found6`, `vuln_found_policy6`, `coverageR6`,
      `vuln_foundR6`, `vuln_found_M6`, and the iteration with W6 in every forward run:
      `iteration_sound_conc6`, `iteration_sound_M6`, `iteration_sound_M6_identity`,
      `iteration_general6` (the backward run `Backward.DB` stays without W6);
    * exactness: `D6_normal`, `edge_exact6`, `edge_exact_valid6`, `DR6_normal`, `edge_exactR6`,
      `edge_exactR_valid6`;
    * confirmation: `confirmed_of_confirmed6`, `confirmed_real6`, `confirmed_real_valid6`,
      `confirmedM_of_confirmedM6`, `confirmed_real_M6`, `confirmed_real_M6_valid`;
    * the summaries and the demand they pass on are the same with and without W6
      (`summaryDemand_iff`, `revSummaryDemand_iff`);
    * the hypothesis is necessary (`Cex.cex_w6_changes_fact`); W6 can remove a record
      (`Cex.cex_record_lost`): the normal edges of `D6` are a SUBSET of those of `D`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.Basic
import ApSpec.Core
import ApSpec.Invariant
import ApSpec.Coverage
import ApSpec.Exact
import ApSpec.Confirmed
import ApSpec.Restricted
import ApSpec.RestrictedCore
import ApSpec.RestrictedCoverage
import ApSpec.RestrictedExact
import ApSpec.RestrictedMain
import ApSpec.Backward

namespace ApSpec.W6
open ApSpec

/-! ## 1. W6 on one fact, and the layer relation -/

/-- W6 on one fact: an `[any]` fact goes to the demand layer. -/
def w6 (f : AFact) : AFact := if f.fact.kind.isAny then ⟨f.fact, true⟩ else f

/-- `w6` is the `normA` of `Invariant`. -/
theorem w6_eq_normA : w6 = Invariant.normA := rfl

/-- `w6` in the form `if f.fact.kind = .any then ⟨f.fact, true⟩ else f`. -/
theorem w6_spec (f : AFact) : w6 f = if f.fact.kind = .any then ⟨f.fact, true⟩ else f := by
  unfold w6
  cases h : f.fact.kind with
  | star e => rfl
  | any => rfl
  | exact => rfl

theorem w6_fact (f : AFact) : (w6 f).fact = f.fact := (Invariant.demand_of_any_ok f).1

/-- W6 holds on the result of `w6`. -/
theorem w6_ok (f : AFact) (h : (w6 f).fact.kind.isAny = true) : (w6 f).demand = true := by
  rw [w6_fact] at h
  unfold w6
  rw [if_pos h]

/-- `w6` commutes with the field limit. -/
theorem w6_limitF (counted : Acc → Bool) (L : Nat) (f : AFact) :
    w6 (limitF counted L f) = limitF counted L (w6 f) := by
  unfold limitF
  rw [w6_fact]
  cases cutPath counted L f.fact.path with
  | none => rfl
  | some p => rfl

/-- `LE f g`: `g` has the fact of `f`, in the same or a raised layer; a `*` fact keeps its
    layer. -/
def LE (f g : AFact) : Prop := g = f ∨ (f.fact.kind.isStar = false ∧ g = ⟨f.fact, true⟩)

theorem LE.refl (f : AFact) : LE f f := Or.inl rfl

theorem LE.fact {f g : AFact} (h : LE f g) : f.fact = g.fact := by
  rcases h with rfl | ⟨_, rfl⟩ <;> rfl

theorem LE.dem {f g : AFact} (h : LE f g) : f.demand = true → g.demand = true := by
  rcases h with rfl | ⟨_, rfl⟩
  · exact id
  · exact fun _ => rfl

theorem LE.star_eq {f g : AFact} (h : LE f g) (hs : f.fact.kind.isStar = true) : g = f := by
  rcases h with e | ⟨hn, _⟩
  · exact e
  · rw [hn] at hs; cases hs

/-- A normal-layer upper fact has the same lower fact. -/
theorem LE.eq_of_normal {f g : AFact} (h : LE f g) (hg : g.demand = false) : g = f := by
  rcases h with e | ⟨_, rfl⟩
  · exact e
  · cases hg

theorem LE.of_nonstar {f g : AFact} (hf : f.fact = g.fact) (hns : f.fact.kind.isStar = false)
    (hd : f.demand = true → g.demand = true) : LE f g := by
  obtain ⟨ff, fd⟩ := f
  obtain ⟨gf, gd⟩ := g
  have e : ff = gf := hf
  subst e
  cases gd with
  | true => exact Or.inr ⟨hns, rfl⟩
  | false =>
    cases fd with
    | false => exact Or.inl rfl
    | true => exact absurd (hd rfl) Bool.false_ne_true

theorem LE.raise {f : AFact} (hns : f.fact.kind.isStar = false) : LE f ⟨f.fact, true⟩ :=
  Or.inr ⟨hns, rfl⟩

/-- `w6` only raises: `LE` is closed under `w6` on the upper side. -/
theorem LE_w6 {f g : AFact} (h : LE f g) : LE f (w6 g) := by
  rcases Invariant.normA_cases g with e | ⟨ha, e⟩
  · show LE f (Invariant.normA g)
    rw [e]; exact h
  · show LE f (Invariant.normA g)
    rw [e]
    have hf := h.fact
    have hns : f.fact.kind.isStar = false := by
      rw [hf]
      cases hk : g.fact.kind with
      | star e0 => rw [hk] at ha; cases ha
      | any => rfl
      | exact => rfl
    exact LE.of_nonstar hf hns (fun _ => rfl)

theorem LE_w6_self (f : AFact) : LE f (w6 f) := LE_w6 (LE.refl f)

theorem bor_mono {a b c d : Bool} (h1 : a = true → c = true) (h2 : b = true → d = true) :
    (a || b) = true → (c || d) = true := by
  intro h
  cases a with
  | true => rw [h1 rfl]; rfl
  | false =>
    cases b with
    | true => rw [h2 rfl]; cases c <;> rfl
    | false => exact absurd h Bool.false_ne_true

/-! ## 2. Lists of results -/

/-- Two result lists, element by element in `LE`. -/
inductive LL : List AFact → List AFact → Prop where
  | nil : LL [] []
  | cons {x y : AFact} {xs ys : List AFact} : LE x y → LL xs ys → LL (x :: xs) (y :: ys)

theorem LL.refl : ∀ (xs : List AFact), LL xs xs
  | [] => LL.nil
  | x :: xs => LL.cons (LE.refl x) (LL.refl xs)

theorem LL.append {xs ys xs' ys' : List AFact} (h : LL xs ys) (h' : LL xs' ys') :
    LL (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | cons hxy _ ih => exact LL.cons hxy ih

theorem LL.fwd {xs ys : List AFact} (h : LL xs ys) {x : AFact} (hx : x ∈ xs) :
    ∃ y, y ∈ ys ∧ LE x y := by
  induction h with
  | nil => exact absurd hx List.not_mem_nil
  | @cons x0 y0 xs0 ys0 hxy _ ih =>
    rcases List.mem_cons.mp hx with e | hx'
    · subst e; exact ⟨y0, List.mem_cons_self .., hxy⟩
    · obtain ⟨y, hy, hle⟩ := ih hx'
      exact ⟨y, List.mem_cons_of_mem _ hy, hle⟩

theorem LL.bwd {xs ys : List AFact} (h : LL xs ys) {y : AFact} (hy : y ∈ ys) :
    ∃ x, x ∈ xs ∧ LE x y := by
  induction h with
  | nil => exact absurd hy List.not_mem_nil
  | @cons x0 y0 xs0 ys0 hxy _ ih =>
    rcases List.mem_cons.mp hy with e | hy'
    · subst e; exact ⟨x0, List.mem_cons_self .., hxy⟩
    · obtain ⟨x, hx, hle⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hle⟩

theorem LL.map {xs ys : List AFact} (h : LL xs ys) {F G : AFact → AFact}
    (hFG : ∀ x y, x ∈ xs → LE x y → LE (F x) (G y)) : LL (xs.map F) (ys.map G) := by
  induction h with
  | nil => exact LL.nil
  | @cons x y xs0 ys0 hxy _ ih =>
    exact LL.cons (hFG x y (List.mem_cons_self ..) hxy)
      (ih (fun x' y' hx' h' => hFG x' y' (List.mem_cons_of_mem _ hx') h'))

/-- The layer of a non-`*` list is a tag. -/
theorem LL.tag {d d' : Bool} (hd : d = true → d' = true) :
    ∀ (xs : List AFact), (∀ x, x ∈ xs → x.fact.kind.isStar = false) →
      LL (xs.map (fun x => (⟨x.fact, d || x.demand⟩ : AFact)))
        (xs.map (fun x => (⟨x.fact, d' || x.demand⟩ : AFact)))
  | [], _ => LL.nil
  | x :: xs, h =>
    LL.cons (LE.of_nonstar rfl (h x (List.mem_cons_self ..)) (bor_mono hd id))
      (LL.tag hd xs (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-! ## 3. The operations under `LE` -/

/-- The requests of `applyEdge` do not read the layer. -/
theorem applyEdge_reqs_layer (cf fr to : PFact) (d d' : Bool) :
    (applyEdge ⟨cf, d⟩ fr to).reqs = (applyEdge ⟨cf, d'⟩ fr to).reqs := by
  rw [CoreAux.applyEdge_eq, CoreAux.applyEdge_eq]
  show (if Nat.beq cf.base fr.base = true then
      CoreAux.fin ⟨cf, d⟩ fr to (CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind)
      else Res.none).reqs =
    (if Nat.beq cf.base fr.base = true then
      CoreAux.fin ⟨cf, d'⟩ fr to (CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind)
      else Res.none).reqs
  cases Nat.beq cf.base fr.base with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl]
    cases CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind with
    | none => rfl
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      show (CoreAux.finG ⟨cf, d⟩ to p k ap (markGate fr.mark cf.mark)).reqs =
        (CoreAux.finG ⟨cf, d'⟩ to p k ap (markGate fr.mark cf.mark)).reqs
      cases markGate fr.mark cf.mark with
      | no => rfl
      | req t => rfl
      | ok =>
        show (CoreAux.finM ⟨cf, d⟩ to p k ap (markComp to.mark cf.mark)).reqs =
          (CoreAux.finM ⟨cf, d'⟩ to p k ap (markComp to.mark cf.mark)).reqs
        cases markComp to.mark cf.mark <;> rfl

/-- `applyEdge` under `LE`: the results are in `LE`, the requests are the same. -/
theorem applyEdge_LL {c c' : AFact} {fr to : PFact} (h : LE c c') :
    LL (applyEdge c fr to).facts (applyEdge c' fr to).facts ∧
    (applyEdge c fr to).reqs = (applyEdge c' fr to).reqs := by
  obtain ⟨cf, d⟩ := c
  rcases h with rfl | ⟨hns, rfl⟩
  · exact ⟨LL.refl _, rfl⟩
  · have hns' : cf.kind.isStar = false := hns
    refine ⟨?_, applyEdge_reqs_layer cf fr to d true⟩
    show LL (applyEdge ⟨cf, d⟩ fr to).facts (applyEdge ⟨cf, true⟩ fr to).facts
    rw [Invariant.applyEdge_tag (d := d) hns', Invariant.applyEdge_tag (d := true) hns']
    exact LL.tag (fun _ => rfl) _ (fun x hx => Confirmed.applyEdge_nonstar hns' hx)

theorem applyAll_LL {c c' : AFact} (h : LE c c') :
    ∀ (es : List MicroEdge), LL (applyAll c es).facts (applyAll c' es).facts ∧
      (applyAll c es).reqs = (applyAll c' es).reqs
  | [] => ⟨LL.nil, rfl⟩
  | e :: es => by
    obtain ⟨h1, h2⟩ := applyEdge_LL (fr := e.1) (to := e.2) h
    obtain ⟨h3, h4⟩ := applyAll_LL h es
    refine ⟨LL.append h1 h3, ?_⟩
    show (applyEdge c e.1 e.2).reqs ++ (applyAll c es).reqs =
      (applyEdge c' e.1 e.2).reqs ++ (applyAll c' es).reqs
    rw [h2, h4]

theorem limitF_LE {counted : Acc → Bool} {L : Nat} {f g : AFact} (h : LE f g) :
    LE (limitF counted L f) (limitF counted L g) := by
  have hf : g.fact = f.fact := h.fact.symm
  unfold limitF
  rw [hf]
  cases cutPath counted L f.fact.path with
  | none => exact h
  | some p => exact LE.refl _

/-- The statement transfer under `LE`. -/
theorem transfer_LL {counted : Acc → Bool} {L : Nat} {s : Stmt} {c c' : AFact} (h : LE c c') :
    LL (transfer counted L s c).facts (transfer counted L s c').facts ∧
    (transfer counted L s c).reqs = (transfer counted L s c').reqs := by
  have hf : c'.fact = c.fact := h.fact.symm
  unfold transfer
  rw [hf]
  cases memB c.fact.base s.touched with
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    exact ⟨LL.cons h LL.nil, rfl⟩
  | true =>
    rw [if_pos rfl, if_pos rfl]
    obtain ⟨h1, h2⟩ := applyAll_LL h s.edges
    exact ⟨h1.map (fun _ _ _ hxy => limitF_LE hxy), h2⟩

/-- The summary application under `LE`. The layer of the summary edge is read before the
    normal form, so a `*` result needs the same summary edge on both sides (`hX`). -/
theorem applySummary_LL {a a' g g' : AFact} {j : PFact} (ha : LE a a') (hg : LE g g')
    (hX : ∀ x, x ∈ (applyEdge a j g.fact).facts → x.fact.kind.isStar = true → g' = g) :
    LL (applySummary a j g).facts (applySummary a' j g').facts := by
  have hgf : g'.fact = g.fact := hg.fact.symm
  show LL ((applyEdge a j g.fact).facts.map (fun x => AFact.norm ⟨x.fact, x.demand || g.demand⟩))
    ((applyEdge a' j g'.fact).facts.map (fun x => AFact.norm ⟨x.fact, x.demand || g'.demand⟩))
  rw [hgf]
  refine LL.map (applyEdge_LL ha).1 (fun x y hx hxy => ?_)
  cases hs : x.fact.kind.isStar with
  | true =>
    have e1 : y = x := hxy.star_eq hs
    have e2 : g' = g := hX x hx hs
    rw [e1, e2]
    exact LE.refl _
  | false =>
    have hys : y.fact.kind.isStar = false := by rw [← hxy.fact]; exact hs
    show LE (AFact.norm ⟨x.fact, x.demand || g.demand⟩) (AFact.norm ⟨y.fact, y.demand || g'.demand⟩)
    rw [Invariant.norm_id_of_nonstar (x := ⟨x.fact, x.demand || g.demand⟩) hs,
      Invariant.norm_id_of_nonstar (x := ⟨y.fact, y.demand || g'.demand⟩) hys]
    exact LE.of_nonstar hxy.fact hs (bor_mono hxy.dem hg.dem)

/-- `concPart` under a raise of a non-`*` fact. -/
theorem concPart_LE {cl : Cleaner} {cf : PFact} {d : Bool} (hns : cf.kind.isStar = false) :
    LE (concPart cl ⟨cf, d⟩) (concPart cl ⟨cf, true⟩) := by
  unfold concPart
  dsimp only
  cases hk : cf.kind with
  | star e => rw [hk] at hns; cases hns
  | exact => exact LE.refl _
  | any =>
    cases cl.reach with
    | exact => exact LE.refl _
    | atAndBelow => exact LE.refl _
    | below =>
      cases relate cl.path cf.path with
      | below r =>
        cases r with
        | nil => exact LE.of_nonstar rfl rfl (fun _ => rfl)
        | cons a r => exact LE.refl _
      | above r => exact LE.refl _
      | apart => exact LE.refl _

#print axioms concPart_LE

/-- The cleaner under `LE`: the results are in `LE`, the requests are the same. -/
theorem cleanRes_LL {cl : Cleaner} {c c' : AFact} (h : LE c c') :
    LL (cleanRes cl c).facts (cleanRes cl c').facts ∧ (cleanRes cl c).reqs = (cleanRes cl c').reqs := by
  obtain ⟨cf, d⟩ := c
  rcases h with rfl | ⟨hns, rfl⟩
  · exact ⟨LL.refl _, rfl⟩
  · have hns' : cf.kind.isStar = false := hns
    show LL (cleanRes cl ⟨cf, d⟩).facts (cleanRes cl ⟨cf, true⟩).facts ∧
      (cleanRes cl ⟨cf, d⟩).reqs = (cleanRes cl ⟨cf, true⟩).reqs
    unfold cleanRes
    dsimp only
    cases cleanPos cl cf with
    | disjoint => exact ⟨LL.cons (LE.raise hns') LL.nil, rfl⟩
    | inside =>
      cases cf.mark with
      | conc t =>
        dsimp only
        cases cl.markB t with
        | true => exact ⟨LL.nil, rfl⟩
        | false => exact ⟨LL.cons (LE.raise hns') LL.nil, rfl⟩
      | star =>
        cases cl.mark with
        | none => exact ⟨LL.nil, rfl⟩
        | some t => exact ⟨LL.cons (LE.of_nonstar rfl hns' (fun _ => rfl)) LL.nil, rfl⟩
      | starEx x =>
        cases cl.mark with
        | none => exact ⟨LL.nil, rfl⟩
        | some t => exact ⟨LL.cons (LE.of_nonstar rfl hns' (fun _ => rfl)) LL.nil, rfl⟩
    | part =>
      cases cf.mark with
      | conc t =>
        dsimp only
        cases cl.markB t with
        | true => exact ⟨LL.cons (concPart_LE hns') LL.nil, rfl⟩
        | false => exact ⟨LL.cons (LE.raise hns') LL.nil, rfl⟩
      | star =>
        cases cl.mark with
        | none => exact ⟨LL.refl _, rfl⟩
        | some t => exact ⟨LL.cons (LE.of_nonstar rfl hns' (fun _ => rfl)) LL.nil, rfl⟩
      | starEx x =>
        cases cl.mark with
        | none => exact ⟨LL.refl _, rfl⟩
        | some t => exact ⟨LL.cons (LE.of_nonstar rfl hns' (fun _ => rfl)) LL.nil, rfl⟩

/-- The sink check reads only the fact. -/
theorem check_LE (i s : PFact) {f g : AFact} (h : LE f g) : check i f s = check i g s := by
  obtain ⟨ff, fd⟩ := f
  obtain ⟨gf, gd⟩ := g
  have e : ff = gf := h.fact
  subst e
  rfl

/-! ## 4. The hypothesis on summary applications -/

/-- The shape of a `*` result of `applyEdge` with a non-`*` target: the input is `*`, the
    premise is `$`, and the mark gate passes. -/
theorem below_star_target {ck fk tk k : Kind} {r tp p : List Acc} {ap : Bool}
    (h : belowCase ck fk r tp tk = some (p, k, ap)) (hk : k.isStar = true)
    (htk : tk.isStar = false) : fk = .exact := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et => cases htk
    | any => cases h; cases hk
    | exact =>
      cases ck with
      | star e =>
        cases fk with
        | exact => rfl
        | star e' => cases h; cases hk
        | any => cases h; cases hk
      | any => cases h; cases hk
      | exact => cases h; cases hk

theorem geo_star_target {ck fk tk k : Kind} {P q tp p : List Acc} {ap : Bool}
    (h : CoreAux.geo ck fk P q tp tk = some (p, k, ap)) (hk : k.isStar = true)
    (htk : tk.isStar = false) : fk = .exact := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r0 =>
    rw [hrel] at h
    rw [Invariant.aboveCase_nonstar h] at hk
    cases hk
  | below r0 => rw [hrel] at h; exact below_star_target h hk htk

/-- A `*` result of `applyEdge a j g` with a non-`*` target `g`: `a` is `*`, `j` is `$`, and the
    mark gate of `j` passes `a`. -/
theorem summary_star_shape {a x : AFact} {j g : PFact} (hx : x ∈ (applyEdge a j g).facts)
    (hxs : x.fact.kind.isStar = true) (hg : g.kind.isStar = false) :
    a.fact.kind.isStar = true ∧ j.kind = .exact ∧ markGate j.mark a.fact.mark = .ok := by
  obtain ⟨p, k, ap, m, hgeo, hgate, _, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hx
  have hk : k.isStar = true := by
    cases hk : k.isStar with
    | true => rfl
    | false =>
      have e := Invariant.norm_id_of_nonstar (x := ⟨⟨g.base, p, k, m⟩, a.demand || ap⟩) hk
      rw [e] at hxs
      exact absurd (hk.symm.trans hxs) Bool.false_ne_true
  have hak : a.fact.kind.isStar = true := by
    cases h' : a.fact.kind.isStar with
    | true => rfl
    | false =>
      rw [Invariant.geo_nonstar h' hgeo] at hk
      exact absurd hk Bool.false_ne_true
  exact ⟨hak, geo_star_target hgeo hk hg, hgate⟩

/-- THE CONDITION ON ONE SUMMARY APPLICATION. If a `$` premise has a concrete mark and the caller
    fact is legal (W2), a `*` result of the summary application needs a `*` summary conclusion. -/
theorem summary_star {a x : AFact} {j g : PFact} (hj : j.kind = .exact → ∃ t, j.mark = .conc t)
    (ha : Invariant.Legal a) (hx : x ∈ (applyEdge a j g).facts) (hxs : x.fact.kind.isStar = true) :
    g.kind.isStar = true := by
  cases hgk : g.kind.isStar with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨hak, hfk, hgate⟩ := summary_star_shape hx hxs hgk
    obtain ⟨t, ht⟩ := hj hfk
    rw [ht] at hgate
    obtain ⟨t', ht'⟩ := Invariant.gate_ok_conc hgate
    obtain ⟨e, he⟩ : ∃ e, a.fact.kind = .star e := by
      cases h2 : a.fact.kind with
      | star e => exact ⟨e, rfl⟩
      | any => rw [h2] at hak; cases hak
      | exact => rw [h2] at hak; cases hak
    exact (ha e he).1.not_conc t' ht'

#print axioms summary_star

/-- Every `$` initial fact of the run `R` has a concrete mark. -/
def ExactInitConc (R : Obj → Prop) : Prop :=
  ∀ m j, R (.init m j) → j.kind = .exact → ∃ t, j.mark = .conc t

/-- THE HYPOTHESIS of the run-1 simulation: in the rule `ret` of the run `R`, a `*` result of the
    summary application needs a `*` summary conclusion (so the layer of the summary edge, which
    `applySummary` reads before the normal form, can only differ on a non-`*` result). -/
def SummaryStar (P : Program) (R : Obj → Prop) : Prop :=
  ∀ {M : MethodId} {i : PFact} {n : Node} {f : AFact} {n' : Node} {c : Call} {e1 : MicroEdge}
    {a : AFact} {j : PFact} {g : AFact} {x : AFact},
    R (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges → e1 ∈ c.toCallee →
    a ∈ (applyEdge f e1.1 e1.2).facts → R (.init c.callee j) → applicable j a.fact = true →
    R (.edge c.callee j (P.exit c.callee) g) → x ∈ (applyEdge a j g.fact).facts →
    x.fact.kind.isStar = true → g.fact.kind.isStar = true

/-- `SummaryStar` from concrete `$` initial facts. -/
theorem summaryStar_of_eic {P : Program} {R : Obj → Prop} (hJ : ExactInitConc R) :
    SummaryStar P R :=
  fun _ _ _ ha hj _ _ hx hxs => summary_star (hJ _ _ hj) (Invariant.applyEdge_Legal ha) hx hxs

#print axioms summaryStar_of_eic

/-- The answer of a request has a concrete mark. -/
theorem answerInit_mark (i a : PFact) (t : Mark) : (answerInit i a t).mark = .conc t := by
  unfold answerInit
  split <;> rfl

/-- The motive of `D_eic`. -/
def EIC : Obj → Prop
  | .init _ j => j.kind = .exact → ∃ t, j.mark = .conc t
  | _ => True

section EICD
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- `ExactInitConc` for run 1, from the abstraction: the root is the zero fact, an answer has the
    requested mark. -/
theorem D_eic (hα : ∀ m a, (α m a).kind = .exact → ∃ t, (α m a).mark = .conc t) :
    ExactInitConc (D P counted L α sinks roots) := by
  have key : ∀ o, D P counted L α sinks roots o → EIC o := by
    intro o h
    induction h with
    | root => exact fun _ => ⟨zeroMark, rfl⟩
    | initA => exact hα _ _
    | @answer M i t a _ _ _ _ _ _ => exact fun _ => ⟨t, answerInit_mark i a t⟩
    | start => trivial
    | step => trivial
    | reqStmt => trivial
    | pass => trivial
    | added => trivial
    | ret => trivial
    | reqSink => trivial
    | reqUp => trivial
    | vuln => trivial
    | clean => trivial
    | reqClean => trivial
    | filt => trivial
  exact fun m j h => key _ h

#print axioms D_eic

/-- `SummaryStar` under the hypotheses of `Invariant.no_univ_star` (S8: a `$` premise of a micro
    edge has a concrete mark; no `*/Universe` micro edge or initial fact). -/
theorem summaryStar_of_noUniv (hA : Invariant.AllEdges P Invariant.PremConc)
    (hB : Invariant.AllEdges P Invariant.NoUnivE)
    (hC : ∀ M i, D P counted L α sinks roots (.init M i) → i.kind ≠ .star .univ) :
    SummaryStar P (D P counted L α sinks roots) := by
  intro M i n f n' c e1 a j g x hf hE he1 ha _ happ _ hx hxs
  cases hgk : g.fact.kind.isStar with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨hak, hfk, _⟩ := summary_star_shape hx hxs hgk
    have hfu := Invariant.no_univ_star P counted L α sinks roots hA hB hC hf
    have hb1 := hB.2.1 _ _ _ _ hE e1 he1
    have hau := Invariant.applyEdge_no_univ hfu hb1.1 hb1.2
      (fun h0 => Or.inl (hA.2.1 _ _ _ _ hE e1 he1 h0)) ha
    rw [Invariant.applicable_exact_nonstar hfk hau happ] at hak
    cases hak

#print axioms summaryStar_of_noUniv

end EICD

/-- The policy gives a `$` fact only as the zero fact. -/
theorem policy_eic (demand : MethodId → List PFact) :
    ∀ m a, (policy demand m a).kind = .exact → ∃ t, (policy demand m a).mark = .conc t := by
  intro m a h
  revert h
  unfold policy
  split
  · exact fun _ => ⟨zeroMark, rfl⟩
  · split
    · intro h; cases h
    · intro h; cases h

/-! ## 5. The run-1 closure with W6 -/

section Closure6
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- Run 1 with W6: the rules of `D`; the result of every AP operation passes through `w6`. -/
inductive D6 : Obj → Prop where
  | root {M} : M ∈ roots → D6 (.init M zeroFact)
  | start {M i} : D6 (.init M i) → D6 (.edge M i (P.entry M) (w6 (startFact i)))
  | step {M i n f n' s f'} :
      D6 (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → D6 (.edge M i n' (w6 f'))
  | reqStmt {M i n f n' s t} :
      D6 (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs → D6 (.req M i t)
  | pass {M i n f n' c} :
      D6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → D6 (.edge M i n' f)
  | added {M i n f n' c e a} :
      D6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      D6 (.added c.callee a.fact)
  | initA {m a} : D6 (.added m a) → D6 (.init m (α m a))
  | ret {M i n f n' c e1 a j g r e2 r'} :
      D6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      D6 (.init c.callee j) →
      applicable j a.fact = true →
      D6 (.edge c.callee j (P.exit c.callee) g) →
      r ∈ (applySummary (w6 a) j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge (w6 r) e2.1 e2.2).facts →
      D6 (.edge M i n' (w6 (limitF counted L r')))
  | reqSink {M i n f s t} :
      D6 (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      D6 (.req M i t)
  | answer {M i t a} :
      D6 (.req M i t) → D6 (.added M a) → a.mark = .conc t →
      overlapB a i = true → D6 (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      D6 (.req m j t) → D6 (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → D6 (.req M ic t)
  | vuln {M i n f s} :
      D6 (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      D6 (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      D6 (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → D6 (.edge M i n' (w6 f'))
  | reqClean {M i n f n' cl t} :
      D6 (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs → D6 (.req M i t)
  | filt {M i n f n' b may} :
      D6 (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → D6 (.edge M i n' f)

end Closure6

/-! ## 6. The simulation relation on objects -/

/-- `Up R o`: `R` has the object `o`, an edge in the same or a raised layer (`LE`), a
    vulnerability in the same or a raised layer. -/
def Up (R : Obj → Prop) : Obj → Prop
  | .init M i => R (.init M i)
  | .edge M i n f => ∃ g, R (.edge M i n g) ∧ LE f g
  | .added M a => R (.added M a)
  | .req M i t => R (.req M i t)
  | .vuln M n s d => ∃ d', R (.vuln M n s d') ∧ (d = true → d' = true)

/-- `Down R o`: `R` has the object `o`, an edge in the same or a lower layer, a vulnerability in
    the same or a lower layer. -/
def Down (R : Obj → Prop) : Obj → Prop
  | .init M i => R (.init M i)
  | .edge M i n g => ∃ f, R (.edge M i n f) ∧ LE f g
  | .added M a => R (.added M a)
  | .req M i t => R (.req M i t)
  | .vuln M n s d' => ∃ d, R (.vuln M n s d) ∧ (d = true → d' = true)

section Sim1
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- THE SIMULATION, D INTO D6: every object of `D` is an object of `D6`, every edge with the same
    fact in the same or a raised layer, every vulnerability in the same or a raised layer. -/
theorem D_le_D6 (hS : SummaryStar P (D P counted L α sinks roots)) {o : Obj}
    (h : D P counted L α sinks roots o) : Up (D6 P counted L α sinks roots) o := by
  induction h with
  | root hM => exact D6.root hM
  | @start M i _ ih => exact ⟨_, D6.start ih, LE_w6_self _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (transfer_LL hle).1.fwd hf
    exact ⟨_, D6.step hg hE hg', LE_w6 hle'⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6.reqStmt hg hE (by rw [← (transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6.pass hg hE (by rw [← hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a', ha', hla⟩ := (applyEdge_LL hle).1.fwd ha
    show D6 P counted L α sinks roots (.added c.callee a.fact)
    rw [hla.fact]
    exact D6.added hg hE he ha'
  | initA _ ih => exact D6.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' hf hE he1 ha hj happ hg hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f6, hf6, hlf⟩ := ihF
    obtain ⟨g6, hg6, hlg⟩ := ihG
    obtain ⟨a6, ha6, hla⟩ := (applyEdge_LL hlf).1.fwd ha
    have hX : ∀ x, x ∈ (applyEdge a j g.fact).facts → x.fact.kind.isStar = true → g6 = g :=
      fun x hx hxs => hlg.star_eq (hS hf hE he1 ha hj happ hg hx hxs)
    obtain ⟨r6, hr6, hlr⟩ := (applySummary_LL (LE_w6 hla) hlg hX).fwd hr
    obtain ⟨r6', hr6', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.fwd hr'
    exact ⟨_, D6.ret hf6 hE he1 ha6 ihJ (by rw [← hla.fact]; exact happ) hg6 hr6 he2 hr6',
      LE_w6 (limitF_LE hlr')⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6.reqSink hg hs (by rw [← check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact D6.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a', ha', hla⟩ := (applyEdge_LL hle).1.fwd ha
    exact D6.reqUp ihR hg hE hc he ha' (by rw [← hla.fact]; exact hcl)
      (by rw [← hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, D6.vuln hg hs (by rw [← check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (cleanRes_LL hle).1.fwd hf
    exact ⟨_, D6.clean hg hE hg', LE_w6 hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D6.reqClean hg hE (by rw [← (cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D6.filt hg hE (by rw [← hle.fact]; exact hp), hle⟩

#print axioms D_le_D6

/-- THE SIMULATION, D6 INTO D: every object of `D6` is an object of `D`, every edge with the same
    fact in the same or a lower layer, every vulnerability in the same or a lower layer. -/
theorem D6_le_D (hS : SummaryStar P (D P counted L α sinks roots)) {o : Obj}
    (h : D6 P counted L α sinks roots o) : Down (D P counted L α sinks roots) o := by
  induction h with
  | root hM => exact D.root hM
  | @start M i _ ih => exact ⟨_, D.start ih, LE_w6_self _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (transfer_LL hle).1.bwd hf
    exact ⟨g', D.step hg hE hg', LE_w6 hle'⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqStmt hg hE (by rw [(transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D.pass hg hE (by rw [hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hle).1.bwd ha
    show D P counted L α sinks roots (.added c.callee a.fact)
    rw [← hla.fact]
    exact D.added hg hE he ha0
  | initA _ ih => exact D.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' hf hE he1 ha hj happ hg hr he2 hr' ihF ihJ ihG =>
    obtain ⟨f0, hf0, hlf⟩ := ihF
    obtain ⟨g0, hg0, hlg⟩ := ihG
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hlf).1.bwd ha
    have happ0 : applicable j a0.fact = true := by rw [hla.fact]; exact happ
    have hX : ∀ x, x ∈ (applyEdge a0 j g0.fact).facts → x.fact.kind.isStar = true → g = g0 :=
      fun x hx hxs => hlg.star_eq (hS hf0 hE he1 ha0 ihJ happ0 hg0 hx hxs)
    obtain ⟨r0, hr0, hlr⟩ := (applySummary_LL (LE_w6 hla) hlg hX).bwd hr
    obtain ⟨r0', hr0', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.bwd hr'
    exact ⟨_, D.ret hf0 hE he1 ha0 ihJ happ0 hg0 hr0 he2 hr0', LE_w6 (limitF_LE hlr')⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqSink hg hs (by rw [check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact D.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hle).1.bwd ha
    exact D.reqUp ihR hg hE hc he ha0 (by rw [hla.fact]; exact hcl) (by rw [hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, D.vuln hg hs (by rw [check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (cleanRes_LL hle).1.bwd hf
    exact ⟨g', D.clean hg hE hg', LE_w6 hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact D.reqClean hg hE (by rw [(cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, D.filt hg hE (by rw [hle.fact]; exact hp), hle⟩

#print axioms D6_le_D

/-- THE SAME SHAPE: with W6, run 1 has the same initial facts, added facts, requests, edge facts
    (each edge in the same or a raised layer) and reported sinks. So the abstraction, the
    requests and the answers do not see W6. -/
theorem D6_same_shape (hS : SummaryStar P (D P counted L α sinks roots)) :
    (∀ M i, D6 P counted L α sinks roots (.init M i) ↔ D P counted L α sinks roots (.init M i)) ∧
    (∀ M a, D6 P counted L α sinks roots (.added M a) ↔ D P counted L α sinks roots (.added M a)) ∧
    (∀ M i t, D6 P counted L α sinks roots (.req M i t) ↔ D P counted L α sinks roots (.req M i t)) ∧
    (∀ M i n p, (∃ g, D6 P counted L α sinks roots (.edge M i n g) ∧ g.fact = p) ↔
      (∃ f, D P counted L α sinks roots (.edge M i n f) ∧ f.fact = p)) ∧
    (∀ M n s, (∃ b, D6 P counted L α sinks roots (.vuln M n s b)) ↔
      (∃ b, D P counted L α sinks roots (.vuln M n s b))) := by
  have up := fun o (h : D P counted L α sinks roots o) => D_le_D6 P counted L α sinks roots hS h
  have down := fun o (h : D6 P counted L α sinks roots o) => D6_le_D P counted L α sinks roots hS h
  refine ⟨fun M i => ⟨down _, up _⟩, fun M a => ⟨down _, up _⟩, fun M i t => ⟨down _, up _⟩,
    fun M i n p => ⟨?_, ?_⟩, fun M n s => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hle⟩ := down _ hg
    exact ⟨f, hf, hle.fact⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hle⟩ := up _ hf
    exact ⟨g, hg, hle.fact.symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := down _ hb
    exact ⟨b', hb'⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := up _ hb
    exact ⟨b', hb'⟩

#print axioms D6_same_shape

end Sim1

/-! ## 7. The restriction under `LE` -/

/-- Two optional facts in `LE`. -/
def OptLE : Option AFact → Option AFact → Prop
  | none, none => True
  | some x, some y => LE x y
  | _, _ => False

theorem OptLE.refl : ∀ (o : Option AFact), OptLE o o
  | none => trivial
  | some x => LE.refl x

theorem OptLE.some_left {x : AFact} {o : Option AFact} (h : OptLE (some x) o) :
    ∃ y, o = some y ∧ LE x y := by
  cases o with
  | none => exact False.elim h
  | some y => exact ⟨y, rfl, h⟩

theorem OptLE.some_right {o : Option AFact} {y : AFact} (h : OptLE o (some y)) :
    ∃ x, o = some x ∧ LE x y := by
  cases o with
  | none => exact False.elim h
  | some x => exact ⟨x, rfl, h⟩

/-- The restriction reads the layer only to copy it. -/
def RestrictLE (restrict : PFact → AFact → DemandEdge → Option AFact) : Prop :=
  ∀ j g g' d, LE g g' → OptLE (restrict j g d) (restrict j g' d)

/-- The same for a conclusion restriction. -/
def ConcLE (rc : AFact → PFact → Option AFact) : Prop :=
  ∀ g g' p, LE g g' → OptLE (rc g p) (rc g' p)

theorem restrictWith_LE {rc : AFact → PFact → Option AFact} (h : ConcLE rc) :
    RestrictLE (restrictWith rc) := by
  intro j g g' d hle
  unfold restrictWith
  cases d.dout with
  | none => trivial
  | some p =>
    dsimp only
    cases overlapB j d.din with
    | true => exact h g g' p hle
    | false => trivial

theorem restrictConcU_LE : ConcLE restrictConcU := by
  intro g g' p hle
  obtain ⟨gf, gd⟩ := g
  rcases hle with rfl | ⟨hns, rfl⟩
  · exact OptLE.refl _
  · have hns' : gf.kind.isStar = false := hns
    show OptLE (restrictConcU ⟨gf, gd⟩ p) (restrictConcU ⟨gf, true⟩ p)
    unfold restrictConcU
    dsimp only
    cases Nat.beq gf.base p.base with
    | false => trivial
    | true =>
      try dsimp only
      cases relate p.path gf.path with
      | below r =>
        try dsimp only
        cases admitsTailB p.kind r with
        | true => exact LE.raise (f := ⟨gf, gd⟩) hns'
        | false => trivial
      | above r =>
        try dsimp only
        cases hk : gf.kind with
        | any => exact LE.of_nonstar rfl (by cases p.kind <;> rfl) (fun _ => rfl)
        | star e => trivial
        | exact => trivial
      | apart => trivial

theorem restrictConcS_LE : ConcLE restrictConcS := by
  intro g g' p hle
  obtain ⟨gf, gd⟩ := g
  rcases hle with rfl | ⟨hns, rfl⟩
  · exact OptLE.refl _
  · have hns' : gf.kind.isStar = false := hns
    show OptLE (restrictConcS ⟨gf, gd⟩ p) (restrictConcS ⟨gf, true⟩ p)
    unfold restrictConcS
    dsimp only
    cases Nat.beq gf.base p.base with
    | false => trivial
    | true =>
      try dsimp only
      cases relate p.path gf.path with
      | below r =>
        try dsimp only
        cases admitsTailB p.kind r with
        | true => exact LE.raise (f := ⟨gf, gd⟩) hns'
        | false => trivial
      | above r =>
        try dsimp only
        cases hk : gf.kind with
        | any => exact LE.of_nonstar rfl (by cases p.kind <;> rfl) (fun _ => rfl)
        | star e => rw [hk] at hns'; cases hns'
        | exact => trivial
      | apart => trivial

theorem restrictU_LE : RestrictLE restrictU := restrictWith_LE restrictConcU_LE
theorem restrictS_LE : RestrictLE restrictS := restrictWith_LE restrictConcS_LE

#print axioms restrictU_LE
#print axioms restrictS_LE

/-! ## 8. The restricted closure with W6 -/

section ClosureR6
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- A restricted run with W6: the rules of `DR`; the result of every AP operation passes through
    `w6` (also the restricted summary edge). A persisted record is applied as it is. -/
inductive DR6 : Obj → Prop where
  | root {M} : M ∈ roots → DR6 (.init M zeroFact)
  | start {M i} : DR6 (.init M i) → DR6 (.edge M i (P.entry M) (w6 (startFact i)))
  | step {M i n f n' s f'} :
      DR6 (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → DR6 (.edge M i n' (w6 f'))
  | reqStmt {M i n f n' s t} :
      DR6 (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs → DR6 (.req M i t)
  | pass {M i n f n' c} :
      DR6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → DR6 (.edge M i n' f)
  | added {M i n f n' c e a} :
      DR6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DR6 (.added c.callee a.fact)
  | initR {m a d j} :
      DR6 (.added m a) → demand m d → emit d.din a = some j → DR6 (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      DR6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DR6 (.init c.callee j) →
      DR6 (.edge c.callee j (P.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary (w6 a) j (w6 g')).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge (w6 r) e2.1 e2.2).facts →
      DR6 (.edge M i n' (w6 (limitF counted L r')))
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      DR6 (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary (w6 a) j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge (w6 r) e2.1 e2.2).facts →
      DR6 (.edge M i n' (w6 (limitF counted L r')))
  | reqSink {M i n f s t} :
      DR6 (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      DR6 (.req M i t)
  | answer {M i t a} :
      DR6 (.req M i t) → DR6 (.added M a) → a.mark = .conc t →
      overlapB a i = true → DR6 (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DR6 (.req m j t) → DR6 (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DR6 (.req M ic t)
  | vuln {M i n f s} :
      DR6 (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DR6 (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DR6 (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → DR6 (.edge M i n' (w6 f'))
  | reqClean {M i n f n' cl t} :
      DR6 (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanRes cl f).reqs → DR6 (.req M i t)
  | filt {M i n f n' b may} :
      DR6 (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → DR6 (.edge M i n' f)

end ClosureR6

section SimR
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- THE SIMULATION, DR INTO DR6. -/
theorem DR_le_DR6 (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots)) {o : Obj}
    (h : DR P counted L demand emit sat restrict recs sinks roots o) :
    Up (DR6 P counted L demand emit sat restrict recs sinks roots) o := by
  induction h with
  | root hM => exact DR6.root hM
  | @start M i _ ih => exact ⟨_, DR6.start ih, LE_w6_self _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (transfer_LL hle).1.fwd hf
    exact ⟨_, DR6.step hg hE hg', LE_w6 hle'⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR6.reqStmt hg hE (by rw [← (transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, DR6.pass hg hE (by rw [← hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a', ha', hla⟩ := (applyEdge_LL hle).1.fwd ha
    show DR6 P counted L demand emit sat restrict recs sinks roots (.added c.callee a.fact)
    rw [hla.fact]
    exact DR6.added hg hE he ha'
  | initR _ hd hj ih => exact DR6.initR ih hd hj
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf hE he1 ha hj hg hd hres hsat hr he2 hr'
      ihF ihJ ihG =>
    obtain ⟨f6, hf6, hlf⟩ := ihF
    obtain ⟨g6, hg6, hlg⟩ := ihG
    obtain ⟨a6, ha6, hla⟩ := (applyEdge_LL hlf).1.fwd ha
    have hopt := hRL j g g6 d hlg
    rw [hres] at hopt
    obtain ⟨g6', hres6, hlg'⟩ := OptLE.some_left hopt
    have hX : ∀ x, x ∈ (applyEdge a j g'.fact).facts → x.fact.kind.isStar = true → w6 g6' = g' :=
      fun x hx hxs => (LE_w6 hlg').star_eq
        (summary_star (hJ _ _ hj) (Invariant.applyEdge_Legal ha) hx hxs)
    obtain ⟨r6, hr6, hlr⟩ := (applySummary_LL (LE_w6 hla) (LE_w6 hlg') hX).fwd hr
    obtain ⟨r6', hr6', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.fwd hr'
    exact ⟨_, DR6.ret hf6 hE he1 ha6 ihJ hg6 hd hres6 (by rw [← hla.fact]; exact hsat) hr6 he2
      hr6', LE_w6 (limitF_LE hlr')⟩
  | @retRec M i n f n' c e1 a j g r e2 r' hf hE he1 ha hrec hsat hr he2 hr' ihF =>
    obtain ⟨f6, hf6, hlf⟩ := ihF
    obtain ⟨a6, ha6, hla⟩ := (applyEdge_LL hlf).1.fwd ha
    obtain ⟨r6, hr6, hlr⟩ :=
      (applySummary_LL (LE_w6 hla) (LE.refl g) (fun _ _ _ => rfl)).fwd hr
    obtain ⟨r6', hr6', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.fwd hr'
    exact ⟨_, DR6.retRec hf6 hE he1 ha6 hrec (by rw [← hla.fact]; exact hsat) hr6 he2 hr6',
      LE_w6 (limitF_LE hlr')⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR6.reqSink hg hs (by rw [← check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact DR6.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a', ha', hla⟩ := (applyEdge_LL hle).1.fwd ha
    exact DR6.reqUp ihR hg hE hc he ha' (by rw [← hla.fact]; exact hcl)
      (by rw [← hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, DR6.vuln hg hs (by rw [← check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (cleanRes_LL hle).1.fwd hf
    exact ⟨_, DR6.clean hg hE hg', LE_w6 hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR6.reqClean hg hE (by rw [← (cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, DR6.filt hg hE (by rw [← hle.fact]; exact hp), hle⟩

#print axioms DR_le_DR6

/-- THE SIMULATION, DR6 INTO DR. -/
theorem DR6_le_DR (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots)) {o : Obj}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots o) :
    Down (DR P counted L demand emit sat restrict recs sinks roots) o := by
  induction h with
  | root hM => exact DR.root hM
  | @start M i _ ih => exact ⟨_, DR.start ih, LE_w6_self _⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (transfer_LL hle).1.bwd hf
    exact ⟨g', DR.step hg hE hg', LE_w6 hle'⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR.reqStmt hg hE (by rw [(transfer_LL hle).2]; exact ht)
  | @pass M i n f n' c _ hE hm ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, DR.pass hg hE (by rw [hle.fact]; exact hm), hle⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hle).1.bwd ha
    show DR P counted L demand emit sat restrict recs sinks roots (.added c.callee a.fact)
    rw [← hla.fact]
    exact DR.added hg hE he ha0
  | initR _ hd hj ih => exact DR.initR ih hd hj
  | @ret M i n f n' c e1 a j g d g' r e2 r' hf hE he1 ha hj hg hd hres hsat hr he2 hr'
      ihF ihJ ihG =>
    obtain ⟨f0, hf0, hlf⟩ := ihF
    obtain ⟨g0, hg0, hlg⟩ := ihG
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hlf).1.bwd ha
    have hopt := hRL j g0 g d hlg
    rw [hres] at hopt
    obtain ⟨g0', hres0, hlg'⟩ := OptLE.some_right hopt
    have hX : ∀ x, x ∈ (applyEdge a0 j g0'.fact).facts → x.fact.kind.isStar = true →
        w6 g' = g0' :=
      fun x hx hxs => (LE_w6 hlg').star_eq
        (summary_star (hJ _ _ ihJ) (Invariant.applyEdge_Legal ha0) hx hxs)
    obtain ⟨r0, hr0, hlr⟩ := (applySummary_LL (LE_w6 hla) (LE_w6 hlg') hX).bwd hr
    obtain ⟨r0', hr0', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.bwd hr'
    exact ⟨_, DR.ret hf0 hE he1 ha0 ihJ hg0 hd hres0 (by rw [hla.fact]; exact hsat) hr0 he2 hr0',
      LE_w6 (limitF_LE hlr')⟩
  | @retRec M i n f n' c e1 a j g r e2 r' hf hE he1 ha hrec hsat hr he2 hr' ihF =>
    obtain ⟨f0, hf0, hlf⟩ := ihF
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hlf).1.bwd ha
    obtain ⟨r0, hr0, hlr⟩ :=
      (applySummary_LL (LE_w6 hla) (LE.refl g) (fun _ _ _ => rfl)).bwd hr
    obtain ⟨r0', hr0', hlr'⟩ := (applyEdge_LL (LE_w6 hlr)).1.bwd hr'
    exact ⟨_, DR.retRec hf0 hE he1 ha0 hrec (by rw [hla.fact]; exact hsat) hr0 he2 hr0',
      LE_w6 (limitF_LE hlr')⟩
  | @reqSink M i n f s t _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR.reqSink hg hs (by rw [check_LE i s hle]; exact hc)
  | answer _ _ hm ho ihR ihA => exact DR.answer ihR ihA hm ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl ho ihR ihF =>
    obtain ⟨g, hg, hle⟩ := ihF
    obtain ⟨a0, ha0, hla⟩ := (applyEdge_LL hle).1.bwd ha
    exact DR.reqUp ihR hg hE hc he ha0 (by rw [hla.fact]; exact hcl) (by rw [hla.fact]; exact ho)
  | @vuln M i n f s _ hs hc ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g.demand, DR.vuln hg hs (by rw [check_LE i s hle]; exact hc), hle.dem⟩
  | @clean M i n f n' cl f' _ hE hf ih =>
    obtain ⟨g, hg, hle⟩ := ih
    obtain ⟨g', hg', hle'⟩ := (cleanRes_LL hle).1.bwd hf
    exact ⟨g', DR.clean hg hE hg', LE_w6 hle'⟩
  | @reqClean M i n f n' cl t _ hE ht ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact DR.reqClean hg hE (by rw [(cleanRes_LL hle).2]; exact ht)
  | @filt M i n f n' b may _ hE hp ih =>
    obtain ⟨g, hg, hle⟩ := ih
    exact ⟨g, DR.filt hg hE (by rw [hle.fact]; exact hp), hle⟩

#print axioms DR6_le_DR

/-- `ExactInitConc` for a restricted run with a mark-copying emission (`emitM`): every initial
    fact is concrete (`RExact.init_concrete`). -/
theorem DR_eic (hem : EmitCopiesMark emit) :
    ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots) :=
  fun _ _ h _ => RExact.init_concrete hem h

/-- THE SAME SHAPE for a restricted run. -/
theorem DR6_same_shape (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots)) :
    (∀ M i, DR6 P counted L demand emit sat restrict recs sinks roots (.init M i) ↔
      DR P counted L demand emit sat restrict recs sinks roots (.init M i)) ∧
    (∀ M a, DR6 P counted L demand emit sat restrict recs sinks roots (.added M a) ↔
      DR P counted L demand emit sat restrict recs sinks roots (.added M a)) ∧
    (∀ M i t, DR6 P counted L demand emit sat restrict recs sinks roots (.req M i t) ↔
      DR P counted L demand emit sat restrict recs sinks roots (.req M i t)) ∧
    (∀ M i n p, (∃ g, DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n g) ∧
        g.fact = p) ↔
      (∃ f, DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) ∧
        f.fact = p)) ∧
    (∀ M n s, (∃ b, DR6 P counted L demand emit sat restrict recs sinks roots (.vuln M n s b)) ↔
      (∃ b, DR P counted L demand emit sat restrict recs sinks roots (.vuln M n s b))) := by
  have up := fun o (h : DR P counted L demand emit sat restrict recs sinks roots o) =>
    DR_le_DR6 P counted L demand emit sat restrict recs sinks roots hRL hJ h
  have down := fun o (h : DR6 P counted L demand emit sat restrict recs sinks roots o) =>
    DR6_le_DR P counted L demand emit sat restrict recs sinks roots hRL hJ h
  refine ⟨fun M i => ⟨down _, up _⟩, fun M a => ⟨down _, up _⟩, fun M i t => ⟨down _, up _⟩,
    fun M i n p => ⟨?_, ?_⟩, fun M n s => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hle⟩ := down _ hg
    exact ⟨f, hf, hle.fact⟩
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hle⟩ := up _ hf
    exact ⟨g, hg, hle.fact.symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := down _ hb
    exact ⟨b', hb'⟩
  · rintro ⟨b, hb⟩
    obtain ⟨b', hb', _⟩ := up _ hb
    exact ⟨b', hb'⟩

#print axioms DR6_same_shape

end SimR

/-! ## 9. W6 holds in the W6 runs -/

/-- The motive of W6: an `[any]` edge fact is in the demand layer. -/
def W6Inv : Obj → Prop
  | .edge _ _ _ f => f.fact.kind.isAny = true → f.demand = true
  | _ => True

section W6Holds
variable (P : Program) (counted : Acc → Bool) (L : Nat)

theorem D6_w6inv {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj} (h : D6 P counted L α sinks roots o) : W6Inv o := by
  induction h with
  | root => trivial
  | start => exact w6_ok _
  | step => exact w6_ok _
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | ret => exact w6_ok _
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean => exact w6_ok _
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- W6 HOLDS IN `D6`: every `[any]` edge fact is in the demand layer. -/
theorem D6_w6 {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6 P counted L α sinks roots (.edge M i n f)) (ha : f.fact.kind.isAny = true) :
    f.demand = true :=
  D6_w6inv P counted L h ha

#print axioms D6_w6

theorem DR6_w6inv {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → (PFact × AFact) → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {o : Obj}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots o) : W6Inv o := by
  induction h with
  | root => trivial
  | start => exact w6_ok _
  | step => exact w6_ok _
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret => exact w6_ok _
  | retRec => exact w6_ok _
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean => exact w6_ok _
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- W6 HOLDS IN `DR6`. -/
theorem DR6_w6 {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → (PFact × AFact) → Prop} {sinks : List (MethodId × Node × PFact)}
    {roots : List MethodId} {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.fact.kind.isAny = true) : f.demand = true :=
  DR6_w6inv P counted L h ha

#print axioms DR6_w6

end W6Holds

/-- With W6 a normal edge is complete: `AFact.complete` and the normal layer agree (spec §11.2). -/
theorem complete_iff_of_w6 {f : AFact} (hw : f.fact.kind.isAny = true → f.demand = true) :
    f.complete = true ↔ f.demand = false := by
  unfold AFact.complete
  cases hd : f.demand with
  | true => exact ⟨fun h' => absurd h' Bool.false_ne_true, fun h' => absurd h'.symm Bool.false_ne_true⟩
  | false =>
    cases ha : f.fact.kind.isAny with
    | true => exact absurd (hd.symm.trans (hw ha)) Bool.false_ne_true
    | false => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ## 10. The summaries and the demand they pass on do not see W6 -/

section Shape
variable {P : Program} {R R6 : Obj → Prop}

theorem summaryDemand_of_up (hup : ∀ o, R o → Up R6 o) {m : MethodId} {d : DemandEdge}
    (h : summaryDemand P R m d) : summaryDemand P R6 m d := by
  obtain ⟨hi, hd⟩ := h
  refine ⟨hup _ hi, ?_⟩
  rcases hd with hn | ⟨g, hg, he⟩
  · exact Or.inl hn
  · obtain ⟨g6, hg6, hle⟩ := hup _ hg
    exact Or.inr ⟨g6, hg6, by rw [he, hle.fact]⟩

theorem summaryDemand_of_down (hdown : ∀ o, R6 o → Down R o) {m : MethodId} {d : DemandEdge}
    (h : summaryDemand P R6 m d) : summaryDemand P R m d := by
  obtain ⟨hi, hd⟩ := h
  refine ⟨hdown _ hi, ?_⟩
  rcases hd with hn | ⟨g, hg, he⟩
  · exact Or.inl hn
  · obtain ⟨g0, hg0, hle⟩ := hdown _ hg
    exact Or.inr ⟨g0, hg0, by rw [he, hle.fact]⟩

/-- The summary demand of a run and of its W6 run are the same. -/
theorem summaryDemand_iff (hup : ∀ o, R o → Up R6 o) (hdown : ∀ o, R6 o → Down R o)
    (m : MethodId) (d : DemandEdge) : summaryDemand P R m d ↔ summaryDemand P R6 m d :=
  ⟨summaryDemand_of_up hup, summaryDemand_of_down hdown⟩

theorem revSummaryDemand_of_up (hup : ∀ o, R o → Up R6 o) {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand P R m d) : Backward.revSummaryDemand P R6 m d := by
  obtain ⟨j, g, hsd, he⟩ := h
  exact ⟨j, g, summaryDemand_of_up hup hsd, he⟩

theorem revSummaryDemand_of_down (hdown : ∀ o, R6 o → Down R o) {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand P R6 m d) : Backward.revSummaryDemand P R m d := by
  obtain ⟨j, g, hsd, he⟩ := h
  exact ⟨j, g, summaryDemand_of_down hdown hsd, he⟩

/-- The reversed summary demand (the backward run's demand) is the same with and without W6. -/
theorem revSummaryDemand_iff (hup : ∀ o, R o → Up R6 o) (hdown : ∀ o, R6 o → Down R o)
    (m : MethodId) (d : DemandEdge) :
    Backward.revSummaryDemand P R m d ↔ Backward.revSummaryDemand P R6 m d :=
  ⟨revSummaryDemand_of_up hup, revSummaryDemand_of_down hdown⟩

end Shape

/-! ## 11. Soundness -/

section Sound1
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- COVERAGE OF RUN 1 WITH W6 (from `Coverage.coverage` through the simulation). -/
theorem coverage6 (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, D6 P counted L α sinks roots (.init M i) → i.covers l0 →
      (∃ f, D6 P counted L α sinks roots (.edge M i n f) ∧ den i f.fact l0 l) ∨
      D6 P counted L α sinks roots (.req M i l0.mark) := by
  intro i hi hc
  have hi0 : D P counted L α sinks roots (.init M i) := D6_le_D P counted L α sinks roots hS hi
  rcases Coverage.coverage P counted L α sinks roots hwf hα hfl i hi0 hc with ⟨f, hf, hd⟩ | hr
  · obtain ⟨g, hg, hle⟩ := D_le_D6 P counted L α sinks roots hS hf
    exact Or.inl ⟨g, hg, by rw [← hle.fact]; exact hd⟩
  · exact Or.inr (D_le_D6 P counted L α sinks roots hS hr)

#print axioms coverage6

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH W6. -/
theorem vuln_found6 (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D6 P counted L α sinks roots (.vuln M n s b) := by
  obtain ⟨b, hb⟩ := Coverage.vuln_found P counted L α sinks roots hwf hα hR hs hT hsc
  obtain ⟨b', hb', _⟩ := D_le_D6 P counted L α sinks roots hS hb
  exact ⟨b', hb'⟩

#print axioms vuln_found6

end Sound1

/-- The policy satisfies the hypothesis of the simulation. -/
theorem summaryStar_policy (P : Program) (counted : Acc → Bool) (L : Nat)
    (demand : MethodId → List PFact) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : SummaryStar P (D P counted L (policy demand) sinks roots) :=
  summaryStar_of_eic (D_eic P counted L (policy demand) sinks roots (policy_eic demand))

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH W6, for the policy (no hypothesis but `P.WF`). -/
theorem vuln_found_policy6 {P : Program} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) (demand : MethodId → List PFact)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D6 P counted L (policy demand) sinks roots (.vuln M n s b) :=
  vuln_found6 P counted L (policy demand) sinks roots hwf (policy_applicable demand)
    (summaryStar_policy P counted L demand sinks roots) hR hs hT hsc

#print axioms vuln_found_policy6

section SoundR
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- THE VULNERABILITY THEOREM OF A RESTRICTED RUN WITH W6 (from `RCov.vuln_foundR`): a demanded
    witness gives a `vuln` object of `DR6`, and the summaries of `DR6` demand the witness again. -/
theorem vuln_foundR6 (hwf : P.WF)
    (hE : EmitContractOn (DR6 P counted L demand emit sat restrict recs sinks roots) emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict) (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DR6 P counted L demand emit sat restrict recs sinks roots (.vuln M n s b)) ∧
    ReachR P (summaryDemand P (DR6 P counted L demand emit sat restrict recs sinks roots))
      roots M n l := by
  have hup := fun o (h : DR P counted L demand emit sat restrict recs sinks roots o) =>
    DR_le_DR6 P counted L demand emit sat restrict recs sinks roots hRL hJ h
  have hE0 : EmitContractOn (DR P counted L demand emit sat restrict recs sinks roots) emit sat :=
    fun m d a l hA hd ha => hE m d a l (hup _ hA) hd ha
  obtain ⟨⟨b, hb⟩, hRR⟩ := RCov.vuln_foundR P counted L demand emit sat restrict recs sinks roots
    hwf hE0 hS hR hRe hs hT hsc
  obtain ⟨b', hb', _⟩ := hup _ hb
  exact ⟨⟨b', hb'⟩, RCov.reachR_mono (fun _ _ h => summaryDemand_of_up hup h) hRR⟩

#print axioms vuln_foundR6

/-- COVERAGE OF A RESTRICTED RUN WITH W6 (from `RCov.coverageR`). -/
theorem coverageR6 (hwf : P.WF)
    (hE : EmitContractOn (DR6 P counted L demand emit sat restrict recs sinks roots) emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict) (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i, DR6 P counted L demand emit sat restrict recs sinks roots (.init M i) → i.covers l0 →
      (∃ f, DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f) ∧
        den i f.fact l0 l ∧
        FlowR P (summaryDemand P (DR6 P counted L demand emit sat restrict recs sinks roots))
          M l0 n l) ∨
      DR6 P counted L demand emit sat restrict recs sinks roots (.req M i l0.mark) := by
  have hup := fun o (h : DR P counted L demand emit sat restrict recs sinks roots o) =>
    DR_le_DR6 P counted L demand emit sat restrict recs sinks roots hRL hJ h
  have hE0 : EmitContractOn (DR P counted L demand emit sat restrict recs sinks roots) emit sat :=
    fun m d a l hA hd ha => hE m d a l (hup _ hA) hd ha
  intro i hi hc
  have hi0 : DR P counted L demand emit sat restrict recs sinks roots (.init M i) :=
    DR6_le_DR P counted L demand emit sat restrict recs sinks roots hRL hJ hi
  rcases RCov.coverageR P counted L demand emit sat restrict recs sinks roots hwf hE0 hS hR hfl
    i hi0 hc with ⟨f, hf, hd, hfr⟩ | hr
  · obtain ⟨g, hg, hle⟩ := hup _ hf
    exact Or.inl ⟨g, hg, by rw [← hle.fact]; exact hd,
      RCov.flowR_mono (fun _ _ h => summaryDemand_of_up hup h) hfr⟩
  · exact Or.inr (hup _ hr)

#print axioms coverageR6

end SoundR

/-- The spec rules (`emitM`, `satI`, `restrictU`) satisfy the hypotheses of the restricted
    simulation. -/
theorem DR_up_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (o : Obj)
    (h : DR P counted L demand emitM satI restrictU recs sinks roots o) :
    Up (DR6 P counted L demand emitM satI restrictU recs sinks roots) o :=
  DR_le_DR6 P counted L demand emitM satI restrictU recs sinks roots restrictU_LE
    (DR_eic P counted L demand emitM satI restrictU recs sinks roots RCore.emitM_copies) h

theorem DR_down_M {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (o : Obj)
    (h : DR6 P counted L demand emitM satI restrictU recs sinks roots o) :
    Down (DR P counted L demand emitM satI restrictU recs sinks roots) o :=
  DR6_le_DR P counted L demand emitM satI restrictU recs sinks roots restrictU_LE
    (DR_eic P counted L demand emitM satI restrictU recs sinks roots RCore.emitM_copies) h

/-- THE VULNERABILITY THEOREM OF A RESTRICTED RUN OF THE SPEC RULES WITH W6 (from
    `RMain.vuln_found_M`). -/
theorem vuln_found_M6 {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DR6 P counted L demand emitM satI restrictU recs sinks roots (.vuln M n s b)) ∧
    ReachR P (summaryDemand P (DR6 P counted L demand emitM satI restrictU recs sinks roots))
      roots M n l := by
  obtain ⟨⟨b, hb⟩, hRR⟩ := RMain.vuln_found_M (counted := counted) (L := L) (recs := recs) hwf hRe hs hT hsc
  obtain ⟨b', hb', _⟩ := DR_up_M _ hb
  exact ⟨⟨b', hb'⟩, RCov.reachR_mono (fun _ _ h => summaryDemand_of_up DR_up_M h) hRR⟩

#print axioms vuln_found_M6

/-! ## 12. Exactness -/

section Exact1
variable {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- EVERY NORMAL-LAYER EDGE OF `D6` IS A NORMAL-LAYER EDGE OF `D`. -/
theorem D6_normal (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : D6 P counted L α sinks roots (.edge M i n f)) (hf : f.demand = false) :
    D P counted L α sinks roots (.edge M i n f) := by
  obtain ⟨g, hg, hle⟩ := D6_le_D P counted L α sinks roots hS h
  rw [hle.eq_of_normal hf]
  exact hg

#print axioms D6_normal

/-- THE EXACTNESS THEOREM WITH W6 (from `Exact.edge_exact`). -/
theorem edge_exact6 (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6 P counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  Exact.edge_exact hmw hup (D6_normal hS h ha) ha hd

#print axioms edge_exact6

/-- THE EXACTNESS THEOREM FOR VALID LOCATIONS WITH W6 (from `Exact.edge_exact_valid`). -/
theorem edge_exact_valid6 {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : D6 P counted L α sinks roots (.edge M i n f)) (ha : f.demand = false)
    (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  Exact.edge_exact_valid hmw hv hbo (D6_normal hS h ha) ha hd hok

#print axioms edge_exact_valid6

end Exact1

section ExactR
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → (PFact × AFact) → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- EVERY NORMAL-LAYER EDGE OF `DR6` IS A NORMAL-LAYER EDGE OF `DR`. -/
theorem DR6_normal (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (hf : f.demand = false) : DR P counted L demand emit sat restrict recs sinks roots (.edge M i n f) := by
  obtain ⟨g, hg, hle⟩ := DR6_le_DR P counted L demand emit sat restrict recs sinks roots hRL hJ h
  rw [hle.eq_of_normal hf]
  exact hg

#print axioms DR6_normal

/-- THE EXACTNESS THEOREM OF A RESTRICTED RUN WITH W6 (from `RExact.edge_exactR`). -/
theorem edge_exactR6 (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P) (hsat : RExact.SatMark sat)
    (hsub : RestrictSub restrict) (hrecs : RExact.RecsExact P recs) (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) : Flow P M l0 n l :=
  RExact.edge_exactR hmw hup hsat hsub hrecs (DR6_normal hRL hJ h ha) ha hd

#print axioms edge_exactR6

/-- THE EXACTNESS THEOREM OF A RESTRICTED RUN WITH W6 FOR VALID LOCATIONS. -/
theorem edge_exactR_valid6 {ok : Loc → Prop} (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok)
    (hbo : Exact.BackOK P ok) (hsat : RExact.SatMark sat) (hsub : RestrictSub restrict)
    (hrecs : RExact.RecsExactV P ok recs) (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {i : PFact} {n : Node} {f : AFact} {l0 l : Loc}
    (h : DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f))
    (ha : f.demand = false) (hd : den i f.fact l0 l) (hok : ok l) : Flow P M l0 n l ∧ ok l0 :=
  RExact.edge_exactR_valid hmw hv hbo hsat hsub hrecs (DR6_normal hRL hJ h ha) ha hd hok

#print axioms edge_exactR_valid6

end ExactR

/-! ## 13. Confirmation -/

section Conf1Def
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

/-- The normal-layer support of `Confirmed.Sup`, computed in `D6`. -/
inductive Sup6 : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → Sup6 M zeroFact
  | call {M i n f n' c e a j} :
      Sup6 M i → D6 P counted L α sinks roots (.edge M i n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      D6 P counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, D6 P counted L α sinks roots (.req c.callee k t) ∧ a.fact.kind = .exact ∧
          a.fact.mark = .conc t ∧ j = answerInit k a.fact t ∧ j = a.fact)) →
      Sup6 c.callee j

/-- A confirmed vulnerability of `D6` (support and sink edge computed in `D6`). -/
def Confirmed6 (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D6 P counted L α sinks roots (.edge M i n f) ∧ Sup6 P counted L α sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end Conf1Def

section Conf1
variable {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

theorem sup_of_sup6 (hS : SummaryStar P (D P counted L α sinks roots)) {M : MethodId}
    {i : PFact} (h : Sup6 P counted L α sinks roots M i) :
    Confirmed.Sup P counted L α sinks roots M i := by
  induction h with
  | root hM => exact Confirmed.Sup.root hM
  | call _ hD hfd hE he ha had hJ hj ih =>
    refine Confirmed.Sup.call ih (D6_normal hS hD hfd) hfd hE he ha had
      (D6_le_D P counted L α sinks roots hS hJ) ?_
    rcases hj with h0 | ⟨k, t, hk, h1, h2, h3, h4⟩
    · exact Or.inl h0
    · exact Or.inr ⟨k, t, D6_le_D P counted L α sinks roots hS hk, h1, h2, h3, h4⟩

/-- A CONFIRMED VULNERABILITY OF `D6` IS A CONFIRMED VULNERABILITY OF `D`. -/
theorem confirmed_of_confirmed6 (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {n : Node} {s : PFact} (h : Confirmed6 P counted L α sinks roots M n s) :
    Confirmed.Confirmed P counted L α sinks roots M n s := by
  obtain ⟨i, f, hD, hSup, hc, hs, hch⟩ := h
  exact ⟨i, f, D6_normal hS hD (Exact.complete_demand hc), sup_of_sup6 hS hSup, hc, hs, hch⟩

#print axioms confirmed_of_confirmed6

/-- A CONFIRMED VULNERABILITY OF `D6` IS REAL (from `Confirmed.confirmed_real`). -/
theorem confirmed_real6 (hwf : P.WF) (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hS : SummaryStar P (D P counted L α sinks roots))
    {M : MethodId} {n : Node} {s : PFact} (h : Confirmed6 P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  Confirmed.confirmed_real hwf hmw hup (confirmed_of_confirmed6 hS h)

#print axioms confirmed_real6

/-- The same for valid locations (from `Confirmed.confirmed_real_valid`). -/
theorem confirmed_real_valid6 {ok : Loc → Prop} (hwf : P.WF) (hmw : Exact.MarkWF P)
    (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hS : SummaryStar P (D P counted L α sinks roots)) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l) (h : Confirmed6 P counted L α sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  Confirmed.confirmed_real_valid hwf hmw hv hbo hok (confirmed_of_confirmed6 hS h)

#print axioms confirmed_real_valid6

end Conf1

section ConfRDef
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The generalized support of `RExact.SupM`, computed in `DR6`. -/
inductive SupM6 : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → SupM6 M zeroFact
  | call {M i n f n' c e a j} :
      SupM6 M i →
      DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f) →
      f.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DR6 P counted L demand emit sat restrict recs sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (a.fact.kind = .exact ∧ (∃ t, a.fact.mark = .conc t) ∧ j = a.fact)) →
      SupM6 c.callee j

/-- A confirmed vulnerability of `DR6` (support and sink edge computed in `DR6`). -/
def ConfirmedM6 (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, DR6 P counted L demand emit sat restrict recs sinks roots (.edge M i n f) ∧
    SupM6 P counted L demand emit sat restrict recs sinks roots M i ∧
    f.complete = true ∧ (M, n, s) ∈ sinks ∧ check i f s = .triggered

end ConfRDef

section ConfR
variable {P : Program} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → (PFact × AFact) → Prop}
  {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

theorem supM_of_supM6 (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {i : PFact}
    (h : SupM6 P counted L demand emit sat restrict recs sinks roots M i) :
    RExact.SupM P counted L demand emit sat restrict recs sinks roots M i := by
  induction h with
  | root hM => exact RExact.SupM.root hM
  | call _ hD hfd hE he ha had hJ' hj ih =>
    exact RExact.SupM.call ih (DR6_normal hRL hJ hD hfd) hfd hE he ha had
      (DR6_le_DR P counted L demand emit sat restrict recs sinks roots hRL hJ hJ') hj

/-- A CONFIRMED VULNERABILITY OF `DR6` IS A CONFIRMED VULNERABILITY OF `DR`. -/
theorem confirmedM_of_confirmedM6 (hRL : RestrictLE restrict)
    (hJ : ExactInitConc (DR P counted L demand emit sat restrict recs sinks roots))
    {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM6 P counted L demand emit sat restrict recs sinks roots M n s) :
    RExact.ConfirmedM P counted L demand emit sat restrict recs sinks roots M n s := by
  obtain ⟨i, f, hD, hSup, hc, hs, hch⟩ := h
  exact ⟨i, f, DR6_normal hRL hJ hD (Exact.complete_demand hc), supM_of_supM6 hRL hJ hSup, hc, hs,
    hch⟩

#print axioms confirmedM_of_confirmedM6

end ConfR

/-- A CONFIRMED VULNERABILITY OF A RESTRICTED RUN OF THE SPEC RULES WITH W6 IS REAL (from
    `RMain.confirmed_real_M`). -/
theorem confirmed_real_M6 {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hmw : Exact.MarkWF P) (hup : Exact.FiltUp P)
    (hrecs : RExact.RecsExact P recs) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedM6 P counted L demand emitM satI restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RMain.confirmed_real_M hmw hup hrecs (confirmedM_of_confirmedM6 restrictU_LE
    (DR_eic P counted L demand emitM satI restrictU recs sinks roots RCore.emitM_copies) h)

#print axioms confirmed_real_M6

/-- The same for valid locations (from `RMain.confirmed_real_M_valid`). -/
theorem confirmed_real_M6_valid {P : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {ok : Loc → Prop}
    (hmw : Exact.MarkWF P) (hv : Exact.FiltValid P ok) (hbo : Exact.BackOK P ok)
    (hrecs : RExact.RecsExactV P ok recs) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedM6 P counted L demand emitM satI restrictU recs sinks roots M n s) :
    ∃ l, Reach P roots M n l ∧ s.covers l :=
  RMain.confirmed_real_M_valid hmw hv hbo hrecs hok (confirmedM_of_confirmedM6 restrictU_LE
    (DR_eic P counted L demand emitM satI restrictU recs sinks roots RCore.emitM_copies) h)

#print axioms confirmed_real_M6_valid

/-! ## 14. The iteration with W6 in every forward run -/

/-- The run sequence with W6 in every forward run: run 0 is `D6` with `policy1`, run `k + 1` is
    `DR6` with the demand `dem k`. -/
def runSeq6 (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D6 P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR6 P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots

section Iter
variable {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- Run `k` without W6 is simulated by run `k` with W6 (a mark-copying emission and a
    restriction that copies the layer). -/
theorem runSeq_up (hem : EmitCopiesMark emit) (hRL : RestrictLE restrict) (k : Nat) (o : Obj)
    (h : RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots k o) :
    Up (runSeq6 P counted Ls dem emit sat restrict recs sinks roots k) o := by
  cases k with
  | zero =>
    exact D_le_D6 P counted (Ls 0) policy1 sinks roots
      (summaryStar_policy P counted (Ls 0) (fun _ => []) sinks roots) h
  | succ k =>
    exact DR_le_DR6 P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots hRL
      (DR_eic P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots hem) h

/-- Run `k` with W6 is simulated by run `k` without W6. -/
theorem runSeq_down (hem : EmitCopiesMark emit) (hRL : RestrictLE restrict) (k : Nat) (o : Obj)
    (h : runSeq6 P counted Ls dem emit sat restrict recs sinks roots k o) :
    Down (RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots k) o := by
  cases k with
  | zero =>
    exact D6_le_D P counted (Ls 0) policy1 sinks roots
      (summaryStar_policy P counted (Ls 0) (fun _ => []) sinks roots) h
  | succ k =>
    exact DR6_le_DR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots hRL
      (DR_eic P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots hem) h

/-- The backward contract does not see W6: it reads the summary demand only. -/
theorem backward_of_backward6 (hem : EmitCopiesMark emit) (hRL : RestrictLE restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq6 P counted Ls dem emit sat restrict recs sinks roots k) (dem k)) (k : Nat) :
    BackwardContract P roots sinks (RCov.runSeq P counted Ls dem emit sat restrict recs sinks roots k)
      (dem k) := by
  intro M n l s T hs hT hc hr
  exact hB k M n l s T hs hT hc
    (RCov.reachR_mono (fun _ _ h => summaryDemand_of_up (runSeq_up hem hRL k) h) hr)

/-- THE ITERATION THEOREM WITH W6 (generic rules, from `RCov.iteration_sound_conc`): if every
    backward step keeps the witnesses that the summaries of the previous W6 run demand
    (contract B), every W6 run reports every real vulnerability. -/
theorem iteration_sound_conc6 (hwf : P.WF) (hE : EmitContractConc emit sat)
    (hcm : EmitCopiesMark emit) (hS : SatContract sat) (hR : RestrictContract restrict)
    (hRL : RestrictLE restrict)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq6 P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq6 P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) := by
  intro k
  obtain ⟨b, hb⟩ := RCov.iteration_sound_conc hwf hE hcm hS hR
    (backward_of_backward6 hcm hRL hB) hRe hs hT hsc k
  obtain ⟨b', hb', _⟩ := runSeq_up hcm hRL k _ hb
  exact ⟨b', hb'⟩

#print axioms iteration_sound_conc6

end Iter

/-- THE ITERATION THEOREM FOR THE SPEC RULES WITH W6 IN EVERY FORWARD RUN (from
    `RMain.iteration_sound_M`). -/
theorem iteration_sound_M6 {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF)
    (hB : ∀ k, BackwardContract P roots sinks
      (runSeq6 P counted Ls dem emitM satI restrictU recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq6 P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  obtain ⟨b, hb⟩ := RMain.iteration_sound_M hwf
    (backward_of_backward6 RCore.emitM_copies restrictU_LE hB) hRe hs hT hsc k
  obtain ⟨b', hb', _⟩ := runSeq_up RCore.emitM_copies restrictU_LE k _ hb
  exact ⟨b', hb'⟩

#print axioms iteration_sound_M6

/-- The run sequence with W6 and the identity backward step. -/
def runSeqId6 (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool)
    (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D6 P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR6 P counted (Ls (k + 1))
      (summaryDemand P (runSeqId6 P counted Ls emit sat restrict recs sinks roots k))
      emit sat restrict (recs k) sinks roots

theorem runSeqId6_eq (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (emit : PFact → PFact → Option PFact) (sat : PFact → PFact → Bool)
    (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) (k : Nat) :
    runSeqId6 P counted Ls emit sat restrict recs sinks roots k =
      runSeq6 P counted Ls
        (fun k => summaryDemand P (runSeqId6 P counted Ls emit sat restrict recs sinks roots k))
        emit sat restrict recs sinks roots k := by
  cases k <;> rfl

/-- THE ITERATION THEOREM FOR THE SPEC RULES WITH W6 AND THE IDENTITY BACKWARD STEP: no
    hypothesis on the backward run. -/
theorem iteration_sound_M6_identity {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqId6 P counted Ls emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [runSeqId6_eq]
  refine iteration_sound_M6 hwf (fun k' => ?_) hRe hs hT hsc k
  show BackwardContract P roots sinks _
    (summaryDemand P (runSeqId6 P counted Ls emitM satI restrictU recs sinks roots k'))
  rw [runSeqId6_eq P counted Ls emitM satI restrictU recs sinks roots k']
  exact RCov.backward_identity P roots sinks _

#print axioms iteration_sound_M6_identity

/-- THE GENERAL ITERATION THEOREM WITH W6 IN EVERY FORWARD RUN (from
    `Backward.iteration_general`). The hypotheses on the hand-off read the W6 runs: their
    reversed summaries (`hdemB`) and their reported sinks (`hseeds`). The backward run itself is
    `Backward.DB` (W6 is not applied there: its zero rules match the zero fact in the normal
    layer, `Backward.zeroAF`, so a raised zero fact is not a layer refinement of `DB`). -/
theorem iteration_general6 {P : Program} (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    {roots : List MethodId} (hX : Backward.ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeq6 P counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeq6 P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P) counted (LB k)
      (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq6 P counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) := by
  have up := runSeq_up (P := P) (counted := counted) (Ls := Ls) (dem := dem) (recs := recs)
    (sinks := sinks) (roots := roots) (sat := satI) RCore.emitM_copies restrictU_LE
  have h := Backward.iteration_general hW hT hmr hNZB hZ hX hk LB demB recsB seeds
    (fun k m d hd => hdemB k m d (revSummaryDemand_of_up (up k) hd))
    (fun k M' n' s' b hv => by
      obtain ⟨b', hb', _⟩ := up k _ hv
      exact hseeds k M' n' s' b' hb')
    hdem hRe hs hT' hsc
  intro k
  obtain ⟨b, hb⟩ := h k
  obtain ⟨b', hb', _⟩ := up k _ hb
  exact ⟨b', hb'⟩

#print axioms iteration_general6

/-! ## 15. The hypothesis stays: a counterexample

  A well-formed program in which the layer of a summary edge changes a FACT (spec §4.3: the
  summary application ORs the layer of the summary edge into the result before the normal
  form). The root `0` binds the zero fact into method `1`. The abstraction gives `i0 = 1.*` in
  method `1` and `jX = 2.$` with the mark `*` in method `2` (a `$` initial fact with an abstract
  mark: `ExactInitConc` fails). Method `1` binds `1.$` (premise mark `*`: S8, `PremConc`, fails)
  to `2.*`, so the caller fact is `2.*/Universe`. Method `2` makes `5.[any]` (an `[any]` target
  on an exact derivation: normal in `D`, demand in `D6`) and then `3.$`. The summary `jX → 3.$`
  is normal in `D` and in the demand layer in `D6`; applied to `2.*/Universe` it gives
  `3.*/Universe` (normal) in `D` and its normal form `3.$` (demand) in `D6`; the binding back
  gives `4.*/Universe` in `D` and `4.$` in `D6`. These are the ONLY edges of `1.*` at the exit
  in each run (`D_good`, `D6_good` compute both closures), so neither run simulates the other. -/
namespace Cex

abbrev i0 : PFact := ⟨1, [], .star (.set []), .star⟩
abbrev jX : PFact := ⟨2, [], .exact, .star⟩
abbrev a0 : PFact := ⟨1, [], .exact, .conc 0⟩
abbrev aU : PFact := ⟨2, [], .star .univ, .star⟩
abbrev b0 : MicroEdge := (⟨0, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
abbrev b1 : MicroEdge := (⟨1, [], .exact, .star⟩, ⟨2, [], .star (.set []), .star⟩)
abbrev b2 : MicroEdge := (⟨3, [], .star (.set []), .star⟩, ⟨4, [], .star (.set []), .star⟩)
abbrev c0 : Call := ⟨1, [0], [b0], []⟩
abbrev c1 : Call := ⟨2, [1], [b1], [b2]⟩
abbrev sA : Stmt := ⟨[2], [(⟨2, [], .exact, .star⟩, ⟨5, [], .any, .star⟩)]⟩
abbrev sB : Stmt := ⟨[5], [(⟨5, [], .star (.set []), .star⟩, ⟨3, [], .exact, .star⟩)]⟩
abbrev Pc : Program := ⟨fun _ => 0, fun _ => 1,
  [(0, 0, .call c0, 1), (1, 0, .call c1, 1), (2, 0, .stmt sA, 2), (2, 2, .stmt sB, 1)]⟩
abbrev αc : MethodId → PFact → PFact := fun m _ => if m = 2 then jX else i0
/-- The exit edge of `1.*` in `D`. -/
abbrev fU : AFact := ⟨⟨4, [], .star .univ, .star⟩, false⟩
/-- The exit edge of `1.*` in `D6`. -/
abbrev fE : AFact := ⟨⟨4, [], .exact, .star⟩, true⟩
abbrev zA : AFact := ⟨zeroFact, false⟩

theorem mem2 {β : Type} {x a b : β} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr h
    · exact absurd h List.not_mem_nil

theorem mem3 {β : Type} {x a b c : β} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (mem2 h)

theorem mem4 {β : Type} {x a b c d : β} (h : x ∈ [a, b, c, d]) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (mem3 h)

theorem mem5 {β : Type} {x a b c d e : β} (h : x ∈ [a, b, c, d, e]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (mem4 h)

theorem mem6 {β : Type} {x a b c d e f : β} (h : x ∈ [a, b, c, d, e, f]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (mem5 h)

theorem pc_edges {x : MethodId × Node × Instr × Node} (h : x ∈ Pc.edges) :
    x = (0, 0, .call c0, 1) ∨ x = (1, 0, .call c1, 1) ∨ x = (2, 0, .stmt sA, 2) ∨
    x = (2, 2, .stmt sB, 1) := mem4 h

theorem wf : Pc.WF where
  stmtTouched := by
    intro M n s n' hE e he
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases List.mem_singleton.mp he with rfl; rfl
    · rcases List.mem_singleton.mp he with rfl; rfl
  toStar := by
    intro M n c n' hE e he
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases List.mem_singleton.mp he with rfl; rfl
    · rcases List.mem_singleton.mp he with rfl; rfl
  fromStar := by
    intro M n c n' hE e he
    rcases pc_edges hE with h | h | h | h <;> cases h
    · exact absurd he List.not_mem_nil
    · rcases List.mem_singleton.mp he with rfl; rfl
  filtPrefix := by
    intro M n b may n' hE
    rcases pc_edges hE with h | h | h | h <;> cases h

/-- The objects of each closure: `b = false` for `D`, `b = true` for `D6`. -/
abbrev goodEdges (b : Bool) : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, zA), (1, i0, 0, ⟨i0, false⟩), (2, jX, 0, ⟨jX, false⟩),
   (2, jX, 2, ⟨⟨5, [], .any, .star⟩, b⟩), (2, jX, 1, ⟨⟨3, [], .exact, .star⟩, b⟩),
   (1, i0, 1, if b then fE else fU)]
abbrev goodInits : List (MethodId × PFact) := [(0, zeroFact), (1, i0), (2, jX)]
abbrev goodAdded : List (MethodId × PFact) := [(1, a0), (2, aU)]

def Good (b : Bool) : Obj → Prop
  | .init M i => (M, i) ∈ goodInits
  | .edge M i n f => (M, i, n, f) ∈ goodEdges b
  | .added M a => (M, a) ∈ goodAdded
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

section Runs
variable (counted : Acc → Bool) (L : Nat)

/-- The closure `D6` of the program, computed: its objects are the objects of `Good true`. -/
theorem D6_good {o : Obj} (h : D6 Pc counted L αc [] [0] o) : Good true o := by
  induction h with
  | root hM =>
    rcases List.mem_singleton.mp hM with rfl
    show (0, zeroFact) ∈ goodInits
    decide
  | @start M i _ ih =>
    have ih' : (M, i) ∈ goodInits := ih
    rcases mem3 ih' with h | h | h <;> cases h
    · show (0, zeroFact, 0, zA) ∈ goodEdges true; decide
    · show (1, i0, 0, (⟨i0, false⟩ : AFact)) ∈ goodEdges true; decide
    · show (2, jX, 0, (⟨jX, false⟩ : AFact)) ∈ goodEdges true; decide
  | @step M i n f n' s f' _ hE hf ih =>
    have ih' : (M, i, n, f) ∈ goodEdges true := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      have hf' : f' ∈ ([⟨⟨5, [], .any, .star⟩, false⟩] : List AFact) := hf
      rcases List.mem_singleton.mp hf' with rfl
      show (2, jX, 2, (⟨⟨5, [], .any, .star⟩, true⟩ : AFact)) ∈ goodEdges true
      decide
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      have hf' : f' ∈ ([⟨⟨3, [], .exact, .star⟩, true⟩] : List AFact) := hf
      rcases List.mem_singleton.mp hf' with rfl
      show (2, jX, 1, (⟨⟨3, [], .exact, .star⟩, true⟩ : AFact)) ∈ goodEdges true
      decide
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have ih' : (M, i, n, f) ∈ goodEdges true := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd (ht : t ∈ ([] : List Mark)) List.not_mem_nil
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd (ht : t ∈ ([] : List Mark)) List.not_mem_nil
  | @pass M i n f n' c _ hE hm ih =>
    have ih' : (M, i, n, f) ∈ goodEdges true := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd hm (by decide)
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd hm (by decide)
  | @added M i n f n' c e a _ hE he ha ih =>
    have ih' : (M, i, n, f) ∈ goodEdges true := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he with rfl
      have ha' : a ∈ ([⟨a0, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      show (1, a0) ∈ goodAdded; decide
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he with rfl
      have ha' : a ∈ ([⟨aU, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      show (2, aU) ∈ goodAdded; decide
  | @initA m a _ ih =>
    have ih' : (m, a) ∈ goodAdded := ih
    rcases mem2 ih' with h | h <;> cases h
    · show (1, i0) ∈ goodInits; decide
    · show (2, jX) ∈ goodInits; decide
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihF ihJ ihG =>
    have ihF' : (M, i, n, f) ∈ goodEdges true := ihF
    rcases pc_edges hE with h | h | h | h <;> cases h
    · exact absurd he2 List.not_mem_nil
    · rcases mem6 ihF' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he1 with rfl
      have ha' : a ∈ ([⟨aU, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      have ihJ' : (2, j) ∈ goodInits := ihJ
      rcases mem3 ihJ' with h | h | h <;> cases h
      have ihG' : (2, jX, 1, g) ∈ goodEdges true := ihG
      rcases mem6 ihG' with h | h | h | h | h | h <;> cases h
      have hr2 : r ∈ ([⟨⟨3, [], .exact, .star⟩, true⟩] : List AFact) := hr
      rcases List.mem_singleton.mp hr2 with rfl
      rcases List.mem_singleton.mp he2 with rfl
      have hr2' : r' ∈ ([fE] : List AFact) := hr'
      rcases List.mem_singleton.mp hr2' with rfl
      show (1, i0, 1, fE) ∈ goodEdges true
      decide
  | reqSink _ hs _ _ => exact absurd hs List.not_mem_nil
  | answer _ _ _ _ ihR _ => exact False.elim ihR
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact False.elim ihR
  | vuln _ hs _ _ => exact absurd hs List.not_mem_nil
  | clean _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h
  | reqClean _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h
  | filt _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h

/-- The closure `D` of the program, computed: its objects are the objects of `Good false`. -/
theorem D_good {o : Obj} (h : D Pc counted L αc [] [0] o) : Good false o := by
  induction h with
  | root hM =>
    rcases List.mem_singleton.mp hM with rfl
    show (0, zeroFact) ∈ goodInits
    decide
  | @start M i _ ih =>
    have ih' : (M, i) ∈ goodInits := ih
    rcases mem3 ih' with h | h | h <;> cases h
    · show (0, zeroFact, 0, zA) ∈ goodEdges false; decide
    · show (1, i0, 0, (⟨i0, false⟩ : AFact)) ∈ goodEdges false; decide
    · show (2, jX, 0, (⟨jX, false⟩ : AFact)) ∈ goodEdges false; decide
  | @step M i n f n' s f' _ hE hf ih =>
    have ih' : (M, i, n, f) ∈ goodEdges false := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      have hf' : f' ∈ ([⟨⟨5, [], .any, .star⟩, false⟩] : List AFact) := hf
      rcases List.mem_singleton.mp hf' with rfl
      show (2, jX, 2, (⟨⟨5, [], .any, .star⟩, false⟩ : AFact)) ∈ goodEdges false
      decide
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      have hf' : f' ∈ ([⟨⟨3, [], .exact, .star⟩, false⟩] : List AFact) := hf
      rcases List.mem_singleton.mp hf' with rfl
      show (2, jX, 1, (⟨⟨3, [], .exact, .star⟩, false⟩ : AFact)) ∈ goodEdges false
      decide
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have ih' : (M, i, n, f) ∈ goodEdges false := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd (ht : t ∈ ([] : List Mark)) List.not_mem_nil
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd (ht : t ∈ ([] : List Mark)) List.not_mem_nil
  | @pass M i n f n' c _ hE hm ih =>
    have ih' : (M, i, n, f) ∈ goodEdges false := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd hm (by decide)
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      exact absurd hm (by decide)
  | @added M i n f n' c e a _ hE he ha ih =>
    have ih' : (M, i, n, f) ∈ goodEdges false := ih
    rcases pc_edges hE with h | h | h | h <;> cases h
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he with rfl
      have ha' : a ∈ ([⟨a0, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      show (1, a0) ∈ goodAdded; decide
    · rcases mem6 ih' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he with rfl
      have ha' : a ∈ ([⟨aU, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      show (2, aU) ∈ goodAdded; decide
  | @initA m a _ ih =>
    have ih' : (m, a) ∈ goodAdded := ih
    rcases mem2 ih' with h | h <;> cases h
    · show (1, i0) ∈ goodInits; decide
    · show (2, jX) ∈ goodInits; decide
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ hr he2 hr' ihF ihJ ihG =>
    have ihF' : (M, i, n, f) ∈ goodEdges false := ihF
    rcases pc_edges hE with h | h | h | h <;> cases h
    · exact absurd he2 List.not_mem_nil
    · rcases mem6 ihF' with h | h | h | h | h | h <;> cases h
      rcases List.mem_singleton.mp he1 with rfl
      have ha' : a ∈ ([⟨aU, false⟩] : List AFact) := ha
      rcases List.mem_singleton.mp ha' with rfl
      have ihJ' : (2, j) ∈ goodInits := ihJ
      rcases mem3 ihJ' with h | h | h <;> cases h
      have ihG' : (2, jX, 1, g) ∈ goodEdges false := ihG
      rcases mem6 ihG' with h | h | h | h | h | h <;> cases h
      have hr2 : r ∈ ([⟨⟨3, [], .star .univ, .star⟩, false⟩] : List AFact) := hr
      rcases List.mem_singleton.mp hr2 with rfl
      rcases List.mem_singleton.mp he2 with rfl
      have hr2' : r' ∈ ([fU] : List AFact) := hr'
      rcases List.mem_singleton.mp hr2' with rfl
      show (1, i0, 1, fU) ∈ goodEdges false
      decide
  | reqSink _ hs _ _ => exact absurd hs List.not_mem_nil
  | answer _ _ _ _ ihR _ => exact False.elim ihR
  | reqUp _ _ _ _ _ _ _ _ ihR _ => exact False.elim ihR
  | vuln _ hs _ _ => exact absurd hs List.not_mem_nil
  | clean _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h
  | reqClean _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h
  | filt _ hE _ _ => rcases pc_edges hE with h | h | h | h <;> cases h

/-- The derivation in `D` up to the exit edge of method `2`. -/
theorem d5 : D Pc counted L αc [] [0] (.edge 1 i0 0 ⟨i0, false⟩) := by
  have h1 : D Pc counted L αc [] [0] (.init 0 zeroFact) := D.root (List.Mem.head _)
  have h2 : D Pc counted L αc [] [0] (.edge 0 zeroFact 0 zA) := D.start h1
  have h3 : D Pc counted L αc [] [0] (.added 1 a0) :=
    D.added (n' := 1) (c := c0) (e := b0) (a := ⟨a0, false⟩) h2 (List.Mem.head _)
      (List.Mem.head _) (by decide)
  have h4 : D Pc counted L αc [] [0] (.init 1 i0) := D.initA h3
  exact D.start h4

theorem d7 : D Pc counted L αc [] [0] (.init 2 jX) := by
  have h6 : D Pc counted L αc [] [0] (.added 2 aU) :=
    D.added (n' := 1) (c := c1) (e := b1) (a := ⟨aU, false⟩) (d5 counted L)
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide)
  exact D.initA h6

theorem d10 : D Pc counted L αc [] [0] (.edge 2 jX 1 ⟨⟨3, [], .exact, .star⟩, false⟩) := by
  have h8 : D Pc counted L αc [] [0] (.edge 2 jX 0 ⟨jX, false⟩) := D.start (d7 counted L)
  have h9 : D Pc counted L αc [] [0] (.edge 2 jX 2 ⟨⟨5, [], .any, .star⟩, false⟩) :=
    D.step (s := sA) h8 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (List.Mem.head _ : (⟨⟨5, [], .any, .star⟩, false⟩ : AFact) ∈
        [(⟨⟨5, [], .any, .star⟩, false⟩ : AFact)])
  exact D.step (s := sB) h9 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.head _))))
    (List.Mem.head _ : (⟨⟨3, [], .exact, .star⟩, false⟩ : AFact) ∈
      [(⟨⟨3, [], .exact, .star⟩, false⟩ : AFact)])

/-- `D` has the normal exit edge `1.* → 4.*/Universe`. -/
theorem d_fU : D Pc counted L αc [] [0] (.edge 1 i0 1 fU) :=
  D.ret (n' := 1) (c := c1) (e1 := b1) (a := ⟨aU, false⟩) (j := jX)
    (g := ⟨⟨3, [], .exact, .star⟩, false⟩) (r := ⟨⟨3, [], .star .univ, .star⟩, false⟩) (e2 := b2)
    (r' := fU) (d5 counted L) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide)
    (d7 counted L) (by decide) (d10 counted L) (by decide) (List.Mem.head _) (by decide)

/-- `D6` has the demand exit edge `1.* → 4.$`. -/
theorem d6_fE : D6 Pc counted L αc [] [0] (.edge 1 i0 1 fE) := by
  have h1 : D6 Pc counted L αc [] [0] (.init 0 zeroFact) := D6.root (List.Mem.head _)
  have h2 : D6 Pc counted L αc [] [0] (.edge 0 zeroFact 0 zA) := D6.start h1
  have h3 : D6 Pc counted L αc [] [0] (.added 1 a0) :=
    D6.added (n' := 1) (c := c0) (e := b0) (a := ⟨a0, false⟩) h2 (List.Mem.head _)
      (List.Mem.head _) (by decide)
  have h4 : D6 Pc counted L αc [] [0] (.init 1 i0) := D6.initA h3
  have h5 : D6 Pc counted L αc [] [0] (.edge 1 i0 0 ⟨i0, false⟩) := D6.start h4
  have h6 : D6 Pc counted L αc [] [0] (.added 2 aU) :=
    D6.added (n' := 1) (c := c1) (e := b1) (a := ⟨aU, false⟩) h5
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide)
  have h7 : D6 Pc counted L αc [] [0] (.init 2 jX) := D6.initA h6
  have h8 : D6 Pc counted L αc [] [0] (.edge 2 jX 0 ⟨jX, false⟩) := D6.start h7
  have h9 : D6 Pc counted L αc [] [0] (.edge 2 jX 2 ⟨⟨5, [], .any, .star⟩, true⟩) :=
    D6.step (s := sA) (f' := ⟨⟨5, [], .any, .star⟩, false⟩) h8
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (List.Mem.head _ : (⟨⟨5, [], .any, .star⟩, false⟩ : AFact) ∈
        [(⟨⟨5, [], .any, .star⟩, false⟩ : AFact)])
  have h10 : D6 Pc counted L αc [] [0] (.edge 2 jX 1 ⟨⟨3, [], .exact, .star⟩, true⟩) :=
    D6.step (s := sB) (f' := ⟨⟨3, [], .exact, .star⟩, true⟩) h9
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
      (List.Mem.head _ : (⟨⟨3, [], .exact, .star⟩, true⟩ : AFact) ∈
        [(⟨⟨3, [], .exact, .star⟩, true⟩ : AFact)])
  exact D6.ret (n' := 1) (c := c1) (e1 := b1) (a := ⟨aU, false⟩) (j := jX)
    (g := ⟨⟨3, [], .exact, .star⟩, true⟩) (r := ⟨⟨3, [], .exact, .star⟩, true⟩) (e2 := b2)
    (r' := fE) h5 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) (by decide) h7
    (by decide) h10 (by decide) (List.Mem.head _) (by decide)

/-- THE COUNTEREXAMPLE. A well-formed program whose `D` has the normal exit edge `1.* → 4.*/U`
    and whose `D6` has, at the same place, only the demand edge `1.* → 4.$`: W6 changes a FACT,
    not only a layer, and neither closure simulates the other. The program breaks both
    sufficient conditions (`ExactInitConc`, and S8 = `PremConc` of `Invariant.no_univ_star`), and
    `SummaryStar` fails. -/
theorem cex_w6_changes_fact :
    Pc.WF ∧
    D Pc counted L αc [] [0] (.edge 1 i0 1 fU) ∧
    D6 Pc counted L αc [] [0] (.edge 1 i0 1 fE) ∧
    (∀ f, D Pc counted L αc [] [0] (.edge 1 i0 1 f) → f = fU) ∧
    (∀ g, D6 Pc counted L αc [] [0] (.edge 1 i0 1 g) → g = fE) ∧
    fU.fact ≠ fE.fact ∧
    ¬ SummaryStar Pc (D Pc counted L αc [] [0]) ∧
    ¬ ExactInitConc (D Pc counted L αc [] [0]) ∧
    ¬ Invariant.AllEdges Pc Invariant.PremConc ∧
    ¬ (∀ o, D Pc counted L αc [] [0] o → Up (D6 Pc counted L αc [] [0]) o) ∧
    ¬ (∀ o, D6 Pc counted L αc [] [0] o → Down (D Pc counted L αc [] [0]) o) := by
  have hD : ∀ f, D Pc counted L αc [] [0] (.edge 1 i0 1 f) → f = fU := by
    intro f h
    have h' : (1, i0, 1, f) ∈ goodEdges false := D_good counted L h
    rcases mem6 h' with h | h | h | h | h | h <;> cases h
    rfl
  have hD6 : ∀ g, D6 Pc counted L αc [] [0] (.edge 1 i0 1 g) → g = fE := by
    intro g h
    have h' : (1, i0, 1, g) ∈ goodEdges true := D6_good counted L h
    rcases mem6 h' with h | h | h | h | h | h <;> cases h
    rfl
  have hne : ¬ LE fU fE := by
    intro h
    rcases h with h | ⟨h, _⟩
    · cases h
    · cases h
  refine ⟨wf, d_fU counted L, d6_fE counted L, hD, hD6, by decide, ?_, ?_, ?_, ?_, ?_⟩
  · intro hS
    have h := hS (f := ⟨i0, false⟩) (c := c1) (e1 := b1) (a := ⟨aU, false⟩) (j := jX)
      (g := ⟨⟨3, [], .exact, .star⟩, false⟩) (x := ⟨⟨3, [], .star .univ, .star⟩, false⟩)
      (n' := 1) (d5 counted L) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _)
      (by decide) (d7 counted L) (by decide) (d10 counted L) (by decide) rfl
    cases h
  · intro hJ
    obtain ⟨t, ht⟩ := hJ 2 jX (d7 counted L) rfl
    cases ht
  · intro hA
    obtain ⟨t, ht⟩ := hA.2.1 1 0 c1 1 (List.Mem.tail _ (List.Mem.head _)) b1 (List.Mem.head _) rfl
    cases ht
  · intro hup
    obtain ⟨g, hg, hle⟩ := hup _ (d_fU counted L)
    rw [hD6 g hg] at hle
    exact hne hle
  · intro hdown
    obtain ⟨f, hf, hle⟩ := hdown _ (d6_fE counted L)
    rw [hD f hf] at hle
    exact hne hle

#print axioms cex_w6_changes_fact

/-- W6 can REMOVE a record: the exit edge `2.$ → 3.$` of method `2` is complete in `D` (it comes
    from the normal `[any]` fact `5.[any]`), and every edge of `D6` at that place is in the demand
    layer. -/
theorem cex_record_lost :
    D Pc counted L αc [] [0] (.edge 2 jX 1 ⟨⟨3, [], .exact, .star⟩, false⟩) ∧
    (⟨⟨3, [], .exact, .star⟩, false⟩ : AFact).complete = true ∧
    ∀ g, D6 Pc counted L αc [] [0] (.edge 2 jX 1 g) → g.demand = true := by
  refine ⟨d10 counted L, rfl, fun g h => ?_⟩
  have h' : (2, jX, 1, g) ∈ goodEdges true := D6_good counted L h
  rcases mem6 h' with h | h | h | h | h | h <;> cases h
  rfl

#print axioms cex_record_lost

end Runs

end Cex

end ApSpec.W6
