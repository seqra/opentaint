/-
  ApSpec.AnyTaintExCov — the SOUNDNESS of the refined forward model with the EXCLUSION of the
  `[any-taint]` conclusion (decision F69, DESIGN §6, amendment A2).

  The definitions are in `AnyTaintExDefs.lean` (namespace `ApSpec.AnyTaintEx`): the annotated fact
  `XFact`, the pair relation `denX`, the refined operations (`applyEdgeX`, `transferX`,
  `applySummaryX`, `cleanResX`, `limitFX`, `startX`, `emitX`, `satX`, `restrictX`, `checkX`) and the
  refined closures `D6X` (run 1) and `DRX` / `DRXs` (the restricted forward run). This file proves:

  1. THE LOCAL LEMMAS. The pair relation splits into the base pair relation and two location
     conditions (`denX_iff`, `Adm`). THE CORE LEMMA `applyEdgeX_sound`: the refined core operation
     covers the composition of the refined fact relation with the refined edge relation, or raises
     the request (the rows of A2: an exclusion edge at `r = []` gives `E ∪ …`, the case above gives
     the edge exclusion, the case below keeps `E`; `annX_admits`). Then `bindX_sound`,
     `transferX_sound`, `applySummaryX_sound`, `limitFX_sound`, `startX_sound`, `cleanResX_sound`
     (with `partX_sound`: the `atAndBelow` / `below` rows at `P.f`), `checkX_sound`.
  2. THE CONTRACTS of the restricted run with exclusions: C2 `emitX_contract` (`EmitContractX`), C3
     `AnyTaintEx.emitX_copies`, C4 `satX_contract` (`SatContractX`), C5 `restrictX_contractNS`
     (`RestrictContractNSX`: the restriction contract for conclusions without the `*` tail). The
     contract `RestrictContractX` of the definitions file is FALSE for `restrictX`
     (`restrictX_not_contract`, the counterexample of `RCore.restrictU_fails`), and it is not
     needed: a restricted run has no `*` conclusion (`concX_all`).
  3. RUN 1 (`D6X`): the invariants (`edgeInv6X_all`, `req_initial_star6X`), THE COVERAGE THEOREM
     `coverage6X` (with the den-aware witness `FlowRD` of its own summaries, the exclusions
     dropped), `reach_strong6X`, the vulnerability theorems `vuln_found6X`, `vuln_found_policy6X`.
  4. THE RESTRICTED RUN (`DRX`, generic rules; `DRXs`, the spec rules): the concreteness invariant
     `concX_all` (no request, every conclusion concrete and not `*`), THE COVERAGE THEOREM
     `coverageRX` (a demanded flow), `reach_strongRX`, `vuln_foundRX`; the spec instances
     `coverageRXs`, `vuln_foundRXs`.
  5. THE ITERATION: `runSeqX` (run 1 = `D6X`, backward = `Backward.DB`, forward restricted =
     `DRXs`, each forward run read by the backward run with its exclusions DROPPED: `forget6`,
     `forgetX`), `iteration_invariantX`, `iteration_generalX`, THE CITED FORM
     `iteration_reportsX`; with forward seeds `runSeqSrcX`, `iteration_srcX`.
  6. CEGAR on the suggested route of the brief (`CexRoute.route_a_false`): the hand-off of a `DRX`
     run does NOT contain the hand-off of the `DRT` run on the same demand (the exclusion removes
     summaries: a read through an excluded accessor gives nothing), so the iteration is proved
     directly (Part 5), not through `AnyTaintSim.iteration_generalT`; the vector
     `CexRoute.keep_excludes_name` (the keep edge of a strong write does not relate the overwritten
     location, so the refined result need not cover it).

  Not proved here (not needed by the direct route): the simulations `Sim6X`, `SimRX` (and the `In`
  forms) of the definitions file. They go from the refined run to the base run, so they cannot give
  step (a) of the suggested route (Part 6). The exactness and the confirmation of `DRX` are not in
  this file.

  Hypotheses added to the base theorems (each one is reported where it is used):
    * none for run 1 (`coverage6X`, `vuln_found6X`: `Program.WF` and the abstraction contract C1,
      as `Coverage.coverage`);
    * the restricted run with generic rules: `EmitContractX emit sat` (C2), `EmitCopiesMarkX emit`
      (C3), `RestrictContractNSX restrict` (C5 for conclusions without `*`); no `SatContract`
      (the run has no request, so C4 is not read); the spec rules have all three;
    * the iteration: exactly the hypotheses of `Backward.iteration_general` (and of
      `FSeeds.iteration_src` for the seeded form), with the hand-off read from the refined runs.

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintExDefs
import ApSpec.Coverage
import ApSpec.RestrictedCoverage
import ApSpec.RestrictedCore
import ApSpec.Invariant
import ApSpec.Backward
import ApSpec.ForwardSeeds
import ApSpec.AnyTaintSim

namespace ApSpec.AnyTaintExCov
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx
open ApSpec.Backward (FlowRD ReachRD)

/-! ## 1. The local lemmas -/

/-! ### 1.1 The pair relation splits -/

/-- The exclusion `e` admits the continuation of the location `l` below the fact `p` (every
    continuation `σ` with `l.path = p.path ++ σ`; there is at most one). -/
def Adm (p : PFact) (e : Excl) (l : Loc) : Prop :=
  ∀ σ, l.path = p.path ++ σ → e.admits σ = true

theorem adm_empty (p : PFact) (l : Loc) : Adm p Excl.empty l := fun σ _ => admits_empty σ

theorem adm_path {p q : PFact} {e : Excl} {l : Loc} (h : p.path = q.path) (ha : Adm p e l) :
    Adm q e l :=
  fun σ hσ => ha σ (by rw [h]; exact hσ)

theorem adm_of {p : PFact} {e : Excl} {l : Loc} {σ : List Acc} (hp : l.path = p.path ++ σ)
    (h : e.admits σ = true) : Adm p e l := by
  intro σ' hσ'
  have e1 : σ' = σ := List.append_cancel_left (hσ'.symm.trans hp)
  rw [e1]
  exact h

/-- THE SPLIT OF THE PAIR RELATION: an annotated pair is a base pair whose start location the
    premise exclusion admits and whose end location the conclusion exclusion admits. -/
theorem denX_iff {i f : PFact} {iex fex : Excl} {l0 l1 : Loc} :
    denX i iex f fex l0 l1 ↔ den i f l0 l1 ∧ Adm i iex l0 ∧ Adm f fex l1 := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, h10, h11⟩
    exact ⟨⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9⟩, adm_of h6 h10, adm_of h7 h11⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9⟩, ha, hb⟩
    exact ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, ha σ h6, hb τ h7⟩

#print axioms denX_iff

/-- Dropping the conclusion exclusion keeps the pair. -/
theorem denX_drop {i f : PFact} {iex fex : Excl} {l0 l1 : Loc} (h : denX i iex f fex l0 l1) :
    denX i iex f Excl.empty l0 l1 :=
  denX_iff.mpr ⟨(denX_iff.mp h).1, (denX_iff.mp h).2.1, adm_empty _ _⟩

/-- The end location of an annotated pair lies in the admitted location set of the conclusion. -/
theorem denX_end {i f : PFact} {iex fex : Excl} {l0 l1 : Loc} (h : denX i iex f fex l0 l1) :
    coversX f fex l1 := by
  obtain ⟨_, hb1, _, hm1, hps, σ, τ, _, hp1, _, htf, _, hfe⟩ := h
  refine ⟨hb1, ⟨τ, hp1, CoreAux.tailI_of_tailF htf, hfe⟩, ?_⟩
  rw [hm1]
  exact CoreAux.admits_out f.mark l0.mark hps

/-- The location part of `coversX` (marks ignored). -/
def CovLocX (p : PFact) (e : Excl) (l : Loc) : Prop :=
  l.base = p.base ∧ ∃ σ, l.path = p.path ++ σ ∧ tailI p.kind σ ∧ e.admits σ = true

theorem covLoc_of_coversX {p : PFact} {e : Excl} {l : Loc} (h : coversX p e l) : CovLocX p e l :=
  ⟨h.1, h.2.1⟩

theorem covLoc_of_covers {p : PFact} {l : Loc} (h : p.covers l) : CovLocX p Excl.empty l :=
  covLoc_of_coversX (covers_coversX h)

theorem covLoc_of_coversLoc {p : PFact} {l : Loc} (h : p.coversLoc l) : CovLocX p Excl.empty l := by
  obtain ⟨hb, σ, hp, ht⟩ := h
  exact ⟨hb, σ, hp, ht, admits_empty σ⟩

/-- An exclusion that admits `r ++ s` admits `r`. -/
theorem admits_prefix {e : Excl} {r s : List Acc} (h : e.admits (r ++ s) = true) :
    e.admits r = true := by
  cases r with
  | nil => exact CoreAux.admits_nil e
  | cons x r => rw [← admits_cons_append e x r s]; exact h

/-- Two admitted location sets with a common location overlap (`overlapX`, marks ignored). -/
theorem overlapX_of_common {a b : PFact} {aex bex : Excl} {l : Loc}
    (ha : CovLocX a aex l) (hb : CovLocX b bex l) : overlapX a aex b bex = true := by
  obtain ⟨hba, σa, hpa, hta, hea⟩ := ha
  obtain ⟨hbb, σb, hpb, htb, heb⟩ := hb
  have hov : overlapB a b = true :=
    RCore.overlapB_of_commonLoc ⟨hba, σa, hpa, hta⟩ ⟨hbb, σb, hpb, htb⟩
  unfold overlapX
  rw [hov, Bool.true_and]
  have h : a.path ++ σa = b.path ++ σb := by rw [← hpa, ← hpb]
  rcases CoreAux.relate_common h with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, _, hτ⟩
  · rw [hrel]
    rw [hσ] at hea
    exact admits_prefix hea
  · rw [hrel]
    rw [hτ] at heb
    exact admits_prefix heb

#print axioms overlapX_of_common

/-! ### 1.2 Small lemmas on the annotation -/

theorem normX_ex_cases (x : XFact) : (normX x).ex = x.ex ∨ (normX x).ex = Excl.empty := by
  unfold normX
  cases carriesB x.af
  · right; rfl
  · left; rfl

theorem layerX_fact (keep cd : Bool) (y : AFact) : (layerX keep cd y).fact = y.fact := by
  unfold layerX
  cases keep && !cd <;> rfl

theorem norm_path (x : AFact) : x.norm.fact.path = x.fact.path := by
  obtain ⟨⟨b, p, k, m⟩, d⟩ := x
  unfold AFact.norm
  cases k with
  | star e => cases m <;> cases d <;> cases e <;> rfl
  | any => rfl
  | exact => rfl

/-- The result path of the case `below r`: the target path, or the target path with `r` for a
    `*` target. -/
theorem belowCase_path {ck fk tk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (h : belowCase ck fk r tp tk = some (p, k, ap)) :
    (tk.isStar = false → p = tp) ∧ (∀ et, tk = .star et → p = tp ++ r) := by
  unfold belowCase at h
  cases ha : admitsTailB fk r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk with
    | star et =>
      refine ⟨fun h' => Bool.noConfusion h', fun et' _ => ?_⟩
      cases r with
      | cons x r =>
        dsimp only at h
        cases he : et.admits (x :: r) with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true => rw [he, if_pos rfl] at h; cases h; rfl
      | nil =>
        dsimp only at h
        rw [List.append_nil]
        split at h <;> (cases h; rfl)
    | any =>
      cases h
      exact ⟨fun _ => rfl, fun _ h' => Kind.noConfusion h'⟩
    | exact =>
      refine ⟨fun _ => ?_, fun _ h' => Kind.noConfusion h'⟩
      dsimp only at h
      split at h <;> (cases h; rfl)

/-- The result path of the case `above r`: the target path. -/
theorem aboveCase_path {ck fk tk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (h : aboveCase ck fk r tp tk = some (p, k, ap)) : p = tp := by
  unfold aboveCase at h
  cases ha : admitsTailB ck r with
  | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [ha, if_pos rfl] at h
    cases tk <;> (cases h; rfl)

/-! ### 1.3 THE CORE LEMMA -/

/-- THE ANNOTATION ADMITS THE RESULT (the rows of DESIGN A2). For an annotated pair of the fact
    `c` and an annotated pair of the edge `(fr, fex) → (to, tex)` that compose, the annotation
    rules give `some (keep, ex)` (the exclusions do not remove the common location), and the
    exclusion `ex` admits the end location below every base result. The rows: case `below []`
    with a `*/et` target: `E ∪ tailExcl fk ∪ fex ∪ et` (the end continuation is the continuation
    of `c`, which `E` admits, and the continuation of the edge premise, which the edge admits);
    case `below r` (`r ≠ []`) with a `*` target: `E` (the end continuation is the continuation of
    `c`); case `above r` with a `*/et` target: `tailExcl fk ∪ fex ∪ et` (the end continuation is
    the continuation of the edge premise), and `E` admits `r`; an `.any` target: `tex`; a `$`
    target: nothing to admit. -/
theorem annX_admits {ic fr to : PFact} {icx fex tex : Excl} {c : XFact} {l0 l1 l2 : Loc}
    (h1 : denX ic icx c.af.fact c.ex l0 l1) (h2 : denX fr fex to tex l1 l2) :
    ∃ keep ex, annX c fr fex to tex = some (keep, ex) ∧
      ∀ y, y ∈ (applyEdge c.af fr to).facts → Adm y.fact ex l2 := by
  obtain ⟨_, _, _, _, _, σ, τ, _, hp1, _, _, _, hE⟩ := h1
  obtain ⟨_, _, _, _, _, σ', τ', hp1', hp2, hti', htf', hfex, htex⟩ := h2
  have hpath : fr.path ++ σ' = c.af.fact.path ++ τ := by rw [← hp1', hp1]
  -- the path of a base result, from its geometry
  have hres : ∀ y, y ∈ (applyEdge c.af fr to).facts → ∃ p k ap,
      CoreAux.geo c.af.fact.kind fr.kind fr.path c.af.fact.path to.path to.kind = some (p, k, ap) ∧
      y.fact.path = p := by
    intro y hy
    obtain ⟨p, k, ap, m, hg, _, hyr⟩ := Invariant.applyEdge_shape hy
    refine ⟨p, k, ap, hg, ?_⟩
    rw [hyr, norm_path]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ'⟩ | ⟨r, hrel, _, hr, hτ⟩
  · -- case `below r`: the fact is at or below the edge premise; `σ' = r ++ τ`
    have hgeo : ∀ y, y ∈ (applyEdge c.af fr to).facts → ∃ p k ap,
        belowCase c.af.fact.kind fr.kind r to.path to.kind = some (p, k, ap) ∧ y.fact.path = p := by
      intro y hy
      obtain ⟨p, k, ap, hg, hp⟩ := hres y hy
      unfold CoreAux.geo at hg
      rw [hrel] at hg
      exact ⟨p, k, ap, hg, hp⟩
    cases r with
    | nil =>
      have hσ'' : σ' = τ := hσ'
      unfold annX
      rw [hrel]
      dsimp only
      cases htk : to.kind with
      | star et =>
        refine ⟨_, _, rfl, fun y hy τ0 hτ0 => ?_⟩
        obtain ⟨p, k, ap, hb, hp⟩ := hgeo y hy
        rw [htk] at hb htf'
        have hpt : p = to.path ++ [] := (belowCase_path hb).2 et rfl
        obtain ⟨hτ', het⟩ := htf'
        have e1 : τ0 = τ := by
          have e2 : to.path ++ τ' = to.path ++ τ0 := by rw [← hp2, hτ0, hp, hpt, List.append_nil]
          rw [← List.append_cancel_left e2, hτ', hσ'']
        rw [e1, CoreAux.Excl.admits_union, CoreAux.Excl.admits_union, CoreAux.Excl.admits_union,
          hE, tailExcl_admits (by rw [← hσ'']; exact hti'), ← hσ'', hfex, het]
        rfl
      | any =>
        refine ⟨_, _, rfl, fun y hy τ0 hτ0 => ?_⟩
        obtain ⟨p, k, ap, hb, hp⟩ := hgeo y hy
        rw [htk] at hb
        have hpt : p = to.path := (belowCase_path hb).1 rfl
        have e2 : to.path ++ τ' = to.path ++ τ0 := by rw [← hp2, hτ0, hp, hpt]
        rw [← List.append_cancel_left e2]
        exact htex
      | exact => exact ⟨_, _, rfl, fun _ _ τ0 _ => admits_empty τ0⟩
    | cons x r =>
      have hfx : fex.admits (x :: r) = true := by
        rw [hσ'] at hfex
        exact admits_prefix hfex
      unfold annX
      rw [hrel]
      dsimp only
      rw [if_pos hfx]
      cases htk : to.kind with
      | star et =>
        refine ⟨_, _, rfl, fun y hy τ0 hτ0 => ?_⟩
        obtain ⟨p, k, ap, hb, hp⟩ := hgeo y hy
        rw [htk] at hb htf'
        have hpt : p = to.path ++ x :: r := (belowCase_path hb).2 et rfl
        obtain ⟨hτ', _⟩ := htf'
        have e1 : τ0 = τ := by
          have e2 : to.path ++ (x :: r ++ τ) = to.path ++ (x :: r ++ τ0) := by
            rw [← hσ', ← hτ', ← hp2, hτ0, hp, hpt, List.append_assoc]
          exact (List.append_cancel_left (List.append_cancel_left e2)).symm
        rw [e1]
        exact hE
      | any =>
        refine ⟨_, _, rfl, fun y hy τ0 hτ0 => ?_⟩
        obtain ⟨p, k, ap, hb, hp⟩ := hgeo y hy
        rw [htk] at hb
        have hpt : p = to.path := (belowCase_path hb).1 rfl
        have e2 : to.path ++ τ' = to.path ++ τ0 := by rw [← hp2, hτ0, hp, hpt]
        rw [← List.append_cancel_left e2]
        exact htex
      | exact => exact ⟨_, _, rfl, fun _ _ τ0 _ => admits_empty τ0⟩
  · -- case `above r`: the fact is above the edge premise; `τ = r ++ σ'`
    have hEr : c.ex.admits r = true := by
      rw [hτ] at hE
      exact admits_prefix hE
    have hgeo : ∀ y, y ∈ (applyEdge c.af fr to).facts → ∀ τ0, l2.path = y.fact.path ++ τ0 →
        τ0 = τ' := by
      intro y hy τ0 hτ0
      obtain ⟨p, k, ap, hg, hp⟩ := hres y hy
      unfold CoreAux.geo at hg
      rw [hrel] at hg
      have hpt : p = to.path := aboveCase_path hg
      have e2 : to.path ++ τ' = to.path ++ τ0 := by rw [← hp2, hτ0, hp, hpt]
      exact (List.append_cancel_left e2).symm
    unfold annX
    rw [hrel]
    dsimp only
    rw [if_pos hEr]
    cases htk : to.kind with
    | star et =>
      refine ⟨_, _, rfl, fun y hy τ0 hτ0 => ?_⟩
      rw [hgeo y hy τ0 hτ0]
      rw [htk] at htf'
      obtain ⟨hτ', het⟩ := htf'
      rw [CoreAux.Excl.admits_union, CoreAux.Excl.admits_union, hτ', tailExcl_admits hti', hfex,
        het]
      rfl
    | any =>
      exact ⟨_, _, rfl, fun y hy τ0 hτ0 => by rw [hgeo y hy τ0 hτ0]; exact htex⟩
    | exact => exact ⟨_, _, rfl, fun _ _ τ0 _ => admits_empty τ0⟩

#print axioms annX_admits

/-- THE CORE LEMMA OF THE REFINED MODEL (DESIGN A2). `applyEdgeX` covers the composition of the
    refined fact relation (`denX` of the premise `(ic, icx)` and the annotated conclusion `c`) with
    the refined edge relation (`denX` of the edge `(fr, fex) → (to, tex)`: a micro edge or a
    binding with no exclusion, or a summary with the exclusion of a must-premise and of an
    `[any-taint]/E` conclusion), or it raises the request for the entry mark (the fact mark is
    then not concrete). The result has the fact of the base result, and its exclusion admits the
    end location: an exclusion edge at `r = []` gives `E ∪ …`, the case above gives the edge
    exclusion, the case below keeps `E` (`annX_admits`). A location that an exclusion of the fact
    or of the edge removes is not in either relation, so the result need not cover it. -/
theorem applyEdgeX_sound {ic fr to : PFact} {icx fex tex : Excl} {c : XFact} {l0 l1 l2 : Loc}
    (h1 : denX ic icx c.af.fact c.ex l0 l1) (h2 : denX fr fex to tex l1 l2) :
    (∃ r, r ∈ (applyEdgeX c fr fex to tex).facts ∧ denX ic icx r.af.fact r.ex l0 l2) ∨
    ((∀ t, c.af.fact.mark ≠ .conc t) ∧ l0.mark ∈ (applyEdgeX c fr fex to tex).reqs) := by
  obtain ⟨keep, ex, ha, hadm⟩ := annX_admits h1 h2
  have hp0 := (denX_iff.mp h1).2.1
  unfold applyEdgeX
  rw [ha]
  dsimp only
  rcases applyEdge_sound (denX_den h1) (denX_den h2) with ⟨y, hy, hd⟩ | ⟨hs, hq⟩
  · left
    refine ⟨normX ⟨layerX keep c.af.demand y, ex⟩, List.mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
    have hf : (normX ⟨layerX keep c.af.demand y, ex⟩).af.fact = y.fact := by
      rw [normX_af]
      exact layerX_fact keep c.af.demand y
    rw [hf]
    refine denX_iff.mpr ⟨hd, hp0, ?_⟩
    rcases normX_ex_cases ⟨layerX keep c.af.demand y, ex⟩ with he | he
    · rw [he]; exact hadm y hy
    · rw [he]; exact adm_empty _ _
  · right
    exact ⟨hs, hq⟩

#print axioms applyEdgeX_sound

/-! ### 1.4 The other refined operations -/

/-- A call binding (a micro edge with no exclusion). -/
theorem bindX_sound {ic : PFact} {icx : Excl} {c : XFact} {e : MicroEdge} {l0 l1 l2 : Loc}
    (h1 : denX ic icx c.af.fact c.ex l0 l1) (h2 : den e.1 e.2 l1 l2) :
    (∃ r, r ∈ (bindX c e).facts ∧ denX ic icx r.af.fact r.ex l0 l2) ∨
    ((∀ t, c.af.fact.mark ≠ .conc t) ∧ l0.mark ∈ (bindX c e).reqs) :=
  applyEdgeX_sound h1 (den_denX h2)

#print axioms bindX_sound

/-- A mark-agnostic binding raises no request. -/
theorem bindX_noreq {c : XFact} {e : MicroEdge} (h : e.1.mark = .star) {t : Mark} :
    t ∉ (bindX c e).reqs := by
  intro ht
  have h' := applyEdgeX_reqs (fr := e.1) (to := e.2) (fex := Excl.empty) (tex := Excl.empty) ht
  rw [applyEdge_reqs_of_star h] at h'
  exact List.not_mem_nil h'

/-- The binding into the callee (S10: mark agnostic) covers the pair, with no request. -/
theorem bind_inX {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he1 : e ∈ c.toCallee)
    {i : PFact} {iex : Excl} {f : XFact} {l0 l l1 : Loc}
    (hd : denX i iex f.af.fact f.ex l0 l) (hd1 : den e.1 e.2 l l1) :
    ∃ a, a ∈ (bindX f e).facts ∧ denX i iex a.af.fact a.ex l0 l1 := by
  rcases bindX_sound hd hd1 with h | ⟨_, hq⟩
  · exact h
  · exact absurd hq (bindX_noreq (hwf.toStar M n c n' he e he1))

/-- The binding back from the callee (S10: mark agnostic) covers the pair, with no request. -/
theorem bind_outX {P : Program} (hwf : P.WF) {M : MethodId} {n n' : Node} {c : Call}
    (he : (M, n, Instr.call c, n') ∈ P.edges) {e : MicroEdge} (he2 : e ∈ c.fromCallee)
    {i : PFact} {iex : Excl} {r : XFact} {l0 l l1 : Loc}
    (hd : denX i iex r.af.fact r.ex l0 l) (hd2 : den e.1 e.2 l l1) :
    ∃ r', r' ∈ (bindX r e).facts ∧ denX i iex r'.af.fact r'.ex l0 l1 := by
  rcases bindX_sound hd hd2 with h | ⟨_, hq⟩
  · exact h
  · exact absurd hq (bindX_noreq (hwf.fromStar M n c n' he e he2))

#print axioms bind_inX
#print axioms bind_outX

/-- W6T keeps the pair (a demoted result drops its exclusion, so it only covers more). -/
theorem w6tX_sound {taint : TaintEdges} {e : MicroEdge} {i : PFact} {iex : Excl} {x : XFact}
    {l0 l : Loc} (h : denX i iex x.af.fact x.ex l0 l) :
    denX i iex (w6tX taint e x).af.fact (w6tX taint e x).ex l0 l := by
  unfold w6tX
  split
  · exact denX_drop h
  · exact h

/-- THE FIELD LIMIT (ap.md §4.4 with A2): the cut gives a fact that covers more and drops the
    exclusion; a fact within the limit does not change. -/
theorem limitFX_sound {counted : Acc → Bool} {L : Nat} {i : PFact} {iex : Excl} {x : XFact}
    {l0 l : Loc} (h : denX i iex x.af.fact x.ex l0 l) :
    denX i iex (limitFX counted L x).af.fact (limitFX counted L x).ex l0 l := by
  unfold limitFX
  cases cutPath counted L x.af.fact.path with
  | none => exact h
  | some p =>
    obtain ⟨hd, hp, _⟩ := denX_iff.mp h
    exact denX_iff.mpr ⟨limitF_sound hd, hp, adm_empty _ _⟩

#print axioms limitFX_sound

theorem mem_applyAllXT_facts {taint : TaintEdges} {c r : XFact} {e : MicroEdge} :
    ∀ {es : List MicroEdge}, e ∈ es → r ∈ (applyEdgeXT taint c e).facts →
      r ∈ (applyAllXT taint c es).facts
  | [], he, _ => absurd he List.not_mem_nil
  | e' :: es, he, hr => by
    show r ∈ (applyEdgeXT taint c e').facts ++ (applyAllXT taint c es).facts
    rcases List.mem_cons.mp he with h | h
    · subst h; exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (mem_applyAllXT_facts h hr)

theorem mem_applyAllXT_reqs {taint : TaintEdges} {c : XFact} {e : MicroEdge} {t : Mark} :
    ∀ {es : List MicroEdge}, e ∈ es → t ∈ (bindX c e).reqs → t ∈ (applyAllXT taint c es).reqs
  | [], he, _ => absurd he List.not_mem_nil
  | e' :: es, he, hr => by
    show t ∈ (bindX c e').reqs ++ (applyAllXT taint c es).reqs
    rcases List.mem_cons.mp he with h | h
    · subst h; exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (mem_applyAllXT_reqs h hr)

/-- THE STATEMENT TRANSFER (ap.md §4.2 with A2): `transferX` covers the statement step, or the
    entry mark is requested on a fact with an abstract mark. Hypothesis (S10 `Program.WF`): every
    micro edge reads from a touched base. -/
theorem transferX_sound {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {ic : PFact} {icx : Excl} {c : XFact} {l0 l l' : Loc}
    (hwf : ∀ e, e ∈ s.edges → memB e.1.base s.touched = true)
    (hden : denX ic icx c.af.fact c.ex l0 l) (hstep : s.step l l') :
    (∃ r, r ∈ (transferX taint counted L s c).facts ∧ denX ic icx r.af.fact r.ex l0 l') ∨
    ((∀ t, c.af.fact.mark ≠ .conc t) ∧ l0.mark ∈ (transferX taint counted L s c).reqs) := by
  have hb : l.base = c.af.fact.base := hden.2.1
  unfold transferX
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [if_neg Bool.false_ne_true]
    rcases hstep with ⟨_, hl⟩ | ⟨e, he, hde⟩
    · left
      rw [hl]
      exact ⟨c, List.mem_singleton.mpr rfl, hden⟩
    · exfalso
      have h1 := hwf e he
      rw [← hde.1, hb, hm] at h1
      exact Bool.noConfusion h1
  | true =>
    rw [if_pos rfl]
    rcases hstep with ⟨hnt, _⟩ | ⟨e, he, hde⟩
    · exfalso
      rw [hb, hm] at hnt
      exact Bool.noConfusion hnt
    · rcases bindX_sound hden hde with ⟨r, hr, hd⟩ | ⟨hs, hreq⟩
      · left
        exact ⟨limitFX counted L (w6tX taint e r),
          List.mem_map_of_mem (mem_applyAllXT_facts he (List.mem_map_of_mem hr)),
          limitFX_sound (w6tX_sound hd)⟩
      · right
        exact ⟨hs, mem_applyAllXT_reqs he hreq⟩

#print axioms transferX_sound

/-- THE SUMMARY APPLICATION (ap.md §4.3 with A2): `applySummaryX` covers the composition of the
    pair of the added fact with an annotated pair of the summary `(j, jex) → g`, or raises the
    request. -/
theorem applySummaryX_sound {ic j : PFact} {icx jex : Excl} {a g : XFact} {l0 l1 l2 : Loc}
    (h1 : denX ic icx a.af.fact a.ex l0 l1) (h2 : denX j jex g.af.fact g.ex l1 l2) :
    (∃ r, r ∈ (applySummaryX a j jex g).facts ∧ denX ic icx r.af.fact r.ex l0 l2) ∨
    ((∀ t, a.af.fact.mark ≠ .conc t) ∧ l0.mark ∈ (applySummaryX a j jex g).reqs) := by
  rcases applyEdgeX_sound h1 h2 with ⟨x, hx, hd⟩ | ⟨hs, hq⟩
  · left
    refine ⟨_, List.mem_map_of_mem (f := fun x : XFact =>
      normX ⟨AFact.norm ⟨x.af.fact, x.af.demand || g.af.demand⟩, x.ex⟩) hx, ?_⟩
    obtain ⟨hden, hp, hc⟩ := denX_iff.mp hd
    refine denX_iff.mpr ⟨?_, hp, ?_⟩
    · rw [normX_fact]
      exact CoreAux.norm_sound (f := ⟨x.af.fact, x.af.demand || g.af.demand⟩) hden
    · rcases normX_ex_cases
          (⟨AFact.norm ⟨x.af.fact, x.af.demand || g.af.demand⟩, x.ex⟩ : XFact) with he | he
      · rw [he, normX_fact]
        exact adm_path (norm_path ⟨x.af.fact, x.af.demand || g.af.demand⟩).symm hc
      · rw [he]; exact adm_empty _ _
  · right
    exact ⟨hs, hq⟩

#print axioms applySummaryX_sound

/-- Run 1: an applicable summary raises no request (a concrete premise mark forces the same mark
    on the added fact). -/
theorem summary_stepX {i j : PFact} {iex jex : Excl} {a g : XFact} {l0 l1 l2 : Loc}
    (hap : applicable j a.af.fact = true) (hda : denX i iex a.af.fact a.ex l0 l1)
    (hdg : denX j jex g.af.fact g.ex l1 l2) :
    ∃ r, r ∈ (applySummaryX a j jex g).facts ∧ denX i iex r.af.fact r.ex l0 l2 := by
  rcases applySummaryX_sound hda hdg with h | ⟨hst, hq⟩
  · exact h
  · exfalso
    have hq' := applySummaryX_reqs hq
    rcases Coverage.mark_cases j.mark with hj | ⟨t, hj⟩
    · rw [Coverage.applySummary_reqs, Coverage.applyEdge_reqs_of_abs hj] at hq'
      exact List.not_mem_nil hq'
    · exact hst _ (applicable_mark hap hj)

#print axioms summary_stepX

/-- A concrete added fact raises no request from a summary application. -/
theorem summary_stepConcX {i j : PFact} {iex jex : Excl} {a g : XFact} {l0 l1 l2 : Loc} {t : Mark}
    (hac : a.af.fact.mark = .conc t) (hda : denX i iex a.af.fact a.ex l0 l1)
    (hdg : denX j jex g.af.fact g.ex l1 l2) :
    ∃ r, r ∈ (applySummaryX a j jex g).facts ∧ denX i iex r.af.fact r.ex l0 l2 := by
  rcases applySummaryX_sound hda hdg with h | ⟨hst, _⟩
  · exact h
  · exact absurd hac (hst t)

/-- A fact relates every location of its location set to itself. -/
theorem den_self {j : PFact} {l0 : Loc} (h : j.covers l0) : den j j l0 l0 := by
  obtain ⟨hb, ⟨σ, hp, ht⟩, hm⟩ := h
  refine ⟨hb, hb, hm, CoreAux.out_of_admits hm, CoreAux.passes_of_admits hm, σ, σ, hp, hp, ht, ?_⟩
  cases hk : j.kind with
  | star e => rw [hk] at ht; exact ⟨rfl, ht⟩
  | any => trivial
  | exact => rw [hk] at ht; exact ht

/-- THE START FACT (ap.md §6.5 with A2): the start fact of a premise `(j, jex)` (a must-premise
    starts as itself, normal, with its exclusion) relates every admitted location of the premise
    to itself. -/
theorem startX_sound {j : PFact} {mj : Bool} {jex : Excl} {l0 : Loc} (h : coversX j jex l0) :
    denX j jex (startX j mj jex).af.fact (startX j mj jex).ex l0 l0 := by
  obtain ⟨hb, ⟨σ, hp, ht, he⟩, hm⟩ := h
  cases mj with
  | false =>
    exact denX_iff.mpr ⟨startFact_sound ⟨hb, ⟨σ, hp, ht⟩, hm⟩, adm_of hp he, adm_empty _ _⟩
  | true =>
    show denX j jex (normX ⟨⟨j, false⟩, jex⟩).af.fact (normX ⟨⟨j, false⟩, jex⟩).ex l0 l0
    rw [normX_fact]
    refine denX_iff.mpr ⟨den_self ⟨hb, ⟨σ, hp, ht⟩, hm⟩, adm_of hp he, ?_⟩
    rcases normX_ex_cases (⟨⟨j, false⟩, jex⟩ : XFact) with h' | h'
    · rw [h']; exact adm_of hp he
    · rw [h']; exact adm_empty _ _

#print axioms startX_sound

/-- The refined sink check is the base check when the sink pattern meets the admitted location
    set of the fact. -/
theorem checkX_eq {i s : PFact} {f : XFact} (h : overlapX f.af.fact f.ex s Excl.empty = true) :
    checkX i f s = check i f.af s := by
  unfold checkX
  rw [h, if_pos rfl]

/-- THE SINK CHECK (ap.md §4.9 with A2): an admitted tainted location that the sink pattern covers
    triggers the sink, or raises the request for the sink mark on a mark-abstract premise. -/
theorem checkX_sound {i s : PFact} {iex : Excl} {f : XFact} {l0 l : Loc} {T : Mark}
    (hsm : s.mark = .conc T) (hd : denX i iex f.af.fact f.ex l0 l) (hs : s.covers l) :
    checkX i f s = .triggered ∨ (checkX i f s = .request l0.mark ∧ ∀ t, i.mark ≠ .conc t) := by
  rw [checkX_eq (overlapX_of_common (covLoc_of_coversX (denX_end hd)) (covLoc_of_covers hs))]
  exact check_sound hsm (denX_den hd) hs

#print axioms checkX_sound

/-! ### 1.5 The cleaner -/

/-- The one-accessor exclusion `{f}` admits every continuation that does not start with `f`. -/
theorem admits_single {f : Acc} {τ : List Acc} (h : ∀ τ1, τ = f :: τ1 → False) :
    (Excl.set [f]).admits τ = true := by
  cases τ with
  | nil => rfl
  | cons x τ1 =>
    cases hx : Nat.beq x f with
    | true => exact absurd (by rw [CoreAux.beq_iff.mp hx]) (h τ1)
    | false =>
      show (!(Nat.beq x f || memB x [])) = true
      rw [hx]
      rfl

/-- THE `part` ROWS OF A CONCRETE CLEANED MARK (`partX`, ap.md §4.7 with A2). A pair of the
    annotated fact `c` whose end location `l` the cleaner does not clean (its mark is cleaned, so
    `l` is not at the cleaned position) is covered by a result: for an `[any-taint]/E` fact at `P`
    and a cleaner at `P.f`, `atAndBelow` gives `E ∪ {f}` (no location of `c` that the cleaner
    leaves starts with `f`), `below` gives `E ∪ {f}` or the position `(b, P.f, $, T)` itself (the
    only location below `P.f` that `below` leaves); every other row is the base `concPart`. -/
theorem partX_sound {cl : Cleaner} {i : PFact} {iex : Excl} {c : XFact} {l0 l : Loc}
    (hd : denX i iex c.af.fact c.ex l0 l) (hcl : cl.cleansB l = false)
    (hmk : cl.markB l.mark = true) (hbe : Nat.beq c.af.fact.base cl.base = true) :
    ∃ r, r ∈ partX cl c ∧ denX i iex r.af.fact r.ex l0 l := by
  obtain ⟨hden, hpre, hcon⟩ := denX_iff.mp hd
  have hbase : ∃ r, r ∈ ([⟨concPart cl c.af, Excl.empty⟩] : List XFact) ∧
      denX i iex r.af.fact r.ex l0 l :=
    ⟨_, List.mem_singleton.mpr rfl,
      denX_iff.mpr ⟨concPart_sound hden hcl hmk hbe, hpre, adm_empty _ _⟩⟩
  have hden0 := hden
  obtain ⟨hb0, hb1, hm0, hm1, hps, σ, τ, hp0, hp1, hti, _⟩ := hden0
  have hposF : cl.posB l = false := by
    rw [Cleaner.cleansB_eq, hmk] at hcl
    exact hcl
  have hb' : Nat.beq l.base cl.base = true := by rw [hb1]; exact hbe
  unfold partX
  cases hcar : carriesB c.af with
  | false => exact hbase
  | true =>
    dsimp only
    rw [if_pos rfl]
    cases hrch : cl.reach with
    | exact => exact hbase
    | atAndBelow =>
      cases hrel : relate cl.path c.af.fact.path with
      | below r => exact hbase
      | apart => exact hbase
      | above r =>
        cases r with
        | nil => exact hbase
        | cons f r' =>
          cases r' with
          | cons g r'' => exact hbase
          | nil =>
            have hclp : cl.path = c.af.fact.path ++ [f] := (CoreAux.relate_above_inv hrel).1
            refine ⟨⟨c.af, c.ex.union (.set [f])⟩, List.mem_singleton.mpr rfl, ?_⟩
            refine denX_iff.mpr ⟨hden, hpre, fun τ0 hτ0 => ?_⟩
            rw [CoreAux.Excl.admits_union, hcon τ0 hτ0, Bool.true_and]
            refine admits_single (fun τ1 hτ1 => ?_)
            have hpos : cl.posB l = true :=
              Cleaner.posB_of hb' (σ := τ1)
                (by rw [hτ0, hτ1, hclp, List.append_assoc]; rfl) (by rw [hrch]; rfl)
            rw [hposF] at hpos
            exact Bool.noConfusion hpos
    | below =>
      cases hrel : relate cl.path c.af.fact.path with
      | below r => exact hbase
      | apart => exact hbase
      | above r =>
        cases r with
        | nil => exact hbase
        | cons f r' =>
          cases r' with
          | cons g r'' => exact hbase
          | nil =>
            have hclp : cl.path = c.af.fact.path ++ [f] := (CoreAux.relate_above_inv hrel).1
            -- the location `l` is `P.f` itself, or it does not start with `f`
            have hcase : τ = [f] ∨ ∀ τ1, τ = f :: τ1 → False := by
              cases τ with
              | nil => exact Or.inr (fun _ h => nomatch h)
              | cons x τ1 =>
                cases hx : Nat.beq x f with
                | false =>
                  refine Or.inr (fun τ2 h => ?_)
                  have hxf : x = f := (List.cons.inj h).1
                  rw [hxf, Nat.beq_refl] at hx
                  exact Bool.noConfusion hx
                | true =>
                  have hxf : x = f := CoreAux.beq_iff.mp hx
                  cases τ1 with
                  | nil => left; rw [hxf]
                  | cons y τ2 =>
                    exfalso
                    have hpos : cl.posB l = true :=
                      Cleaner.posB_of hb' (σ := y :: τ2)
                        (by rw [hp1, hclp, hxf, List.append_assoc]; rfl) (by rw [hrch]; rfl)
                    rw [hposF] at hpos
                    exact Bool.noConfusion hpos
            rcases hcase with hτ | hnf
            · refine ⟨⟨⟨⟨c.af.fact.base, c.af.fact.path ++ [f], .exact, c.af.fact.mark⟩,
                c.af.demand⟩, Excl.empty⟩, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), ?_⟩
              refine denX_iff.mpr ⟨?_, hpre, adm_empty _ _⟩
              refine ⟨hb0, hb1, hm0, hm1, hps, σ, [], hp0, ?_, hti, rfl⟩
              rw [hp1, hτ, List.append_nil]
            · refine ⟨⟨c.af, c.ex.union (.set [f])⟩, List.mem_cons_self .., ?_⟩
              refine denX_iff.mpr ⟨hden, hpre, fun τ0 hτ0 => ?_⟩
              rw [CoreAux.Excl.admits_union, hcon τ0 hτ0, Bool.true_and]
              have e1 : τ0 = τ := List.append_cancel_left (hτ0.symm.trans hp1)
              rw [e1]
              exact admits_single hnf

#print axioms partX_sound

/-- THE CLEANER (ap.md §4.7 with A2): a pair of the annotated fact whose end location the cleaner
    does not clean is covered by a result of `cleanResX`, or the entry mark is requested on a fact
    with an abstract mark (the `part` row of an abstract mark, as the base). A cleaner in the
    excluded part of the fact (`cleanPosX` is `disjoint`) keeps the fact. -/
theorem cleanResX_sound {cl : Cleaner} {i : PFact} {iex : Excl} {c : XFact} {l0 l : Loc}
    (hd : denX i iex c.af.fact c.ex l0 l) (hcl : cl.cleansB l = false) :
    (∃ r, r ∈ (cleanResX cl c).facts ∧ denX i iex r.af.fact r.ex l0 l) ∨
    ((∀ t, c.af.fact.mark ≠ .conc t) ∧ l0.mark ∈ (cleanResX cl c).reqs) := by
  obtain ⟨hden, hpre, hcon⟩ := denX_iff.mp hd
  have hb1 : l.base = c.af.fact.base := hden.2.1
  have hloc : ∃ τ, l.path = c.af.fact.path ++ τ ∧ tailI c.af.fact.kind τ := by
    obtain ⟨_, _, _, _, _, σ, τ, _, hp1, _, htf⟩ := hden
    exact ⟨τ, hp1, CoreAux.tailI_of_tailF htf⟩
  have hm1 : l.mark = c.af.fact.mark.out l0.mark := hden.2.2.2.1
  have hsplit : cl.markB l.mark = false ∨ cl.posB l = false := by
    rw [Cleaner.cleansB_eq] at hcl
    cases hmk : cl.markB l.mark with
    | false => exact .inl rfl
    | true => rw [hmk] at hcl; exact .inr hcl
  have habs : ∀ t, (∀ t', c.af.fact.mark ≠ .conc t') → cl.mark = some t →
      cl.markB l.mark = false → Nat.beq l0.mark t = false := by
    intro t ha hclm hmk
    rw [den_mark_abs hden ha] at hmk
    unfold Cleaner.markB at hmk
    rw [hclm] at hmk
    exact hmk
  have hadd : ∀ t, Nat.beq l0.mark t = false →
      denX i iex (⟨c.af.fact.base, c.af.fact.path, c.af.fact.kind, addEx c.af.fact.mark t⟩ : PFact)
        c.ex l0 l :=
    fun t hx => denX_iff.mpr ⟨den_addEx hden hx, hpre, hcon⟩
  unfold cleanResX
  rcases cleanPosX_cases cl c with hp | ⟨hp, _, _, _⟩
  · rw [hp]
    cases hpos : cleanPos cl c.af.fact with
    | disjoint => exact .inl ⟨c, List.mem_singleton.mpr rfl, hd⟩
    | inside =>
      have hin := cleanPos_inside_sound hpos hb1 hloc
      have hmk : cl.markB l.mark = false := by
        rcases hsplit with h | h
        · exact h
        · rw [hin] at h; exact Bool.noConfusion h
      cases hcm : c.af.fact.mark with
      | conc t =>
        rw [hcm] at hm1
        have hlt : l.mark = t := hm1
        rw [hlt] at hmk
        show (∃ r, r ∈ (if cl.markB t = true then ResX.none else ⟨[c], []⟩ : ResX).facts ∧ _) ∨ _
        rw [hmk, if_neg Bool.false_ne_true]
        exact .inl ⟨c, List.mem_singleton.mpr rfl, hd⟩
      | star =>
        have ha : ∀ t', c.af.fact.mark ≠ .conc t' := fun t' h => by
          rw [hcm] at h; exact MarkA.noConfusion h
        cases hclm : cl.mark with
        | none =>
          unfold Cleaner.markB at hmk
          rw [hclm] at hmk
          exact Bool.noConfusion hmk
        | some t =>
          refine .inl ⟨_, List.mem_singleton.mpr rfl, ?_⟩
          have h := hadd t (habs t ha hclm hmk)
          rw [hcm] at h
          exact h
      | starEx y =>
        have ha : ∀ t', c.af.fact.mark ≠ .conc t' := fun t' h => by
          rw [hcm] at h; exact MarkA.noConfusion h
        cases hclm : cl.mark with
        | none =>
          unfold Cleaner.markB at hmk
          rw [hclm] at hmk
          exact Bool.noConfusion hmk
        | some t =>
          refine .inl ⟨_, List.mem_singleton.mpr rfl, ?_⟩
          have h := hadd t (habs t ha hclm hmk)
          rw [hcm] at h
          exact h
    | part =>
      cases hcm : c.af.fact.mark with
      | conc t =>
        cases hmt : cl.markB t with
        | true =>
          show (∃ r, r ∈ (if cl.markB t = true then (⟨partX cl c, []⟩ : ResX)
            else ⟨[c], []⟩).facts ∧ _) ∨ _
          rw [hmt, if_pos rfl]
          have hbe : Nat.beq c.af.fact.base cl.base = true := by
            unfold cleanPos at hpos
            cases hbe : Nat.beq c.af.fact.base cl.base with
            | true => rfl
            | false => rw [hbe, if_neg Bool.false_ne_true] at hpos; exact CPos.noConfusion hpos
          rw [hcm] at hm1
          have hlt : l.mark = t := hm1
          have hmk : cl.markB l.mark = true := by rw [hlt]; exact hmt
          exact .inl (partX_sound hd hcl hmk hbe)
        | false =>
          show (∃ r, r ∈ (if cl.markB t = true then (⟨partX cl c, []⟩ : ResX)
            else ⟨[c], []⟩).facts ∧ _) ∨ _
          rw [hmt, if_neg Bool.false_ne_true]
          exact .inl ⟨c, List.mem_singleton.mpr rfl, hd⟩
      | star =>
        cases hclm : cl.mark with
        | none =>
          exact .inl ⟨⟨AFact.norm ⟨c.af.fact, true⟩, Excl.empty⟩, List.mem_singleton.mpr rfl,
            denX_iff.mpr ⟨CoreAux.norm_sound (f := ⟨c.af.fact, true⟩) hden, hpre, adm_empty _ _⟩⟩
        | some t =>
          cases hx : Nat.beq l0.mark t with
          | true =>
            exact .inr ⟨fun _ h0 => MarkA.noConfusion h0,
              List.mem_singleton.mpr (CoreAux.beq_iff.mp hx)⟩
          | false =>
            refine .inl ⟨_, List.mem_singleton.mpr rfl, ?_⟩
            have h := hadd t hx
            rw [hcm] at h
            exact h
      | starEx y =>
        cases hclm : cl.mark with
        | none =>
          exact .inl ⟨⟨AFact.norm ⟨c.af.fact, true⟩, Excl.empty⟩, List.mem_singleton.mpr rfl,
            denX_iff.mpr ⟨CoreAux.norm_sound (f := ⟨c.af.fact, true⟩) hden, hpre, adm_empty _ _⟩⟩
        | some t =>
          cases hx : Nat.beq l0.mark t with
          | true =>
            exact .inr ⟨fun _ h0 => MarkA.noConfusion h0,
              List.mem_singleton.mpr (CoreAux.beq_iff.mp hx)⟩
          | false =>
            refine .inl ⟨_, List.mem_singleton.mpr rfl, ?_⟩
            have h := hadd t hx
            rw [hcm] at h
            exact h
  · rw [hp]
    exact .inl ⟨c, List.mem_singleton.mpr rfl, hd⟩

#print axioms cleanResX_sound

/-! ### 1.6 Marks, tails and requests of the results (for the invariants) -/

theorem nonstar_of_legalM {f : AFact} (hl : Invariant.LegalM f) {t : Mark}
    (hm : f.fact.mark = .conc t) : f.fact.kind.isStar = false := by
  cases hk : f.fact.kind with
  | star e => exact absurd hm ((hl e hk).not_conc t)
  | any => rfl
  | exact => rfl

/-- The fact of a refined transfer result is the fact of a base transfer result. -/
theorem transferX_fact {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (h : x ∈ (transferX taint counted L s c).facts) :
    ∃ y, y ∈ (transfer counted L s c.af).facts ∧ x.af.fact = y.fact := by
  obtain ⟨y, hy, hf, _⟩ := transferX_base h
  obtain ⟨f, hf', hle⟩ := transferT_mem hy
  exact ⟨f, hf', hf.trans hle.fact.symm⟩

theorem transferX_mark_conc {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} {t : Mark} (hct : c.af.fact.mark = .conc t)
    (h : x ∈ (transferX taint counted L s c).facts) : ∃ t', x.af.fact.mark = .conc t' := by
  obtain ⟨y, hy, hf⟩ := transferX_fact h
  rw [hf]
  exact transfer_mark_conc hct hy

/-- A transfer result of a concrete fact without the `*` tail is concrete and has no `*` tail. -/
theorem transferX_conc {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (hc : c.af.fact.kind.isStar = false) {t : Mark} (hct : c.af.fact.mark = .conc t)
    (h : x ∈ (transferX taint counted L s c).facts) :
    (∃ t', x.af.fact.mark = .conc t') ∧ x.af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hf⟩ := transferX_fact h
  rw [hf]
  obtain ⟨t', ht'⟩ := transfer_mark_conc hct hy
  refine ⟨⟨t', ht'⟩, ?_⟩
  rcases Invariant.transfer_mem hy with rfl | ⟨x, e, _, hx, rfl⟩
  · exact hc
  · exact nonstar_of_legalM (Invariant.limitF_LegalM (Invariant.applyEdge_LegalM hx)) ht'

theorem bindX_mark_conc {c x : XFact} {e : MicroEdge} {t : Mark} (hct : c.af.fact.mark = .conc t)
    (h : x ∈ (bindX c e).facts) : ∃ t', x.af.fact.mark = .conc t' := by
  obtain ⟨y, hy, hf, _⟩ := bindX_base h
  rw [hf]
  exact applyEdge_mark_conc hct hy

/-- The field limit of a result whose fact is a `LegalM` concrete fact: concrete, no `*` tail. -/
theorem limitFX_conc {counted : Acc → Bool} {L : Nat} {x : XFact} {y : AFact}
    (hf : x.af.fact = y.fact) (hl : Invariant.LegalM y) {t : Mark} (hm : y.fact.mark = .conc t) :
    (∃ t', (limitFX counted L x).af.fact.mark = .conc t') ∧
      (limitFX counted L x).af.fact.kind.isStar = false := by
  rw [limitFX_af, limitF_fact_eq (g := y) hf]
  exact ⟨⟨t, by rw [limitF_mark]; exact hm⟩,
    nonstar_of_legalM (Invariant.limitF_LegalM hl) (by rw [limitF_mark]; exact hm)⟩

/-- The binding back of a summary result: concrete, and its field limit has no `*` tail. -/
theorem ret_conc {counted : Acc → Bool} {L : Nat} {a g r r' x : XFact} {j : PFact} {jex : Excl}
    {e2 : MicroEdge} {t : Mark} (hat : a.af.fact.mark = .conc t)
    (hr : r ∈ (applySummaryX a j jex g).facts) (hr' : r' ∈ (bindX r e2).facts)
    (hx : x.af.fact = r'.af.fact) :
    (∃ t', (limitFX counted L x).af.fact.mark = .conc t') ∧
      (limitFX counted L x).af.fact.kind.isStar = false := by
  obtain ⟨y, hy, hfy, _⟩ := applySummaryX_base hr
  obtain ⟨t1, h1⟩ := applySummary_mark_conc hat hy
  obtain ⟨y', hy', hfy', _⟩ := bindX_base hr'
  have h1' : r.af.fact.mark = .conc t1 := by rw [hfy]; exact h1
  obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1' hy'
  exact limitFX_conc (hx.trans hfy') (Invariant.applyEdge_LegalM hy') h2

/-- A cleaner result of a concrete fact: concrete (the base result, or the position `P.f` of the
    `below` row, which has the mark of the fact). -/
theorem cleanResX_mark_conc {cl : Cleaner} {c x : XFact} (hw : WFX c) {t : Mark}
    (hct : c.af.fact.mark = .conc t) (h : x ∈ (cleanResX cl c).facts) :
    ∃ t', x.af.fact.mark = .conc t' := by
  rcases cleanResX_base hw h with ⟨y, hy, hf, _⟩ | ⟨_, _, f, _, rfl⟩
  · rw [hf]; exact cleanRes_mark_conc hct hy
  · exact ⟨t, hct⟩

theorem cleanResX_conc {cl : Cleaner} {c x : XFact} (hw : WFX c) (hc : c.af.fact.kind.isStar = false)
    {t : Mark} (hct : c.af.fact.mark = .conc t) (h : x ∈ (cleanResX cl c).facts) :
    (∃ t', x.af.fact.mark = .conc t') ∧ x.af.fact.kind.isStar = false := by
  rcases cleanResX_base hw h with ⟨y, hy, hf, _⟩ | ⟨_, _, f, _, rfl⟩
  · rw [hf]
    obtain ⟨t', ht'⟩ := cleanRes_mark_conc hct hy
    have hl : Invariant.LegalM c.af := fun e hk => by rw [hk] at hc; cases hc
    exact ⟨⟨t', ht'⟩, nonstar_of_legalM (Invariant.cleanRes_LegalM hl hy) ht'⟩
  · exact ⟨⟨t, hct⟩, rfl⟩

/-- The requests of the refined cleaner are requests of the base cleaner (a cleaner in the
    excluded part raises none). -/
theorem cleanResX_reqs_sub {cl : Cleaner} {c : XFact} {t : Mark}
    (h : t ∈ (cleanResX cl c).reqs) : t ∈ (cleanRes cl c.af).reqs := by
  unfold cleanResX at h
  rcases cleanPosX_cases cl c with hp | ⟨hp, _⟩
  · rw [hp] at h
    unfold cleanRes
    revert h
    cases cleanPos cl c.af.fact with
    | disjoint => exact id
    | inside =>
      cases c.af.fact.mark with
      | conc t0 => dsimp only; cases cl.markB t0 <;> exact id
      | star => cases cl.mark <;> exact id
      | starEx y => cases cl.mark <;> exact id
    | part =>
      cases c.af.fact.mark with
      | conc t0 => dsimp only; cases cl.markB t0 <;> exact id
      | star => cases cl.mark <;> exact id
      | starEx y => cases cl.mark <;> exact id
  · rw [hp] at h
    exact absurd h List.not_mem_nil

#print axioms cleanResX_reqs_sub

/-! ## 2. The contracts of the restricted run with exclusions -/

theorem subB_union_self (e e' : Excl) : e.subB (e'.union e) = true := by
  cases e' with
  | univ => exact Invariant.subB_univ _
  | set ys =>
    cases e with
    | univ => exact Invariant.subB_univ _
    | set xs =>
      show xs.all (fun a => memB a (ys ++ xs)) = true
      apply List.all_eq_true.mpr
      intro a ha
      rw [CoreAux.memB_append, CoreAux.memB_iff.mpr ha, Bool.or_true]

/-- The exclusion of an emitted premise at the path of its added fact: the added fact excludes at
    most what the premise excludes. -/
theorem subB_tail_normJ (j : PFact) (aex : Excl) :
    aex.subB ((tailExcl j.kind).union (normJ j aex)) = true := by
  unfold normJ
  cases j.kind with
  | exact => exact Invariant.subB_univ _
  | star e => exact subB_union_self aex e
  | any => exact subB_union_self aex Excl.empty

/-- C2 FOR THE SPEC EMISSION WITH EXCLUSIONS (ap.md §6.3 with DESIGN A2): for a demanded location
    `l` (with its mark) that the ADMITTED part of a concrete added fact `(a, aex)` carries, `emitX`
    gives a premise `(j, jex)` whose admitted location set contains `l` and that lies inside the
    added fact (`satX`). So the emitted fact covers every location of `a ∩ D-c` with `E`: at the
    path of `a` (or below the pattern chain) the premise keeps `E`; above the chain the chain
    `D-c` needs `E` to admit the step down (and then no exclusion is left below it). -/
theorem emitX_contract : EmitContractX emitX satX := by
  intro d a aex l t ham hd ha
  obtain ⟨j, hj, hjc, hsat⟩ := RCore.emitM_contract_I d a l t ham hd (coversX_covers ha)
  obtain ⟨_, _, hshape⟩ := RCore.emitM_cases hj
  obtain ⟨_, ⟨σa, hpa, _, hea⟩, _⟩ := ha
  obtain ⟨_, ⟨σd, hpd, _⟩, _⟩ := hd
  have hpath : d.path ++ σd = a.path ++ σa := by rw [← hpd, ← hpa]
  unfold emitX
  rw [hj]
  dsimp only
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, _⟩ | ⟨r, hrel, hP, hr, hτ⟩
  · -- the added fact at or below the pattern chain: the premise is at the path of `a`
    rw [hrel]
    have hjp : j.path = a.path := by
      rcases hshape with ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r', hr', _, _, _, _⟩
      · rw [h1]
      · rw [h2]
      · rw [hrel] at hr'; cases hr'
    refine ⟨j, normJ j aex, rfl, ?_, ?_⟩
    · obtain ⟨hbj, ⟨σj, hpj, htj⟩, hmj⟩ := hjc
      refine ⟨hbj, ⟨σj, hpj, htj, ?_⟩, hmj⟩
      have e1 : σj = σa := by
        have e2 : a.path ++ σj = a.path ++ σa := by rw [← hpa, hpj, hjp]
        exact List.append_cancel_left e2
      unfold normJ
      split
      · exact admits_empty σj
      · rw [e1]; exact hea
    · unfold satX
      rw [hsat, Bool.true_and]
      unfold insideExB
      rw [hjp, RCore.relate_self]
      exact subB_tail_normJ j aex
  · -- the added fact above the pattern chain: the chain, if `aex` admits the step down
    rw [hrel]
    dsimp only
    have hra : aex.admits r = true := by rw [hτ] at hea; exact admits_prefix hea
    rw [if_pos hra]
    have hjp : j.path = a.path ++ r := by
      rcases hshape with ⟨h0, _⟩ | ⟨x, r', h0, _, _⟩ | ⟨r', _, _, _, _, h3⟩
      · exfalso
        rw [h0, RCore.relate_self] at hrel
        cases hrel
      · exfalso
        rw [h0, CoreAux.relate_below (CoreAux.dropPrefix_some.mpr rfl)] at hrel
        cases hrel
      · rw [h3]; exact hP
    refine ⟨j, Excl.empty, rfl, covers_coversX hjc, ?_⟩
    unfold satX
    rw [hsat, Bool.true_and]
    unfold insideExB
    rw [hjp, CoreAux.relate_below (CoreAux.dropPrefix_some.mpr rfl)]
    cases r with
    | nil => exact absurd rfl hr
    | cons x r' => exact hra

#print axioms emitX_contract

/-- C4 FOR THE SPEC SATISFACTION WITH EXCLUSIONS (its first part, `SatContract`): a satisfied
    premise has a sub-mark of the added fact, so the mark gate raises no request. (The second part
    of `SatContract`, the answers of requests, is not read: a restricted run has no request,
    `noReqX`.) `satX` also reads the premise as INSIDE the added fact with the exclusions
    (`AnyTaintEx.satX_inside`). -/
def SatContractX (sat : PFact → Excl → PFact → Excl → Bool) : Prop :=
  ∀ j jex a aex, sat j jex a aex = true → markSubB j.mark a.mark = true

/-- C4 for `satX`: a premise that `satX` accepts has a sub-mark of the added fact (from
    `AnyTaintEx.satX_inside`). -/
theorem satX_contract : SatContractX satX := fun j jex a aex h => (satX_inside j jex a aex h).2

#print axioms satX_contract

/-- C5 FOR CONCLUSIONS WITHOUT THE `*` TAIL: a demanded pair of an annotated summary edge whose
    conclusion has no `*` tail survives the restriction, in the same layer. (A restricted run has
    no `*` conclusion: `concX_all`.) -/
def RestrictContractNSX (restrict : PFact → Excl → XFact → DemandEdge → Option XFact) : Prop :=
  ∀ j jex g d p l1 l2, g.af.fact.kind.isStar = false → denX j jex g.af.fact g.ex l1 l2 →
    d.din.coversLoc l1 → d.dout = some p → p.coversLoc l2 →
    ∃ g', restrict j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand

/-- C5 FOR THE SPEC RESTRICTION WITH EXCLUSIONS (ap.md §6.4 with DESIGN A2), for conclusions
    without the `*` tail: the premise meets `D-c` (with its exclusion: `overlapX`); a conclusion at
    or below `D-p` keeps its exclusion; an `[any-taint]/E` conclusion above `D-p` gives the chain
    `D-p`, and `E` admits the step down because the demanded end location lies below it. -/
theorem restrictX_contractNS : RestrictContractNSX restrictX := by
  intro j jex g d p l1 l2 hns hd hdin hdout hp
  obtain ⟨hden, hpre, hcon⟩ := denX_iff.mp hd
  have hd0 := hd
  obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf, hjex, hgex⟩ := hd0
  have hov : overlapX j jex d.din Excl.empty = true :=
    overlapX_of_common ⟨hb1, σ, hp1, hti, hjex⟩ (covLoc_of_coversLoc hdin)
  unfold restrictX
  rw [hdout]
  dsimp only
  rw [if_pos hov]
  unfold restrictConcX restrictConcU
  obtain ⟨hpb, σp, hpp, htp⟩ := hp
  have hbeq : Nat.beq g.af.fact.base p.base = true := by rw [← hb2, ← hpb]; exact Nat.beq_refl _
  rw [if_pos hbeq]
  have hpath : p.path ++ σp = g.af.fact.path ++ τ := by rw [← hpp, ← hp2]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, hr, hτ⟩
  · rw [hrel]
    dsimp only
    have hadm : admitsTailB p.kind r = true := by
      rw [hσ] at htp
      exact CoreAux.tailI_append_admits htp
    rw [if_pos hadm]
    dsimp only
    refine ⟨normX ⟨g.af, g.ex⟩, rfl, ?_, by rw [normX_af]⟩
    rw [normX_fact]
    refine denX_iff.mpr ⟨hden, hpre, ?_⟩
    rcases normX_ex_cases (⟨g.af, g.ex⟩ : XFact) with he | he
    · rw [he]; exact hcon
    · rw [he]; exact adm_empty _ _
  · rw [hrel]
    dsimp only
    cases hk : g.af.fact.kind with
    | star e => rw [hk] at hns; cases hns
    | exact =>
      exfalso
      rw [hk] at htf
      have h0 : τ = [] := htf
      rw [hτ] at h0
      cases r with
      | nil => exact hr rfl
      | cons x r' => exact nomatch h0
    | any =>
      dsimp only
      have hra : g.ex.admits r = true := by rw [hτ] at hgex; exact admits_prefix hgex
      rw [if_pos hra]
      refine ⟨_, rfl, ?_, rfl⟩
      refine ⟨hb1, hb2, hm1, hm2, hps, σ, σp, hp1, hpp, hti, ?_, hjex, admits_empty σp⟩
      cases hpk : p.kind with
      | exact => rw [hpk] at htp; exact htp
      | any => trivial
      | star e => trivial

#print axioms restrictX_contractNS

/-- CEGAR: the FULL restriction contract `RestrictContractX` of the definitions file is FALSE for
    `restrictX` (as `restrictU` fails C5, `RCore.restrictU_fails`): a correlated `*` conclusion
    above `D-p` gives nothing. It is not needed: a restricted run has no `*` conclusion
    (`concX_all`), and `RestrictContractNSX` holds. -/
theorem restrictX_not_contract : ¬ RestrictContractX restrictX := by
  intro h
  have hdin : RCore.wDE.din.coversLoc RCore.wL1 := ⟨rfl, [1, 4, 5], rfl, trivial⟩
  have hp : RCore.wP.coversLoc RCore.wL2 := ⟨rfl, [5], rfl, trivial⟩
  obtain ⟨g', hg', _, _⟩ := h RCore.wJ Excl.empty ⟨RCore.wG, Excl.empty⟩ RCore.wDE RCore.wP
    RCore.wL1 RCore.wL2 (den_denX RCore.wDen) hdin rfl hp
  have hnone : restrictX RCore.wJ Excl.empty ⟨RCore.wG, Excl.empty⟩ RCore.wDE = none := by decide
  rw [hnone] at hg'
  cases hg'

#print axioms restrictX_not_contract

/-! ## 3. Run 1 with the exclusion (`D6X`) -/

/-- Run 1 read without its exclusions: the base object of each refined object (`XObj6.forget`:
    an edge keeps its base fact, the exclusion is DROPPED). The backward run and the reports read
    run 1 so. -/
def forget6 (R : XObj6 → Prop) (o : Obj) : Prop := ∃ x, R x ∧ x.forget = o

theorem forget6_vuln {R : XObj6 → Prop} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : forget6 R (.vuln M n s b)) : R (.vuln M n s b) := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | vuln M' n' s' d => cases he; exact hx
  | init => cases he
  | edge => cases he
  | added => cases he
  | req => cases he

/-- The edge invariant of run 1: the annotation is well formed, and a concrete premise mark gives
    a concrete final mark. -/
def EdgeInv6X : XObj6 → Prop
  | .edge _ i _ f => WFX f ∧ ∀ t, i.mark = .conc t → ∃ t', f.af.fact.mark = .conc t'
  | _ => True

/-- The request invariant of run 1: a request is on a premise whose mark is not concrete. -/
def ReqInv6X : XObj6 → Prop
  | .req _ i _ => ∀ t, i.mark ≠ .conc t
  | _ => True

section Run1
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "D6Xr" => D6X P taint counted L α sinks roots

theorem edgeInv6X_all {o : XObj6} (h : D6Xr o) : EdgeInv6X o := by
  induction h with
  | start _ =>
    refine ⟨startX_wf _ _ _, fun t ht => ⟨t, ?_⟩⟩
    show (startFact _).fact.mark = _
    rw [startFact_mark]
    exact ht
  | step _ _ hf' ih =>
    refine ⟨transferX_wf ih.1 hf', fun t ht => ?_⟩
    obtain ⟨t1, h1⟩ := ih.2 t ht
    exact transferX_mark_conc h1 hf'
  | pass _ _ _ ih => exact ih
  | clean _ _ hf' ih =>
    refine ⟨cleanResX_wf ih.1 hf', fun t ht => ?_⟩
    obtain ⟨t1, h1⟩ := ih.2 t ht
    exact cleanResX_mark_conc ih.1 h1 hf'
  | filt _ _ _ ih => exact ih
  | ret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    refine ⟨limitFX_wf counted L (applyEdgeX_wf hr'), fun t ht => ?_⟩
    obtain ⟨t1, h1⟩ := ih.2 t ht
    obtain ⟨t2, h2⟩ := bindX_mark_conc h1 ha
    exact (ret_conc h2 hr hr' rfl).1
  | root _ => trivial
  | reqStmt _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | reqSink _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | reqUp _ _ _ _ _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial
  | reqClean _ _ _ _ => trivial

#print axioms edgeInv6X_all

theorem edge_conc6X {M : MethodId} {i : PFact} {n : Node} {f : XFact} {t : Mark}
    (h : D6Xr (.edge M i n f)) (ht : i.mark = .conc t) : ∃ t', f.af.fact.mark = .conc t' :=
  (edgeInv6X_all P taint counted L α sinks roots h).2 t ht

theorem reqInv6X_all {o : XObj6} (h : D6Xr o) : ReqInv6X o := by
  induction h with
  | @reqStmt _ i _ _ _ _ _ hf _ hq _ =>
    rcases Coverage.mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_conc6X P taint counted L α sinks roots hf hm
      have hq' := transferX_reqs hq
      rw [transferT_reqs, transfer_reqs_of_conc h1] at hq'
      exact List.not_mem_nil hq'
  | reqSink _ _ hc _ => exact check_request_star (checkX_request hc)
  | @reqUp _ _ _ _ ic _ _ _ _ _ _ _ hf _ _ _ ha hcl _ _ _ =>
    rcases Coverage.mark_cases ic.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_conc6X P taint counted L α sinks roots hf hm
      obtain ⟨t2, h2⟩ := bindX_mark_conc h1 ha
      exact climbsB_abs hcl t2 h2
  | @reqClean _ i _ _ _ _ _ hf _ hq _ =>
    rcases Coverage.mark_cases i.mark with hm | ⟨t0, hm⟩
    · exact hm
    · exfalso
      obtain ⟨t1, h1⟩ := edge_conc6X P taint counted L α sinks roots hf hm
      exact (cleanRes_reqs_abstract (cleanResX_reqs_sub hq)).1 t1 h1
  | clean _ _ _ _ => trivial
  | filt _ _ _ _ => trivial
  | root _ => trivial
  | start _ _ => trivial
  | step _ _ _ _ => trivial
  | pass _ _ _ _ => trivial
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | answer _ _ _ _ _ _ => trivial
  | vuln _ _ _ _ => trivial

/-- The request invariant of run 1 with the exclusion: every request is on a premise whose mark
    is not concrete (as `Coverage.req_initial_star`). -/
theorem req_initial_star6X {M : MethodId} {i : PFact} {t : Mark}
    (h : D6Xr (.req M i t)) : ∀ t', i.mark ≠ .conc t' :=
  reqInv6X_all P taint counted L α sinks roots h

#print axioms req_initial_star6X

/-- THE COVERAGE THEOREM OF RUN 1 WITH THE EXCLUSION (as `Coverage.coverage`, DESIGN A2). If a
    premise `i` of `M` in `D6X` covers the entry location `l0` and the value at `l0` flows to `l` at
    `n`, then an edge of `i` at `n` covers the pair in the refined relation (its exclusion admits
    `l`: the exclusion removes only locations that are not reached), or `D6X` has the request for
    the entry mark on `i`. The flow is den-aware for the summaries of `D6X` read without their
    exclusions (`FlowRD`, the input of the backward run). Hypotheses: S10 (`Program.WF`) and C1
    (the abstraction gives an applicable premise), as the base theorem. -/
theorem coverage6X (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, D6Xr (.init M i) → i.covers l0 →
      (∃ f, D6Xr (.edge M i n f) ∧ denX i Excl.empty f.af.fact f.ex l0 l ∧
        FlowRD P (forget6 D6Xr) M l0 n l) ∨
      D6Xr (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, D6X.start hi, startX_sound (covers_coversX hc), FlowRD.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases transferX_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D6X.step hf he hr, hdr, FlowRD.step hfr he hs⟩
      · exact .inr (D6X.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · have hb : memB f.af.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, D6X.pass hf he hb, hd, FlowRD.pass hfr he hm⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · -- the caller fact reaches the call; bind it into the callee
      obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
      have hadd := D6X.added hf he he1 ha
      have hacX : coversX a.af.fact a.ex l1 := denX_end hda
      have hac : a.af.fact.covers l1 := coversX_covers hacX
      have hapj := hα c.callee a.af.fact
      have hjc : (α c.callee a.af.fact).covers l1 := applicable_sound hapj hac
      have hov : overlapB a.af.fact (α c.callee a.af.fact) = true := overlapB_of_common hac hjc
      have hovX : overlapX a.af.fact a.ex (α c.callee a.af.fact) Excl.empty = true :=
        overlapX_of_common (covLoc_of_coversX hacX) (covLoc_of_covers hjc)
      -- a covered callee exit pair of an applicable premise gives the caller edge
      have fin : ∀ j, D6Xr (.init c.callee j) → j.covers l1 → applicable j a.af.fact = true →
          ∀ g, D6Xr (.edge c.callee j (P.exit c.callee) g) →
          denX j Excl.empty g.af.fact g.ex l1 l2 →
          FlowRD P (forget6 D6Xr) c.callee l1 (P.exit c.callee) l2 →
          ∃ f', D6Xr (.edge M i n' f') ∧ denX i Excl.empty f'.af.fact f'.ex l0 l3 ∧
            FlowRD P (forget6 D6Xr) M l0 n' l3 := by
        intro j hj hjc' hap g hg hdg hfc'
        obtain ⟨r, hr, hdr⟩ := summary_stepX hap hda hdg
        obtain ⟨r', hr', hdr'⟩ := bind_outX hwf he he2 hdr hd2
        exact ⟨_, D6X.ret hf he he1 ha hj hap hg hr he2 hr', limitFX_sound hdr',
          FlowRD.call hfr he he1 hd1 hfc' ⟨_, hj, rfl⟩ ⟨_, hg, rfl⟩ hjc' (denX_den hdg) he2 hd2⟩
      rcases ihc _ (D6X.initA hadd) hjc with ⟨g, hg, hdg, hfc'⟩ | hreq
      · exact .inl (fin _ (D6X.initA hadd) hjc hapj g hg hdg hfc')
      · rcases Coverage.mark_cases a.af.fact.mark with ham | ⟨t', ham⟩
        · -- the added fact is mark-abstract: the request climbs to the caller
          have hup := D6X.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hovX
          rw [den_mark_abs (denX_den hda) ham] at hup
          exact .inr hup
        · -- the added fact is concrete: it answers the request
          have hmk := Coverage.den_mark_conc (denX_den hda) ham
          have hans := D6X.answer hreq hadd hmk hov
          have hap' := answerInit_applicable hapj hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg, hfc'⟩ | hreq'
          · exact .inl (fin _ hans hc' hap' g hg hdg hfc')
          · exfalso
            exact req_initial_star6X P taint counted L α sinks roots hreq' l1.mark answerInit_mark
    · exact .inr hr
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases cleanResX_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D6X.clean hf he hr, hdr, FlowRD.clean hfr he hcl⟩
      · exact .inr (D6X.reqClean hf he hq)
    · exact .inr hr
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · exact .inl ⟨f, D6X.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) (denX_den hd) hl),
        hd, FlowRD.filt hfr he hl⟩
    · exact .inr hr

#print axioms coverage6X

theorem coverage_conc6X (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l)
    {i : PFact} {t : Mark}
    (hi : D6Xr (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, D6Xr (.edge M i n f) ∧ denX i Excl.empty f.af.fact f.ex l0 l ∧
      FlowRD P (forget6 D6Xr) M l0 n l := by
  rcases coverage6X P taint counted L α sinks roots hwf hα hfl i hi hc with h | hr
  · exact h
  · exact absurd ht (req_initial_star6X P taint counted L α sinks roots hr t)

/-- The strengthened reach statement of run 1 with the exclusion (as `Backward.reach_strongDD`):
    run 1 makes every real witness a den-aware witness of its own summaries (read without the
    exclusions), and an edge covers the witness in the refined relation. -/
theorem reach_strong6X (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    ReachRD P (forget6 D6Xr) roots M n l ∧
    ∃ l0 i f, D6Xr (.edge M i n f) ∧ denX i Excl.empty f.af.fact f.ex l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       ((∀ t, i.mark ≠ .conc t) ∧ (D6Xr (.req M i l0.mark) →
          ∃ i' f', D6Xr (.edge M i' n f') ∧ denX i' Excl.empty f'.af.fact f'.ex l0 l ∧
            ∃ t, i'.mark = .conc t))) := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverage_conc6X P taint counted L α sinks roots hwf hα hfl
      (t := zeroMark) (D6X.root hM) Coverage.zeroFact_covers rfl
    exact ⟨ReachRD.root hM hfr, zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := D6X.added hf he he1 ha
    have hacX : coversX a.af.fact a.ex l1 := denX_end hda
    have hac : a.af.fact.covers l1 := coversX_covers hacX
    have hapj := hα c.callee a.af.fact
    have hjc : (α c.callee a.af.fact).covers l1 := applicable_sound hapj hac
    have key : D6Xr (.req c.callee (α c.callee a.af.fact) l1.mark) →
        ∃ j', D6Xr (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', D6Xr (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases Coverage.mark_cases a.af.fact.mark with ham | ⟨t', ham⟩
        · have hup := D6X.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapX_of_common (covLoc_of_coversX hacX) (covLoc_of_covers hjc))
          rw [den_mark_abs (denX_den hda) ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exact absurd ht (req_initial_star6X P taint counted L α sinks roots hup t)
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_inX hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_conc6X P taint counted L α sinks roots hf' ht
            obtain ⟨t2, h2⟩ := bindX_mark_conc h1 ha'
            exact ⟨a'.af.fact, D6X.added hf' he he1 ha', coversX_covers (denX_end hda'),
              Coverage.den_mark_conc (denX_den hda') h2⟩
        · exact ⟨a.af.fact, hadd, hac, Coverage.den_mark_conc (denX_den hda) ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := D6X.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    have mk : ∀ j', D6Xr (.init c.callee j') → j'.covers l1 →
        FlowRD P (forget6 D6Xr) c.callee l1 n2 l2 → ReachRD P (forget6 D6Xr) roots c.callee n2 l2 :=
      fun j' hj' hjc' hfr => ReachRD.down hRR he he1 hd1 ⟨_, hj', rfl⟩ hjc' hfr
    rcases coverage6X P taint counted L α sinks roots hwf hα hfc _ (D6X.initA hadd) hjc with
      ⟨g, hg, hdg, hfr⟩ | hreq
    · refine ⟨mk _ (D6X.initA hadd) hjc hfr, l1, _, g, hg, hdg, ?_⟩
      rcases Coverage.mark_cases (α c.callee a.af.fact).mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg', _⟩ :=
          coverage_conc6X P taint counted L α sinks roots hwf hα hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg', hfr⟩ :=
        coverage_conc6X P taint counted L α sinks roots hwf hα hfc hj' hjc' ht
      exact ⟨mk j' hj' hjc' hfr, l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strong6X

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH THE EXCLUSION (as `Coverage.vuln_found`): a real
    source-to-sink witness (a concrete flow from the zero location of a root, through a chain of
    calls, to a location at a sink node that the sink pattern covers) gives a `vuln` object of
    `D6X` (in some layer); the witness is den-aware for the summaries of `D6X` read without their
    exclusions (the input of the backward run). Hypotheses: S10, C1. -/
theorem vuln_found6X (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6Xr (.vuln M n s b)) ∧ ReachRD P (forget6 D6Xr) roots M n l := by
  obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := reach_strong6X P taint counted L α sinks roots hwf hα hR
  refine ⟨?_, hRR⟩
  rcases checkX_sound hT hd hsc with htr | ⟨hrq, hist⟩
  · exact ⟨_, D6X.vuln hf hs htr⟩
  · have hreq := D6X.reqSink hf hs hrq
    rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
    · exact absurd ht (hist t)
    · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hreq
      rcases checkX_sound hT hd' hsc with htr' | ⟨_, hist'⟩
      · exact ⟨_, D6X.vuln hf' hs htr'⟩
      · exact absurd ht (hist' t)

#print axioms vuln_found6X

end Run1

/-- THE VULNERABILITY THEOREM OF RUN 1 WITH THE EXCLUSION, THE POLICY (spec §6.2): `D6X` with the
    run-1 policy `policy1` reports every real vulnerability (in some layer). Only hypothesis: S10
    (`Program.WF`). -/
theorem vuln_found_policy6X {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (hwf : P.WF)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∃ b, D6X P taint counted L policy1 sinks roots (.vuln M n s b) :=
  (vuln_found6X P taint counted L policy1 sinks roots hwf (policy_applicable (fun _ => [])) hR hs
    hT hsc).1

#print axioms vuln_found_policy6X

/-! ## 4. The restricted forward run with the exclusion (`DRX`) -/

/-- A restricted run read without its exclusions and must flags (`XObj.forget`, then
    `TObj.forget`): every premise and every conclusion keeps its base fact, the exclusions are
    DROPPED (DESIGN A2: "the hand-off may drop `E`"). The backward run and the reports read a
    restricted run so. -/
def forgetX (R : XObj → Prop) (o : Obj) : Prop := ∃ x, R x ∧ x.forget.forget = o

theorem forgetX_vuln {R : XObj → Prop} {M : MethodId} {n : Node} {s : PFact} {b : Bool}
    (h : forgetX R (.vuln M n s b)) : R (.vuln M n s b) := by
  obtain ⟨x, hx, he⟩ := h
  cases x with
  | vuln M' n' s' d => cases he; exact hx
  | init => cases he
  | edge => cases he
  | added => cases he
  | req => cases he

/-- The concreteness invariant of a restricted run with exclusions (`RCov.ConcInv` with A2): every
    premise, conclusion and added fact has a concrete mark; a must-premise has the `.any` tail;
    every conclusion has no `*` tail and a well-formed annotation; there is no request. -/
def ConcX : XObj → Prop
  | .init _ i mi _ => (∃ t, i.mark = .conc t) ∧ (mi = true → i.kind = .any)
  | .edge _ i _ _ _ f => (∃ t, i.mark = .conc t) ∧ (∃ t, f.af.fact.mark = .conc t) ∧
      f.af.fact.kind.isStar = false ∧ WFX f
  | .added _ a _ _ => ∃ t, a.mark = .conc t
  | .req _ _ _ => False
  | .vuln _ _ _ _ => True

theorem startFact_nonstar_conc {j : PFact} {t : Mark} (h : j.mark = .conc t) :
    (startFact j).fact.kind.isStar = false := by
  obtain ⟨b, p, k, m⟩ := j
  have hm : m = .conc t := h
  subst hm
  cases k <;> rfl

theorem emitTX_some {emit : PFact → PFact → Excl → Option (PFact × Excl)} {d a j : PFact}
    {am mj : Bool} {aex jex : Excl} (h : emitTX emit d a am aex = some (j, mj, jex)) :
    emit d a aex = some (j, jex) ∧ mj = (am && j.kind.isAny) := by
  unfold emitTX at h
  cases he : emit d a aex with
  | none => rw [he] at h; cases h
  | some p =>
    obtain ⟨j0, jex0⟩ := p
    rw [he] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem emitTX_of {emit : PFact → PFact → Excl → Option (PFact × Excl)} {d a j : PFact}
    {aex jex : Excl} (h : emit d a aex = some (j, jex)) (am : Bool) :
    emitTX emit d a am aex = some (j, am && j.kind.isAny, jex) := by
  unfold emitTX
  rw [h]
  rfl

section RunR
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

local notation "DRXr" => DRX P taint counted L demand emit sat restrict recs sinks roots

/-- THE CONCRETENESS INVARIANT OF A RESTRICTED RUN WITH EXCLUSIONS (`RCov.concInvR_all` with A2):
    with a mark-copying emission (C3) the run starts from the zero fact and every object is
    concrete, a must-premise has the `.any` tail, no conclusion has the `*` tail, every annotation
    is well formed, and the run has no request. The records and the restriction do not matter. -/
theorem concX_all (hem : EmitCopiesMarkX emit) {o : XObj} (h : DRXr o) : ConcX o := by
  induction h with
  | root _ => exact ⟨⟨zeroMark, rfl⟩, fun h => Bool.noConfusion h⟩
  | @start M j mj jex _ ih =>
    obtain ⟨⟨t, ht⟩, hmk⟩ := ih
    refine ⟨⟨t, ht⟩, ⟨t, ?_⟩, ?_, startX_wf _ _ _⟩
    · rw [startX_af, startT_mark]; exact ht
    · cases mj with
      | false =>
        show (startFact j).fact.kind.isStar = false
        exact startFact_nonstar_conc ht
      | true =>
        show (normX ⟨⟨j, false⟩, jex⟩).af.fact.kind.isStar = false
        rw [normX_fact]
        show j.kind.isStar = false
        rw [hmk rfl]
        rfl
  | step _ _ hf' ih =>
    obtain ⟨hi, ⟨t1, h1⟩, hns, hw⟩ := ih
    obtain ⟨hm, hns'⟩ := transferX_conc hns h1 hf'
    exact ⟨hi, hm, hns', transferX_wf hw hf'⟩
  | reqStmt _ _ hq ih =>
    obtain ⟨_, ⟨t1, h1⟩, _, _⟩ := ih
    have hq' := transferX_reqs hq
    rw [transferT_reqs, transfer_reqs_of_conc h1] at hq'
    exact List.not_mem_nil hq'
  | pass _ _ _ ih => exact ih
  | added _ _ _ ha ih =>
    obtain ⟨_, ⟨t1, h1⟩, _, _⟩ := ih
    exact bindX_mark_conc h1 ha
  | initR _ _ hemit ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨he, hmj⟩ := emitTX_some hemit
    refine ⟨⟨t, by rw [hem _ _ _ _ _ he]; exact ht⟩, fun h => ?_⟩
    rw [hmj] at h
    exact isAny_eq ((Bool.and_eq_true _ _).mp h).2
  | ret _ _ _ ha _ _ _ _ _ hr _ hr' ih _ _ =>
    obtain ⟨hi, ⟨t1, h1⟩, _, _⟩ := ih
    obtain ⟨t2, h2⟩ := bindX_mark_conc h1 ha
    obtain ⟨hm, hns⟩ := ret_conc (counted := counted) (L := L) h2 hr hr' rfl
    exact ⟨hi, hm, hns, limitFX_wf counted L (applyEdgeX_wf hr')⟩
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ _ _ ha _ _ hr _ hr' ih =>
    obtain ⟨hi, ⟨t1, h1⟩, _, _⟩ := ih
    obtain ⟨t2, h2⟩ := bindX_mark_conc h1 ha
    obtain ⟨hm, hns⟩ := ret_conc (counted := counted) (L := L)
      (x := recLayerX mj (sat j jex a.af.fact a.ex) r') h2 hr hr'
      (by rw [recLayerX_af, recLayer_fact])
    exact ⟨hi, hm, hns, limitFX_wf counted L (recLayerX_wf _ _ (applyEdgeX_wf hr'))⟩
  | reqSink _ _ hc ih =>
    obtain ⟨⟨t, ht⟩, _⟩ := ih
    exact check_request_star (checkX_request hc) t ht
  | answer _ _ _ _ ih _ => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih _ => exact ih.elim
  | vuln _ _ _ _ => trivial
  | clean _ _ hf' ih =>
    obtain ⟨hi, ⟨t1, h1⟩, hns, hw⟩ := ih
    obtain ⟨hm, hns'⟩ := cleanResX_conc hw hns h1 hf'
    exact ⟨hi, hm, hns', cleanResX_wf hw hf'⟩
  | reqClean _ _ hq ih =>
    obtain ⟨_, ⟨t1, h1⟩, _, _⟩ := ih
    exact (cleanRes_reqs_abstract (cleanResX_reqs_sub hq)).1 t1 h1
  | filt _ _ _ ih => exact ih

#print axioms concX_all

/-- A restricted run with exclusions has no request (C3). -/
theorem noReqX (hem : EmitCopiesMarkX emit) {M : MethodId} {i : PFact} {t : Mark} :
    ¬ DRXr (.req M i t) :=
  fun h => concX_all P taint counted L demand emit sat restrict recs sinks roots hem h

#print axioms noReqX

/-- THE COVERAGE THEOREM OF A RESTRICTED RUN WITH THE EXCLUSION (as `RCov.coverageR`, DESIGN A2).
    If a premise `(i, mi, iex)` of `M` in `DRX` covers the entry location `l0` in its ADMITTED
    location set (a must-premise or a premise emitted from an `[any-taint]/E` added fact can carry
    an exclusion), and the value at `l0` flows to `l` at `n` along a flow that the demand of the
    previous run demands, then an edge of `(i, mi, iex)` at `n` covers the pair in the refined
    relation. The run has no request. The flow is den-aware for the summaries of this run read
    without their exclusions (`FlowRD`, the input of the next backward run). Hypotheses: S10
    (`Program.WF`), C2 for the annotated emission (`EmitContractX`), C3 (`EmitCopiesMarkX`), C5 for
    conclusions without `*` (`RestrictContractNSX`); C4 is not read (no request). -/
theorem coverageRX (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hR : RestrictContractNSX restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i mi iex, DRXr (.init M i mi iex) → coversX i iex l0 →
      ∃ f, DRXr (.edge M i mi iex n f) ∧ denX i iex f.af.fact f.ex l0 l ∧
        FlowRD P (forgetX DRXr) M l0 n l := by
  have hcx : ∀ {o}, DRXr o → ConcX o :=
    fun h => concX_all P taint counted L demand emit sat restrict recs sinks roots hem h
  induction hfl with
  | start M l0 =>
    intro i mi iex hi hc
    exact ⟨_, DRX.start hi, startX_sound hc, FlowRD.start M l0⟩
  | step _ he hs ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    rcases transferX_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ⟨r, DRX.step hf he hr, hdr, FlowRD.step hfr he hs⟩
    · obtain ⟨_, ⟨t, ht⟩, _⟩ := hcx hf
      exact absurd ht (habs t)
  | @pass M l0 n l n' c _ he hm ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    have hb : memB f.af.fact.base c.touched = false := by
      rw [← hd.2.1]
      exact hm
    exact ⟨f, DRX.pass hf he hb, hd, FlowRD.pass hfr he hm⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 d p _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    -- the caller fact reaches the call; bind it into the callee
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := DRX.added hf he he1 ha
    have hacX : coversX a.af.fact a.ex l1 := denX_end hda
    obtain ⟨t, ht⟩ : ∃ t, a.af.fact.mark = .conc t := hcx hadd
    -- the demand edge covers `l1`: the emission gives the premise `(j, jex)` (C2)
    obtain ⟨j, jex, hemit, hjc, hsat⟩ := hE d.din a.af.fact a.ex l1 t ht hdin hacX
    have hj := DRX.initR hadd hdem (emitTX_of hemit _)
    -- the callee exit pair, restricted by the demand edge (C5), applied, bound back
    obtain ⟨g, hg, hdg, hfc'⟩ := ihc j _ jex hj hjc
    have hgns : g.af.fact.kind.isStar = false := (hcx hg).2.2.1
    obtain ⟨g', hres, hdg', _⟩ := hR j jex g d p l1 l2 hgns hdg (RCov.covers_loc hdin) hdout hp
    obtain ⟨r, hr, hdr⟩ := summary_stepConcX ht hda hdg'
    obtain ⟨r', hr', hdr'⟩ := bind_outX hwf he he2 hdr hd2
    exact ⟨_, DRX.ret hf he he1 ha hj hg hdem hres hsat hr he2 hr', limitFX_sound hdr',
      FlowRD.call hfr he he1 hd1 hfc' ⟨_, hj, rfl⟩ ⟨_, hg, rfl⟩ (coversX_covers hjc)
        (denX_den hdg) he2 hd2⟩
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    rcases cleanResX_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ⟨r, DRX.clean hf he hr, hdr, FlowRD.clean hfr he hcl⟩
    · obtain ⟨_, ⟨t, ht⟩, _⟩ := hcx hf
      exact absurd ht (habs t)
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i mi iex hi hc
    obtain ⟨f, hf, hd, hfr⟩ := ih i mi iex hi hc
    exact ⟨f, DRX.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) (denX_den hd) hl), hd,
      FlowRD.filt hfr he hl⟩

#print axioms coverageRX

/-- `coverageRX` in the form of `RCov.coverageR`: the covered flow is demanded by the summaries
    of this run (read without their exclusions). -/
theorem coverageRX_summary (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hR : RestrictContractNSX restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i mi iex, DRXr (.init M i mi iex) → coversX i iex l0 →
      ∃ f, DRXr (.edge M i mi iex n f) ∧ denX i iex f.af.fact f.ex l0 l ∧
        FlowR P (summaryDemand P (forgetX DRXr)) M l0 n l := by
  intro i mi iex hi hc
  obtain ⟨f, hf, hd, hfr⟩ :=
    coverageRX P taint counted L demand emit sat restrict recs sinks roots hwf hE hem hR hfl
      i mi iex hi hc
  exact ⟨f, hf, hd, Backward.flowRD_flowR hfr⟩

#print axioms coverageRX_summary

/-- The strengthened reach statement of a restricted run with the exclusion (as
    `Backward.reach_strongRD`): a demanded real witness is a den-aware witness of the summaries of
    this run (read without their exclusions), and an edge covers it in the refined relation. -/
theorem reach_strongRX (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hR : RestrictContractNSX restrict)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachR P demand roots M n l) :
    ReachRD P (forgetX DRXr) roots M n l ∧
    ∃ l0 i mi iex f, DRXr (.edge M i mi iex n f) ∧ denX i iex f.af.fact f.ex l0 l := by
  have hcx : ∀ {o}, DRXr o → ConcX o :=
    fun h => concX_all P taint counted L demand emit sat restrict recs sinks roots hem h
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverageRX P taint counted L demand emit sat restrict recs sinks roots
      hwf hE hem hR hfl zeroFact false Excl.empty (DRX.root hM)
      (covers_coversX Coverage.zeroFact_covers)
    exact ⟨ReachRD.root hM hfr, zeroLoc, zeroFact, false, Excl.empty, f, hf, hd⟩
  | @down M n l n' c e l1 n2 l2 d _ he he1 hd1 hdem hdin hfc ih =>
    obtain ⟨hRR, l0, i, mi, iex, f, hf, hd⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_inX hwf he he1 hd hd1
    have hadd := DRX.added hf he he1 ha
    obtain ⟨t, ht⟩ : ∃ t, a.af.fact.mark = .conc t := hcx hadd
    obtain ⟨j, jex, hemit, hjc, _⟩ := hE d.din a.af.fact a.ex l1 t ht hdin (denX_end hda)
    have hj := DRX.initR hadd hdem (emitTX_of hemit _)
    obtain ⟨g, hg, hdg, hfr⟩ := coverageRX P taint counted L demand emit sat restrict recs sinks
      roots hwf hE hem hR hfc j _ jex hj hjc
    exact ⟨ReachRD.down hRR he he1 hd1 ⟨_, hj, rfl⟩ (coversX_covers hjc) hfr, l1, j, _, jex, g,
      hg, hdg⟩

#print axioms reach_strongRX

/-- THE VULNERABILITY THEOREM OF A RESTRICTED RUN WITH THE EXCLUSION (as `RCov.vuln_foundR`): a
    real source-to-sink witness that the demand of the previous run demands gives a `vuln` object
    of `DRX` (in some layer), and the witness is den-aware for the summaries of this run read
    without their exclusions. Hypotheses: as `coverageRX`. -/
theorem vuln_foundRX (hwf : P.WF) (hE : EmitContractX emit sat) (hem : EmitCopiesMarkX emit)
    (hR : RestrictContractNSX restrict)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DRXr (.vuln M n s b)) ∧ ReachRD P (forgetX DRXr) roots M n l := by
  obtain ⟨hRR, l0, i, mi, iex, f, hf, hd⟩ :=
    reach_strongRX P taint counted L demand emit sat restrict recs sinks roots hwf hE hem hR hRe
  refine ⟨?_, hRR⟩
  rcases checkX_sound hT hd hsc with htr | ⟨hrq, _⟩
  · exact ⟨_, DRX.vuln hf hs htr⟩
  · exact (noReqX P taint counted L demand emit sat restrict recs sinks roots hem
      (DRX.reqSink hf hs hrq)).elim

#print axioms vuln_foundRX

end RunR

/-- COVERAGE OF THE SPEC RESTRICTED RUN WITH THE EXCLUSION (`DRXs`: `emitX`, `satX`, `restrictX`):
    `coverageRX` with the contracts discharged (`emitX_contract`, `emitX_copies`,
    `restrictX_contractNS`). Only hypothesis: S10 (`Program.WF`). -/
theorem coverageRXs {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (hwf : P.WF)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i mi iex, DRXs P taint counted L demand recs sinks roots (.init M i mi iex) →
      coversX i iex l0 →
      ∃ f, DRXs P taint counted L demand recs sinks roots (.edge M i mi iex n f) ∧
        denX i iex f.af.fact f.ex l0 l ∧
        FlowRD P (forgetX (DRXs P taint counted L demand recs sinks roots)) M l0 n l :=
  coverageRX P taint counted L demand emitX satX restrictX recs sinks roots hwf emitX_contract
    emitX_copies restrictX_contractNS hfl

#print axioms coverageRXs

/-- THE VULNERABILITY THEOREM OF THE SPEC RESTRICTED RUN WITH THE EXCLUSION (`DRXs`): a demanded
    real witness is reported (in some layer), and it is den-aware for the summaries of the run read
    without their exclusions. Only hypothesis: S10 (`Program.WF`). -/
theorem vuln_foundRXs {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} (hwf : P.WF)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachR P demand roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, DRXs P taint counted L demand recs sinks roots (.vuln M n s b)) ∧
    ReachRD P (forgetX (DRXs P taint counted L demand recs sinks roots)) roots M n l :=
  vuln_foundRX P taint counted L demand emitX satX restrictX recs sinks roots hwf emitX_contract
    emitX_copies restrictX_contractNS hRe hs hT hsc

#print axioms vuln_foundRXs

/-! ## 5. The iteration

  The sequence of the spec with the exclusion: run 1 is `D6X` with the policy `policy1`; after each
  forward run, the backward run of the user's design (`Backward.DB` on the reversed program) is
  restricted by (at least) the reversed summaries of that forward run READ WITHOUT ITS EXCLUSIONS
  (`forget6`, `forgetX`: the hand-off may drop `E`, DESIGN A2) and seeded (at least) at the sinks
  that it reported; forward run `k + 1` is the spec restricted run with the exclusion `DRXs` whose
  demand contains the hand-off of that backward run. The proof is the induction of
  `Backward.iteration_invariant_D` with the refined forward theorems: each refined forward run
  gives the den-aware witness of its own summaries (`vuln_found6X`, `vuln_foundRXs`), and the
  backward contract `Backward.B_general` (in the seeded form `FSeeds.B_src`) needs nothing else of
  the forward run. -/

/-- The run sequence with the exclusion: run 0 (the spec's run 1) is `D6X` with `policy1`; run
    `k + 1` is `DRXs` with the demand `dem k` and the records `recs k`. Each run is read without
    its exclusions and must flags (the backward run and the reports read it so). -/
def runSeqX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (dem : Nat → MethodId → DemandEdge → Prop)
    (recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Obj → Prop
  | 0     => forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
  | k + 1 => forgetX (DRXs P taint counted (Ls (k + 1)) (dem k) (recs k) sinks roots)

section IterX
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop}
  {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}

/-- The invariant of the iteration with the exclusion: forward run `k` justifies the witness (a
    den-aware witness of its own summaries, read without the exclusions) and reports its
    vulnerability. -/
theorem iteration_invariantX (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    (hX : Backward.ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeqX P taint counted Ls dem recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachRD P (runSeqX P taint counted Ls dem recs sinks roots k) roots M n l ∧
      ∃ b, runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨⟨b, hb⟩, hRR⟩ := vuln_found6X P taint counted (Ls 0) policy1 sinks roots hW
      (policy_applicable (fun _ => [])) hRe hs hT' hsc
    show ReachRD P (forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)) roots M n l ∧
      ∃ b, forget6 (D6X P taint counted (Ls 0) policy1 sinks roots) (.vuln M n s b)
    exact ⟨hRR, b, _, hb, rfl⟩
  | succ k ih =>
    -- contract B: the backward run after forward run `k` demands the justified witness
    have hRk := RCov.reachR_mono (hdem k)
      (Backward.B_general hW hT hmr hNZB hZ hX hk (hseeds k) (hdemB k) M n l s T hs hT' hsc
        ih.1 ih.2)
    -- forward run `k + 1` covers the demanded witness
    obtain ⟨⟨b, hb⟩, hRR⟩ := vuln_foundRXs (taint := taint) (counted := counted) (L := Ls (k + 1))
      (recs := recs k) hW hRk hs hT' hsc
    show ReachRD P (forgetX (DRXs P taint counted (Ls (k + 1)) (dem k) (recs k) sinks roots))
        roots M n l ∧
      ∃ b, forgetX (DRXs P taint counted (Ls (k + 1)) (dem k) (recs k) sinks roots) (.vuln M n s b)
    exact ⟨hRR, b, _, hb, rfl⟩

#print axioms iteration_invariantX

/-- THE GENERAL ITERATION THEOREM WITH THE EXCLUSION: every forward run of the sequence (run 1 =
    `D6X`, the backward runs = `Backward.DB`, the forward restricted runs = `DRXs`) reports every
    real vulnerability, in some layer. Hypotheses: those of `Backward.iteration_general`: on the
    program S10 (`Program.WF`), mark-agnostic binding targets (`BindTargetsStar`, S11 (a)),
    mark-reversible statements (`StmtsMarkRev`), no zero binding back (`NoZeroBack`), the zero
    kept by every instruction (`ZeroKept`), every node reaches its exit (`ExitReach`); the sinks
    have the tail `$` or `[any]`; the backward demand contains the reversed summaries of the
    previous forward run READ WITHOUT ITS EXCLUSIONS, the seeds contain the sinks it reported, and
    the demand of each forward run contains the hand-off of the backward run before it (any
    backward field limit and record set; any forward records). -/
theorem iteration_generalX (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    (hX : Backward.ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeqX P taint counted Ls dem recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b) :=
  fun k => (iteration_invariantX hW hT hmr hNZB hZ hX hk LB demB recsB seeds hdemB hseeds hdem
    hRe hs hT' hsc k).2

#print axioms iteration_generalX

/-- EVERY COMPLETE FORWARD RUN WITH THE EXCLUSION REPORTS EVERY REAL VULNERABILITY, IN SOME LAYER
    (the form to cite; `iteration_generalX` with the runs named): run 1 `D6X` reports it, and every
    forward restricted run `DRXs` (`k + 1`) reports it. Hypotheses: those of
    `iteration_generalX` (= those of `Backward.iteration_general`, with the hand-off read from the
    refined runs without their exclusions). -/
theorem iteration_reportsX (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    (hX : Backward.ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand P
      (runSeqX P taint counted Ls dem recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqX P taint counted Ls dem recs sinks roots k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6X P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, DRXs P taint counted (Ls (k + 1)) (dem k) (recs k) sinks roots (.vuln M n s b) := by
  have h := iteration_generalX hW hT hmr hNZB hZ hX hk LB demB recsB seeds hdemB hseeds hdem
    hRe hs hT' hsc
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h 0
    exact ⟨b, forget6_vuln hb⟩
  · obtain ⟨b, hb⟩ := h (k + 1)
    exact ⟨b, forgetX_vuln hb⟩

#print axioms iteration_reportsX

end IterX

/-! ### The iteration with forward seeds -/

/-- The run sequence with forward seeds and the exclusion: run 0 is `D6X` of the full program;
    run `k + 1` is `DRXs` of `FSeeds.keepSources P (σ k)` (only the seeded unconditional sources
    fire). Each run is read without its exclusions and must flags. -/
def runSeqSrcX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (dem : Nat → MethodId → DemandEdge → Prop)
    (recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Nat → Obj → Prop
  | 0     => forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)
  | k + 1 => forgetX (DRXs (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) (recs k)
      sinks roots)

section IterSrcX
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {taint : TaintEdges} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop}
  {recs : Nat → MethodId → PFact × Bool × Excl × XFact → Prop}

/-- The invariant of the iteration with forward seeds and the exclusion (as
    `FSeeds.iteration_src_invariant`): forward run `k` justifies the witness in its own program and
    reports its vulnerability. -/
theorem iteration_src_invariantX (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    (hX : Backward.ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand (FSeeds.progSrc P σ k)
      (runSeqSrcX P taint counted Ls σ dem recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqSrcX P taint counted Ls σ dem recs sinks roots k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (Backward.DB (Reverse.Program.rev P) counted (LB k) (demB k)
      emitM satI restrictU (recsB k) [] roots (seeds k) true) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachRD (FSeeds.progSrc P σ k) (runSeqSrcX P taint counted Ls σ dem recs sinks roots k)
        roots M n l ∧
      ∃ b, runSeqSrcX P taint counted Ls σ dem recs sinks roots k (.vuln M n s b) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨⟨b, hb⟩, hRR⟩ := vuln_found6X P taint counted (Ls 0) policy1 sinks roots hW
      (policy_applicable (fun _ => [])) hRe hs hT' hsc
    show ReachRD P (forget6 (D6X P taint counted (Ls 0) policy1 sinks roots)) roots M n l ∧
      ∃ b, forget6 (D6X P taint counted (Ls 0) policy1 sinks roots) (.vuln M n s b)
    exact ⟨hRR, b, _, hb, rfl⟩
  | succ k ih =>
    -- the witness of forward run `k` is a witness of `P`, so contract B with seeds applies
    have hP := FSeeds.reachRD_progSrc ih.1
    have hdemB' : ∀ m d, Backward.revSummaryDemand P
        (runSeqSrcX P taint counted Ls σ dem recs sinks roots k) m d → demB k m d :=
      fun m d h => hdemB k m d (by rw [FSeeds.revSummaryDemand_progSrc]; exact h)
    have hRR := RCov.reachR_mono (hdem k)
      (FSeeds.B_src hW hT hmr hNZB hZ hX hk (hseeds k) hdemB' (hσ k) M n l s T hs hT' hsc hP ih.2)
    -- forward run `k + 1` (on the seeded program) covers the demanded witness
    have hW' : (FSeeds.keepSources P (σ k)).WF := FSeeds.keep_WF hW
    obtain ⟨⟨b, hb⟩, hRD⟩ := vuln_foundRXs (taint := taint) (counted := counted)
      (L := Ls (k + 1)) (recs := recs k) hW' hRR hs hT' hsc
    show ReachRD (FSeeds.keepSources P (σ k)) (forgetX (DRXs (FSeeds.keepSources P (σ k)) taint
        counted (Ls (k + 1)) (dem k) (recs k) sinks roots)) roots M n l ∧
      ∃ b, forgetX (DRXs (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) (recs k)
        sinks roots) (.vuln M n s b)
    exact ⟨hRD, b, _, hb, rfl⟩

#print axioms iteration_src_invariantX

/-- THE ITERATION THEOREM WITH FORWARD SEEDS AND THE EXCLUSION (as `FSeeds.iteration_src`): run 1
    (`D6X`) analyses the full program; forward run `k + 1` (`DRXs`) fires only the unconditional
    sources in `σ k`, which contains the source hits of the backward run after forward run `k`.
    Every forward run reports every real vulnerability of `P`, in some layer. Hypotheses: those of
    `FSeeds.iteration_src`, with the hand-off read from the refined runs without their
    exclusions. -/
theorem iteration_srcX (hW : P.WF) (hT : Reverse.BindTargetsStar P)
    (hmr : Backward.StmtsMarkRev P) (hNZB : Backward.NoZeroBack P) (hZ : Backward.ZeroKept P)
    (hX : Backward.ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, Backward.revSummaryDemand (FSeeds.progSrc P σ k)
      (runSeqSrcX P taint counted Ls σ dem recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqSrcX P taint counted Ls σ dem recs sinks roots k (.vuln M n s b) → (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, Backward.demOf (Reverse.Program.rev P) (Backward.DB (Reverse.Program.rev P)
      counted (LB k) (demB k) emitM satI restrictU (recsB k) [] roots (seeds k) true) m d →
      dem k m d)
    (hσ : ∀ k M n e, FSeeds.srcHit P (Backward.DB (Reverse.Program.rev P) counted (LB k) (demB k)
      emitM satI restrictU (recsB k) [] roots (seeds k) true) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    (∃ b, D6X P taint counted (Ls 0) policy1 sinks roots (.vuln M n s b)) ∧
    ∀ k, ∃ b, DRXs (FSeeds.keepSources P (σ k)) taint counted (Ls (k + 1)) (dem k) (recs k) sinks
      roots (.vuln M n s b) := by
  have h := fun k => (iteration_src_invariantX hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds hdemB
    hseeds hdem hσ hRe hs hT' hsc k).2
  refine ⟨?_, fun k => ?_⟩
  · obtain ⟨b, hb⟩ := h 0
    exact ⟨b, forget6_vuln hb⟩
  · obtain ⟨b, hb⟩ := h (k + 1)
    exact ⟨b, forgetX_vuln hb⟩

#print axioms iteration_srcX

end IterSrcX

/-! ## 6. CEGAR on the suggested route of the brief

  The brief suggests to prove the iteration through the `[any-taint]` model without the
  exclusion: "(a) the hand-off of a `DRX` run contains the hand-off of the `DRT` run on the same
  demand; (b) so the sequence of `DRX` runs has (at least) the demands of the `DRT` sequence;
  (c) `AnyTaintSim.iteration_generalT`; (d) the refined coverage". Step (a) is FALSE: the
  exclusion REMOVES summaries (the reads through an excluded accessor), so the `DRX` hand-off can
  be strictly SMALLER than the `DRT` hand-off (the simulation goes the other way: every refined
  object has a base object, `Sim6X`/`SimRX`). Then (b) fails, and (c) gives witnesses demanded by
  the wrong sequence. The counterexample (`CexRoute`): one method,
      `this = srcAny()` (a taint edge, `this.[any-taint]`);  `this.name = v` (the strong write);
      `x = this; y = this.name` (a copy and a read through the overwritten field).
  `DRT` demotes the keep edge of the write to `[any]` (demand), and the read gives
  `(y, [], [any], T)` at the exit: its hand-off has the demand edge `D-c = (y, [any])`. `DRX` keeps
  `(this, [], [any-taint], {name}, T)` normal, and the read through `name` gives nothing: no exit
  fact on `y`, so its hand-off does not have that demand edge (`rx_no_y`). The flow it removes is
  not real (`this.name` holds the untainted `v`). So the iteration is proved directly
  (`iteration_reportsX`, Part 5): the backward contract needs only the den-aware witnesses that each
  refined run gives itself. -/

namespace CexRoute

def src : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 5⟩)
/-- `this = srcAny()`: the zero keep edge and the source with an `[any]` target. -/
def s1 : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), src]⟩
def idE : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨1, [], .star (.set []), .star⟩)
def readE : MicroEdge := (⟨1, [3], .star (.set []), .star⟩, ⟨4, [], .star (.set []), .star⟩)
/-- `x = this; y = this.name` (`name = 3`, `y = 4`). -/
def s3 : Stmt := ⟨[1, 4], [idE, readE]⟩
/-- The program: `s1`, then the strong write `this.name = v` (`Vec.setter`), then `s3`. -/
def Pc : Program :=
  ⟨fun _ => 0, fun _ => 3, [(0, 0, .stmt s1, 1), (0, 1, .stmt Vec.setter, 2), (0, 2, .stmt s3, 3)]⟩
def taintC : TaintEdges := fun e => decide (e = src)
def cnt : Acc → Bool := fun _ => true
def noDem : MethodId → DemandEdge → Prop := fun _ _ => False

/-- The `[any-taint]` run without the exclusion (spec rules). -/
abbrev RT := DRT Pc taintC cnt 3 noDem emitM satI restrictU (fun _ _ => False) [] [0]
/-- The run with the exclusion, on the same demand (spec rules). -/
abbrev RX := DRXs Pc taintC cnt 3 noDem (fun _ _ => False) [] [0]

/-- The exit fact of `DRT` on `y`: `(y, [], [any], T)`, demand. -/
def gY : AFact := ⟨⟨4, [], .any, .conc 5⟩, true⟩
/-- The demand edge that the `DRT` hand-off gives for it: `D-c = (y, [any])`, `D-p = zero`. -/
def dW : DemandEdge := ⟨gY.fact, some zeroFact⟩

theorem e1 : ((0 : MethodId), (0 : Node), Instr.stmt s1, (1 : Node)) ∈ Pc.edges :=
  List.mem_cons_self ..
theorem e2 : ((0 : MethodId), (1 : Node), Instr.stmt Vec.setter, (2 : Node)) ∈ Pc.edges :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem e3 : ((0 : MethodId), (2 : Node), Instr.stmt s3, (3 : Node)) ∈ Pc.edges :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `DRT` has the exit edge `(y, [], [any], T)` (the read after the demoted keep edge). -/
theorem rt_exit : RT (.edge 0 zeroFact false 3 gY) := by
  have h0 : RT (.init 0 zeroFact false) := DRT.root (List.mem_singleton.mpr rfl)
  have h1 : RT (.edge 0 zeroFact false 0 ⟨zeroFact, false⟩) := DRT.start h0
  have h2 : RT (.edge 0 zeroFact false 1 ⟨⟨1, [], .any, .conc 5⟩, false⟩) :=
    DRT.step h1 e1 (by decide)
  have h3 : RT (.edge 0 zeroFact false 2 ⟨⟨1, [], .any, .conc 5⟩, true⟩) :=
    DRT.step h2 e2 (by decide)
  exact DRT.step h3 e3 (by decide)

/-- THE HAND-OFF OF `DRT` HAS THE DEMAND EDGE `dW`. -/
theorem rt_handoff : Backward.revSummaryDemand Pc (AnyTaintSim.forgetRun RT) 0 dW :=
  ⟨zeroFact, gY.fact,
    ⟨⟨_, DRT.root (List.mem_singleton.mpr rfl), rfl⟩, Or.inr ⟨gY, ⟨_, rt_exit, rfl⟩, rfl⟩⟩, rfl⟩

#print axioms rt_handoff

def xZ : XFact := ⟨⟨zeroFact, false⟩, Excl.empty⟩
def xA : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, Excl.empty⟩
def xB : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [3]⟩

/-- The conclusions of `DRX` at each node. -/
def allowed : Node → List XFact
  | 0 => [xZ]
  | 1 => [xZ, xA]
  | 2 => [xZ, xB]
  | 3 => [xZ, xB]
  | _ => []

/-- The objects of `DRX` on `Pc`: the zero premise, and the conclusions of `allowed`. -/
def Inv : XObj → Prop
  | .init M j mj jex => M = 0 ∧ j = zeroFact ∧ mj = false ∧ jex = Excl.empty
  | .edge M j mj jex n f => M = 0 ∧ j = zeroFact ∧ mj = false ∧ jex = Excl.empty ∧ f ∈ allowed n
  | .added _ _ _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

theorem step_ok {M : MethodId} {n n' : Node} {s : Stmt} (he : (M, n, Instr.stmt s, n') ∈ Pc.edges) :
    ∀ f, f ∈ allowed n → (∀ f', f' ∈ (transferX taintC cnt 3 s f).facts → f' ∈ allowed n') ∧
      (transferX taintC cnt 3 s f).reqs = [] := by
  cases he with
  | head => decide
  | tail _ he =>
    cases he with
    | head => decide
    | tail _ he =>
      cases he with
      | head => decide
      | tail _ he => cases he

theorem no_call {M : MethodId} {n n' : Node} {c : Call} : (M, n, Instr.call c, n') ∉ Pc.edges := by
  intro h
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem no_clean {M : MethodId} {n n' : Node} {cl : Cleaner} :
    (M, n, Instr.clean cl, n') ∉ Pc.edges := by
  intro h
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem no_filt {M : MethodId} {n n' : Node} {b : Base} {may : List Acc → Bool} :
    (M, n, Instr.filt b may, n') ∉ Pc.edges := by
  intro h
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Every object of `DRX` on `Pc` is in `Inv`. -/
theorem rx_inv {o : XObj} (h : RX o) : Inv o := by
  induction h with
  | root hM =>
    cases hM with
    | head => exact ⟨rfl, rfl, rfl, rfl⟩
    | tail _ h => cases h
  | start _ ih =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ih
    exact ⟨rfl, rfl, rfl, rfl, by decide⟩
  | step _ he hf' ih =>
    obtain ⟨rfl, rfl, rfl, rfl, hf⟩ := ih
    exact ⟨rfl, rfl, rfl, rfl, (step_ok he _ hf).1 _ hf'⟩
  | reqStmt _ he hq ih =>
    obtain ⟨rfl, rfl, rfl, rfl, hf⟩ := ih
    rw [(step_ok he _ hf).2] at hq
    exact List.not_mem_nil hq
  | pass _ he _ _ => exact absurd he no_call
  | added _ he _ _ _ => exact absurd he no_call
  | initR _ _ _ ih => exact ih.elim
  | ret _ he _ _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd he no_call
  | retRec _ he _ _ _ _ _ _ _ _ => exact absurd he no_call
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih _ => exact ih.elim
  | reqUp _ _ he _ _ _ _ _ _ _ => exact absurd he no_call
  | vuln _ hs _ _ => cases hs
  | clean _ he _ _ => exact absurd he no_clean
  | reqClean _ he _ _ => exact absurd he no_clean
  | filt _ he _ _ => exact absurd he no_filt

#print axioms rx_inv

/-- No exit conclusion of `DRX` is on `y`. -/
theorem rx_exit_base {j : PFact} {g' : AFact} (h : forgetX RX (.edge 0 j 3 g')) :
    g'.fact.base ≠ 4 := by
  obtain ⟨x, hx, hxe⟩ := h
  have hinv := rx_inv hx
  cases x with
  | edge M' j' mj jex n f =>
    obtain ⟨_, _, _, _, hf⟩ := hinv
    have hxe' : Obj.edge M' j' n f.af = Obj.edge 0 j 3 g' := hxe
    injection hxe' with _ _ h3 h4
    subst h3
    subst h4
    exact (by decide : ∀ f, f ∈ allowed 3 → f.af.fact.base ≠ 4) f hf
  | init => cases hxe
  | added => cases hxe
  | req => cases hxe
  | vuln => cases hxe

/-- THE HAND-OFF OF `DRX` DOES NOT HAVE THE DEMAND EDGE `dW`. -/
theorem rx_no_y : ¬ Backward.revSummaryDemand Pc (forgetX RX) 0 dW := by
  rintro ⟨j, g, ⟨_, hd⟩, he⟩
  have hg : g = gY.fact := (congrArg DemandEdge.din he).symm
  rcases hd with hd | ⟨g', hg', hdo⟩
  · exact nomatch hd
  · have hb := rx_exit_base hg'
    have e : g = g'.fact := Option.some.inj hdo
    rw [← e, hg] at hb
    exact hb rfl

#print axioms rx_no_y

/-- CEGAR, STEP (a) OF THE SUGGESTED ROUTE IS FALSE: on the same program and the same demand, the
    hand-off of the `[any-taint]` run without the exclusion (`DRT`) has a demand edge that the
    hand-off of the run with the exclusion (`DRXs`) does not have. -/
theorem route_a_false :
    Backward.revSummaryDemand Pc (AnyTaintSim.forgetRun RT) 0 dW ∧
    ¬ Backward.revSummaryDemand Pc (forgetX RX) 0 dW :=
  ⟨rt_handoff, rx_no_y⟩

#print axioms route_a_false

/-- The keep edge of the strong write does not relate the overwritten location `this.name`
    (`this.* →_{name} this.*`): so the refined result `(this, [], [any-taint], {name}, T)` need
    not cover it (the write edge `v.* → this.name.*` covers the new value). -/
theorem keep_excludes_name :
    ¬ den Vec.keepEdge.1 Vec.keepEdge.2 ⟨1, [3], 5⟩ ⟨1, [3], 5⟩ := by
  rintro ⟨_, _, _, _, _, σ, τ, h0, _, _, htf⟩
  have hσ : σ = [3] := h0.symm
  have htf' : τ = σ ∧ (Excl.set [3]).admits σ = true := htf
  rw [hσ] at htf'
  exact absurd htf'.2 (by decide)

#print axioms keep_excludes_name

end CexRoute

end ApSpec.AnyTaintExCov
