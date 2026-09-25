import MarkScan.Selection
import MarkScan.FlowSensitive

/-!
# Relevance over an arbitrary applicability predicate (obligation O-FS-3)

`Selection` proves T-REL for `Needed`, the relevance pass computed over the
flow-insensitive `Applicable`. Option 3* prunes sites by the smaller
`ApplicableFS` and computes its relevance pass over `ApplicableFS` as well, so
both the enabled sites and the needed marks shrink. This module shows that the
restricted full scan is still exact.

1. `NeededOver p App` is `Needed` with the applicability predicate as a
   parameter. `needed_eq_neededOver` shows that `Needed` is the instance
   `App = Applicable p`.
2. `relOver_preserves_needed_strong` and `relOver_fires_iff`: T-REL for any
   `App` that covers every site whose cube holds in the baseline engine run.
   The proof is the one of `Selection` with `Applicable` replaced by `App`.
3. `ecube_applicableFS`: `ApplicableFS` is such an `App` (every site, not only
   sinks, whose cube holds in the engine model is 3*-applicable).
4. `markset_exact_fs`: the 3* selection is exact.
-/

namespace MarkScan

/-! ## 1. Relevance parameterized by applicability -/

/-- Marks needed by the full scan when sites are selected by the predicate
`App`. The five rules are those of `Needed`, with `Applicable p` replaced by
`App`: seeds from the atoms and gens of `App`-sinks, backward closure over
`App`-sites that generate a needed mark, every recorded cleaner atom, and the
atoms of `App`-pass-throughs. -/
inductive NeededOver (p : Program) (App : Node → Pc → ESite → Prop) : Mark → Prop
  | sinkAtom {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      App n pc σ → σ.kind = .sink → m ∈ σ.abstract.cond.atoms → NeededOver p App m
  | sinkGen {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      App n pc σ → σ.kind = .sink → m ∈ σ.abstract.gens → NeededOver p App m
  | trans {n : Node} {pc : Pc} {σ : ESite} {g m : Mark} :
      App n pc σ → g ∈ σ.abstract.gens → NeededOver p App g →
      m ∈ σ.abstract.cond.atoms → NeededOver p App m
  | cleanerAtom {n : Node} {pc : Pc} {m : Mark} :
      m ∈ p.cleanerAtoms n pc → NeededOver p App m
  | passAtom {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      App n pc σ → σ.kind = .passThrough → m ∈ σ.abstract.cond.atoms →
      NeededOver p App m

/-- `Needed` is the relevance pass over the flow-insensitive applicability:
the parameterized definition specializes to the original one, so every result
about `NeededOver` applies to the default mode. -/
theorem needed_eq_neededOver {p : Program} {m : Mark} :
    Needed p m ↔ NeededOver p (Applicable p) m := by
  constructor
  · intro h
    induction h with
    | sinkAtom hA hk hm => exact .sinkAtom hA hk hm
    | sinkGen hA hk hm => exact .sinkGen hA hk hm
    | trans hA hg _ hm ih => exact .trans hA hg ih hm
    | cleanerAtom hm => exact .cleanerAtom hm
    | passAtom hA hk hm => exact .passAtom hA hk hm
  · intro h
    induction h with
    | sinkAtom hA hk hm => exact .sinkAtom hA hk hm
    | sinkGen hA hk hm => exact .sinkGen hA hk hm
    | trans hA hg _ hm ih => exact .trans hA hg ih hm
    | cleanerAtom hm => exact .cleanerAtom hm
    | passAtom hA hk hm => exact .passAtom hA hk hm

/-- Relevance is monotone in the applicability predicate: selecting fewer sites
never makes more marks needed. -/
theorem neededOver_mono {p : Program} {App App' : Node → Pc → ESite → Prop}
    (hsub : ∀ n pc σ, App n pc σ → App' n pc σ) {m : Mark} :
    NeededOver p App m → NeededOver p App' m := by
  intro h
  induction h with
  | sinkAtom hA hk hm => exact .sinkAtom (hsub _ _ _ hA) hk hm
  | sinkGen hA hk hm => exact .sinkGen (hsub _ _ _ hA) hk hm
  | trans hA hg _ hm ih => exact .trans (hsub _ _ _ hA) hg ih hm
  | cleanerAtom hm => exact .cleanerAtom hm
  | passAtom hA hk hm => exact .passAtom (hsub _ _ _ hA) hk hm

/-- Option 3* never needs a mark that the default mode does not need: its
relevance pass, computed over `ApplicableFS`, is contained in `Needed`. -/
theorem neededFS_implies_needed {p : Program} (hw : FSWF p) {m : Mark}
    (h : NeededOver p (ApplicableFS p) m) : Needed p m :=
  needed_eq_neededOver.2
    (neededOver_mono (fun _ _ _ hA => applicableFS_implies_applicable hw hA) h)

/-! ## 2. T-REL over an arbitrary applicability predicate -/

open SelectionLemmas

section TRelOver
variable {p : Program} {App : Node → Pc → ESite → Prop}
  {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
  (hApp : ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.cond → ECubeHolds p Sel.all n pc c →
    App n pc σ)
  (hAppB : ∀ n pc σ, App n pc σ → app n pc σ = true)
  (hNeed : ∀ m, NeededOver p App m → need m = true)
include hApp hAppB hNeed

/-- The invariant of T-REL over `App`. A baseline fact `g` whose mark is needed
over `App` is derived by the restricted scan either in the zero context, or in
the same context `d0 = some f0` whose entry mark is itself needed over `App`.
This is `rel_preserves_needed_strong` with the applicability predicate as a
parameter: the argument only uses that every site whose cube holds in the
baseline is `App`, and that `App` is closed under the rules of `NeededOver`. -/
theorem relOver_preserves_needed_strong {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : NeededOver p App g.mark) :
    PE p (Sel.ofScan app need) n none pc (some g) ∨
    (∃ f0, d0 = some f0 ∧ NeededOver p App f0.mark ∧
      PE p (Sel.ofScan app need) n d0 pc (some g)) := by
  suffices ∀ d, PE p Sel.all n d0 pc d → ∀ g, d = some g → NeededOver p App g.mark →
      PE p (Sel.ofScan app need) n none pc (some g) ∨
      (∃ f0, d0 = some f0 ∧ NeededOver p App f0.mark ∧
        PE p (Sel.ofScan app need) n d0 pc (some g))
    from this _ h g rfl hg
  clear h hg g
  intro d h
  induction h with
  | root _ => intro g e; cases e
  | intra _ hs hk ih =>
      intro g e hg; subst e
      rcases ih g rfl hg with h' | ⟨f0, e0, hf0, h'⟩
      · exact .inl (.intra h' hs hk)
      · exact .inr ⟨f0, e0, hf0, .intra h' hs hk⟩
  | callZero _ _ _ => intro g e; cases e
  | @callFact n c d0 pc f b _ hc hm hk ih =>
      intro g e hg; cases e
      have hd : ∃ d', PE p (Sel.ofScan app need) n d' pc (some f) := by
        rcases ih f rfl hg with h' | ⟨_, _, _, h'⟩
        · exact ⟨_, h'⟩
        · exact ⟨_, h'⟩
      obtain ⟨_, h'⟩ := hd
      exact .inr ⟨_, rfl, hg, .callFact h' hc hm hk⟩
  | retZero h0 hc _ hex hm hs _ ih2 =>
      intro g' e hg; cases e
      rcases ih2 _ rfl hg with h' | ⟨_, e0, _, _⟩
      · exact .inl (.retZero (pe_zero_reach h0) hc h' hex hm hs)
      · cases e0
  | @retFact n c d0 pc pc' ex f g bi b hf hc hmi hk _ hex hm hs ih1 ih2 =>
      intro g' e hg; cases e
      rcases ih2 _ rfl hg with h' | ⟨f0, e0, hf0, h'⟩
      · exact .inl (.retZero (pe_zero_reach hf) hc h' hex hm hs)
      · cases e0
        rcases ih1 _ rfl hf0 with h1 | ⟨f1, e1, hf1, h1⟩
        · exact .inl (.retFact h1 hc hmi hk h' hex hm hs)
        · exact .inr ⟨f1, e1, hf1, .retFact h1 hc hmi hk h' hex hm hs⟩
  | genEmpty hσ _ hc hpos ha _ h _ =>
      intro g e hg; cases e
      have hA := hApp _ _ _ _ hσ hc (.inl ⟨hpos, _, _, h⟩)
      have h' := PE.genEmpty (sel := Sel.ofScan app need) hσ
        (by simp [Sel.ofScan, hAppB _ _ _ hA]) hc hpos ha
        (by simp [Sel.ofScan, hAppB _ _ _ hA, hNeed _ hg]) (pe_zero_reach h)
      rw [genCtx_none] at h'
      exact .inl h'
  | @genSingle n d0 pc σ c f a hσ _ hc hpos ha _ h ih =>
      intro g e hg; cases e
      have hA := hApp _ _ _ _ hσ hc (.inr (.inl ⟨_, hpos, _, h⟩))
      have hf : NeededOver p App f.mark :=
        .trans hA (gen_of_assign ha) hg (atom_of_pos hc (by simp [hpos]))
      have hs : (Sel.ofScan app need).site n pc σ = true := by
        simp [Sel.ofScan, hAppB _ _ _ hA]
      have hact : (Sel.ofScan app need).act n pc σ a = true := by
        simp [Sel.ofScan, hAppB _ _ _ hA, hNeed _ hg]
      rcases ih f rfl hf with h' | ⟨f0, e0, hf0, h'⟩
      · have h'' := PE.genSingle hσ hs hc hpos ha hact h'
        rw [genCtx_none] at h''
        exact .inl h''
      · have h'' := PE.genSingle hσ hs hc hpos ha hact h'
        rcases genCtx_cases σ d0 with ek | ek <;> rw [ek] at h'' ⊢
        · exact .inl h''
        · exact .inr ⟨f0, e0, hf0, h''⟩
  | @genJoined n pc σ c a hσ _ hc hlen ha _ wn w hm h h0 ih _ =>
      intro g e hg; cases e
      have hA := hApp _ _ _ _ hσ hc
        (.inr (.inr ⟨hlen, fun f hf => ⟨wn f, w f, hm f hf, h f hf⟩⟩))
      have hex : ∀ f, f ∈ c.positive →
          ∃ d', PE p (Sel.ofScan app need) (wn f) d' pc (some f) := by
        intro f hf
        have hN : NeededOver p App f.mark :=
          .trans hA (gen_of_assign ha) hg (atom_of_pos hc hf)
        rcases ih f hf f rfl hN with h' | ⟨_, _, _, h'⟩
        · exact ⟨_, h'⟩
        · exact ⟨_, h'⟩
      obtain ⟨w', hw'⟩ := choose_ctx _ hex
      exact .inl (.genJoined hσ (by simp [Sel.ofScan, hAppB _ _ _ hA]) hc hlen ha
        (by simp [Sel.ofScan, hAppB _ _ _ hA, hNeed _ hg]) wn w' hm hw' (pe_zero_reach h0))
  | copy hσ hk hcp _ ih =>
      intro g e hg; cases e
      rcases ih _ rfl hg with h' | ⟨f0, e0, hf0, h'⟩
      · exact .inl (.copy hσ hk hcp h')
      · exact .inr ⟨f0, e0, hf0, .copy hσ hk hcp h'⟩

private theorem relOver_some_ctx {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : NeededOver p App g.mark) :
    ∃ d', PE p (Sel.ofScan app need) n d' pc (some g) := by
  rcases relOver_preserves_needed_strong hApp hAppB hNeed h hg with h' | ⟨_, _, _, h'⟩
  · exact ⟨_, h'⟩
  · exact ⟨_, h'⟩

/-- T-REL over `App`: when the installed selection enables every `App`-site and
every action whose mark is needed over `App`, and `App` covers every site whose
cube holds in the baseline, the restricted full scan reports exactly the
baseline findings. Any applicability predicate that is sound against the
engine may drive both site pruning and the relevance pass. -/
theorem relOver_fires_iff {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app need) n pc σ := by
  constructor
  · rintro ⟨hσ, hk, _, c, hc, hh⟩
    have hA := hApp _ _ _ _ hσ hc hh
    have hs : (Sel.ofScan app need).site n pc σ = true := by
      simp [Sel.ofScan, hAppB _ _ _ hA]
    refine ⟨hσ, hk, hs, c, hc, ?_⟩
    rcases hh with ⟨h0, d0, d, h⟩ | ⟨f, h1, d0, h⟩ | ⟨h2, h⟩
    · exact .inl ⟨h0, none, none, pe_zero_reach h⟩
    · have hN : NeededOver p App f.mark := .sinkAtom hA hk (atom_of_pos hc (by simp [h1]))
      obtain ⟨d', h'⟩ := relOver_some_ctx hApp hAppB hNeed h hN
      exact .inr (.inl ⟨f, h1, d', h'⟩)
    · refine .inr (.inr ⟨h2, fun f hf => ?_⟩)
      obtain ⟨n', d0, hm, h⟩ := h f hf
      obtain ⟨d', h'⟩ :=
        relOver_some_ctx hApp hAppB hNeed h (.sinkAtom hA hk (atom_of_pos hc hf))
      exact ⟨n', d', hm, h'⟩
  · exact fires_mono ofScan_le_all.1 ofScan_le_all.2

end TRelOver

/-- The original T-REL is the instance `App = Applicable p` of
`relOver_fires_iff`, through `needed_eq_neededOver`. -/
theorem rel_fires_iff_of_relOver {p : Program} {app : Node → Pc → ESite → Bool}
    {need : Mark → Bool}
    (hApp : ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.cond → ECubeHolds p Sel.all n pc c →
      Applicable p n pc σ)
    (hAppB : ∀ n pc σ, Applicable p n pc σ → app n pc σ = true)
    (hNeed : ∀ m, Needed p m → need m = true)
    {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app need) n pc σ :=
  relOver_fires_iff hApp hAppB (fun m h => hNeed m (needed_eq_neededOver.2 h))

/-! ## 3. Option 3*: engine cubes select their sites -/

open FlowSensitiveLemmas

/-- Every site, of any kind, whose cube holds in the engine model under any
selection is selected by option 3*. This generalizes `fs_fires_applicable`
from firing sinks to all sites (sources, transformers, pass-throughs), which
is what the site pruning and the relevance pass of 3* rely on. No
well-formedness hypothesis is needed. -/
theorem ecube_applicableFS {p : Program} {sel : Sel} {n : Node} {pc : Pc} {σ : ESite}
    {c : ECube} (hσ : σ ∈ p.sites n pc) (hc : c ∈ σ.cond)
    (hh : ECubeHolds p sel n pc c) : ApplicableFS p n pc σ := by
  refine ⟨hσ, _, abs_mem hc, ?_⟩
  rcases hh with ⟨hpos, d0, d, hpe⟩ | ⟨f, hpos, d0, hpe⟩ | ⟨hlen, hall⟩
  · obtain ⟨E, _, hr, _⟩ := pe_ptreach hpe
    exact Or.inl ⟨by rw [hpos]; simp, E, hr, by rw [hpos]; simp⟩
  · obtain ⟨⟨E, _, hr, hctx⟩, hsound⟩ := fs_sound hpe
    refine Or.inl ⟨by rw [hpos]; simp, E, hr, ?_⟩
    intro m hm
    rw [hpos] at hm
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
    subst hm
    exact hsound E (ptreach_root hr) hr hctx
  · refine Or.inr ⟨by simpa using hlen, ?_⟩
    intro m hm
    obtain ⟨f, hf, hfm⟩ := List.mem_map.mp hm
    subst hfm
    obtain ⟨n', d0, hmeth, hpe⟩ := hall f hf
    obtain ⟨⟨E, _, hr, hctx⟩, hsound⟩ := fs_sound hpe
    exact ⟨E, n', hr, hmeth, hsound E (ptreach_root hr) hr hctx⟩

/-! ## 4. Exactness of the 3* selection (O-FS-3) -/

/-- O-FS-3, relevance under option 3*: the selection that enables only
3*-applicable sites, and only actions whose mark is needed over
`ApplicableFS`, reports exactly the baseline findings. Both the site set and
the needed marks may be strictly smaller than in the default mode
(`fs_strict`, `neededFS_implies_needed`); no finding is lost. No
well-formedness hypothesis on the program is needed. -/
theorem markset_exact_fs {p : Program}
    {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (hAppB : ∀ n pc σ, ApplicableFS p n pc σ → app n pc σ = true)
    (hNeed : ∀ m, NeededOver p (ApplicableFS p) m → need m = true)
    {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app need) n pc σ :=
  relOver_fires_iff (fun _ _ _ _ hs hc hh => ecube_applicableFS hs hc hh) hAppB hNeed

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
