import MarkScan.Basic

/-!
# Selection exactness

The full scan runs the engine model (`PE`, `Fires`) under a rule selection
`Sel`. The baseline is `Sel.all`. The shallow scan installs
`Sel.ofScan app need`, where `app` over-approximates `Applicable` and `need`
over-approximates `Needed`. This module proves that the restricted full scan
reports exactly the baseline findings, and that the backward closure of
`Needed` over transformers is necessary for that.

Throughout, the fact that every site the engine fires is applicable is taken
as the hypothesis `hApp` (it is proved in another module).
-/

namespace MarkScan

/-! ## 1. Monotonicity in the selection -/

/-- Growing the selection (both the enabled sites and the enabled actions) can
only add path edges: a larger selection never loses a fact. -/
theorem pe_mono {p : Program} {sel sel' : Sel}
    (hs : ∀ n pc σ, sel.site n pc σ = true → sel'.site n pc σ = true)
    (ha : ∀ n pc σ a, sel.act n pc σ a = true → sel'.act n pc σ a = true)
    {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE p sel n d0 pc d → PE p sel' n d0 pc d := by
  intro h
  induction h with
  | root hr => exact .root hr
  | intra _ hs' hk ih => exact .intra ih hs' hk
  | callZero _ hc ih => exact .callZero ih hc
  | callFact _ hc hm hk ih => exact .callFact ih hc hm hk
  | retZero _ hc _ hex hm hs' ih1 ih2 => exact .retZero ih1 hc ih2 hex hm hs'
  | retFact _ hc hmi hk _ hex hm hs' ih1 ih2 => exact .retFact ih1 hc hmi hk ih2 hex hm hs'
  | genEmpty hσ hsel hc hpos ha' hact _ ih =>
      exact .genEmpty hσ (hs _ _ _ hsel) hc hpos ha' (ha _ _ _ _ hact) ih
  | genSingle hσ hsel hc hpos ha' hact _ ih =>
      exact .genSingle hσ (hs _ _ _ hsel) hc hpos ha' (ha _ _ _ _ hact) ih
  | genJoined hσ hsel hc hlen ha' hact wn w hm _ _ ih ih0 =>
      exact .genJoined hσ (hs _ _ _ hsel) hc hlen ha' (ha _ _ _ _ hact) wn w hm ih ih0
  | copy hσ hk hcp _ ih => exact .copy hσ hk hcp ih

namespace SelectionLemmas

theorem ecube_mono {p : Program} {sel sel' : Sel}
    (hs : ∀ n pc σ, sel.site n pc σ = true → sel'.site n pc σ = true)
    (ha : ∀ n pc σ a, sel.act n pc σ a = true → sel'.act n pc σ a = true)
    {n : Node} {pc : Pc} {c : ECube} :
    ECubeHolds p sel n pc c → ECubeHolds p sel' n pc c := by
  rintro (⟨h0, d0, d, h⟩ | ⟨f, h1, d0, h⟩ | ⟨h2, h⟩)
  · exact .inl ⟨h0, d0, d, pe_mono hs ha h⟩
  · exact .inr (.inl ⟨f, h1, d0, pe_mono hs ha h⟩)
  · exact .inr (.inr ⟨h2, fun f hf => (h f hf).elim fun n' ⟨d0, hm, h⟩ =>
      ⟨n', d0, hm, pe_mono hs ha h⟩⟩)

end SelectionLemmas

/-- Growing the selection can only add findings. -/
theorem fires_mono {p : Program} {sel sel' : Sel}
    (hs : ∀ n pc σ, sel.site n pc σ = true → sel'.site n pc σ = true)
    (ha : ∀ n pc σ a, sel.act n pc σ a = true → sel'.act n pc σ a = true)
    {n : Node} {pc : Pc} {σ : ESite} :
    Fires p sel n pc σ → Fires p sel' n pc σ := by
  rintro ⟨hσ, hk, hsel, c, hc, hh⟩
  exact ⟨hσ, hk, hs _ _ _ hsel, c, hc, SelectionLemmas.ecube_mono hs ha hh⟩

/-! ## 2. The zero fact -/

/-- The zero fact lives only in the zero context. -/
private theorem pe_zero_ctx {p : Program} {sel : Sel} {n : Node} {d0 : Ctx} {pc : Pc} :
    PE p sel n d0 pc none → d0 = none := by
  suffices ∀ d, PE p sel n d0 pc d → d = none → d0 = none from fun h => this _ h rfl
  intro d h
  induction h with
  | root _ => intro _; rfl
  | intra _ _ _ ih => exact ih
  | callZero _ _ _ => intro _; rfl
  | callFact _ _ _ _ _ => intro e; cases e
  | retZero _ _ _ _ _ _ _ _ => intro e; cases e
  | retFact _ _ _ _ _ _ _ _ _ _ => intro e; cases e
  | genEmpty _ _ _ _ _ _ _ _ => intro e; cases e
  | genSingle _ _ _ _ _ _ _ _ => intro e; cases e
  | genJoined => intro e; cases e
  | copy _ _ _ _ _ => intro e; cases e

/-- Zero-fact reachability does not depend on the selection: every statement
the engine visits under some selection, it visits (with the zero fact, in the
zero context) under every selection. Restricting rules never makes code
unreachable. -/
theorem pe_zero_reach {p : Program} {sel sel' : Sel}
    {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE p sel n d0 pc d → PE p sel' n none pc none := by
  intro h
  induction h with
  | root hr => exact .root hr
  | intra _ hs hk ih => exact .intra ih hs rfl
  | callZero _ hc ih => exact .callZero ih hc
  | callFact _ hc _ _ ih => exact .callZero ih hc
  | retZero _ _ _ _ _ hs ih1 _ => exact .intra ih1 hs rfl
  | retFact _ _ _ _ _ _ _ hs ih1 _ => exact .intra ih1 hs rfl
  | genEmpty _ _ _ _ _ _ _ ih => exact ih
  | genSingle _ _ _ _ _ _ _ ih => exact ih
  | genJoined _ _ _ _ _ _ _ _ _ _ _ _ ih0 => exact ih0
  | copy _ _ _ _ ih => exact ih

/-! ## 3. Helpers on abstract sites -/

namespace SelectionLemmas

theorem atom_of_pos {σ : ESite} {c : ECube} {f : Fact}
    (hc : c ∈ σ.cond) (hf : f ∈ c.positive) : f.mark ∈ σ.abstract.cond.atoms := by
  unfold Dnf.atoms ESite.abstract
  exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨c, hc, rfl⟩, List.mem_map.2 ⟨f, hf, rfl⟩⟩

theorem gen_of_assign {σ : ESite} {a : Fact} (ha : a ∈ σ.assigns) :
    a.mark ∈ σ.abstract.gens := by
  unfold ESite.abstract
  exact List.mem_map.2 ⟨a, ha, rfl⟩

/-- Finite choice of contexts: over a list, a pointwise existence gives one
function. Constructive because the list is finite and `Fact` has decidable
equality. -/
theorem choose_ctx {P : Fact → Ctx → Prop} :
    ∀ (l : List Fact), (∀ f, f ∈ l → ∃ d, P f d) → ∃ w : Fact → Ctx, ∀ f, f ∈ l → P f (w f)
  | [], _ => ⟨fun _ => none, fun _ hf => nomatch hf⟩
  | f :: l, h => by
    obtain ⟨w, hw⟩ := choose_ctx l (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨d, hd⟩ := h f List.mem_cons_self
    refine ⟨fun x => if x = f then d else w x, ?_⟩
    intro g hg
    cases decEq g f with
    | isTrue e => subst e; simpa using hd
    | isFalse e =>
      simp only [e, if_false]
      exact hw g ((List.mem_cons.1 hg).resolve_left e)

/-- A full-scan cube that holds makes its site applicable (via `hApp`); the
shallow scan then enables it. -/
theorem site_ofScan {p : Program} {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (hApp : ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.cond → ECubeHolds p Sel.all n pc c →
      Applicable p n pc σ)
    (hAppB : ∀ n pc σ, Applicable p n pc σ → app n pc σ = true)
    {n : Node} {pc : Pc} {σ : ESite} {c : ECube}
    (hσ : σ ∈ p.sites n pc) (hc : c ∈ σ.cond) (hh : ECubeHolds p Sel.all n pc c) :
    (Sel.ofScan app need).site n pc σ = true := by
  simp [Sel.ofScan, hAppB _ _ _ (hApp _ _ _ _ hσ hc hh)]

theorem genCtx_none (σ : ESite) : σ.genCtx none = none := by
  unfold ESite.genCtx; split <;> rfl

theorem genCtx_cases (σ : ESite) (d0 : Ctx) : σ.genCtx d0 = none ∨ σ.genCtx d0 = d0 := by
  unfold ESite.genCtx; split
  · exact .inl rfl
  · exact .inr rfl

theorem ofScan_le_all {app : Node → Pc → ESite → Bool} {need : Mark → Bool} :
    (∀ n pc σ, (Sel.ofScan app need).site n pc σ = true → Sel.all.site n pc σ = true) ∧
    (∀ n pc σ a, (Sel.ofScan app need).act n pc σ a = true → Sel.all.act n pc σ a = true) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

end SelectionLemmas

open SelectionLemmas

/-! ## 4. T-SEL: restricting to applicable sites is exact -/

section TSel
variable {p : Program} {app : Node → Pc → ESite → Bool}
  (hApp : ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.cond → ECubeHolds p Sel.all n pc c →
    Applicable p n pc σ)
  (hAppB : ∀ n pc σ, Applicable p n pc σ → app n pc σ = true)
include hApp hAppB

/-- T-SEL for facts: disabling every site the shallow scan proves inapplicable
(keeping all actions of the selected ones) changes no path edge. -/
theorem sel_pe_iff {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE p Sel.all n d0 pc d ↔ PE p (Sel.ofScan app (fun _ => true)) n d0 pc d := by
  constructor
  · intro h
    induction h with
    | root hr => exact .root hr
    | intra _ hs hk ih => exact .intra ih hs hk
    | callZero _ hc ih => exact .callZero ih hc
    | callFact _ hc hm hk ih => exact .callFact ih hc hm hk
    | retZero _ hc _ hex hm hs ih1 ih2 => exact .retZero ih1 hc ih2 hex hm hs
    | retFact _ hc hmi hk _ hex hm hs ih1 ih2 => exact .retFact ih1 hc hmi hk ih2 hex hm hs
    | genEmpty hσ _ hc hpos ha _ h ih =>
        have hA := hApp _ _ _ _ hσ hc (.inl ⟨hpos, _, _, h⟩)
        exact .genEmpty hσ (by simp [Sel.ofScan, hAppB _ _ _ hA]) hc hpos ha
          (by simp [Sel.ofScan, hAppB _ _ _ hA]) ih
    | genSingle hσ _ hc hpos ha _ h ih =>
        have hA := hApp _ _ _ _ hσ hc (.inr (.inl ⟨_, hpos, _, h⟩))
        exact .genSingle hσ (by simp [Sel.ofScan, hAppB _ _ _ hA]) hc hpos ha
          (by simp [Sel.ofScan, hAppB _ _ _ hA]) ih
    | genJoined hσ _ hc hlen ha _ wn w hm h _ ih ih0 =>
        have hA := hApp _ _ _ _ hσ hc
          (.inr (.inr ⟨hlen, fun f hf => ⟨wn f, w f, hm f hf, h f hf⟩⟩))
        exact .genJoined hσ (by simp [Sel.ofScan, hAppB _ _ _ hA]) hc hlen ha
          (by simp [Sel.ofScan, hAppB _ _ _ hA]) wn w hm ih ih0
    | copy hσ hk hcp _ ih => exact .copy hσ hk hcp ih
  · exact pe_mono ofScan_le_all.1 ofScan_le_all.2

/-- T-SEL for findings: the selection by applicability reports exactly the
baseline findings. -/
theorem sel_fires_iff {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app (fun _ => true)) n pc σ := by
  constructor
  · rintro ⟨hσ, hk, _, c, hc, hh⟩
    refine ⟨hσ, hk, site_ofScan hApp hAppB hσ hc hh, c, hc, ?_⟩
    rcases hh with ⟨h0, d0, d, h⟩ | ⟨f, h1, d0, h⟩ | ⟨h2, h⟩
    · exact .inl ⟨h0, d0, d, (sel_pe_iff hApp hAppB).1 h⟩
    · exact .inr (.inl ⟨f, h1, d0, (sel_pe_iff hApp hAppB).1 h⟩)
    · exact .inr (.inr ⟨h2, fun f hf => (h f hf).elim fun n' ⟨d0, hm, h⟩ =>
        ⟨n', d0, hm, (sel_pe_iff hApp hAppB).1 h⟩⟩)
  · exact fires_mono ofScan_le_all.1 ofScan_le_all.2

end TSel

/-! ## 5. T-REL: restricting `AssignMark` actions to needed marks is exact -/

section TRel
variable {p : Program} {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
  (hApp : ∀ n pc σ c, σ ∈ p.sites n pc → c ∈ σ.cond → ECubeHolds p Sel.all n pc c →
    Applicable p n pc σ)
  (hAppB : ∀ n pc σ, Applicable p n pc σ → app n pc σ = true)
  (hNeed : ∀ m, Needed p m → need m = true)
include hApp hAppB hNeed

/-- The invariant of T-REL. A needed fact `g` derived by the baseline in
context `d0` is derived by the relevance-restricted scan either in the zero
context, or in the same context `d0 = some f0` whose entry mark is itself
needed. The second case is what `retFact` needs: when the callee context's
mark is not needed, the callee result was produced without that context and is
therefore reproducible in the zero context. Sink gens land in the zero context
in both runs (`ESite.genCtx`), so they fall under the first case. -/
theorem rel_preserves_needed_strong {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : Needed p g.mark) :
    PE p (Sel.ofScan app need) n none pc (some g) ∨
    (∃ f0, d0 = some f0 ∧ Needed p f0.mark ∧ PE p (Sel.ofScan app need) n d0 pc (some g)) := by
  suffices ∀ d, PE p Sel.all n d0 pc d → ∀ g, d = some g → Needed p g.mark →
      PE p (Sel.ofScan app need) n none pc (some g) ∨
      (∃ f0, d0 = some f0 ∧ Needed p f0.mark ∧ PE p (Sel.ofScan app need) n d0 pc (some g))
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
      have hf : Needed p f.mark :=
        .trans hA (gen_of_assign ha) hg (atom_of_pos hc (by simp [hpos]))
      have hs : (Sel.ofScan app need).site n pc σ = true := by
        simp [Sel.ofScan, hAppB _ _ _ hA]
      have hact : (Sel.ofScan app need).act n pc σ a = true := by
        simp [Sel.ofScan, hAppB _ _ _ hA, hNeed _ hg]
      rcases ih f rfl hf with h' | ⟨f0, e0, hf0, h'⟩
      · have h'' := PE.genSingle hσ hs hc hpos ha hact h'
        rw [genCtx_none] at h''
        exact .inl h''
      · -- A sink's gen lands in the zero context; any other gen keeps `d0`.
        have h'' := PE.genSingle hσ hs hc hpos ha hact h'
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
        have hN : Needed p f.mark := .trans hA (gen_of_assign ha) hg (atom_of_pos hc hf)
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

/-- T-REL (a): every baseline fact with a needed mark is still derived by the
relevance-restricted scan, in the zero context or in its own context. -/
theorem rel_preserves_needed {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : Needed p g.mark) :
    PE p (Sel.ofScan app need) n none pc (some g) ∨
    PE p (Sel.ofScan app need) n d0 pc (some g) := by
  rcases rel_preserves_needed_strong hApp hAppB hNeed h hg with h' | ⟨_, _, _, h'⟩
  · exact .inl h'
  · exact .inr h'

private theorem rel_some_ctx {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : Needed p g.mark) :
    ∃ d', PE p (Sel.ofScan app need) n d' pc (some g) := by
  rcases rel_preserves_needed hApp hAppB hNeed h hg with h' | h'
  · exact ⟨_, h'⟩
  · exact ⟨_, h'⟩

/-- T-REL (b): the shallow scan's selection (applicable sites, needed actions)
reports exactly the baseline findings. -/
theorem rel_fires_iff {n : Node} {pc : Pc} {σ : ESite} :
    Fires p Sel.all n pc σ ↔ Fires p (Sel.ofScan app need) n pc σ := by
  constructor
  · rintro ⟨hσ, hk, _, c, hc, hh⟩
    have hA := hApp _ _ _ _ hσ hc hh
    refine ⟨hσ, hk, site_ofScan hApp hAppB hσ hc hh, c, hc, ?_⟩
    rcases hh with ⟨h0, d0, d, h⟩ | ⟨f, h1, d0, h⟩ | ⟨h2, h⟩
    · exact .inl ⟨h0, none, none, pe_zero_reach h⟩
    · have hN : Needed p f.mark := .sinkAtom hA hk (atom_of_pos hc (by simp [h1]))
      obtain ⟨d', h'⟩ := rel_some_ctx hApp hAppB hNeed h hN
      exact .inr (.inl ⟨f, h1, d', h'⟩)
    · refine .inr (.inr ⟨h2, fun f hf => ?_⟩)
      obtain ⟨n', d0, hm, h⟩ := h f hf
      obtain ⟨d', h'⟩ := rel_some_ctx hApp hAppB hNeed h (.sinkAtom hA hk (atom_of_pos hc hf))
      exact ⟨n', d', hm, h'⟩
  · exact fires_mono ofScan_le_all.1 ofScan_le_all.2

/-- T-REL, zero context: a needed fact that the baseline derives in the zero
context is derived by the restricted scan in the zero context too. -/
theorem rel_preserves_needed_zero {n : Node} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n none pc (some g)) (hg : Needed p g.mark) :
    PE p (Sel.ofScan app need) n none pc (some g) := by
  rcases rel_preserves_needed_strong hApp hAppB hNeed h hg with h' | ⟨_, e, _, _⟩
  · exact h'
  · cases e

/-- T-REL, unneeded context: a needed fact that the baseline derives in a
context whose entry mark is not needed is derived by the restricted scan in
the zero context. -/
theorem rel_unneeded_ctx_zero {n : Node} {pc : Pc} {f0 g : Fact}
    (h : PE p Sel.all n (some f0) pc (some g)) (hg : Needed p g.mark)
    (hf0 : ¬ Needed p f0.mark) :
    PE p (Sel.ofScan app need) n none pc (some g) := by
  rcases rel_preserves_needed_strong hApp hAppB hNeed h hg with h' | ⟨_, e, hf, _⟩
  · exact h'
  · cases e; exact absurd hf hf0

/-- T-REL, context form (the reviewer's wording). For an entry context that is
the zero context or has a needed mark, the restricted scan derives the needed
fact in that same context or in the zero context. The hypothesis `_hd0` is not
used: the disjunction holds for every context. The stronger claim without the
zero-context disjunct is false for `d0 = some f0`; see
`rel_ctx_not_preserved`. -/
theorem rel_preserves_needed_ctx {n : Node} {d0 : Ctx} {pc : Pc} {g : Fact}
    (h : PE p Sel.all n d0 pc (some g)) (hg : Needed p g.mark)
    (_hd0 : d0 = none ∨ ∃ f0, d0 = some f0 ∧ Needed p f0.mark) :
    PE p (Sel.ofScan app need) n d0 pc (some g) ∨
    PE p (Sel.ofScan app need) n none pc (some g) := by
  rcases rel_preserves_needed hApp hAppB hNeed h hg with h' | h'
  · exact .inr h'
  · exact .inl h'

end TRel

/-- T-REL (c): the restricted scan derives nothing the baseline does not; it
is sound with respect to the baseline. -/
theorem rel_sound_subset {p : Program} {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE p (Sel.ofScan app need) n d0 pc d → PE p Sel.all n d0 pc d :=
  pe_mono ofScan_le_all.1 ofScan_le_all.2

/-! ## 6. Necessity of the backward closure over transformers -/

/-- A relevance pass *without* backward closure: a mark is kept only if it
appears in a sink's condition or `trackFactsReachAnalysisEnd` marks. -/
def needSinkOnly (p : Program) (m : Mark) : Bool :=
  p.nodes.any fun n => (p.nodeSites n).any fun ps =>
    ps.2.kind == .sink && (ps.2.abstract.cond.atoms.contains m || ps.2.abstract.gens.contains m)

namespace SelectionLemmas

/-- The source: unconditionally assigns mark 1. -/
def cexSrc : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }
/-- The transformer: assigns mark 2 when mark 1 is present. -/
def cexTr : ESite :=
  { rule := 1, kind := .source, cond := [[⟨⟨0, 1⟩, false⟩]], assigns := [⟨0, 2⟩], copies := [] }
/-- The sink: fires on mark 2. -/
def cexSink : ESite :=
  { rule := 2, kind := .sink, cond := [[⟨⟨0, 2⟩, false⟩]], assigns := [], copies := [] }

/-- One node, one statement, the three sites above, no calls. -/
def cex : Program where
  nodes := [0]
  roots := [0]
  pcs := fun _ => [0]
  succ := fun _ _ => []
  exits := fun _ => [0]
  sites := fun _ _ => [cexSrc, cexTr, cexSink]
  calls := fun _ _ => []
  mapIn := fun _ _ _ => none
  mapOut := fun _ _ _ => none
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

theorem cex_pos_tr : ECube.positive [⟨⟨0, 1⟩, false⟩] = [⟨0, 1⟩] := by decide
theorem cex_pos_sink : ECube.positive [⟨⟨0, 2⟩, false⟩] = [⟨0, 2⟩] := by decide

/-- Under any selection whose `need` drops mark 1, no fact at all is derived
in `cex`: the source's action is disabled, and every other rule needs a fact. -/
theorem cex_no_fact {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (h1 : need 1 = false) {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE cex (Sel.ofScan app need) n d0 pc d → d = none := by
  intro h
  induction h with
  | root _ => rfl
  | intra _ _ _ ih => exact ih
  | callZero _ _ _ => rfl
  | callFact _ hc _ _ _ => exact absurd hc (by simp [cex])
  | retZero _ hc _ _ _ _ _ _ => exact absurd hc (by simp [cex])
  | retFact _ hc _ _ _ _ _ _ _ _ => exact absurd hc (by simp [cex])
  | genEmpty hσ _ hc hpos ha hact _ _ =>
      simp only [cex, List.mem_cons, List.not_mem_nil, or_false] at hσ
      rcases hσ with rfl | rfl | rfl
      · simp only [cexSrc, List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        simp [Sel.ofScan, h1] at hact
      · simp only [cexTr, List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        rw [cex_pos_tr] at hpos
        cases hpos
      · simp [cexSink] at ha
  | genSingle _ _ _ _ _ _ _ ih => cases ih
  | genJoined _ _ _ hlen _ _ _ _ _ _ _ ih _ =>
      cases hp : ECube.positive _ with
      | nil => rw [hp] at hlen; cases hlen
      | cons f _ => cases ih f (by rw [hp]; exact List.mem_cons_self)
  | copy _ _ _ _ ih => cases ih

theorem cex_src_mem : (0, cexSrc) ∈ cex.nodeSites 0 := by simp [Program.nodeSites, cex]
theorem cex_tr_mem : (0, cexTr) ∈ cex.nodeSites 0 := by simp [Program.nodeSites, cex]
theorem cex_sink_mem : (0, cexSink) ∈ cex.nodeSites 0 := by simp [Program.nodeSites, cex]

theorem cex_abs_src_cond : cexSrc.abstract.cond = [[]] := by decide
theorem cex_abs_src_gens : cexSrc.abstract.gens = [1] := by decide
theorem cex_abs_tr_cond : cexTr.abstract.cond = [[1]] := by decide
theorem cex_abs_tr_gens : cexTr.abstract.gens = [2] := by decide
theorem cex_abs_sink_cond : cexSink.abstract.cond = [[2]] := by decide

theorem cex_InS1 : InS cex 0 1 :=
  .single (n := 0) (pc := 0) (σ := cexSrc) (c := []) (by simp [cex]) (.refl 0) cex_src_mem
    (by rw [cex_abs_src_cond]; simp) (by decide) (by simp) (by rw [cex_abs_src_gens]; simp)

theorem cex_InS2 : InS cex 0 2 :=
  .single (n := 0) (pc := 0) (σ := cexTr) (c := [1]) (by simp [cex]) (.refl 0) cex_tr_mem
    (by rw [cex_abs_tr_cond]; simp) (by decide) (by simp [cex_InS1])
    (by rw [cex_abs_tr_gens]; simp)

theorem cex_app_tr : Applicable cex 0 0 cexTr :=
  ⟨by simp [cex], [1], by rw [cex_abs_tr_cond]; simp,
    .inl ⟨by decide, 0, by simp [cex], .refl 0, by simp [cex_InS1]⟩⟩

theorem cex_app_sink : Applicable cex 0 0 cexSink :=
  ⟨by simp [cex], [2], by rw [cex_abs_sink_cond]; simp,
    .inl ⟨by decide, 0, by simp [cex], .refl 0, by simp [cex_InS2]⟩⟩

end SelectionLemmas

open SelectionLemmas in
/-- In `cex`, the true relevance pass keeps mark 1 (it is needed through the
transformer), but the sink-only pass drops it and keeps exactly mark 2. So
`needSinkOnly` violates the hypothesis `hNeed` of T-REL. -/
theorem cex_needed_one : Needed cex 1 ∧ needSinkOnly cex 1 = false ∧
    ∀ m, needSinkOnly cex m = (m == 2) := by
  refine ⟨.trans (g := 2) cex_app_tr (by rw [cex_abs_tr_gens]; simp)
      (.sinkAtom cex_app_sink rfl (by rw [cex_abs_sink_cond]; decide))
      (by rw [cex_abs_tr_cond]; decide), by decide, ?_⟩
  intro m
  have e1 : (Kind.source == Kind.sink) = false := by decide
  simp [needSinkOnly, Program.nodeSites, cex, cexSrc, cexTr, cexSink, ESite.abstract, Dnf.atoms,
    cex_pos_sink, e1]
  cases h : m == 2 <;> simp_all

namespace SelectionLemmas

/-- No selection that drops mark 1 reports any finding in `cex`. -/
theorem cex_no_fires {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (h1 : need 1 = false) (n : Node) (pc : Pc) (σ : ESite) :
    ¬ Fires cex (Sel.ofScan app need) n pc σ := by
  rintro ⟨hσ, hk, _, c, hc, hh⟩
  simp only [cex, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl
  · cases hk
  · cases hk
  simp only [cexSink, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  rcases hh with ⟨hp, _⟩ | ⟨f, _, _, h⟩ | ⟨hlen, _⟩
  · rw [cex_pos_sink] at hp; cases hp
  · cases cex_no_fact h1 h
  · rw [cex_pos_sink] at hlen; simp at hlen

theorem cex_baseline_fires : Fires cex Sel.all 0 0 cexSink := by
  have h0 : PE cex Sel.all 0 none 0 none := .root (by simp [cex])
  have h1 : PE cex Sel.all 0 none 0 (some ⟨0, 1⟩) :=
    .genEmpty (σ := cexSrc) (c := []) (by simp [cex]) rfl (by simp [cexSrc]) (by decide)
      (by simp [cexSrc]) rfl h0
  have h2 : PE cex Sel.all 0 none 0 (some ⟨0, 2⟩) :=
    .genSingle (σ := cexTr) (by simp [cex]) rfl (by simp [cexTr]) cex_pos_tr
      (by simp [cexTr]) rfl h1
  exact ⟨by simp [cex], rfl, rfl, _, List.mem_singleton_self _,
    .inr (.inl ⟨_, cex_pos_sink, none, h2⟩)⟩

end SelectionLemmas

open SelectionLemmas in
/-- Necessity of the backward closure: in `cex` the baseline reports the sink,
but the selection that keeps only the sink's own mark 2 (dropping the
transformer's input mark 1) reports nothing, although it enables every site.
Keeping only marks named by sinks is unsound; `Needed` must close backward
over transformers (automaton edges). -/
theorem backward_closure_necessary :
    Fires cex Sel.all 0 0 cexSink ∧
    ∀ n pc σ, ¬ Fires cex (Sel.ofScan (fun _ _ _ => true) (fun m => m == 2)) n pc σ :=
  ⟨cex_baseline_fires, cex_no_fires rfl⟩

open SelectionLemmas in
/-- The same failure stated with `needSinkOnly` itself: installing the
sink-only relevance pass loses the finding in `cex`. -/
theorem needSinkOnly_unsound :
    Fires cex Sel.all 0 0 cexSink ∧
    ∀ n pc σ, ¬ Fires cex (Sel.ofScan (fun _ _ _ => true) (needSinkOnly cex)) n pc σ :=
  ⟨cex_baseline_fires, cex_no_fires (by decide)⟩

/-! ## 7. The restricted scan does not preserve contexts

`rel_preserves_needed_ctx` keeps a zero-context disjunct, and it cannot be
dropped. In `cexCtx`, root 0 generates mark 1 and calls node 1, which is
entered in context `some ⟨0, 1⟩`. At statement 0 of node 1, a cleaner on mark 1
kills the entry fact, and an unconditional source generates mark 3, which
nothing needs. At statement 1, an unconditional source generates mark 2, and
a sink fires on mark 2. The baseline derives mark 2 in context `some ⟨0, 1⟩`,
because the fact with mark 3 keeps that context alive at statement 1. The
restricted scan disables the mark-3 action, so that context is empty at
statement 1 and mark 2 is derived only in the zero context. The finding is the
same in both runs. -/

namespace SelectionLemmas

def cxSrcA : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }
def cxSrcX : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨0, 3⟩], copies := [] }
def cxSrcG : ESite :=
  { rule := 2, kind := .source, cond := [[]], assigns := [⟨0, 2⟩], copies := [] }
def cxSink : ESite :=
  { rule := 3, kind := .sink, cond := [[⟨⟨0, 2⟩, false⟩]], assigns := [], copies := [] }

/-- Root 0 calls node 1 at statement 0. The cleaner at `(1, 0)` kills mark 1
and records the cleaner atom 1. -/
def cexCtx : Program where
  nodes := [0, 1]
  roots := [0]
  pcs := fun n => if n = 1 then [0, 1] else [0]
  succ := fun n pc => if n = 1 ∧ pc = 0 then [1] else []
  exits := fun n => if n = 1 then [1] else [0]
  sites := fun n pc =>
    if n = 0 ∧ pc = 0 then [cxSrcA]
    else if n = 1 ∧ pc = 0 then [cxSrcX]
    else if n = 1 ∧ pc = 1 then [cxSrcG, cxSink]
    else []
  calls := fun n pc => if n = 0 ∧ pc = 0 then [1] else []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ _ => none
  kills := fun n pc f => n == 1 && pc == 0 && f.mark == 1
  method := id
  cleanerAtoms := fun n pc => if n = 1 ∧ pc = 0 then [1] else []

/-- The relevance pass of `cexCtx`: exactly the marks 1 and 2. -/
def cxNeed (m : Mark) : Bool := m == 1 || m == 2

theorem genCtx_some {σ : ESite} {d0 : Ctx} {f : Fact} (h : σ.genCtx d0 = some f) :
    d0 = some f := by
  rcases genCtx_cases σ d0 with e | e <;> rw [e] at h
  · cases h
  · exact h

theorem cx_sites {n : Node} {pc : Pc} {σ : ESite} (h : σ ∈ cexCtx.sites n pc) :
    (n = 0 ∧ pc = 0 ∧ σ = cxSrcA) ∨ (n = 1 ∧ pc = 0 ∧ σ = cxSrcX) ∨
    (n = 1 ∧ pc = 1 ∧ (σ = cxSrcG ∨ σ = cxSink)) := by
  simp only [cexCtx] at h
  split at h
  · rename_i hh; simp at h; exact .inl ⟨hh.1, hh.2, h⟩
  · split at h
    · rename_i _ hh; simp at h; exact .inr (.inl ⟨hh.1, hh.2, h⟩)
    · split at h
      · rename_i _ _ hh; simp at h; exact .inr (.inr ⟨hh.1, hh.2, h⟩)
      · simp at h

theorem cx_atoms {n : Node} {pc : Pc} {σ : ESite} {m : Mark}
    (h : σ ∈ cexCtx.sites n pc) (hm : m ∈ σ.abstract.cond.atoms) : m = 2 := by
  have eA : cxSrcA.abstract.cond.atoms = [] := by decide
  have eX : cxSrcX.abstract.cond.atoms = [] := by decide
  have eG : cxSrcG.abstract.cond.atoms = [] := by decide
  have eS : cxSink.abstract.cond.atoms = [2] := by decide
  rcases cx_sites h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl | rfl⟩
  · rw [eA] at hm; cases hm
  · rw [eX] at hm; cases hm
  · rw [eG] at hm; cases hm
  · rw [eS] at hm; simpa using hm

theorem cx_not_pass {n : Node} {pc : Pc} {σ : ESite}
    (h : σ ∈ cexCtx.sites n pc) : σ.kind ≠ .passThrough := by
  rcases cx_sites h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl | rfl⟩ <;> intro e <;> cases e

theorem cx_needed {m : Mark} (h : Needed cexCtx m) : m = 1 ∨ m = 2 := by
  cases h with
  | sinkAtom hA _ hm => exact .inr (cx_atoms hA.1 hm)
  | sinkGen hA hk hm =>
      have eS : cxSink.abstract.gens = [] := by decide
      rcases cx_sites hA.1 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl | rfl⟩
      · cases hk
      · cases hk
      · cases hk
      · rw [eS] at hm; cases hm
  | trans hA _ _ hm => exact .inr (cx_atoms hA.1 hm)
  | cleanerAtom hm =>
      simp only [cexCtx] at hm
      split at hm
      · simp at hm; exact .inl hm
      · cases hm
  | passAtom hA hk _ => exact absurd hk (cx_not_pass hA.1)

theorem cx_reach1 : Reaches cexCtx 0 1 :=
  .step (b := 1) (by simp [Program.callees, cexCtx]) (.refl 1)

theorem cx_InS2 : InS cexCtx 0 2 :=
  .single (n := 1) (pc := 1) (σ := cxSrcG) (c := []) (by simp [cexCtx]) cx_reach1
    (by simp [Program.nodeSites, cexCtx]) (by decide) (by decide) (by simp)
    (by decide)

theorem cx_app {n : Node} {pc : Pc} {σ : ESite} (h : σ ∈ cexCtx.sites n pc) :
    Applicable cexCtx n pc σ := by
  refine ⟨h, ?_⟩
  have hsrc : ∀ τ : ESite, τ.abstract.cond = [[]] → (n = 0 ∨ n = 1) →
      ∃ c, c ∈ τ.abstract.cond ∧ CubeSat cexCtx n c := by
    intro τ e hn
    refine ⟨[], by rw [e]; simp, .inl ⟨by decide, 0, by simp [cexCtx], ?_, by simp⟩⟩
    rcases hn with rfl | rfl
    · exact .refl 0
    · exact cx_reach1
  rcases cx_sites h with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl | rfl⟩
  · exact hsrc _ (by decide) (.inl rfl)
  · exact hsrc _ (by decide) (.inr rfl)
  · exact hsrc _ (by decide) (.inr rfl)
  · have e : cxSink.abstract.cond = [[2]] := by decide
    exact ⟨[2], by rw [e]; simp,
      .inl ⟨by decide, 0, by simp [cexCtx], cx_reach1, by simp [cx_InS2]⟩⟩

/-- In the restricted run of `cexCtx`, the only fact of node 1 in context
`some ⟨0, 1⟩` is the entry fact at statement 0. -/
theorem cx_rel_inv {app : Node → Pc → ESite → Bool} {need : Mark → Bool}
    (h3 : need 3 = false) {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact} :
    PE cexCtx (Sel.ofScan app need) n d0 pc d →
    n = 1 → d0 = some ⟨0, 1⟩ → pc = 0 ∧ d = some ⟨0, 1⟩ := by
  intro h
  induction h with
  | root hr => intro hn; subst hn; simp [cexCtx] at hr
  | intra _ _ hk ih =>
      intro hn hd
      obtain ⟨rfl, rfl⟩ := ih hn hd
      subst hn
      exact absurd hk (by decide)
  | callZero _ _ _ => intro _ hd; cases hd
  | callFact _ _ _ _ _ => intro _ hd; exact ⟨rfl, hd⟩
  | retZero _ hc _ _ _ _ _ _ => intro hn; subst hn; simp [cexCtx] at hc
  | retFact _ hc _ _ _ _ _ _ _ _ => intro hn; subst hn; simp [cexCtx] at hc
  | genEmpty hσ _ _ _ ha hact _ ih =>
      intro hn hd
      obtain ⟨rfl, _⟩ := ih hn (genCtx_some hd)
      subst hn
      rcases cx_sites hσ with ⟨e, _, _⟩ | ⟨_, _, rfl⟩ | ⟨_, e, _⟩
      · cases e
      · simp only [cxSrcX, List.mem_singleton] at ha
        subst ha
        simp [Sel.ofScan, h3] at hact
      · cases e
  | genSingle hσ _ hc hpos _ _ _ ih =>
      intro hn hd
      obtain ⟨rfl, _⟩ := ih hn (genCtx_some hd)
      subst hn
      rcases cx_sites hσ with ⟨e, _, _⟩ | ⟨_, _, rfl⟩ | ⟨_, e, _⟩
      · cases e
      · simp only [cxSrcX, List.mem_singleton] at hc
        subst hc
        cases hpos
      · cases e
  | genJoined => intro _ hd; cases hd
  | copy hσ hk _ _ _ => intro _ _; exact absurd hk (cx_not_pass hσ)

end SelectionLemmas

open SelectionLemmas in
/-- The restricted scan does not preserve contexts. `cexCtx` satisfies the
hypotheses of T-REL (every site is applicable, and `cxNeed` holds for every
needed mark). Marks 1 and 2 are needed. The baseline derives mark 2 at
`(1, 1)` in the context `some ⟨0, 1⟩`, whose entry mark is needed; the
restricted scan does not derive it there, and derives it only in the zero
context. -/
theorem rel_ctx_not_preserved :
    (∀ n pc σ c, σ ∈ cexCtx.sites n pc → c ∈ σ.cond → ECubeHolds cexCtx Sel.all n pc c →
      Applicable cexCtx n pc σ) ∧
    (∀ n pc σ, Applicable cexCtx n pc σ → (fun _ _ _ => true : Node → Pc → ESite → Bool) n pc σ = true) ∧
    (∀ m, Needed cexCtx m → cxNeed m = true) ∧
    Needed cexCtx 1 ∧ Needed cexCtx 2 ∧
    PE cexCtx Sel.all 1 (some ⟨0, 1⟩) 1 (some ⟨0, 2⟩) ∧
    ¬ PE cexCtx (Sel.ofScan (fun _ _ _ => true) cxNeed) 1 (some ⟨0, 1⟩) 1 (some ⟨0, 2⟩) ∧
    PE cexCtx (Sel.ofScan (fun _ _ _ => true) cxNeed) 1 none 1 (some ⟨0, 2⟩) := by
  refine ⟨fun _ _ _ _ h _ _ => cx_app h, fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    rcases cx_needed hm with rfl | rfl <;> rfl
  · exact .cleanerAtom (n := 1) (pc := 0) (by simp [cexCtx])
  · have hs : cxSink ∈ cexCtx.sites 1 1 := by simp [cexCtx]
    have e : cxSink.abstract.cond.atoms = [2] := by decide
    exact .sinkAtom (cx_app hs) rfl (by rw [e]; simp)
  · have h0 : PE cexCtx Sel.all 0 none 0 none := .root (by simp [cexCtx])
    have h1 : PE cexCtx Sel.all 0 none 0 (some ⟨0, 1⟩) :=
      .genEmpty (σ := cxSrcA) (c := []) (by simp [cexCtx]) rfl (by simp [cxSrcA]) (by decide)
        (by simp [cxSrcA]) rfl h0
    have h2 : PE cexCtx Sel.all 1 (some ⟨0, 1⟩) 0 (some ⟨0, 1⟩) :=
      .callFact (b := 0) h1 (by simp [cexCtx]) rfl rfl
    have h3 : PE cexCtx Sel.all 1 (some ⟨0, 1⟩) 0 (some ⟨0, 3⟩) :=
      .genEmpty (σ := cxSrcX) (c := []) (by simp [cexCtx]) rfl (by simp [cxSrcX]) (by decide)
        (by simp [cxSrcX]) rfl h2
    have h4 : PE cexCtx Sel.all 1 (some ⟨0, 1⟩) 1 (some ⟨0, 3⟩) :=
      .intra h3 (by simp [cexCtx]) rfl
    exact .genEmpty (σ := cxSrcG) (c := []) (by simp [cexCtx]) rfl (by simp [cxSrcG])
      (by decide) (by simp [cxSrcG]) rfl h4
  · intro h
    obtain ⟨e, _⟩ := cx_rel_inv (by rfl) h rfl rfl
    cases e
  · have r0 : PE cexCtx (Sel.ofScan (fun _ _ _ => true) cxNeed) 0 none 0 none :=
      .root (by simp [cexCtx])
    have r1 : PE cexCtx (Sel.ofScan (fun _ _ _ => true) cxNeed) 1 none 0 none :=
      .callZero r0 (by simp [cexCtx])
    have r2 : PE cexCtx (Sel.ofScan (fun _ _ _ => true) cxNeed) 1 none 1 none :=
      .intra r1 (by simp [cexCtx]) rfl
    exact .genEmpty (σ := cxSrcG) (c := []) (by simp [cexCtx]) rfl
      (by simp [cxSrcG]) (by decide) (by simp [cxSrcG]) rfl r2

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
