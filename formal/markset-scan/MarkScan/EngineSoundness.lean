import MarkScan.Basic

/-!
# Soundness of the shallow scan against the engine model

The mark-set semantics `InS` (with the D1 correction) over-approximates the
engine model `PE`: every mark the engine can carry in a context that some root
reaches is in that root's `S_E`, and every rule instance the engine can fire
or use to generate a fact is `Applicable`. This holds for *any* selection.

Two engine behaviours shape `InS`:
* a joined cube may take its facts from any context of any node of the same
  method at the statement, and its gens are zero-context facts;
* a sink's `trackFactsReachAnalysisEnd` gens are zero-context facts too.
Zero-context facts return to every caller, so both kinds of gens go to every
root that reaches the site's node (`InS.joined`, `InS.sinkGen`).

We also show:
* the well-formedness hypothesis `PcWF` is necessary (without it the engine
  may use a call edge at a statement the scan never looks at);
* the per-root collapse without the D1 correction (`InSNoJoin`) is unsound;
* dropping `InS.sinkGen` is unsound (`sinkgen_zero_ctx_needed`);
* the scan is incomplete: `Applicable` may hold for a sink that never fires.
-/

namespace MarkScan

/-! ## Well-formedness and contexts -/

/-- Statements that carry a call or a rule site are listed in `pcs`. The scan
enumerates only `pcs n` (through `callees` and `nodeSites`), while the engine
may reach any statement through `succ`. -/
structure PcWF (p : Program) : Prop where
  callPc : ∀ n pc c, c ∈ p.calls n pc → pc ∈ p.pcs n
  sitePc : ∀ n pc, p.sites n pc ≠ [] → pc ∈ p.pcs n

/-- A context is admissible for root `E` when its entry fact's mark is in
`S_E`. The zero context is admissible for every root. -/
def CtxOk (p : Program) (E : Node) : Ctx → Prop
  | none => True
  | some f0 => InS p E f0.mark

namespace EngineSoundnessLemmas

theorem mem_callees {p : Program} {n c : Node} {pc : Pc}
    (hc : c ∈ p.calls n pc) (hpc : pc ∈ p.pcs n) : c ∈ p.callees n :=
  List.mem_flatMap.2 ⟨pc, hpc, hc⟩

theorem mem_nodeSites {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (hpc : pc ∈ p.pcs n) (hs : σ ∈ p.sites n pc) : (pc, σ) ∈ p.nodeSites n :=
  List.mem_flatMap.2 ⟨pc, hpc, List.mem_map.2 ⟨σ, hs, rfl⟩⟩

theorem site_pc {p : Program} (wf : PcWF p) {n : Node} {pc : Pc} {σ : ESite}
    (hs : σ ∈ p.sites n pc) : pc ∈ p.pcs n :=
  wf.sitePc n pc (fun h => by rw [h] at hs; cases hs)

theorem cube_mem {σ : ESite} {c : ECube} (hc : c ∈ σ.cond) :
    c.positive.map (·.mark) ∈ σ.abstract.cond :=
  List.mem_map_of_mem hc

theorem gen_mem {σ : ESite} {a : Fact} (ha : a ∈ σ.assigns) :
    a.mark ∈ σ.abstract.gens :=
  List.mem_map_of_mem ha

/-- Finite choice over a list of marks, constructively: from a pointwise
witness on a list we build a witness function (by case split on the decidable
equality of marks, no choice principle). -/
theorem list_choice {α : Type} [Inhabited α] (Q : Mark → α → Prop) :
    ∀ l : List Mark, (∀ m, m ∈ l → ∃ x, Q m x) → ∃ w : Mark → α, ∀ m, m ∈ l → Q m (w m)
  | [], _ => ⟨fun _ => default, fun _ hm => by cases hm⟩
  | a :: l, h => by
    obtain ⟨E, hE⟩ := h a List.mem_cons_self
    obtain ⟨w, hw⟩ := list_choice Q l (fun m hm => h m (List.mem_cons_of_mem _ hm))
    refine ⟨fun x => if x = a then E else w x, fun m hm => ?_⟩
    exact if hma : m = a then by subst hma; simpa using hE
      else by
        simp only [hma, if_false]
        exact hw m ((List.mem_cons.1 hm).resolve_left hma)

/-- Moving a generated fact to `σ.genCtx d0` keeps an admissible context
admissible (it is either `d0` or the zero context). -/
theorem ctxOk_genCtx {p : Program} {E : Node} {σ : ESite} {d0 : Ctx}
    (h : CtxOk p E d0) : CtxOk p E (σ.genCtx d0) := by
  unfold ESite.genCtx
  split
  · trivial
  · exact h

end EngineSoundnessLemmas

open EngineSoundnessLemmas

/-! ## Reachability -/

/-- Call-graph reachability is transitive: a root reaching a caller reaches
everything the caller reaches. -/
theorem Reaches.trans {p : Program} {a b c : Node}
    (h1 : Reaches p a b) (h2 : Reaches p b c) : Reaches p a c := by
  induction h1 with
  | refl => exact h2
  | step hb _ ih => exact .step hb (ih h2)

/-- A root that reaches a node also reaches every callee at a statement the
scan enumerates. -/
theorem Reaches.callee {p : Program} {E n c : Node} {pc : Pc}
    (h : Reaches p E n) (hc : c ∈ p.calls n pc) (hpc : pc ∈ p.pcs n) :
    Reaches p E c :=
  h.trans (.step (mem_callees hc hpc) (.refl c))

/-! ## The engine model -/

/-- The zero fact exists only in the zero context: entry facts never produce
the zero fact, so zero-fact path edges carry no context. -/
theorem pe_zero_ctx {p : Program} {sel : Sel} {n : Node} {d0 : Ctx} {pc : Pc}
    (h : PE p sel n d0 pc none) : d0 = none := by
  suffices ∀ d, PE p sel n d0 pc d → d = none → d0 = none from this _ h rfl
  clear h
  intro d h
  induction h with
  | root => intro _; rfl
  | intra _ _ _ ih => exact ih
  | callZero => intro _; rfl
  | _ => intro hd; cases hd

/-- Main soundness theorem. For every path edge of the engine model under any
selection: (1) some root reaches the node in a context admissible for it, and
(2) the fact's mark is in `S_E` for every root `E` that reaches the node with
an admissible context. For the zero context (joined gens, sink gens) every
root reaching the node is admissible. So the shallow scan's mark sets
over-approximate every fact the precise engine can derive, whatever rules it
installs. -/
theorem pe_sound {p : Program} (wf : PcWF p) {sel : Sel} {n : Node} {d0 : Ctx}
    {pc : Pc} {d : Option Fact} (h : PE p sel n d0 pc d) :
    (∃ E, E ∈ p.roots ∧ Reaches p E n ∧ CtxOk p E d0) ∧
    (∀ f, d = some f → ∀ E, E ∈ p.roots → Reaches p E n → CtxOk p E d0 →
      InS p E f.mark) := by
  induction h with
  | root hr => exact ⟨⟨_, hr, .refl _, trivial⟩, fun _ hf => by cases hf⟩
  | intra _ _ _ ih => exact ih
  | callZero _ hc ih =>
    obtain ⟨⟨E, hE, hR, _⟩, _⟩ := ih
    exact ⟨⟨E, hE, hR.callee hc (wf.callPc _ _ _ hc), trivial⟩, fun _ hf => by cases hf⟩
  | callFact _ hc _ _ ih =>
    obtain ⟨⟨E, hE, hR, hctx⟩, hs⟩ := ih
    refine ⟨⟨E, hE, hR.callee hc (wf.callPc _ _ _ hc), hs _ rfl E hE hR hctx⟩, ?_⟩
    intro _ hf _ _ _ hctx'
    cases hf
    exact hctx'
  | retZero _ hc _ _ _ _ ih0 ihc =>
    refine ⟨ih0.1, ?_⟩
    intro _ hf E hE hR _
    cases hf
    exact ihc.2 _ rfl E hE (hR.callee hc (wf.callPc _ _ _ hc)) trivial
  | retFact _ hc _ _ _ _ _ _ ihf ihc =>
    refine ⟨ihf.1, ?_⟩
    intro _ hf E hE hR hctx
    cases hf
    exact ihc.2 _ rfl E hE (hR.callee hc (wf.callPc _ _ _ hc)) (ihf.2 _ rfl E hE hR hctx)
  | genEmpty hs _ hc hpos ha _ _ ih =>
    obtain ⟨E0, hE0, hR0, hctx0⟩ := ih.1
    refine ⟨⟨E0, hE0, hR0, ctxOk_genCtx hctx0⟩, ?_⟩
    intro _ hf E hE hR _
    cases hf
    exact InS.single hE hR (mem_nodeSites (site_pc wf hs) hs) (cube_mem hc)
      (by simp [hpos]) (by simp [hpos]) (gen_mem ha)
  | @genSingle n d0 pc σ c f a hs _ hc hpos ha _ _ ih =>
    obtain ⟨E0, hE0, hR0, hctx0⟩ := ih.1
    refine ⟨⟨E0, hE0, hR0, ctxOk_genCtx hctx0⟩, ?_⟩
    intro _ hf E hE hR hctx
    cases hf
    have hns := mem_nodeSites (site_pc wf hs) hs
    have hcube : ∀ m, m ∈ c.positive.map (·.mark) → m = f.mark := by
      intro m hm
      simpa only [hpos, List.map_cons, List.map_nil, List.mem_singleton] using hm
    unfold ESite.genCtx at hctx
    split at hctx
    · -- A sink: its gen lands in the zero context, so every root reaching
      -- `n` gets it, including roots whose own context never fires the sink.
      rename_i hk
      refine InS.sinkGen hE hR hns hk (cube_mem hc) (fun _ => E0) (fun _ => n)
        (fun _ _ => hE0) (fun _ _ => hR0) (fun _ _ => rfl) ?_ (gen_mem ha)
      intro m hm
      rw [hcube m hm]
      exact ih.2 _ rfl E0 hE0 hR0 hctx0
    · refine InS.single hE hR hns (cube_mem hc) (by simp [hpos]) ?_ (gen_mem ha)
      intro m hm
      rw [hcube m hm]
      exact ih.2 _ rfl E hE hR hctx
  | @genJoined n pc σ c a hs _ hc hlen ha _ wn w hmeth _ _ ihw ihz =>
    refine ⟨ihz.1, ?_⟩
    intro _ hf E hE hR _
    cases hf
    -- Each premise fact comes from some node `wn f` of the same method; the
    -- existence half at `wn f` supplies a root reaching it.
    have hex : ∀ m, m ∈ c.positive.map (·.mark) → ∃ x : Node × Node,
        x.1 ∈ p.roots ∧ Reaches p x.1 x.2 ∧ p.method x.2 = p.method n ∧ InS p x.1 m := by
      intro m hm
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hm
      obtain ⟨⟨E', hE', hR', hctx'⟩, hs'⟩ := ihw f hf
      exact ⟨(E', wn f), hE', hR', hmeth f hf, hs' f rfl E' hE' hR' hctx'⟩
    obtain ⟨w', hw'⟩ := list_choice _ _ hex
    exact InS.joined hE hR (mem_nodeSites (site_pc wf hs) hs) (cube_mem hc)
      (by simpa using hlen) (fun m => (w' m).1) (fun m => (w' m).2)
      (fun m hm => (hw' m hm).1) (fun m hm => (hw' m hm).2.1)
      (fun m hm => (hw' m hm).2.2.1) (fun m hm => (hw' m hm).2.2.2) (gen_mem ha)
  | copy _ _ _ _ ih =>
    refine ⟨ih.1, ?_⟩
    intro _ hf E hE hR hctx
    cases hf
    exact ih.2 _ rfl E hE hR hctx

/-- Every cube the engine can satisfy at a statement, under any selection,
makes its site `Applicable`. So the shallow scan never deselects a rule the
engine could fire or use to generate a fact. -/
theorem ecube_applicable {p : Program} (wf : PcWF p) {sel : Sel} {n : Node}
    {pc : Pc} {σ : ESite} {c : ECube}
    (hs : σ ∈ p.sites n pc) (hc : c ∈ σ.cond) (hh : ECubeHolds p sel n pc c) :
    Applicable p n pc σ := by
  refine ⟨hs, _, cube_mem hc, ?_⟩
  rcases hh with ⟨hpos, d0, d, hpe⟩ | ⟨f, hpos, d0, hpe⟩ | ⟨hlen, hall⟩
  · obtain ⟨⟨E, hE, hR, _⟩, _⟩ := pe_sound wf hpe
    exact .inl ⟨by simp [hpos], E, hE, hR, by simp [hpos]⟩
  · obtain ⟨⟨E, hE, hR, hctx⟩, hsnd⟩ := pe_sound wf hpe
    refine .inl ⟨by simp [hpos], E, hE, hR, ?_⟩
    intro m hm
    simp only [hpos, List.map_cons, List.map_nil, List.mem_singleton] at hm
    subst hm
    exact hsnd f rfl E hE hR hctx
  · refine .inr ⟨by simpa using hlen, ?_⟩
    intro m hm
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hm
    obtain ⟨n', d0, hm, hpe⟩ := hall f hf
    obtain ⟨⟨E, hE, hR, hctx⟩, hsnd⟩ := pe_sound wf hpe
    exact ⟨E, n', hE, hR, hm, hsnd f rfl E hE hR hctx⟩

/-- Every sink finding of the engine, under any selection, is at an
`Applicable` site: the shallow scan's site selection loses no finding. -/
theorem fires_applicable {p : Program} (wf : PcWF p) {sel : Sel} {n : Node}
    {pc : Pc} {σ : ESite} (h : Fires p sel n pc σ) : Applicable p n pc σ := by
  obtain ⟨hs, _, _, c, hc, hh⟩ := h
  exact ecube_applicable wf hs hc hh

/-! ## `PcWF` is necessary

If a call sits at a statement outside `pcs`, the engine enters the callee but
the scan's call graph (`callees`) has no edge to it, so no root reaches it. -/

namespace EngineSoundnessLemmas

/-- Root `0` calls node `1` at statement `0`, but `pcs` is empty. -/
def noWFProgram : Program where
  nodes := [0, 1]
  roots := [0]
  pcs := fun _ => []
  succ := fun _ _ => []
  exits := fun _ => []
  sites := fun _ _ => []
  calls := fun n pc => if n = 0 ∧ pc = 0 then [1] else []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

end EngineSoundnessLemmas

/-- Without `PcWF` the existence half of `pe_sound` fails: the engine derives
a path edge in node `1`, yet no root reaches node `1` in the scan's call
graph. The hypothesis is therefore needed, not an artefact of the proof. -/
theorem pcwf_needed :
    PE noWFProgram Sel.all 1 none 0 none ∧
    ¬ ∃ E, E ∈ noWFProgram.roots ∧ Reaches noWFProgram E 1 := by
  refine ⟨.callZero (n := 0) (pc := 0) (.root (by decide)) (by decide), ?_⟩
  rintro ⟨E, hE, hR⟩
  cases hR with
  | refl => cases hE with | tail _ h => cases h
  | step hb _ => simp [Program.callees, noWFProgram] at hb

/-! ## D1: the per-root collapse is unsound

`InSNoJoin` evaluates every cube, whatever its length, on a single root's set
`S_E`, and gives the site's gens only to that root; sinks are treated like any
other site. This is the uncorrected, collapsed reading in which `S_E` alone
decides a site. -/

/-- Per-root mark sets without the D1 correction: every cube on `S_E` alone,
gens only to the satisfying root `E`, sinks included. -/
inductive InSNoJoin (p : Program) : Node → Mark → Prop
  | gen {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → (∀ m, m ∈ c → InSNoJoin p E m) →
      g ∈ σ.abstract.gens → InSNoJoin p E g

/-- Applicability without the D1 correction: one root must supply every mark
of the cube. -/
def ApplicableNoJoin (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧
    ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ ∀ m, m ∈ c → InSNoJoin p E m

namespace EngineSoundnessLemmas

/-- Mark `A`. -/
def d1MarkA : Mark := 1
/-- Mark `B`. -/
def d1MarkB : Mark := 2

/-- Root `E1 = 1`: unconditional source of `(base 0, A)`. -/
def d1SrcA : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨0, d1MarkA⟩], copies := [] }
/-- Root `E2 = 2`: unconditional source of `(base 1, B)`. -/
def d1SrcB : ESite :=
  { rule := 2, kind := .source, cond := [[]], assigns := [⟨1, d1MarkB⟩], copies := [] }
/-- Shared node `3`: a sink needing `(base 0, A)` and `(base 1, B)`. -/
def d1Sink : ESite :=
  { rule := 3, kind := .sink
    cond := [[⟨⟨0, d1MarkA⟩, false⟩, ⟨⟨1, d1MarkB⟩, false⟩]]
    assigns := [], copies := [] }

def d1Pcs : Node → List Pc
  | 1 => [0, 1]
  | 2 => [0, 1]
  | 3 => [0]
  | _ => []

def d1Succ : Node → Pc → List Pc
  | 1, 0 => [1]
  | 2, 0 => [1]
  | _, _ => []

def d1Sites : Node → Pc → List ESite
  | 1, 0 => [d1SrcA]
  | 2, 0 => [d1SrcB]
  | 3, 0 => [d1Sink]
  | _, _ => []

def d1Calls : Node → Pc → List Node
  | 1, 1 => [3]
  | 2, 1 => [3]
  | _, _ => []

end EngineSoundnessLemmas

/-- Two roots `E1 = 1`, `E2 = 2` each call the shared node `B = 3` at their
statement `1`. `E1` passes `(0, A)`, `E2` passes `(1, B)`; the sink at `(3, 0)`
needs both. -/
def d1Program : Program where
  nodes := [1, 2, 3]
  roots := [1, 2]
  pcs := d1Pcs
  succ := d1Succ
  exits := fun _ => [0]
  sites := d1Sites
  calls := d1Calls
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ _ => none
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

namespace EngineSoundnessLemmas

theorem d1_calls {n pc c : Node} (h : c ∈ d1Program.calls n pc) : c = 3 ∧ pc ∈ d1Pcs n := by
  simp only [d1Program] at h
  unfold d1Calls at h
  split at h <;> simp_all [d1Pcs]

theorem d1_reaches {a c : Node} (h : Reaches d1Program a c) : c = a ∨ c = 3 := by
  induction h with
  | refl => exact .inl rfl
  | step hb _ ih =>
    obtain ⟨pc, _, hpc⟩ := List.mem_flatMap.1 hb
    have := (d1_calls hpc).1
    rcases ih with h | h
    · exact .inr (h.trans this)
    · exact .inr h

/-- The only per-root marks without the join: `A` for `E1`, `B` for `E2`. -/
theorem d1_noJoin_inv {E m : Node} (h : InSNoJoin d1Program E m) :
    (E = 1 ∧ m = d1MarkA) ∨ (E = 2 ∧ m = d1MarkB) := by
  induction h with
  | gen hE hR hns _ _ hg _ =>
    obtain ⟨pc', _, hmem⟩ := List.mem_flatMap.1 hns
    obtain ⟨σ', hσ', heq⟩ := List.mem_map.1 hmem
    cases heq
    have hE' : E = 1 ∨ E = 2 := by simpa [d1Program] using hE
    rcases d1_reaches hR with rfl | rfl
    · rcases hE' with rfl | rfl
      · simp only [d1Program] at hσ'
        unfold d1Sites at hσ'
        split at hσ' <;> simp_all [ESite.abstract, d1SrcA]
      · simp only [d1Program] at hσ'
        unfold d1Sites at hσ'
        split at hσ' <;> simp_all [ESite.abstract, d1SrcB]
    · simp only [d1Program] at hσ'
      unfold d1Sites at hσ'
      split at hσ' <;> simp_all [ESite.abstract, d1Sink]

end EngineSoundnessLemmas

/-- `d1Program` satisfies the well-formedness hypothesis. -/
theorem d1Program_wf : PcWF d1Program where
  callPc := fun _ _ _ h => (d1_calls h).2
  sitePc := by
    intro n pc h
    simp only [d1Program] at h ⊢
    unfold d1Sites at h
    split at h <;> simp_all [d1Pcs]

/-- The engine (with every rule installed) fires the sink at `(3, 0)`: the
fact `(0, A)` arrives in `E1`'s context and `(1, B)` in `E2`'s, and the
engine joins them at one statement. -/
theorem d1_fires : Fires d1Program Sel.all 3 0 d1Sink := by
  have hA : PE d1Program Sel.all 3 (some ⟨0, d1MarkA⟩) 0 (some ⟨0, d1MarkA⟩) := by
    have h0 : PE d1Program Sel.all 1 none 0 (some ⟨0, d1MarkA⟩) :=
      .genEmpty (σ := d1SrcA) (c := []) List.mem_cons_self rfl List.mem_cons_self rfl
        List.mem_cons_self rfl (d := none) (.root (by decide))
    have h1 : PE d1Program Sel.all 1 none 1 (some ⟨0, d1MarkA⟩) :=
      .intra h0 List.mem_cons_self rfl
    exact .callFact (pc := 1) h1 List.mem_cons_self rfl rfl
  have hB : PE d1Program Sel.all 3 (some ⟨1, d1MarkB⟩) 0 (some ⟨1, d1MarkB⟩) := by
    have h0 : PE d1Program Sel.all 2 none 0 (some ⟨1, d1MarkB⟩) :=
      .genEmpty (σ := d1SrcB) (c := []) List.mem_cons_self rfl List.mem_cons_self rfl
        List.mem_cons_self rfl (d := none) (.root (by decide))
    have h1 : PE d1Program Sel.all 2 none 1 (some ⟨1, d1MarkB⟩) :=
      .intra h0 List.mem_cons_self rfl
    exact .callFact (pc := 1) h1 List.mem_cons_self rfl rfl
  refine ⟨List.mem_cons_self, rfl, rfl, _, List.mem_cons_self, .inr (.inr ⟨by decide, ?_⟩)⟩
  intro f hf
  have : f = ⟨0, d1MarkA⟩ ∨ f = ⟨1, d1MarkB⟩ := by
    have hpos : ECube.positive [⟨⟨0, d1MarkA⟩, false⟩, ⟨⟨1, d1MarkB⟩, false⟩] =
        [⟨0, d1MarkA⟩, ⟨1, d1MarkB⟩] := by decide
    simpa [hpos] using hf
  rcases this with rfl | rfl
  · exact ⟨3, _, rfl, hA⟩
  · exact ⟨3, _, rfl, hB⟩

/-- The collapsed per-root semantics does not select that sink: no single
root has both `A` and `B`. Together with `d1_fires` this shows that without
the D1 correction the shallow scan would drop a real finding. -/
theorem d1_not_applicableNoJoin : ¬ ApplicableNoJoin d1Program 3 0 d1Sink := by
  rintro ⟨_, c, hc, E, _, _, hall⟩
  have hcond : d1Sink.abstract.cond = [[d1MarkA, d1MarkB]] := by decide
  have hc' : c = [d1MarkA, d1MarkB] := by
    rw [hcond] at hc
    simpa using hc
  subst hc'
  rcases d1_noJoin_inv (hall _ List.mem_cons_self) with ⟨h1, _⟩ | ⟨_, h⟩
  · rcases d1_noJoin_inv (hall d1MarkB (by simp)) with ⟨_, h⟩ | ⟨h2, _⟩
    · exact absurd h (by decide)
    · exact absurd (h1.symm.trans h2) (by decide)
  · exact absurd h (by decide)

/-- With the D1 correction the sink is selected, as `fires_applicable`
guarantees. -/
theorem d1_applicable : Applicable d1Program 3 0 d1Sink :=
  fires_applicable d1Program_wf d1_fires

/-! ## Precision witness: `Applicable` without `Fires`

Root `1` calls node `2` at statement `0`, then reaches the sink at statement
`1`. Node `2` assigns mark `M` to a local base `5`, which `mapOut` drops. The
scan erases bases and returns, so it deems the sink applicable; the engine
never sees the mark in node `1`. A refinement target: escape-aware returns. -/

namespace EngineSoundnessLemmas

def pwMark : Mark := 7

def pwSrc : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨5, pwMark⟩], copies := [] }
def pwSink : ESite :=
  { rule := 2, kind := .sink, cond := [[⟨⟨0, pwMark⟩, false⟩]], assigns := [], copies := [] }

def pwPcs : Node → List Pc
  | 1 => [0, 1]
  | 2 => [0]
  | _ => []

def pwSucc : Node → Pc → List Pc
  | 1, 0 => [1]
  | _, _ => []

def pwSites : Node → Pc → List ESite
  | 1, 1 => [pwSink]
  | 2, 0 => [pwSrc]
  | _, _ => []

def pwCalls : Node → Pc → List Node
  | 1, 0 => [2]
  | _, _ => []

end EngineSoundnessLemmas

/-- The precision-witness program. -/
def pwProgram : Program where
  nodes := [1, 2]
  roots := [1]
  pcs := pwPcs
  succ := pwSucc
  exits := fun _ => [0]
  sites := pwSites
  calls := pwCalls
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ _ => none
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

namespace EngineSoundnessLemmas

theorem pw_calls {n pc c : Node} (h : c ∈ pwProgram.calls n pc) : c = 2 ∧ pc ∈ pwPcs n := by
  simp only [pwProgram] at h
  unfold pwCalls at h
  split at h <;> simp_all [pwPcs]

theorem pw_sites1 {pc : Pc} {σ : ESite} (h : σ ∈ pwProgram.sites 1 pc) : σ.assigns = [] := by
  simp only [pwProgram] at h
  unfold pwSites at h
  split at h <;> simp_all [pwSink]

/-- Node `1` only ever holds the zero fact. -/
theorem pw_inv {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact}
    (h : PE pwProgram Sel.all n d0 pc d) : n = 1 → d = none := by
  induction h with
  | root => intro _; rfl
  | intra _ _ _ ih => exact ih
  | callZero _ hc => intro _; rfl
  | callFact _ hc => intro h; exact absurd ((pw_calls hc).1.symm.trans h) (by decide)
  | retZero _ _ _ _ hout => cases hout
  | retFact _ _ _ _ _ _ hout => cases hout
  | genEmpty hs _ _ _ ha =>
    intro h; subst h; rw [pw_sites1 hs] at ha; cases ha
  | genSingle hs _ _ _ ha =>
    intro h; subst h; rw [pw_sites1 hs] at ha; cases ha
  | genJoined hs _ _ _ ha =>
    intro h; subst h; rw [pw_sites1 hs] at ha; cases ha
  | copy _ _ _ _ ih => intro h; cases ih h

end EngineSoundnessLemmas

/-- `pwProgram` satisfies the well-formedness hypothesis. -/
theorem pwProgram_wf : PcWF pwProgram where
  callPc := fun _ _ _ h => (pw_calls h).2
  sitePc := by
    intro n pc h
    simp only [pwProgram] at h ⊢
    unfold pwSites at h
    split at h <;> simp_all [pwPcs]

/-- The scan selects the sink at `(1, 1)`: mark `M` is in `S_1` because root
`1` reaches the source in node `2`. -/
theorem pw_applicable : Applicable pwProgram 1 1 pwSink := by
  have hM : InS pwProgram 1 pwMark :=
    InS.single (n := 2) (pc := 0) (σ := pwSrc) (c := []) List.mem_cons_self
      (.step (b := 2) (by decide) (.refl 2)) (mem_nodeSites (by decide) List.mem_cons_self)
      (by decide) (by decide)
      (fun _ h => by cases h) List.mem_cons_self
  refine ⟨List.mem_cons_self, [pwMark], by decide, .inl ⟨by decide, 1, List.mem_cons_self,
    .refl 1, ?_⟩⟩
  intro m hm
  simp only [List.mem_singleton] at hm
  subst hm
  exact hM

/-- The engine never fires that sink, even with every rule installed: the
mark lives on a callee-local base that the return drops. So `Applicable` is
an over-approximation, and the scan is sound but not complete. -/
theorem pw_not_fires : ¬ Fires pwProgram Sel.all 1 1 pwSink := by
  rintro ⟨_, _, _, c, hc, hh⟩
  simp only [pwSink, List.mem_singleton] at hc
  subst hc
  have hpos : ECube.positive [⟨⟨0, pwMark⟩, false⟩] = [⟨0, pwMark⟩] := by decide
  rcases hh with ⟨h, _⟩ | ⟨f, h, _, hpe⟩ | ⟨h, _⟩
  · rw [hpos] at h; cases h
  · cases pw_inv hpe rfl
  · rw [hpos] at h; exact absurd h (by decide)

/-! ## Sink gens must reach every root that reaches the sink

The engine emits a sink's `trackFactsReachAnalysisEnd` facts in the zero
context, whatever context the sink fired in. Zero-context facts return to
every caller. So a root that reaches the sink node, but never supplies the
sink's condition itself, still receives the gen. `InSNoSinkGen` is `InS`
without the `sinkGen` constructor: it gives a single-literal sink's gens only
to the root that satisfies the sink, as a source's gens. The program below
shows that this misses a finding.

Roots `E1 = 1` and `E2 = 2` both call node `3` at their statement `1`.
* `E1` makes `(0, A)` at statement `0` and passes it to node `3`.
* Node `3` has a sink at statement `0` that needs `(0, A)`. When it fires, it
  gens `(0, T)`, its `trackFactsReachAnalysisEnd` mark.
* `E2` never has `A`. Its zero-fact call to node `3` returns the zero-context
  `(0, T)` to its statement `2`, where a second sink that needs `(0, T)`
  fires. -/

/-- `InS` without the `sinkGen` constructor: a sink's gens go only to the root
that satisfies it (its single-literal cube is evaluated on that root's set). -/
inductive InSNoSinkGen (p : Program) : Node → Mark → Prop
  | single {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → c.length ≤ 1 →
      (∀ m, m ∈ c → InSNoSinkGen p E m) →
      g ∈ σ.abstract.gens → InSNoSinkGen p E g
  | joined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → 2 ≤ c.length →
      (w wn : Mark → Node) →
      (∀ m, m ∈ c → w m ∈ p.roots) → (∀ m, m ∈ c → Reaches p (w m) (wn m)) →
      (∀ m, m ∈ c → p.method (wn m) = p.method n) →
      (∀ m, m ∈ c → InSNoSinkGen p (w m) m) →
      g ∈ σ.abstract.gens → InSNoSinkGen p E g

/-- `Applicable`, with `CubeSat` evaluated on `InSNoSinkGen`. -/
def ApplicableNoSinkGen (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧
    ((c.length ≤ 1 ∧ ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ ∀ m, m ∈ c → InSNoSinkGen p E m) ∨
     (2 ≤ c.length ∧ ∀ m, m ∈ c →
       ∃ E n', E ∈ p.roots ∧ Reaches p E n' ∧ p.method n' = p.method n ∧ InSNoSinkGen p E m))

namespace EngineSoundnessLemmas

/-- Mark `A`. -/
def sgMarkA : Mark := 1
/-- Mark `T`, the first sink's `trackFactsReachAnalysisEnd` mark. -/
def sgMarkT : Mark := 2

/-- `E1`, statement `0`: unconditional source of `(0, A)`. -/
def sgSrcA : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨0, sgMarkA⟩], copies := [] }
/-- Node `3`, statement `0`: a sink that needs `(0, A)` and gens `(0, T)`. -/
def sgSinkA : ESite :=
  { rule := 2, kind := .sink, cond := [[⟨⟨0, sgMarkA⟩, false⟩]]
    assigns := [⟨0, sgMarkT⟩], copies := [] }
/-- `E2`, statement `2`: a sink that needs `(0, T)`. -/
def sgSinkT : ESite :=
  { rule := 3, kind := .sink, cond := [[⟨⟨0, sgMarkT⟩, false⟩]], assigns := [], copies := [] }

def sgPcs : Node → List Pc
  | 1 => [0, 1]
  | 2 => [0, 1, 2]
  | 3 => [0]
  | _ => []

def sgSucc : Node → Pc → List Pc
  | 1, 0 => [1]
  | 2, 0 => [1]
  | 2, 1 => [2]
  | _, _ => []

def sgSites : Node → Pc → List ESite
  | 1, 0 => [sgSrcA]
  | 3, 0 => [sgSinkA]
  | 2, 2 => [sgSinkT]
  | _, _ => []

def sgCalls : Node → Pc → List Node
  | 1, 1 => [3]
  | 2, 1 => [3]
  | _, _ => []

end EngineSoundnessLemmas

/-- The sink-gen witness program. Returns keep bases. -/
def sgProgram : Program where
  nodes := [1, 2, 3]
  roots := [1, 2]
  pcs := sgPcs
  succ := sgSucc
  exits := fun _ => [0]
  sites := sgSites
  calls := sgCalls
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

namespace EngineSoundnessLemmas

theorem sg_calls {n pc c : Node} (h : c ∈ sgProgram.calls n pc) : c = 3 ∧ pc ∈ sgPcs n := by
  simp only [sgProgram] at h
  unfold sgCalls at h
  split at h <;> simp_all [sgPcs]

theorem sg_reaches {a c : Node} (h : Reaches sgProgram a c) : c = a ∨ c = 3 := by
  induction h with
  | refl => exact .inl rfl
  | step hb _ ih =>
    obtain ⟨pc, _, hpc⟩ := List.mem_flatMap.1 hb
    have := (sg_calls hpc).1
    rcases ih with h | h
    · exact .inr (h.trans this)
    · exact .inr h

/-- Every abstract site of the program: the source at node `1`, the first sink
at node `3`, the second sink at node `2`. -/
theorem sg_nodeSites {n pc : Nat} {σ : ESite} (h : (pc, σ) ∈ sgProgram.nodeSites n) :
    (n = 1 ∧ σ = sgSrcA) ∨ (n = 3 ∧ σ = sgSinkA) ∨ (n = 2 ∧ σ = sgSinkT) := by
  obtain ⟨pc', _, hmem⟩ := List.mem_flatMap.1 h
  obtain ⟨σ', hσ', heq⟩ := List.mem_map.1 hmem
  cases heq
  simp only [sgProgram] at hσ'
  unfold sgSites at hσ'
  split at hσ' <;> simp_all

/-- Every cube of the program has at most one literal. -/
theorem sg_short {n pc : Nat} {σ : ESite} {c : Cube} (h : (pc, σ) ∈ sgProgram.nodeSites n)
    (hc : c ∈ σ.abstract.cond) : c.length ≤ 1 := by
  have h1 : ∀ c, c ∈ sgSrcA.abstract.cond → c.length ≤ 1 := by decide
  have h2 : ∀ c, c ∈ sgSinkA.abstract.cond → c.length ≤ 1 := by decide
  have h3 : ∀ c, c ∈ sgSinkT.abstract.cond → c.length ≤ 1 := by decide
  rcases sg_nodeSites h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact h1 c hc
  · exact h2 c hc
  · exact h3 c hc

/-- Without `sinkGen`, only `E1` has marks: `A`, and `T` from the first sink
it satisfies. -/
theorem sg_noSinkGen_inv {E m : Node} (h : InSNoSinkGen sgProgram E m) :
    E = 1 ∧ (m = sgMarkA ∨ m = sgMarkT) := by
  induction h with
  | @single E n pc σ c g hE hR hns hc _ _ hg ih =>
    rcases sg_nodeSites hns with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hg' : g = sgMarkA := by simpa [ESite.abstract, sgSrcA] using hg
      refine ⟨?_, .inl hg'⟩
      rcases sg_reaches hR with h | h
      · exact h.symm
      · exact absurd h (by decide)
    · have hcond : sgSinkA.abstract.cond = [[sgMarkA]] := by decide
      rw [hcond, List.mem_singleton] at hc
      subst hc
      have hg' : g = sgMarkT := by simpa [ESite.abstract, sgSinkA] using hg
      exact ⟨(ih _ List.mem_cons_self).1, .inr hg'⟩
    · simp [ESite.abstract, sgSinkT] at hg
  | joined _ _ hns hc hlen =>
    exact absurd (Nat.le_trans hlen (sg_short hns hc)) (by decide)

end EngineSoundnessLemmas

/-- `sgProgram` satisfies the well-formedness hypothesis. -/
theorem sgProgram_wf : PcWF sgProgram where
  callPc := fun _ _ _ h => (sg_calls h).2
  sitePc := by
    intro n pc h
    simp only [sgProgram] at h ⊢
    unfold sgSites at h
    split at h <;> simp_all [sgPcs]

/-- The engine (with every rule installed) fires the second sink at `(2, 2)`.
The first sink fires in node `3` under `E1`'s context `(0, A)`; its gen
`(0, T)` lands in node `3`'s zero context and returns through `E2`'s
zero-fact call. -/
theorem sg_fires : Fires sgProgram Sel.all 2 2 sgSinkT := by
  -- `E1` passes `(0, A)` to node `3`.
  have hA : PE sgProgram Sel.all 3 (some ⟨0, sgMarkA⟩) 0 (some ⟨0, sgMarkA⟩) := by
    have h0 : PE sgProgram Sel.all 1 none 0 (some ⟨0, sgMarkA⟩) :=
      .genEmpty (σ := sgSrcA) (c := []) List.mem_cons_self rfl List.mem_cons_self rfl
        List.mem_cons_self rfl (d := none) (.root (by decide))
    exact .callFact (pc := 1) (.intra h0 List.mem_cons_self rfl) List.mem_cons_self rfl rfl
  -- The first sink fires in that context; its gen lands in the zero context.
  have hT : PE sgProgram Sel.all 3 none 0 (some ⟨0, sgMarkT⟩) :=
    .genSingle (σ := sgSinkA) (c := [⟨⟨0, sgMarkA⟩, false⟩]) List.mem_cons_self rfl
      List.mem_cons_self (by decide) List.mem_cons_self rfl hA
  -- `E2`'s zero-fact call to node `3` returns `(0, T)`.
  have hz : PE sgProgram Sel.all 2 none 1 none :=
    .intra (.root (by decide)) List.mem_cons_self rfl
  have hE2 : PE sgProgram Sel.all 2 none 2 (some ⟨0, sgMarkT⟩) :=
    .retZero (c := 3) (ex := 0) hz List.mem_cons_self hT List.mem_cons_self rfl
      List.mem_cons_self
  exact ⟨List.mem_cons_self, rfl, rfl, _, List.mem_cons_self,
    .inr (.inl ⟨⟨0, sgMarkT⟩, by decide, _, hE2⟩)⟩

/-- Without `sinkGen` the scan drops that finding: `T` reaches only `E1`'s set,
and `E1` does not reach node `2`. So a sink's gens must go to every root that
reaches the sink node, not only to the root whose context satisfies it. -/
theorem sinkgen_zero_ctx_needed :
    Fires sgProgram Sel.all 2 2 sgSinkT ∧ ¬ ApplicableNoSinkGen sgProgram 2 2 sgSinkT := by
  refine ⟨sg_fires, ?_⟩
  rintro ⟨_, c, hc, h⟩
  have hcond : sgSinkT.abstract.cond = [[sgMarkT]] := by decide
  rw [hcond, List.mem_singleton] at hc
  subst hc
  rcases h with ⟨_, E, _, hR, hall⟩ | ⟨hlen, _⟩
  · have h1 := (sg_noSinkGen_inv (hall _ List.mem_cons_self)).1
    subst h1
    rcases sg_reaches hR with h | h <;> exact absurd h (by decide)
  · exact absurd hlen (by decide)

/-- With `sinkGen` the scan selects it, as `fires_applicable` guarantees. -/
theorem sg_applicable : Applicable sgProgram 2 2 sgSinkT :=
  fires_applicable sgProgram_wf sg_fires

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
