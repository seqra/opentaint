import MarkScan.Basic

/-!
# Option 3*: the flow-sensitive mark-set scan

Option 3* resolves rules and calls in CFG order, so that a later call does not
contribute marks to an earlier call's IN set. This module defines the
flow-sensitive refinement of the flow-insensitive scan `InS`:

* per root `E` and per program point `(n, pc)`;
* context-insensitive across callers within one root: a callee's entry set is
  the union over its call sites reachable under `E`, and its exit set flows
  back to every call site reachable under `E`;
* no kills (an over-approximation, as in `InS`);
* the same D1 join rule as `InS`: a cube of one literal (or none) is evaluated
  on the set of `E` at that point, a cube of two or more literals on the union
  over every root that reaches that point.

Results:
1. `fs_sound` / `pe_ptreach`: the engine model `PE` is covered, for every root
   that reaches the point and under which the fact's context is valid;
   `fs_ctx_needed`: that context condition cannot be dropped.
2. `fs_fires_applicable`: every engine finding selects its sink.
3. `fs_refines_fi`, `applicableFS_implies_applicable`: 3* never selects more
   than the default flow-insensitive mode.
4. `fs_strict`: 3* is strictly finer (sink before source, no loop).
5. `linear_order_unsound`: the "statement order" reading of 3* is unsound on a
   loop; 3* must be a CFG fixpoint.
6. `fsPoints_length`: the number of `(root, point)` pairs is
   `|roots| · Σ_n |pcs n|`.
-/

namespace MarkScan

/-! ## Definitions -/

/-- `PtReach p E n pc`: the point `(n, pc)` is reachable under root `E`.

There is no separate "return successor" rule. In the engine model the `intra`
rule passes every fact, the zero fact included, along every CFG edge,
including the edge from a call statement to its successor (call-to-return).
So the return successor of a reachable call point is always reachable,
whether or not some callee exit is. This is the "always" variant, and it is
the one the soundness proof needs, because `PE.intra` does not look at calls. -/
inductive PtReach (p : Program) (E : Node) : Node → Pc → Prop
  | root : E ∈ p.roots → PtReach p E E 0
  | succ {n : Node} {pc pc' : Pc} : PtReach p E n pc → pc' ∈ p.succ n pc → PtReach p E n pc'
  | call {n c : Node} {pc : Pc} : PtReach p E n pc → c ∈ p.calls n pc → PtReach p E c 0

/-- `InFS p E n pc m`: the mark `m` may hold at `(n, pc)` under root `E`.

* `flow`: along CFG edges, with no kills.
* `callIn`: from a call point into the callee's entry. The callee entry set is
  the union over all call sites reachable under `E`.
* `ret`: from a callee exit back to the successor of every call point of that
  callee that is reachable under `E`.
* `single`: gens of a site whose cube has at most one literal, evaluated on
  the set of `E` at `(n, pc)`.
* `joined`: gens of a site whose cube has two or more literals. Each literal's
  mark must be present at `(n, pc)` under some root `w m` that reaches that
  point (the D1 join over contexts). -/
inductive InFS (p : Program) : Node → Node → Pc → Mark → Prop
  | flow {E n : Node} {pc pc' : Pc} {m : Mark} :
      InFS p E n pc m → pc' ∈ p.succ n pc → InFS p E n pc' m
  | callIn {E n c : Node} {pc : Pc} {m : Mark} :
      InFS p E n pc m → c ∈ p.calls n pc → InFS p E c 0 m
  | ret {E n c : Node} {pc pc' ex : Pc} {m : Mark} :
      PtReach p E n pc → c ∈ p.calls n pc → InFS p E c ex m → ex ∈ p.exits c →
      pc' ∈ p.succ n pc → InFS p E n pc' m
  | single {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      PtReach p E n pc → σ ∈ p.sites n pc → c ∈ σ.abstract.cond → c.length ≤ 1 →
      (∀ m, m ∈ c → InFS p E n pc m) → g ∈ σ.abstract.gens → InFS p E n pc g
  | joined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      PtReach p E n pc → σ ∈ p.sites n pc → c ∈ σ.abstract.cond → 2 ≤ c.length →
      (w : Mark → Node) → (∀ m, m ∈ c → PtReach p (w m) n pc) →
      (∀ m, m ∈ c → InFS p (w m) n pc m) → g ∈ σ.abstract.gens → InFS p E n pc g

/-- The cube `c` of a site at `(n, pc)` is satisfiable in the flow-sensitive
semantics. -/
def CubeSatFS (p : Program) (n : Node) (pc : Pc) (c : Cube) : Prop :=
  (c.length ≤ 1 ∧ ∃ E, PtReach p E n pc ∧ ∀ m, m ∈ c → InFS p E n pc m) ∨
  (2 ≤ c.length ∧ ∀ m, m ∈ c → ∃ E, PtReach p E n pc ∧ InFS p E n pc m)

/-- Option 3* selects the site `σ` at `(n, pc)`. -/
def ApplicableFS (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧ CubeSatFS p n pc c

/-- The engine context `d0` of node `n` is valid under root `E`: the zero
context always is, and a fact context is valid when its mark is in the entry
set of `n` under `E`. -/
def CtxOkFS (p : Program) (E n : Node) : Ctx → Prop
  | none => True
  | some f0 => InFS p E n 0 f0.mark

/-- Well-formedness needed to compare with `InS`: calls and sites sit at
statements listed in `pcs`. -/
structure FSWF (p : Program) : Prop where
  calls_pc : ∀ n pc c, c ∈ p.calls n pc → pc ∈ p.pcs n
  sites_pc : ∀ n pc σ, σ ∈ p.sites n pc → pc ∈ p.pcs n

/-! ## Example sites (used by the concrete programs below) -/

/-- A sink on mark `1` (one literal, on base `0`). It generates nothing. -/
def fsSinkSite : ESite :=
  { rule := 0, kind := .sink, cond := [[⟨⟨0, 1⟩, false⟩]], assigns := [], copies := [] }

/-- An unconditional source of mark `1` on base `0`. -/
def fsSrcSite : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }

/-! ## Helpers -/

namespace FlowSensitiveLemmas

theorem ptreach_root {p : Program} {E n : Node} {pc : Pc} (h : PtReach p E n pc) :
    E ∈ p.roots := by
  induction h with
  | root h => exact h
  | succ _ _ ih => exact ih
  | call _ _ ih => exact ih

theorem ptreach_entry {p : Program} {E n : Node} {pc : Pc} (h : PtReach p E n pc) :
    PtReach p E n 0 := by
  induction h with
  | root h => exact PtReach.root h
  | succ _ _ ih => exact ih
  | call h hc _ => exact PtReach.call h hc

theorem infs_ptreach {p : Program} {E n : Node} {pc : Pc} {m : Mark} (h : InFS p E n pc m) :
    PtReach p E n pc := by
  induction h with
  | flow _ hs ih => exact ih.succ hs
  | callIn _ hc ih => exact ih.call hc
  | ret hr _ _ _ hs _ => exact hr.succ hs
  | single hr _ _ _ _ _ _ => exact hr
  | joined hr _ _ _ _ _ _ _ _ => exact hr

theorem reaches_snoc {p : Program} {a b c : Node} (h : Reaches p a b) (hc : c ∈ p.callees b) :
    Reaches p a c := by
  induction h with
  | refl _ => exact Reaches.step hc (Reaches.refl c)
  | step hab _ ih => exact Reaches.step hab (ih hc)

theorem ptreach_reaches {p : Program} (hw : FSWF p) {E n : Node} {pc : Pc}
    (h : PtReach p E n pc) : Reaches p E n := by
  induction h with
  | root _ => exact Reaches.refl _
  | succ _ _ ih => exact ih
  | @call n c pc _ hc ih =>
    refine reaches_snoc ih ?_
    unfold Program.callees
    exact List.mem_flatMap.mpr ⟨pc, hw.calls_pc n pc c hc, hc⟩

theorem abs_mem {σ : ESite} {c : ECube} (h : c ∈ σ.cond) :
    c.positive.map (·.mark) ∈ σ.abstract.cond :=
  List.mem_map_of_mem h

theorem gen_mem {σ : ESite} {a : Fact} (h : a ∈ σ.assigns) : a.mark ∈ σ.abstract.gens :=
  List.mem_map_of_mem h

theorem nodeSites_mem {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (hp : pc ∈ p.pcs n) (hs : σ ∈ p.sites n pc) : (pc, σ) ∈ p.nodeSites n := by
  unfold Program.nodeSites
  exact List.mem_flatMap.mpr ⟨pc, hp, List.mem_map_of_mem hs⟩

/-- Finite choice over a list with decidable equality (constructive). -/
theorem choose_fin {α β : Type} [DecidableEq α] (b0 : β) (P : α → β → Prop) :
    ∀ l : List α, (∀ x, x ∈ l → ∃ y, P x y) → ∃ g : α → β, ∀ x, x ∈ l → P x (g x)
  | [], _ => ⟨fun _ => b0, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x (List.mem_cons_self)
    obtain ⟨g, hg⟩ := choose_fin b0 P l (fun z hz => h z (List.mem_cons_of_mem _ hz))
    refine ⟨fun z => if z = x then y else g z, ?_⟩
    intro z hz
    show P z (if z = x then y else g z)
    split
    · next hzx => subst hzx; exact hy
    · next hzx =>
      cases hz with
      | head => exact absurd rfl hzx
      | tail _ h' => exact hg z h'

/-- The combined invariant proved by induction on `PE`. -/
def Goal (p : Program) (n : Node) (d0 : Ctx) (pc : Pc) (d : Option Fact) : Prop :=
  (∃ E, PtReach p E n pc ∧ CtxOkFS p E n d0) ∧
  (∀ E, PtReach p E n 0 → CtxOkFS p E n d0 →
     PtReach p E n pc ∧ ∀ f, d = some f → InFS p E n pc f.mark)

theorem sound_aux {p : Program} {sel : Sel} {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact}
    (h : PE p sel n d0 pc d) : Goal p n d0 pc d := by
  induction h with
  | root hr =>
    exact ⟨⟨_, PtReach.root hr, trivial⟩, fun E hE _ => ⟨hE, fun f hf => nomatch hf⟩⟩
  | intra _ hs _ ih =>
    obtain ⟨⟨E, hr, hc⟩, hall⟩ := ih
    refine ⟨⟨E, hr.succ hs, hc⟩, fun E' h0 hc' => ?_⟩
    obtain ⟨hr', hin⟩ := hall E' h0 hc'
    exact ⟨hr'.succ hs, fun f hf => (hin f hf).flow hs⟩
  | callZero _ hc ih =>
    obtain ⟨⟨E, hr, _⟩, _⟩ := ih
    exact ⟨⟨E, hr.call hc, trivial⟩, fun _ h0 _ => ⟨h0, fun f hf => nomatch hf⟩⟩
  | @callFact n c d0 pc f b _ hc _ _ ih =>
    obtain ⟨⟨E, hr, hctx⟩, hall⟩ := ih
    obtain ⟨_, hin⟩ := hall E (ptreach_entry hr) hctx
    refine ⟨⟨E, hr.call hc, (hin f rfl).callIn hc⟩, fun _ h0' hc' => ⟨h0', fun f' hf' => ?_⟩⟩
    cases hf'
    exact hc'
  | @retZero n c d0 pc pc' ex g b _ hc _ hex _ hs ih1 ih2 =>
    obtain ⟨⟨E, hr, hctx⟩, hall1⟩ := ih1
    obtain ⟨_, hall2⟩ := ih2
    refine ⟨⟨E, hr.succ hs, hctx⟩, fun E' h0 hc' => ?_⟩
    obtain ⟨hr', _⟩ := hall1 E' h0 hc'
    obtain ⟨_, hin2⟩ := hall2 E' (hr'.call hc) trivial
    refine ⟨hr'.succ hs, fun f hf => ?_⟩
    cases hf
    exact InFS.ret hr' hc (hin2 g rfl) hex hs
  | @retFact n c d0 pc pc' ex f g bi b _ hc _ _ _ hex _ hs ih1 ih2 =>
    obtain ⟨⟨E, hr, hctx⟩, hall1⟩ := ih1
    obtain ⟨_, hall2⟩ := ih2
    refine ⟨⟨E, hr.succ hs, hctx⟩, fun E' h0 hc' => ?_⟩
    obtain ⟨hr', hin1⟩ := hall1 E' h0 hc'
    have hctx2 : CtxOkFS p E' c (some ⟨bi, f.mark⟩) := (hin1 f rfl).callIn hc
    obtain ⟨_, hin2⟩ := hall2 E' (hr'.call hc) hctx2
    refine ⟨hr'.succ hs, fun f' hf => ?_⟩
    cases hf
    exact InFS.ret hr' hc (hin2 g rfl) hex hs
  | genEmpty hσ _ hcσ hpos ha _ _ ih =>
    obtain ⟨hex, hall⟩ := ih
    refine ⟨hex, fun E h0 hc => ?_⟩
    obtain ⟨hr, _⟩ := hall E h0 hc
    refine ⟨hr, fun f hf => ?_⟩
    cases hf
    exact InFS.single hr hσ (abs_mem hcσ) (by rw [hpos]; simp) (by rw [hpos]; simp) (gen_mem ha)
  | @genSingle n d0 pc σ c f a hσ _ hcσ hpos ha _ _ ih =>
    obtain ⟨hex, hall⟩ := ih
    refine ⟨hex, fun E h0 hc => ?_⟩
    obtain ⟨hr, hin⟩ := hall E h0 hc
    refine ⟨hr, fun f' hf => ?_⟩
    cases hf
    refine InFS.single hr hσ (abs_mem hcσ) (by rw [hpos]; simp) ?_ (gen_mem ha)
    intro m hm
    rw [hpos] at hm
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
    subst hm
    exact hin f rfl
  | @genJoined n pc σ c a hσ _ hcσ hlen ha _ w _ _ ih_fs ih0 =>
    obtain ⟨hex, hall0⟩ := ih0
    refine ⟨hex, fun E h0 _ => ?_⟩
    obtain ⟨hr, _⟩ := hall0 E h0 trivial
    refine ⟨hr, fun f' hf => ?_⟩
    cases hf
    have hper : ∀ m, m ∈ c.positive.map (·.mark) →
        ∃ E', PtReach p E' n pc ∧ InFS p E' n pc m := by
      intro m hm
      obtain ⟨f, hf, hfm⟩ := List.mem_map.mp hm
      subst hfm
      obtain ⟨⟨E', hr', hctx'⟩, hall'⟩ := ih_fs f hf
      exact ⟨E', hr', (hall' E' (ptreach_entry hr') hctx').2 f rfl⟩
    obtain ⟨W, hW⟩ := choose_fin (0 : Node) (fun m E' => PtReach p E' n pc ∧ InFS p E' n pc m)
      _ hper
    exact InFS.joined hr hσ (abs_mem hcσ) (by simpa using hlen) W
      (fun m hm => (hW m hm).1) (fun m hm => (hW m hm).2) (gen_mem ha)
  | @copy n d0 pc σ fr to m _ _ _ _ ih =>
    obtain ⟨hex, hall⟩ := ih
    refine ⟨hex, fun E h0 hc => ?_⟩
    obtain ⟨hr, hin⟩ := hall E h0 hc
    refine ⟨hr, fun f hf => ?_⟩
    cases hf
    have h := hin ⟨fr, m⟩ rfl
    exact h

end FlowSensitiveLemmas

open FlowSensitiveLemmas

/-! ## 1. Soundness w.r.t. the engine model -/

/-- Every engine path edge sits at a point reachable under some root for which
its context is valid. With `fs_sound` this says the per-root, per-point sets of
option 3* never miss an engine fact. -/
theorem pe_ptreach {p : Program} {sel : Sel} {n : Node} {d0 : Ctx} {pc : Pc} {d : Option Fact}
    (h : PE p sel n d0 pc d) :
    ∃ E, E ∈ p.roots ∧ PtReach p E n pc ∧ CtxOkFS p E n d0 := by
  obtain ⟨E, hr, hc⟩ := (sound_aux h).1
  exact ⟨E, ptreach_root hr, hr, hc⟩

/-- Soundness of option 3*: an engine fact `f` at `(n, pc)` in context `d0`
has its mark in the flow-sensitive set of every root `E` that reaches the
point and under which the context `d0` is valid (the context mark is in `n`'s
entry set under `E`), and at least one such root exists. The context condition
is what makes a per-root statement true for facts inside callees. -/
theorem fs_sound {p : Program} {sel : Sel} {n : Node} {d0 : Ctx} {pc : Pc} {f : Fact}
    (h : PE p sel n d0 pc (some f)) :
    (∃ E, E ∈ p.roots ∧ PtReach p E n pc ∧ CtxOkFS p E n d0) ∧
    ∀ E, E ∈ p.roots → PtReach p E n pc → CtxOkFS p E n d0 → InFS p E n pc f.mark := by
  refine ⟨pe_ptreach h, fun E _ hr hc => ?_⟩
  exact ((sound_aux h).2 E (ptreach_entry hr) hc).2 f rfl

/-- Two roots `0` and `1` both call node `2` at `pc 1`. Root `0` has an
unconditional source of mark `1` at `pc 0` and passes it to the callee; root
`1` passes nothing. -/
def exCtx : Program where
  nodes := [0, 1, 2]
  roots := [0, 1]
  pcs := fun _ => [0, 1]
  succ := fun _ pc => if pc = 0 then [1] else []
  exits := fun _ => [1]
  sites := fun n pc => if n = 0 ∧ pc = 0 then [fsSrcSite] else []
  calls := fun n pc => if (n = 0 ∨ n = 1) ∧ pc = 1 then [2] else []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false

namespace FlowSensitiveLemmas

theorem exCtx_ptreach {E n : Node} {pc : Pc} (h : PtReach exCtx E n pc) : n = 0 → E = 0 := by
  induction h with
  | root _ => exact id
  | succ _ _ ih => exact ih
  | call _ hc _ =>
    intro h0
    subst h0
    simp only [exCtx] at hc
    split at hc
    · simp at hc
    · exact absurd hc List.not_mem_nil

theorem exCtx_infs {E n : Node} {pc : Pc} {m : Mark} (h : InFS exCtx E n pc m) : E = 0 := by
  induction h with
  | flow _ _ ih => exact ih
  | callIn _ _ ih => exact ih
  | ret _ _ _ _ _ ih => exact ih
  | single hr hσ _ _ _ _ _ | joined hr hσ _ _ _ _ _ _ _ =>
    simp only [exCtx] at hσ
    split at hσ
    · next h => exact exCtx_ptreach hr h.1
    · exact absurd hσ List.not_mem_nil

end FlowSensitiveLemmas

/-- The context condition `CtxOkFS` in `fs_sound` cannot be dropped: an engine
fact in callee `2` under the context passed from root `0` is not in the set of
root `1`, although root `1` reaches the same point. Per-root sets of 3* are
precise per root precisely because callee facts are attributed only to roots
that pass their context. -/
theorem fs_ctx_needed :
    PE exCtx Sel.all 2 (some ⟨0, 1⟩) 0 (some ⟨0, 1⟩) ∧ 1 ∈ exCtx.roots ∧
    PtReach exCtx 1 2 0 ∧ ¬ InFS exCtx 1 2 0 1 := by
  refine ⟨?_, by simp [exCtx], ?_, fun h => absurd (exCtx_infs h) (by decide)⟩
  · have h0 : PE exCtx Sel.all 0 none 0 none := PE.root (by simp [exCtx])
    have h0' : PE exCtx Sel.all 0 none 0 (some ⟨0, 1⟩) :=
      PE.genEmpty (σ := fsSrcSite) (c := []) (by simp [exCtx]) rfl (by simp [fsSrcSite])
        (by decide) (by simp [fsSrcSite]) rfl h0
    have h1 : PE exCtx Sel.all 0 none 1 (some ⟨0, 1⟩) := PE.intra h0' (by simp [exCtx]) rfl
    exact PE.callFact h1 (by simp [exCtx]) rfl rfl
  · have r0 : PtReach exCtx 1 1 0 := PtReach.root (by simp [exCtx])
    have r1 : PtReach exCtx 1 1 1 := PtReach.succ r0 (by simp [exCtx])
    exact PtReach.call r1 (by simp [exCtx])

/-! ## 2. Findings select their sinks -/

/-- Every engine finding, under any selection, is at a sink that option 3*
selects. So restricting the full scan to 3*-applicable sinks loses no
finding. -/
theorem fs_fires_applicable {p : Program} {sel : Sel} {n : Node} {pc : Pc} {σ : ESite}
    (h : Fires p sel n pc σ) : ApplicableFS p n pc σ := by
  obtain ⟨hσ, _, _, c, hc, hh⟩ := h
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
    obtain ⟨d0, hpe⟩ := hall f hf
    obtain ⟨⟨E, _, hr, hctx⟩, hsound⟩ := fs_sound hpe
    exact ⟨E, hr, hsound E (ptreach_root hr) hr hctx⟩

/-! ## 3. Refinement of the flow-insensitive scan -/

/-- Every flow-sensitive mark is a flow-insensitive mark of the same root, so
option 3* computes subsets of the default mode's sets. -/
theorem fs_refines_fi {p : Program} (hw : FSWF p) {E n : Node} {pc : Pc} {m : Mark}
    (h : InFS p E n pc m) : InS p E m := by
  induction h with
  | flow _ _ ih => exact ih
  | callIn _ _ ih => exact ih
  | ret _ _ _ _ _ ih => exact ih
  | @single E n pc σ c g hr hσ hc hlen _ hg ih =>
    exact InS.single (ptreach_root hr) (ptreach_reaches hw hr)
      (nodeSites_mem (hw.sites_pc n pc σ hσ) hσ) hc hlen ih hg
  | @joined E n pc σ c g hr hσ hc hlen w hw' _ hg ih =>
    exact InS.joined (ptreach_root hr) (ptreach_reaches hw hr)
      (nodeSites_mem (hw.sites_pc n pc σ hσ) hσ) hc hlen w
      (fun m hm => ptreach_root (hw' m hm)) (fun m hm => ptreach_reaches hw (hw' m hm)) ih hg

/-- Option 3* never selects a site that the default flow-insensitive mode does
not select. -/
theorem applicableFS_implies_applicable {p : Program} (hw : FSWF p) {n : Node} {pc : Pc}
    {σ : ESite} (h : ApplicableFS p n pc σ) : Applicable p n pc σ := by
  obtain ⟨hσ, c, hc, hsat⟩ := h
  refine ⟨hσ, c, hc, ?_⟩
  rcases hsat with ⟨hlen, E, hr, hall⟩ | ⟨hlen, hall⟩
  · exact Or.inl ⟨hlen, E, ptreach_root hr, ptreach_reaches hw hr,
      fun m hm => fs_refines_fi hw (hall m hm)⟩
  · refine Or.inr ⟨hlen, fun m hm => ?_⟩
    obtain ⟨E, hr, hin⟩ := hall m hm
    exact ⟨E, ptreach_root hr, ptreach_reaches hw hr, fs_refines_fi hw hin⟩

/-! ## 4. Strictness: sink before source -/

/-- One method (node `0`, the root): `pc 0` is the sink, `pc 1` the source,
edge `0 → 1`, no loop. -/
def exOrder : Program where
  nodes := [0]
  roots := [0]
  pcs := fun _ => [0, 1]
  succ := fun n pc => if n = 0 ∧ pc = 0 then [1] else []
  exits := fun _ => [1]
  sites := fun n pc =>
    if n = 0 ∧ pc = 0 then [fsSinkSite] else if n = 0 ∧ pc = 1 then [fsSrcSite] else []
  calls := fun _ _ => []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false

namespace FlowSensitiveLemmas

theorem sink_cond : fsSinkSite.abstract.cond = [[1]] := by decide

theorem sink_gens : fsSinkSite.abstract.gens = [] := rfl

theorem src_cond : fsSrcSite.abstract.cond = [[]] := by decide

theorem src_gens : fsSrcSite.abstract.gens = [1] := rfl

theorem exOrder_wf : FSWF exOrder := by
  constructor
  · intro n pc c hc; exact absurd hc List.not_mem_nil
  · intro n pc σ hσ
    simp only [exOrder] at hσ ⊢
    split at hσ
    · next h => rw [h.2]; simp
    · split at hσ
      · next h => rw [h.2]; simp
      · exact absurd hσ List.not_mem_nil

/-- In `exOrder`, every flow-sensitive mark lives at `pc 1`. -/
theorem exOrder_inv {E n : Node} {pc : Pc} {m : Mark} (h : InFS exOrder E n pc m) : pc = 1 := by
  induction h with
  | @flow E n pc pc' m _ hs _ =>
    simp only [exOrder] at hs
    split at hs
    · simpa using hs
    · exact absurd hs List.not_mem_nil
  | callIn _ hc _ => exact absurd hc List.not_mem_nil
  | ret _ hc _ _ _ _ => exact absurd hc List.not_mem_nil
  | single _ hσ _ _ _ hg _ | joined _ hσ _ _ _ _ _ hg _ =>
    simp only [exOrder] at hσ
    split at hσ
    · simp only [List.mem_singleton] at hσ; subst hσ; rw [sink_gens] at hg
      exact absurd hg List.not_mem_nil
    · split at hσ
      · next h => exact h.2
      · exact absurd hσ List.not_mem_nil

end FlowSensitiveLemmas

/-- Option 3* is strictly finer than the default mode: when the sink precedes
the source in the CFG of the same method (no loop), the default mode selects
the sink but option 3* does not. -/
theorem fs_strict : Applicable exOrder 0 0 fsSinkSite ∧ ¬ ApplicableFS exOrder 0 0 fsSinkSite := by
  constructor
  · refine ⟨by simp [exOrder], [1], by rw [sink_cond]; simp, Or.inl ⟨by decide, 0, by simp [exOrder],
      Reaches.refl 0, ?_⟩⟩
    intro m hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact InS.single (E := 0) (n := 0) (pc := 1) (σ := fsSrcSite) (c := [])
      (by simp [exOrder]) (Reaches.refl 0) (nodeSites_mem (by simp [exOrder]) (by simp [exOrder]))
      (by rw [src_cond]; simp) (by decide)
      (fun _ h => absurd h List.not_mem_nil) (by rw [src_gens]; simp)
  · rintro ⟨_, c, hc, hsat⟩
    rw [sink_cond] at hc
    simp only [List.mem_singleton] at hc
    subst hc
    rcases hsat with ⟨_, E, _, hall⟩ | ⟨hlen, _⟩
    · exact absurd (exOrder_inv (hall 1 (by simp))) (by decide)
    · exact absurd hlen (by decide)

/-! ## 5. The "statement order" reading is unsound -/

/-- The linear ("statement order") reading of option 3*: `InFS` where marks
move along an intra-procedural edge `pc → pc'` only when `pc < pc'`, i.e. back
edges are ignored and the method is resolved in one ordered pass. -/
inductive InLin (p : Program) : Node → Node → Pc → Mark → Prop
  | flow {E n : Node} {pc pc' : Pc} {m : Mark} :
      InLin p E n pc m → pc' ∈ p.succ n pc → pc < pc' → InLin p E n pc' m
  | callIn {E n c : Node} {pc : Pc} {m : Mark} :
      InLin p E n pc m → c ∈ p.calls n pc → InLin p E c 0 m
  | ret {E n c : Node} {pc pc' ex : Pc} {m : Mark} :
      PtReach p E n pc → c ∈ p.calls n pc → InLin p E c ex m → ex ∈ p.exits c →
      pc' ∈ p.succ n pc → pc < pc' → InLin p E n pc' m
  | single {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      PtReach p E n pc → σ ∈ p.sites n pc → c ∈ σ.abstract.cond → c.length ≤ 1 →
      (∀ m, m ∈ c → InLin p E n pc m) → g ∈ σ.abstract.gens → InLin p E n pc g
  | joined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      PtReach p E n pc → σ ∈ p.sites n pc → c ∈ σ.abstract.cond → 2 ≤ c.length →
      (w : Mark → Node) → (∀ m, m ∈ c → PtReach p (w m) n pc) →
      (∀ m, m ∈ c → InLin p (w m) n pc m) → g ∈ σ.abstract.gens → InLin p E n pc g

/-- Cube satisfiability in the linear reading. -/
def CubeSatLin (p : Program) (n : Node) (pc : Pc) (c : Cube) : Prop :=
  (c.length ≤ 1 ∧ ∃ E, PtReach p E n pc ∧ ∀ m, m ∈ c → InLin p E n pc m) ∨
  (2 ≤ c.length ∧ ∀ m, m ∈ c → ∃ E, PtReach p E n pc ∧ InLin p E n pc m)

/-- Site selection in the linear reading. -/
def ApplicableLin (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧ CubeSatLin p n pc c

/-- One method with a loop: `0 → 1 → 2 → 1`. The sink is at `pc 1`, the source
at `pc 2`, and the back edge `2 → 1` carries the source's mark to the sink. -/
def exLoop : Program where
  nodes := [0]
  roots := [0]
  pcs := fun _ => [0, 1, 2]
  succ := fun n pc =>
    if n = 0 ∧ pc = 0 then [1] else if n = 0 ∧ pc = 1 then [2]
    else if n = 0 ∧ pc = 2 then [1] else []
  exits := fun _ => [2]
  sites := fun n pc =>
    if n = 0 ∧ pc = 1 then [fsSinkSite] else if n = 0 ∧ pc = 2 then [fsSrcSite] else []
  calls := fun _ _ => []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false

namespace FlowSensitiveLemmas

/-- In `exLoop`, every linear-reading mark lives at `pc 2`. -/
theorem exLoop_lin_inv {E n : Node} {pc : Pc} {m : Mark} (h : InLin exLoop E n pc m) :
    pc = 2 := by
  induction h with
  | @flow E n pc pc' m _ hs hlt ih =>
    subst ih
    simp only [exLoop] at hs
    split at hs
    · next h => exact absurd h.2 (by decide)
    · split at hs
      · next h => exact absurd h.2 (by decide)
      · split at hs
        · simp only [List.mem_singleton] at hs; subst hs; exact absurd hlt (by decide)
        · exact absurd hs List.not_mem_nil
  | callIn _ hc _ => exact absurd hc List.not_mem_nil
  | ret _ hc _ _ _ _ _ => exact absurd hc List.not_mem_nil
  | single _ hσ _ _ _ hg _ | joined _ hσ _ _ _ _ _ hg _ =>
    simp only [exLoop] at hσ
    split at hσ
    · simp only [List.mem_singleton] at hσ; subst hσ; rw [sink_gens] at hg
      exact absurd hg List.not_mem_nil
    · split at hσ
      · next h => exact h.2
      · exact absurd hσ List.not_mem_nil

end FlowSensitiveLemmas

/-- The "statement order" reading of option 3* is unsound: on a loop whose
back edge carries a source's mark to an earlier sink, the engine reports the
finding but the linear reading does not select the sink. Option 3* must be
computed as a fixpoint over the CFG, not as one pass in statement order. -/
theorem linear_order_unsound :
    Fires exLoop Sel.all 0 1 fsSinkSite ∧ ¬ ApplicableLin exLoop 0 1 fsSinkSite := by
  constructor
  · have h0 : PE exLoop Sel.all 0 none 0 none := PE.root (by simp [exLoop])
    have h1 : PE exLoop Sel.all 0 none 1 none := PE.intra h0 (by simp [exLoop]) rfl
    have h2 : PE exLoop Sel.all 0 none 2 none := PE.intra h1 (by simp [exLoop]) rfl
    have h2' : PE exLoop Sel.all 0 none 2 (some ⟨0, 1⟩) :=
      PE.genEmpty (σ := fsSrcSite) (c := []) (by simp [exLoop]) rfl (by simp [fsSrcSite])
        (by decide) (by simp [fsSrcSite]) rfl h2
    have h1' : PE exLoop Sel.all 0 none 1 (some ⟨0, 1⟩) := PE.intra h2' (by simp [exLoop]) rfl
    refine ⟨by simp [exLoop], rfl, rfl, [⟨⟨0, 1⟩, false⟩], by simp [fsSinkSite], ?_⟩
    exact Or.inr (Or.inl ⟨⟨0, 1⟩, by decide, none, h1'⟩)
  · rintro ⟨_, c, hc, hsat⟩
    rw [sink_cond] at hc
    simp only [List.mem_singleton] at hc
    subst hc
    rcases hsat with ⟨_, E, _, hall⟩ | ⟨hlen, _⟩
    · exact absurd (exLoop_lin_inv (hall 1 (by simp))) (by decide)
    · exact absurd hlen (by decide)

/-- On the same loop program, the fixpoint reading of option 3* does select
the sink (a corollary of `fs_fires_applicable`). -/
theorem exLoop_fs_applicable : ApplicableFS exLoop 0 1 fsSinkSite :=
  fs_fires_applicable linear_order_unsound.1

/-! ## 6. Cost: the number of (root, point) pairs -/

/-- An executable enumeration of the `(root, node, pc)` triples over which
option 3* keeps one mark set each. -/
def fsPoints (p : Program) : List (Node × Node × Pc) :=
  p.roots.flatMap fun E => p.nodes.flatMap fun n => (p.pcs n).map fun pc => (E, n, pc)

namespace FlowSensitiveLemmas

theorem sum_const_map {α : Type} (l : List α) (k : Nat) :
    (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ l ih => simp [List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

end FlowSensitiveLemmas

/-- The state of option 3* is one mark set per `(root, node, pc)` triple, and
there are `|roots| · Σ_n |pcs n|` of them, against `|roots|` sets for the
default mode. -/
theorem fsPoints_length (p : Program) :
    (fsPoints p).length = p.roots.length * (p.nodes.map fun n => (p.pcs n).length).sum := by
  unfold fsPoints
  rw [List.length_flatMap]
  simp only [List.length_flatMap, List.length_map]
  exact sum_const_map _ _

/-- `fsPoints` enumerates exactly the listed triples. -/
theorem mem_fsPoints (p : Program) (E n : Node) (pc : Pc) :
    (E, n, pc) ∈ fsPoints p ↔ E ∈ p.roots ∧ n ∈ p.nodes ∧ pc ∈ p.pcs n := by
  unfold fsPoints
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨_, hE, _, hn, _, hpc, rfl, rfl, rfl⟩
    exact ⟨hE, hn, hpc⟩
  · rintro ⟨hE, hn, hpc⟩
    exact ⟨E, hE, n, hn, pc, hpc, rfl, rfl, rfl⟩

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

end MarkScan
