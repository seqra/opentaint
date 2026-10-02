import MarkScan.Basic

/-!
# Coarsening: running the mark-set scan on a smaller graph

`Basic` defines the mark-set semantics over analysis nodes, which are
`(method, method context)` pairs. The implementation does not run the scan on
that graph: on real projects the per-context graph explodes. It runs the scan
on a coarser graph whose nodes are methods (all contexts of a method merged,
their call edges and residual rule sites unioned), and it keys the final
selection by statement rather than by `(node, statement)`.

This module shows that both coarsenings are sound: they can only add
selections, never drop one.

* `Hom p q h hp` says that `q` is a coarsening of `p` along the node map `h`
  and the statement map `hp`.
* `Program.merge` is the executable context-merging construction, and
  `merge_hom` shows that it is a `Hom`.
* Under a `Hom`, reachability, mark sets, cube satisfaction, applicability and
  neededness all transfer from `p` to `q` (`reaches_hom`, `inS_hom`,
  `cubeSat_hom`, `applicable_hom`, `needed_hom`).
* Keying the selection by statement is also an over-approximation
  (`applicable_stmtApplicable`, `keyed_overapprox`), and both coarsenings
  compose (`coarse_keyed_overapprox`, `coarse_needed_overapprox`).
* `Example` exhibits the price. Merging two contexts of one method makes a
  sink applicable that no single context makes applicable. This is a loss of
  precision, not of soundness.

## Choice of the `Hom` hypotheses

The site condition is the strictest of the proposed forms: the *same* `ESite`
must appear at the image statement (`σ ∈ p.sites n pc → σ ∈ q.sites (h n) (hp
pc)`). This holds for "merge contexts of the same method" because the merged
node's residual sites at a statement are the union of the per-context residual
sites at that statement. Two contexts that fold a rule to different residuals
contribute two different `ESite`s, and both are kept. Because the site is kept
exactly, there is no `∃ σ'` to eliminate. The `joined` case of `InS` therefore
needs no choice. Its witness functions for `q` are just `h ∘ w` and `h ∘ wn`, and
`Applicable q` is stated about the same `σ`.

Call edges and statements are required pointwise (`calls`, `pcs`) rather than
on `callees`/`nodeSites`. The pointwise forms are what the merge construction
gives directly, and the `callees`/`nodeSites` forms follow from them
(`CoarseningLemmas.hom_callees`, `CoarseningLemmas.hom_nodeSites`).

Two fields are about the v2 model.
* `method`: two fine nodes of one method map to coarse nodes of one method.
  The joined cases of `InS` and `CubeSat` range over every node of the
  method, so this is what lets the witness nodes `wn` be mapped through `h`.
  Preserving equality is weaker than asking for a function on method ids, and
  it is exactly what the proofs use.
* `cleanerAtoms`: the recorded cleaner atoms of `(n, pc)` are recorded at the
  image `(h n, hp pc)`. `Needed.cleanerAtom` seeds the needed set with them.
-/

namespace MarkScan

/-! ## 1. Homomorphisms of programs -/

/-- `q` is a coarsening of `p` along `h : Node → Node` and `hp : Pc → Pc`.
Roots, statements, call edges, residual sites and cleaner atoms of `p` all
have images in `q`, and nodes of one method map to nodes of one method. The
engine-only fields (`succ`, `exits`, `mapIn`, `mapOut`, `kills`) are
unconstrained, because the mark-set semantics never reads them. -/
structure Hom (p q : Program) (h : Node → Node) (hp : Pc → Pc) : Prop where
  roots : ∀ E, E ∈ p.roots → h E ∈ q.roots
  pcs : ∀ n pc, pc ∈ p.pcs n → hp pc ∈ q.pcs (h n)
  calls : ∀ n pc c, c ∈ p.calls n pc → h c ∈ q.calls (h n) (hp pc)
  sites : ∀ n pc σ, σ ∈ p.sites n pc → σ ∈ q.sites (h n) (hp pc)
  method : ∀ n n', p.method n = p.method n' → q.method (h n) = q.method (h n')
  cleanerAtoms : ∀ n pc m, m ∈ p.cleanerAtoms n pc → m ∈ q.cleanerAtoms (h n) (hp pc)

namespace CoarseningLemmas

theorem hom_callees {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {n c : Node} (hc : c ∈ p.callees n) :
    h c ∈ q.callees (h n) := by
  unfold Program.callees at *
  rw [List.mem_flatMap] at hc ⊢
  obtain ⟨pc, hpc, hcall⟩ := hc
  exact ⟨hp pc, H.pcs n pc hpc, H.calls n pc c hcall⟩

theorem hom_nodeSites {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {n : Node} {pc : Pc} {σ : ESite}
    (hs : (pc, σ) ∈ p.nodeSites n) : (hp pc, σ) ∈ q.nodeSites (h n) := by
  unfold Program.nodeSites at *
  rw [List.mem_flatMap] at hs ⊢
  obtain ⟨pc', hpc', hmem⟩ := hs
  rw [List.mem_map] at hmem
  obtain ⟨σ', hσ', heq⟩ := hmem
  cases heq
  exact ⟨hp pc, H.pcs n pc hpc', List.mem_map.mpr ⟨σ, H.sites n pc σ hσ', rfl⟩⟩

theorem nodeSites_sites {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (hs : (pc, σ) ∈ p.nodeSites n) : pc ∈ p.pcs n ∧ σ ∈ p.sites n pc := by
  unfold Program.nodeSites at hs
  rw [List.mem_flatMap] at hs
  obtain ⟨pc', hpc', hmem⟩ := hs
  rw [List.mem_map] at hmem
  obtain ⟨σ', hσ', heq⟩ := hmem
  cases heq
  exact ⟨hpc', hσ'⟩

/-- Reachability stays inside any set closed under `callees`. -/
theorem reaches_closed {p : Program} {S : List Node}
    (hcl : ∀ x, x ∈ S → ∀ y, y ∈ p.callees x → y ∈ S) :
    ∀ {a b}, Reaches p a b → a ∈ S → b ∈ S := by
  intro a b hr
  induction hr with
  | refl _ => exact id
  | step hbc _ ih => exact fun ha => ih (hcl _ ha _ hbc)

end CoarseningLemmas

open CoarseningLemmas

/-! ## 2. The context-merging construction -/

/-- Merges the contexts of each method. `h` maps a node to its method's
coarse node, and `fib m` lists the fine nodes merged into `m` (the contexts of
method `m`). Statements, call edges (mapped through `h`) and residual sites
are unioned over the fiber, and statements are not renumbered (`hp = id`).
The merged node keeps the method id of its fiber (read off the first member;
`merge_hom` assumes the fiber is one method), and its cleaner atoms are the
union over the fiber. The engine-only fields are filled conservatively (union,
first mapping, kill only if every context kills), but the mark-set semantics
does not read them. -/
def Program.merge (p : Program) (h : Node → Node) (fib : Node → List Node) : Program where
  nodes := (p.nodes.map h).eraseDups
  roots := (p.roots.map h).eraseDups
  pcs m := (fib m).flatMap p.pcs
  succ m pc := (fib m).flatMap (p.succ · pc)
  exits m := (fib m).flatMap p.exits
  sites m pc := (fib m).flatMap (p.sites · pc)
  calls m pc := (fib m).flatMap fun n => (p.calls n pc).map h
  mapIn m pc b := (fib m).findSome? fun n => p.mapIn n pc b
  mapOut m pc b := (fib m).findSome? fun n => p.mapOut n pc b
  kills m pc f := (fib m).all fun n => p.kills n pc f
  method m := match fib m with
    | [] => m
    | n :: _ => p.method n
  cleanerAtoms m pc := (fib m).flatMap (p.cleanerAtoms · pc)

namespace CoarseningLemmas

/-- In a method-homogeneous fiber, the merged node carries the method of any
of its members. -/
theorem merge_method (p : Program) (h : Node → Node) (fib : Node → List Node)
    (hfibM : ∀ m n n', n ∈ fib m → n' ∈ fib m → p.method n = p.method n')
    {m n : Node} (hn : n ∈ fib m) : (p.merge h fib).method m = p.method n := by
  simp only [Program.merge]
  cases hf : fib m with
  | nil => rw [hf] at hn; cases hn
  | cons n0 rest =>
    exact hfibM m n0 n (by rw [hf]; exact List.mem_cons_self) hn

end CoarseningLemmas

/-- The executable context-merging construction satisfies `Hom`, provided that
every node lies in the fiber of its own image and every fiber consists of
nodes of one method (it merges contexts of a method, never two methods). So
the `Hom` hypotheses are exactly what "merge contexts, union edges, residuals
and cleaner atoms" provides. In v2 the fiber condition `hfibM` is new: it is
what makes the merged node's method well defined. -/
theorem merge_hom (p : Program) (h : Node → Node) (fib : Node → List Node)
    (hfib : ∀ n, n ∈ fib (h n))
    (hfibM : ∀ m n n', n ∈ fib m → n' ∈ fib m → p.method n = p.method n') :
    Hom p (p.merge h fib) h id where
  roots E hE := by
    simp only [Program.merge]
    rw [List.mem_eraseDups]
    exact List.mem_map_of_mem hE
  pcs n pc hpc := List.mem_flatMap.mpr ⟨n, hfib n, hpc⟩
  calls n pc c hc :=
    List.mem_flatMap.mpr ⟨n, hfib n, List.mem_map_of_mem hc⟩
  sites n pc σ hσ := List.mem_flatMap.mpr ⟨n, hfib n, hσ⟩
  method n n' he := by
    rw [merge_method p h fib hfibM (hfib n), merge_method p h fib hfibM (hfib n')]
    exact he
  cleanerAtoms n pc m hm := List.mem_flatMap.mpr ⟨n, hfib n, hm⟩

/-! ## 3. Transfer along a homomorphism -/

/-- Coarsening preserves call-graph reachability: every fine path has an image
path in the coarse graph. -/
theorem reaches_hom {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {a b : Node} (hr : Reaches p a b) : Reaches q (h a) (h b) := by
  induction hr with
  | refl n => exact .refl (h n)
  | step hbc _ ih => exact .step (hom_callees H hbc) ih

/-- Coarsening only grows mark sets. A mark in `S_E` of the fine graph is in
`S_{h E}` of the coarse graph. In the joined and sink-gen cases the coarse
witness roots are `h ∘ w` and the witness nodes `h ∘ wn` (they stay in the
method of `h n` by `Hom.method`), so no choice is needed. -/
theorem inS_hom {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {E : Node} {m : Mark} (hin : InS p E m) : InS q (h E) m := by
  induction hin with
  | single hE hR hs hc hl _ hg ih =>
    exact .single (H.roots _ hE) (reaches_hom H hR) (hom_nodeSites H hs) hc hl ih hg
  | joined hE hR hs hc hl w wn hw hwR hwm _ hg ih =>
    exact .joined (H.roots _ hE) (reaches_hom H hR) (hom_nodeSites H hs) hc hl
      (fun m => h (w m)) (fun m => h (wn m)) (fun m hm => H.roots _ (hw m hm))
      (fun m hm => reaches_hom H (hwR m hm)) (fun m hm => H.method _ _ (hwm m hm)) ih hg
  | sinkGen hE hR hs hk hc w wn hw hwR hwm _ hg ih =>
    exact .sinkGen (H.roots _ hE) (reaches_hom H hR) (hom_nodeSites H hs) hk hc
      (fun m => h (w m)) (fun m => h (wn m)) (fun m hm => H.roots _ (hw m hm))
      (fun m hm => reaches_hom H (hwR m hm)) (fun m hm => H.method _ _ (hwm m hm)) ih hg

/-- A cube satisfiable at a fine node is satisfiable at its coarse image. -/
theorem cubeSat_hom {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {n : Node} {c : Cube} (hc : CubeSat p n c) : CubeSat q (h n) c := by
  rcases hc with ⟨hl, E, hE, hR, hin⟩ | ⟨hl, hall⟩
  · exact .inl ⟨hl, h E, H.roots _ hE, reaches_hom H hR, fun m hm => inS_hom H (hin m hm)⟩
  · refine .inr ⟨hl, fun m hm => ?_⟩
    obtain ⟨E, n', hE, hR, hmeth, hin⟩ := hall m hm
    exact ⟨h E, h n', H.roots _ hE, reaches_hom H hR, H.method _ _ hmeth, inS_hom H hin⟩

/-- A site applicable at a fine `(n, pc)` is applicable at its coarse image
`(h n, hp pc)`. Selecting what the coarse scan finds applicable therefore
never drops a fine-applicable site. -/
theorem applicable_hom {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {n : Node} {pc : Pc} {σ : ESite} (ha : Applicable p n pc σ) :
    Applicable q (h n) (hp pc) σ := by
  obtain ⟨hσ, c, hc, hsat⟩ := ha
  exact ⟨H.sites n pc σ hσ, c, hc, cubeSat_hom H hsat⟩

/-- Coarsening only grows the set of needed marks, so the coarse `AssignMark`
filter never drops an action that the fine scan would keep. The v2 seeds
transfer too: cleaner atoms by `Hom.cleanerAtoms`, pass-through atoms by
`applicable_hom`. -/
theorem needed_hom {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {m : Mark} (hn : Needed p m) : Needed q m := by
  induction hn with
  | sinkAtom ha hk hm => exact .sinkAtom (applicable_hom H ha) hk hm
  | sinkGen ha hk hm => exact .sinkGen (applicable_hom H ha) hk hm
  | trans ha hg _ hm ih => exact .trans (applicable_hom H ha) hg ih hm
  | cleanerAtom hm => exact .cleanerAtom (H.cleanerAtoms _ _ _ hm)
  | passAtom ha hk hm => exact .passAtom (applicable_hom H ha) hk hm

/-! ## 4. Statement-keyed selection -/

/-- The site `σ` is applicable at statement key `s` if it is applicable at
some `(node, pc)` whose statement is `s`. So the key merges every context of
the statement. -/
def stmtApplicable (p : Program) (stmtOf : Node → Pc → Nat) (s : Nat) (σ : ESite) : Prop :=
  ∃ n pc, stmtOf n pc = s ∧ Applicable p n pc σ

/-- A union at the key level over-approximates the per-node relation: a site
applicable at `(n, pc)` is statement-applicable at `stmtOf n pc`. -/
theorem applicable_stmtApplicable {p : Program} {stmtOf : Node → Pc → Nat}
    {n : Node} {pc : Pc} {σ : ESite} (ha : Applicable p n pc σ) :
    stmtApplicable p stmtOf (stmtOf n pc) σ :=
  ⟨n, pc, rfl, ha⟩

/-- A Bool selection keyed by statement that covers `stmtApplicable` also
covers `Applicable` pointwise, once it is read back as
`fun n pc σ => appK (stmtOf n pc) σ`. Theorems that assume `app ⊇ Applicable`
therefore still apply to the keyed selection. -/
theorem keyed_overapprox {p : Program} {stmtOf : Node → Pc → Nat}
    {appK : Nat → ESite → Bool}
    (hK : ∀ s σ, stmtApplicable p stmtOf s σ → appK s σ = true) :
    ∀ n pc σ, Applicable p n pc σ → appK (stmtOf n pc) σ = true :=
  fun _ _ _ ha => hK _ _ (applicable_stmtApplicable ha)

/-- Both coarsenings compose. Suppose the scan runs on the coarse graph `q`
and keys its result by statement. Then pulling the selection back to fine
nodes, as `fun n pc σ => appK (stmtOf (h n) (hp pc)) σ`, over-approximates
fine applicability. -/
theorem coarse_keyed_overapprox {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {stmtOf : Node → Pc → Nat} {appK : Nat → ESite → Bool}
    (hK : ∀ s σ, stmtApplicable q stmtOf s σ → appK s σ = true) :
    ∀ n pc σ, Applicable p n pc σ → appK (stmtOf (h n) (hp pc)) σ = true :=
  fun _ _ _ ha => keyed_overapprox hK _ _ _ (applicable_hom H ha)

/-- A `need` filter that covers the coarse `Needed` also covers the fine
`Needed`. -/
theorem coarse_needed_overapprox {p q : Program} {h : Node → Node} {hp : Pc → Pc}
    (H : Hom p q h hp) {need : Mark → Bool}
    (hN : ∀ m, Needed q m → need m = true) :
    ∀ m, Needed p m → need m = true :=
  fun m hn => hN m (needed_hom H hn)

/-! ## 5. Coarsening loses precision: a concrete witness

Method `M` has two contexts: node `3` is reached only from root `1`, and node
`4` only from root `2`. Root `2` has a source that generates mark `7`. Context
`3` calls node `5`, which holds a sink on mark `7`. Context `4` calls nothing.
In the fine graph the only root that reaches `5` is `1`, and `S_1 = ∅`, so the
sink is not applicable. Merging `3` and `4` into one node adds the coarse path
`2 → M → 5`, which carries mark `7`, and the sink becomes applicable. -/

namespace CoarseningExample

def srcSite : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 7⟩], copies := [] }

def sinkSite : ESite :=
  { rule := 1, kind := .sink, cond := [[⟨⟨0, 7⟩, false⟩]], assigns := [], copies := [] }

theorem sinkSite_cond : sinkSite.abstract.cond = [[7]] := rfl

def fine : Program where
  nodes := [1, 2, 3, 4, 5]
  roots := [1, 2]
  pcs _ := [0]
  succ _ _ := []
  exits _ := [0]
  sites n pc := if n = 2 ∧ pc = 0 then [srcSite] else if n = 5 ∧ pc = 0 then [sinkSite] else []
  calls n pc :=
    if pc = 0 then (if n = 1 then [3] else if n = 2 then [4] else if n = 3 then [5] else [])
    else []
  mapIn _ _ _ := none
  mapOut _ _ _ := none
  kills _ _ _ := false
  method n := if n = 4 then 3 else n
  cleanerAtoms _ _ := []

/-- Contexts `3` and `4` of method `M` both map to coarse node `3`. -/
def hM (n : Node) : Node := if n = 4 then 3 else n

def fibM (m : Node) : List Node := if m = 3 then [3, 4] else [m]

theorem hM_fib (n : Node) : n ∈ fibM (hM n) := by
  unfold hM fibM
  by_cases h4 : n = 4
  · subst h4; decide
  · rw [if_neg h4]
    by_cases h3 : n = 3
    · subst h3; decide
    · rw [if_neg h3]; exact List.mem_singleton_self n

def coarse : Program := fine.merge hM fibM

theorem fibM_method (m n n' : Node) (hn : n ∈ fibM m) (hn' : n' ∈ fibM m) :
    fine.method n = fine.method n' := by
  unfold fibM at hn hn'
  by_cases h3 : m = 3
  · rw [if_pos h3] at hn hn'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn hn'
    rcases hn with rfl | rfl <;> rcases hn' with rfl | rfl <;> decide
  · rw [if_neg h3] at hn hn'
    rw [List.mem_singleton.1 hn, List.mem_singleton.1 hn']

theorem coarse_hom : Hom fine coarse hM id := merge_hom fine hM fibM hM_fib fibM_method

theorem fine_callees (x : Node) :
    fine.callees x = if x = 1 then [3] else if x = 2 then [4] else if x = 3 then [5] else [] := by
  simp only [Program.callees, fine, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_true]

theorem fine_reach_from_1 {b : Node} (hr : Reaches fine 1 b) : b ∈ [1, 3, 5] := by
  refine reaches_closed (fun x hx y hy => ?_) hr (by decide)
  rw [fine_callees] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simp at hy; subst hy; decide
  · simp at hy; subst hy; decide
  · simp at hy

theorem fine_reach_from_2 {b : Node} (hr : Reaches fine 2 b) : b ∈ [2, 4] := by
  refine reaches_closed (fun x hx y hy => ?_) hr (by decide)
  rw [fine_callees] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp at hy; subst hy; decide
  · simp at hy

theorem fine_gens_from_1 {n : Node} {pc : Pc} {σ : ESite} {g : Mark}
    (hn : n ∈ [1, 3, 5]) (hs : (pc, σ) ∈ fine.nodeSites n) (hg : g ∈ σ.abstract.gens) :
    False := by
  have hσ := (nodeSites_sites hs).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · simp [fine] at hσ
  · simp [fine] at hσ
  · simp [fine] at hσ
    obtain ⟨_, rfl⟩ := hσ
    simp [ESite.abstract, sinkSite] at hg

theorem fine_not_inS_1_7 : ¬ InS fine 1 7 := by
  intro hin
  cases hin with
  | single _ hR hs _ _ _ hg => exact fine_gens_from_1 (fine_reach_from_1 hR) hs hg
  | joined _ hR hs _ _ _ _ _ _ _ _ hg => exact fine_gens_from_1 (fine_reach_from_1 hR) hs hg
  | sinkGen _ hR hs _ _ _ _ _ _ _ _ hg => exact fine_gens_from_1 (fine_reach_from_1 hR) hs hg

/-- In the per-context graph the sink at node `5` is not applicable: the only
root that reaches it (`1`) never carries mark `7`. -/
theorem fine_not_applicable : ¬ Applicable fine 5 0 sinkSite := by
  rintro ⟨_, c, hc, hsat⟩
  rw [sinkSite_cond] at hc
  have hc' : c = [7] := List.mem_singleton.mp hc
  subst hc'
  rcases hsat with ⟨_, E, hE, hR, hin⟩ | ⟨hl, _⟩
  · simp only [fine, List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl
    · exact fine_not_inS_1_7 (hin 7 (List.mem_singleton_self 7))
    · have := fine_reach_from_2 hR; simp at this
  · simp at hl

theorem coarse_inS_2_7 : InS coarse 2 7 := by
  refine InS.single (n := 2) (pc := 0) (σ := srcSite) (c := []) ?_ (.refl 2) ?_ ?_ ?_ ?_ ?_
  · decide
  · simp [coarse, Program.merge, Program.nodeSites, fibM, fine]
  · simp [ESite.abstract, srcSite, ECube.positive]
  · decide
  · intro m hm; simp at hm
  · simp [ESite.abstract, srcSite]

theorem coarse_reach_2_5 : Reaches coarse 2 5 := by
  refine .step (b := 3) ?_ (.step (b := 5) ?_ (.refl 5))
  · simp [coarse, Program.merge, Program.callees, fibM, fine, hM]
  · simp [coarse, Program.merge, Program.callees, fibM, fine, hM]

/-- After merging the contexts of `M`, the same sink is applicable: the coarse
graph has a path from root `2` (which carries mark `7`) through the merged
node to `5`. -/
theorem coarse_applicable : Applicable coarse 5 0 sinkSite := by
  refine ⟨?_, [7], ?_, .inl ⟨by decide, 2, by decide, coarse_reach_2_5, ?_⟩⟩
  · simp [coarse, Program.merge, fibM, fine]
  · rw [sinkSite_cond]; exact List.mem_singleton_self _
  · intro m hm
    simp at hm; subst hm
    exact coarse_inS_2_7

end CoarseningExample

open CoarseningExample in
/-- Coarsening is sound but not exact. The context-merged graph is a `Hom`
image of the fine graph, yet it selects a sink that the fine graph does not.
This is the precision paid for making the scan tractable. -/
theorem coarsening_loses_precision :
    Hom fine coarse hM id ∧ ¬ Applicable fine 5 0 sinkSite ∧
      Applicable coarse (hM 5) (id 0) sinkSite :=
  ⟨coarse_hom, fine_not_applicable, coarse_applicable⟩

end MarkScan

/-! ## Axiom audit
Run `./check.sh`: `AxiomAudit.lean` prints the axioms of every theorem. -/

