import MarkScan.Basic

/-!
# Option 4*: relaxed mark conditions, done correctly

Option 4* relaxes the mark conditions so that a rule counts as satisfiable
when *any* of the marks it mentions is present. Constant-true cubes are kept.

The spec's first reading of 4* replaced every cube by its atoms as
single-literal cubes, all evaluated per root. It claimed that the per-root
closure alone is then sound and the method-level union `U(n)` is never
needed. That claim is false (`naive_relax_unsound`). The joined result of a
multi-literal cube is a zero-context fact. It flows back into every caller of
`n`, including a root that passes none of the cube's marks.

Correct 4* (`InSRelax`, `ApplicableRelax`, `NeededRelax`):
* A multi-literal cube keeps its joined *placement*: its gens go to every root
  that reaches `n`. Only its *satisfaction test* is relaxed, to "some atom of
  the cube is in the method-level union `U(method n)`".
* A cube of at most one literal is unchanged. It is already "any mark".

This file proves the following.
* Correct 4* over-approximates the exact semantics (`inS_relax`,
  `applicable_relax`, `needed_relax`). These are the hypotheses of the
  end-to-end exactness theorem, so 4* selections stay exact.
* The naive reading is unsound (`naive_relax_unsound`).
* Correct 4* is strictly coarser than the exact semantics
  (`relax_strictly_coarser`).
* The relaxed joined test needs one mark, never a combination of marks
  (`joined_relax_single_mark` and its corollaries).
-/

namespace MarkScan

/-! ## 1. Correct 4* semantics -/

/-- The per-root mark sets `S_E` under correct 4*. `InSRelax p E m` means
`m ∈ S_E`. It is `InS` with the premise of a multi-literal cube weakened from
"every atom is in `U(method n)`" to "one atom `m0` is in `U(method n)`". The
witnesses are given for `m0` only. The gens still go to every root that
reaches `n`. -/
inductive InSRelax (p : Program) : Node → Mark → Prop
  | single {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → c.length ≤ 1 →
      (∀ m, m ∈ c → InSRelax p E m) →
      g ∈ σ.abstract.gens → InSRelax p E g
  | joined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g m0 : Mark} {w0 wn0 : Node} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond → 2 ≤ c.length → m0 ∈ c →
      w0 ∈ p.roots → Reaches p w0 wn0 → p.method wn0 = p.method n →
      InSRelax p w0 m0 →
      g ∈ σ.abstract.gens → InSRelax p E g
  | sinkGen {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n → σ.kind = .sink →
      c ∈ σ.abstract.cond → c.length ≤ 1 →
      (w wn : Mark → Node) →
      (∀ m, m ∈ c → w m ∈ p.roots) → (∀ m, m ∈ c → Reaches p (w m) (wn m)) →
      (∀ m, m ∈ c → p.method (wn m) = p.method n) →
      (∀ m, m ∈ c → InSRelax p (w m) m) →
      g ∈ σ.abstract.gens → InSRelax p E g
  | sinkGenJoined {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g m0 : Mark} {w0 wn0 : Node} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n → σ.kind = .sink →
      c ∈ σ.abstract.cond → 2 ≤ c.length → m0 ∈ c →
      w0 ∈ p.roots → Reaches p w0 wn0 → p.method wn0 = p.method n →
      InSRelax p w0 m0 →
      g ∈ σ.abstract.gens → InSRelax p E g

/-- `m ∈ U(method n)` under correct 4*: some root that reaches a node of the
same method as `n` has `m`. -/
def RelaxU (p : Program) (n : Node) (m : Mark) : Prop :=
  ∃ E n', E ∈ p.roots ∧ Reaches p E n' ∧ p.method n' = p.method n ∧ InSRelax p E m

/-- The cube `c` of a site at node `n` is satisfiable under correct 4*.
A cube of at most one literal is tested as in `CubeSat`. A cube of two or more
literals needs one of its atoms in `U(method n)`. -/
def CubeSatRelax (p : Program) (n : Node) (c : Cube) : Prop :=
  (c.length ≤ 1 ∧ ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ ∀ m, m ∈ c → InSRelax p E m) ∨
  (2 ≤ c.length ∧ ∃ m, m ∈ c ∧ RelaxU p n m)

/-- The site `σ` at `(n, pc)` is selected under correct 4*. -/
def ApplicableRelax (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond ∧ CubeSatRelax p n c

/-- The relevance pass under correct 4*: `Needed` with `ApplicableRelax` in
place of `Applicable`. -/
inductive NeededRelax (p : Program) : Mark → Prop
  | sinkAtom {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      ApplicableRelax p n pc σ → σ.kind = .sink → m ∈ σ.abstract.cond.atoms →
      NeededRelax p m
  | sinkGen {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      ApplicableRelax p n pc σ → σ.kind = .sink → m ∈ σ.abstract.gens → NeededRelax p m
  | trans {n : Node} {pc : Pc} {σ : ESite} {g m : Mark} :
      ApplicableRelax p n pc σ → g ∈ σ.abstract.gens → NeededRelax p g →
      m ∈ σ.abstract.cond.atoms → NeededRelax p m
  | cleanerAtom {n : Node} {pc : Pc} {m : Mark} :
      m ∈ p.cleanerAtoms n pc → NeededRelax p m
  | passAtom {n : Node} {pc : Pc} {σ : ESite} {m : Mark} :
      ApplicableRelax p n pc σ → σ.kind = .passThrough → m ∈ σ.abstract.cond.atoms →
      NeededRelax p m

/-! ## 2. Correct 4* over-approximates the exact semantics -/

namespace RelaxedLemmas

theorem exists_mem_of_two_le {c : Cube} (h : 2 ≤ c.length) : ∃ m, m ∈ c := by
  cases c with
  | nil => simp at h
  | cons m _ => exact ⟨m, List.mem_cons_self⟩

end RelaxedLemmas

open RelaxedLemmas in
/-- Every mark of the exact per-root set `S_E` is in the relaxed one. A
multi-literal cube that holds exactly holds relaxed: any of its atoms serves
as `m0`, with the exact witnesses for that atom. -/
theorem inS_relax {p : Program} {E : Node} {m : Mark} (h : InS p E m) : InSRelax p E m := by
  induction h with
  | single hE hR hs hc hl _ hg ih => exact .single hE hR hs hc hl ih hg
  | joined hE hR hs hc hl w wn hw hwr hwm _ hg ih =>
      obtain ⟨m0, hm0⟩ := exists_mem_of_two_le hl
      exact .joined hE hR hs hc hl hm0 (hw m0 hm0) (hwr m0 hm0) (hwm m0 hm0) (ih m0 hm0) hg
  | sinkGen hE hR hs hk hc w wn hw hwr hwm _ hg ih =>
      rcases Nat.lt_or_ge _ 2 with hl | hl
      · exact .sinkGen hE hR hs hk hc (Nat.le_of_lt_succ hl) w wn hw hwr hwm ih hg
      · obtain ⟨m0, hm0⟩ := exists_mem_of_two_le hl
        exact .sinkGenJoined hE hR hs hk hc hl hm0 (hw m0 hm0) (hwr m0 hm0) (hwm m0 hm0)
          (ih m0 hm0) hg

/-- An exactly satisfiable cube is satisfiable under correct 4*. -/
theorem cubeSat_relax {p : Program} {n : Node} {c : Cube} (h : CubeSat p n c) :
    CubeSatRelax p n c := by
  rcases h with ⟨hl, E, hE, hR, hin⟩ | ⟨hl, hall⟩
  · exact .inl ⟨hl, E, hE, hR, fun m hm => inS_relax (hin m hm)⟩
  · obtain ⟨m0, hm0⟩ := RelaxedLemmas.exists_mem_of_two_le hl
    obtain ⟨E, n', hE, hR, hmeth, hin⟩ := hall m0 hm0
    exact .inr ⟨hl, m0, hm0, E, n', hE, hR, hmeth, inS_relax hin⟩

/-- Every exactly applicable site is selected under correct 4*. With
`app` deciding `ApplicableRelax`, this discharges the hypothesis `hAppB` of the
end-to-end theorem `markset_exact`, so a 4* site selection reports exactly the
baseline findings. -/
theorem applicable_relax {p : Program} {n : Node} {pc : Pc} {σ : ESite}
    (h : Applicable p n pc σ) : ApplicableRelax p n pc σ :=
  let ⟨hs, c, hc, hsat⟩ := h
  ⟨hs, c, hc, cubeSat_relax hsat⟩

/-- Every exactly needed mark is needed under correct 4*. With `need`
deciding `NeededRelax`, this discharges the hypothesis `hNeed` of
`markset_exact`, so 4* action pruning stays exact too. -/
theorem needed_relax {p : Program} {m : Mark} (h : Needed p m) : NeededRelax p m := by
  induction h with
  | sinkAtom ha hk hm => exact .sinkAtom (applicable_relax ha) hk hm
  | sinkGen ha hk hm => exact .sinkGen (applicable_relax ha) hk hm
  | trans ha hg _ hm ih => exact .trans (applicable_relax ha) hg ih hm
  | cleanerAtom hm => exact .cleanerAtom hm
  | passAtom ha hk hm => exact .passAtom (applicable_relax ha) hk hm

/-! ## 3. The naive reading is unsound -/

/-- The spec's old reading of 4*: every cube is replaced by its atoms as
single-literal cubes (`Dnf.relax`), all are evaluated on `S_E`, and gens go
only to the root that satisfies the cube. There is no method-level union and
no joined placement. -/
inductive InSNaiveRelax (p : Program) : Node → Mark → Prop
  | mk {E n : Node} {pc : Pc} {σ : ESite} {c : Cube} {g : Mark} :
      E ∈ p.roots → Reaches p E n → (pc, σ) ∈ p.nodeSites n →
      c ∈ σ.abstract.cond.relax → (∀ m, m ∈ c → InSNaiveRelax p E m) →
      g ∈ σ.abstract.gens → InSNaiveRelax p E g

/-- Site selection under the naive reading. -/
def ApplicableNaiveRelax (p : Program) (n : Node) (pc : Pc) (σ : ESite) : Prop :=
  σ ∈ p.sites n pc ∧ ∃ c, c ∈ σ.abstract.cond.relax ∧
    ∃ E, E ∈ p.roots ∧ Reaches p E n ∧ ∀ m, m ∈ c → InSNaiveRelax p E m

namespace RelaxedLemmas

/-! Marks: `A = 1`, `B = 2`, `C = 3`. Nodes: roots `E1 = 1`, `E2 = 2`,
`E3 = 3`, all calling the shared node `n = 4`. -/

/-- `E1` puts mark `A` on base 0. -/
def srcA : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }
/-- `E2` puts mark `B` on base 1. -/
def srcB : ESite :=
  { rule := 1, kind := .source, cond := [[]], assigns := [⟨1, 2⟩], copies := [] }
/-- In `n`: when base 0 has `A` and base 1 has `B`, put `C` on the return
base 5. -/
def joinC : ESite :=
  { rule := 2, kind := .source, cond := [[⟨⟨0, 1⟩, false⟩, ⟨⟨1, 2⟩, false⟩]],
    assigns := [⟨5, 3⟩], copies := [] }
/-- In `E3`, after the call: a sink on `C` at base 5. -/
def sinkC : ESite :=
  { rule := 3, kind := .sink, cond := [[⟨⟨5, 3⟩, false⟩]], assigns := [], copies := [] }

/-- The reviewer's program. `E1` and `E2` call `n` at statement 0 with
`(0, A)` and `(1, B)`. `E3` calls `n` at statement 0 and passes nothing; its
statement 1 has the sink. Bases are mapped identically at calls and returns. -/
def cexR : Program where
  nodes := [1, 2, 3, 4]
  roots := [1, 2, 3]
  pcs := fun n => if n = 3 then [0, 1] else [0]
  succ := fun n pc => if n = 3 ∧ pc = 0 then [1] else []
  exits := fun n => if n = 3 then [1] else [0]
  sites := fun n pc =>
    if n = 1 ∧ pc = 0 then [srcA]
    else if n = 2 ∧ pc = 0 then [srcB]
    else if n = 4 ∧ pc = 0 then [joinC]
    else if n = 3 ∧ pc = 1 then [sinkC]
    else []
  calls := fun n pc => if pc = 0 ∧ (n = 1 ∨ n = 2 ∨ n = 3) then [4] else []
  mapIn := fun _ _ b => some b
  mapOut := fun _ _ b => some b
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

theorem cexR_zero_mem (n : Node) : 0 ∈ cexR.pcs n := by
  simp only [cexR]; split <;> simp

/-- `cexR` is well formed: calls, rule sites, exits and successors sit at
listed statements (`PcWF` of `EngineSoundness`, plus exits and successors),
and every node has the entry statement 0. -/
theorem cexR_wf :
    (∀ n pc c, c ∈ cexR.calls n pc → pc ∈ cexR.pcs n) ∧
    (∀ n pc, cexR.sites n pc ≠ [] → pc ∈ cexR.pcs n) ∧
    (∀ n ex, ex ∈ cexR.exits n → ex ∈ cexR.pcs n) ∧
    (∀ n pc pc', pc' ∈ cexR.succ n pc → pc ∈ cexR.pcs n ∧ pc' ∈ cexR.pcs n) ∧
    (∀ n, 0 ∈ cexR.pcs n) := by
  refine ⟨?_, ?_, ?_, ?_, cexR_zero_mem⟩
  · intro n pc c h
    simp only [cexR] at h
    split at h
    · next hc => rw [hc.1]; exact cexR_zero_mem n
    · cases h
  · intro n pc h
    simp only [cexR] at h ⊢
    split at h
    · next hc => rw [hc.2]; split <;> simp
    split at h
    · next hc => rw [hc.2]; split <;> simp
    split at h
    · next hc => rw [hc.2]; split <;> simp
    split at h
    · next hc => rw [hc.1, hc.2]; simp
    · exact absurd rfl h
  · intro n ex h
    simp only [cexR] at h ⊢
    split at h <;> simp_all
  · intro n pc pc' h
    simp only [cexR] at h ⊢
    split at h
    · next hc => simp_all
    · cases h

theorem cexR_sites4 : cexR.sites 4 0 = [joinC] := rfl
theorem cexR_sites3 : cexR.sites 3 1 = [sinkC] := rfl
theorem cexR_ns3 : cexR.nodeSites 3 = [(1, sinkC)] := rfl
theorem cexR_ns4 : cexR.nodeSites 4 = [(0, joinC)] := rfl
theorem cexR_ns1 : cexR.nodeSites 1 = [(0, srcA)] := rfl
theorem cexR_callees3 : cexR.callees 3 = [4] := by decide
theorem cexR_callees4 : cexR.callees 4 = [] := by decide
theorem cexR_callees1 : cexR.callees 1 = [4] := by decide

theorem joinC_pos : ECube.positive [⟨⟨0, 1⟩, false⟩, ⟨⟨1, 2⟩, false⟩] = [⟨0, 1⟩, ⟨1, 2⟩] := by
  decide
theorem sinkC_pos : ECube.positive [⟨⟨5, 3⟩, false⟩] = [⟨5, 3⟩] := by decide
theorem joinC_abs_cond : joinC.abstract.cond = [[1, 2]] := by decide
theorem joinC_relax : joinC.abstract.cond.relax = [[1], [2]] := by decide
theorem joinC_gens : joinC.abstract.gens = [3] := by decide
theorem sinkC_abs_cond : sinkC.abstract.cond = [[3]] := by decide
theorem sinkC_relax : sinkC.abstract.cond.relax = [[3]] := by decide
theorem sinkC_gens : sinkC.abstract.gens = [] := by decide
theorem srcA_abs_cond : srcA.abstract.cond = [[]] := by decide
theorem srcA_gens : srcA.abstract.gens = [1] := by decide

/-- The engine derives `C` at the exit of `n` in the zero context: the join
takes `(0, A)` from `n`'s context entered by `E1` and `(1, B)` from the one
entered by `E2`. -/
theorem cexR_pe_C : PE cexR Sel.all 4 none 0 (some ⟨5, 3⟩) := by
  have hE1 : PE cexR Sel.all 1 none 0 (some ⟨0, 1⟩) :=
    .genEmpty (σ := srcA) (c := []) (d := none) (by rw [show cexR.sites 1 0 = [srcA] from rfl]; simp)
      rfl (by simp [srcA]) (by decide) (by simp [srcA]) rfl (.root (by decide))
  have hE2 : PE cexR Sel.all 2 none 0 (some ⟨1, 2⟩) :=
    .genEmpty (σ := srcB) (c := []) (d := none) (by rw [show cexR.sites 2 0 = [srcB] from rfl]; simp)
      rfl (by simp [srcB]) (by decide) (by simp [srcB]) rfl (.root (by decide))
  have hA : PE cexR Sel.all 4 (some ⟨0, 1⟩) 0 (some ⟨0, 1⟩) :=
    .callFact (b := 0) hE1 (by decide) rfl rfl
  have hB : PE cexR Sel.all 4 (some ⟨1, 2⟩) 0 (some ⟨1, 2⟩) :=
    .callFact (b := 1) hE2 (by decide) rfl rfl
  have hZ : PE cexR Sel.all 4 none 0 none := .callZero (n := 3) (.root (by decide)) (by decide)
  refine .genJoined (σ := joinC) (c := [⟨⟨0, 1⟩, false⟩, ⟨⟨1, 2⟩, false⟩])
    (by rw [cexR_sites4]; simp) rfl (by simp [joinC]) (by rw [joinC_pos]; decide)
    (by simp [joinC]) rfl (fun _ => 4) (fun f => some f) (fun _ _ => rfl) ?_ hZ
  intro f hf
  rw [joinC_pos] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact hA
  · exact hB

/-- The sink in `E3` fires in the baseline: the zero-context `C` returns into
`E3` through the zero fact of its call. -/
theorem cexR_fires : Fires cexR Sel.all 3 1 sinkC := by
  have h : PE cexR Sel.all 3 none 1 (some ⟨5, 3⟩) :=
    .retZero (c := 4) (pc := 0) (ex := 0) (b := 5) (.root (by decide)) (by decide) cexR_pe_C
      (by decide) rfl (by decide)
  exact ⟨by rw [cexR_sites3]; simp, rfl, rfl, _, List.mem_singleton_self _,
    .inr (.inl ⟨_, sinkC_pos, none, h⟩)⟩

theorem cexR_reach3 {a b : Node} (h : Reaches cexR a b) : (a = 3 ∨ a = 4) → (b = 3 ∨ b = 4) := by
  induction h with
  | refl => exact id
  | step hb _ ih =>
      intro ha
      rcases ha with rfl | rfl
      · rw [cexR_callees3] at hb
        simp only [List.mem_singleton] at hb
        exact ih (.inr hb)
      · rw [cexR_callees4] at hb; cases hb

theorem cexR_reach4 {b : Node} (h : Reaches cexR 4 b) : b = 4 := by
  cases h with
  | refl => rfl
  | step hb _ => rw [cexR_callees4] at hb; cases hb

/-- Invariant of the naive reading: `S_E3` is empty. `E3` reaches only its
own sink (no gens) and `n`, whose relaxed cubes `[A]` and `[B]` need a mark
of `S_E3`. -/
theorem cexR_naive_E3_empty {E : Node} {m : Mark} (h : InSNaiveRelax cexR E m) : E ≠ 3 := by
  induction h with
  | mk _ hR hs hc _ hg ih =>
      intro hE
      subst hE
      rcases cexR_reach3 hR (.inl rfl) with rfl | rfl
      · rw [cexR_ns3] at hs
        simp only [List.mem_singleton, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [sinkC_gens] at hg; cases hg
      · rw [cexR_ns4] at hs
        simp only [List.mem_singleton, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        rw [joinC_relax] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ih 1 (by simp) rfl
        · exact ih 2 (by simp) rfl

theorem cexR_naive_not_app : ¬ ApplicableNaiveRelax cexR 3 1 sinkC := by
  rintro ⟨_, c, hc, E, hE, hR, hall⟩
  rw [sinkC_relax] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  have hE3 : E = 3 := by
    revert hE
    cases hR with
    | refl => intro _; rfl
    | step hb _ =>
        intro hE
        simp only [cexR, List.mem_cons, List.not_mem_nil, or_false] at hE
        rcases hE with rfl | rfl | rfl
        · rw [cexR_callees1] at hb; simp only [List.mem_singleton] at hb; subst hb
          rename_i h; exact absurd (cexR_reach4 h) (by decide)
        · rw [show cexR.callees 2 = [4] from by decide] at hb
          simp only [List.mem_singleton] at hb; subst hb
          rename_i h; exact absurd (cexR_reach4 h) (by decide)
        · rfl
  exact cexR_naive_E3_empty (hall 3 (by simp)) hE3

/-- Correct 4* does select the sink in `E3`: `C` joins into `S_E3` because
the joined placement of `n`'s cube reaches every root that calls `n`. -/
theorem cexR_relax_app : ApplicableRelax cexR 3 1 sinkC := by
  have hA : InSRelax cexR 1 1 :=
    .single (n := 1) (pc := 0) (σ := srcA) (c := []) (by decide) (.refl 1)
      (by rw [cexR_ns1]; simp) (by rw [srcA_abs_cond]; simp) (by decide) (by simp)
      (by rw [srcA_gens]; simp)
  have hC : InSRelax cexR 3 3 :=
    .joined (n := 4) (pc := 0) (σ := joinC) (c := [1, 2]) (m0 := 1) (w0 := 1) (wn0 := 4)
      (by decide) (.step (by rw [cexR_callees3]; simp) (.refl 4)) (by rw [cexR_ns4]; simp)
      (by rw [joinC_abs_cond]; simp) (by decide) (by simp) (by decide)
      (.step (by rw [cexR_callees1]; simp) (.refl 4)) rfl hA (by rw [joinC_gens]; simp)
  exact ⟨by rw [cexR_sites3]; simp, [3], by rw [sinkC_abs_cond]; simp,
    .inl ⟨by decide, 3, by decide, .refl 3, by simp [hC]⟩⟩

end RelaxedLemmas

open RelaxedLemmas in
/-- The spec's old reading of 4* is unsound. In `cexR` the baseline reports
the sink in `E3`, yet the naive per-root relaxation does not select it:
`S_E3` is empty, since `E3` passes neither `A` nor `B`. The joined result `C`
is a zero-context fact that returns into every caller of `n`. So the per-root
closure alone is not enough, and the joined placement (or `U`) is needed.
Correct 4* selects the sink (`cexR_relax_app`). `cexR` is well formed
(`cexR_wf`). -/
theorem naive_relax_unsound :
    Fires cexR Sel.all 3 1 sinkC ∧ ¬ ApplicableNaiveRelax cexR 3 1 sinkC ∧
      ApplicableRelax cexR 3 1 sinkC :=
  ⟨cexR_fires, cexR_naive_not_app, cexR_relax_app⟩

/-! ## 4. Correct 4* is strictly coarser -/

namespace RelaxedLemmas

/-- A source putting `A = 1` on base 0. -/
def srcP : ESite :=
  { rule := 0, kind := .source, cond := [[]], assigns := [⟨0, 1⟩], copies := [] }
/-- A sink that needs both `A` on base 0 and `B = 2` on base 1. -/
def sinkAB : ESite :=
  { rule := 1, kind := .sink, cond := [[⟨⟨0, 1⟩, false⟩, ⟨⟨1, 2⟩, false⟩]], assigns := [],
    copies := [] }

/-- One root, one statement, both sites. Nothing generates `B`. -/
def cexP : Program where
  nodes := [0]
  roots := [0]
  pcs := fun _ => [0]
  succ := fun _ _ => []
  exits := fun _ => [0]
  sites := fun _ _ => [srcP, sinkAB]
  calls := fun _ _ => []
  mapIn := fun _ _ _ => none
  mapOut := fun _ _ _ => none
  kills := fun _ _ _ => false
  method := id
  cleanerAtoms := fun _ _ => []

theorem cexP_ns (n : Node) : cexP.nodeSites n = [(0, srcP), (0, sinkAB)] := rfl
theorem srcP_abs_cond : srcP.abstract.cond = [[]] := by decide
theorem srcP_gens : srcP.abstract.gens = [1] := by decide
theorem sinkAB_abs_cond : sinkAB.abstract.cond = [[1, 2]] := by decide
theorem sinkAB_gens : sinkAB.abstract.gens = [] := by decide

theorem cexP_gen {n : Node} {pc : Pc} {σ : ESite} {g : Mark}
    (hs : (pc, σ) ∈ cexP.nodeSites n) (hg : g ∈ σ.abstract.gens) : g = 1 := by
  rw [cexP_ns] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hs
  rcases hs with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · rw [srcP_gens] at hg; simpa using hg
  · rw [sinkAB_gens] at hg; cases hg

/-- In `cexP` the exact sets contain only `A`. -/
theorem cexP_inS {E : Node} {m : Mark} (h : InS cexP E m) : m = 1 := by
  cases h with
  | single _ _ hs _ _ _ hg => exact cexP_gen hs hg
  | joined _ _ hs _ _ _ _ _ _ _ _ hg => exact cexP_gen hs hg
  | sinkGen _ _ hs _ _ _ _ _ _ _ _ hg => exact cexP_gen hs hg

theorem cexP_not_app : ¬ Applicable cexP 0 0 sinkAB := by
  rintro ⟨_, c, hc, hsat⟩
  rw [sinkAB_abs_cond] at hc
  simp only [List.mem_singleton] at hc
  subst hc
  rcases hsat with ⟨hl, _⟩ | ⟨_, hall⟩
  · simp at hl
  · obtain ⟨_, _, _, _, _, hin⟩ := hall 2 (by simp)
    exact absurd (cexP_inS hin) (by decide)

theorem cexP_relax_app : ApplicableRelax cexP 0 0 sinkAB := by
  have hA : InSRelax cexP 0 1 :=
    .single (n := 0) (pc := 0) (σ := srcP) (c := []) (by decide) (.refl 0)
      (by rw [cexP_ns]; simp) (by rw [srcP_abs_cond]; simp) (by decide) (by simp)
      (by rw [srcP_gens]; simp)
  exact ⟨by simp [cexP], [1, 2], by rw [sinkAB_abs_cond]; simp,
    .inr ⟨by decide, 1, by simp, 0, 0, by decide, .refl 0, rfl, hA⟩⟩

end RelaxedLemmas

open RelaxedLemmas in
/-- Correct 4* loses precision: in `cexP` a sink that needs both `A` and `B`
is selected because `A` is present, although nothing ever generates `B`, so
the exact scan does not select it. -/
theorem relax_strictly_coarser :
    ApplicableRelax cexP 0 0 sinkAB ∧ ¬ Applicable cexP 0 0 sinkAB :=
  ⟨cexP_relax_app, cexP_not_app⟩

/-! ## 5. The relaxed joined test needs single marks only -/

/-- The premise of `InSRelax.joined` (and `sinkGenJoined`) for a cube `c` at
node `n`: one atom `m0` of `c`, held by a root `w0` that reaches a node `wn0`
of `n`'s method. -/
def JoinedPremiseRelax (p : Program) (n : Node) (c : Cube) : Prop :=
  ∃ m0 w0 wn0, m0 ∈ c ∧ w0 ∈ p.roots ∧ Reaches p w0 wn0 ∧ p.method wn0 = p.method n ∧
    InSRelax p w0 m0

/-- The relaxed joined premise holds iff ONE mark of the cube is in
`U(method n)`. The scan therefore never tracks combinations of marks, only
individual marks. That is the motivation for 4*. -/
theorem joined_relax_single_mark {p : Program} {n : Node} {c : Cube} :
    JoinedPremiseRelax p n c ↔ ∃ m, m ∈ c ∧ RelaxU p n m := by
  constructor
  · rintro ⟨m0, w0, wn0, hm, hw, hr, hmeth, hin⟩
    exact ⟨m0, hm, w0, wn0, hw, hr, hmeth, hin⟩
  · rintro ⟨m0, hm, w0, wn0, hw, hr, hmeth, hin⟩
    exact ⟨m0, w0, wn0, hm, hw, hr, hmeth, hin⟩

/-- No combination is ever needed: the relaxed joined premise of a cube is the
disjunction of the premises of its one-atom sub-cubes. -/
theorem joined_relax_singletons {p : Program} {n : Node} {c : Cube} :
    JoinedPremiseRelax p n c ↔ ∃ m, m ∈ c ∧ JoinedPremiseRelax p n [m] := by
  constructor
  · rintro ⟨m0, w0, wn0, hm, hw, hr, hmeth, hin⟩
    exact ⟨m0, hm, m0, w0, wn0, List.mem_singleton_self _, hw, hr, hmeth, hin⟩
  · rintro ⟨m, hm, m0, w0, wn0, hm0, hw, hr, hmeth, hin⟩
    rw [List.mem_singleton] at hm0
    subst hm0
    exact ⟨m0, w0, wn0, hm, hw, hr, hmeth, hin⟩

/-- Given any list `U` that enumerates `U(method n)`, the relaxed joined test
is the executable check `U ∩ atoms(c) ≠ ∅`. -/
theorem joined_relax_decide {p : Program} {n : Node} {c : Cube} {U : List Mark}
    (hU : ∀ m, m ∈ U ↔ RelaxU p n m) :
    JoinedPremiseRelax p n c ↔ (c.any fun m => U.contains m) = true := by
  rw [joined_relax_single_mark]
  simp only [List.any_eq_true, List.contains_iff_mem, hU]

/-- The relaxed joined test is monotone in `U`: adding marks to `U` can only
turn it from false to true. -/
theorem joined_relax_mono {c : Cube} {U U' : List Mark} (h : Subset U U')
    (hc : (c.any fun m => U.contains m) = true) : (c.any fun m => U'.contains m) = true := by
  simp only [List.any_eq_true, List.contains_iff_mem] at hc ⊢
  obtain ⟨m, hm, hu⟩ := hc
  exact ⟨m, hm, h m hu⟩

/-- For a multi-literal cube, relaxed satisfiability is exactly the relaxed
joined premise, i.e. the single-mark test. -/
theorem cubeSatRelax_joined_iff {p : Program} {n : Node} {c : Cube} (hl : 2 ≤ c.length) :
    CubeSatRelax p n c ↔ JoinedPremiseRelax p n c := by
  rw [joined_relax_single_mark]
  constructor
  · rintro (⟨hl1, _⟩ | ⟨_, h⟩)
    · exact absurd (Nat.le_trans hl hl1) (by decide)
    · exact h
  · exact fun h => .inr ⟨hl, h⟩

end MarkScan
