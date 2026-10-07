/-
  ApSpec.ForwardSeeds — FORWARD SEEDS: after run 1, a forward restricted run fires an unconditional
  source only if the backward run before it reached that source.

  The design change (the user's decision). Up to now every forward run of the iteration
  (`RCov.runSeq`, `Backward.iteration_general`) analyses the full program `P`: every unconditional
  source fires where the zero fact reaches it. With forward seeds, run 1 still fires every source,
  but a later forward run fires an UNCONDITIONAL SOURCE only if it is a FORWARD SEED: a source that
  the previous backward run reached (its SOURCE HIT, `ap.md` §8.11, analyzer-core.md §4.7). This is
  the mirror of the backward run, where only the seeded sinks fire (rule `DB.seed`). The zero fact
  still propagates as before (the zero demand is in every method); only the source edges are
  restricted.

  The model (Part 1). An unconditional source is a statement micro edge `e` with the zero premise
  base and a non-zero target base (`isSrc`). The zero keep edge `zero → zero` is not a source; a
  conditional source (a non-zero premise) is not restricted. The restricted program
  `keepSources P σ` keeps every instruction and every micro edge of `P`, except the source edges
  `e` at the statement `(M, n, stmt s, n')` with `σ M n e = false` (`touched` is unchanged: only
  edges are dropped). A forward restricted run with seeds is `DR (keepSources P σ) …`.

  The source hits (Part 3). `srcHit P R M n e`: the backward run `R` has a concrete requirement at
  the forward node after the statement whose location set meets the image of the source edge.
  The implementation records a hit when it applies the reversed source edge to a requirement and
  gets a result; that is a superset (`srcHit_applies`), so the theorems hold for every `σ` that
  contains `srcHit`.

  Main results:
    * Part 1. What `keepSources` drops: exactly the unseeded unconditional sources
      (`mem_keepStmt`, `unseeded_dropped`; a conditional source and the zero keep edge stay:
      `cond_kept`, `zero_kept`). It keeps the hypotheses of the iteration: `keep_WF`, `keep_bindStar`,
      `keep_markRev`, `keep_noZeroBack`, `keep_zeroKept` (the zero keep edge stays: `zero_kept`),
      `keep_exitReach` (the CFG does not change: `cfg_keep_iff`). The sinks are a separate
      parameter of the runs; the forward runs with seeds use the same sinks.
    * Part 2. Monotonicity: a flow of the restricted program is a flow of `P` (`flow_keep`,
      `reach_keep`, `flowRD_keep`, `reachRD_keep`, `flowR_keep`, `reachR_keep`), and a larger seed
      set keeps it (`flow_keep_mono`, …, `reachR_keep_mono`). One simulation `Sim` gives them all.
    * Part 4. THE CORE: along a justified witness the backward run hits every source step, so the
      demanded witness that contract B gives lies in `keepSources P σ` for every `σ` that contains
      the hits (`seg_src`, `reach_of_db_src`, `demanded_src`), and contract B with sources
      (`B_src`).
    * Part 5. The iteration with forward seeds (`runSeqSrc`, `iteration_src`): every forward run
      reports every real vulnerability of `P`, if each forward run after run 1 fires at least the
      sources that the previous backward run hit (on the FULL reversed program `Program.rev P`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.Backward

namespace ApSpec.FSeeds
open ApSpec ApSpec.Reverse ApSpec.Backward

/-! ## Part 1. The restricted program -/

/-- An UNCONDITIONAL SOURCE edge: a micro edge from the zero base to another base. The zero keep
    edge `zero → zero` is not a source, and neither is a conditional source (non-zero premise). -/
def isSrc (e : MicroEdge) : Bool := Nat.beq e.1.base zeroBase && !Nat.beq e.2.base zeroBase

/-- The statement `s` at `(M, n)` with the source edges that `σ` does not seed dropped. The touched
    bases are unchanged. -/
def keepStmt (σ : MethodId → Node → MicroEdge → Bool) (M : MethodId) (n : Node) (s : Stmt) :
    Stmt :=
  { touched := s.touched, edges := s.edges.filter (fun e => !isSrc e || σ M n e) }

/-- The instruction at `(M, n)` with the unseeded source edges dropped (only a statement changes). -/
def keepInstr (σ : MethodId → Node → MicroEdge → Bool) (M : MethodId) (n : Node) : Instr → Instr
  | .stmt s     => .stmt (keepStmt σ M n s)
  | .call c     => .call c
  | .clean cl   => .clean cl
  | .filt b may => .filt b may

def keepE (σ : MethodId → Node → MicroEdge → Bool) (x : MethodId × Node × Instr × Node) :
    MethodId × Node × Instr × Node :=
  (x.1, x.2.1, keepInstr σ x.1 x.2.1 x.2.2.1, x.2.2.2)

/-- THE PROGRAM OF A FORWARD RUN WITH SEEDS: `P` with every unconditional source edge `e` at the
    statement `(M, n, stmt s, n')` dropped unless `σ M n e = true`. -/
def keepSources (P : Program) (σ : MethodId → Node → MicroEdge → Bool) : Program :=
  { entry := P.entry, exit := P.exit, edges := P.edges.map (keepE σ) }

theorem isSrc_true {e : MicroEdge} (h : isSrc e = true) :
    e.1.base = zeroBase ∧ e.2.base ≠ zeroBase := by
  unfold isSrc at h
  cases h1 : Nat.beq e.1.base zeroBase with
  | false => rw [h1] at h; cases h
  | true =>
    cases h2 : Nat.beq e.2.base zeroBase with
    | false => exact ⟨Nat.eq_of_beq_eq_true h1, Nat.ne_of_beq_eq_false h2⟩
    | true => rw [h1, h2] at h; cases h

theorem isSrc_zero : isSrc (zeroFact, zeroFact) = false := rfl

/-- The edges of a restricted statement: the edges of `s`, a source edge only if seeded. -/
theorem mem_keepStmt {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} {e : MicroEdge} :
    e ∈ (keepStmt σ M n s).edges ↔ e ∈ s.edges ∧ (isSrc e = true → σ M n e = true) := by
  constructor
  · intro h
    obtain ⟨hm, hp⟩ := List.mem_filter.mp h
    refine ⟨hm, fun hs => ?_⟩
    rw [hs] at hp
    exact hp
  · rintro ⟨hm, hp⟩
    refine List.mem_filter.mpr ⟨hm, ?_⟩
    cases hs : isSrc e with
    | false => rfl
    | true =>
      have h1 := hp hs
      rw [h1]
      rfl

/-- A micro edge that is not an unconditional source stays (conditional sources, the zero keep
    edge, every other edge). -/
theorem nonsrc_kept {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} {e : MicroEdge} (he : e ∈ s.edges) (hn : isSrc e = false) :
    e ∈ (keepStmt σ M n s).edges :=
  mem_keepStmt.mpr ⟨he, fun h => by rw [hn] at h; cases h⟩

/-- The zero keep edge stays. -/
theorem zero_kept {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} (he : (zeroFact, zeroFact) ∈ s.edges) :
    (zeroFact, zeroFact) ∈ (keepStmt σ M n s).edges :=
  nonsrc_kept he isSrc_zero

/-- A conditional source (a premise off the zero base) stays. -/
theorem cond_kept {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} {e : MicroEdge} (he : e ∈ s.edges) (hb : e.1.base ≠ zeroBase) :
    e ∈ (keepStmt σ M n s).edges := by
  refine nonsrc_kept he ?_
  unfold isSrc
  cases h1 : Nat.beq e.1.base zeroBase with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true h1) hb

/-- An unconditional source that `σ` does not seed is dropped. -/
theorem unseeded_dropped {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} {e : MicroEdge} (hs : isSrc e = true) (hσ : σ M n e = false) :
    e ∉ (keepStmt σ M n s).edges := fun h => by
  have h1 := (mem_keepStmt.mp h).2 hs
  rw [hσ] at h1
  cases h1

/-- A restricted statement makes fewer steps. -/
theorem keepStmt_step_sub {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId} {n : Node}
    {s : Stmt} {l l' : Loc} (h : (keepStmt σ M n s).step l l') : s.step l l' := by
  rcases h with ⟨hb, hl⟩ | ⟨e, he, hd⟩
  · exact Or.inl ⟨hb, hl⟩
  · exact Or.inr ⟨e, (mem_keepStmt.mp he).1, hd⟩

/-- A larger seed set makes more steps. -/
theorem keepStmt_step_mono {σ σ' : MethodId → Node → MicroEdge → Bool}
    (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true) {M : MethodId} {n : Node}
    {s : Stmt} {l l' : Loc} (h : (keepStmt σ M n s).step l l') : (keepStmt σ' M n s).step l l' := by
  rcases h with ⟨hb, hl⟩ | ⟨e, he, hd⟩
  · exact Or.inl ⟨hb, hl⟩
  · obtain ⟨hm, hp⟩ := mem_keepStmt.mp he
    exact Or.inr ⟨e, mem_keepStmt.mpr ⟨hm, fun hs => hσσ M n e (hp hs)⟩, hd⟩

/-- With every source seeded, a statement makes every step. -/
theorem keepStmt_step_all {M : MethodId} {n : Node} {s : Stmt} {l l' : Loc} (h : s.step l l') :
    (keepStmt (fun _ _ _ => true) M n s).step l l' := by
  rcases h with ⟨hb, hl⟩ | ⟨e, he, hd⟩
  · exact Or.inl ⟨hb, hl⟩
  · exact Or.inr ⟨e, mem_keepStmt.mpr ⟨he, fun _ => rfl⟩, hd⟩

/-! ### Membership in the restricted program -/

theorem mem_keep_stmt {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {s : Stmt} (h : (M, n, Instr.stmt s, n') ∈ P.edges) :
    (M, n, Instr.stmt (keepStmt σ M n s), n') ∈ (keepSources P σ).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_keep_call {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {c : Call} (h : (M, n, Instr.call c, n') ∈ P.edges) :
    (M, n, Instr.call c, n') ∈ (keepSources P σ).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_keep_clean {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {cl : Cleaner} (h : (M, n, Instr.clean cl, n') ∈ P.edges) :
    (M, n, Instr.clean cl, n') ∈ (keepSources P σ).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_keep_filt {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {b : Base} {may : List Acc → Bool} (h : (M, n, Instr.filt b may, n') ∈ P.edges) :
    (M, n, Instr.filt b may, n') ∈ (keepSources P σ).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem mem_keep {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {ins : Instr} (h : (M, n, ins, n') ∈ P.edges) :
    (M, n, keepInstr σ M n ins, n') ∈ (keepSources P σ).edges :=
  List.mem_map.mpr ⟨_, h, rfl⟩

/-- Every edge of the restricted program comes from an edge of `P` at the same place. -/
theorem mem_keep_inv {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {ins' : Instr} (h : (M, n, ins', n') ∈ (keepSources P σ).edges) :
    ∃ ins, (M, n, ins, n') ∈ P.edges ∧ ins' = keepInstr σ M n ins := by
  obtain ⟨⟨M0, a, ins, b⟩, hm, he⟩ := List.mem_map.mp h
  injection he with h1 h2
  injection h2 with h3 h4
  injection h4 with h5 h6
  subst h1 h3 h6
  exact ⟨ins, hm, h5.symm⟩

theorem keep_stmt_inv {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {s' : Stmt} (h : (M, n, Instr.stmt s', n') ∈ (keepSources P σ).edges) :
    ∃ s, (M, n, Instr.stmt s, n') ∈ P.edges ∧ s' = keepStmt σ M n s := by
  obtain ⟨ins, hm, he⟩ := mem_keep_inv h
  cases ins with
  | stmt s =>
    injection he with he'
    exact ⟨s, hm, he'⟩
  | call c => cases he
  | clean cl => cases he
  | filt b may => cases he

theorem keep_call_inv {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {c : Call} (h : (M, n, Instr.call c, n') ∈ (keepSources P σ).edges) :
    (M, n, Instr.call c, n') ∈ P.edges := by
  obtain ⟨ins, hm, he⟩ := mem_keep_inv h
  cases ins with
  | stmt s => cases he
  | call c0 =>
    injection he with he'
    subst he'
    exact hm
  | clean cl => cases he
  | filt b may => cases he

theorem keep_clean_inv {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {cl : Cleaner} (h : (M, n, Instr.clean cl, n') ∈ (keepSources P σ).edges) :
    (M, n, Instr.clean cl, n') ∈ P.edges := by
  obtain ⟨ins, hm, he⟩ := mem_keep_inv h
  cases ins with
  | stmt s => cases he
  | call c => cases he
  | clean cl0 =>
    injection he with he'
    subst he'
    exact hm
  | filt b may => cases he

theorem keep_filt_inv {P : Program} {σ : MethodId → Node → MicroEdge → Bool} {M : MethodId}
    {n n' : Node} {b : Base} {may : List Acc → Bool}
    (h : (M, n, Instr.filt b may, n') ∈ (keepSources P σ).edges) :
    (M, n, Instr.filt b may, n') ∈ P.edges := by
  obtain ⟨ins, hm, he⟩ := mem_keep_inv h
  cases ins with
  | stmt s => cases he
  | call c => cases he
  | clean cl => cases he
  | filt b0 may0 =>
    injection he with hb hmay
    subst hb hmay
    exact hm

/-! ### The hypotheses of the iteration hold for the restricted program -/

section Preserve
variable {P : Program} {σ : MethodId → Node → MicroEdge → Bool}

theorem keep_WF (hW : P.WF) : (keepSources P σ).WF where
  stmtTouched := fun M n s' n' h e he => by
    obtain ⟨s, hm, rfl⟩ := keep_stmt_inv h
    exact hW.stmtTouched M n s n' hm e (mem_keepStmt.mp he).1
  toStar := fun M n c n' h => hW.toStar M n c n' (keep_call_inv h)
  fromStar := fun M n c n' h => hW.fromStar M n c n' (keep_call_inv h)
  filtPrefix := fun M n b may n' h => hW.filtPrefix M n b may n' (keep_filt_inv h)

theorem keep_bindStar (hT : BindTargetsStar P) : BindTargetsStar (keepSources P σ) :=
  fun M n c n' h => hT M n c n' (keep_call_inv h)

theorem keep_markRev (hmr : StmtsMarkRev P) : StmtsMarkRev (keepSources P σ) := by
  intro M n s' n' h e he
  obtain ⟨s, hm, rfl⟩ := keep_stmt_inv h
  exact hmr M n s n' hm e (mem_keepStmt.mp he).1

theorem keep_noZeroBack (hNZB : NoZeroBack P) : NoZeroBack (keepSources P σ) :=
  fun M n c n' h => hNZB M n c n' (keep_call_inv h)

/-- The zero keep edge stays, so the zero fact is still kept by every instruction. -/
theorem keep_zeroKept (hZ : ZeroKept P) : ZeroKept (keepSources P σ) where
  stmt := fun M n s' n' h hz => by
    obtain ⟨s, hm, rfl⟩ := keep_stmt_inv h
    exact zero_kept (hZ.stmt M n s n' hm hz)
  clean := fun M n cl n' h => hZ.clean M n cl n' (keep_clean_inv h)
  filt := fun M n b may n' h => hZ.filt M n b may n' (keep_filt_inv h)

/-- The CFG does not change. -/
theorem cfg_keep_iff {M : MethodId} {a b : Node} :
    CfgPath (keepSources P σ) M a b ↔ CfgPath P M a b := by
  constructor
  · intro h
    induction h with
    | refl => exact CfgPath.refl
    | step _ he ih =>
      obtain ⟨_, hm, _⟩ := mem_keep_inv he
      exact CfgPath.step ih hm
  · intro h
    induction h with
    | refl => exact CfgPath.refl
    | step _ he ih => exact CfgPath.step ih (mem_keep he)

theorem called_keep_iff {roots : List MethodId} {M : MethodId} :
    Called (keepSources P σ) roots M ↔ Called P roots M := by
  constructor
  · rintro (h | ⟨M', n, c, n', he, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨M', n, c, n', keep_call_inv he, hc⟩
  · rintro (h | ⟨M', n, c, n', he, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨M', n, c, n', mem_keep_call he, hc⟩

theorem keep_exitReach {roots : List MethodId} (hX : ExitReach P roots) :
    ExitReach (keepSources P σ) roots := fun M n hc hp =>
  cfg_keep_iff.mpr (hX M n (called_keep_iff.mp hc) (cfg_keep_iff.mp hp))

/-- The forward summaries handed to the backward run read only the method exits, which do not
    change: the reversed summary demand of a run on the restricted program is the same relation. -/
theorem revSummaryDemand_keep (R : Obj → Prop) :
    revSummaryDemand (keepSources P σ) R = revSummaryDemand P R := rfl

end Preserve

#print axioms mem_keepStmt
#print axioms zero_kept
#print axioms cond_kept
#print axioms unseeded_dropped
#print axioms keep_WF
#print axioms keep_bindStar
#print axioms keep_markRev
#print axioms keep_noZeroBack
#print axioms keep_zeroKept
#print axioms keep_exitReach

/-! ## Part 2. Monotonicity: a simulation of the instructions -/

/-- `Q` simulates `P` instruction by instruction at the same places: the same entries and exits,
    a statement of `Q` makes at least the steps of the statement of `P`, and the other
    instructions are the same. -/
structure Sim (P Q : Program) : Prop where
  entry : ∀ M, Q.entry M = P.entry M
  exit : ∀ M, Q.exit M = P.exit M
  stmt : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    ∃ s', (M, n, Instr.stmt s', n') ∈ Q.edges ∧ ∀ l l', s.step l l' → s'.step l l'
  call : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → (M, n, Instr.call c, n') ∈ Q.edges
  clean : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → (M, n, Instr.clean cl, n') ∈ Q.edges
  filt : ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges →
    (M, n, Instr.filt b may, n') ∈ Q.edges

section SimLemmas
variable {P Q : Program} (hs : Sim P Q)
include hs

theorem flow_sim {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (h : Flow P M l0 n l) :
    Flow Q M l0 n l := by
  induction h with
  | start M l0 => rw [← hs.entry M]; exact Flow.start M l0
  | step _ he hst ih =>
    obtain ⟨s', he', hss⟩ := hs.stmt _ _ _ _ he
    exact Flow.step ih he' (hss _ _ hst)
  | pass _ he hm ih => exact Flow.pass ih (hs.call _ _ _ _ he) hm
  | call _ he he1 hd1 _ he2 hd2 ih ihc =>
    rw [← hs.exit] at ihc
    exact Flow.call ih (hs.call _ _ _ _ he) he1 hd1 ihc he2 hd2
  | clean _ he hcl ih => exact Flow.clean ih (hs.clean _ _ _ _ he) hcl
  | filt _ he hl ih => exact Flow.filt ih (hs.filt _ _ _ _ _ he) hl

theorem reach_sim {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ApSpec.Reach P roots M n l) : ApSpec.Reach Q roots M n l := by
  induction h with
  | root hM hfl => exact Reach.root hM (flow_sim hs hfl)
  | down _ he he1 hd1 hfc ih => exact Reach.down ih (hs.call _ _ _ _ he) he1 hd1 (flow_sim hs hfc)

theorem flowRD_sim {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowRD P R M l0 n l) : FlowRD Q R M l0 n l := by
  induction h with
  | start M l0 => rw [← hs.entry M]; exact FlowRD.start M l0
  | step _ he hst ih =>
    obtain ⟨s', he', hss⟩ := hs.stmt _ _ _ _ he
    exact FlowRD.step ih he' (hss _ _ hst)
  | pass _ he hm ih => exact FlowRD.pass ih (hs.call _ _ _ _ he) hm
  | call _ he he1 hd1 _ hj hg hjc hdg he2 hd2 ih ihc =>
    rw [← hs.exit] at ihc hg
    exact FlowRD.call ih (hs.call _ _ _ _ he) he1 hd1 ihc hj hg hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRD.clean ih (hs.clean _ _ _ _ he) hcl
  | filt _ he hl ih => exact FlowRD.filt ih (hs.filt _ _ _ _ _ he) hl

theorem reachRD_sim {R : Obj → Prop} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRD P R roots M n l) : ReachRD Q R roots M n l := by
  induction h with
  | root hM hfl => exact ReachRD.root hM (flowRD_sim hs hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachRD.down ih (hs.call _ _ _ _ he) he1 hd1 hj hjc (flowRD_sim hs hfc)

theorem flowR_sim {dem : MethodId → DemandEdge → Prop} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : FlowR P dem M l0 n l) : FlowR Q dem M l0 n l := by
  induction h with
  | start M l0 => rw [← hs.entry M]; exact FlowR.start M l0
  | step _ he hst ih =>
    obtain ⟨s', he', hss⟩ := hs.stmt _ _ _ _ he
    exact FlowR.step ih he' (hss _ _ hst)
  | pass _ he hm ih => exact FlowR.pass ih (hs.call _ _ _ _ he) hm
  | call _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    rw [← hs.exit] at ihc
    exact FlowR.call ih (hs.call _ _ _ _ he) he1 hd1 ihc hdem hdin hdout hp he2 hd2
  | clean _ he hcl ih => exact FlowR.clean ih (hs.clean _ _ _ _ he) hcl
  | filt _ he hl ih => exact FlowR.filt ih (hs.filt _ _ _ _ _ he) hl

theorem reachR_sim {dem : MethodId → DemandEdge → Prop} {roots : List MethodId} {M : MethodId}
    {n : Node} {l : Loc} (h : ReachR P dem roots M n l) : ReachR Q dem roots M n l := by
  induction h with
  | root hM hfl => exact ReachR.root hM (flowR_sim hs hfl)
  | down _ he he1 hd1 hdem hdin hfc ih =>
    exact ReachR.down ih (hs.call _ _ _ _ he) he1 hd1 hdem hdin (flowR_sim hs hfc)

end SimLemmas

/-- `P` simulates its restriction. -/
theorem sim_keep {P : Program} {σ : MethodId → Node → MicroEdge → Bool} :
    Sim (keepSources P σ) P where
  entry := fun _ => rfl
  exit := fun _ => rfl
  stmt := fun _ _ _ _ h => by
    obtain ⟨s, hm, rfl⟩ := keep_stmt_inv h
    exact ⟨s, hm, fun _ _ hst => keepStmt_step_sub hst⟩
  call := fun _ _ _ _ h => keep_call_inv h
  clean := fun _ _ _ _ h => keep_clean_inv h
  filt := fun _ _ _ _ _ h => keep_filt_inv h

/-- A larger seed set simulates a smaller one. -/
theorem sim_keep_mono {P : Program} {σ σ' : MethodId → Node → MicroEdge → Bool}
    (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true) :
    Sim (keepSources P σ) (keepSources P σ') where
  entry := fun _ => rfl
  exit := fun _ => rfl
  stmt := fun _ _ _ _ h => by
    obtain ⟨s, hm, rfl⟩ := keep_stmt_inv h
    exact ⟨_, mem_keep_stmt hm, fun _ _ hst => keepStmt_step_mono hσσ hst⟩
  call := fun _ _ _ _ h => mem_keep_call (keep_call_inv h)
  clean := fun _ _ _ _ h => mem_keep_clean (keep_clean_inv h)
  filt := fun _ _ _ _ _ h => mem_keep_filt (keep_filt_inv h)

/-- With every source seeded the restriction simulates `P` (run 1 is the case `σ = true`). -/
theorem sim_all {P : Program} : Sim P (keepSources P (fun _ _ _ => true)) where
  entry := fun _ => rfl
  exit := fun _ => rfl
  stmt := fun _ _ _ _ h => ⟨_, mem_keep_stmt h, fun _ _ hst => keepStmt_step_all hst⟩
  call := fun _ _ _ _ h => mem_keep_call h
  clean := fun _ _ _ _ h => mem_keep_clean h
  filt := fun _ _ _ _ _ h => mem_keep_filt h

section Mono
variable {P : Program} {σ σ' : MethodId → Node → MicroEdge → Bool}

theorem flow_keep {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : Flow (keepSources P σ) M l0 n l) : Flow P M l0 n l := flow_sim sim_keep h

theorem reach_keep {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ApSpec.Reach (keepSources P σ) roots M n l) : ApSpec.Reach P roots M n l :=
  reach_sim sim_keep h

theorem flowRD_keep {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowRD (keepSources P σ) R M l0 n l) : FlowRD P R M l0 n l := flowRD_sim sim_keep h

theorem reachRD_keep {R : Obj → Prop} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRD (keepSources P σ) R roots M n l) : ReachRD P R roots M n l :=
  reachRD_sim sim_keep h

theorem flowR_keep {dem : MethodId → DemandEdge → Prop} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : FlowR (keepSources P σ) dem M l0 n l) : FlowR P dem M l0 n l :=
  flowR_sim sim_keep h

theorem reachR_keep {dem : MethodId → DemandEdge → Prop} {roots : List MethodId} {M : MethodId}
    {n : Node} {l : Loc} (h : ReachR (keepSources P σ) dem roots M n l) : ReachR P dem roots M n l :=
  reachR_sim sim_keep h

theorem flow_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : Flow (keepSources P σ) M l0 n l) : Flow (keepSources P σ') M l0 n l :=
  flow_sim (sim_keep_mono hσσ) h

theorem reach_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ApSpec.Reach (keepSources P σ) roots M n l) : ApSpec.Reach (keepSources P σ') roots M n l :=
  reach_sim (sim_keep_mono hσσ) h

theorem flowRD_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowRD (keepSources P σ) R M l0 n l) : FlowRD (keepSources P σ') R M l0 n l :=
  flowRD_sim (sim_keep_mono hσσ) h

theorem reachRD_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {R : Obj → Prop} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRD (keepSources P σ) R roots M n l) : ReachRD (keepSources P σ') R roots M n l :=
  reachRD_sim (sim_keep_mono hσσ) h

theorem flowR_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {dem : MethodId → DemandEdge → Prop} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowR (keepSources P σ) dem M l0 n l) : FlowR (keepSources P σ') dem M l0 n l :=
  flowR_sim (sim_keep_mono hσσ) h

theorem reachR_keep_mono (hσσ : ∀ M n e, σ M n e = true → σ' M n e = true)
    {dem : MethodId → DemandEdge → Prop} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachR (keepSources P σ) dem roots M n l) : ReachR (keepSources P σ') dem roots M n l :=
  reachR_sim (sim_keep_mono hσσ) h

/-- Seeding every source gives exactly the flows of `P`. -/
theorem flow_keep_all_iff {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} :
    Flow (keepSources P (fun _ _ _ => true)) M l0 n l ↔ Flow P M l0 n l :=
  ⟨flow_keep, flow_sim sim_all⟩

end Mono

#print axioms flow_keep
#print axioms reach_keep
#print axioms flowRD_keep
#print axioms reachRD_keep
#print axioms flowR_keep
#print axioms reachR_keep
#print axioms flow_keep_mono
#print axioms reach_keep_mono
#print axioms flowRD_keep_mono
#print axioms reachRD_keep_mono
#print axioms flowR_keep_mono
#print axioms reachR_keep_mono
#print axioms flow_keep_all_iff

/-! ## Part 3. The source hits of a backward run

`R` is a backward run (`DB (Program.rev P) …`); its edges are at FORWARD nodes. The source edge `e`
of the forward statement `(M, n, stmt s, n')` is HIT if `R` has a concrete requirement `f` at the
node `n'` AFTER the statement whose location set (from the premise location `lX`) contains a
location `l'` that `e` gives from a location `l1` (necessarily of the zero base; for the source
edges with the premise `zeroFact`, `l1` is the zero location). -/

def srcHit (P : Program) (R : Obj → Prop) (M : MethodId) (n : Node) (e : MicroEdge) : Prop :=
  ∃ s n' i f lX l1 l', (M, n, Instr.stmt s, n') ∈ P.edges ∧ e ∈ s.edges ∧
    e.1.base = zeroBase ∧ e.2.base ≠ zeroBase ∧
    R (.edge M i n' f) ∧ (∃ t, f.fact.mark = .conc t) ∧ den i f.fact lX l' ∧ den e.1 e.2 l1 l'

/-- A hit is what the implementation records: the reversed source edge (an edge of the reversed
    statement) applied to the requirement gives a result. So every `σ` that contains the recorded
    hits contains `srcHit`. -/
theorem srcHit_applies {P : Program} (hmr : StmtsMarkRev P) {R : Obj → Prop} {M : MethodId}
    {n : Node} {e : MicroEdge} (h : srcHit P R M n e) :
    ∃ s n' i f, (M, n, Instr.stmt s, n') ∈ P.edges ∧ e ∈ s.edges ∧
      revEdge e.1 e.2 ∈ (Stmt.rev s).edges ∧ R (.edge M i n' f) ∧
      ∃ r, r ∈ (applyEdge f (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts := by
  obtain ⟨s, n', i, f, lX, l1, l', he, hes, _, _, hR, ⟨t, ht⟩, hd, hde⟩ := h
  have hrev : revEdge e.1 e.2 ∈ (Stmt.rev s).edges :=
    List.mem_append_left _ (List.mem_map.mpr ⟨e, hes, rfl⟩)
  have hdr := revEdge_sound (hmr M n s n' he e hes) hde
  rcases applyEdge_sound hd hdr with ⟨r, hr, _⟩ | ⟨habs, _⟩
  · exact ⟨s, n', i, f, he, hes, hrev, hR, r, hr⟩
  · exact absurd ht (habs t)

#print axioms srcHit_applies

/-- THE STEP LEMMA. A forward statement step that ends at a location of a concrete requirement of
    the backward run is a step of the restricted statement, for every `σ` that contains the hits:
    if the step uses a source edge, that edge is hit. -/
theorem keep_step {P : Program} {R : Obj → Prop} {σ : MethodId → Node → MicroEdge → Bool}
    (hσ : ∀ M n e, srcHit P R M n e → σ M n e = true)
    {M : MethodId} {n n' : Node} {s : Stmt} {i : PFact} {f : AFact} {lX l1 l' : Loc}
    (he : (M, n, Instr.stmt s, n') ∈ P.edges) (h : R (.edge M i n' f))
    (hc : ∃ t, f.fact.mark = .conc t) (hd : den i f.fact lX l') (hst : s.step l1 l') :
    (keepStmt σ M n s).step l1 l' := by
  rcases hst with ⟨hb, hl⟩ | ⟨e, hes, hde⟩
  · exact Or.inl ⟨hb, hl⟩
  · refine Or.inr ⟨e, mem_keepStmt.mpr ⟨hes, fun hsrc => ?_⟩, hde⟩
    obtain ⟨hz, hnz⟩ := isSrc_true hsrc
    exact hσ M n e ⟨s, n', i, f, lX, l1, l', he, hes, hz, hnz, h, hc, hd, hde⟩

#print axioms keep_step

/-! ## Part 4. The backward run hits every source step of a justified witness

The induction of `Backward.seg_gen`, `reach_of_db_gen`, `demanded_gen`, with the demanded flow
built in `keepSources P σ`: in the `step` case the backward requirement after the statement covers
the end location of the step, so a source edge of the step is hit (`keep_step`); in the `call` case
the callee flow in the restricted program comes from the induction hypothesis of the callee. The
backward run itself runs on the FULL reversed program `Program.rev P`. -/

section Src
variable {P : Program} {Rk : Obj → Prop} {counted : Acc → Bool} {L : Nat}
  {demB : MethodId → DemandEdge → Prop} {recsB : MethodId → PFact × AFact → Prop}
  {sinksB : List (MethodId × Node × PFact)} {rootsB : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
  {σ : MethodId → Node → MicroEdge → Bool}

/-- `Backward.seg_gen` with the demanded flow in `keepSources P σ`. -/
theorem seg_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    (hσ : ∀ M n e, srcHit P (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB
      rootsB seeds zbind) M n e → σ M n e = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowRD P Rk M l0 n l) :
    ∀ i f lX, DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
        zbind (.edge M i n f) →
      den i f.fact lX l → (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      (∃ f', DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
          zbind (.edge M i (P.entry M) f') ∧ den i f'.fact lX l0 ∧
          (∃ t, f'.fact.mark = .conc t) ∧ Invariant.Legal f') ∧
      FlowR (keepSources P σ) (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI
        restrictU recsB sinksB rootsB seeds zbind)) M l0 n l := by
  induction hfl with
  | start M l0 =>
    intro i f lX h hd hc hl
    exact ⟨⟨f, h, hd, hc, hl⟩, FlowR.start M l0⟩
  | @step M l0 n1 l1 n' l' s _ he hst ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.stmt (Stmt.rev s), n1) ∈ (Program.rev P).edges := mem_rev_stmt he
    have hrs : (Stmt.rev s).step l' l1 := Stmt.rev_step_sound (hmr M n1 s n' he) hst
    -- the forward step is a step of the restricted statement: a source edge of it is hit
    have hks : (keepStmt σ M n1 s).step l1 l' := keep_step hσ he h hc hd hst
    obtain ⟨t, ht⟩ := hc
    rcases transfer_sound (counted := counted) (L := L) (rev_touched s) hd hrs with
      ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.step h hEr hr) hdr (transfer_mark_conc ht hr)
        (legal_transfer hl hr)
      exact ⟨res, FlowR.step hfr (mem_keep_stmt he) hks⟩
    · exact absurd ht (habs t)
  | @pass M l0 n1 l1 n' c _ he hb ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.call (Call.rev c), n1) ∈ (Program.rev P).edges := mem_rev_call he
    have hb' : memB f.fact.base (Call.rev c).touched = false := by
      show memB f.fact.base c.touched = false
      rw [← hd.2.1]
      exact hb
    obtain ⟨res, hfr⟩ := ih i f lX (DB.pass h hEr hb') hd hc hl
    exact ⟨res, FlowR.pass hfr (mem_keep_call he) hb⟩
  | @call M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 _ hj hg hjc hdg he2 hd2 ih ihc =>
    intro i f lX h hd hc hl
    obtain ⟨t, ht⟩ := hc
    have hEr : (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges := mem_rev_call he
    have hWr := rev_WF hW hT
    -- the reversed binding back takes the requirement into the callee's forward exit
    have her2 : revEdge e2.1 e2.2 ∈ (Call.rev c).toCallee := List.mem_map.mpr ⟨e2, he2, rfl⟩
    have hdr2 : den (revEdge e2.1 e2.2).1 (revEdge e2.1 e2.2).2 l3 l2 :=
      revEdge_sound (markRev_star ((hT M n c n' he).2 e2 he2)) hd2
    obtain ⟨a, ha, hda⟩ := Coverage.bind_in hWr hEr her2 hd hdr2
    have hadd : DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
        zbind (.added c.callee a.fact) := DB.added (c := Call.rev c) h hEr her2 ha
    obtain ⟨ta, hta⟩ := applyEdge_mark_conc ht ha
    -- the backward demand edge: the reversed forward summary `(j, g)`
    have hdB : demB c.callee ⟨g.fact, some j⟩ :=
      hdemB _ _ ⟨j, g.fact, ⟨hj, Or.inr ⟨g, hg, rfl⟩⟩, rfl⟩
    obtain ⟨jb, hemit, hjbc, hsat⟩ := RCore.emitM_contract_I g.fact a.fact l2 ta hta
      (den_covers_final hdg) (den_covers_final hda)
    have hjb : DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
        zbind (.init c.callee jb) := DB.initR (m := c.callee) hadd hdB hemit
    have hjbm : jb.mark = .conc ta := by rw [RCov.emitM_copies _ _ _ hemit]; exact hta
    -- the reversed callee flow: from the backward premise at the forward exit to the entry; the
    -- callee flow in the restricted program comes from the induction hypothesis of the callee
    obtain ⟨⟨gb, hgb, hdgb, ⟨tg, htg⟩, hlg⟩, hfrc⟩ := ihc jb (startFact jb) l2 (DB.start hjb)
      (startFact_sound hjbc) ⟨ta, by rw [startFact_mark]; exact hjbm⟩
      (fun _ hk => Invariant.startFact_legal hk)
    -- the restriction by the backward demand keeps the pair
    obtain ⟨g', hres, hdg', _⟩ := RCore.restrictS_contract jb gb ⟨g.fact, some j⟩ j l2 l1 hdgb
      (RCov.covers_loc (den_covers_final hdg)) rfl (RCov.covers_loc hjc)
    rw [← RCore.restrictU_eq_S_nonstar (not_star_of_legal hlg htg)] at hres
    -- the backward summary applied, and the reversed binding into the callee back to the caller
    obtain ⟨r, hr, hdr⟩ := RCov.sat_step RCore.satI_contract hsat hda hdg'
    have her1 : revEdge e1.1 e1.2 ∈ (Call.rev c).fromCallee := List.mem_map.mpr ⟨e1, he1, rfl⟩
    have hdr1 : den (revEdge e1.1 e1.2).1 (revEdge e1.1 e1.2).2 l1 l :=
      revEdge_sound (markRev_star ((hT M n c n' he).1 e1 he1)) hd1
    obtain ⟨r', hr', hdr'⟩ := Coverage.bind_out hWr hEr her1 hdr hdr1
    have hret := DB.ret (c := Call.rev c) h hEr her2 ha hjb hgb hdB hres hsat hr her1 hr'
    obtain ⟨t1, h1⟩ := applySummary_mark_conc hta hr
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 hr'
    obtain ⟨res, hfr⟩ := ih i _ lX hret (limitF_sound hdr') ⟨t2, by rw [limitF_mark]; exact h2⟩
      (Invariant.limitF_Legal (Invariant.applyEdge_Legal hr'))
    -- the hand-off demands the call: `(gb, some jb)`, and `jb` is not the zero fact
    have hne : jb ≠ zeroFact := by
      intro hz
      have hb1 : l2.base = jb.base := hjbc.1
      have hb2 : l2.base = e2.1.base := hd2.1
      rw [hz] at hb1
      exact hNZB M n c n' he e2 he2 (hb2.symm.trans hb1)
    have hdem : demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU
        recsB sinksB rootsB seeds zbind) c.callee ⟨gb.fact, some jb⟩ :=
      Or.inr (Or.inr ⟨jb, gb, hjb, hne, hgb, rfl⟩)
    exact ⟨res, FlowR.call hfr (mem_keep_call he) he1 hd1 hfrc hdem (den_covers_final hdgb) rfl
      (RCov.covers_loc hjbc) he2 hd2⟩
  | @clean M l0 n1 l1 n' cl _ he hcl ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.clean cl, n1) ∈ (Program.rev P).edges := mem_rev_clean he
    obtain ⟨t, ht⟩ := hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.clean h hEr hr) hdr (cleanRes_mark_conc ht hr)
        (Invariant.cleanRes_Legal hl hr)
      exact ⟨res, FlowR.clean hfr (mem_keep_clean he) hcl⟩
    · exact absurd ht (habs t)
  | @filt M l0 n1 l1 n' b may _ he hmay ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.filt b may, n1) ∈ (Program.rev P).edges := mem_rev_filt he
    have hff : f.fact.base = b → may f.fact.path = true := by
      intro hfb
      obtain ⟨_, hb1, _, _, _, σ, τ, _, hp1, _, _⟩ := hd
      have hm := hmay (hb1.trans hfb)
      rw [hp1] at hm
      exact hW.filtPrefix _ _ _ _ _ he _ _ hm
    obtain ⟨res, hfr⟩ := ih i f lX (DB.filt h hEr hff) hd hc hl
    exact ⟨res, FlowR.filt hfr (mem_keep_filt he) hmay⟩

#print axioms seg_src

/-- `Backward.reach_of_db_gen` with the demanded witness in `keepSources P σ`. -/
theorem reach_of_db_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    (hσ : ∀ M n e, srcHit P (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB
      rootsB seeds zbind) M n e → σ M n e = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRD P Rk roots M n l) :
    ∀ f, DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds zbind
        (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l → (∃ t, f.fact.mark = .conc t) →
      Invariant.Legal f →
      ReachR (keepSources P σ) (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI
        restrictU recsB sinksB rootsB seeds zbind)) roots M n l := by
  induction hRe with
  | root hM hfl =>
    intro f h hd hc hl
    exact ReachR.root hM (seg_src hW hT hmr hNZB hdemB hσ hfl zeroFact f zeroLoc h hd hc hl).2
  | @down M n l n' c e l1 n2 l2 j hRe0 hE he hd1 _ _ hfl ih =>
    intro f h hd hc hl
    obtain ⟨⟨f', h', hd', hc', _⟩, hfr⟩ :=
      seg_src hW hT hmr hNZB hdemB hσ hfl zeroFact f zeroLoc h hd hc hl
    have hRe0' := reachRD_reach hRe0
    have hz := zero_path (counted := counted) (L := L) (demand := demB) (emit := emitM)
      (sat := satI) (restrict := restrictU) (recs := recsB) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ
      (hX M n' (reach_called hRe0') (CfgPath.step (reach_cfg hRe0') hE))
      (zero_exit (zero_init hZ hX hzb hroots hRe0'))
    obtain ⟨g, hg, hdg, hcg, hlg⟩ := zret_descent hW hT hzb hE he hd1 hz h' hd' hc'
    have hdem : demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU
        recsB sinksB rootsB seeds zbind) c.callee ⟨f'.fact, none⟩ := Or.inr (Or.inl ⟨f', h', rfl⟩)
    exact ReachR.down (ih g hg hdg hcg hlg) (mem_keep_call hE) he hd1 hdem (den_covers_final hd')
      hfr

#print axioms reach_of_db_src

/-- `Backward.demanded_gen` in `keepSources P σ`: every den-aware sink witness of `P` whose sink is
    seeded is demanded by the backward run in the program with the sources it hit. -/
theorem demanded_src (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    (hσ : ∀ M n e, srcHit P (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB
      rootsB seeds zbind) M n e → σ M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachRD P Rk roots M n l) (hseed : (M, n, s) ∈ seeds)
    (hT' : s.mark = .conc T) (hk : s.kind = .exact ∨ s.kind = .any) (hsc : s.covers l) :
    ReachR (keepSources P σ) (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI
      restrictU recsB sinksB rootsB seeds zbind)) roots M n l :=
  reach_of_db_src hW hT hmr hNZB hZ hX hzb hroots hdemB hσ hRe _
    (DB.seed hseed (zero_at hZ hX hzb hroots (reachRD_reach hRe)))
    (limitF_sound (seed_den hT' hk hsc)) ⟨T, by rw [limitF_mark]; exact hT'⟩ (legal_seed hk)

#print axioms demanded_src

end Src

/-- Contract B with the hand-off in the program `Pn` of the next forward run: every den-aware
    witness of `P` (justified by the forward run `Rk`) whose sink `Rk` reported is demanded by
    `dnext` in `Pn`. With `Pn = P` it is `Backward.BackwardContractD`. -/
def BackwardContractIn (P Pn : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (Rk : Obj → Prop)
    (dnext : MethodId → DemandEdge → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRD P Rk roots M n l → (∃ b, Rk (.vuln M n s b)) → ReachR Pn dnext roots M n l

/-- CONTRACT B WITH FORWARD SEEDS. Under the hypotheses of `Backward.B_general`, the hand-off of
    the backward run demands every justified witness of a reported sink IN `keepSources P σ`, for
    every `σ` that contains the source hits of that backward run. -/
theorem B_src {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {σ : MethodId → Node → MicroEdge → Bool}
    (hσ : ∀ M n e, srcHit P (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB
      roots seeds true) M n e → σ M n e = true) :
    BackwardContractIn P (keepSources P σ) roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) := by
  intro M n l s T hs hT' hsc hRR hv
  obtain ⟨b, hv⟩ := hv
  exact demanded_src hW hT hmr hNZB hZ hX rfl (fun _ h => h) hdemB hσ hRR (hseeds M n s b hv) hT'
    (hk M n s hs) hsc

#print axioms B_src

/-- `B_src` gives `Backward.B_general` back (every source seeded, then forget the restriction). -/
theorem B_general_of_src {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractD P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) :=
  fun M n l s T hs hT' hsc hRR hv =>
    reachR_keep (B_src (σ := fun _ _ _ => true) hW hT hmr hNZB hZ hX hk hseeds hdemB
      (fun _ _ _ _ => rfl) M n l s T hs hT' hsc hRR hv)

#print axioms B_general_of_src

/-! ## Part 5. The iteration with forward seeds -/

/-- The program of forward run `k`: run 1 (`k = 0`) analyses `P`, run `k + 1` analyses `P` with
    the source seeds `σ k` (the hits of the backward run after run `k`). -/
def progSrc (P : Program) (σ : Nat → MethodId → Node → MicroEdge → Bool) : Nat → Program
  | 0     => P
  | k + 1 => keepSources P (σ k)

/-- The run sequence with forward seeds. Run 0 is the closure `D` of the full program (every
    source fires); run `k + 1` is the restricted closure of `keepSources P (σ k)`. -/
def runSeqSrc (P : Program) (counted : Acc → Bool) (Ls : Nat → Nat)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (dem : Nat → MethodId → DemandEdge → Prop) (emit : PFact → PFact → Option PFact)
    (sat : PFact → PFact → Bool) (restrict : PFact → AFact → DemandEdge → Option AFact)
    (recs : Nat → MethodId → PFact × AFact → Prop) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Nat → Obj → Prop
  | 0     => D P counted (Ls 0) policy1 sinks roots
  | k + 1 => DR (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emit sat restrict (recs k)
      sinks roots

/-- The reversed summary demand of a forward run computed on its own program is the one computed
    on `P` (the exits do not change). -/
theorem revSummaryDemand_progSrc {P : Program} {σ : Nat → MethodId → Node → MicroEdge → Bool}
    (k : Nat) (R : Obj → Prop) : revSummaryDemand (progSrc P σ k) R = revSummaryDemand P R := by
  cases k <;> rfl

/-- A witness of the program of a forward run is a witness of `P`. -/
theorem reachRD_progSrc {P : Program} {σ : Nat → MethodId → Node → MicroEdge → Bool} {k : Nat}
    {R : Obj → Prop} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRD (progSrc P σ k) R roots M n l) : ReachRD P R roots M n l := by
  cases k with
  | zero => exact h
  | succ k => exact reachRD_keep h

theorem progSrc_WF {P : Program} {σ : Nat → MethodId → Node → MicroEdge → Bool} (hW : P.WF)
    (k : Nat) : (progSrc P σ k).WF := by
  cases k with
  | zero => exact hW
  | succ k => exact keep_WF hW

section IterationSrc
variable {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
  {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}

/-- The invariant of the iteration with forward seeds: forward run `k` justifies the witness in
    its own program, and reports its vulnerability. -/
theorem iteration_src_invariant (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P)
    (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, revSummaryDemand (progSrc P σ k)
      (runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    (hσ : ∀ k M n e, srcHit P (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachRD (progSrc P σ k)
        (runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k) roots M n l ∧
      ∃ b, runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  induction k with
  | zero =>
    exact ⟨(reach_strongDD P counted (Ls 0) policy1 sinks roots hW
        (policy_applicable (fun _ => [])) hRe).1,
      Coverage.vuln_found P counted (Ls 0) policy1 sinks roots hW
        (policy_applicable (fun _ => [])) hRe hs hT' hsc⟩
  | succ k ih =>
    -- (b) the witness of forward run `k` is a witness of `P`, so contract B with seeds applies
    have hP := reachRD_progSrc ih.1
    have hdemB' : ∀ m d, revSummaryDemand P
        (runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k) m d → demB k m d :=
      fun m d h => hdemB k m d (by rw [revSummaryDemand_progSrc]; exact h)
    have hRR := B_src hW hT hmr hNZB hZ hX hk (hseeds k) hdemB' (hσ k) M n l s T hs hT' hsc hP ih.2
    -- (c) the demanded witness in `keepSources P (σ k)` is covered by forward run `k + 1`
    have hRR' := RCov.reachR_mono (hdem k) hRR
    have hW' : (keepSources P (σ k)).WF := keep_WF hW
    show ReachRD (keepSources P (σ k)) (DR (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM
        satI restrictU (recs k) sinks roots) roots M n l ∧
      ∃ b, DR (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI restrictU (recs k) sinks
        roots (.vuln M n s b)
    rw [RMain.runU_eq_S]
    have hE := RCov.emitOn_of_conc (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI
      restrictS (recs k) sinks roots RCore.emitM_contract_I RCore.emitM_copies
    -- (a) the run justifies the witness in its own program
    exact ⟨(reach_strongRD (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI restrictS
        (recs k) sinks roots hW' hE RCore.satI_contract RCore.restrictS_contract hRR').1,
      (RCov.vuln_foundR (keepSources P (σ k)) counted (Ls (k + 1)) (dem k) emitM satI restrictS
        (recs k) sinks roots hW' hE RCore.satI_contract RCore.restrictS_contract hRR' hs hT' hsc).1⟩

#print axioms iteration_src_invariant

/-- THE ITERATION THEOREM WITH FORWARD SEEDS. Run 1 analyses the full program; forward run `k + 1`
    fires only the unconditional sources in `σ k`, and `σ k` contains the source hits of the
    backward run after forward run `k` (which runs on the FULL reversed program, seeded at the sinks
    that forward run `k` reported, with a backward demand that contains the reversed summaries of
    forward run `k`, computed on its own program). If the demand of every forward run contains the
    hand-off of the backward run before it, every forward run reports every real vulnerability of
    `P`. The hypotheses on `P` are those of `Backward.iteration_general`. -/
theorem iteration_src (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P)
    (hX : ExitReach P roots)
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (σ : Nat → MethodId → Node → MicroEdge → Bool)
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, revSummaryDemand (progSrc P σ k)
      (runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    (hσ : ∀ k M n e, srcHit P (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) M n e → σ k M n e = true)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ApSpec.Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeqSrc P counted Ls σ dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) :=
  fun k => (iteration_src_invariant hW hT hmr hNZB hZ hX hk σ LB demB recsB seeds hdemB hseeds hdem
    hσ hRe hs hT' hsc k).2

#print axioms iteration_src

end IterationSrc

end ApSpec.FSeeds
