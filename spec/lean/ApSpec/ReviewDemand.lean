/-
  Focused review regressions for the fact-threaded cleaner mode of F73.
  `Before` archives the F72 mode and proves its whole-program counterexample.
  This file changes no AP operation or run rule.
  F75 supersedes its same-base spatial certificates. The different-base getter
  stays compatible; current base-cleaner checks are in BaseCleaner.
-/
import ApSpec.AbsClosure

namespace ApSpec.ReviewDemand
open ApSpec ApSpec.Handoff ApSpec.Abs ApSpec.Reverse

def st : Kind := .star Excl.empty
def cnt : Acc → Bool := fun _ => true
def x : PFact := ⟨1, [], .exact, .conc 1⟩
def p : PFact := ⟨3, [], .exact, .conc 1⟩
def r : PFact := ⟨2, [], .exact, .conc 1⟩
def jp : PFact := ⟨3, [], st, .star⟩
def cl : Cleaner := ⟨5, [], .atAndBelow, some 1⟩
def source : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, x)]⟩
def bind : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def back : MicroEdge := (⟨3, [], st, .star⟩, ⟨2, [], st, .star⟩)
def cz : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def call : Call := ⟨1, [1, 2], [bind, cz], [back]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 0 then 2 else 1,
  [(0, 0, .stmt source, 1), (0, 1, .call call, 2), (1, 0, .clean cl, 1)]⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, r)]
abbrev R1 := D P cnt 2 policy1 sinks [0]

/-- The earlier mode checked only the mark, ignoring unrelated cleaner bases. -/
def cleanMABBefore (cl : Cleaner) (l : Loc) : Bool :=
  match cl.mark with
  | none => true
  | some t => !(Nat.beq l.mark t)

/-- The old published-summary guard, before the propagated facts became part of the mode. -/
def starJBefore (P : Program) (R : Obj → Prop) (pub : Pub)
    (m : MethodId) (l1 l2 : Loc) : Prop :=
  ∃ j g g', R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ pub m j g g' ∧ j.mark = .star ∧
    j.covers l1 ∧ den j g'.fact l1 l2

/-- The approved disjoint mode uses the unchanged AP cleaner cell. -/
theorem disjoint_cleaner_keeps_fact {cl : Cleaner} {f : AFact}
    (h : cleanPos cl f.fact = .disjoint) : cleanRes cl f = ⟨[f], []⟩ := by
  unfold cleanRes
  rw [h]

theorem unrelated_cleaner : cleanPos cl jp = .disjoint ∧
    cleanRes cl ⟨jp, false⟩ = ⟨[⟨jp, false⟩], []⟩ ∧
    cl.cleansB ⟨3, [], 1⟩ = false ∧ cleanMABBefore cl ⟨3, [], 1⟩ = false := by
  exact ⟨by decide, rfl, by decide, by decide⟩

def S : LS where
  inits := [(0, zeroFact), (1, zeroFact), (1, jp)]
  edges := [(0, zeroFact, 0, ⟨zeroFact, false⟩),
    (0, zeroFact, 1, ⟨zeroFact, false⟩), (0, zeroFact, 1, ⟨x, false⟩),
    (0, zeroFact, 2, ⟨zeroFact, false⟩), (0, zeroFact, 2, ⟨r, false⟩),
    (1, zeroFact, 0, ⟨zeroFact, false⟩), (1, zeroFact, 1, ⟨zeroFact, false⟩),
    (1, jp, 0, ⟨jp, false⟩), (1, jp, 1, ⟨jp, false⟩)]
  addeds := [(1, zeroFact), (1, p)]
  reqs := []
  vulns := [(0, 2, r, false)]

theorem closed1 : ClosedD P cnt 2 sinks [0] S := by decide
theorem inv1 {o : Obj} (h : R1 o) : S.Inv o := closedD_sound P cnt 2 sinks [0] S closed1 h

theorem source_edge : R1 (.edge 0 zeroFact 1 ⟨x, false⟩) :=
  D.step (D.start (D.root (by decide))) (s := source) (by simp [P]) (by decide)

theorem get_added : R1 (.added 1 p) :=
  D.added (c := call) (e := bind) (a := ⟨p, false⟩) (n' := 2)
    source_edge (by simp [P]) (by simp [call]) (by decide)

theorem get_init : R1 (.init 1 jp) := D.initA get_added

theorem get_exit : R1 (.edge 1 jp 1 ⟨jp, false⟩) :=
  D.clean (D.start get_init) (cl := cl) (by simp [P]) (by decide)

theorem return_edge : R1 (.edge 0 zeroFact 2 ⟨r, false⟩) :=
  D.ret (c := call) (e1 := bind) (a := ⟨p, false⟩) (j := jp)
    (g := ⟨jp, false⟩) (r := ⟨p, false⟩) (e2 := back) (r' := ⟨r, false⟩)
    source_edge (by simp [P]) (by simp [call]) (by decide) get_init (by decide)
    get_exit (by decide) (by simp [call]) (by decide)

theorem found : R1 (.vuln 0 2 r false) :=
  D.vuln return_edge (by decide) (by decide)

theorem no_concrete_get_init : ∀ t, R1 (.init 1 ⟨3, [], .exact, .conc t⟩) → False := by
  intro t h
  have hi := inv1 h
  simp [LS.Inv, S, jp, zeroFact, zeroBase] at hi

theorem no_requests : ∀ M i t, ¬ R1 (.req M i t) := by
  intro M i t h
  exact List.not_mem_nil (inv1 h)

namespace Before

abbrev cleanMAB := cleanMABBefore
abbrev starJ := starJBefore

inductive FlowMA (P : Program) (ok : MethodId → Loc → Loc → Prop) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowMA P ok rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → StepMA s l l' →
      FlowMA P ok rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowMA P ok rc M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowMA P ok rc c.callee l1 (P.exit c.callee) l2 → ok c.callee l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowMA P ok rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.mark = .star → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowMA P ok rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → cleanMAB cl l = true → FlowMA P ok rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowMA P ok rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowMA P ok rc M l0 n' l

inductive FlowRDNA (P : Program) (R : Obj → Prop) (pub : Pub) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRDNA P R pub rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRDNA P R pub rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRDNA P R pub rc M l0 n' l
  | acall {M l0 n l n' c e1 e2 l1 l2 l3} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowMA P (starJ P R pub) rc c.callee l1 (P.exit c.callee) l2 → starJ P R pub c.callee l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P R pub rc M l0 n' l3
  | ccall {M l0 n l n' c e1 e2 l1 l2 l3 j g g' t} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRDNA P R pub rc c.callee l1 (P.exit c.callee) l2 →
      R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) → pub c.callee j g g' →
      j.mark = .conc t → j.covers l1 → den j g'.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P R pub rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P R pub rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRDNA P R pub rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRDNA P R pub rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRDNA P R pub rc M l0 n' l

/-- The output vulnerability witness with modes: its calls down enter an initial fact of `R` that
    covers the entry location, its flows are `FlowRDNA`. -/
inductive ReachRDNA (P : Program) (R : Obj → Prop) (pub : Pub) (rc : Recs) (roots : List MethodId) :
    MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRDNA P R pub rc M zeroLoc n l → ReachRDNA P R pub rc roots M n l
  | down {M n l n' c e l1 n2 l2 j} :
      ReachRDNA P R pub rc roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      R (.init c.callee j) → j.covers l1 →
      FlowRDNA P R pub rc c.callee l1 n2 l2 → ReachRDNA P R pub rc roots c.callee n2 l2

def Run1ContractA (P : Program) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (R1 : Obj → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l → Reach P roots M n l →
    ReachRDNA P R1 pubD (fun _ _ => False) roots M n l ∧ ∃ b, R1 (.vuln M n s b)


theorem no_mark_agnostic_getter {ok : MethodId → Loc → Loc → Prop} {rc : Recs}
    {l0 l : Loc} (h : FlowMA P ok rc 1 l0 1 l) (ht : l.mark = 1) : False := by
  cases h with
  | step _ he _ => simp [P] at he
  | pass _ he _ => simp [P] at he
  | call _ he _ _ _ _ _ _ => simp [P] at he
  | rcall _ he _ _ _ _ _ _ _ _ _ => simp [P] at he
  | clean _ he _ hm =>
    simp [P] at he
    rcases he with ⟨_, rfl⟩
    simp [cleanMAB, cleanMABBefore, cl, ht] at hm
  | filt _ he _ => simp [P] at he

theorem no_moded_root_sink {l0 l : Loc}
    (h : FlowRDNA P R1 pubD (fun _ _ => False) 0 l0 2 l)
    (hb : l.base = 2) (ht : l.mark = 1) : False := by
  cases h with
  | step _ he _ => simp [P] at he
  | pass _ he hm =>
    simp [P] at he
    rcases he with ⟨_, rfl⟩
    simp [call, memB, hb] at hm
  | acall _ he _ _ hf _ he2 hd2 =>
    simp [P] at he
    rcases he with ⟨_, rfl⟩
    simp [call] at he2
    subst he2
    have hm : l.mark = _ := hd2.2.2.2.1
    simp [back, MarkA.out] at hm
    exact no_mark_agnostic_getter hf (hm.symm.trans ht)
  | ccall _ he _ _ _ hj hg hpub hm _ hdg he2 hd2 =>
    simp [P] at he
    rcases he with ⟨_, rfl⟩
    simp [call] at he2
    subst he2
    have hi := inv1 hj
    have hi' := inv1 hg
    simp [LS.Inv, S, call, P] at hi hi'
    rcases hi' with hzero | hstar
    · rcases hzero with ⟨rfl, rfl⟩
      have hp := hpub
      simp [pubD] at hp
      subst hp
      have hh := hd2.1
      have hh' := hdg.2.1
      simp [back] at hh
      simp [zeroFact, zeroBase] at hh'
      exact (by decide : ¬ ((3 : Base) = 0)) (hh.symm.trans hh')
    · rcases hstar with ⟨rfl, rfl⟩
      simp [jp] at hm
  | rcall _ _ _ _ hr _ _ _ _ _ => exact hr
  | clean _ he _ => simp [P] at he
  | filt _ he _ => simp [P] at he

def lx : Loc := ⟨1, [], 1⟩
def lp : Loc := ⟨3, [], 1⟩
def lr : Loc := ⟨2, [], 1⟩

theorem source_pair : den zeroFact x zeroLoc lx := by
  exact ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
theorem bind_pair : den bind.1 bind.2 lx lp := by
  exact ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
theorem back_pair : den back.1 back.2 lp lr := by
  exact ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

theorem concrete_flow : Flow P 0 zeroLoc 2 lr :=
  Flow.call (c := call) (e1 := bind) (e2 := back) (n := 1) (n' := 2)
    (Flow.step (Flow.start 0 zeroLoc) (s := source) (n' := 1) (by simp [P])
      (Or.inr ⟨(zeroFact, x), by simp [source], source_pair⟩))
    (by simp [P]) (by simp [call]) bind_pair
    (Flow.clean (Flow.start 1 lp) (cl := cl) (by simp [P, call]) (by decide))
    (by simp [call]) back_pair

theorem real_sink : Reach P [0] 0 2 lr := Reach.root (by decide) concrete_flow

theorem no_moded_sink {M n : Nat} {l : Loc}
    (h : ReachRDNA P R1 pubD (fun _ _ => False) [0] M n l)
    (hm : M = 0) (hn : n = 2) (hb : l.base = 2) (ht : l.mark = 1) : False := by
  cases h with
  | root _ hf =>
    subst hm
    subst hn
    exact no_moded_root_sink hf hb ht
  | down _ he _ _ _ _ _ =>
    simp [P] at he
    rcases he with ⟨_, _, rfl, _⟩
    simp [call] at hm

theorem not_run1_contract_with_modes : ¬ Run1ContractA P [0] sinks R1 := by
  intro h
  obtain ⟨hr, _⟩ := h 0 2 lr r 1 (by decide) rfl
    (by exact ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩) real_sink
  exact no_moded_sink hr rfl rfl rfl rfl

end Before

#print axioms unrelated_cleaner
#print axioms found
#print axioms no_requests
#print axioms Before.concrete_flow
#print axioms Before.not_run1_contract_with_modes

/-- Accepting only another base repairs the first example but misses disjoint branches. -/
def cleanMABBaseOnly (cl : Cleaner) (l : Loc) : Bool :=
  !(Nat.beq l.base cl.base) || cleanMABBefore cl l

/-- This sink has one concrete location, so its whole-program contract has one witness. -/
theorem sink_location_unique {l : Loc} (h : r.covers l) : l = Before.lr := by
  obtain ⟨b, q, t⟩ := l
  simp [PFact.covers, r, tailI, MarkA.admits] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

/-- Executable certificate using the actual F73 mode and the run's published FLOW premise. -/
def corrected_getter_mode : ApSpec.Abs.FlowMA P cnt 2 (ApSpec.Abs.starJ P R1 pubD)
    (fun _ _ => False) 1 jp Before.lp 1 ⟨jp, false⟩ Before.lp :=
  ApSpec.Abs.FlowMA.clean
    (ApSpec.Abs.FlowMA.start 1 jp Before.lp rfl ⟨rfl, ⟨[], rfl, rfl⟩, trivial⟩)
    (cl := cl) (by simp [P]) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

theorem corrected_moded_flow : ApSpec.Abs.FlowRDNA P cnt 2 R1 pubD
    (fun _ _ => False) 0 zeroLoc 2 Before.lr :=
  ApSpec.Abs.FlowRDNA.acall (c := call) (e1 := bind) (e2 := back) (n := 1) (n' := 2)
    (j := jp) (g := ⟨jp, false⟩) (g' := ⟨jp, false⟩)
    (ApSpec.Abs.FlowRDNA.step (ApSpec.Abs.FlowRDNA.start 0 zeroLoc)
      (s := source) (n' := 1) (by simp [P])
      (Or.inr ⟨(zeroFact, x), by simp [source], Before.source_pair⟩))
    (by simp [P]) (by simp [call]) Before.bind_pair corrected_getter_mode
    get_init get_exit rfl rfl ⟨rfl, ⟨[], rfl, rfl⟩, trivial⟩
    ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
    (by simp [call]) Before.back_pair

theorem corrected_moded_reach : ApSpec.Abs.ReachRDNA P cnt 2 R1 pubD
    (fun _ _ => False) [0] 0 2 Before.lr :=
  ApSpec.Abs.ReachRDNA.root (by decide) corrected_moded_flow

/-- The same concrete program satisfies the corrected actual run-1 contract. -/
theorem corrected_run1_contract_with_modes : ApSpec.Abs.Run1ContractA P cnt 2 [0] sinks R1 := by
  intro M n l s T hsk _ hcov _
  simp [sinks] at hsk
  rcases hsk with ⟨rfl, rfl, rfl⟩
  have hl := sink_location_unique hcov
  subst hl
  exact ⟨corrected_moded_reach, false, found⟩

#print axioms corrected_getter_mode
#print axioms corrected_run1_contract_with_modes

/-- The same location is covered by a narrow FLOW fact and by a coarse FLOW fact. A cleaner on
    another branch preserves only the narrow fact without asking for the mark. The proof mode
    therefore needs the propagated fact, not only the concrete witness location. -/
def spatialCleaner : Cleaner := ⟨5, [2], .exact, some 1⟩
def spatialNarrow : PFact := ⟨5, [1], st, .star⟩
def spatialCoarse : PFact := ⟨5, [], st, .star⟩
def spatialLoc : Loc := ⟨5, [1, 3], 1⟩
def spatialExcluded : PFact := ⟨5, [], .star (.set [2]), .star⟩

theorem same_base_disjoint_flow :
    spatialNarrow.covers spatialLoc ∧ spatialCoarse.covers spatialLoc ∧
    cleanPos spatialCleaner spatialNarrow = .disjoint ∧
    cleanPos spatialCleaner spatialCoarse = .part ∧
    cleanRes spatialCleaner ⟨spatialNarrow, false⟩ = ⟨[⟨spatialNarrow, false⟩], []⟩ ∧
    (cleanRes spatialCleaner ⟨spatialCoarse, false⟩).reqs = [1] ∧
    spatialCleaner.cleansB spatialLoc = false ∧
    cleanMABBaseOnly spatialCleaner spatialLoc = false := by
  refine ⟨⟨rfl, ⟨[3], rfl, rfl⟩, trivial⟩,
    ⟨rfl, ⟨[1, 3], rfl, rfl⟩, trivial⟩, by decide, by decide, rfl,
    by decide, by decide, by decide⟩

theorem coarse_flow_loses_the_uncleaned_mark :
    (cleanRes spatialCleaner ⟨spatialCoarse, false⟩).facts =
      [⟨⟨5, [], st, .starEx [1]⟩, false⟩] ∧
    ¬ (⟨5, [], st, .starEx [1]⟩ : PFact).covers spatialLoc := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Bool.noConfusion h.2.2

/-- An exclusion on the propagated fact also makes the cleaner disjoint. -/
theorem same_base_excluded_branch_disjoint :
    spatialExcluded.covers spatialLoc ∧
    cleanPos spatialCleaner spatialExcluded = .disjoint ∧
    cleanRes spatialCleaner ⟨spatialExcluded, false⟩ =
      ⟨[⟨spatialExcluded, false⟩], []⟩ := by
  exact ⟨⟨rfl, ⟨[1, 3], rfl, rfl⟩, trivial⟩, by decide, rfl⟩

/-- The actual mode accepts narrow and excluded facts and rejects the coarse fact. -/
theorem actual_fact_dependent_cleaner_modes :
    ApSpec.Abs.cleanMAB spatialCleaner ⟨spatialNarrow, false⟩ spatialLoc = true ∧
    ApSpec.Abs.cleanMAB spatialCleaner ⟨spatialExcluded, false⟩ spatialLoc = true ∧
    ApSpec.Abs.cleanMAB spatialCleaner ⟨spatialCoarse, false⟩ spatialLoc = false := by
  exact ⟨by decide, by decide, by decide⟩

def spatialP : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .clean spatialCleaner, 1)]⟩

/-- A same-base disjoint branch has an executable trace from its selected narrow premise. -/
def narrow_abstract_trace (ok : AbstractOK) (rc : Recs) :
    ApSpec.Abs.FlowMA spatialP cnt 2 ok rc 0 spatialNarrow spatialLoc 1
      ⟨spatialNarrow, false⟩ spatialLoc :=
  ApSpec.Abs.FlowMA.clean
    (ApSpec.Abs.FlowMA.start 0 spatialNarrow spatialLoc rfl same_base_disjoint_flow.1)
    (cl := spatialCleaner) (by simp [spatialP]) (by decide) (by decide) (by decide)
    ⟨rfl, rfl, trivial, rfl, trivial, [3], [3], rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

/-- The trace cannot replace a coarse starting premise by the narrow fact at the cleaner. -/
theorem coarse_abstract_trace_cannot_pass {ok : AbstractOK} {rc : Recs} {f : AFact}
    (h : ApSpec.Abs.FlowMA spatialP cnt 2 ok rc 0 spatialCoarse spatialLoc 1 f spatialLoc) :
    False := by
  cases h with
  | step _ he => simp [spatialP] at he
  | pass _ he => simp [spatialP] at he
  | call _ he => simp [spatialP] at he
  | rcall _ he => simp [spatialP] at he
  | clean hf he _ hm =>
    simp [spatialP] at he
    rcases he with ⟨rfl, rfl⟩
    cases hf with
    | start =>
      have hz : ApSpec.Abs.cleanMAB spatialCleaner (startFact spatialCoarse) spatialLoc = false :=
        by decide
      rw [hz] at hm
      cases hm
    | step _ he => simp [spatialP] at he
    | pass _ he => simp [spatialP] at he
    | call _ he => simp [spatialP] at he
    | rcall _ he => simp [spatialP] at he
    | clean _ he => simp [spatialP] at he
    | filt _ he => simp [spatialP] at he
  | filt _ he => simp [spatialP] at he

#print axioms same_base_disjoint_flow
#print axioms coarse_flow_loses_the_uncleaned_mark
#print axioms same_base_excluded_branch_disjoint
#print axioms actual_fact_dependent_cleaner_modes
#print axioms narrow_abstract_trace
#print axioms coarse_abstract_trace_cannot_pass

/-- Generic AP call bindings can add a path. Interpreter-generated bindings into the callee
    have empty paths and cannot do this; that shape is a separate hypothesis of W3. -/
def growingBinding : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [4, 5], st, .star⟩)
def grownAdded : PFact := ⟨3, [4, 5], .exact, .conc 1⟩
def shallowDemand : PFact := ⟨3, [4], .any, .conc 1⟩

theorem binding_in_needs_non_growth_condition :
    (applyEdge ⟨x, false⟩ growingBinding.1 growingBinding.2).facts = [⟨grownAdded, false⟩] ∧
    emitW shallowDemand grownAdded = some grownAdded ∧
    (startFact grownAdded).fact.path.length = 2 ∧ shallowDemand.path.length = 1 := by
  exact ⟨rfl, by decide, rfl, rfl⟩

#print axioms binding_in_needs_non_growth_condition

/-- A concrete premise keeps concrete final marks even if other premises of F72 are abstract. -/
def ConcEdge : Obj → Prop
  | .edge _ i _ f => (∃ t, i.mark = .conc t) → ∃ t, f.fact.mark = .conc t
  | _ => True

theorem backward_concrete_premise {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool} {o : Obj}
    (hsd : ∀ M n s, (M, n, s) ∈ seeds → ∃ t, s.mark = .conc t)
    (h : DBA Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    ConcEdge o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro hc
    obtain ⟨t, ht⟩ := hc
    exact ⟨t, by rw [startFact_mark, ht]⟩
  | @step M i n f n' s f' _ _ hf ih =>
    intro hc
    obtain ⟨t, ht⟩ := ih hc
    exact transfer_mark_conc ht hf
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ ha _ _ _ _ _ hr _ hr' ihF _ _ =>
    intro hc
    obtain ⟨t, ht⟩ := ihF hc
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨t3, by rw [limitF_mark, h3]⟩
  | @retRec M i n f n' c e1 a j g r e2 r' _ _ _ ha _ _ hr _ hr' ihF =>
    intro hc
    obtain ⟨t, ht⟩ := ihF hc
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht ha
    obtain ⟨t2, h2⟩ := applySummary_mark_conc h1 hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact ⟨t3, by rw [limitF_mark, h3]⟩
  | vuln => trivial
  | @clean M i n f n' cl f' _ _ hf ih =>
    intro hc
    obtain ⟨t, ht⟩ := ih hc
    exact cleanRes_mark_conc ht hf
  | filt _ _ _ ih => exact ih
  | zpass => exact fun _ => ⟨zeroMark, rfl⟩
  | zin => trivial
  | @seed M n s hs _ _ =>
    obtain ⟨t, ht⟩ := hsd M n s hs
    exact fun _ => ⟨t, by rw [limitF_mark]; exact ht⟩
  | @zret M n n' c g r e2 r' _ _ _ _ hr _ hr' _ _ =>
    obtain ⟨t2, h2⟩ := applySummary_mark_conc (a := Backward.zeroAF) (t := zeroMark) rfl hr
    obtain ⟨t3, h3⟩ := applyEdge_mark_conc h2 hr'
    exact fun _ => ⟨t3, by rw [limitF_mark, h3]⟩

theorem backward_zero_premise_concrete {Pb : Program} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
    {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {seeds : List (MethodId × Node × PFact)} {zbind : Bool} {M n} {f : AFact}
    (hsd : ∀ M n s, (M, n, s) ∈ seeds → ∃ t, s.mark = .conc t)
    (h : DBA Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.edge M zeroFact n f)) :
    ∃ t, f.fact.mark = .conc t := backward_concrete_premise hsd h ⟨zeroMark, rfl⟩

#print axioms backward_zero_premise_concrete

end ApSpec.ReviewDemand
