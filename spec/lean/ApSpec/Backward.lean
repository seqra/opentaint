/-
  ApSpec.Backward — the BACKWARD RUN of the bidirectional analysis (the user's design).

  The forward runs are `D` (run 1) and the restricted closure `DR` (the later runs). Between two
  forward runs a backward run computes the demand of the next forward run. This file models the
  backward run as the user designed it and checks it.

  The design (Part 1, the closure `DB`):
    * the rules of `DR` on the reversed program `Pb = Program.rev P` (the reversed statements,
      calls, cleaners and filters), with the backward field limit `L` and the backward demand
      (the reversed summaries of the previous forward run);
    * the backward run starts at every ROOT with the zero fact (`root`, `start`: at the forward
      exit of the root, the entry of the reversed method);
    * the zero fact passes over every call (`zpass`) and ENTERS every callee through its own
      binding `zero.* → zero.*` (`zin`): from the caller's call node into the callee's forward
      EXIT. This binding is not a reversed forward binding (the forward zero binding goes into the
      callee; its plain reversal goes up, from the callee's forward entry to the caller);
    * the SINK rule (`seed`): where the zero fact reaches the statement of a seeded sink, a
      zero-to-fact edge to the requirement (the sink pattern, cut to the field limit);
    * the BALANCED return (`zret`): a zero-premise backward edge at the callee's forward entry
      (a zero-premise backward summary) is applied at a call site where the caller's zero fact
      entered the callee, through the reversed binding into the callee (`c.fromCallee` of the
      reversed call).
  The flag `zbind` switches `zin` and `zret` on (the user's design) or off (the plain reversal,
  Part 7). The seeds are a parameter: the checks use the sinks of the vulnerabilities that forward
  run 1 reported, which are all the sinks of programs 1 and 2 (`seeds1_reported`,
  `seeds2_reported`); the general theorems need only that every REPORTED sink is seeded
  (`B_fragment_rep`, `B_general`), so seeding every sink (`B_fragment`) is a special case.

  The hand-off (Part 2, `demOf`): a backward summary `jb → gb` (non-zero premise) gives the
  forward demand edge `(D-c = gb, D-p = jb)`, a zero-premise backward edge at the forward entry
  gives `(gb, none)`, and the zero demand `(zero, none)` is accepted in every method.

  Main results:
    * Part 3. `BackwardContractRep` (contract B for the REPORTED vulnerabilities only),
      `rep_of_B`, and the iteration theorems `iteration_sound_rep`, `iteration_sound_M_rep`.
    * Part 4. The fragment theorem: if no call binds anything back, the backward run satisfies
      contract B (`B_fragment`, every sink seeded) and `BackwardContractRep` for every seeding that
      contains the reported sinks (`B_fragment_rep`), for every backward demand, field limit and
      record set; end to end: `iteration_fragment`. Added hypotheses: the zero fact is kept by
      every instruction (`ZeroKept`), and every node reachable from the entry of its method reaches
      the exit of its method (`ExitReach`, for the methods of the program: roots and callees).
    * Part 5. Program 1 (`RCases.P1`): the complete backward closure (`inv_b1`); the hand-off is
      EXACTLY `RCases.dem1M`, the zero demand, and one demand edge of the root (`dem1_exact`), for
      every backward demand and record set; forward run 3 reports the vulnerability (`p1_found`).
      Program 1 is in the fragment (`p1_reachR_fragment`, the second route).
    * Part 6. Program 2 (`RCases.P2`): forward run 1 (field limit 1) computed completely
      (`inv_r1`); the backward run restricted by ITS reversed summaries (`inv_b2`) hands off
      EXACTLY `RCases.dem2M`, the zero demand, and one demand edge of the root (`dem2_exact`);
      forward run 3 reports the vulnerability (`p2_found`).
    * Part 7. Without the zero binding into the callee (the plain reversal) the backward run loses
      program 1 (`lost_plain`, `B_fails_plain`), also when the forward run binds the zero into the
      callees and its binding is reversed plainly (`lost_plain_z`).
    * Part 8. The general case (calls that bind back). `BackwardContractRep` is too weak there: its
      hypothesis does not fix the mark at the exit of a call that returns, and the mark-aware
      backward emission needs it (counterexample `B_rep_fails_general` on program 2). The
      den-aware contract `BackwardContractD` (the hypothesis `ReachRD`: each call that returns is
      justified by a summary whose pair relation contains the concrete pair) is weaker than
      `BackwardContractRep` (`repD_of_rep`), every forward run provides its hypothesis
      (`reach_strongRD`, `reach_strongDD`), so the iteration needs only it (`iteration_sound_D`,
      `iteration_sound_M_D`); the backward run of the user's design satisfies it for every
      forward run `Rk` (`B_general`); end to end: `iteration_general`. Added hypothesis: no call
      binds the zero base back (`NoZeroBack`). Program 2 instance: `p2_reachR_general`.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.RestrictedMain
import ApSpec.RestrictedCases
import ApSpec.Reverse

namespace ApSpec.Backward
open ApSpec ApSpec.Reverse

/-! ## Part 1. The backward closure -/

/-- The zero fact as a final fact in the normal layer (the start fact of the zero premise). -/
def zeroAF : AFact := ⟨zeroFact, false⟩

theorem startFact_zero : startFact zeroFact = zeroAF := rfl

section Closure
variable (Pb : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact))
  (zbind : Bool)

/-- The backward run on the reversed program `Pb`: the rules of `DR` (first block), and the zero
    rules of the user's design (second block). `roots` are the FORWARD roots: the zero fact starts
    at their forward exits (`Pb.entry`). `seeds` are the seeded sinks. `zbind = true` is the user's
    design (the zero binding into the callee and the balanced return of zero-premise summaries);
    `zbind = false` is the plain reversal. The backward run is given no forward sinks
    (`sinks = []` in every use): its sink rule is `seed`. -/
inductive DB : Obj → Prop where
  | root {M} : M ∈ roots → DB (.init M zeroFact)
  | start {M i} : DB (.init M i) → DB (.edge M i (Pb.entry M) (startFact i))
  | step {M i n f n' s f'} :
      DB (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      f' ∈ (transfer counted L s f).facts → DB (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      DB (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      t ∈ (transfer counted L s f).reqs → DB (.req M i t)
  | pass {M i n f n' c} :
      DB (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      memB f.fact.base c.touched = false → DB (.edge M i n' f)
  | added {M i n f n' c e a} :
      DB (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DB (.added c.callee a.fact)
  | initR {m a d j} :
      DB (.added m a) → demand m d → emit d.din a = some j → DB (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      DB (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DB (.init c.callee j) →
      DB (.edge c.callee j (Pb.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DB (.edge M i n' (limitF counted L r'))
  -- a persisted record: as `DR.retRec`, it applies by `sat` OR by `applicable`
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      DB (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DB (.edge M i n' (limitF counted L r'))
  | reqSink {M i n f s t} :
      DB (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      DB (.req M i t)
  | answer {M i t a} :
      DB (.req M i t) → DB (.added M a) → a.mark = .conc t →
      overlapB a i = true → DB (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DB (.req m j t) → DB (.edge M ic n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DB (.req M ic t)
  | vuln {M i n f s} :
      DB (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DB (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DB (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      f' ∈ (cleanRes cl f).facts → DB (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      DB (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      t ∈ (cleanRes cl f).reqs → DB (.req M i t)
  | filt {M i n f n' b may} :
      DB (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ Pb.edges →
      (f.fact.base = b → may f.fact.path = true) → DB (.edge M i n' f)
  -- the zero fact passes over every call
  | zpass {M n n' c} :
      DB (.edge M zeroFact n zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DB (.edge M zeroFact n' zeroAF)
  -- the zero fact enters every callee through its own binding `zero.* → zero.*`: from the call
  -- node into the callee's backward entry (its forward exit), where `start` continues it
  | zin {M n n' c} : zbind = true →
      DB (.edge M zeroFact n zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DB (.init c.callee zeroFact)
  -- the sink rule: where the zero fact reaches a seeded sink statement, a zero-to-fact edge to
  -- the requirement (the sink pattern; a result, so the backward field limit applies)
  | seed {M n s} : (M, n, s) ∈ seeds → DB (.edge M zeroFact n zeroAF) →
      DB (.edge M zeroFact n (limitF counted L ⟨s, false⟩))
  -- the balanced return: a zero-premise backward summary of the callee (an edge at its backward
  -- exit, the forward entry) is applied to the zero fact of the caller at the call site where that
  -- zero entered the callee, and goes through the reversed binding into the callee
  -- (`c.fromCallee` of the reversed call) to the caller's backward target node
  | zret {M n n' c g r e2 r'} : zbind = true →
      DB (.edge M zeroFact n zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DB (.edge c.callee zeroFact (Pb.exit c.callee) g) →
      r ∈ (applySummary zeroAF zeroFact g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DB (.edge M zeroFact n' (limitF counted L r'))

end Closure

/-! ## Part 2. The hand-off to the next forward run

In forward orientation: `D-c` is the backward conclusion at the forward entry (the backward exit
`Pb.exit M`), `D-p` is the backward premise (at the forward exit). A zero-premise backward edge
does not reach the forward exit: `D-p = none`. The zero demand `(zero, none)` is accepted in
every method. -/

def demOf (Pb : Program) (R : Obj → Prop) (M : MethodId) (d : DemandEdge) : Prop :=
  d = ⟨zeroFact, none⟩ ∨
  (∃ g, R (.edge M zeroFact (Pb.exit M) g) ∧ d = ⟨g.fact, none⟩) ∨
  (∃ jb gb, R (.init M jb) ∧ jb ≠ zeroFact ∧ R (.edge M jb (Pb.exit M) gb) ∧
    d = ⟨gb.fact, some jb⟩)

/-- The demand that a forward run passes to the backward run: its summaries, reversed. Every
    forward summary `(j, some g)` gives the backward demand edge `(D-c = g, D-p = j)` (the
    backward entry pattern is the forward exit fact). A forward `(j, none)` has no backward entry
    pattern and is not passed (the zero rules replace it). -/
def revSummaryDemand (P : Program) (R : Obj → Prop) (m : MethodId) (d : DemandEdge) : Prop :=
  ∃ j g, summaryDemand P R m ⟨j, some g⟩ ∧ d = ⟨g, some j⟩

/-! ## Part 3. The weaker contract B and the iteration theorem

The backward run is seeded at the sinks of the REPORTED vulnerabilities, but `BackwardContract`
quantifies over every sink witness that the summaries demand. The iteration theorem needs only the
reported ones: by the induction hypothesis the forward run has reported every real vulnerability. -/

/-- Contract B for the reported vulnerabilities only. -/
def BackwardContractRep (P : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (Rk : Obj → Prop)
    (dnext : MethodId → DemandEdge → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachR P (summaryDemand P Rk) roots M n l → (∃ b, Rk (.vuln M n s b)) →
    ReachR P dnext roots M n l

/-- Contract B gives the weaker contract. -/
theorem rep_of_B {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
    {Rk : Obj → Prop} {dnext : MethodId → DemandEdge → Prop}
    (h : BackwardContract P roots sinks Rk dnext) : BackwardContractRep P roots sinks Rk dnext :=
  fun M n l s T hs hT hc hr _ => h M n l s T hs hT hc hr

#print axioms rep_of_B

section Iteration
open RCov
variable {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

theorem iteration_invariant_rep (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContractRep P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachR P (summaryDemand P (runSeq P counted Ls dem emit sat restrict recs sinks roots k))
      roots M n l ∧ ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) := by
  intro k
  induction k with
  | zero =>
    exact ⟨reach_to_reachR P counted (Ls 0) policy1 sinks roots hwf
        (policy_applicable (fun _ => [])) hRe,
      Coverage.vuln_found P counted (Ls 0) policy1 sinks roots hwf
        (policy_applicable (fun _ => [])) hRe hs hT hsc⟩
  | succ k ih =>
    obtain ⟨hv, hRR⟩ := vuln_foundR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k)
      sinks roots hwf (hE k) hS hR (hB k M n l s T hs hT hsc ih.1 ih.2) hs hT hsc
    exact ⟨hRR, hv⟩

#print axioms iteration_invariant_rep

/-- THE ITERATION THEOREM with the weaker contract: contract B is needed only for the reported
    vulnerabilities. Every forward run of the sequence reports every real vulnerability. -/
theorem iteration_sound_rep (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContractRep P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) :=
  fun k => (iteration_invariant_rep hwf hE hS hR hB hRe hs hT hsc k).2

#print axioms iteration_sound_rep

end Iteration

/-- THE ITERATION THEOREM for the spec rules (`emitM`, `satI`, `restrictU`) with the weaker
    contract. -/
theorem iteration_sound_M_rep {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF)
    (hB : ∀ k, BackwardContractRep P roots sinks
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [RMain.runSeqU_eq_S k]
  refine iteration_sound_rep (emit := emitM) (sat := satI) (restrict := restrictS) hwf
    (fun k => RCov.emitOn_of_conc P counted (Ls (k + 1)) (dem k) emitM satI restrictS (recs k)
      sinks roots RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract (fun k' => ?_) hRe hs hT hsc k
  rw [← RMain.runSeqU_eq_S k']
  exact hB k'

#print axioms iteration_sound_M_rep

/-! ## Part 4. Contract B on the fragment with no binding back

The FRAGMENT: no call binds anything back (`c.fromCallee = []` for every call). Then a sink
witness is a chain of calls DOWN (a call that returns carries no flow back), and every demand edge
that the next forward run needs is a zero-premise backward edge at a forward entry. The backward
run of the user's design gives them all: the zero fact reaches the sink node (it starts at the
root's exit, passes every instruction, and enters every callee), the sink rule seeds the
requirement there, the reversed statements carry it to the forward entry of its method, and the
balanced return brings it to the call site in the caller, and so on up to the root.

Added hypotheses (both hold for programs 1 and 2):
  * `ZeroKept P`: the zero fact passes every instruction backward (a statement that touches the
    zero base regenerates it, no cleaner is on the zero base, a filter on the zero base admits
    the empty path). The zero rules of the design cover the calls (`zpass`, `zin`).
  * `ExitReach P`: every node reachable from the entry of its method reaches the exit of its
    method. This is the user's "every forward-reachable instruction is also backward reachable"
    (the implementation wires non-returning code to the exit). The concrete `Flow` does not need
    it; the backward run does, because its zero fact starts at the forward EXIT. -/

/-- No call binds anything back. -/
def NoBack (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → c.fromCallee = []

/-- The micro edges of every statement are mark-reversible. -/
def StmtsMarkRev (P : Program) : Prop :=
  ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → ∀ e, e ∈ s.edges → MarkRev e.1 e.2

/-- The zero fact is kept by every instruction that is not a call. -/
structure ZeroKept (P : Program) : Prop where
  stmt : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    memB zeroBase s.touched = true → (zeroFact, zeroFact) ∈ s.edges
  clean : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase
  filt : ∀ M n b may n', (M, n, Instr.filt b may, n') ∈ P.edges → b = zeroBase → may [] = true

/-- A path of CFG edges of `M` (any instruction) from `a`. -/
inductive CfgPath (P : Program) (M : MethodId) (a : Node) : Node → Prop where
  | refl : CfgPath P M a a
  | step {b c ins} : CfgPath P M a b → (M, b, ins, c) ∈ P.edges → CfgPath P M a c

/-- The method `M` is a root or the callee of a call (a method of the program, as opposed to an
    unused method identifier). -/
def Called (P : Program) (roots : List MethodId) (M : MethodId) : Prop :=
  M ∈ roots ∨ ∃ M' n c n', (M', n, Instr.call c, n') ∈ P.edges ∧ c.callee = M

/-- Every node reachable from the entry of its method reaches the exit of its method (for every
    method of the program). -/
def ExitReach (P : Program) (roots : List MethodId) : Prop :=
  ∀ M n, Called P roots M → CfgPath P M (P.entry M) n → CfgPath P M n (P.exit M)

/-! ### Small lemmas -/

theorem mem_applyAll {c x : AFact} {e : MicroEdge} :
    ∀ {es : List MicroEdge}, e ∈ es → x ∈ (applyEdge c e.1 e.2).facts →
      x ∈ (applyAll c es).facts
  | [], he, _ => by cases he
  | e' :: es, he, hx => by
    show x ∈ (applyEdge c e'.1 e'.2).facts ++ (applyAll c es).facts
    cases he with
    | head => exact List.mem_append_left _ hx
    | tail _ h => exact List.mem_append_right _ (mem_applyAll h hx)

theorem limitF_zero (counted : Acc → Bool) (L : Nat) : limitF counted L zeroAF = zeroAF := rfl

theorem den_zero : den zeroFact zeroAF.fact zeroLoc zeroLoc :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

/-- A reversed statement keeps the zero fact. -/
theorem zero_stmt {s : Stmt} (h : memB zeroBase s.touched = true → (zeroFact, zeroFact) ∈ s.edges)
    (counted : Acc → Bool) (L : Nat) : zeroAF ∈ (transfer counted L (Stmt.rev s) zeroAF).facts := by
  unfold transfer
  cases ht : memB zeroAF.fact.base (Stmt.rev s).touched with
  | false => exact List.Mem.head _
  | true =>
    show zeroAF ∈ (applyAll zeroAF (Stmt.rev s).edges).facts.map (limitF counted L)
    refine List.mem_map.mpr ⟨zeroAF, ?_, limitF_zero counted L⟩
    cases hs : memB zeroBase s.touched with
    | true =>
      have he : revEdge zeroFact zeroFact ∈ (Stmt.rev s).edges :=
        List.mem_append_left _ (List.mem_map.mpr ⟨_, h hs, rfl⟩)
      exact mem_applyAll he (by decide)
    | false =>
      have hts : memB zeroBase (targets s) = true := by
        have h2 : memB zeroBase (s.touched ++ targets s) = true := ht
        rw [memB_append, hs, Bool.false_or] at h2
        exact h2
      have hf : (!memB zeroBase s.touched) = true := by rw [hs]; rfl
      have he : idEdge zeroBase ∈ (Stmt.rev s).edges :=
        List.mem_append_right _
          (List.mem_map.mpr ⟨zeroBase, List.mem_filter.mpr ⟨mem_of_memB hts, hf⟩, rfl⟩)
      exact mem_applyAll he (by decide)

/-- A cleaner off the zero base keeps the zero fact. -/
theorem zero_clean {cl : Cleaner} (h : cl.base ≠ zeroBase) :
    zeroAF ∈ (cleanRes cl zeroAF).facts := by
  have hb : Nat.beq zeroAF.fact.base cl.base = false := by
    cases hb : Nat.beq zeroAF.fact.base cl.base with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb).symm h
  have hp : cleanPos cl zeroAF.fact = .disjoint := by
    unfold cleanPos
    rw [hb]
    rfl
  unfold cleanRes
  rw [hp]
  exact List.Mem.head _

/-- A flow reaches its node along a CFG path from the entry. -/
theorem flow_cfg {P : Program} {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : Flow P M l0 n l) : CfgPath P M (P.entry M) n := by
  induction h with
  | start => exact CfgPath.refl
  | step _ he _ ih => exact CfgPath.step ih he
  | pass _ he _ ih => exact CfgPath.step ih he
  | call _ he _ _ _ _ _ ih _ => exact CfgPath.step ih he
  | clean _ he _ ih => exact CfgPath.step ih he
  | filt _ he _ ih => exact CfgPath.step ih he

/-- The node of a witness is reachable from the entry of its method. -/
theorem reach_cfg {P : Program} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : Reach P roots M n l) : CfgPath P M (P.entry M) n := by
  cases h with
  | root _ hfl => exact flow_cfg hfl
  | down _ _ _ _ hfl => exact flow_cfg hfl

/-- The method of a witness is a method of the program. -/
theorem reach_called {P : Program} {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : Reach P roots M n l) : Called P roots M := by
  cases h with
  | root hM _ => exact Or.inl hM
  | @down M0 n0 _ n0' c _ _ _ _ _ hE _ _ _ => exact Or.inr ⟨M0, n0, c, n0', hE, rfl⟩

/-- In the fragment a concrete flow is demanded by every demand (it has no call that returns). -/
theorem flowR_of_flow {P : Program} (hnb : NoBack P) {dem : MethodId → DemandEdge → Prop}
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (h : Flow P M l0 n l) :
    FlowR P dem M l0 n l := by
  induction h with
  | start M l0 => exact FlowR.start M l0
  | step _ he hs ih => exact FlowR.step ih he hs
  | pass _ he hb ih => exact FlowR.pass ih he hb
  | call _ he _ _ _ he2 _ _ _ =>
    rw [hnb _ _ _ _ he] at he2
    cases he2
  | clean _ he hc ih => exact FlowR.clean ih he hc
  | filt _ he hf ih => exact FlowR.filt ih he hf

/-- A seed covers every location of its sink pattern (a sink pattern has the tail `$` or `[any]`
    and a concrete mark). -/
theorem seed_den {s : PFact} {l : Loc} {T : Mark} (hT : s.mark = .conc T)
    (hk : s.kind = .exact ∨ s.kind = .any) (hc : s.covers l) : den zeroFact s zeroLoc l := by
  obtain ⟨hb, ⟨τ, hp, ht⟩, hm⟩ := hc
  refine ⟨rfl, hb, rfl, ?_, ?_, [], τ, rfl, hp, rfl, ?_⟩
  · rw [hT] at hm ⊢
    exact hm
  · rw [hT]; trivial
  · rcases hk with hk | hk
    · rw [hk] at ht ⊢
      exact ht
    · rw [hk]; trivial

section Fragment
variable {P : Program} {counted : Acc → Bool} {L : Nat} {demand : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
  {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

/-! ### The zero fact reaches every node of a witness -/

/-- The zero fact goes backward along a CFG path. -/
theorem zero_path (hZ : ZeroKept P) {M : MethodId} {a b : Node} (hp : CfgPath P M a b) :
    DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
        (.edge M zeroFact b zeroAF) →
      DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
        (.edge M zeroFact a zeroAF) := by
  induction hp with
  | refl => exact id
  | @step b c ins _ he ih =>
    intro h
    apply ih
    cases ins with
    | stmt s => exact DB.step h (mem_rev_stmt he) (zero_stmt (hZ.stmt _ _ _ _ he) counted L)
    | call c' => exact DB.zpass h (mem_rev_call he)
    | clean cl => exact DB.clean h (mem_rev_clean he) (zero_clean (hZ.clean _ _ _ _ he))
    | filt b' may => exact DB.filt h (mem_rev_filt he) (fun hb => hZ.filt _ _ _ _ _ he hb.symm)

/-- The zero premise of a method starts at its forward exit. -/
theorem zero_exit {M : MethodId}
    (h : DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.init M zeroFact)) :
    DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.edge M zeroFact (P.exit M) zeroAF) :=
  DB.start h

/-- Every method of a witness has the zero premise in the backward run (the zero enters every
    callee through its own binding). -/
theorem zero_init (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots) (hzb : zbind = true)
    (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.init M zeroFact) := by
  induction hRe with
  | root hM _ => exact DB.root (hroots _ hM)
  | @down M n l n' c e l1 n2 l2 hRe0 hE _ _ _ ih =>
    have hz := zero_path (counted := counted) (L := L) (demand := demand) (emit := emit)
      (sat := sat) (restrict := restrict) (recs := recs) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ (hX M n' (reach_called hRe0) (CfgPath.step (reach_cfg hRe0) hE))
      (zero_exit ih)
    exact DB.zin (c := Call.rev c) hzb hz (mem_rev_call hE)

/-- The zero fact is at every node of a witness. -/
theorem zero_at (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots) (hzb : zbind = true)
    (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.edge M zeroFact n zeroAF) :=
  zero_path hZ (hX M n (reach_called hRe) (reach_cfg hRe)) (zero_exit (zero_init hZ hX hzb hroots hRe))

/-! ### The backward segment and the balanced return -/

/-- BACKWARD SEGMENT COVERAGE (zero premise, no call that returns): a forward flow of `M` from
    the entry location `l0` to `(n, l)`, and a concrete zero-premise backward edge at `n` that
    covers `l`, give a concrete zero-premise backward edge at the forward entry that covers
    `l0`. -/
theorem seg_cover (hW : P.WF) (hmr : StmtsMarkRev P) (hnb : NoBack P)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ f, DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
        (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l → (∃ t, f.fact.mark = .conc t) →
      ∃ f', DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
        (.edge M zeroFact (P.entry M) f') ∧ den zeroFact f'.fact zeroLoc l0 ∧
        ∃ t, f'.fact.mark = .conc t := by
  induction hfl with
  | start M l0 => exact fun f h hd hc => ⟨f, h, hd, hc⟩
  | @step M l0 n1 l1 n' l' s _ he hst ih =>
    intro f h hd hc
    have hEr : (M, n', Instr.stmt (Stmt.rev s), n1) ∈ (Program.rev P).edges := mem_rev_stmt he
    have hrs : (Stmt.rev s).step l' l1 := Stmt.rev_step_sound (hmr M n1 s n' he) hst
    obtain ⟨t, ht⟩ := hc
    rcases transfer_sound (counted := counted) (L := L) (rev_touched s) hd hrs with
      ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ih r (DB.step h hEr hr) hdr (transfer_mark_conc ht hr)
    · exact absurd ht (habs t)
  | @pass M l0 n1 l1 n' c _ he hb ih =>
    intro f h hd hc
    have hEr : (M, n', Instr.call (Call.rev c), n1) ∈ (Program.rev P).edges := mem_rev_call he
    have hb' : memB f.fact.base (Call.rev c).touched = false := by
      show memB f.fact.base c.touched = false
      rw [← hd.2.1]
      exact hb
    exact ih f (DB.pass h hEr hb') hd hc
  | call _ he _ _ _ he2 _ _ _ =>
    rw [hnb _ _ _ _ he] at he2
    cases he2
  | @clean M l0 n1 l1 n' cl _ he hcl ih =>
    intro f h hd hc
    have hEr : (M, n', Instr.clean cl, n1) ∈ (Program.rev P).edges := mem_rev_clean he
    obtain ⟨t, ht⟩ := hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · exact ih r (DB.clean h hEr hr) hdr (cleanRes_mark_conc ht hr)
    · exact absurd ht (habs t)
  | @filt M l0 n1 l1 n' b may _ he hmay ih =>
    intro f h hd hc
    have hEr : (M, n', Instr.filt b may, n1) ∈ (Program.rev P).edges := mem_rev_filt he
    have hff : f.fact.base = b → may f.fact.path = true := by
      intro hfb
      obtain ⟨_, hb1, _, _, _, σ, τ, _, hp1, _, _⟩ := hd
      have hm := hmay (hb1.trans hfb)
      rw [hp1] at hm
      exact hW.filtPrefix _ _ _ _ _ he _ _ hm
    exact ih f (DB.filt h hEr hff) hd hc

#print axioms seg_cover

/-- THE BALANCED RETURN mirrors a forward call step down. A concrete zero-premise backward edge
    of the callee at its forward entry that covers the callee entry location `l1` of the call
    step, and the caller's zero fact at the call node, give a concrete zero-premise backward edge
    at the forward pre-call node that covers the caller location `l`. -/
theorem zret_descent (hW : P.WF) (hT : BindTargetsStar P) (hzb : zbind = true)
    {M : MethodId} {n n' : Node} {c : Call} {e : MicroEdge} {l l1 : Loc} {f : AFact}
    (hE : (M, n, Instr.call c, n') ∈ P.edges) (he : e ∈ c.toCallee) (hd1 : den e.1 e.2 l l1)
    (hz : DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.edge M zeroFact n' zeroAF))
    (hf : DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.edge c.callee zeroFact (P.entry c.callee) f))
    (hdf : den zeroFact f.fact zeroLoc l1) (hcf : ∃ t, f.fact.mark = .conc t) :
    ∃ g, DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
      (.edge M zeroFact n g) ∧ den zeroFact g.fact zeroLoc l ∧ (∃ t, g.fact.mark = .conc t) ∧
      Invariant.Legal g := by
  have _ := hcf
  have hEr : (M, n', Instr.call (Call.rev c), n) ∈ (Program.rev P).edges := mem_rev_call hE
  have her : revEdge e.1 e.2 ∈ (Call.rev c).fromCallee := List.mem_map.mpr ⟨e, he, rfl⟩
  have hmr : MarkRev e.1 e.2 := markRev_star ((hT M n c n' hE).1 e he)
  have hdr : den (revEdge e.1 e.2).1 (revEdge e.1 e.2).2 l1 l := revEdge_sound hmr hd1
  have hstar : (revEdge e.1 e.2).1.mark = .star :=
    (rev_WF hW hT).fromStar M n' (Call.rev c) n hEr _ her
  -- the zero-premise summary applied to the caller's zero fact
  obtain ⟨r, hr, hdr0⟩ : ∃ r, r ∈ (applySummary zeroAF zeroFact f).facts ∧
      den zeroFact r.fact zeroLoc l1 := by
    rcases applySummary_sound den_zero hdf with h | ⟨habs, _⟩
    · exact h
    · exact absurd rfl (habs zeroMark)
  obtain ⟨t, ht⟩ := applySummary_mark_conc (a := zeroAF) (t := zeroMark) rfl hr
  -- the reversed binding into the callee, back to the caller
  rcases applyEdge_sound hdr0 hdr with ⟨r', hr', hdr'⟩ | ⟨_, hq⟩
  · refine ⟨_, DB.zret hzb hz hEr hf hr her hr', limitF_sound hdr', ?_,
      Invariant.limitF_Legal (Invariant.applyEdge_Legal hr')⟩
    obtain ⟨t', ht'⟩ := applyEdge_mark_conc ht hr'
    exact ⟨t', by rw [limitF_mark]; exact ht'⟩
  · rw [applyEdge_reqs_of_star hstar] at hq
    cases hq

#print axioms zret_descent

/-- The induction over the calls down: a concrete zero-premise backward edge at `(M, n)` that
    covers the end location of a witness gives the witness demanded by the hand-off of the
    backward run. -/
theorem reach_of_db (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P) (hnb : NoBack P)
    (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots) (hzb : zbind = true)
    (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    ∀ f, DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind
        (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l → (∃ t, f.fact.mark = .conc t) →
      ReachR P (demOf (Program.rev P)
        (DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind))
        roots M n l := by
  induction hRe with
  | root hM hfl => exact fun _ _ _ _ => ReachR.root hM (flowR_of_flow hnb hfl)
  | @down M n l n' c e l1 n2 l2 hRe0 hE he hd1 hfl ih =>
    intro f h hd hc
    obtain ⟨f', h', hd', hc'⟩ := seg_cover hW hmr hnb hfl f h hd hc
    have hz := zero_path (counted := counted) (L := L) (demand := demand) (emit := emit)
      (sat := sat) (restrict := restrict) (recs := recs) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ (hX M n' (reach_called hRe0) (CfgPath.step (reach_cfg hRe0) hE))
      (zero_exit (zero_init hZ hX hzb hroots hRe0))
    obtain ⟨g, hg, hdg, hcg, _⟩ := zret_descent hW hT hzb hE he hd1 hz h' hd' hc'
    have hdem : demOf (Program.rev P)
        (DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind)
        c.callee ⟨f'.fact, none⟩ := Or.inr (Or.inl ⟨f', h', rfl⟩)
    exact ReachR.down (ih g hg hdg hcg) hE he hd1 hdem (den_covers_final hd')
      (flowR_of_flow hnb hfl)

#print axioms reach_of_db

/-- Every real sink witness whose sink is seeded is demanded by the backward run (for every
    backward demand, field limit and record set). -/
theorem demanded_fragment (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hnb : NoBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots) (hzb : zbind = true)
    (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hseed : (M, n, s) ∈ seeds)
    (hT' : s.mark = .conc T) (hk : s.kind = .exact ∨ s.kind = .any) (hsc : s.covers l) :
    ReachR P (demOf (Program.rev P)
      (DB (Program.rev P) counted L demand emit sat restrict recs sinksB rootsB seeds zbind))
      roots M n l :=
  reach_of_db hW hT hmr hnb hZ hX hzb hroots hRe _
    (DB.seed hseed (zero_at hZ hX hzb hroots hRe))
    (limitF_sound (seed_den hT' hk hsc)) ⟨T, by rw [limitF_mark]; exact hT'⟩

#print axioms demanded_fragment

end Fragment

/-- CONTRACT B ON THE FRAGMENT (every sink seeded). The backward run of the user's design, seeded
    at every sink and started at the forward roots, satisfies contract B, for every backward
    demand, field limit and record set. -/
theorem B_fragment {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hnb : NoBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (Rk : Obj → Prop) {counted : Acc → Bool} {L : Nat} {demand : MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContract P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demand emit sat restrict recs sinksB roots sinks true)) := by
  intro M n l s T hs hT' hsc hRR
  exact demanded_fragment hW hT hmr hnb hZ hX rfl (fun _ h => h) (RCov.reachR_reach hRR) hs
    hT' (hk M n s hs) hsc

#print axioms B_fragment

/-- THE WEAKER CONTRACT ON THE FRAGMENT (only the reported sinks seeded). Every seeding that
    contains the sinks of the vulnerabilities that the forward run `Rk` reported satisfies
    `BackwardContractRep`. So it does not matter for the theorems whether every sink or only the
    reported ones are seeded. -/
theorem B_fragment_rep {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hnb : NoBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ seeds)
    {counted : Acc → Bool} {L : Nat} {demand : MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractRep P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demand emit sat restrict recs sinksB roots seeds true)) := by
  intro M n l s T hs hT' hsc hRR hv
  obtain ⟨b, hv⟩ := hv
  exact demanded_fragment hW hT hmr hnb hZ hX rfl (fun _ h => h) (RCov.reachR_reach hRR)
    (hseeds M n s b hv) hT' (hk M n s hs) hsc

#print axioms B_fragment_rep

/-- THE ITERATION ON THE FRAGMENT, end to end: if the demand of every forward run contains the
    hand-off of a backward run of the user's design (any backward demand, field limit and record
    set) that is seeded at least at the sinks the previous forward run reported, every forward run
    reports every real vulnerability. -/
theorem iteration_fragment {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hnb : NoBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hseeds : ∀ k M n s b,
      RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) :=
  iteration_sound_M_rep hW (fun k M' n' l' s' T' hs' hT'' hc' hr' hv' =>
    RCov.reachR_mono (hdem k)
      (B_fragment_rep hW hT hmr hnb hZ hX hk (hseeds k) M' n' l' s' T' hs' hT'' hc' hr' hv'))
    hRe hs hT' hsc

#print axioms iteration_fragment

/-! ## Part 5. Program 1 (`RCases.P1`): the backward run produces exactly `dem1M`

```
root():  x.g.h.f.k.z = source();  c(x);         // method 0: 0 -src-> 1 -call c-> 2
c(x):    y = x.g.h;  m(y);                       // method 1: 0 -rd-> 1 -call m-> 2
m(arg):  sink(arg.f.k.z);                        // method 2: sink at node 0 (entry = exit)
```
The backward run (field limit 2) starts at the root `0` with the zero fact at its forward exit `2`.
The zero passes over the call of `c` and enters `c` at its forward exit; there it passes over the
call of `m` and enters `m`. At the sink of `m` the sink rule seeds `(arg,.f.k,[any],T)`
(`arg.f.k.z` cut to 2). This zero-premise edge is at the forward entry of `m`: the demand of `m`.
The balanced return brings it to `(y,.f.k,[any],T)` before the call in `c`, and the reversed
`y = x.g.h` gives `(x,.g.h,[any],T)` at the forward entry of `c`: the demand of `c`. The balanced
return brings that to the root. No call binds back, so the reversed calls bind nothing into the
callee except the zero: the backward demand and the backward records are never used. -/

/-- The reversed program 1. -/
def Pb1 : Program := Program.rev RCases.P1

theorem Pb1_edges : Pb1.edges =
    [(0, 1, .stmt (Stmt.rev RCases.src), 0), (0, 2, .call (Call.rev RCases.callC), 1),
     (1, 1, .stmt (Stmt.rev RCases.rd), 0), (1, 2, .call (Call.rev RCases.callM), 1)] := rfl

theorem hb1_src : (0, 1, Instr.stmt (Stmt.rev RCases.src), 0) ∈ Pb1.edges := by
  rw [Pb1_edges]; exact List.Mem.head _
theorem hb1_c : (0, 2, Instr.call (Call.rev RCases.callC), 1) ∈ Pb1.edges := by
  rw [Pb1_edges]; exact List.Mem.tail _ (List.Mem.head _)
theorem hb1_rd : (1, 1, Instr.stmt (Stmt.rev RCases.rd), 0) ∈ Pb1.edges := by
  rw [Pb1_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hb1_m : (1, 2, Instr.call (Call.rev RCases.callM), 1) ∈ Pb1.edges := by
  rw [Pb1_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- The zero fact in the demand layer: the requirement `(x,.g.h,[any],T)` reached the source. -/
def Zd : AFact := ⟨zeroFact, true⟩
/-- The requirement `(x,.g.h,[any],T)`. -/
def xgh : PFact := ⟨1, [2, 3], .any, .conc 1⟩
def Xg : AFact := ⟨xgh, true⟩
/-- The requirement `(y,.f.k,[any],T)` before the call of `m`. -/
def Yb1 : AFact := ⟨⟨2, [1, 4], .any, .conc 1⟩, true⟩
/-- The seed `(arg,.f.k,[any],T)`: the sink pattern `arg.f.k.z` cut to the field limit 2. -/
def argfk : PFact := ⟨3, [1, 4], .any, .conc 1⟩
def Sd1 : AFact := ⟨argfk, true⟩

/-- The backward run of program 1 (the user's design, `zbind = true`; or the plain reversal). -/
abbrev B1 (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    (zb : Bool) : Obj → Prop :=
  DB Pb1 RCases.cnt 2 demB emitM satI restrictU recsB [] [0] RCases.sinks1 zb

/-! ### The objects of the backward run, derived -/

section Derive1
variable (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)

theorem b1_r0 : B1 demB recsB true (.init 0 zeroFact) := DB.root (List.Mem.head _)
theorem b1_e02 : B1 demB recsB true (.edge 0 zeroFact 2 zeroAF) := DB.start (b1_r0 demB recsB)
/-- The zero enters `c`. -/
theorem b1_i1 : B1 demB recsB true (.init 1 zeroFact) :=
  DB.zin (c := Call.rev RCases.callC) rfl (b1_e02 demB recsB) hb1_c
theorem b1_e12 : B1 demB recsB true (.edge 1 zeroFact 2 zeroAF) := DB.start (b1_i1 demB recsB)
/-- The zero enters `m`. -/
theorem b1_i2 : B1 demB recsB true (.init 2 zeroFact) :=
  DB.zin (c := Call.rev RCases.callM) rfl (b1_e12 demB recsB) hb1_m
theorem b1_e20 : B1 demB recsB true (.edge 2 zeroFact 0 zeroAF) := DB.start (b1_i2 demB recsB)
/-- The sink rule: the seed at the sink of `m`, at its forward entry. -/
theorem b1_s20 : B1 demB recsB true (.edge 2 zeroFact 0 Sd1) :=
  DB.seed (s := RCases.sink1) (List.Mem.head _) (b1_e20 demB recsB)
/-- The balanced return in `c`: `(y,.f.k,[any],T)` before the call of `m`. -/
theorem b1_y11 : B1 demB recsB true (.edge 1 zeroFact 1 Yb1) :=
  DB.zret (c := Call.rev RCases.callM) (r := Sd1) (r' := Yb1) rfl (b1_e12 demB recsB) hb1_m
    (b1_s20 demB recsB) (by decide) (List.Mem.head _) (by decide)
/-- `y = x.g.h` reversed: `(x,.g.h,[any],T)` at the forward entry of `c`. -/
theorem b1_x10 : B1 demB recsB true (.edge 1 zeroFact 0 Xg) :=
  DB.step (b1_y11 demB recsB) hb1_rd (by decide)
/-- The balanced return in the root. -/
theorem b1_x01 : B1 demB recsB true (.edge 0 zeroFact 1 Xg) :=
  DB.zret (c := Call.rev RCases.callC) (r := Xg) (r' := Xg) rfl (b1_e02 demB recsB) hb1_c
    (b1_x10 demB recsB) (by decide) (List.Mem.head _) (by decide)
theorem b1_x00 : B1 demB recsB true (.edge 0 zeroFact 0 Xg) :=
  DB.step (b1_x01 demB recsB) hb1_src (by decide)

end Derive1

/-! ### The complete closure of the backward run -/

def initsB1 : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (2, zeroFact)]
def edgesB1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, zeroAF), (0, zeroFact, 1, zeroAF), (0, zeroFact, 1, Xg),
   (0, zeroFact, 0, zeroAF), (0, zeroFact, 0, Zd), (0, zeroFact, 0, Xg),
   (1, zeroFact, 2, zeroAF), (1, zeroFact, 1, zeroAF), (1, zeroFact, 1, Yb1),
   (1, zeroFact, 0, zeroAF), (1, zeroFact, 0, Xg),
   (2, zeroFact, 0, zeroAF), (2, zeroFact, 0, Sd1)]

/-- Every object of the backward run of program 1 is in the lists: no added fact, no request, no
    vulnerability. -/
def InvB1 : Obj → Prop
  | .init M i => (M, i) ∈ initsB1
  | .edge M i n f => (M, i, n, f) ∈ edgesB1
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvB1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsB1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesB1))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

theorem rev1C_to : (Call.rev RCases.callC).toCallee = [] := rfl
theorem rev1M_to : (Call.rev RCases.callM).toCallee = [] := rfl

/-- THE COMPLETE BACKWARD CLOSURE OF PROGRAM 1 (the user's design), for every backward demand
    and every set of backward records. -/
theorem inv_b1 (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    {o : Obj} (h : B1 demB recsB true o) : InvB1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsB1, InvB1 (.edge x.1 x.2 (Pb1.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).facts,
          InvB1 (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB1, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd) x.2.2.2).facts,
              InvB1 (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB1, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB1, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev RCases.callC).touched = false →
            InvB1 (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesB1, x.1 = 1 → x.2.2.1 = 2 →
              memB x.2.2.2.fact.base (Call.rev RCases.callM).touched = false →
                InvB1 (.edge 1 x.2.1 1 x.2.2.2))
              (1, i, 2, f) ih rfl rfl hm
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he; cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he; cases he
          | tail _ hE => cases hE
  | initR _ _ _ ih => exact ih.elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 _ _ _ _ _ _ _ _ _ _ _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he1; cases he1
          | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 _ _ _ _ _ _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he1; cases he1
          | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => decide
          | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => decide
          | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesB1, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev RCases.callC).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB1 (.edge 0 zeroFact 1 (limitF RCases.cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ y ∈ edgesB1, y.1 = 2 → y.2.1 = zeroFact → y.2.2.1 = 0 →
              ∀ r ∈ (applySummary zeroAF zeroFact y.2.2.2).facts,
              ∀ e2 ∈ (Call.rev RCases.callM).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
                InvB1 (.edge 1 zeroFact 1 (limitF RCases.cnt 2 r')))
              (2, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
          | tail _ hE => cases hE

#print axioms inv_b1

/-! ### The hand-off of program 1, exactly -/

/-- The zero demand. -/
def zeroDem : DemandEdge := ⟨zeroFact, none⟩

/-- Every demand edge of the hand-off (zero premise, at a forward entry). -/
def demList1 : List (MethodId × DemandEdge) :=
  [(0, zeroDem), (0, ⟨xgh, none⟩), (1, zeroDem), (1, ⟨xgh, none⟩), (2, zeroDem), (2, ⟨argfk, none⟩)]

theorem demList1_cases {m : MethodId} {d : DemandEdge} (h : (m, d) ∈ demList1) :
    RCases.dem1M m d ∨ d = zeroDem ∨ (m = 0 ∧ d = ⟨xgh, none⟩) := by
  cases h with
  | head => exact Or.inr (Or.inl rfl)
  | tail _ h => cases h with
    | head => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | tail _ h => cases h with
      | head => exact Or.inr (Or.inl rfl)
      | tail _ h => cases h with
        | head => exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        | tail _ h => cases h with
          | head => exact Or.inr (Or.inl rfl)
          | tail _ h => cases h with
            | head => exact Or.inl (Or.inr ⟨rfl, rfl⟩)
            | tail _ h => cases h

/-- PROGRAM 1, EXACTLY. The hand-off of the backward run is `RCases.dem1M` (the demand of `c`:
    `((x,.g.h,[any],T), none)`; of `m`: `((arg,.f.k,[any],T), none)`), the zero demand, and the
    edge `((x,.g.h,[any],T), none)` of the root (where the requirement reached the source; a root
    is never entered through the demand). For every backward demand and every set of backward
    records. -/
theorem dem1_exact (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    (m : MethodId) (d : DemandEdge) :
    demOf Pb1 (B1 demB recsB true) m d ↔
      RCases.dem1M m d ∨ d = zeroDem ∨ (m = 0 ∧ d = ⟨xgh, none⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, _, _⟩)
    · exact Or.inr (Or.inl h)
    · exact demList1_cases ((by decide : ∀ x ∈ edgesB1, x.2.1 = zeroFact → x.2.2.1 = 0 →
        (x.1, (⟨x.2.2.2.fact, none⟩ : DemandEdge)) ∈ demList1)
        (m, zeroFact, 0, g) (inv_b1 demB recsB hg) rfl rfl)
    · exact absurd ((by decide : ∀ x ∈ initsB1, x.2 = zeroFact) (m, jb) (inv_b1 demB recsB hjb))
        hne
  · rintro ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | rfl | ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨Xg, b1_x10 demB recsB, rfl⟩)
    · exact Or.inr (Or.inl ⟨Sd1, b1_s20 demB recsB, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Xg, b1_x00 demB recsB, rfl⟩)

#print axioms dem1_exact

/-- In particular `RCases.dem1M` is inside the hand-off. -/
theorem dem1M_sub (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop) :
    ∀ m d, RCases.dem1M m d → demOf Pb1 (B1 demB recsB true) m d :=
  fun m d h => (dem1_exact demB recsB m d).mpr (Or.inl h)

/-- Forward run 3 (field limit 3, the spec rules) with the hand-off reports the vulnerability of
    program 1, for every backward demand, backward record set and forward record set. -/
theorem p1_found (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    (recs : MethodId → PFact × AFact → Prop) :
    ∃ b, DR RCases.P1 RCases.cnt 3 (demOf Pb1 (B1 demB recsB true)) emitM satI restrictU recs
      RCases.sinks1 [0] (.vuln 2 0 RCases.sink1 b) :=
  (RMain.vuln_found_M RCases.p1_wf (RCov.reachR_mono (dem1M_sub demB recsB) RCases.p1_reachR_M)
    (List.Mem.head _) rfl RCases.p1_sink_covers).1

#print axioms p1_found

/-! ### The seeds of program 1 are the sinks that forward run 1 reported -/

/-- A vulnerability object of run 1 is at a sink of the list. -/
theorem D_vuln_sink {P : Program} {counted : Acc → Bool} {L : Nat} {α : MethodId → PFact → PFact}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId} {o : Obj}
    (h : D P counted L α sinks roots o) :
    match o with
    | .vuln M n s _ => (M, n, s) ∈ sinks
    | _ => True := by
  induction h with
  | vuln _ hs _ _ => exact hs
  | _ => trivial

/-- Forward run 1 of program 1 (any field limit) reports exactly the seeded sinks. -/
theorem seeds1_reported (L1 : Nat) (x : MethodId × Node × PFact) :
    x ∈ RCases.sinks1 ↔ ∃ b, D RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0]
      (.vuln x.1 x.2.1 x.2.2 b) := by
  have hv : ∃ b, D RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0] (.vuln 2 0 RCases.sink1 b) :=
    Coverage.vuln_found RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0] RCases.p1_wf
      (policy_applicable (fun _ => [])) RCases.p1_reach (List.Mem.head _) rfl
      RCases.p1_sink_covers
  constructor
  · intro h
    cases h with
    | head => exact hv
    | tail _ h => cases h
  · rintro ⟨b, h⟩
    exact D_vuln_sink h

#print axioms seeds1_reported

/-! ### Program 1 is in the fragment: a second route through `demanded_fragment` -/

theorem p1_noBack : NoBack RCases.P1 := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head => rfl
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => rfl
        | tail _ hE => cases hE

theorem star_one {b b' : Base} {e : MicroEdge}
    (he : e ∈ [((⟨b, [], RCases.st, .star⟩ : PFact), (⟨b', [], RCases.st, .star⟩ : PFact))]) :
    e.2.mark = .star := by
  cases he with
  | head => rfl
  | tail _ he => cases he

theorem p1_bindStar : BindTargetsStar RCases.P1 := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head => exact ⟨fun _ he => star_one he, fun _ he => by cases he⟩
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ⟨fun _ he => star_one he, fun _ he => by cases he⟩
        | tail _ hE => cases hE

theorem p1_markRev : StmtsMarkRev RCases.P1 := by
  intro M n s n' hE e he
  cases hE with
  | head =>
    cases he with
    | head => exact Or.inr ⟨0, rfl⟩
    | tail _ he => cases he with
      | head => exact Or.inr ⟨0, rfl⟩
      | tail _ he => cases he
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        cases he with
        | head => exact markRev_star rfl
        | tail _ he => cases he with
          | head => exact markRev_star rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

theorem p1_zeroKept : ZeroKept RCases.P1 where
  stmt := by
    intro M n s n' hE _
    cases hE with
    | head => exact List.Mem.head _
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact absurd ‹memB zeroBase RCases.rd.touched = true› (by decide)
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  clean := fun _ _ _ _ h => (RCases.p1_no_clean h).elim
  filt := fun _ _ _ _ _ h => (RCases.p1_no_filt h).elim

/-- The nodes of a method of program 1 that a CFG path from the entry reaches. -/
theorem p1_nodes {M n : Node} (h : CfgPath RCases.P1 M 0 n) : n = 0 ∨ n = 1 ∨ n = 2 := by
  induction h with
  | refl => exact Or.inl rfl
  | @step b c ins _ he _ =>
    cases he with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ he => cases he with
      | head => exact Or.inr (Or.inr rfl)
      | tail _ he => cases he with
        | head => exact Or.inr (Or.inl rfl)
        | tail _ he => cases he with
          | head => exact Or.inr (Or.inr rfl)
          | tail _ he => cases he

theorem p1_exitReach : ExitReach RCases.P1 [0] := by
  intro M n hM hp
  -- the methods of program 1: the root 0 and the callees 1, 2
  have hM' : M = 0 ∨ M = 1 ∨ M = 2 := by
    rcases hM with h | ⟨M', n0, c, n1, hE, rfl⟩
    · cases h with
      | head => exact Or.inl rfl
      | tail _ h => cases h
    · cases hE with
      | tail _ hE => cases hE with
        | head => exact Or.inr (Or.inl rfl)
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head => exact Or.inr (Or.inr rfl)
            | tail _ hE => cases hE
  have e00 : (0, 0, Instr.stmt RCases.src, 1) ∈ RCases.P1.edges := List.Mem.head _
  have e01 : (0, 1, Instr.call RCases.callC, 2) ∈ RCases.P1.edges :=
    List.Mem.tail _ (List.Mem.head _)
  have e10 : (1, 0, Instr.stmt RCases.rd, 1) ∈ RCases.P1.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have e11 : (1, 1, Instr.call RCases.callM, 2) ∈ RCases.P1.edges :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  rcases hM' with rfl | rfl | rfl
  · rcases p1_nodes hp with rfl | rfl | rfl
    · exact CfgPath.step (CfgPath.step CfgPath.refl e00) e01
    · exact CfgPath.step CfgPath.refl e01
    · exact CfgPath.refl
  · rcases p1_nodes hp with rfl | rfl | rfl
    · exact CfgPath.step (CfgPath.step CfgPath.refl e10) e11
    · exact CfgPath.step CfgPath.refl e11
    · exact CfgPath.refl
  · -- `m` has no edge: the path is empty
    have hn : n = 0 := by
      cases hp with
      | refl => rfl
      | step _ he => cases he with
        | tail _ he => cases he with
          | tail _ he => cases he with
            | tail _ he => cases he with
              | tail _ he => cases he
    subst hn
    exact CfgPath.refl

#print axioms p1_exitReach

/-- The general theorem applied to program 1 gives the same demanded witness. -/
theorem p1_reachR_fragment (demB : MethodId → DemandEdge → Prop)
    (recsB : MethodId → PFact × AFact → Prop) :
    ReachR RCases.P1 (demOf Pb1 (B1 demB recsB true)) [0] 2 0 ⟨3, [1, 4, 5], 1⟩ :=
  demanded_fragment RCases.p1_wf p1_bindStar p1_markRev p1_noBack p1_zeroKept p1_exitReach rfl
    (fun _ h => h) RCases.p1_reach (List.Mem.head _) rfl (Or.inl rfl) RCases.p1_sink_covers

#print axioms p1_reachR_fragment

/-- Program 1 with the backward demand of the real forward run 1 (field limit 1): its reversed
    summaries. -/
theorem dem1_exact_run1 (L1 : Nat) (m : MethodId) (d : DemandEdge) :
    demOf Pb1 (B1 (revSummaryDemand RCases.P1 (D RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0]))
        (fun _ _ => False) true) m d ↔
      RCases.dem1M m d ∨ d = zeroDem ∨ (m = 0 ∧ d = ⟨xgh, none⟩) :=
  dem1_exact _ _ m d

/-! ## Part 6. Program 2 (`RCases.P2`): forward run 1 → backward run 2 → forward run 3

```
root():  x.h.i.f.k.z = source();  r = c(x);  sink(r.f.k.z);   // method 0, sink at node 2
c(arg):  ret = arg.h.i;  return ret;                           // method 1
```
Forward run 1 (field limit 1) is computed completely (`inv_r1`). The backward run 2 (field limit
2) is restricted by the reversed summaries of forward run 1 (`revSummaryDemand`). Its zero fact
starts at the forward exit `2` of the root, which is the sink node: the sink rule seeds
`(r,.f.k,[any],T)`. The requirement enters `c` through the reversed binding back (`r.* → ret.*`),
the emission of the backward demand `((ret,.[any],*), D-p = (arg,.*,*))` gives the backward
premise `(ret,.f.k,[any],T)`, and the reversed `ret = arg.h.i` gives `(arg,.h.i,[any],T)` at the
forward entry of `c`: the backward summary `(ret,.f.k,[any],T) → (arg,.h.i,[any],T)`, the demand
`dem2M` of `c`. The zero also enters `c` (and passes it), which gives the zero demand. -/

/-- The reversed program 2. -/
def Pb2 : Program := Program.rev RCases.P2

theorem Pb2_edges : Pb2.edges =
    [(0, 1, .stmt (Stmt.rev RCases.src2), 0), (0, 2, .call (Call.rev RCases.callC2), 1),
     (1, 1, .stmt (Stmt.rev RCases.rd2), 0)] := rfl

theorem hb2_src : (0, 1, Instr.stmt (Stmt.rev RCases.src2), 0) ∈ Pb2.edges := by
  rw [Pb2_edges]; exact List.Mem.head _
theorem hb2_c : (0, 2, Instr.call (Call.rev RCases.callC2), 1) ∈ Pb2.edges := by
  rw [Pb2_edges]; exact List.Mem.tail _ (List.Mem.head _)
theorem hb2_rd : (1, 1, Instr.stmt (Stmt.rev RCases.rd2), 0) ∈ Pb2.edges := by
  rw [Pb2_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-! ### Forward run 1 of program 2, completely -/

/-- Forward run 1 of program 2 (field limit 1, the most abstract abstraction). -/
abbrev R1p := D RCases.P2 RCases.cnt 1 policy1 RCases.sinks2 [0]

/-- The initial fact of `c` in run 1: `(arg,.*,*)`. -/
def Jc : PFact := ⟨3, [], RCases.st, .star⟩
def Jcf : AFact := ⟨Jc, false⟩
/-- The exit fact of `c` in run 1: `(ret,.[any],*)`. -/
def Gc : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
/-- The root facts of run 1: the source cut to `(x,.h,[any],T)`, the result `(r,.[any],T)`. -/
def X1 : AFact := ⟨⟨1, [2], .any, .conc 1⟩, true⟩
def Rr1 : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩
/-- The added fact of `c` in run 1: `(arg,.h,[any],T)`. -/
def A1 : PFact := ⟨3, [2], .any, .conc 1⟩

def initsR1 : List (MethodId × PFact) := [(0, zeroFact), (1, Jc)]
def edgesR1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, zeroAF), (0, zeroFact, 1, zeroAF), (0, zeroFact, 1, X1),
   (0, zeroFact, 2, zeroAF), (0, zeroFact, 2, Rr1),
   (1, Jc, 0, Jcf), (1, Jc, 1, Jcf), (1, Jc, 1, Gc)]
def addedsR1 : List (MethodId × PFact) := [(1, A1)]

/-- Every object of forward run 1 of program 2 is in the lists (no request). -/
def InvR1 : Obj → Prop
  | .init M i => (M, i) ∈ initsR1
  | .edge M i n f => (M, i, n, f) ∈ edgesR1
  | .added M a => (M, a) ∈ addedsR1
  | .req _ _ _ => False
  | .vuln _ _ _ _ => True

instance : DecidablePred InvR1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsR1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesR1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsR1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable True)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 1 OF PROGRAM 2. -/
theorem inv_r1 {o : Obj} (h : R1p o) : InvR1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsR1,
      InvR1 (.edge x.1 x.2 (RCases.P2.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer RCases.cnt 1 RCases.src2 x.2.2.2).facts, InvR1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesR1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer RCases.cnt 1 RCases.rd2 x.2.2.2).facts, InvR1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer RCases.cnt 1 RCases.src2 x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesR1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer RCases.cnt 1 RCases.rd2 x.2.2.2).reqs, False)
            (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base RCases.callC2.touched = false → InvR1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ RCases.callC2.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvR1 (.added RCases.callC2.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addedsR1, InvR1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ RCases.callC2.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsR1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edgesR1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ RCases.callC2.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvR1 (.edge 0 x.2.1 2 (limitF RCases.cnt 1 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesR1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 RCases.sink2 = .none ∨ check x.2.1 x.2.2.2 RCases.sink2 = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ _ _ _ => trivial
  | clean _ hE _ _ => exact (RCases.p2_no_clean hE).elim
  | reqClean _ hE _ _ => exact (RCases.p2_no_clean hE).elim
  | filt _ hE _ _ => exact (RCases.p2_no_filt hE).elim

#print axioms inv_r1

/-- The reversed summaries of forward run 1: the backward demand of backward run 2. -/
def revDem2 : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, some zeroFact⟩), (0, ⟨Rr1.fact, some zeroFact⟩),
   (1, ⟨Jc, some Jc⟩), (1, ⟨Gc.fact, some Jc⟩)]

theorem revDem2_bound {m : MethodId} {d : DemandEdge} (h : revSummaryDemand RCases.P2 R1p m d) :
    (m, d) ∈ revDem2 := by
  obtain ⟨j, g, ⟨_, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · cases hgg
    exact (by decide : ∀ x ∈ edgesR1, x.2.2.1 = RCases.P2.exit x.1 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ revDem2) (m, j, _, g') (inv_r1 hg') rfl

#print axioms revDem2_bound

theorem r1_init_c : R1p (.init 1 Jc) := by
  have e0 : R1p (.edge 0 zeroFact 0 zeroAF) := D.start (D.root (List.Mem.head _))
  have e1 : R1p (.edge 0 zeroFact 1 X1) := D.step e0 (s := RCases.src2) RCases.Prog2.hE00 (by decide)
  have ad : R1p (.added 1 A1) :=
    D.added (c := RCases.callC2) (e := RCases.Prog2.bx) (a := ⟨A1, true⟩) e1 RCases.Prog2.hE01
      (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := RCases.cnt) (L := 1) (sinks := RCases.sinks2)
    (roots := [0]) (P := RCases.P2) ad
  have hp : policy1 1 A1 = Jc := by decide
  rw [hp] at h
  exact h

theorem r1_exit_c : R1p (.edge 1 Jc 1 Gc) :=
  D.step (D.start r1_init_c) (s := RCases.rd2) RCases.Prog2.hE10 (by decide)

/-- The backward demand edge of `c` that the backward run uses: `((ret,.[any],*), D-p = (arg,.*,*))`. -/
theorem revDem_c : revSummaryDemand RCases.P2 R1p 1 ⟨Gc.fact, some Jc⟩ :=
  ⟨Jc, Gc.fact, ⟨r1_init_c, Or.inr ⟨Gc, r1_exit_c, rfl⟩⟩, rfl⟩

/-! ### Backward run 2 of program 2, completely -/

/-- Backward run 2: the user's design on the reversed program 2, restricted by the reversed
    summaries of forward run 1, field limit 2, no backward records. -/
abbrev B2 : Obj → Prop :=
  DB Pb2 RCases.cnt 2 (revSummaryDemand RCases.P2 R1p) emitM satI restrictU (fun _ _ => False)
    [] [0] RCases.sinks2 true

/-- The seed `(r,.f.k,[any],T)` (`r.f.k.z` cut to 2). -/
def Sd2 : AFact := ⟨⟨2, [1, 4], .any, .conc 1⟩, true⟩
/-- The backward premise of `c`: `(ret,.f.k,[any],T)`. -/
def Jb2 : PFact := ⟨4, [1, 4], .any, .conc 1⟩
def Jb2t : AFact := ⟨Jb2, true⟩
/-- The backward conclusion of `c` at its forward entry: `(arg,.h.i,[any],T)`. -/
def Gb2 : AFact := ⟨⟨3, [2, 3], .any, .conc 1⟩, true⟩

def initsB2 : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jb2)]
def edgesB2 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, zeroAF), (0, zeroFact, 2, Sd2), (0, zeroFact, 1, zeroAF), (0, zeroFact, 1, Xg),
   (0, zeroFact, 0, zeroAF), (0, zeroFact, 0, Zd), (0, zeroFact, 0, Xg),
   (1, zeroFact, 1, zeroAF), (1, zeroFact, 0, zeroAF), (1, Jb2, 1, Jb2t), (1, Jb2, 0, Gb2)]
def addedsB2 : List (MethodId × PFact) := [(1, Jb2)]

def InvB2 : Obj → Prop
  | .init M i => (M, i) ∈ initsB2
  | .edge M i n f => (M, i, n, f) ∈ edgesB2
  | .added M a => (M, a) ∈ addedsB2
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvB2 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsB2))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesB2))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsB2))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN 2 OF PROGRAM 2 (the user's design). -/
theorem inv_b2 {o : Obj} (h : B2 o) : InvB2 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsB2, InvB2 (.edge x.1 x.2 (Pb2.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB2, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src2) x.2.2.2).facts,
          InvB2 (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB2, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd2) x.2.2.2).facts,
              InvB2 (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB2, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src2) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB2, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd2) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB2, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev RCases.callC2).touched = false →
            InvB2 (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB2, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev RCases.callC2).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvB2 (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ revDem2, ∀ y ∈ addedsB2, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvB2 (.init x.1 j))
      (m, d) (revDem2_bound hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB2, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev RCases.callC2).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsB2, y.1 = 1 →
          ∀ z ∈ edgesB2, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ revDem2, dd.1 = 1 → ∀ g' ∈ (restrictU y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Call.rev RCases.callC2).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB2 (.edge 0 x.2.1 1 (limitF RCases.cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (revDem2_bound hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesB2, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev RCases.callC2).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB2 (.edge 0 zeroFact 1 (limitF RCases.cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_b2

/-! ### The objects of backward run 2, derived -/

theorem b2_e02 : B2 (.edge 0 zeroFact 2 zeroAF) := DB.start (DB.root (List.Mem.head _))
/-- The sink rule at the root's forward exit. -/
theorem b2_s02 : B2 (.edge 0 zeroFact 2 Sd2) :=
  DB.seed (s := RCases.sink2) (List.Mem.head _) b2_e02
/-- The requirement enters `c` through the reversed binding back, and the backward demand emits
    the backward premise `(ret,.f.k,[any],T)`. -/
theorem b2_i1 : B2 (.init 1 Jb2) := by
  have ad : B2 (.added 1 Jb2) :=
    DB.added (c := Call.rev RCases.callC2) (e := revEdge RCases.Prog2.br.1 RCases.Prog2.br.2)
      (a := Jb2t) b2_s02 hb2_c (List.Mem.head _) (by decide)
  exact DB.initR ad revDem_c (by decide)
/-- The backward summary of `c`: `(ret,.f.k,[any],T) → (arg,.h.i,[any],T)`. -/
theorem b2_g1 : B2 (.edge 1 Jb2 0 Gb2) := DB.step (DB.start b2_i1) hb2_rd (by decide)
/-- The restricted backward summary is applied in the root: `(x,.h.i,[any],T)`. -/
theorem b2_x01 : B2 (.edge 0 zeroFact 1 Xg) :=
  DB.ret (c := Call.rev RCases.callC2) (e1 := revEdge RCases.Prog2.br.1 RCases.Prog2.br.2)
    (a := Jb2t) (j := Jb2) (g := Gb2) (d := ⟨Gc.fact, some Jc⟩) (g' := Gb2) (r := Gb2)
    (e2 := revEdge RCases.Prog2.bx.1 RCases.Prog2.bx.2) (r' := Xg) b2_s02 hb2_c (List.Mem.head _)
    (by decide) b2_i1 b2_g1 revDem_c (by decide) (by decide) (by decide) (List.Mem.head _)
    (by decide)
theorem b2_x00 : B2 (.edge 0 zeroFact 0 Xg) := DB.step b2_x01 hb2_src (by decide)

/-! ### The hand-off of program 2, exactly -/

/-- `dem2M`'s edge: `(D-c = (arg,.h.i,[any],T), D-p = (ret,.f.k,[any],T))`. -/
def dem2c : DemandEdge := ⟨Gb2.fact, some Jb2⟩

def demList2 : List (MethodId × DemandEdge) :=
  [(0, zeroDem), (0, ⟨xgh, none⟩), (1, zeroDem), (1, dem2c)]

theorem demList2_cases {m : MethodId} {d : DemandEdge} (h : (m, d) ∈ demList2) :
    RCases.dem2M m d ∨ d = zeroDem ∨ (m = 0 ∧ d = ⟨xgh, none⟩) := by
  cases h with
  | head => exact Or.inr (Or.inl rfl)
  | tail _ h => cases h with
    | head => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | tail _ h => cases h with
      | head => exact Or.inr (Or.inl rfl)
      | tail _ h => cases h with
        | head => exact Or.inl ⟨rfl, rfl⟩
        | tail _ h => cases h

/-- PROGRAM 2, EXACTLY. The hand-off of backward run 2 (restricted by the reversed summaries of
    the real forward run 1) is `RCases.dem2M` (the backward summary of `c`), the zero demand, and
    the edge `((x,.h.i,[any],T), none)` of the root. -/
theorem dem2_exact (m : MethodId) (d : DemandEdge) :
    demOf Pb2 B2 m d ↔ RCases.dem2M m d ∨ d = zeroDem ∨ (m = 0 ∧ d = ⟨xgh, none⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, hgb, rfl⟩)
    · exact Or.inr (Or.inl h)
    · exact demList2_cases ((by decide : ∀ x ∈ edgesB2, x.2.1 = zeroFact → x.2.2.1 = 0 →
        (x.1, (⟨x.2.2.2.fact, none⟩ : DemandEdge)) ∈ demList2)
        (m, zeroFact, 0, g) (inv_b2 hg) rfl rfl)
    · exact demList2_cases ((by decide : ∀ x ∈ initsB2, x.2 ≠ zeroFact →
        ∀ y ∈ edgesB2, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = 0 →
          (x.1, (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge)) ∈ demList2)
        (m, jb) (inv_b2 hjb) hne (m, jb, 0, gb) (inv_b2 hgb) rfl rfl rfl)
  · rintro (⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨Jb2, Gb2, b2_i1, by decide, b2_g1, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Xg, b2_x00, rfl⟩)

#print axioms dem2_exact

theorem dem2M_sub : ∀ m d, RCases.dem2M m d → demOf Pb2 B2 m d :=
  fun m d h => (dem2_exact m d).mpr (Or.inl h)

/-- THE CHAIN OF PROGRAM 2: forward run 1 → backward run 2 → forward run 3 (field limit 3, the
    spec rules) reports the vulnerability, for every forward record set. -/
theorem p2_found (recs : MethodId → PFact × AFact → Prop) :
    ∃ b, DR RCases.P2 RCases.cnt 3 (demOf Pb2 B2) emitM satI restrictU recs RCases.sinks2 [0]
      (.vuln 0 2 RCases.sink2 b) :=
  (RMain.vuln_found_M RCases.p2_wf (RCov.reachR_mono dem2M_sub RCases.p2_reachR_M)
    (List.Mem.head _) rfl RCases.p2_sink_covers).1

#print axioms p2_found

/-- Forward run 1 of program 2 (any field limit) reports exactly the seeded sinks. -/
theorem seeds2_reported (L1 : Nat) (x : MethodId × Node × PFact) :
    x ∈ RCases.sinks2 ↔ ∃ b, D RCases.P2 RCases.cnt L1 policy1 RCases.sinks2 [0]
      (.vuln x.1 x.2.1 x.2.2 b) := by
  have hv : ∃ b, D RCases.P2 RCases.cnt L1 policy1 RCases.sinks2 [0] (.vuln 0 2 RCases.sink2 b) :=
    Coverage.vuln_found RCases.P2 RCases.cnt L1 policy1 RCases.sinks2 [0] RCases.p2_wf
      (policy_applicable (fun _ => [])) RCases.p2_reach (List.Mem.head _) rfl
      RCases.p2_sink_covers
  constructor
  · intro h
    cases h with
    | head => exact hv
    | tail _ h => cases h
  · rintro ⟨b, h⟩
    exact D_vuln_sink h

#print axioms seeds2_reported

/-! ## Part 7. Without the zero binding into the callee, program 1 is lost

The plain reversal of the forward zero binding `zero.* → zero.*` (forward: caller → callee
entry) is a binding from the callee's forward entry UP to the caller: a `fromCallee` edge of the
reversed call. It is used only after a fact entered the callee, so with it the zero fact never
enters a callee (`zbind = false`: no `zin`, no `zret`). Then the zero never reaches the sink of
`m`, the sink rule never fires, and the hand-off is the zero demand only. Forward run 3 does not
report the real vulnerability of program 1 (`lost_plain`), so the weaker contract B fails
(`B_fails_plain`); compare `p1_found`. -/

def edgesB1p : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, zeroAF), (0, zeroFact, 1, zeroAF), (0, zeroFact, 0, zeroAF)]

def InvB1p : Obj → Prop
  | .init M i => (M, i) = (0, zeroFact)
  | .edge M i n f => (M, i, n, f) ∈ edgesB1p
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvB1p := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) = (0, zeroFact)))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesB1p))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

/-- The complete backward closure of program 1 without the zero binding into the callee. -/
theorem inv_b1_plain (demB : MethodId → DemandEdge → Prop)
    (recsB : MethodId → PFact × AFact → Prop) {o : Obj} (h : B1 demB recsB false o) :
    InvB1p o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ih
    decide
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).facts,
          InvB1p (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev RCases.callC).touched = false →
            InvB1p (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he; cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he; cases he
          | tail _ hE => cases hE
  | initR _ _ _ ih => exact ih.elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 _ _ _ _ _ _ _ _ _ _ _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he1; cases he1
          | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 _ _ _ _ _ _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1C_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1M_to] at he1; cases he1
          | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zpass M n n' c _ hE ih =>
    rw [Pb1_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | zin hzb _ _ _ => exact Bool.noConfusion hzb
  | @seed M n s hs _ ih =>
    cases hs with
    | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 2) _ ih rfl).elim
    | tail _ h => cases h
  | zret hzb _ _ _ _ _ _ _ _ => exact Bool.noConfusion hzb

#print axioms inv_b1_plain

/-- The hand-off of the plain reversal is the zero demand only. -/
theorem demOf_plain (demB : MethodId → DemandEdge → Prop) (recsB : MethodId → PFact × AFact → Prop)
    {m : MethodId} {d : DemandEdge} (h : demOf Pb1 (B1 demB recsB false) m d) : d = zeroDem := by
  rcases h with h | ⟨g, hg, rfl⟩ | ⟨jb, _, hjb, hne, _, _⟩
  · exact h
  · exact (by decide : ∀ x ∈ edgesB1p, x.2.2.1 = 0 → (⟨x.2.2.2.fact, none⟩ : DemandEdge) = zeroDem)
      (m, zeroFact, 0, g) (inv_b1_plain demB recsB hg) rfl
  · exact absurd (Prod.mk.inj (inv_b1_plain demB recsB hjb)).2 hne

#print axioms demOf_plain

/-! ### Forward run 3 of program 1 with the zero demand only -/

def initsF1 : List (MethodId × PFact) := [(0, zeroFact)]
def edgesF1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, zeroAF), (0, zeroFact, 1, zeroAF), (0, zeroFact, 1, RCases.Prog1.X),
   (0, zeroFact, 2, zeroAF)]
def addedsF1 : List (MethodId × PFact) := [(1, RCases.Prog1.X.fact)]

def InvF1 : Obj → Prop
  | .init M i => (M, i) ∈ initsF1
  | .edge M i n f => (M, i, n, f) ∈ edgesF1
  | .added M a => (M, a) ∈ addedsF1
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvF1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsF1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesF1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsF1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

theorem restrictU_none {j : PFact} {g : AFact} {d : DemandEdge} (h : d.dout = none) :
    restrictU j g d = none := by
  obtain ⟨din, dout⟩ := d
  cases h
  rfl

/-- Forward run 3 of program 1 (field limit 3, the spec rules) with only the zero demand, for
    every forward record set: the closure stays in the root. -/
theorem fwd1_zero_inv {dem : MethodId → DemandEdge → Prop} (hdem : ∀ M d, dem M d → d = zeroDem)
    (recs : MethodId → PFact × AFact → Prop) {o : Obj}
    (h : DR RCases.P1 RCases.cnt 3 dem emitM satI restrictU recs RCases.sinks1 [0] o) :
    InvF1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsF1,
      InvF1 (.edge x.1 x.2 (RCases.P1.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesF1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer RCases.cnt 3 RCases.src x.2.2.2).facts, InvF1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesF1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer RCases.cnt 3 RCases.src x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesF1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base RCases.callC.touched = false → InvF1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesF1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ RCases.callC.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvF1 (.added RCases.callC.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    have hd' := hdem m d hd
    subst hd'
    exact (by decide : ∀ y ∈ addedsF1, ∀ j ∈ (emitM zeroFact y.2).toList, InvF1 (.init y.1 j))
      (m, a) ih j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hr _ _ _ _ _ _ _ =>
    rw [hdem _ _ hd, restrictU_none rfl] at hr
    cases hr
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE _ _ _ _ _ he2 _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he2
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he2
          | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 2) _ ih rfl).elim
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs _ ih =>
    cases hs with
    | head => exact ((by decide : ∀ x ∈ edgesF1, x.1 ≠ 2) _ ih rfl).elim
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (RCases.p1_no_clean hE).elim
  | reqClean _ hE _ _ => exact (RCases.p1_no_clean hE).elim
  | filt _ hE _ _ => exact (RCases.p1_no_filt hE).elim

#print axioms fwd1_zero_inv

/-- PROGRAM 1 IS LOST WITHOUT THE ZERO BINDING INTO THE CALLEE: forward run 3 with the hand-off
    of the plain backward run does not report the real vulnerability, for every backward demand,
    backward record set and forward record set. -/
theorem lost_plain (demB : MethodId → DemandEdge → Prop) (recsB recs : MethodId → PFact × AFact → Prop)
    (b : Bool) :
    ¬ DR RCases.P1 RCases.cnt 3 (demOf Pb1 (B1 demB recsB false)) emitM satI restrictU recs
        RCases.sinks1 [0] (.vuln 2 0 RCases.sink1 b) :=
  fun h => fwd1_zero_inv (fun _ _ hd => demOf_plain demB recsB hd) recs h

#print axioms lost_plain

/-- So the plain backward run violates even the weaker contract B after forward run 1 (the
    vulnerability is real and reported by run 1). -/
theorem B_fails_plain (L1 : Nat) (demB : MethodId → DemandEdge → Prop)
    (recsB : MethodId → PFact × AFact → Prop) :
    ¬ BackwardContractRep RCases.P1 [0] RCases.sinks1
        (D RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0]) (demOf Pb1 (B1 demB recsB false)) := by
  intro hB
  have hRR := RCov.reach_to_reachR RCases.P1 RCases.cnt L1 policy1 RCases.sinks1 [0] RCases.p1_wf
    (policy_applicable (fun _ => [])) RCases.p1_reach
  have hv := (seeds1_reported L1 (2, 0, RCases.sink1)).mp (List.Mem.head _)
  have hR' := hB 2 0 ⟨3, [1, 4, 5], 1⟩ RCases.sink1 1 (List.Mem.head _) rfl RCases.p1_sink_covers
    hRR hv
  obtain ⟨⟨b, hv3⟩, _⟩ := RMain.vuln_found_M (counted := RCases.cnt) (L := 3)
    (recs := fun _ _ => False) RCases.p1_wf hR' (List.Mem.head _) rfl RCases.p1_sink_covers
  exact lost_plain demB recsB (fun _ _ => False) b hv3

#print axioms B_fails_plain

/-! ### The plain reversal of an explicit forward zero binding

`RCases.P1` has no forward zero binding. `P1z` is program 1 with the forward zero binding
`zero.* → zero.*` into both callees (the forward run of the implementation). Its plain reversal is
in the reversed calls (`fromCallee`, from the callee's forward entry up to the caller); with it
and without the zero binding into the callee the backward run is the same as for `RCases.P1`, and
forward run 3 of `P1z` still loses the vulnerability (`lost_plain_z`), although the zero now
enters the callees forward. -/

/-- The forward zero binding. -/
def zbF : MicroEdge := (⟨0, [], RCases.st, .star⟩, ⟨0, [], RCases.st, .star⟩)
def callCz : Call :=
  ⟨1, [1], [(⟨1, [], RCases.st, .star⟩, ⟨1, [], RCases.st, .star⟩), zbF], []⟩
def callMz : Call :=
  ⟨2, [2], [(⟨2, [], RCases.st, .star⟩, ⟨3, [], RCases.st, .star⟩), zbF], []⟩
def P1z : Program := ⟨RCases.P1.entry, RCases.P1.exit,
  [(0, 0, .stmt RCases.src, 1), (0, 1, .call callCz, 2), (1, 0, .stmt RCases.rd, 1),
   (1, 1, .call callMz, 2)]⟩
def Pb1z : Program := Program.rev P1z

theorem Pb1z_edges : Pb1z.edges =
    [(0, 1, .stmt (Stmt.rev RCases.src), 0), (0, 2, .call (Call.rev callCz), 1),
     (1, 1, .stmt (Stmt.rev RCases.rd), 0), (1, 2, .call (Call.rev callMz), 1)] := rfl

/-- The plain reversal of the forward zero binding is a binding UP (callee entry → caller). -/
theorem revCz_bindings : (Call.rev callCz).toCallee = [] ∧
    revEdge zbF.1 zbF.2 ∈ (Call.rev callCz).fromCallee :=
  ⟨rfl, List.Mem.tail _ (List.Mem.head _)⟩

/-- The vulnerability is real in `P1z`. -/
theorem p1z_reach : Reach P1z [0] 2 0 ⟨3, [1, 4, 5], 1⟩ := by
  have f0 : Flow P1z 0 zeroLoc 1 RCases.Prog1.l0 :=
    Flow.step (Flow.start 0 zeroLoc) (s := RCases.src) (List.Mem.head _)
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), RCases.Prog1.den_src⟩)
  have fc : Flow P1z 1 RCases.Prog1.l0 1 RCases.Prog1.l1 :=
    Flow.step (Flow.start 1 RCases.Prog1.l0) (s := RCases.rd)
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), RCases.Prog1.den_rd⟩)
  have r1 : Reach P1z [0] 1 1 RCases.Prog1.l1 :=
    Reach.down (Reach.root (List.Mem.head _) f0) (c := callCz) (n' := 2)
      (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) RCases.Prog1.den_cx fc
  exact Reach.down r1 (c := callMz) (n' := 2)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _)
    RCases.Prog1.den_my (Flow.start 2 RCases.Prog1.l2)

#print axioms p1z_reach

theorem rev1Cz_to : (Call.rev callCz).toCallee = [] := rfl
theorem rev1Mz_to : (Call.rev callMz).toCallee = [] := rfl

/-- The backward run of `P1z` with the plain reversal (no zero binding into the callee): the same
    closure as for `RCases.P1`. -/
theorem inv_b1z_plain (demB : MethodId → DemandEdge → Prop)
    (recsB : MethodId → PFact × AFact → Prop) {o : Obj}
    (h : DB Pb1z RCases.cnt 2 demB emitM satI restrictU recsB [] [0] RCases.sinks1 false o) :
    InvB1p o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ih
    decide
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb1z_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).facts,
          InvB1p (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb1z_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB1p, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callCz).touched = false →
            InvB1p (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1Cz_to] at he; cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1Mz_to] at he; cases he
          | tail _ hE => cases hE
  | initR _ _ _ ih => exact ih.elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 _ _ _ _ _ _ _ _ _ _ _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1Cz_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1Mz_to] at he1; cases he1
          | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 _ _ _ _ _ _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => rw [rev1Cz_to] at he1; cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => rw [rev1Mz_to] at he1; cases he1
          | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zpass M n n' c _ hE ih =>
    rw [Pb1z_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 1) _ ih rfl).elim
          | tail _ hE => cases hE
  | zin hzb _ _ _ => exact Bool.noConfusion hzb
  | @seed M n s hs _ ih =>
    cases hs with
    | head => exact ((by decide : ∀ x ∈ edgesB1p, x.1 ≠ 2) _ ih rfl).elim
    | tail _ h => cases h
  | zret hzb _ _ _ _ _ _ _ _ => exact Bool.noConfusion hzb

#print axioms inv_b1z_plain

theorem demOf_plain_z (demB : MethodId → DemandEdge → Prop)
    (recsB : MethodId → PFact × AFact → Prop) {m : MethodId} {d : DemandEdge}
    (h : demOf Pb1z (DB Pb1z RCases.cnt 2 demB emitM satI restrictU recsB [] [0] RCases.sinks1
      false) m d) : d = zeroDem := by
  rcases h with h | ⟨g, hg, rfl⟩ | ⟨jb, _, hjb, hne, _, _⟩
  · exact h
  · exact (by decide : ∀ x ∈ edgesB1p, x.2.2.1 = 0 → (⟨x.2.2.2.fact, none⟩ : DemandEdge) = zeroDem)
      (m, zeroFact, 0, g) (inv_b1z_plain demB recsB hg) rfl
  · exact absurd (Prod.mk.inj (inv_b1z_plain demB recsB hjb)).2 hne

/-- Forward run 3 of `P1z` with the zero demand only: the zero enters both callees (the forward
    zero binding and the accepted zero demand), the tainted fact never does. -/
def initsF1z : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (2, zeroFact)]
def edgesF1z : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, zeroAF), (0, zeroFact, 1, zeroAF), (0, zeroFact, 1, RCases.Prog1.X),
   (0, zeroFact, 2, zeroAF), (1, zeroFact, 0, zeroAF), (1, zeroFact, 1, zeroAF),
   (1, zeroFact, 2, zeroAF), (2, zeroFact, 0, zeroAF)]
def addedsF1z : List (MethodId × PFact) := [(1, zeroFact), (1, RCases.Prog1.X.fact), (2, zeroFact)]

def InvF1z : Obj → Prop
  | .init M i => (M, i) ∈ initsF1z
  | .edge M i n f => (M, i, n, f) ∈ edgesF1z
  | .added M a => (M, a) ∈ addedsF1z
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvF1z := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsF1z))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesF1z))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsF1z))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

theorem p1z_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ P1z.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

theorem p1z_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ P1z.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

theorem fwd1z_zero_inv {dem : MethodId → DemandEdge → Prop} (hdem : ∀ M d, dem M d → d = zeroDem)
    (recs : MethodId → PFact × AFact → Prop) {o : Obj}
    (h : DR P1z RCases.cnt 3 dem emitM satI restrictU recs RCases.sinks1 [0] o) : InvF1z o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsF1z,
      InvF1z (.edge x.1 x.2 (P1z.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesF1z, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer RCases.cnt 3 RCases.src x.2.2.2).facts, InvF1z (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesF1z, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer RCases.cnt 3 RCases.rd x.2.2.2).facts, InvF1z (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesF1z, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer RCases.cnt 3 RCases.src x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesF1z, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer RCases.cnt 3 RCases.rd x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesF1z, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callCz.touched = false → InvF1z (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesF1z, x.1 = 1 → x.2.2.1 = 1 →
              memB x.2.2.2.fact.base callMz.touched = false → InvF1z (.edge 1 x.2.1 2 x.2.2.2))
              (1, i, 1, f) ih rfl rfl hm
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesF1z, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callCz.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvF1z (.added callCz.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesF1z, x.1 = 1 → x.2.2.1 = 1 → ∀ e ∈ callMz.toCallee,
              ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvF1z (.added callMz.callee a.fact))
              (1, i, 1, f) ih rfl rfl e he a ha
          | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    have hd' := hdem m d hd
    subst hd'
    exact (by decide : ∀ y ∈ addedsF1z, ∀ j ∈ (emitM zeroFact y.2).toList, InvF1z (.init y.1 j))
      (m, a) ih j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hr _ _ _ _ _ _ _ =>
    rw [hdem _ _ hd, restrictU_none rfl] at hr
    cases hr
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE _ _ _ _ _ he2 _ _ =>
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he2
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he2
          | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      have hn := (by decide : ∀ x ∈ edgesF1z, x.1 = 2 → x.2.2.1 = 0 →
        check x.2.1 x.2.2.2 RCases.sink1 = .none) (2, i, 0, f) ih rfl rfl
      rw [hn] at hc
      exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      have hn := (by decide : ∀ x ∈ edgesF1z, x.1 = 2 → x.2.2.1 = 0 →
        check x.2.1 x.2.2.2 RCases.sink1 = .none) (2, i, 0, f) ih rfl rfl
      rw [hn] at hc
      exact Check.noConfusion hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (p1z_no_clean hE).elim
  | reqClean _ hE _ _ => exact (p1z_no_clean hE).elim
  | filt _ hE _ _ => exact (p1z_no_filt hE).elim

#print axioms fwd1z_zero_inv

/-- THE PLAIN REVERSAL OF THE FORWARD ZERO BINDING LOSES PROGRAM 1 (`P1z`). -/
theorem lost_plain_z (demB : MethodId → DemandEdge → Prop)
    (recsB recs : MethodId → PFact × AFact → Prop) (b : Bool) :
    ¬ DR P1z RCases.cnt 3 (demOf Pb1z (DB Pb1z RCases.cnt 2 demB emitM satI restrictU recsB []
        [0] RCases.sinks1 false)) emitM satI restrictU recs RCases.sinks1 [0]
        (.vuln 2 0 RCases.sink1 b) :=
  fun h => fwd1z_zero_inv (fun _ _ hd => demOf_plain_z demB recsB hd) recs h

#print axioms lost_plain_z

/-! ## Part 8. The general case: calls that bind back

With calls that bind back, a sink witness contains BALANCED calls (a callee flow from its entry to
its exit, bound back), and the next forward run needs, for each of them, a demand edge with an
exit pattern: a backward summary `jb → gb` of the callee. The backward run gives it: the
requirement enters the callee through the reversed binding back, the backward demand (the
reversed summaries of the previous forward run) emits the backward premise `jb`, the reversed
callee flow carries it to the forward entry (`gb`), and the restricted backward summary is applied
at the call site.

Why contract B in the form `BackwardContractRep` is too weak here: its hypothesis is a witness
demanded by the SUMMARIES of the forward run (`ReachR P (summaryDemand P Rk)`), whose balanced
calls only say that the exit pattern covers the exit LOCATION (`p.coversLoc l2`, no mark). The
backward emission (`emitM`, mark-aware) needs a forward exit pattern that covers the exit location
WITH ITS MARK. The hypothesis does not say that the forward run has such an exit fact: a summary
set whose only exit fact at the exit location has another concrete mark (for example the result of
a mark-changing edge `x.* (T) → y.* (T')`) satisfies it, and then the backward run cannot enter
the callee (Part 8d: `B_rep_fails_general`, on program 2).

So the general case uses the DEN-AWARE witness `ReachRD P Rk` (Part 8a): each balanced call is
justified by a summary of the forward run whose pair relation contains the concrete pair
(`den j g.fact l1 l2`). Every forward run gives it for every real vulnerability (`reach_strongRD`,
`reach_strongDD`: the coverage proofs of `RestrictedCoverage.lean`, with the pair relation kept),
so the iteration needs contract B only in this weaker form (`iteration_sound_D`,
`iteration_sound_M_D`). Part 8b proves that the backward run of the user's design satisfies it
(`B_general`), Part 8c joins them (`iteration_general`), and Part 8d is the counterexample for the
`BackwardContractRep` form. -/

/-! ### Part 8a. The den-aware demanded witness, and the forward runs give it -/

/-- A concrete flow whose every call that returns is justified by a summary of the run `R` that
    contains the concrete pair (its initial fact covers the entry location with its mark). -/
inductive FlowRD (P : Program) (R : Obj → Prop) : MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRD P R M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRD P R M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRD P R M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRD P R M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRD P R M l0 n' l
  | call {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRD P R M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRD P R c.callee l1 (P.exit c.callee) l2 →
      R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) →
      j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRD P R M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRD P R M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRD P R M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRD P R M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRD P R M l0 n' l

/-- A concrete vulnerability witness whose calls down enter an initial fact of `R` that covers the
    entry location, and whose flows are den-aware. -/
inductive ReachRD (P : Program) (R : Obj → Prop) (roots : List MethodId) :
    MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRD P R M zeroLoc n l → ReachRD P R roots M n l
  | down {M n l n' c e l1 n2 l2 j} :
      ReachRD P R roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      R (.init c.callee j) → j.covers l1 →
      FlowRD P R c.callee l1 n2 l2 → ReachRD P R roots c.callee n2 l2

theorem flowRD_flowR {P : Program} {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : FlowRD P R M l0 n l) : FlowR P (summaryDemand P R) M l0 n l := by
  induction h with
  | start M l0 => exact FlowR.start M l0
  | step _ he hs ih => exact FlowR.step ih he hs
  | pass _ he hm ih => exact FlowR.pass ih he hm
  | @call M l0 n l n' c e1 e2 l1 l2 l3 j g _ he he1 hd1 _ hj hg hjc hdg he2 hd2 ih ihc =>
    exact FlowR.call (d := ⟨j, some g.fact⟩) (p := g.fact) ih he he1 hd1 ihc
      ⟨hj, .inr ⟨g, hg, rfl⟩⟩ hjc rfl (RCov.covers_loc (den_covers_final hdg)) he2 hd2
  | clean _ he hcl ih => exact FlowR.clean ih he hcl
  | filt _ he hl ih => exact FlowR.filt ih he hl

theorem flowRD_flow {P : Program} {R : Obj → Prop} {M : MethodId} {l0 : Loc} {n : Node}
    {l : Loc} (h : FlowRD P R M l0 n l) : Flow P M l0 n l :=
  RCov.flowR_flow (flowRD_flowR h)

/-- The den-aware witness is a witness demanded by the summaries (the hypothesis of contract B). -/
theorem reachRD_reachR {P : Program} {R : Obj → Prop} {roots : List MethodId} {M : MethodId}
    {n : Node} {l : Loc} (h : ReachRD P R roots M n l) :
    ReachR P (summaryDemand P R) roots M n l := by
  induction h with
  | root hM hfl => exact ReachR.root hM (flowRD_flowR hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachR.down (d := ⟨_, none⟩) ih he he1 hd1 ⟨hj, .inl rfl⟩ hjc (flowRD_flowR hfc)

theorem reachRD_reach {P : Program} {R : Obj → Prop} {roots : List MethodId} {M : MethodId}
    {n : Node} {l : Loc} (h : ReachRD P R roots M n l) : Reach P roots M n l :=
  RCov.reachR_reach (reachRD_reachR h)

section CoverageRD
open ApSpec.Coverage ApSpec.RCov
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

local notation "DRr" => DR P counted L demand emit sat restrict recs sinks roots

/-- `RCov.coverageR` with the pair relation of the summaries kept (`FlowRD`). -/
theorem coverageRD (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l) :
    ∀ i, DRr (.init M i) → i.covers l0 →
      (∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowRD P DRr M l0 n l) ∨
      DRr (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, DR.start hi, startFact_sound hc, FlowRD.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DR.step hf he hr, hdr, FlowRD.step hfr he hs⟩
      · exact .inr (DR.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, DR.pass hf he hb, hd, FlowRD.pass hfr he hm⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 d p _ he he1 hd1 _ hdem hdin hdout hp he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
      have hadd := DR.added hf he he1 ha
      have hac : a.fact.covers l1 := den_covers_final hda
      obtain ⟨j, hemit, hjc, hsat⟩ := hE c.callee d.din a.fact l1 hadd hdin hac
      have hj := DR.initR hadd hdem hemit
      have hov : overlapB a.fact j = true := overlapB_of_common hac hjc
      have fin : ∀ j', DRr (.init c.callee j') → j'.covers l1 → sat j' a.fact = true →
          ∀ g, DRr (.edge c.callee j' (P.exit c.callee) g) → den j' g.fact l1 l2 →
          FlowRD P DRr c.callee l1 (P.exit c.callee) l2 →
          ∃ f', DRr (.edge M i n' f') ∧ den i f'.fact l0 l3 ∧ FlowRD P DRr M l0 n' l3 := by
        intro j' hj' hjc' hsat' g hg hdg hfc'
        obtain ⟨f', hf', hd'⟩ := ret_stepR P counted L demand emit sat restrict recs sinks roots
          hwf hS hR hf he he1 ha hda hj' hsat' hg hdg hdem (covers_loc hdin) hdout hp he2 hd2
        exact ⟨f', hf', hd', FlowRD.call hfr he he1 hd1 hfc' hj' hg hjc' hdg he2 hd2⟩
      rcases ihc j hj hjc with ⟨g, hg, hdg, hfc'⟩ | hreq
      · exact .inl (fin j hj hjc hsat g hg hdg hfc')
      · rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := DR.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hov
          rw [den_mark_abs hda ham] at hup
          exact .inr hup
        · have hmk := den_mark_conc hda ham
          have hans := DR.answer hreq hadd hmk hov
          have hsat' := hS.2 j a.fact l1.mark hsat hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg, hfc'⟩ | hreq'
          · exact .inl (fin _ hans hc' hsat' g hg hdg hfc')
          · exfalso
            exact req_initial_starR P counted L demand emit sat restrict recs sinks roots hreq'
              l1.mark answerInit_mark
    · exact .inr hr
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, DR.clean hf he hr, hdr, FlowRD.clean hfr he hcl⟩
      · exact .inr (DR.reqClean hf he hq)
    · exact .inr hr
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · exact .inl ⟨f, DR.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hd hl), hd,
        FlowRD.filt hfr he hl⟩
    · exact .inr hr

#print axioms coverageRD

theorem coverage_concRD (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowR P demand M l0 n l)
    {i : PFact} {t : Mark}
    (hi : DRr (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowRD P DRr M l0 n l := by
  rcases coverageRD P counted L demand emit sat restrict recs sinks roots hwf hE hS hR hfl i hi hc
    with h | hr
  · exact h
  · exact absurd ht (req_initial_starR P counted L demand emit sat restrict recs sinks roots hr t)

/-- `RCov.reach_strongR` with the den-aware witness: a restricted run makes every demanded
    witness a den-aware witness of its own summaries. -/
theorem reach_strongRD (hwf : P.WF) (hE : EmitContractOn DRr emit sat) (hS : SatContract sat)
    (hR : RestrictContract restrict)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachR P demand roots M n l) :
    ReachRD P DRr roots M n l ∧
    ∃ l0 i f, DRr (.edge M i n f) ∧ den i f.fact l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       ((∀ t, i.mark ≠ .conc t) ∧ (DRr (.req M i l0.mark) →
          ∃ i' f', DRr (.edge M i' n f') ∧ den i' f'.fact l0 l ∧
            ∃ t, i'.mark = .conc t))) := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverage_concRD P counted L demand emit sat restrict recs sinks roots
      hwf hE hS hR hfl (t := zeroMark) (DR.root hM) zeroFact_covers rfl
    exact ⟨ReachRD.root hM hfr, zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 d _ he he1 hd1 hdem hdin hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := DR.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    obtain ⟨j, hemit, hjc, _⟩ := hE c.callee d.din a.fact l1 hadd hdin hac
    have hj := DR.initR hadd hdem hemit
    have key : DRr (.req c.callee j l1.mark) →
        ∃ j', DRr (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', DRr (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := DR.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapB_of_common hac hjc)
          rw [den_mark_abs hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exact absurd ht
              (req_initial_starR P counted L demand emit sat restrict recs sinks roots hup t)
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_concR P counted L demand emit sat restrict recs sinks roots hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, DR.added hf' he he1 ha', den_covers_final hda', den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := DR.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    have mk : ∀ j', DRr (.init c.callee j') → j'.covers l1 →
        FlowRD P DRr c.callee l1 n2 l2 → ReachRD P DRr roots c.callee n2 l2 :=
      fun j' hj' hjc' hfr => ReachRD.down hRR he he1 hd1 hj' hjc' hfr
    rcases coverageRD P counted L demand emit sat restrict recs sinks roots hwf hE hS hR hfc _ hj hjc
      with ⟨g, hg, hdg, hfr⟩ | hreq
    · refine ⟨mk j hj hjc hfr, l1, _, g, hg, hdg, ?_⟩
      rcases mark_cases j.mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg', _⟩ := coverage_concRD P counted L demand emit sat restrict recs
          sinks roots hwf hE hS hR hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg', hfr⟩ := coverage_concRD P counted L demand emit sat restrict recs
        sinks roots hwf hE hS hR hfc hj' hjc' ht
      exact ⟨mk j' hj' hjc' hfr, l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strongRD

end CoverageRD

section CoverageDD
open ApSpec.Coverage ApSpec.RCov
variable (P : Program) (counted : Acc → Bool) (L : Nat) (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)

local notation "Dr" => D P counted L α sinks roots

/-- `RCov.coverageD` (run 1) with the pair relation of the summaries kept. -/
theorem coverageDD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l) :
    ∀ i, Dr (.init M i) → i.covers l0 →
      (∃ f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowRD P Dr M l0 n l) ∨
      Dr (.req M i l0.mark) := by
  induction hfl with
  | start M l0 =>
    intro i hi hc
    exact .inl ⟨_, D.start hi, startFact_sound hc, FlowRD.start M l0⟩
  | step _ he hs ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases transfer_sound (hwf.stmtTouched _ _ _ _ he) hd hs with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D.step hf he hr, hdr, FlowRD.step hfr he hs⟩
      · exact .inr (D.reqStmt hf he hq)
    · exact .inr hr
  | @pass M l0 n l n' c _ he hm ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · have hb : memB f.fact.base c.touched = false := by
        rw [← hd.2.1]
        exact hm
      exact .inl ⟨f, D.pass hf he hb, hd, FlowRD.pass hfr he hm⟩
    · exact .inr hr
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ he he1 hd1 _ he2 hd2 ih ihc =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
      have hadd := D.added hf he he1 ha
      have hac : a.fact.covers l1 := den_covers_final hda
      have hapj := hα c.callee a.fact
      have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
      have hov : overlapB a.fact (α c.callee a.fact) = true := overlapB_of_common hac hjc
      have fin : ∀ j, Dr (.init c.callee j) → j.covers l1 → applicable j a.fact = true →
          ∀ g, Dr (.edge c.callee j (P.exit c.callee) g) → den j g.fact l1 l2 →
          FlowRD P Dr c.callee l1 (P.exit c.callee) l2 →
          ∃ f', Dr (.edge M i n' f') ∧ den i f'.fact l0 l3 ∧ FlowRD P Dr M l0 n' l3 := by
        intro j hj hjc' hap g hg hdg hfc'
        obtain ⟨f', hf', hd'⟩ := ret_step P counted L α sinks roots hwf hf he he1 ha hda hj hap
          hg hdg he2 hd2
        exact ⟨f', hf', hd', FlowRD.call hfr he he1 hd1 hfc' hj hg hjc' hdg he2 hd2⟩
      rcases ihc _ (D.initA hadd) hjc with ⟨g, hg, hdg, hfc'⟩ | hreq
      · exact .inl (fin _ (D.initA hadd) hjc hapj g hg hdg hfc')
      · rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := D.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham) hov
          rw [den_mark_abs hda ham] at hup
          exact .inr hup
        · have hmk := den_mark_conc hda ham
          have hans := D.answer hreq hadd hmk hov
          have hap' := answerInit_applicable hapj hmk
          have hc' := answerInit_covers (t := l1.mark) hjc hac rfl
          rcases ihc _ hans hc' with ⟨g, hg, hdg, hfc'⟩ | hreq'
          · exact .inl (fin _ hans hc' hap' g hg hdg hfc')
          · exfalso
            exact req_initial_star P counted L α sinks roots hreq' l1.mark answerInit_mark
    · exact .inr hr
  | @clean M l0 n l n' cl _ he hcl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨_, hq⟩
      · exact .inl ⟨r, D.clean hf he hr, hdr, FlowRD.clean hfr he hcl⟩
      · exact .inr (D.reqClean hf he hq)
    · exact .inr hr
  | @filt M l0 n l n' b may _ he hl ih =>
    intro i hi hc
    rcases ih i hi hc with ⟨f, hf, hd, hfr⟩ | hr
    · exact .inl ⟨f, D.filt hf he (filt_keeps (hwf.filtPrefix M n b may n' he) hd hl), hd,
        FlowRD.filt hfr he hl⟩
    · exact .inr hr

#print axioms coverageDD

theorem coverage_concDD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : Flow P M l0 n l)
    {i : PFact} {t : Mark}
    (hi : Dr (.init M i)) (hc : i.covers l0) (ht : i.mark = .conc t) :
    ∃ f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧ FlowRD P Dr M l0 n l := by
  rcases coverageDD P counted L α sinks roots hwf hα hfl i hi hc with h | hr
  · exact h
  · exact absurd ht (req_initial_star P counted L α sinks roots hr t)

/-- `RCov.reach_strongD` with the den-aware witness: run 1 makes every concrete witness a
    den-aware witness of its own summaries. -/
theorem reach_strongDD (hwf : P.WF) (hα : ∀ m a, applicable (α m a) a = true)
    {M : MethodId} {n : Node} {l : Loc} (hRe : Reach P roots M n l) :
    ReachRD P Dr roots M n l ∧
    ∃ l0 i f, Dr (.edge M i n f) ∧ den i f.fact l0 l ∧
      ((∃ t, i.mark = .conc t) ∨
       ((∀ t, i.mark ≠ .conc t) ∧ (Dr (.req M i l0.mark) →
          ∃ i' f', Dr (.edge M i' n f') ∧ den i' f'.fact l0 l ∧ ∃ t, i'.mark = .conc t))) := by
  induction hRe with
  | root hM hfl =>
    obtain ⟨f, hf, hd, hfr⟩ := coverage_concDD P counted L α sinks roots hwf hα hfl
      (t := zeroMark) (D.root hM) zeroFact_covers rfl
    exact ⟨ReachRD.root hM hfr, zeroLoc, zeroFact, f, hf, hd, .inl ⟨zeroMark, rfl⟩⟩
  | @down M n l n' c e l1 n2 l2 _ he he1 hd1 hfc ih =>
    obtain ⟨hRR, l0, i, f, hf, hd, hdisj⟩ := ih
    obtain ⟨a, ha, hda⟩ := bind_in hwf he he1 hd hd1
    have hadd := D.added hf he he1 ha
    have hac : a.fact.covers l1 := den_covers_final hda
    have hapj := hα c.callee a.fact
    have hjc : (α c.callee a.fact).covers l1 := applicable_sound hapj hac
    have key : Dr (.req c.callee (α c.callee a.fact) l1.mark) →
        ∃ j', Dr (.init c.callee j') ∧ j'.covers l1 ∧ ∃ t, j'.mark = .conc t := by
      intro hreq
      have hconc : ∃ a', Dr (.added c.callee a') ∧ a'.covers l1 ∧ a'.mark = .conc l1.mark := by
        rcases mark_cases a.fact.mark with ham | ⟨t', ham⟩
        · have hup := D.reqUp hreq hf he rfl he1 ha (climbsB_of_covers hac rfl ham)
            (overlapB_of_common hac hjc)
          rw [den_mark_abs hda ham] at hup
          rcases hdisj with ⟨t, ht⟩ | ⟨_, himp⟩
          · exact absurd ht (req_initial_star P counted L α sinks roots hup t)
          · obtain ⟨i', f', hf', hd', t, ht⟩ := himp hup
            obtain ⟨a', ha', hda'⟩ := bind_in hwf he he1 hd' hd1
            obtain ⟨t1, h1⟩ := edge_conc P counted L α sinks roots hf' ht
            obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha'
            exact ⟨a'.fact, D.added hf' he he1 ha', den_covers_final hda', den_mark_conc hda' h2⟩
        · exact ⟨a.fact, hadd, hac, den_mark_conc hda ham⟩
      obtain ⟨a', hadd', hac', hm'⟩ := hconc
      have hans := D.answer hreq hadd' hm' (overlapB_of_common hac' hjc)
      exact ⟨_, hans, answerInit_covers hjc hac' rfl, l1.mark, answerInit_mark⟩
    have mk : ∀ j', Dr (.init c.callee j') → j'.covers l1 →
        FlowRD P Dr c.callee l1 n2 l2 → ReachRD P Dr roots c.callee n2 l2 :=
      fun j' hj' hjc' hfr => ReachRD.down hRR he he1 hd1 hj' hjc' hfr
    rcases coverageDD P counted L α sinks roots hwf hα hfc _ (D.initA hadd) hjc with
      ⟨g, hg, hdg, hfr⟩ | hreq
    · refine ⟨mk _ (D.initA hadd) hjc hfr, l1, _, g, hg, hdg, ?_⟩
      rcases mark_cases (α c.callee a.fact).mark with hjm | ⟨t, hjm⟩
      · refine .inr ⟨hjm, fun hreq => ?_⟩
        obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
        obtain ⟨g', hg', hdg', _⟩ :=
          coverage_concDD P counted L α sinks roots hwf hα hfc hj' hjc' ht
        exact ⟨j', g', hg', hdg', t, ht⟩
      · exact .inl ⟨t, hjm⟩
    · obtain ⟨j', hj', hjc', t, ht⟩ := key hreq
      obtain ⟨g', hg', hdg', hfr⟩ := coverage_concDD P counted L α sinks roots hwf hα hfc hj' hjc' ht
      exact ⟨mk j' hj' hjc' hfr, l1, j', g', hg', hdg', .inl ⟨t, ht⟩⟩

#print axioms reach_strongDD

end CoverageDD

/-! ### The iteration with the den-aware contract -/

/-- Contract B for the reported vulnerabilities, with the den-aware witness as hypothesis. It is
    weaker than `BackwardContractRep` (`repD_of_rep`), so a backward run that satisfies it is
    enough for the iteration. -/
def BackwardContractD (P : Program) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (Rk : Obj → Prop)
    (dnext : MethodId → DemandEdge → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRD P Rk roots M n l → (∃ b, Rk (.vuln M n s b)) → ReachR P dnext roots M n l

theorem repD_of_rep {P : Program} {roots : List MethodId} {sinks : List (MethodId × Node × PFact)}
    {Rk : Obj → Prop} {dnext : MethodId → DemandEdge → Prop}
    (h : BackwardContractRep P roots sinks Rk dnext) : BackwardContractD P roots sinks Rk dnext :=
  fun M n l s T hs hT hc hr hv => h M n l s T hs hT hc (reachRD_reachR hr) hv

#print axioms repD_of_rep

section IterationD
open RCov
variable {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
  {dem : Nat → MethodId → DemandEdge → Prop} {emit : PFact → PFact → Option PFact}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recs : Nat → MethodId → PFact × AFact → Prop} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

theorem iteration_invariant_D (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContractD P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ReachRD P (runSeq P counted Ls dem emit sat restrict recs sinks roots k) roots M n l ∧
      ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) := by
  intro k
  induction k with
  | zero =>
    exact ⟨(reach_strongDD P counted (Ls 0) policy1 sinks roots hwf
        (policy_applicable (fun _ => [])) hRe).1,
      Coverage.vuln_found P counted (Ls 0) policy1 sinks roots hwf
        (policy_applicable (fun _ => [])) hRe hs hT hsc⟩
  | succ k ih =>
    have hRk := hB k M n l s T hs hT hsc ih.1 ih.2
    obtain ⟨hv, _⟩ := vuln_foundR P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k)
      sinks roots hwf (hE k) hS hR hRk hs hT hsc
    exact ⟨(reach_strongRD P counted (Ls (k + 1)) (dem k) emit sat restrict (recs k) sinks roots
      hwf (hE k) hS hR hRk).1, hv⟩

#print axioms iteration_invariant_D

/-- THE ITERATION THEOREM with the den-aware contract. -/
theorem iteration_sound_D (hwf : P.WF)
    (hE : ∀ k, EmitContractOn (runSeq P counted Ls dem emit sat restrict recs sinks roots (k + 1))
      emit sat)
    (hS : SatContract sat) (hR : RestrictContract restrict)
    (hB : ∀ k, BackwardContractD P roots sinks
      (runSeq P counted Ls dem emit sat restrict recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, runSeq P counted Ls dem emit sat restrict recs sinks roots k (.vuln M n s b) :=
  fun k => (iteration_invariant_D hwf hE hS hR hB hRe hs hT hsc k).2

#print axioms iteration_sound_D

end IterationD

/-- THE ITERATION THEOREM for the spec rules with the den-aware contract. -/
theorem iteration_sound_M_D {P : Program} {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hwf : P.WF)
    (hB : ∀ k, BackwardContractD P roots sinks
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) (dem k))
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) := by
  intro k
  rw [RMain.runSeqU_eq_S k]
  refine iteration_sound_D (emit := emitM) (sat := satI) (restrict := restrictS) hwf
    (fun k => RCov.emitOn_of_conc P counted (Ls (k + 1)) (dem k) emitM satI restrictS (recs k)
      sinks roots RCore.emitM_contract_I RCore.emitM_copies)
    RCore.satI_contract RCore.restrictS_contract (fun k' => ?_) hRe hs hT hsc k
  rw [← RMain.runSeqU_eq_S k']
  exact hB k'

#print axioms iteration_sound_M_D

/-! ### Part 8b. The backward run of the user's design satisfies the den-aware contract

Added hypothesis: no call binds the zero base back (`NoZeroBack`, the user's "no zero binding
back is needed"). Then the backward premise of a callee entered through a binding back is never
the zero fact, so its backward summary is handed off as `(gb, some jb)`. -/

/-- No call binds the zero base back. -/
def NoZeroBack (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges → ∀ e, e ∈ c.fromCallee → e.1.base ≠ zeroBase

/-- A legal concrete fact has no `*` tail. -/
theorem not_star_of_legal {f : AFact} {t : Mark} (hl : Invariant.Legal f)
    (ht : f.fact.mark = .conc t) : f.fact.kind.isStar = false := by
  cases hk : f.fact.kind with
  | star e => exact absurd ht ((hl e hk).1.not_conc t)
  | any => rfl
  | exact => rfl

theorem legal_transfer {counted : Acc → Bool} {L : Nat} {s : Stmt} {f r : AFact}
    (hl : Invariant.Legal f) (hr : r ∈ (transfer counted L s f).facts) : Invariant.Legal r := by
  rcases Invariant.transfer_mem hr with rfl | ⟨x, e, _, hx, rfl⟩
  · exact hl
  · exact Invariant.limitF_Legal (Invariant.applyEdge_Legal hx)

theorem legal_seed {counted : Acc → Bool} {L : Nat} {s : PFact}
    (hk : s.kind = .exact ∨ s.kind = .any) : Invariant.Legal (limitF counted L ⟨s, false⟩) := by
  refine Invariant.limitF_Legal (fun e hke => ?_)
  have hke' : s.kind = .star e := hke
  rcases hk with hk | hk <;> (rw [hk] at hke'; cases hke')

section General
variable {P : Program} {Rk : Obj → Prop} {counted : Acc → Bool} {L : Nat}
  {demB : MethodId → DemandEdge → Prop} {recsB : MethodId → PFact × AFact → Prop}
  {sinksB : List (MethodId × Node × PFact)} {rootsB : List MethodId}
  {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

/-- BACKWARD SEGMENT COVERAGE WITH CALLS THAT RETURN. A den-aware forward flow of `M` from the
    entry location `l0` to `(n, l)`, and a concrete legal backward edge of any premise `i` at `n`
    that covers `l` (from the backward premise location `lX`), give a backward edge of `i` at the
    forward entry that covers `l0`; and the flow is demanded by the hand-off of the backward run
    (every call that returns gets the backward summary of its callee as the demand edge
    `(gb, some jb)`). The backward demand must contain the reversed summaries of `Rk`. -/
theorem seg_gen (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (hfl : FlowRD P Rk M l0 n l) :
    ∀ i f lX, DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
        zbind (.edge M i n f) →
      den i f.fact lX l → (∃ t, f.fact.mark = .conc t) → Invariant.Legal f →
      (∃ f', DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds
          zbind (.edge M i (P.entry M) f') ∧ den i f'.fact lX l0 ∧
          (∃ t, f'.fact.mark = .conc t) ∧ Invariant.Legal f') ∧
      FlowR P (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU recsB
        sinksB rootsB seeds zbind)) M l0 n l := by
  induction hfl with
  | start M l0 =>
    intro i f lX h hd hc hl
    exact ⟨⟨f, h, hd, hc, hl⟩, FlowR.start M l0⟩
  | @step M l0 n1 l1 n' l' s _ he hst ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.stmt (Stmt.rev s), n1) ∈ (Program.rev P).edges := mem_rev_stmt he
    have hrs : (Stmt.rev s).step l' l1 := Stmt.rev_step_sound (hmr M n1 s n' he) hst
    obtain ⟨t, ht⟩ := hc
    rcases transfer_sound (counted := counted) (L := L) (rev_touched s) hd hrs with
      ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.step h hEr hr) hdr (transfer_mark_conc ht hr)
        (legal_transfer hl hr)
      exact ⟨res, FlowR.step hfr he hst⟩
    · exact absurd ht (habs t)
  | @pass M l0 n1 l1 n' c _ he hb ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.call (Call.rev c), n1) ∈ (Program.rev P).edges := mem_rev_call he
    have hb' : memB f.fact.base (Call.rev c).touched = false := by
      show memB f.fact.base c.touched = false
      rw [← hd.2.1]
      exact hb
    obtain ⟨res, hfr⟩ := ih i f lX (DB.pass h hEr hb') hd hc hl
    exact ⟨res, FlowR.pass hfr he hb⟩
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
    -- the reversed callee flow: from the backward premise at the forward exit to the entry
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
    exact ⟨res, FlowR.call hfr he he1 hd1 hfrc hdem (den_covers_final hdgb) rfl
      (RCov.covers_loc hjbc) he2 hd2⟩
  | @clean M l0 n1 l1 n' cl _ he hcl ih =>
    intro i f lX h hd hc hl
    have hEr : (M, n', Instr.clean cl, n1) ∈ (Program.rev P).edges := mem_rev_clean he
    obtain ⟨t, ht⟩ := hc
    rcases cleanRes_sound hd hcl with ⟨r, hr, hdr⟩ | ⟨habs, _⟩
    · obtain ⟨res, hfr⟩ := ih i r lX (DB.clean h hEr hr) hdr (cleanRes_mark_conc ht hr)
        (Invariant.cleanRes_Legal hl hr)
      exact ⟨res, FlowR.clean hfr he hcl⟩
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
    exact ⟨res, FlowR.filt hfr he hmay⟩

#print axioms seg_gen

/-- The induction over the calls down (general case). -/
theorem reach_of_db_gen (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {M : MethodId} {n : Node} {l : Loc} (hRe : ReachRD P Rk roots M n l) :
    ∀ f, DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB rootsB seeds zbind
        (.edge M zeroFact n f) → den zeroFact f.fact zeroLoc l → (∃ t, f.fact.mark = .conc t) →
      Invariant.Legal f →
      ReachR P (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU
        recsB sinksB rootsB seeds zbind)) roots M n l := by
  induction hRe with
  | root hM hfl =>
    intro f h hd hc hl
    exact ReachR.root hM (seg_gen hW hT hmr hNZB hdemB hfl zeroFact f zeroLoc h hd hc hl).2
  | @down M n l n' c e l1 n2 l2 j hRe0 hE he hd1 _ _ hfl ih =>
    intro f h hd hc hl
    obtain ⟨⟨f', h', hd', hc', _⟩, hfr⟩ := seg_gen hW hT hmr hNZB hdemB hfl zeroFact f zeroLoc h hd hc hl
    have hRe0' := reachRD_reach hRe0
    have hz := zero_path (counted := counted) (L := L) (demand := demB) (emit := emitM)
      (sat := satI) (restrict := restrictU) (recs := recsB) (sinksB := sinksB) (rootsB := rootsB)
      (seeds := seeds) (zbind := zbind) hZ
      (hX M n' (reach_called hRe0') (CfgPath.step (reach_cfg hRe0') hE))
      (zero_exit (zero_init hZ hX hzb hroots hRe0'))
    obtain ⟨g, hg, hdg, hcg, hlg⟩ := zret_descent hW hT hzb hE he hd1 hz h' hd' hc'
    have hdem : demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU
        recsB sinksB rootsB seeds zbind) c.callee ⟨f'.fact, none⟩ := Or.inr (Or.inl ⟨f', h', rfl⟩)
    exact ReachR.down (ih g hg hdg hcg hlg) hE he hd1 hdem (den_covers_final hd') hfr

#print axioms reach_of_db_gen

/-- Every den-aware sink witness whose sink is seeded is demanded by the backward run. -/
theorem demanded_gen (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    (hzb : zbind = true) (hroots : ∀ M, M ∈ roots → M ∈ rootsB)
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : ReachRD P Rk roots M n l) (hseed : (M, n, s) ∈ seeds)
    (hT' : s.mark = .conc T) (hk : s.kind = .exact ∨ s.kind = .any) (hsc : s.covers l) :
    ReachR P (demOf (Program.rev P) (DB (Program.rev P) counted L demB emitM satI restrictU
      recsB sinksB rootsB seeds zbind)) roots M n l :=
  reach_of_db_gen hW hT hmr hNZB hZ hX hzb hroots hdemB hRe _
    (DB.seed hseed (zero_at hZ hX hzb hroots (reachRD_reach hRe)))
    (limitF_sound (seed_den hT' hk hsc)) ⟨T, by rw [limitF_mark]; exact hT'⟩ (legal_seed hk)

#print axioms demanded_gen

end General

/-- CONTRACT B IN THE GENERAL CASE (den-aware form). The backward run of the user's design,
    restricted by (at least) the reversed summaries of the forward run `Rk`, seeded (at least) at
    the sinks `Rk` reported, started at the forward roots, satisfies `BackwardContractD`, for every
    backward field limit and record set. -/
theorem B_general {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractD P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) := by
  intro M n l s T hs hT' hsc hRR hv
  obtain ⟨b, hv⟩ := hv
  exact demanded_gen hW hT hmr hNZB hZ hX rfl (fun _ h => h) hdemB hRR (hseeds M n s b hv) hT'
    (hk M n s hs) hsc

#print axioms B_general

/-! ### Part 8c. The iteration in the general case, end to end -/

/-- THE GENERAL ITERATION THEOREM. Every forward run of the sequence reports every real
    vulnerability, if the demand of each forward run contains the hand-off of a backward run of
    the user's design whose backward demand contains the reversed summaries of the previous
    forward run and whose seeds contain the sinks the previous forward run reported (any backward
    field limit and record set). Hypotheses on the program: well-formed, mark-agnostic binding
    targets, mark-reversible statements, no zero binding back, the zero kept by every instruction,
    every node of a method reaches its exit; the sinks have the tail `$` or `[any]`. -/
theorem iteration_general {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, revSummaryDemand P
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k M n s b,
      RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k (.vuln M n s b) →
      (M, n, s) ∈ seeds k)
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) :=
  iteration_sound_M_D hW (fun k M' n' l' s' T' hs' hT'' hc' hr' hv' =>
    RCov.reachR_mono (hdem k)
      (B_general hW hT hmr hNZB hZ hX hk (hseeds k) (hdemB k) M' n' l' s' T' hs' hT'' hc' hr' hv'))
    hRe hs hT' hsc

#print axioms iteration_general

/-! ### Program 2 through the general theorem

Program 2 has a call that binds back, so it is outside the fragment of Part 6. It satisfies the
hypotheses of `B_general`, and the den-aware witness comes from forward run 1
(`reach_strongDD`): a second route to `p2_found`, independent of the exhaustive computation. -/

theorem p2_bindStar : BindTargetsStar RCases.P2 := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head => exact ⟨fun _ he => star_one he, fun _ he => star_one he⟩
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

theorem p2_markRev : StmtsMarkRev RCases.P2 := by
  intro M n s n' hE e he
  cases hE with
  | head =>
    cases he with
    | head => exact Or.inr ⟨0, rfl⟩
    | tail _ he => cases he with
      | head => exact Or.inr ⟨0, rfl⟩
      | tail _ he => cases he
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        cases he with
        | head => exact markRev_star rfl
        | tail _ he => cases he with
          | head => exact markRev_star rfl
          | tail _ he => cases he
      | tail _ hE => cases hE

theorem p2_noZeroBack : NoZeroBack RCases.P2 := by
  intro M n c n' hE e he
  cases hE with
  | tail _ hE => cases hE with
    | head =>
      cases he with
      | head => decide
      | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

theorem p2_zeroKept : ZeroKept RCases.P2 where
  stmt := by
    intro M n s n' hE hz
    cases hE with
    | head => exact List.Mem.head _
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact absurd hz (by decide)
        | tail _ hE => cases hE
  clean := fun _ _ _ _ h => (RCases.p2_no_clean h).elim
  filt := fun _ _ _ _ _ h => (RCases.p2_no_filt h).elim

theorem p2_nodes0 {n : Node} (h : CfgPath RCases.P2 0 0 n) : n = 0 ∨ n = 1 ∨ n = 2 := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ he _ =>
    cases he with
    | head => exact Or.inr (Or.inl rfl)
    | tail _ he => cases he with
      | head => exact Or.inr (Or.inr rfl)
      | tail _ he => cases he with
        | tail _ he => cases he

theorem p2_nodes1 {n : Node} (h : CfgPath RCases.P2 1 0 n) : n = 0 ∨ n = 1 := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ he _ =>
    cases he with
    | tail _ he => cases he with
      | tail _ he => cases he with
        | head => exact Or.inr rfl
        | tail _ he => cases he

theorem p2_exitReach : ExitReach RCases.P2 [0] := by
  intro M n hM hp
  have hM' : M = 0 ∨ M = 1 := by
    rcases hM with h | ⟨M', n0, c, n1, hE, rfl⟩
    · cases h with
      | head => exact Or.inl rfl
      | tail _ h => cases h
    · cases hE with
      | tail _ hE => cases hE with
        | head => exact Or.inr rfl
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  rcases hM' with rfl | rfl
  · rcases p2_nodes0 hp with rfl | rfl | rfl
    · exact CfgPath.step (CfgPath.step CfgPath.refl RCases.Prog2.hE00) RCases.Prog2.hE01
    · exact CfgPath.step CfgPath.refl RCases.Prog2.hE01
    · exact CfgPath.refl
  · rcases p2_nodes1 hp with rfl | rfl
    · exact CfgPath.step CfgPath.refl RCases.Prog2.hE10
    · exact CfgPath.refl

#print axioms p2_exitReach

theorem sinks2_kinds : ∀ M n s, (M, n, s) ∈ RCases.sinks2 → s.kind = .exact ∨ s.kind = .any := by
  intro M n s hs
  cases hs with
  | head => exact Or.inl rfl
  | tail _ h => cases h

/-- Forward run 1 makes the witness of program 2 a den-aware witness of its summaries. -/
theorem p2_reachRD : ReachRD RCases.P2 R1p [0] 0 2 ⟨2, [1, 4, 5], 1⟩ :=
  (reach_strongDD RCases.P2 RCases.cnt 1 policy1 RCases.sinks2 [0] RCases.p2_wf
    (policy_applicable (fun _ => [])) RCases.p2_reach).1

/-- The general theorem applied to program 2: backward run 2 demands the witness. -/
theorem p2_reachR_general : ReachR RCases.P2 (demOf Pb2 B2) [0] 0 2 ⟨2, [1, 4, 5], 1⟩ :=
  B_general RCases.p2_wf p2_bindStar p2_markRev p2_noZeroBack p2_zeroKept p2_exitReach
    sinks2_kinds (fun _ _ _ _ h => D_vuln_sink h) (fun _ _ h => h)
    0 2 _ RCases.sink2 1 (List.Mem.head _) rfl RCases.p2_sink_covers p2_reachRD
    ((seeds2_reported 1 (0, 2, RCases.sink2)).mp (List.Mem.head _))

#print axioms p2_reachR_general

/-! ### Part 8d. The den-aware hypothesis is necessary: `BackwardContractRep` fails in general

`B_general` holds for EVERY `Rk` in the den-aware form. The same statement with
`BackwardContractRep` (the hypothesis `ReachR P (summaryDemand P Rk)`) is false: program 2 (which
satisfies every hypothesis of `B_general`) and the summary set `RkX` below, whose only summary of
`c` has the exit fact `(ret,.[any],7)`. The witness is demanded by these summaries (the exit
pattern covers the exit LOCATION `ret.f.k.z`), and `RkX` reports the vulnerability; but the
backward requirement has the mark `T = 1`, the mark-aware emission does not take it into `c`, and
the hand-off has only the zero demand. -/

/-- A summary of `c` with a concrete exit mark `7`. -/
def G7 : AFact := ⟨⟨4, [], .any, .conc 7⟩, true⟩

/-- A summary set: `c` has the initial fact `(arg,.*,*)` and the exit fact `(ret,.[any],7)`;
    the vulnerability is reported. -/
def RkX : Obj → Prop := fun o =>
  o = .init 1 Jc ∨ o = .edge 1 Jc 1 G7 ∨ o = .vuln 0 2 RCases.sink2 true

/-- The witness of program 2 is demanded by the summaries of `RkX`. -/
theorem rkX_reachR : ReachR RCases.P2 (summaryDemand RCases.P2 RkX) [0] 0 2 ⟨2, [1, 4, 5], 1⟩ := by
  have f0 : FlowR RCases.P2 (summaryDemand RCases.P2 RkX) 0 zeroLoc 1 RCases.Prog2.l0 :=
    FlowR.step (FlowR.start 0 zeroLoc) (s := RCases.src2) RCases.Prog2.hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), RCases.Prog2.den_src⟩)
  have fc : FlowR RCases.P2 (summaryDemand RCases.P2 RkX) 1 RCases.Prog2.l1 1 RCases.Prog2.l2 :=
    FlowR.step (FlowR.start 1 RCases.Prog2.l1) (s := RCases.rd2) RCases.Prog2.hE10
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), RCases.Prog2.den_rd⟩)
  have f2 : FlowR RCases.P2 (summaryDemand RCases.P2 RkX) 0 zeroLoc 2 ⟨2, [1, 4, 5], 1⟩ :=
    FlowR.call f0 (c := RCases.callC2) RCases.Prog2.hE01 (List.Mem.head _) RCases.Prog2.den_in fc
      (d := ⟨Jc, some G7.fact⟩) ⟨Or.inl rfl, Or.inr ⟨G7, Or.inr (Or.inl rfl), rfl⟩⟩
      ⟨rfl, ⟨[2, 3, 1, 4, 5], rfl, rfl⟩, trivial⟩ rfl ⟨rfl, [1, 4, 5], rfl, trivial⟩
      (List.Mem.head _) RCases.Prog2.den_out
  exact ReachR.root (List.Mem.head _) f2

/-- The backward run after `RkX` (the user's design, field limit 2, no records). -/
abbrev BX : Obj → Prop :=
  DB Pb2 RCases.cnt 2 (revSummaryDemand RCases.P2 RkX) emitM satI restrictU (fun _ _ => False)
    [] [0] RCases.sinks2 true

def revDemX : List (MethodId × DemandEdge) := [(1, ⟨G7.fact, some Jc⟩)]

theorem revDemX_bound {m : MethodId} {d : DemandEdge} (h : revSummaryDemand RCases.P2 RkX m d) :
    (m, d) ∈ revDemX := by
  obtain ⟨j, g, ⟨hi, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · rcases hg' with h1 | h1 | h1
    · cases h1
    · cases h1
      cases hgg
      exact List.Mem.head _
    · cases h1

def initsBX : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact)]
def edgesBX : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, zeroAF), (0, zeroFact, 2, Sd2), (0, zeroFact, 1, zeroAF),
   (0, zeroFact, 0, zeroAF), (1, zeroFact, 1, zeroAF), (1, zeroFact, 0, zeroAF)]
def addedsBX : List (MethodId × PFact) := [(1, Jb2)]

def InvBX : Obj → Prop
  | .init M i => (M, i) ∈ initsBX
  | .edge M i n f => (M, i, n, f) ∈ edgesBX
  | .added M a => (M, a) ∈ addedsBX
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBX := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBX))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBX))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBX))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The complete backward run after `RkX`: the requirement is added to `c` but never emitted. -/
theorem inv_bX {o : Obj} (h : BX o) : InvBX o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBX, InvBX (.edge x.1 x.2 (Pb2.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBX, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src2) x.2.2.2).facts,
          InvBX (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBX, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd2) x.2.2.2).facts,
              InvBX (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBX, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.src2) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBX, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer RCases.cnt 2 (Stmt.rev RCases.rd2) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBX, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev RCases.callC2).touched = false →
            InvBX (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBX, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev RCases.callC2).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBX (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ revDemX, ∀ y ∈ addedsBX, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvBX (.init x.1 j))
      (m, d) (revDemX_bound hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBX, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev RCases.callC2).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsBX, y.1 = 1 →
          ∀ z ∈ edgesBX, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ revDemX, dd.1 = 1 → ∀ g' ∈ (restrictU y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Call.rev RCases.callC2).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBX (.edge 0 x.2.1 1 (limitF RCases.cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (revDemX_bound hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb2_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBX, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev RCases.callC2).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBX (.edge 0 zeroFact 1 (limitF RCases.cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_bX

/-- The hand-off after `RkX` has only exit-less demand edges (the zero demand). -/
theorem demOf_X_none {m : MethodId} {d : DemandEdge} (h : demOf Pb2 BX m d) : d.dout = none := by
  rcases h with rfl | ⟨g, _, rfl⟩ | ⟨jb, _, hjb, hne, _, _⟩
  · rfl
  · rfl
  · exact absurd ((by decide : ∀ x ∈ initsBX, x.2 = zeroFact) (m, jb) (inv_bX hjb)) hne

/-- In program 2, a demand whose edges have no exit pattern does not demand the witness: the
    sink node is after the call, which touches `r`, so the flow needs a demand edge of `c` with an
    exit pattern. -/
theorem flow2_no_exit {dn : MethodId → DemandEdge → Prop} (hdn : ∀ m d, dn m d → d.dout = none)
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (h : FlowR RCases.P2 dn M l0 n l) :
    M = 0 → n = 2 → l.base = 2 → False := by
  induction h with
  | start M l0 =>
    intro _ hn _
    exact (by decide : (0 : Node) ≠ 2) hn
  | step _ he _ _ =>
    intro _ hn _
    cases he with
    | head => exact (by decide : (1 : Node) ≠ 2) hn
    | tail _ he => cases he with
      | tail _ he => cases he with
        | head => exact (by decide : (1 : Node) ≠ 2) hn
        | tail _ he => cases he
  | pass _ he hm _ =>
    intro _ _ hl
    cases he with
    | tail _ he => cases he with
      | head =>
        rw [hl] at hm
        exact absurd hm (by decide)
      | tail _ he => cases he with
        | tail _ he => cases he
  | call _ _ _ _ _ hdem _ hdout _ _ _ _ _ =>
    intro _ _ _
    rw [hdn _ _ hdem] at hdout
    cases hdout
  | clean _ he _ _ => exact (RCases.p2_no_clean he).elim
  | filt _ he _ _ => exact (RCases.p2_no_filt he).elim

theorem reach2_no_exit {dn : MethodId → DemandEdge → Prop} (hdn : ∀ m d, dn m d → d.dout = none)
    {M : MethodId} {n : Node} {l : Loc} (h : ReachR RCases.P2 dn [0] M n l) :
    M = 0 → n = 2 → l.base = 2 → False := by
  cases h with
  | root _ hfl => exact flow2_no_exit hdn hfl
  | down _ hE _ _ _ _ _ =>
    intro hM _ _
    cases hE with
    | tail _ hE => cases hE with
      | head => exact (by decide : (1 : MethodId) ≠ 0) hM
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

/-- THE COUNTEREXAMPLE. The backward run of the user's design after `RkX` violates
    `BackwardContractRep` on program 2 (and `B_general` gives `BackwardContractD` for the same
    program and the same `RkX`). -/
theorem B_rep_fails_general :
    ¬ BackwardContractRep RCases.P2 [0] RCases.sinks2 RkX (demOf Pb2 BX) := by
  intro hB
  have hR := hB 0 2 ⟨2, [1, 4, 5], 1⟩ RCases.sink2 1 (List.Mem.head _) rfl RCases.p2_sink_covers
    rkX_reachR ⟨true, Or.inr (Or.inr rfl)⟩
  exact reach2_no_exit (fun _ _ h => demOf_X_none h) hR rfl rfl rfl

#print axioms B_rep_fails_general

/-- For the same program and the same `RkX`, the den-aware contract holds (`B_general`). -/
theorem B_D_holds_X :
    BackwardContractD RCases.P2 [0] RCases.sinks2 RkX (demOf Pb2 BX) :=
  B_general RCases.p2_wf p2_bindStar p2_markRev p2_noZeroBack p2_zeroKept p2_exitReach
    sinks2_kinds (fun M n s b h => by
      rcases h with h | h | h
      · cases h
      · cases h
      · cases h
        exact List.Mem.head _) (fun _ _ h => h)

#print axioms B_D_holds_X

end ApSpec.Backward
