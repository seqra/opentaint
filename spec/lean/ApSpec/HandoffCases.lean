/-
  ApSpec.HandoffCases — test programs for the hand-off of the demand edges only (decision F70):
  the program WRAP (old hand-off against new hand-off), the CEGAR of the condition `Cross`
  (programs ANYW and ANYM), and a getter.

  THE MARK-AWARE RESTRICTION (F71, 2026-10-10): `restrictI` tests the marks too (`insideB`,
  `concMarkB`), and the emission tests a `*∖x` entry mark exactly (`markMatchB`). Every program
  here has the one concrete mark `T` (the run-1 patterns have the mark `*`), so every mark test
  passes. The `decide` facts and the closure invariants are computed with the new definitions,
  and every conclusion of this file still holds (WRAP, ANYW, ANYM, the getter).

  Part 0. `Cross` and `CrossK` as Boolean tests (`cross_iff`), so `decide` can read them.

  Part 1. The program WRAP:
  ```
  root():   x.a.b.c = source();  r = wrap(x);  sink(r.f.a.b.c);   // method 0, sink at node 2
  wrap(x):  ret.f = x;  return ret;                                 // method 1
  ```
  Accessors a=1, b=2, c=3, f=4. Bases zero=0, x=1, r=2, arg=3 (the `x` of `wrap`), ret=4. Mark
  T=1. Every accessor counts. Field limits: forward run 1 L=1, backward run 2 L=2, forward run 3
  L=3. The source is one micro edge from the zero fact to `(x,.a.b.c,$,T)`; `wrap` is the one
  statement `ret.f = arg` (the shortest form of `z = new Z(); z.f = x; return z`). The call binds
  `x` into `arg`, the zero fact into the zero fact (so that the claim "only the zero fact enters
  `wrap`" is not empty), and `ret` back into `r`. The seeds of the backward runs are the sinks of
  the demand vulnerabilities of run 1 (`seedsW_exact`).
  Forward run 1 is computed completely (`inv_w1`). The exit edge of `wrap` is the complete
  summary `(arg,.,*) → (ret,.f,*)`, and it is crossable (`w1_exit_cross`).

  Part 2. THE OLD HAND-OFF (`Backward.revSummaryDemand`, `Backward.demOf`, `restrictU`). Backward
  run 2 enters `wrap` with the non-zero premise `(ret,.f.a,[any],T)` (`old_b2_wrap_init`) and
  hands off `((arg,.a,[any],T), D-p = (ret,.f.a,[any],T))` (`old_dem_w`; exactly:
  `old_demOf_exact` from the complete closure `inv_bo`); forward run 3 emits `(arg,.a.b.c,$,T)`
  into `wrap` (`old_f3_wrap_init`) and cuts INSIDE `wrap`: the demand-layer edge
  `(arg,.a.b.c,$,T) → (ret,.f.a.b,[any],T)` (`old_f3_wrap_cut`), which `wrap` did not have in
  run 1 (`w1_wrap_normal`). For every backward and forward record set.

  Part 3. THE NEW HAND-OFF (`Handoff.handF` with `pubD`, `Handoff.demOfN` with `pubR`,
  `restrictI`; the forward records are the crossable exit edges of run 1, the backward records
  their reversals `revRec`). Backward run 2 (`inv_bn`) and forward run 3 (`inv_fn`) are computed
  completely:
    * the forward hand-off is only the root edge (`handF_w1_exact`): `wrap` gets no backward demand;
    * backward run 2 crosses `wrap` by the reversed record (`bn_cross`) and has only the zero fact
      as an initial fact of `wrap` (`bn_wrap_zero_only`);
    * the backward hand-off gives `wrap` only the zero demand (`demN_exact`);
    * forward run 3 has only the zero fact as an initial fact of `wrap`, and every edge of `wrap`
      is the zero edge (`fn_wrap_zero_only`, `fn_wrap_edges_zero`);
    * forward run 3 still reports the vulnerability (`fn_found`, and nothing else:
      `fn_vuln_exact`): the record of `wrap` applies in the root by `applicable` (not by `satI`,
      `fn_record_applicable`), and the cut is in the root (`fn_cut_in_root`). The witness is a
      recorded witness of the new contracts (`wrap_reachRR`).
  All of WRAP in one statement: `wrap_old_vs_new`.

  Part 4. CEGAR of `Cross`:
    (i) a record with an `[any]` conclusion has an `[any]` reversed premise (`revRec_any_premise`),
        so it is not crossable (`not_cross_of_any`), and a `$` requirement neither satisfies the
        `[any]` premise nor is covered by it (`dollar_blocked`, `any_record_blocks_dollar`, with
        vectors; an `[any]` requirement crosses it);
    (ii) the program ANYW (`ret = anyTaint(arg)`, a normal `[any]` conclusion). A looser hand-off
        that treats such a record as complete (`CrossL`: only the forward conditions, `handFL`)
        drops its leaf. Then the backward run cannot cross the call, it does not reach the source
        (`bl_no_srcHit`), and the next forward run with the source seeds (`FSeeds.keepSources`)
        loses the vulnerability (`fl_lost`). The hand-off with `Cross` keeps the leaf: the backward
        run reaches the source (`bs_srcHit`) and the next forward run reports the vulnerability
        (`fs_found`). In one statement: `cegar_cross_anyw`;
    (ii') the program ANYM (the source in a callee `mk`): the same loss with NO source seeds. The
        looser backward run never reaches the call of `mk`, so the demand-layer summary of `mk` has
        no demand edge with a `D-p`, and the next forward run on the full program reports nothing
        (`flm_lost`); with `Cross` it reports the vulnerability (`fsm_found`). In one statement:
        `cegar_cross_anym`.

  Part 5. A getter `ret = arg.f`: its run-1 summary is in the demand layer (the read is above the
  premise), so it is handed off; the backward run computes a normal backward summary whose reversal
  is crossable, so it is a record of forward run 3, not a demand edge (`demG_exact`). Forward run 3
  has only the zero fact as an initial fact of the getter (`fg_getter_zero_only`) and reports the
  vulnerability in the normal layer by the record (`fg_found`).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffDefs
import ApSpec.ForwardSeeds

namespace ApSpec.HandoffCases
open ApSpec ApSpec.Reverse ApSpec.Handoff

/-! ## Part 0. `Cross` as a Boolean test -/

/-- The Boolean form of `CrossK`. -/
def crossKB : Kind → Bool
  | .exact  => true
  | .star e => e.isEmptyB
  | .any    => false

theorem crossK_iff (k : Kind) : CrossK k ↔ crossKB k = true := by
  cases k with
  | exact => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | any => exact ⟨fun h => h.elim, fun h => Bool.noConfusion h⟩
  | star e =>
    cases e with
    | univ => exact ⟨fun h => (by cases h), fun h => Bool.noConfusion h⟩
    | set xs =>
      cases xs with
      | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | cons a r => exact ⟨fun h => (by cases h), fun h => Bool.noConfusion h⟩

#print axioms crossK_iff

/-- The Boolean form of `MarkRev`. -/
def markRevB (i f : PFact) : Bool :=
  match f.mark with
  | .star     => true
  | .starEx _ => true
  | .conc _   =>
    match i.mark with
    | .conc _ => true
    | _       => false

theorem markRev_iff (i f : PFact) : MarkRev i f ↔ markRevB i f = true := by
  obtain ⟨ib, ip, ik, im⟩ := i
  obtain ⟨fb, fp, fk, fm⟩ := f
  cases fm with
  | star => exact ⟨fun _ => rfl, fun _ => Or.inl (Or.inl rfl)⟩
  | starEx x => exact ⟨fun _ => rfl, fun _ => Or.inl (Or.inr ⟨x, rfl⟩)⟩
  | conc t =>
    cases im with
    | conc u => exact ⟨fun _ => rfl, fun _ => Or.inr ⟨u, rfl⟩⟩
    | star =>
      refine ⟨fun h => ?_, fun h => Bool.noConfusion h⟩
      rcases h with (h | ⟨_, h⟩) | ⟨_, h⟩ <;> cases h
    | starEx y =>
      refine ⟨fun h => ?_, fun h => Bool.noConfusion h⟩
      rcases h with (h | ⟨_, h⟩) | ⟨_, h⟩ <;> cases h

#print axioms markRev_iff

/-- The Boolean form of `Cross`. -/
def crossB (j : PFact) (g : AFact) : Bool :=
  !g.demand && crossKB j.kind && markRevB j g.fact && crossKB (revEdge j g.fact).1.kind

theorem cross_iff (j : PFact) (g : AFact) : Cross j g ↔ crossB j g = true := by
  unfold Cross crossB
  rw [crossK_iff, markRev_iff, crossK_iff]
  cases g.demand <;> cases crossKB j.kind <;> cases markRevB j g.fact <;>
    cases crossKB (revEdge j g.fact).1.kind <;> decide

#print axioms cross_iff

instance (j : PFact) (g : AFact) : Decidable (Cross j g) :=
  decidable_of_iff _ (cross_iff j g).symm

/-- `CrossB` (a normal backward edge with a crossable reversal) is decidable. -/
instance (jb : PFact) (gb : AFact) : Decidable (CrossB jb gb) :=
  inferInstanceAs (Decidable (gb.demand = false ∧ Cross (revRec (jb, gb)).1 (revRec (jb, gb)).2))

/-- The demand edges of a method `m` with no `D-p` give a restriction with no result. -/
theorem restrictI_none {j : PFact} {g : AFact} {d : DemandEdge} (h : d.dout = none) :
    restrictI j g d = none := by
  unfold restrictI
  rw [h]

#print axioms restrictI_none

/-! ## Part 1. The program WRAP and its forward run 1 -/

/-- The `*` tail with the Empty exclusion, and the field limit counter (every accessor counts). -/
def st : Kind := .star (.set [])
def cnt : Acc → Bool := fun _ => true

namespace Wrap

/-- `x.a.b.c = source()`: the zero fact is kept, and one source edge to `(x,.a.b.c,$,T)`. -/
def srcW : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [1, 2, 3], .exact, .conc 1⟩)]⟩
/-- The bindings of `r = wrap(x)`: `x → arg`, the zero fact into the zero fact, `ret → r`. -/
def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def zb : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
def callW : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
/-- `ret.f = arg` (the body of `wrap`). -/
def wr : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨4, [4], st, .star⟩)]⟩
def PW : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt srcW, 1), (0, 1, .call callW, 2), (1, 0, .stmt wr, 1)]⟩
/-- The sink `sink(r.f.a.b.c)` at node 2 of the root. -/
def sinkW : PFact := ⟨2, [4, 1, 2, 3], .exact, .conc 1⟩
def sinksW : List (MethodId × Node × PFact) := [(0, 2, sinkW)]

theorem hE00 : (0, 0, Instr.stmt srcW, 1) ∈ PW.edges := List.Mem.head _

#print axioms hE00

theorem hE01 : (0, 1, Instr.call callW, 2) ∈ PW.edges := List.Mem.tail _ (List.Mem.head _)

#print axioms hE01

theorem hE10 : (1, 0, Instr.stmt wr, 1) ∈ PW.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hE10

theorem pw_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ PW.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pw_no_clean

theorem pw_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ PW.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pw_no_filt

/-! ### The facts -/

/-- The zero fact in the normal layer, and in the demand layer. -/
abbrev Z : AFact := Backward.zeroAF
abbrev Zd : AFact := Backward.Zd
/-- The source pattern `(x,.a.b.c,$,T)`. -/
def Xs : PFact := ⟨1, [1, 2, 3], .exact, .conc 1⟩
/-- `(x,.a,[any],T)`: the source cut to 1 (run 1), and the backward requirement at the source. -/
def Xa : AFact := ⟨⟨1, [1], .any, .conc 1⟩, true⟩
/-- The added fact of `wrap` in run 1: `(arg,.a,[any],T)`. -/
def A1 : PFact := ⟨3, [1], .any, .conc 1⟩
/-- The initial fact of `wrap` in run 1: `(arg,.,*)`, and its start fact. -/
def Jw : PFact := ⟨3, [], st, .star⟩
def Jwf : AFact := ⟨Jw, false⟩
/-- The exit fact of `wrap` in run 1: `(ret,.f,*)`, normal layer. -/
def Gw : AFact := ⟨⟨4, [4], st, .star⟩, false⟩
/-- The root fact at the sink in run 1: `(r,.f,[any],T)` (cut to 1). -/
def R1 : AFact := ⟨⟨2, [4], .any, .conc 1⟩, true⟩

/-! ### Forward run 1, completely -/

abbrev W1 := D PW cnt 1 policy1 sinksW [0]

def initsW1 : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jw)]
def edgesW1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, Xa), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, R1), (1, zeroFact, 0, Z), (1, zeroFact, 1, Z), (1, Jw, 0, Jwf), (1, Jw, 1, Gw)]
def addedsW1 : List (MethodId × PFact) := [(1, zeroFact), (1, A1)]

/-- Every object of forward run 1 is in the lists (no request; one vulnerability, in the demand
    layer). -/
def InvW1 : Obj → Prop
  | .init M i => (M, i) ∈ initsW1
  | .edge M i n f => (M, i, n, f) ∈ edgesW1
  | .added M a => (M, a) ∈ addedsW1
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkW ∧ b = true

instance : DecidablePred InvW1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsW1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesW1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsW1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkW ∧ b = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 1 OF WRAP. -/
theorem inv_w1 {o : Obj} (h : W1 o) : InvW1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsW1,
      InvW1 (.edge x.1 x.2 (PW.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 1 srcW x.2.2.2).facts, InvW1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesW1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 1 wr x.2.2.2).facts, InvW1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 1 srcW x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesW1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 1 wr x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callW.touched = false → InvW1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callW.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvW1 (.added callW.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addedsW1, InvW1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callW.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsW1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edgesW1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callW.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvW1 (.edge 0 x.2.1 2 (limitF cnt 1 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkW = .none ∨ check x.2.1 x.2.2.2 sinkW = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesW1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkW = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pw_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pw_no_clean hE).elim
  | filt _ hE _ _ => exact (pw_no_filt hE).elim

#print axioms inv_w1

/-! ### The objects of forward run 1, derived -/

theorem w1_e00 : W1 (.edge 0 zeroFact 0 Z) := D.start (D.root (List.Mem.head _))

#print axioms w1_e00

theorem w1_x01 : W1 (.edge 0 zeroFact 1 Xa) := D.step w1_e00 (s := srcW) hE00 (by decide)

#print axioms w1_x01

theorem w1_e01 : W1 (.edge 0 zeroFact 1 Z) := D.step w1_e00 (s := srcW) hE00 (by decide)

#print axioms w1_e01

theorem w1_init_w : W1 (.init 1 Jw) := by
  have ad : W1 (.added 1 A1) :=
    D.added (c := callW) (e := bx) (a := ⟨A1, true⟩) w1_x01 hE01 (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinksW)
    (roots := [0]) (P := PW) ad
  have hp : policy1 1 A1 = Jw := by decide
  rw [hp] at h
  exact h

#print axioms w1_init_w

/-- The exit edge of `wrap` in run 1: `(arg,.,*) → (ret,.f,*)`, normal layer. -/
theorem w1_exit_w : W1 (.edge 1 Jw 1 Gw) :=
  D.step (D.start w1_init_w) (s := wr) hE10 (by decide)

#print axioms w1_exit_w

/-- The root edge at the sink in run 1: `(r,.f,[any],T)` (demand layer, the cut in the root). -/
theorem w1_r : W1 (.edge 0 zeroFact 2 R1) :=
  D.ret (c := callW) (e1 := bx) (a := ⟨A1, true⟩) (j := Jw) (g := Gw)
    (r := ⟨⟨4, [4, 1], .any, .conc 1⟩, true⟩) (e2 := br) (r' := ⟨⟨2, [4, 1], .any, .conc 1⟩, true⟩)
    w1_x01 hE01 (List.Mem.head _) (by decide) w1_init_w (by decide) w1_exit_w (by decide)
    (List.Mem.head _) (by decide)

#print axioms w1_r

/-- Run 1 reports the vulnerability, in the demand layer. -/
theorem w1_vuln : W1 (.vuln 0 2 sinkW true) := D.vuln w1_r (List.Mem.head _) (by decide)

#print axioms w1_vuln

/-- THE EXIT EDGE OF WRAP IS CROSSABLE: normal, the premise `*` with the Empty exclusion,
    mark-reversible, and the reversed premise `(ret,.f,*)` is crossable too. -/
theorem w1_exit_cross : Cross Jw Gw := by decide

#print axioms w1_exit_cross

/-- Every exit edge of `wrap` in run 1 is crossable (also the zero edge). -/
theorem w1_wrap_exits_cross {j : PFact} {g : AFact} (h : W1 (.edge 1 j (PW.exit 1) g)) :
    Cross j g :=
  (by decide : ∀ x ∈ edgesW1, x.1 = 1 → x.2.2.1 = 1 → Cross x.2.1 x.2.2.2) (1, j, 1, g)
    (inv_w1 h) rfl rfl

#print axioms w1_wrap_exits_cross

/-- The seeds of the backward run: the sinks of the DEMAND vulnerabilities of run 1 (item 4 of
    the user's decisions). Run 1 reports exactly one vulnerability, in the demand layer. -/
def seedsW : List (MethodId × Node × PFact) := sinksW

theorem seedsW_exact (x : MethodId × Node × PFact) :
    x ∈ seedsW ↔ W1 (.vuln x.1 x.2.1 x.2.2 true) := by
  constructor
  · intro h
    cases h with
    | head => exact w1_vuln
    | tail _ h => cases h
  · intro h
    obtain ⟨M, n, s⟩ := x
    obtain ⟨h1, h2, h3, _⟩ := inv_w1 h
    cases h1; cases h2; cases h3
    exact List.Mem.head _

#print axioms seedsW_exact

/-! ## Part 2. The old hand-off: wrap is analysed again

The reversed program, the backward facts and the forward run-3 facts. -/

/-- The reversed program WRAP. -/
abbrev PbW : Program := Program.rev PW

theorem PbW_edges : PbW.edges =
    [(0, 1, .stmt (Stmt.rev srcW), 0), (0, 2, .call (Call.rev callW), 1),
     (1, 1, .stmt (Stmt.rev wr), 0)] := rfl

#print axioms PbW_edges

theorem hb_src : (0, 1, Instr.stmt (Stmt.rev srcW), 0) ∈ PbW.edges := by
  rw [PbW_edges]; exact List.Mem.head _

#print axioms hb_src

theorem hb_c : (0, 2, Instr.call (Call.rev callW), 1) ∈ PbW.edges := by
  rw [PbW_edges]; exact List.Mem.tail _ (List.Mem.head _)

#print axioms hb_c

theorem hb_w : (1, 1, Instr.stmt (Stmt.rev wr), 0) ∈ PbW.edges := by
  rw [PbW_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hb_w

/-- The seed `(r,.f.a,[any],T)` (`r.f.a.b.c` cut to 2). -/
def Sd : AFact := ⟨⟨2, [4, 1], .any, .conc 1⟩, true⟩
/-- The requirement that the seed gives at the forward exit of `wrap`: `(ret,.f.a,[any],T)`. -/
def Jb : PFact := ⟨4, [4, 1], .any, .conc 1⟩
def Jbt : AFact := ⟨Jb, true⟩
/-- The backward conclusion of `wrap` at its forward entry: `(arg,.a,[any],T)`. -/
def Gb : AFact := ⟨⟨3, [1], .any, .conc 1⟩, true⟩
/-- Forward run 3: the source `(x,.a.b.c,$,T)` (no cut at 3), the added fact of `wrap`. -/
def X3 : AFact := ⟨Xs, false⟩
def A3 : PFact := ⟨3, [1, 2, 3], .exact, .conc 1⟩
/-- Forward run 3 with the old hand-off: the exit fact of `wrap`, `(ret,.f.a.b,[any],T)`, cut
    inside `wrap` (demand layer). -/
def W3 : AFact := ⟨⟨4, [4, 1, 2], .any, .conc 1⟩, true⟩
/-- Forward run 3: the root fact at the sink, `(r,.f.a.b,[any],T)` (demand layer). -/
def Rr3 : AFact := ⟨⟨2, [4, 1, 2], .any, .conc 1⟩, true⟩

/-- The old backward run 2: the reversed summaries of run 1 (EVERY summary edge, in every layer)
    are its demand; the restriction `restrictU`; any record set. -/
abbrev BO (recsB : Recs) : Obj → Prop :=
  Backward.DB PbW cnt 2 (Backward.revSummaryDemand PW W1) emitM satI restrictU recsB [] [0]
    seedsW true

/-- The old backward demand edge of `wrap`: the complete summary of run 1, reversed:
    `((ret,.f,*), D-p = (arg,.,*))`. -/
theorem old_revDem_w : Backward.revSummaryDemand PW W1 1 ⟨Gw.fact, some Jw⟩ :=
  ⟨Jw, Gw.fact, ⟨w1_init_w, Or.inr ⟨Gw, w1_exit_w, rfl⟩⟩, rfl⟩

#print axioms old_revDem_w

section OldBackward
variable (recsB : Recs)

theorem bo_e02 : BO recsB (.edge 0 zeroFact 2 Z) := Backward.DB.start (Backward.DB.root (List.Mem.head _))

#print axioms bo_e02

theorem bo_s02 : BO recsB (.edge 0 zeroFact 2 Sd) :=
  Backward.DB.seed (s := sinkW) (List.Mem.head _) (bo_e02 recsB)

#print axioms bo_s02

theorem bo_add : BO recsB (.added 1 Jb) :=
  Backward.DB.added (c := Call.rev callW) (e := revEdge br.1 br.2) (a := Jbt) (bo_s02 recsB) hb_c
    (List.Mem.head _) (by decide)

#print axioms bo_add

/-- OLD (a), BACKWARD: backward run 2 enters `wrap` with the non-zero premise
    `(ret,.f.a,[any],T)`: the complete summary of run 1 is in the backward demand. -/
theorem old_b2_wrap_init : BO recsB (.init 1 Jb) :=
  Backward.DB.initR (bo_add recsB) old_revDem_w (by decide)

#print axioms old_b2_wrap_init

/-- The backward summary of `wrap`: `(ret,.f.a,[any],T) → (arg,.a,[any],T)`. -/
theorem bo_g1 : BO recsB (.edge 1 Jb 0 Gb) :=
  Backward.DB.step (Backward.DB.start (old_b2_wrap_init recsB)) hb_w (by decide)

#print axioms bo_g1

/-- The old hand-off gives `wrap` the demand edge `((arg,.a,[any],T), D-p = (ret,.f.a,[any],T))`. -/
theorem old_dem_w : Backward.demOf PbW (BO recsB) 1 ⟨Gb.fact, some Jb⟩ :=
  Or.inr (Or.inr ⟨Jb, Gb, old_b2_wrap_init recsB, by decide, bo_g1 recsB, rfl⟩)

#print axioms old_dem_w

/-- The old backward run applies the backward summary of `wrap` in the root: `(x,.a,[any],T)`. -/
theorem bo_x01 : BO recsB (.edge 0 zeroFact 1 Xa) :=
  Backward.DB.ret (c := Call.rev callW) (e1 := revEdge br.1 br.2) (a := Jbt) (j := Jb) (g := Gb)
    (d := ⟨Gw.fact, some Jw⟩) (g' := Gb) (r := Gb) (e2 := revEdge bx.1 bx.2) (r' := Xa)
    (bo_s02 recsB) hb_c (List.Mem.head _) (by decide) (old_b2_wrap_init recsB) (bo_g1 recsB)
    old_revDem_w (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms bo_x01

end OldBackward

/-- The old forward run 3: the demand `Backward.demOf` of the old backward run, `restrictU`, any
    record set. -/
abbrev FO (recsB rc : Recs) : Obj → Prop :=
  DR PW cnt 3 (Backward.demOf PbW (BO recsB)) emitM satI restrictU rc sinksW [0]

section OldForward
variable (recsB rc : Recs)

theorem fo_e00 : FO recsB rc (.edge 0 zeroFact 0 Z) := DR.start (DR.root (List.Mem.head _))

#print axioms fo_e00

theorem fo_x01 : FO recsB rc (.edge 0 zeroFact 1 X3) :=
  DR.step (fo_e00 recsB rc) (s := srcW) hE00 (by decide)

#print axioms fo_x01

theorem fo_add : FO recsB rc (.added 1 A3) :=
  DR.added (c := callW) (e := bx) (a := ⟨A3, false⟩) (fo_x01 recsB rc) hE01 (List.Mem.head _)
    (by decide)

#print axioms fo_add

/-- OLD (a), FORWARD: forward run 3 emits the non-zero initial fact `(arg,.a.b.c,$,T)` into
    `wrap`. -/
theorem old_f3_wrap_init : FO recsB rc (.init 1 A3) :=
  DR.initR (fo_add recsB rc) (old_dem_w recsB) (by decide)

#print axioms old_f3_wrap_init

/-- OLD (a), FORWARD: THE CUT INSIDE WRAP. Forward run 3 has the demand-layer edge
    `(arg,.a.b.c,$,T) → (ret,.f.a.b,[any],T)` in `wrap` (run 1 had no demand-layer edge in
    `wrap`: `inv_w1`). -/
theorem old_f3_wrap_cut : FO recsB rc (.edge 1 A3 1 W3) ∧ W3.demand = true :=
  ⟨DR.step (DR.start (old_f3_wrap_init recsB rc)) (s := wr) hE10 (by decide), rfl⟩

#print axioms old_f3_wrap_cut

/-- The old forward run 3 reports the vulnerability too (through the summary of `wrap`, restricted
    by the old demand edge). -/
theorem old_f3_found : FO recsB rc (.vuln 0 2 sinkW true) := by
  have e2 : FO recsB rc (.edge 0 zeroFact 2 (limitF cnt 3 Rr3)) :=
    DR.ret (c := callW) (e1 := bx) (a := ⟨A3, false⟩) (j := A3) (g := W3) (d := ⟨Gb.fact, some Jb⟩)
      (g' := W3) (r := ⟨⟨4, [4, 1, 2], .any, .conc 1⟩, true⟩) (e2 := br) (r' := Rr3)
      (fo_x01 recsB rc) hE01 (List.Mem.head _) (by decide) (old_f3_wrap_init recsB rc)
      (old_f3_wrap_cut recsB rc).1 (old_dem_w recsB) (by decide) (by decide) (by decide)
      (List.Mem.head _) (by decide)
  exact DR.vuln e2 (s := sinkW) (List.Mem.head _) (by decide)

#print axioms old_f3_found

end OldForward

/-- In run 1 `wrap` has no demand-layer edge (so the cut inside `wrap` is new in forward run 3). -/
theorem w1_wrap_normal {j : PFact} {n : Node} {g : AFact} (h : W1 (.edge 1 j n g)) :
    g.demand = false :=
  (by decide : ∀ x ∈ edgesW1, x.1 = 1 → x.2.2.2.demand = false) (1, j, n, g) (inv_w1 h) rfl

#print axioms w1_wrap_normal

/-! ### The old backward run 2, completely (no backward record)

The complete closure gives the old hand-off EXACTLY: `wrap` gets the demand edge
`((arg,.a,[any],T), D-p = (ret,.f.a,[any],T))` from the summary that run 1 had already completed. -/

/-- The reversed summaries of run 1: the old backward demand. -/
def revDemW : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, some zeroFact⟩), (0, ⟨R1.fact, some zeroFact⟩),
   (1, ⟨zeroFact, some zeroFact⟩), (1, ⟨Gw.fact, some Jw⟩)]

theorem revDemW_bound {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand PW W1 m d) : (m, d) ∈ revDemW := by
  obtain ⟨j, g, ⟨_, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · cases hgg
    exact (by decide : ∀ x ∈ edgesW1, x.2.2.1 = PW.exit x.1 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ revDemW) (m, j, _, g') (inv_w1 hg') rfl

#print axioms revDemW_bound

def noRecs : Recs := fun _ _ => False

def initsBO : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jb)]
def edgesBO : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Z), (0, zeroFact, 2, Sd), (0, zeroFact, 1, Z), (0, zeroFact, 1, Xa),
   (0, zeroFact, 0, Z), (0, zeroFact, 0, Zd), (0, zeroFact, 0, Xa),
   (1, zeroFact, 1, Z), (1, zeroFact, 0, Z), (1, Jb, 1, Jbt), (1, Jb, 0, Gb)]
def addedsBO : List (MethodId × PFact) := [(1, Jb)]

def InvBO : Obj → Prop
  | .init M i => (M, i) ∈ initsBO
  | .edge M i n f => (M, i, n, f) ∈ edgesBO
  | .added M a => (M, a) ∈ addedsBO
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBO := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBO))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBO))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBO))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE OLD BACKWARD RUN 2 OF WRAP (no backward record). -/
theorem inv_bo {o : Obj} (h : BO noRecs o) : InvBO o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBO, InvBO (.edge x.1 x.2 (PbW.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [PbW_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBO, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 2 (Stmt.rev srcW) x.2.2.2).facts, InvBO (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBO, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 2 (Stmt.rev wr) x.2.2.2).facts, InvBO (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [PbW_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBO, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 2 (Stmt.rev srcW) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBO, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 2 (Stmt.rev wr) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBO, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callW).touched = false →
            InvBO (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBO, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev callW).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBO (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ revDemW, ∀ y ∈ addedsBO, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvBO (.init x.1 j))
      (m, d) (revDemW_bound hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBO, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callW).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsBO, y.1 = 1 →
          ∀ z ∈ edgesBO, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ revDemW, dd.1 = 1 → ∀ g' ∈ (restrictU y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Call.rev callW).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBO (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (revDemW_bound hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [PbW_edges] at hE
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
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBO, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev callW).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBO (.edge 0 zeroFact 1 (limitF cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_bo

/-- THE OLD HAND-OFF, EXACTLY: the zero demand, the root edge `((x,.a,[any],T), none)`, and the
    demand edge `((arg,.a,[any],T), D-p = (ret,.f.a,[any],T))` of `wrap`. -/
theorem old_demOf_exact (m : MethodId) (d : DemandEdge) :
    Backward.demOf PbW (BO noRecs) m d ↔ d = Backward.zeroDem ∨ (m = 0 ∧ d = ⟨Xa.fact, none⟩) ∨
      (m = 1 ∧ d = ⟨Gb.fact, some Jb⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, hgb, rfl⟩)
    · exact Or.inl h
    · exact (by decide : ∀ x ∈ edgesBO, x.2.1 = zeroFact → x.2.2.1 = PbW.exit x.1 →
        (⟨x.2.2.2.fact, none⟩ : DemandEdge) = Backward.zeroDem ∨
          (x.1 = 0 ∧ (⟨x.2.2.2.fact, none⟩ : DemandEdge) = ⟨Xa.fact, none⟩) ∨
          (x.1 = 1 ∧ (⟨x.2.2.2.fact, none⟩ : DemandEdge) = ⟨Gb.fact, some Jb⟩))
        (m, zeroFact, PbW.exit m, g) (inv_bo hg) rfl rfl
    · exact (by decide : ∀ x ∈ initsBO, x.2 ≠ zeroFact →
        ∀ y ∈ edgesBO, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = PbW.exit x.1 →
          (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge) = Backward.zeroDem ∨
          (x.1 = 0 ∧ (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge) = ⟨Xa.fact, none⟩) ∨
          (x.1 = 1 ∧ (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge) = ⟨Gb.fact, some Jb⟩))
        (m, jb) (inv_bo hjb) hne (m, jb, PbW.exit m, gb) (inv_bo hgb) rfl rfl rfl
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Xa, Backward.DB.step (bo_x01 noRecs) hb_src (by decide), rfl⟩)
    · exact old_dem_w noRecs

#print axioms old_demOf_exact

/-! ## Part 3. The new hand-off: wrap is complete after run 1 -/

/-! ### The forward hand-off and the backward records -/

/-- THE FORWARD HAND-OFF OF RUN 1, EXACTLY: only the root edge `zero → (r,.f,[any],T)` (demand
    layer). The exit edges of `wrap` are crossable, so `wrap` gets no backward demand. -/
theorem handF_w1_exact (m : MethodId) (d : DemandEdge) :
    handF PW W1 pubD m d ↔ m = 0 ∧ d = ⟨R1.fact, some zeroFact⟩ := by
  constructor
  · rintro ⟨j, g, g', _, hg, hnc, hpub, rfl⟩
    cases hpub
    exact (by decide : ∀ x ∈ edgesW1, x.2.2.1 = PW.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
      x.1 = 0 ∧ (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge) = ⟨R1.fact, some zeroFact⟩)
      (m, j, PW.exit m, g) (inv_w1 hg) rfl hnc
  · rintro ⟨rfl, rfl⟩
    exact ⟨zeroFact, R1, R1, D.root (List.Mem.head _), w1_r, by decide, rfl, rfl⟩

#print axioms handF_w1_exact

/-- `wrap` gets no backward demand edge. -/
theorem handF_w1_wrap (d : DemandEdge) : ¬ handF PW W1 pubD 1 d := fun h =>
  absurd ((handF_w1_exact 1 d).mp h).1 (by decide)

#print axioms handF_w1_wrap

/-- The backward records: the reversals of the crossable exit edges of run 1 (`hrecB` of the
    brief with the empty record set of run 1). -/
def recsB1 : Recs := fun m y =>
  ∃ x : PFact × AFact, W1 (.init m x.1) ∧ W1 (.edge m x.1 (PW.exit m) x.2) ∧ Cross x.1 x.2 ∧
    y = revRec x

def recListB : List (MethodId × (PFact × AFact)) :=
  [(0, revRec (zeroFact, Z)), (1, revRec (zeroFact, Z)), (1, revRec (Jw, Gw))]

theorem recsB1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ recListB := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ edgesW1, e.2.2.1 = PW.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ recListB) (m, x.1, PW.exit m, x.2) (inv_w1 hx) rfl hc

#print axioms recsB1_bound

/-- The reversed record of `wrap`: `(ret,.f,*) → (arg,.,*)`. -/
theorem recsB1_w : recsB1 1 (revRec (Jw, Gw)) := ⟨(Jw, Gw), w1_init_w, w1_exit_w, w1_exit_cross, rfl⟩

#print axioms recsB1_w

/-! ### Backward run 2 with the new hand-off, completely -/

/-- The new backward run 2: the demand `handF` (with `pubD`), the restriction `restrictI`, the
    reversed crossable records. -/
abbrev BN : Obj → Prop :=
  Backward.DB PbW cnt 2 (handF PW W1 pubD) emitM satI restrictI recsB1 [] [0] seedsW true

def initsBN : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact)]
def edgesBN : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Z), (0, zeroFact, 2, Sd), (0, zeroFact, 1, Z), (0, zeroFact, 1, Xa),
   (0, zeroFact, 0, Z), (0, zeroFact, 0, Zd), (0, zeroFact, 0, Xa),
   (1, zeroFact, 1, Z), (1, zeroFact, 0, Z)]
def addedsBN : List (MethodId × PFact) := [(1, Jb)]

def InvBN : Obj → Prop
  | .init M i => (M, i) ∈ initsBN
  | .edge M i n f => (M, i, n, f) ∈ edgesBN
  | .added M a => (M, a) ∈ addedsBN
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBN := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBN))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBN))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBN))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE NEW BACKWARD RUN 2 OF WRAP. -/
theorem inv_bn {o : Obj} (h : BN o) : InvBN o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBN, InvBN (.edge x.1 x.2 (PbW.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [PbW_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBN, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 2 (Stmt.rev srcW) x.2.2.2).facts, InvBN (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBN, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 2 (Stmt.rev wr) x.2.2.2).facts, InvBN (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [PbW_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBN, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 2 (Stmt.rev srcW) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBN, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 2 (Stmt.rev wr) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBN, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callW).touched = false →
            InvBN (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBN, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev callW).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBN (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd _ ih =>
    have hm : m = 1 := (by decide : ∀ y ∈ addedsBN, y.1 = 1) (m, a) ih
    subst hm
    exact (handF_w1_wrap d hd).elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE _ _ _ _ hd _ _ _ _ _ _ _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => exact (handF_w1_wrap d hd).elim
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBN, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callW).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListB, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ (Call.rev callW).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBN (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (recsB1_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [PbW_edges] at hE
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
    rw [PbW_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBN, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev callW).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBN (.edge 0 zeroFact 1 (limitF cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_bn

/-- NEW (b), BACKWARD: backward run 2 has only the zero fact as an initial fact of `wrap`. -/
theorem bn_wrap_zero_only {j : PFact} (h : BN (.init 1 j)) : j = zeroFact :=
  (by decide : ∀ x ∈ initsBN, x.1 = 1 → x.2 = zeroFact) (1, j) (inv_bn h) rfl

#print axioms bn_wrap_zero_only

/-- Every edge of `wrap` in the new backward run 2 has the zero premise. -/
theorem bn_wrap_edges_zero {j : PFact} {n : Node} {g : AFact} (h : BN (.edge 1 j n g)) :
    j = zeroFact :=
  (by decide : ∀ x ∈ edgesBN, x.1 = 1 → x.2.1 = zeroFact) (1, j, n, g) (inv_bn h) rfl

#print axioms bn_wrap_edges_zero

/-! ### The objects of the new backward run 2, derived -/

theorem bn_e02 : BN (.edge 0 zeroFact 2 Z) := Backward.DB.start (Backward.DB.root (List.Mem.head _))

#print axioms bn_e02

theorem bn_s02 : BN (.edge 0 zeroFact 2 Sd) :=
  Backward.DB.seed (s := sinkW) (List.Mem.head _) bn_e02

#print axioms bn_s02

/-- NEW (b), BACKWARD: the backward run CROSSES `wrap` by the reversed record
    `(ret,.f,*) → (arg,.,*)`: the requirement `(ret,.f.a,[any],T)` is covered by its premise
    (`applicable`), and the result `(x,.a,[any],T)` reaches the source in the root. -/
theorem bn_cross : BN (.edge 0 zeroFact 1 Xa) :=
  Backward.DB.retRec (c := Call.rev callW) (e1 := revEdge br.1 br.2) (a := Jbt)
    (j := (revRec (Jw, Gw)).1) (g := (revRec (Jw, Gw)).2) (r := Gb)
    (e2 := revEdge bx.1 bx.2) (r' := Xa) bn_s02 hb_c (List.Mem.head _) (by decide) recsB1_w
    (Or.inr (by decide)) (by decide) (List.Mem.head _) (by decide)

#print axioms bn_cross

theorem bn_x00 : BN (.edge 0 zeroFact 0 Xa) := Backward.DB.step bn_cross hb_src (by decide)

#print axioms bn_x00

/-! ### The backward hand-off -/

/-- The demand of forward run 3: `demOfN` of the new backward run with `pubR`. -/
def demN : MethodId → DemandEdge → Prop := demOfN PbW BN (pubR (handF PW W1 pubD))

/-- THE BACKWARD HAND-OFF, EXACTLY: the zero demand, and the root edge `((x,.a,[any],T), none)`.
    `wrap` gets only the zero demand. -/
theorem demN_exact (m : MethodId) (d : DemandEdge) :
    demN m d ↔ d = Backward.zeroDem ∨ (m = 0 ∧ d = ⟨Xa.fact, none⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, _, _, _, _⟩)
    · exact Or.inl h
    · exact (by decide : ∀ x ∈ edgesBN, x.2.1 = zeroFact → x.2.2.1 = PbW.exit x.1 →
        (⟨x.2.2.2.fact, none⟩ : DemandEdge) = Backward.zeroDem ∨
          (x.1 = 0 ∧ (⟨x.2.2.2.fact, none⟩ : DemandEdge) = ⟨Xa.fact, none⟩))
        (m, zeroFact, PbW.exit m, g) (inv_bn hg) rfl rfl
    · exact absurd ((by decide : ∀ x ∈ initsBN, x.2 = zeroFact) (m, jb) (inv_bn hjb)) hne
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Xa, bn_x00, rfl⟩)

#print axioms demN_exact

def demListN : List DemandEdge := [Backward.zeroDem, ⟨Xa.fact, none⟩]

theorem demN_bound {m : MethodId} {d : DemandEdge} (h : demN m d) : d ∈ demListN := by
  rcases (demN_exact m d).mp h with rfl | ⟨_, rfl⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

#print axioms demN_bound

/-- No demand edge of forward run 3 has a `D-p`. -/
theorem demN_dout {m : MethodId} {d : DemandEdge} (h : demN m d) : d.dout = none :=
  (by decide : ∀ x ∈ demListN, x.dout = none) d (demN_bound h)

#print axioms demN_dout

/-! ### Forward run 3 with the new hand-off, completely -/

/-- The records of forward run 3: the crossable exit edges of run 1, and the reversals of the
    NORMAL backward exit edges with a non-zero premise and a crossable reversal (`CrossB`; `hrcN`
    of the brief, with the empty record set of run 1). -/
def rc3 : Recs := fun m x =>
  (W1 (.init m x.1) ∧ W1 (.edge m x.1 (PW.exit m) x.2) ∧ Cross x.1 x.2) ∨
  (∃ jb gb, BN (.init m jb) ∧ jb ≠ zeroFact ∧ BN (.edge m jb (PbW.exit m) gb) ∧
    CrossB jb gb ∧ x = revRec (jb, gb))

def recListF : List (MethodId × (PFact × AFact)) :=
  [(0, (zeroFact, Z)), (1, (zeroFact, Z)), (1, (Jw, Gw))]

theorem rc3_bound {m : MethodId} {x : PFact × AFact} (h : rc3 m x) : (m, x) ∈ recListF := by
  rcases h with ⟨_, hx, hc⟩ | ⟨jb, _, hjb, hne, _⟩
  · exact (by decide : ∀ e ∈ edgesW1, e.2.2.1 = PW.exit e.1 → Cross e.2.1 e.2.2.2 →
      (e.1, (e.2.1, e.2.2.2)) ∈ recListF) (m, x.1, PW.exit m, x.2) (inv_w1 hx) rfl hc
  · exact absurd ((by decide : ∀ x ∈ initsBN, x.2 = zeroFact) (m, jb) (inv_bn hjb)) hne

#print axioms rc3_bound

/-- The record of `wrap` in forward run 3: its run-1 exit edge `(arg,.,*) → (ret,.f,*)`. -/
theorem rc3_w : rc3 1 (Jw, Gw) := Or.inl ⟨w1_init_w, w1_exit_w, w1_exit_cross⟩

#print axioms rc3_w

/-- The new forward run 3: the demand `demN`, the restriction `restrictI`, the records `rc3`. -/
abbrev FN : Obj → Prop := DR PW cnt 3 demN emitM satI restrictI rc3 sinksW [0]

def initsFN : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact)]
def edgesFN : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X3), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, Rr3), (1, zeroFact, 0, Z), (1, zeroFact, 1, Z)]
def addedsFN : List (MethodId × PFact) := [(1, zeroFact), (1, A3)]

def InvFN : Obj → Prop
  | .init M i => (M, i) ∈ initsFN
  | .edge M i n f => (M, i, n, f) ∈ edgesFN
  | .added M a => (M, a) ∈ addedsFN
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkW ∧ b = true

instance : DecidablePred InvFN := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsFN))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesFN))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsFN))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkW ∧ b = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE NEW FORWARD RUN 3 OF WRAP. -/
theorem inv_fn {o : Obj} (h : FN o) : InvFN o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsFN,
      InvFN (.edge x.1 x.2 (PW.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 srcW x.2.2.2).facts, InvFN (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFN, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 wr x.2.2.2).facts, InvFN (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 srcW x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFN, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 wr x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callW.touched = false → InvFN (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callW.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvFN (.added callW.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ demListN, ∀ y ∈ addedsFN,
      ∀ j ∈ (emitM x.din y.2).toList, InvFN (.init y.1 j))
      d (demN_bound hd) (m, a) ih j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hres _ _ _ _ _ _ _ =>
    rw [restrictI_none (demN_dout hd)] at hres
    cases hres
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callW.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListF, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ callW.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvFN (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (rc3_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkW = .none ∨ check x.2.1 x.2.2.2 sinkW = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesFN, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkW = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pw_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pw_no_clean hE).elim
  | filt _ hE _ _ => exact (pw_no_filt hE).elim

#print axioms inv_fn

/-- NEW (b), FORWARD: forward run 3 has only the zero fact as an initial fact of `wrap`. -/
theorem fn_wrap_zero_only {j : PFact} (h : FN (.init 1 j)) : j = zeroFact :=
  (by decide : ∀ x ∈ initsFN, x.1 = 1 → x.2 = zeroFact) (1, j) (inv_fn h) rfl

#print axioms fn_wrap_zero_only

/-- NEW (b), FORWARD: every edge of `wrap` in forward run 3 has the zero premise and is in the
    normal layer: no edge of `wrap` leaves the zero premise, and there is no cut inside `wrap`. -/
theorem fn_wrap_edges_zero {j : PFact} {n : Node} {g : AFact} (h : FN (.edge 1 j n g)) :
    j = zeroFact ∧ g = Z :=
  (by decide : ∀ x ∈ edgesFN, x.1 = 1 → x.2.1 = zeroFact ∧ x.2.2.2 = Z) (1, j, n, g)
    (inv_fn h) rfl

#print axioms fn_wrap_edges_zero

/-! ### Forward run 3 still reports the vulnerability -/

theorem fn_e00 : FN (.edge 0 zeroFact 0 Z) := DR.start (DR.root (List.Mem.head _))

#print axioms fn_e00

theorem fn_x01 : FN (.edge 0 zeroFact 1 X3) := DR.step fn_e00 (s := srcW) hE00 (by decide)

#print axioms fn_x01

/-- The record of `wrap` applies to the caller fact `(arg,.a.b.c,$,T)` by `applicable` (its
    premise `(arg,.,*)` covers the fact); the fact does not satisfy it by `satI`. -/
theorem fn_record_applicable : satI Jw A3 = false ∧ applicable Jw A3 = true := by decide

#print axioms fn_record_applicable

/-- NEW (b): THE CUT IS IN THE ROOT. The record of `wrap` gives `(ret,.f.a.b.c,$,T)` in the normal
    layer; the binding back gives `(r,.f.a.b.c,$,T)`, and the field limit 3 of the ROOT cuts it to
    `(r,.f.a.b,[any],T)` (demand layer). -/
theorem fn_cut_in_root : FN (.edge 0 zeroFact 2 Rr3) ∧ Rr3.demand = true :=
  ⟨DR.retRec (c := callW) (e1 := bx) (a := ⟨A3, false⟩) (j := Jw) (g := Gw)
    (r := ⟨⟨4, [4, 1, 2, 3], .exact, .conc 1⟩, false⟩) (e2 := br)
    (r' := ⟨⟨2, [4, 1, 2, 3], .exact, .conc 1⟩, false⟩) fn_x01 hE01 (List.Mem.head _) (by decide)
    rc3_w (Or.inr fn_record_applicable.2) (by decide) (List.Mem.head _) (by decide), rfl⟩

#print axioms fn_cut_in_root

/-- NEW (b): FORWARD RUN 3 STILL REPORTS THE VULNERABILITY (in the demand layer, as run 1). -/
theorem fn_found : FN (.vuln 0 2 sinkW true) :=
  DR.vuln fn_cut_in_root.1 (s := sinkW) (List.Mem.head _) (by decide)

#print axioms fn_found

/-- And it reports nothing else. -/
theorem fn_vuln_exact {M : MethodId} {n : Node} {s : PFact} {b : Bool} :
    FN (.vuln M n s b) ↔ M = 0 ∧ n = 2 ∧ s = sinkW ∧ b = true := by
  constructor
  · exact fun h => inv_fn h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact fn_found

#print axioms fn_vuln_exact

/-! ### The witness is a recorded witness of the new contracts -/

def l0 : Loc := ⟨1, [1, 2, 3], 1⟩
def l1 : Loc := ⟨3, [1, 2, 3], 1⟩
def l2 : Loc := ⟨4, [4, 1, 2, 3], 1⟩
def l3 : Loc := ⟨2, [4, 1, 2, 3], 1⟩

theorem den_src : den zeroFact Xs zeroLoc l0 :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

#print axioms den_src

theorem den_in : den bx.1 bx.2 l0 l1 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 2, 3], [1, 2, 3], rfl, rfl, rfl, rfl, rfl⟩

#print axioms den_in

theorem den_w : den Jw Gw.fact l1 l2 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 2, 3], [1, 2, 3], rfl, rfl, rfl, rfl, rfl⟩

#print axioms den_w

theorem den_out : den br.1 br.2 l2 l3 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [4, 1, 2, 3], [4, 1, 2, 3], rfl, rfl, rfl, rfl, rfl⟩

#print axioms den_out

theorem sinkW_covers : sinkW.covers l3 := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms sinkW_covers

/-- The real witness of WRAP is a witness of the input of forward run 3 (`ReachRR`): the call of
    `wrap` is RECORDED (`FlowRR.rcall` by the crossable record `(arg,.,*) → (ret,.f,*)`), not
    demanded. So the contracts of the new hand-off need no demand edge in `wrap`. -/
theorem wrap_reachRR : ReachRR PW demN rc3 [0] 0 2 l3 := by
  have f0 : FlowRR PW demN rc3 0 zeroLoc 1 l0 :=
    FlowRR.step (FlowRR.start 0 zeroLoc) (s := srcW) hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have f2 : FlowRR PW demN rc3 0 zeroLoc 2 l3 :=
    FlowRR.rcall f0 (c := callW) hE01 (List.Mem.head _) den_in rc3_w w1_exit_cross
      ⟨rfl, ⟨[1, 2, 3], rfl, rfl⟩, trivial⟩ den_w (List.Mem.head _) den_out
  exact ReachRR.root (List.Mem.head _) f2

#print axioms wrap_reachRR

/-! ### WRAP in one statement -/

/-- THE PROGRAM WRAP, OLD AGAINST NEW. Run 1 gives `wrap` the crossable complete summary and
    reports the vulnerability in the demand layer. (a) With the old hand-off, backward run 2 and
    forward run 3 analyse `wrap` again from a non-zero initial fact, and forward run 3 cuts INSIDE
    `wrap` (for every record set). (b) With the new hand-off, backward run 2 and forward run 3
    have only the zero fact as an initial fact of `wrap`, every edge of `wrap` in forward run 3 is
    the zero edge, and forward run 3 still reports the vulnerability, with the cut in the ROOT. -/
theorem wrap_old_vs_new :
    Cross Jw Gw ∧ W1 (.vuln 0 2 sinkW true) ∧
    (∀ recsB, BO recsB (.init 1 Jb) ∧ Jb ≠ zeroFact) ∧
    (∀ recsB rc, FO recsB rc (.init 1 A3) ∧ A3 ≠ zeroFact ∧ FO recsB rc (.edge 1 A3 1 W3) ∧
      W3.demand = true) ∧
    (∀ j, BN (.init 1 j) → j = zeroFact) ∧
    (∀ j, FN (.init 1 j) → j = zeroFact) ∧
    (∀ j n g, FN (.edge 1 j n g) → j = zeroFact ∧ g = Z) ∧
    FN (.vuln 0 2 sinkW true) ∧ FN (.edge 0 zeroFact 2 Rr3) ∧ Rr3.demand = true :=
  ⟨w1_exit_cross, w1_vuln, fun recsB => ⟨old_b2_wrap_init recsB, by decide⟩,
   fun recsB rc => ⟨old_f3_wrap_init recsB rc, by decide, (old_f3_wrap_cut recsB rc).1, rfl⟩,
   fun _ h => bn_wrap_zero_only h, fun _ h => fn_wrap_zero_only h,
   fun _ _ _ h => fn_wrap_edges_zero h, fn_found, fn_cut_in_root.1, rfl⟩

#print axioms wrap_old_vs_new

end Wrap

/-! ## Part 4. CEGAR of `Cross`

### (i) A record with an `[any]` conclusion has an `[any]` reversed premise

The base model's normal `[any]` conclusion is the `[any-taint]` of decision F69. Its reversal has
the premise `[any]` for every premise tail (`revKinds _ .any`), so the record is not crossable,
and a `$` requirement neither satisfies that premise (`satI`) nor is covered by it
(`applicable`): the backward run cannot cross the record, so the edge must stay in the hand-off. -/

theorem revKinds_any (k : Kind) : (revKinds k .any).1 = .any := by
  cases k <;> rfl

#print axioms revKinds_any

/-- The reversed premise of a record with an `[any]` conclusion is `[any]`. -/
theorem revRec_any_premise {x : PFact × AFact} (h : x.2.fact.kind = .any) :
    (revRec x).1.kind = .any := by
  obtain ⟨⟨ib, ip, ik, im⟩, ⟨⟨fb, fp, fk, fm⟩, fd⟩⟩ := x
  change fk = .any at h
  subst h
  cases ik <;> rfl

#print axioms revRec_any_premise

/-- A record with an `[any]` conclusion is not crossable. -/
theorem not_cross_of_any {j : PFact} {g : AFact} (h : g.fact.kind = .any) : ¬ Cross j g := by
  rintro ⟨_, _, _, hk⟩
  have h1 : (revEdge j g.fact).1.kind = .any := revRec_any_premise (x := (j, g)) h
  rw [h1] at hk
  exact hk

#print axioms not_cross_of_any

/-- A `$` pattern does not cover an `[any]` pattern. -/
theorem coversB_exact_any {i c : PFact} (hi : i.kind = .exact) (hc : c.kind = .any) :
    coversB i c = false := by
  unfold coversB
  rw [hi, hc]
  cases dropPrefix i.path c.path with
  | none => simp
  | some r =>
    cases r with
    | nil => simp [tailSubB]
    | cons x r => simp [admitsTailB]

#print axioms coversB_exact_any

/-- A `$` requirement neither satisfies an `[any]` premise nor is covered by it. -/
theorem dollar_blocked {j a : PFact} (hj : j.kind = .any) (ha : a.kind = .exact) :
    satI j a = false ∧ applicable j a = false := by
  constructor
  · unfold satI
    rw [coversB_exact_any (i := ⟨a.base, a.path, a.kind, .star⟩) ha hj]
    rfl
  · unfold applicable
    rw [hj, ha]
    simp [Kind.isAny]

#print axioms dollar_blocked

/-- THE CEGAR OF `Cross` (i): the reversal of a record with an `[any]` conclusion cannot be crossed
    by a `$` requirement, by `satI` or by `applicable` (the two rules `DB.retRec` reads). -/
theorem any_record_blocks_dollar (x : PFact × AFact) (hg : x.2.fact.kind = .any) (a : PFact)
    (ha : a.kind = .exact) :
    ¬ Cross x.1 x.2 ∧ satI (revRec x).1 a = false ∧ applicable (revRec x).1 a = false :=
  ⟨not_cross_of_any hg, dollar_blocked (revRec_any_premise hg) ha⟩

#print axioms any_record_blocks_dollar

/-- The looser condition: only the FORWARD conditions of `Cross` (a normal edge, a crossable
    premise, mark-reversible), without the condition on the reversed premise. -/
def CrossL (j : PFact) (g : AFact) : Prop :=
  g.demand = false ∧ CrossK j.kind ∧ MarkRev j g.fact

def crossLB (j : PFact) (g : AFact) : Bool :=
  !g.demand && crossKB j.kind && markRevB j g.fact

theorem crossL_iff (j : PFact) (g : AFact) : CrossL j g ↔ crossLB j g = true := by
  unfold CrossL crossLB
  rw [crossK_iff, markRev_iff]
  cases g.demand <;> cases crossKB j.kind <;> cases markRevB j g.fact <;> decide

#print axioms crossL_iff

instance (j : PFact) (g : AFact) : Decidable (CrossL j g) :=
  decidable_of_iff _ (crossL_iff j g).symm

theorem crossL_of_cross {j : PFact} {g : AFact} (h : Cross j g) : CrossL j g :=
  ⟨h.1, h.2.1, h.2.2.1⟩

#print axioms crossL_of_cross

/-- THE LOOSER HAND-OFF: `handF` with `CrossL` in place of `Cross`. It drops every edge that is
    complete in the forward direction only (such as a normal `[any]` leaf). -/
def handFL (P : Program) (R : Obj → Prop) (pub : Pub) (m : MethodId) (d : DemandEdge) : Prop :=
  ∃ j g g', R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ ¬ CrossL j g ∧ pub m j g g' ∧
    d = ⟨g'.fact, some j⟩

/-- The looser hand-off hands off less: it is inside `handF`. -/
theorem handFL_sub {P : Program} {R : Obj → Prop} {pub : Pub} {m : MethodId} {d : DemandEdge}
    (h : handFL P R pub m d) : handF P R pub m d := by
  obtain ⟨j, g, g', hj, hg, hn, hp, hd⟩ := h
  exact ⟨j, g, g', hj, hg, fun hc => hn (crossL_of_cross hc), hp, hd⟩

#print axioms handFL_sub

namespace VecCross

/-- The record of `ret = anyTaint(arg)`: `(arg,.,*) → (ret,.,[any])`, normal layer. -/
def jA : PFact := ⟨3, [], st, .star⟩
def gA : AFact := ⟨⟨4, [], .any, .star⟩, false⟩

-- the reversal: `(ret,.,[any]) → (arg,.,[any])`
example : revRec (jA, gA) = (⟨4, [], .any, .star⟩, ⟨⟨3, [], .any, .star⟩, false⟩) := by decide
-- not crossable, but the looser condition holds
example : ¬ Cross jA gA := by decide
example : CrossL jA gA := by decide
-- `$` requirements at and below the reversed premise: not satisfied, not covered
example : satI (revRec (jA, gA)).1 ⟨4, [], .exact, .conc 1⟩ = false := by decide
example : applicable (revRec (jA, gA)).1 ⟨4, [], .exact, .conc 1⟩ = false := by decide
example : satI (revRec (jA, gA)).1 ⟨4, [4], .exact, .conc 1⟩ = false := by decide
example : applicable (revRec (jA, gA)).1 ⟨4, [4], .exact, .conc 1⟩ = false := by decide
-- an `[any]` requirement crosses it (at the premise by `satI`, below it by `applicable`)
example : satI (revRec (jA, gA)).1 ⟨4, [], .any, .conc 1⟩ = true := by decide
example : applicable (revRec (jA, gA)).1 ⟨4, [4], .any, .conc 1⟩ = true := by decide
-- every premise tail gives the reversed premise `[any]`
example : ∀ k ∈ [Kind.exact, .any, .star (.set []), .star (.set [1]), .star .univ],
    (revKinds k .any).1 = .any := by decide
-- the crossable record of WRAP: the `$` requirement below its reversed premise is covered
example : applicable (revRec (Wrap.Jw, Wrap.Gw)).1 ⟨4, [4, 1], .exact, .conc 1⟩ = true := by decide

end VecCross

/-! ### (ii) The program ANYW: the looser hand-off loses a vulnerability

```
root():  x.a.b = source();  r = anyw(x);  sink(r.f);   // method 0, sink at node 2
anyw(x): ret = anyTaint(x);  return ret;               // method 1: (arg,.,*) → (ret,.,[any])
```
Accessors a=1, b=2, f=4; bases as in WRAP. Field limits 1, 2, 3; seeds: the sinks of the demand
vulnerabilities of run 1. Forward run 1 cuts the source to `(x,.a,[any],T)` (demand layer) and
reports the vulnerability in the demand layer (so it is seeded). The exit edge
`(arg,.,*) → (ret,.,[any])` of `anyw` is normal; `CrossL` holds, `Cross` does not.
  * The looser hand-off (`handFL`, the records `revRec` of the `CrossL` edges): `anyw` gets no
    backward demand, the reversed record has the premise `(ret,.,[any])`, and the requirement
    `(ret,.f,$,T)` cannot cross it. The backward run stops at the call (`inv_bl`), it does not
    reach the source (`bl_no_srcHit`, `bl_no_recorded_hit`), and the next forward run with the
    source seeds drops the source and reports nothing (`fl_lost`, for every demand and record set).
  * The hand-off with `Cross` keeps the leaf `((ret,.,[any]), D-p = (arg,.,*))`: the backward run
    enters `anyw`, reaches the source (`bs_srcHit`), and the next forward run (every `σ` with the
    hit, every record set) reports the vulnerability, in the normal layer (`fs_found`). -/

namespace AnyW

open Wrap (Z Xa A1 Jw Jwf bx br)

def XsA : PFact := ⟨1, [1, 2], .exact, .conc 1⟩
/-- `x.a.b = source()`. -/
def srcA : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, XsA)]⟩
/-- `r = anyw(x)`. -/
def callA : Call := ⟨1, [1, 2], [bx], [br]⟩
/-- `ret = anyTaint(arg)`: every location below `ret` gets the taint of `arg` (`[any-taint]`). -/
def anyS : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨4, [], .any, .star⟩)]⟩
def PA : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt srcA, 1), (0, 1, .call callA, 2), (1, 0, .stmt anyS, 1)]⟩
/-- `sink(r.f)` at node 2 of the root. -/
def sinkA : PFact := ⟨2, [4], .exact, .conc 1⟩
def sinksA : List (MethodId × Node × PFact) := [(0, 2, sinkA)]

theorem hEA00 : (0, 0, Instr.stmt srcA, 1) ∈ PA.edges := List.Mem.head _

#print axioms hEA00

theorem hEA01 : (0, 1, Instr.call callA, 2) ∈ PA.edges := List.Mem.tail _ (List.Mem.head _)

#print axioms hEA01

theorem hEA10 : (1, 0, Instr.stmt anyS, 1) ∈ PA.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hEA10

theorem pa_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ PA.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pa_no_clean

theorem pa_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ PA.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pa_no_filt

/-- The exit fact of `anyw` in run 1: `(ret,.,[any],*)`, NORMAL layer. -/
def GA : AFact := ⟨⟨4, [], .any, .star⟩, false⟩
/-- The root fact at the sink in run 1: `(r,.,[any],T)` (demand layer). -/
def RA1 : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩

/-! #### The vulnerability is real -/

theorem anyw_real : Reach PA [0] 0 2 ⟨2, [4], 1⟩ ∧ sinkA.covers ⟨2, [4], 1⟩ := by
  have d0 : den zeroFact XsA zeroLoc ⟨1, [1, 2], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
  have d1 : den bx.1 bx.2 ⟨1, [1, 2], 1⟩ ⟨3, [1, 2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1, 2], [1, 2], rfl, rfl, rfl, rfl, rfl⟩
  have d2 : den ⟨3, [], st, .star⟩ ⟨4, [], .any, .star⟩ ⟨3, [1, 2], 1⟩ ⟨4, [4], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1, 2], [4], rfl, rfl, rfl, trivial⟩
  have d3 : den br.1 br.2 ⟨4, [4], 1⟩ ⟨2, [4], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [4], [4], rfl, rfl, rfl, rfl, rfl⟩
  have f0 : Flow PA 0 zeroLoc 1 ⟨1, [1, 2], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) (s := srcA) hEA00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), d0⟩)
  have fc : Flow PA 1 ⟨3, [1, 2], 1⟩ 1 ⟨4, [4], 1⟩ :=
    Flow.step (Flow.start 1 ⟨3, [1, 2], 1⟩) (s := anyS) hEA10 (Or.inr ⟨_, List.Mem.head _, d2⟩)
  have f2 : Flow PA 0 zeroLoc 2 ⟨2, [4], 1⟩ :=
    Flow.call f0 (c := callA) hEA01 (List.Mem.head _) d1 fc (List.Mem.head _) d3
  exact ⟨Reach.root (List.Mem.head _) f2, ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩⟩

#print axioms anyw_real

/-! #### Forward run 1, completely -/

abbrev A1R := D PA cnt 1 policy1 sinksA [0]

def initsA1 : List (MethodId × PFact) := [(0, zeroFact), (1, Jw)]
def edgesA1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, Xa), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, RA1), (1, Jw, 0, Jwf), (1, Jw, 1, GA)]
def addedsA1 : List (MethodId × PFact) := [(1, A1)]

def InvA1 : Obj → Prop
  | .init M i => (M, i) ∈ initsA1
  | .edge M i n f => (M, i, n, f) ∈ edgesA1
  | .added M a => (M, a) ∈ addedsA1
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkA ∧ b = true

instance : DecidablePred InvA1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsA1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesA1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsA1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkA ∧ b = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 1 OF ANYW. -/
theorem inv_a1 {o : Obj} (h : A1R o) : InvA1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsA1,
      InvA1 (.edge x.1 x.2 (PA.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 1 srcA x.2.2.2).facts, InvA1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesA1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 1 anyS x.2.2.2).facts, InvA1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 1 srcA x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesA1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 1 anyS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callA.touched = false → InvA1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvA1 (.added callA.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addedsA1, InvA1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callA.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsA1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edgesA1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callA.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvA1 (.edge 0 x.2.1 2 (limitF cnt 1 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkA = .none ∨ check x.2.1 x.2.2.2 sinkA = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesA1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkA = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pa_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pa_no_clean hE).elim
  | filt _ hE _ _ => exact (pa_no_filt hE).elim

#print axioms inv_a1

theorem a1_e00 : A1R (.edge 0 zeroFact 0 Z) := D.start (D.root (List.Mem.head _))

#print axioms a1_e00

theorem a1_x01 : A1R (.edge 0 zeroFact 1 Xa) := D.step a1_e00 (s := srcA) hEA00 (by decide)

#print axioms a1_x01

theorem a1_init : A1R (.init 1 Jw) := by
  have ad : A1R (.added 1 A1) :=
    D.added (c := callA) (e := bx) (a := ⟨A1, true⟩) a1_x01 hEA01 (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinksA)
    (roots := [0]) (P := PA) ad
  have hp : policy1 1 A1 = Jw := by decide
  rw [hp] at h
  exact h

#print axioms a1_init

/-- The exit edge of `anyw` in run 1: `(arg,.,*) → (ret,.,[any])`, normal layer. -/
theorem a1_exit : A1R (.edge 1 Jw 1 GA) := D.step (D.start a1_init) (s := anyS) hEA10 (by decide)

#print axioms a1_exit

theorem a1_r : A1R (.edge 0 zeroFact 2 RA1) :=
  D.ret (c := callA) (e1 := bx) (a := ⟨A1, true⟩) (j := Jw) (g := GA)
    (r := ⟨⟨4, [], .any, .conc 1⟩, true⟩) (e2 := br) (r' := RA1)
    a1_x01 hEA01 (List.Mem.head _) (by decide) a1_init (by decide) a1_exit (by decide)
    (List.Mem.head _) (by decide)

#print axioms a1_r

/-- Run 1 reports the vulnerability in the demand layer: the backward run seeds its sink. -/
theorem a1_vuln : A1R (.vuln 0 2 sinkA true) := D.vuln a1_r (List.Mem.head _) (by decide)

#print axioms a1_vuln

/-- The exit edge of `anyw`: complete in the forward direction (`CrossL`), not crossable. -/
theorem a1_exit_crossL : CrossL Jw GA ∧ ¬ Cross Jw GA := ⟨by decide, not_cross_of_any rfl⟩

#print axioms a1_exit_crossL

/-! #### The reversed program -/

abbrev PbA : Program := Program.rev PA

theorem PbA_edges : PbA.edges =
    [(0, 1, .stmt (Stmt.rev srcA), 0), (0, 2, .call (Call.rev callA), 1),
     (1, 1, .stmt (Stmt.rev anyS), 0)] := rfl

#print axioms PbA_edges

theorem hbA_src : (0, 1, Instr.stmt (Stmt.rev srcA), 0) ∈ PbA.edges := by
  rw [PbA_edges]; exact List.Mem.head _

#print axioms hbA_src

theorem hbA_c : (0, 2, Instr.call (Call.rev callA), 1) ∈ PbA.edges := by
  rw [PbA_edges]; exact List.Mem.tail _ (List.Mem.head _)

#print axioms hbA_c

theorem hbA_any : (1, 1, Instr.stmt (Stmt.rev anyS), 0) ∈ PbA.edges := by
  rw [PbA_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hbA_any

/-- The seed: `(r,.f,$,T)` (no cut at 2). -/
def SA : AFact := ⟨sinkA, false⟩
/-- The requirement at the forward exit of `anyw`: `(ret,.f,$,T)`. -/
def JbA : PFact := ⟨4, [4], .exact, .conc 1⟩

/-! #### The looser hand-off: the backward run, completely -/

/-- The looser backward records: the reversals of the `CrossL` exit edges of run 1. -/
def recsBL : Recs := fun m y =>
  ∃ x : PFact × AFact, A1R (.init m x.1) ∧ A1R (.edge m x.1 (PA.exit m) x.2) ∧ CrossL x.1 x.2 ∧
    y = revRec x

def recListBL : List (MethodId × (PFact × AFact)) :=
  [(0, revRec (zeroFact, Z)), (1, revRec (Jw, GA))]

theorem recsBL_bound {m : MethodId} {y : PFact × AFact} (h : recsBL m y) : (m, y) ∈ recListBL := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ edgesA1, e.2.2.1 = PA.exit e.1 → CrossL e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ recListBL) (m, x.1, PA.exit m, x.2) (inv_a1 hx) rfl hc

#print axioms recsBL_bound

/-- The looser hand-off gives `anyw` no backward demand. -/
theorem handFL_a1_callee (d : DemandEdge) : ¬ handFL PA A1R pubD 1 d := by
  rintro ⟨j, g, g', _, hg, hn, _, _⟩
  exact hn ((by decide : ∀ x ∈ edgesA1, x.1 = 1 → x.2.2.1 = 1 → CrossL x.2.1 x.2.2.2)
    (1, j, 1, g) (inv_a1 hg) rfl rfl)

#print axioms handFL_a1_callee

/-- The backward run after the looser hand-off. -/
abbrev BL : Obj → Prop :=
  Backward.DB PbA cnt 2 (handFL PA A1R pubD) emitM satI restrictI recsBL [] [0] sinksA true

def initsBL : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact)]
def edgesBL : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Z), (0, zeroFact, 2, SA), (0, zeroFact, 1, Z), (0, zeroFact, 0, Z),
   (1, zeroFact, 1, Z), (1, zeroFact, 0, Z)]
def addedsBL : List (MethodId × PFact) := [(1, JbA)]

def InvBL : Obj → Prop
  | .init M i => (M, i) ∈ initsBL
  | .edge M i n f => (M, i, n, f) ∈ edgesBL
  | .added M a => (M, a) ∈ addedsBL
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBL := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBL))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBL))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBL))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN AFTER THE LOOSER HAND-OFF: the requirement `(ret,.f,$,T)` reaches
    the exit of `anyw` (an added fact), but nothing crosses the call. -/
theorem inv_bl {o : Obj} (h : BL o) : InvBL o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBL, InvBL (.edge x.1 x.2 (PbA.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [PbA_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 2 (Stmt.rev srcA) x.2.2.2).facts, InvBL (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBL, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 2 (Stmt.rev anyS) x.2.2.2).facts, InvBL (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [PbA_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 2 (Stmt.rev srcA) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBL, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 2 (Stmt.rev anyS) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callA).touched = false →
            InvBL (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev callA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBL (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd _ ih =>
    have hm : m = 1 := (by decide : ∀ y ∈ addedsBL, y.1 = 1) (m, a) ih
    subst hm
    exact (handFL_a1_callee d hd).elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE _ _ _ _ hd _ _ _ _ _ _ _ _ =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => exact (handFL_a1_callee d hd).elim
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListBL, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ (Call.rev callA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBL (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (recsBL_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [PbA_edges] at hE
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
    rw [PbA_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBL, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev callA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBL (.edge 0 zeroFact 1 (limitF cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_bl

/-- The requirement `(ret,.f,$,T)` is at the exit of `anyw`, but `anyw` has only the zero fact as
    an initial fact: the looser backward run does not enter it, and its record does not apply. -/
theorem bl_stuck : BL (.added 1 JbA) ∧ ∀ j, BL (.init 1 j) → j = zeroFact := by
  refine ⟨?_, fun j h => (by decide : ∀ x ∈ initsBL, x.1 = 1 → x.2 = zeroFact) (1, j) (inv_bl h) rfl⟩
  have e02 : BL (.edge 0 zeroFact 2 Z) := Backward.DB.start (Backward.DB.root (List.Mem.head _))
  have s02 : BL (.edge 0 zeroFact 2 SA) := Backward.DB.seed (s := sinkA) (List.Mem.head _) e02
  exact Backward.DB.added (c := Call.rev callA) (e := revEdge br.1 br.2) (a := ⟨JbA, false⟩) s02
    hbA_c (List.Mem.head _) (by decide)

#print axioms bl_stuck

/-- THE LOOSER BACKWARD RUN DOES NOT REACH THE SOURCE: no source hit (`FSeeds.srcHit`). -/
theorem bl_no_srcHit (M : MethodId) (n : Node) (e : MicroEdge) : ¬ FSeeds.srcHit PA BL M n e := by
  rintro ⟨s, n', i, f, lX, l1, l', hE, he, hz, hnz, hR, _, hd, hde⟩
  cases hE with
  | head =>
    have hfb : f.fact.base = zeroBase :=
      (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 1 → x.2.2.2.fact.base = zeroBase)
        (0, i, 1, f) (inv_bl hR) rfl rfl
    exact hnz (hde.2.1.symm.trans (hd.2.1.trans hfb))
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ e ∈ anyS.edges, e.1.base ≠ zeroBase) e he hz
      | tail _ hE => cases hE

#print axioms bl_no_srcHit

/-- Also the implementation's record of a hit (the reversed source edge applied to a requirement
    at the node after the source gives a result) is empty. -/
theorem bl_no_recorded_hit {i : PFact} {f : AFact} (h : BL (.edge 0 i 1 f)) :
    (applyEdge f (revEdge zeroFact XsA).1 (revEdge zeroFact XsA).2).facts = [] :=
  (by decide : ∀ x ∈ edgesBL, x.1 = 0 → x.2.2.1 = 1 →
    (applyEdge x.2.2.2 (revEdge zeroFact XsA).1 (revEdge zeroFact XsA).2).facts = [])
    (0, i, 1, f) (inv_bl h) rfl rfl

#print axioms bl_no_recorded_hit

/-! #### The next forward run with the source seeds of the looser chain -/

/-- The source seeds of the looser chain: the least set that contains the hits (none). -/
def σ0 : MethodId → Node → MicroEdge → Bool := fun _ _ _ => false

theorem σ0_hits (M : MethodId) (n : Node) (e : MicroEdge) (h : FSeeds.srcHit PA BL M n e) :
    σ0 M n e = true :=
  (bl_no_srcHit M n e h).elim

#print axioms σ0_hits

/-- The source without its source edge (only the zero keep edge). -/
def srcA0 : Stmt := ⟨[0], [(zeroFact, zeroFact)]⟩

theorem keepA0_edges : (FSeeds.keepSources PA σ0).edges =
    [(0, 0, .stmt srcA0, 1), (0, 1, .call callA, 2), (1, 0, .stmt anyS, 1)] := rfl

#print axioms keepA0_edges

def edgesFL : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 2, Z)]

def InvFL : Obj → Prop
  | .init M i => M = 0 ∧ i = zeroFact
  | .edge M i n f => (M, i, n, f) ∈ edgesFL
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvFL := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable (M = 0 ∧ i = zeroFact))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesFL))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE NEXT FORWARD RUN OF THE LOOSER CHAIN, for EVERY demand and record set: the source
    is not seeded, so only the zero fact flows, and nothing enters `anyw`. -/
theorem inv_fl (dem : MethodId → DemandEdge → Prop) (rc : Recs) {o : Obj}
    (h : DR (FSeeds.keepSources PA σ0) cnt 3 dem emitM satI restrictI rc sinksA [0] o) :
    InvFL o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => exact ⟨rfl, rfl⟩
    | tail _ h => cases h
  | @start M i _ ih =>
    obtain ⟨rfl, rfl⟩ := ih
    decide
  | @step M i n f n' s f' _ hE hf ih =>
    rw [keepA0_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 srcA0 x.2.2.2).facts, InvFL (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact ((by decide : ∀ x ∈ edgesFL, x.1 = 1 → False) (1, i, 0, f) ih rfl).elim
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [keepA0_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 srcA0 x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact (by decide : ∀ x ∈ edgesFL, x.1 = 1 → False) (1, i, 0, f) ih rfl
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callA.touched = false → InvFL (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False) (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | initR _ _ _ ih => exact ih.elim
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ _ _ _ _ _ ihf _ _ =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact ((by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False) (0, i, 1, f) ihf rfl rfl e1 he1 a ha).elim
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ _ _ ihf =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact ((by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, False) (0, i, 1, f) ihf rfl rfl e1 he1 a ha).elim
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sinkA = .none :=
        (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sinkA = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sinkA = .none :=
        (by decide : ∀ x ∈ edgesFL, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sinkA = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [keepA0_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_fl

/-- THE LOOSER HAND-OFF LOSES THE VULNERABILITY: the next forward run with the source seeds of the
    looser chain reports nothing, for every demand and every record set. -/
theorem fl_lost (dem : MethodId → DemandEdge → Prop) (rc : Recs) (b : Bool) :
    ¬ DR (FSeeds.keepSources PA σ0) cnt 3 dem emitM satI restrictI rc sinksA [0]
      (.vuln 0 2 sinkA b) :=
  fun h => inv_fl dem rc h

#print axioms fl_lost

/-! #### The hand-off with `Cross` keeps the leaf -/

/-- The backward records of the design: the reversals of the crossable exit edges of run 1. -/
def recsBS : Recs := fun m y =>
  ∃ x : PFact × AFact, A1R (.init m x.1) ∧ A1R (.edge m x.1 (PA.exit m) x.2) ∧ Cross x.1 x.2 ∧
    y = revRec x

/-- The leaf is handed off: `((ret,.,[any],*), D-p = (arg,.,*))`. -/
theorem handF_a1_callee : handF PA A1R pubD 1 ⟨GA.fact, some Jw⟩ :=
  ⟨Jw, GA, GA, a1_init, a1_exit, a1_exit_crossL.2, rfl, rfl⟩

#print axioms handF_a1_callee

abbrev BS : Obj → Prop :=
  Backward.DB PbA cnt 2 (handF PA A1R pubD) emitM satI restrictI recsBS [] [0] sinksA true

/-- The backward conclusion of `anyw` at its forward entry: `(arg,.,[any],T)`, normal layer. -/
def GbA : AFact := ⟨⟨3, [], .any, .conc 1⟩, false⟩
/-- The requirement at the source: `(x,.,[any],T)`. -/
def XbA : AFact := ⟨⟨1, [], .any, .conc 1⟩, false⟩

theorem bs_s02 : BS (.edge 0 zeroFact 2 SA) :=
  Backward.DB.seed (s := sinkA) (List.Mem.head _)
    (Backward.DB.start (Backward.DB.root (List.Mem.head _)))

#print axioms bs_s02

/-- The backward run enters `anyw` by the leaf: the premise `(ret,.f,$,T)`. -/
theorem bs_init : BS (.init 1 JbA) := by
  have ad : BS (.added 1 JbA) :=
    Backward.DB.added (c := Call.rev callA) (e := revEdge br.1 br.2) (a := ⟨JbA, false⟩) bs_s02
      hbA_c (List.Mem.head _) (by decide)
  exact Backward.DB.initR ad handF_a1_callee (by decide)

#print axioms bs_init

theorem bs_g : BS (.edge 1 JbA 0 GbA) :=
  Backward.DB.step (Backward.DB.start bs_init) hbA_any (by decide)

#print axioms bs_g

theorem bs_x01 : BS (.edge 0 zeroFact 1 XbA) :=
  Backward.DB.ret (c := Call.rev callA) (e1 := revEdge br.1 br.2) (a := ⟨JbA, false⟩) (j := JbA)
    (g := GbA) (d := ⟨GA.fact, some Jw⟩) (g' := GbA) (r := GbA) (e2 := revEdge bx.1 bx.2)
    (r' := XbA) bs_s02 hbA_c (List.Mem.head _) (by decide) bs_init bs_g handF_a1_callee
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms bs_x01

/-- THE BACKWARD RUN WITH `Cross` REACHES THE SOURCE. -/
theorem bs_srcHit : FSeeds.srcHit PA BS 0 0 (zeroFact, XsA) :=
  ⟨srcA, 1, zeroFact, XbA, zeroLoc, zeroLoc, ⟨1, [1, 2], 1⟩, hEA00,
    List.Mem.tail _ (List.Mem.head _), rfl, by decide, bs_x01, ⟨1, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, trivial, [], [1, 2], rfl, rfl, rfl, trivial⟩,
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩⟩

#print axioms bs_srcHit

/-- The demand of the next forward run (the design). -/
def demS : MethodId → DemandEdge → Prop := demOfN PbA BS (pubR (handF PA A1R pubD))

/-- The backward summary of `anyw` is handed off: its reversal has the premise `(arg,.,[any],T)`,
    not crossable. -/
theorem demS_callee : demS 1 ⟨GbA.fact, some JbA⟩ :=
  Or.inr (Or.inr ⟨JbA, GbA, GbA, bs_init, by decide, bs_g, by decide,
    ⟨⟨GA.fact, some Jw⟩, handF_a1_callee, by decide⟩, rfl⟩)

#print axioms demS_callee

/-- The source with the hit stays in the program of the next forward run. -/
theorem keepSrcA {σ : MethodId → Node → MicroEdge → Bool} (hσ : σ 0 0 (zeroFact, XsA) = true) :
    FSeeds.keepStmt σ 0 0 srcA = srcA := by
  have hf : srcA.edges.filter (fun e => !FSeeds.isSrc e || σ 0 0 e) = srcA.edges := by
    show List.filter _ [(zeroFact, zeroFact), (zeroFact, XsA)] = [(zeroFact, zeroFact), (zeroFact, XsA)]
    rw [List.filter_cons_of_pos rfl,
      List.filter_cons_of_pos (p := fun e => !FSeeds.isSrc e || σ 0 0 e)
        (a := (zeroFact, XsA)) hσ]
    rfl
  show (⟨srcA.touched, srcA.edges.filter (fun e => !FSeeds.isSrc e || σ 0 0 e)⟩ : Stmt) = srcA
  rw [hf]

#print axioms keepSrcA

theorem keepA_src {σ : MethodId → Node → MicroEdge → Bool} (hσ : σ 0 0 (zeroFact, XsA) = true) :
    (0, 0, Instr.stmt srcA, 1) ∈ (FSeeds.keepSources PA σ).edges := by
  have h := FSeeds.mem_keep_stmt (σ := σ) hEA00
  rw [keepSrcA hσ] at h
  exact h

#print axioms keepA_src

theorem keepA_any {σ : MethodId → Node → MicroEdge → Bool} :
    (1, 0, Instr.stmt anyS, 1) ∈ (FSeeds.keepSources PA σ).edges :=
  FSeeds.mem_keep_stmt (σ := σ) hEA10

#print axioms keepA_any

/-- THE HAND-OFF WITH `Cross` KEEPS THE VULNERABILITY: for every `σ` that fires the hit source,
    and every record set, the next forward run reports it, in the NORMAL layer. -/
theorem fs_found {σ : MethodId → Node → MicroEdge → Bool} (hσ : σ 0 0 (zeroFact, XsA) = true)
    (rc : Recs) :
    DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.vuln 0 2 sinkA false) := by
  have e00 : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 0 Z) := DR.start (DR.root (List.Mem.head _))
  have x01 : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 1 ⟨XsA, false⟩) := DR.step e00 (s := srcA) (keepA_src hσ) (by decide)
  have hc : (0, 1, Instr.call callA, 2) ∈ (FSeeds.keepSources PA σ).edges :=
    FSeeds.mem_keep_call hEA01
  have ad : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.added 1 ⟨3, [1, 2], .exact, .conc 1⟩) :=
    DR.added (c := callA) (e := bx) (a := ⟨⟨3, [1, 2], .exact, .conc 1⟩, false⟩) x01 hc
      (List.Mem.head _) (by decide)
  have i1 : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.init 1 ⟨3, [1, 2], .exact, .conc 1⟩) := DR.initR ad demS_callee (by decide)
  have g1 : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.edge 1 ⟨3, [1, 2], .exact, .conc 1⟩ 1 ⟨⟨4, [], .any, .conc 1⟩, false⟩) :=
    DR.step (DR.start i1) (s := anyS) keepA_any (by decide)
  have r2 : DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 2 (limitF cnt 3 ⟨⟨2, [4], .exact, .conc 1⟩, false⟩)) :=
    DR.ret (c := callA) (e1 := bx) (a := ⟨⟨3, [1, 2], .exact, .conc 1⟩, false⟩)
      (j := ⟨3, [1, 2], .exact, .conc 1⟩) (g := ⟨⟨4, [], .any, .conc 1⟩, false⟩)
      (d := ⟨GbA.fact, some JbA⟩) (g' := ⟨⟨4, [4], .exact, .conc 1⟩, false⟩)
      (r := ⟨⟨4, [4], .exact, .conc 1⟩, false⟩) (e2 := br) (r' := ⟨⟨2, [4], .exact, .conc 1⟩, false⟩)
      x01 hc (List.Mem.head _) (by decide) i1 g1 demS_callee (by decide) (by decide) (by decide)
      (List.Mem.head _) (by decide)
  exact DR.vuln r2 (s := sinkA) (List.Mem.head _) (by decide)

#print axioms fs_found

/-- THE CEGAR OF `Cross` (ii), in one statement. The vulnerability of ANYW is real and run 1
    reports it in the demand layer (so it is seeded). With `Cross` (the design), every `σ` that
    contains the hits of the backward run fires the source, and the next forward run reports the
    vulnerability. With the looser `CrossL`, the backward run hits no source, so the least `σ` with
    its hits (`σ0`) drops the source, and the next forward run reports nothing, for every demand
    and record set. -/
theorem cegar_cross_anyw :
    (Reach PA [0] 0 2 ⟨2, [4], 1⟩ ∧ sinkA.covers ⟨2, [4], 1⟩) ∧ A1R (.vuln 0 2 sinkA true) ∧
    (∀ σ : MethodId → Node → MicroEdge → Bool,
      (∀ M n e, FSeeds.srcHit PA BS M n e → σ M n e = true) →
      ∀ rc, DR (FSeeds.keepSources PA σ) cnt 3 demS emitM satI restrictI rc sinksA [0]
        (.vuln 0 2 sinkA false)) ∧
    (∀ M n e, FSeeds.srcHit PA BL M n e → σ0 M n e = true) ∧
    (∀ dem rc b, ¬ DR (FSeeds.keepSources PA σ0) cnt 3 dem emitM satI restrictI rc sinksA [0]
      (.vuln 0 2 sinkA b)) :=
  ⟨anyw_real, a1_vuln, fun _ hσ rc => fs_found (hσ 0 0 _ bs_srcHit) rc, σ0_hits, fl_lost⟩

#print axioms cegar_cross_anyw

end AnyW

/-! ### (ii') ANYM: the looser hand-off loses a vulnerability with NO source seeds

```
root():  x = mk();  r = anyw(x);  sink(r.f);   // method 0, sink at node 2
anyw(x): ret = anyTaint(x);  return ret;        // method 1, as in ANYW
mk():    ret.a.b = source();  return ret;       // method 2
```
The call of `mk` binds the zero fact into `mk` and `ret` back into `x`. Run 1 (L=1) cuts the
source in `mk` to `(ret,.a,[any],T)`: the summary of `mk` is in the demand layer, so the next
forward run applies it only through a demand edge of `mk` with a `D-p`. The looser hand-off drops
the leaf of `anyw`, the backward run stops at the call of `anyw` (`inv_blm`), so it never reaches
the call of `mk`, and `mk` gets only the zero demand (`demLM_exact`). The next forward run on the
FULL program (no source seeds) cannot apply the summary of `mk` and reports nothing (`flm_lost`,
`inv_flm`). With `Cross` the backward run enters `anyw` and then `mk`, and the next forward run
reports the vulnerability (`fsm_found`). So the condition on the reversed premise is necessary also
without the forward seeds. -/

namespace AnyM

open Wrap (Z Zd Xa A1 Jw Jwf bx br zb)
open AnyW (XsA callA anyS sinkA sinksA GA RA1 SA JbA GbA XbA)

/-- The binding back of `x = mk()`: `ret → x`. -/
def bm : MicroEdge := (⟨4, [], st, .star⟩, ⟨1, [], st, .star⟩)
def callM : Call := ⟨2, [1], [zb], [bm]⟩
/-- `ret.a.b = source()` in `mk`. -/
def mkS : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨4, [1, 2], .exact, .conc 1⟩)]⟩
def PM : Program := ⟨fun _ => 0, fun m => if m = 0 then 2 else 1,
  [(0, 0, .call callM, 1), (0, 1, .call callA, 2), (1, 0, .stmt anyS, 1), (2, 0, .stmt mkS, 1)]⟩

theorem hEM00 : (0, 0, Instr.call callM, 1) ∈ PM.edges := List.Mem.head _

#print axioms hEM00

theorem hEM01 : (0, 1, Instr.call callA, 2) ∈ PM.edges := List.Mem.tail _ (List.Mem.head _)

#print axioms hEM01

theorem hEM10 : (1, 0, Instr.stmt anyS, 1) ∈ PM.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hEM10

theorem hEM20 : (2, 0, Instr.stmt mkS, 1) ∈ PM.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

#print axioms hEM20

theorem pm_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ PM.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

#print axioms pm_no_clean

theorem pm_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ PM.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

#print axioms pm_no_filt

/-- The exit fact of `mk` in run 1: `(ret,.a,[any],T)` (demand layer), and in run 3:
    `(ret,.a.b,$,T)`. -/
def Mk1 : AFact := ⟨⟨4, [1], .any, .conc 1⟩, true⟩
def Mk3 : AFact := ⟨⟨4, [1, 2], .exact, .conc 1⟩, false⟩

/-! #### The vulnerability is real -/

theorem anym_real : Reach PM [0] 0 2 ⟨2, [4], 1⟩ ∧ sinkA.covers ⟨2, [4], 1⟩ := by
  have dz : den zb.1 zb.2 zeroLoc zeroLoc :=
    ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
  have ds : den zeroFact ⟨4, [1, 2], .exact, .conc 1⟩ zeroLoc ⟨4, [1, 2], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
  have dm : den bm.1 bm.2 ⟨4, [1, 2], 1⟩ ⟨1, [1, 2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1, 2], [1, 2], rfl, rfl, rfl, rfl, rfl⟩
  have d1 : den bx.1 bx.2 ⟨1, [1, 2], 1⟩ ⟨3, [1, 2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1, 2], [1, 2], rfl, rfl, rfl, rfl, rfl⟩
  have d2 : den ⟨3, [], st, .star⟩ ⟨4, [], .any, .star⟩ ⟨3, [1, 2], 1⟩ ⟨4, [4], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1, 2], [4], rfl, rfl, rfl, trivial⟩
  have d3 : den br.1 br.2 ⟨4, [4], 1⟩ ⟨2, [4], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [4], [4], rfl, rfl, rfl, rfl, rfl⟩
  have fm : Flow PM 2 zeroLoc 1 ⟨4, [1, 2], 1⟩ :=
    Flow.step (Flow.start 2 zeroLoc) (s := mkS) hEM20
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), ds⟩)
  have f1 : Flow PM 0 zeroLoc 1 ⟨1, [1, 2], 1⟩ :=
    Flow.call (Flow.start 0 zeroLoc) (c := callM) hEM00 (List.Mem.head _) dz fm
      (List.Mem.head _) dm
  have fc : Flow PM 1 ⟨3, [1, 2], 1⟩ 1 ⟨4, [4], 1⟩ :=
    Flow.step (Flow.start 1 ⟨3, [1, 2], 1⟩) (s := anyS) hEM10 (Or.inr ⟨_, List.Mem.head _, d2⟩)
  have f2 : Flow PM 0 zeroLoc 2 ⟨2, [4], 1⟩ :=
    Flow.call f1 (c := callA) hEM01 (List.Mem.head _) d1 fc (List.Mem.head _) d3
  exact ⟨Reach.root (List.Mem.head _) f2, ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩⟩

#print axioms anym_real

/-! #### Forward run 1, completely -/

abbrev M1R := D PM cnt 1 policy1 sinksA [0]

def initsM1 : List (MethodId × PFact) := [(0, zeroFact), (1, Jw), (2, zeroFact)]
def edgesM1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, Xa), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, RA1), (1, Jw, 0, Jwf), (1, Jw, 1, GA), (2, zeroFact, 0, Z), (2, zeroFact, 1, Z),
   (2, zeroFact, 1, Mk1)]
def addedsM1 : List (MethodId × PFact) := [(1, A1), (2, zeroFact)]

def InvM1 : Obj → Prop
  | .init M i => (M, i) ∈ initsM1
  | .edge M i n f => (M, i, n, f) ∈ edgesM1
  | .added M a => (M, a) ∈ addedsM1
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkA ∧ b = true

instance : DecidablePred InvM1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsM1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesM1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsM1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkA ∧ b = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 1 OF ANYM. -/
theorem inv_m1 {o : Obj} (h : M1R o) : InvM1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsM1,
      InvM1 (.edge x.1 x.2 (PM.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesM1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 1 anyS x.2.2.2).facts, InvM1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesM1, x.1 = 2 → x.2.2.1 = 0 →
              ∀ f' ∈ (transfer cnt 1 mkS x.2.2.2).facts, InvM1 (.edge 2 x.2.1 1 f'))
              (2, i, 0, f) ih rfl rfl f' hf
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesM1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 1 anyS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesM1, x.1 = 2 → x.2.2.1 = 0 →
              ∀ t ∈ (transfer cnt 1 mkS x.2.2.2).reqs, False) (2, i, 0, f) ih rfl rfl t ht
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 0 →
        memB x.2.2.2.fact.base callM.touched = false → InvM1 (.edge 0 x.2.1 1 x.2.2.2))
        (0, i, 0, f) ih rfl rfl hm
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callA.touched = false → InvM1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 0 → ∀ e ∈ callM.toCallee,
        ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvM1 (.added callM.callee a.fact))
        (0, i, 0, f) ih rfl rfl e he a ha
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvM1 (.added callA.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addedsM1, InvM1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ e1 ∈ callM.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
        ∀ y ∈ initsM1, y.1 = 2 → applicable y.2 a.fact = true →
        ∀ z ∈ edgesM1, z.1 = 2 → z.2.1 = y.2 → z.2.2.1 = 1 →
        ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
        ∀ e2 ∈ callM.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
          InvM1 (.edge 0 x.2.1 1 (limitF cnt 1 r')))
        (0, i, 0, f) ihf rfl rfl e1 he1 a ha (2, j) ihj rfl hap (2, j, 1, g) ihg rfl rfl rfl
        r hr e2 he2 r' hr'
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callA.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsM1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edgesM1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callA.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvM1 (.edge 0 x.2.1 2 (limitF cnt 1 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkA = .none ∨ check x.2.1 x.2.2.2 sinkA = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesM1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkA = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pm_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pm_no_clean hE).elim
  | filt _ hE _ _ => exact (pm_no_filt hE).elim

#print axioms inv_m1

theorem m1_e00 : M1R (.edge 0 zeroFact 0 Z) := D.start (D.root (List.Mem.head _))

#print axioms m1_e00

theorem m1_init_mk : M1R (.init 2 zeroFact) := by
  have ad : M1R (.added 2 zeroFact) :=
    D.added (c := callM) (e := zb) (a := Z) m1_e00 hEM00 (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinksA)
    (roots := [0]) (P := PM) ad
  have hp : policy1 2 zeroFact = zeroFact := by decide
  rw [hp] at h
  exact h

#print axioms m1_init_mk

/-- The exit edge of `mk` in run 1: `zero → (ret,.a,[any],T)`, demand layer (the cut in `mk`). -/
theorem m1_exit_mk : M1R (.edge 2 zeroFact 1 Mk1) :=
  D.step (D.start m1_init_mk) (s := mkS) hEM20 (by decide)

#print axioms m1_exit_mk

theorem m1_x01 : M1R (.edge 0 zeroFact 1 Xa) :=
  D.ret (c := callM) (e1 := zb) (a := Z) (j := zeroFact) (g := Mk1)
    (r := ⟨⟨4, [1], .any, .conc 1⟩, true⟩) (e2 := bm) (r' := Xa)
    m1_e00 hEM00 (List.Mem.head _) (by decide) m1_init_mk (by decide) m1_exit_mk (by decide)
    (List.Mem.head _) (by decide)

#print axioms m1_x01

theorem m1_init_w : M1R (.init 1 Jw) := by
  have ad : M1R (.added 1 A1) :=
    D.added (c := callA) (e := bx) (a := ⟨A1, true⟩) m1_x01 hEM01 (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinksA)
    (roots := [0]) (P := PM) ad
  have hp : policy1 1 A1 = Jw := by decide
  rw [hp] at h
  exact h

#print axioms m1_init_w

theorem m1_exit_w : M1R (.edge 1 Jw 1 GA) := D.step (D.start m1_init_w) (s := anyS) hEM10 (by decide)

#print axioms m1_exit_w

theorem m1_r : M1R (.edge 0 zeroFact 2 RA1) :=
  D.ret (c := callA) (e1 := bx) (a := ⟨A1, true⟩) (j := Jw) (g := GA)
    (r := ⟨⟨4, [], .any, .conc 1⟩, true⟩) (e2 := br) (r' := RA1)
    m1_x01 hEM01 (List.Mem.head _) (by decide) m1_init_w (by decide) m1_exit_w (by decide)
    (List.Mem.head _) (by decide)

#print axioms m1_r

/-- Run 1 reports the vulnerability in the demand layer: the backward run seeds its sink. -/
theorem m1_vuln : M1R (.vuln 0 2 sinkA true) := D.vuln m1_r (List.Mem.head _) (by decide)

#print axioms m1_vuln

/-! #### The reversed program -/

abbrev PbM : Program := Program.rev PM

theorem PbM_edges : PbM.edges =
    [(0, 1, .call (Call.rev callM), 0), (0, 2, .call (Call.rev callA), 1),
     (1, 1, .stmt (Stmt.rev anyS), 0), (2, 1, .stmt (Stmt.rev mkS), 0)] := rfl

#print axioms PbM_edges

theorem hbM_m : (0, 1, Instr.call (Call.rev callM), 0) ∈ PbM.edges := by
  rw [PbM_edges]; exact List.Mem.head _

#print axioms hbM_m

theorem hbM_a : (0, 2, Instr.call (Call.rev callA), 1) ∈ PbM.edges := by
  rw [PbM_edges]; exact List.Mem.tail _ (List.Mem.head _)

#print axioms hbM_a

theorem hbM_any : (1, 1, Instr.stmt (Stmt.rev anyS), 0) ∈ PbM.edges := by
  rw [PbM_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hbM_any

theorem hbM_mk : (2, 1, Instr.stmt (Stmt.rev mkS), 0) ∈ PbM.edges := by
  rw [PbM_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

#print axioms hbM_mk

/-! #### The looser hand-off: the backward run, completely -/

def handLM : List (MethodId × DemandEdge) :=
  [(0, ⟨RA1.fact, some zeroFact⟩), (2, ⟨Mk1.fact, some zeroFact⟩)]

/-- The looser forward hand-off of run 1, bounded: the root edge and the demand-layer summary of
    `mk`; nothing for `anyw` (its leaf is dropped). -/
theorem handFL_m1_bound {m : MethodId} {d : DemandEdge} (h : handFL PM M1R pubD m d) :
    (m, d) ∈ handLM := by
  obtain ⟨j, g, g', _, hg, hnc, hpub, rfl⟩ := h
  cases hpub
  exact (by decide : ∀ x ∈ edgesM1, x.2.2.1 = PM.exit x.1 → ¬ CrossL x.2.1 x.2.2.2 →
    (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ handLM)
    (m, j, PM.exit m, g) (inv_m1 hg) rfl hnc

#print axioms handFL_m1_bound

def recsBLM : Recs := fun m y =>
  ∃ x : PFact × AFact, M1R (.init m x.1) ∧ M1R (.edge m x.1 (PM.exit m) x.2) ∧ CrossL x.1 x.2 ∧
    y = revRec x

def recListBLM : List (MethodId × (PFact × AFact)) :=
  [(0, revRec (zeroFact, Z)), (1, revRec (Jw, GA)), (2, revRec (zeroFact, Z))]

theorem recsBLM_bound {m : MethodId} {y : PFact × AFact} (h : recsBLM m y) :
    (m, y) ∈ recListBLM := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ edgesM1, e.2.2.1 = PM.exit e.1 → CrossL e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ recListBLM) (m, x.1, PM.exit m, x.2) (inv_m1 hx) rfl hc

#print axioms recsBLM_bound

abbrev BLM : Obj → Prop :=
  Backward.DB PbM cnt 2 (handFL PM M1R pubD) emitM satI restrictI recsBLM [] [0] sinksA true

def initsBLM : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (2, zeroFact)]
def edgesBLM : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Z), (0, zeroFact, 2, SA), (0, zeroFact, 1, Z), (0, zeroFact, 0, Z),
   (1, zeroFact, 1, Z), (1, zeroFact, 0, Z), (2, zeroFact, 1, Z), (2, zeroFact, 0, Z)]
def addedsBLM : List (MethodId × PFact) := [(1, JbA)]

def InvBLM : Obj → Prop
  | .init M i => (M, i) ∈ initsBLM
  | .edge M i n f => (M, i, n, f) ∈ edgesBLM
  | .added M a => (M, a) ∈ addedsBLM
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBLM := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBLM))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBLM))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBLM))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN OF ANYM AFTER THE LOOSER HAND-OFF: the requirement stops at the call
    of `anyw`; the requirement never reaches the call of `mk`. -/
theorem inv_blm {o : Obj} (h : BLM o) : InvBLM o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBLM, InvBLM (.edge x.1 x.2 (PbM.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [PbM_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBLM, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 2 (Stmt.rev anyS) x.2.2.2).facts, InvBLM (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesBLM, x.1 = 2 → x.2.2.1 = 1 →
              ∀ f' ∈ (transfer cnt 2 (Stmt.rev mkS) x.2.2.2).facts, InvBLM (.edge 2 x.2.1 0 f'))
              (2, i, 1, f) ih rfl rfl f' hf
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [PbM_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBLM, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 2 (Stmt.rev anyS) x.2.2.2).reqs, False) (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesBLM, x.1 = 2 → x.2.2.1 = 1 →
              ∀ t ∈ (transfer cnt 2 (Stmt.rev mkS) x.2.2.2).reqs, False) (2, i, 1, f) ih rfl rfl t ht
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [PbM_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 1 →
        memB x.2.2.2.fact.base (Call.rev callM).touched = false → InvBLM (.edge 0 x.2.1 0 x.2.2.2))
        (0, i, 1, f) ih rfl rfl hm
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callA).touched = false →
            InvBLM (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [PbM_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 1 →
        ∀ e ∈ (Call.rev callM).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
          InvBLM (.added 2 a.fact))
        (0, i, 1, f) ih rfl rfl e he a ha
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev callA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBLM (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ handLM, ∀ y ∈ addedsBLM, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvBLM (.init x.1 j))
      (m, d) (handFL_m1_bound hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [PbM_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 1 →
        ∀ e1 ∈ (Call.rev callM).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
        ∀ y ∈ initsBLM, y.1 = 2 →
        ∀ z ∈ edgesBLM, z.1 = 2 → z.2.1 = y.2 → z.2.2.1 = 0 →
        ∀ dd ∈ handLM, dd.1 = 2 → ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList,
        satI y.2 a.fact = true →
        ∀ r ∈ (applySummary a y.2 g').facts,
        ∀ e2 ∈ (Call.rev callM).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
          InvBLM (.edge 0 x.2.1 0 (limitF cnt 2 r')))
        (0, i, 1, f) ihf rfl rfl e1 he1 a ha (2, j) ihj rfl (2, j, 0, g) ihg rfl rfl rfl
        (2, d) (handFL_m1_bound hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
        r hr e2 he2 r' hr'
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsBLM, y.1 = 1 →
          ∀ z ∈ edgesBLM, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ handLM, dd.1 = 1 → ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Call.rev callA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBLM (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (handFL_m1_bound hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    rw [PbM_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 1 →
        ∀ e1 ∈ (Call.rev callM).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
        ∀ y ∈ recListBLM, y.1 = 2 →
        (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
        ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
        ∀ e2 ∈ (Call.rev callM).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
          InvBLM (.edge 0 x.2.1 0 (limitF cnt 2 r')))
        (0, i, 1, f) ihf rfl rfl e1 he1 a ha (2, (j, g)) (recsBLM_bound hrec) rfl hsat
        r hr e2 he2 r' hr'
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBLM, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callA).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListBLM, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ (Call.rev callA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBLM (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (recsBLM_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [PbM_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [PbM_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [PbM_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [PbM_edges] at hE
    cases hE with
    | head => decide
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [PbM_edges] at hE
    cases hE with
    | head => decide
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [PbM_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ y ∈ edgesBLM, y.1 = 2 → y.2.1 = zeroFact → y.2.2.1 = 0 →
        ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
        ∀ e2 ∈ (Call.rev callM).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
          InvBLM (.edge 0 zeroFact 0 (limitF cnt 2 r')))
        (2, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBLM, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev callA).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBLM (.edge 0 zeroFact 1 (limitF cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE

#print axioms inv_blm

/-- The demand of the next forward run after the looser hand-off. -/
def demLM : MethodId → DemandEdge → Prop := demOfN PbM BLM (pubR (handFL PM M1R pubD))

/-- THE LOOSER HAND-OFF GIVES ONLY THE ZERO DEMAND, in every method (also in `mk`). -/
theorem demLM_exact (m : MethodId) (d : DemandEdge) : demLM m d ↔ d = Backward.zeroDem := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, _, _, _, _⟩)
    · exact h
    · exact (by decide : ∀ x ∈ edgesBLM, x.2.1 = zeroFact → x.2.2.1 = PbM.exit x.1 →
        (⟨x.2.2.2.fact, none⟩ : DemandEdge) = Backward.zeroDem)
        (m, zeroFact, PbM.exit m, g) (inv_blm hg) rfl rfl
    · exact absurd ((by decide : ∀ x ∈ initsBLM, x.2 = zeroFact) (m, jb) (inv_blm hjb)) hne
  · rintro rfl
    exact Or.inl rfl

#print axioms demLM_exact

/-- The looser forward records: the `CrossL` exit edges of run 1 and the `CrossL` reversed
    backward summaries (none here). -/
def rcLM : Recs := fun m x =>
  (M1R (.init m x.1) ∧ M1R (.edge m x.1 (PM.exit m) x.2) ∧ CrossL x.1 x.2) ∨
  (∃ jb gb, BLM (.init m jb) ∧ jb ≠ zeroFact ∧ BLM (.edge m jb (PbM.exit m) gb) ∧
    gb.demand = false ∧ CrossL (revRec (jb, gb)).1 (revRec (jb, gb)).2 ∧ x = revRec (jb, gb))

def recListFLM : List (MethodId × (PFact × AFact)) :=
  [(0, (zeroFact, Z)), (1, (Jw, GA)), (2, (zeroFact, Z))]

theorem rcLM_bound {m : MethodId} {x : PFact × AFact} (h : rcLM m x) : (m, x) ∈ recListFLM := by
  rcases h with ⟨_, hx, hc⟩ | ⟨jb, _, hjb, hne, _⟩
  · exact (by decide : ∀ e ∈ edgesM1, e.2.2.1 = PM.exit e.1 → CrossL e.2.1 e.2.2.2 →
      (e.1, (e.2.1, e.2.2.2)) ∈ recListFLM) (m, x.1, PM.exit m, x.2) (inv_m1 hx) rfl hc
  · exact absurd ((by decide : ∀ x ∈ initsBLM, x.2 = zeroFact) (m, jb) (inv_blm hjb)) hne

#print axioms rcLM_bound

/-- The next forward run of the looser chain, on the FULL program (no source seeds). -/
abbrev FLM : Obj → Prop := DR PM cnt 3 demLM emitM satI restrictI rcLM sinksA [0]

def initsFLM : List (MethodId × PFact) := [(0, zeroFact), (2, zeroFact)]
def edgesFLM : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 2, Z), (2, zeroFact, 0, Z),
   (2, zeroFact, 1, Z), (2, zeroFact, 1, Mk3)]
def addedsFLM : List (MethodId × PFact) := [(2, zeroFact)]

def InvFLM : Obj → Prop
  | .init M i => (M, i) ∈ initsFLM
  | .edge M i n f => (M, i, n, f) ∈ edgesFLM
  | .added M a => (M, a) ∈ addedsFLM
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvFLM := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsFLM))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesFLM))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsFLM))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE NEXT FORWARD RUN OF THE LOOSER CHAIN: `mk` computes `(ret,.a.b,$,T)`, but no
    demand edge of `mk` has a `D-p` and no record of `mk` carries it, so it never reaches `x`. -/
theorem inv_flm {o : Obj} (h : FLM o) : InvFLM o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsFLM,
      InvFLM (.edge x.1 x.2 (PM.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFLM, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 anyS x.2.2.2).facts, InvFLM (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesFLM, x.1 = 2 → x.2.2.1 = 0 →
              ∀ f' ∈ (transfer cnt 3 mkS x.2.2.2).facts, InvFLM (.edge 2 x.2.1 1 f'))
              (2, i, 0, f) ih rfl rfl f' hf
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFLM, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 anyS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edgesFLM, x.1 = 2 → x.2.2.1 = 0 →
              ∀ t ∈ (transfer cnt 3 mkS x.2.2.2).reqs, False) (2, i, 0, f) ih rfl rfl t ht
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 0 →
        memB x.2.2.2.fact.base callM.touched = false → InvFLM (.edge 0 x.2.1 1 x.2.2.2))
        (0, i, 0, f) ih rfl rfl hm
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callA.touched = false → InvFLM (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 0 → ∀ e ∈ callM.toCallee,
        ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvFLM (.added callM.callee a.fact))
        (0, i, 0, f) ih rfl rfl e he a ha
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callA.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvFLM (.added callA.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    rw [(demLM_exact m d).mp hd] at he
    exact (by decide : ∀ y ∈ addedsFLM, ∀ j ∈ (emitM Backward.zeroDem.din y.2).toList,
      InvFLM (.init y.1 j)) (m, a) ih j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hres _ _ _ _ _ _ _ =>
    rw [(demLM_exact _ d).mp hd] at hres
    cases hres
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 0 →
        ∀ e1 ∈ callM.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
        ∀ y ∈ recListFLM, y.1 = 2 →
        (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
        ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
        ∀ e2 ∈ callM.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
          InvFLM (.edge 0 x.2.1 1 (limitF cnt 3 r')))
        (0, i, 0, f) ihf rfl rfl e1 he1 a ha (2, (j, g)) (rcLM_bound hrec) rfl hsat
        r hr e2 he2 r' hr'
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callA.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListFLM, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ callA.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvFLM (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (rcLM_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sinkA = .none :=
        (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sinkA = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sinkA = .none :=
        (by decide : ∀ x ∈ edgesFLM, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sinkA = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pm_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pm_no_clean hE).elim
  | filt _ hE _ _ => exact (pm_no_filt hE).elim

#print axioms inv_flm

/-- THE LOOSER HAND-OFF LOSES THE VULNERABILITY, with no source seeds: the next forward run on the
    full program reports nothing. -/
theorem flm_lost (b : Bool) : ¬ FLM (.vuln 0 2 sinkA b) := fun h => inv_flm h

#print axioms flm_lost

/-! #### The hand-off with `Cross` keeps it -/

def recsBSM : Recs := fun m y =>
  ∃ x : PFact × AFact, M1R (.init m x.1) ∧ M1R (.edge m x.1 (PM.exit m) x.2) ∧ Cross x.1 x.2 ∧
    y = revRec x

abbrev BSM : Obj → Prop :=
  Backward.DB PbM cnt 2 (handF PM M1R pubD) emitM satI restrictI recsBSM [] [0] sinksA true

theorem handF_m_anyw : handF PM M1R pubD 1 ⟨GA.fact, some Jw⟩ :=
  ⟨Jw, GA, GA, m1_init_w, m1_exit_w, not_cross_of_any rfl, rfl, rfl⟩

#print axioms handF_m_anyw

theorem handF_m_mk : handF PM M1R pubD 2 ⟨Mk1.fact, some zeroFact⟩ :=
  ⟨zeroFact, Mk1, Mk1, m1_init_mk, m1_exit_mk, by decide, rfl, rfl⟩

#print axioms handF_m_mk

theorem bsm_s02 : BSM (.edge 0 zeroFact 2 SA) :=
  Backward.DB.seed (s := sinkA) (List.Mem.head _)
    (Backward.DB.start (Backward.DB.root (List.Mem.head _)))

#print axioms bsm_s02

theorem bsm_init_w : BSM (.init 1 JbA) := by
  have ad : BSM (.added 1 JbA) :=
    Backward.DB.added (c := Call.rev callA) (e := revEdge br.1 br.2) (a := ⟨JbA, false⟩) bsm_s02
      hbM_a (List.Mem.head _) (by decide)
  exact Backward.DB.initR ad handF_m_anyw (by decide)

#print axioms bsm_init_w

theorem bsm_g_w : BSM (.edge 1 JbA 0 GbA) :=
  Backward.DB.step (Backward.DB.start bsm_init_w) hbM_any (by decide)

#print axioms bsm_g_w

theorem bsm_x01 : BSM (.edge 0 zeroFact 1 XbA) :=
  Backward.DB.ret (c := Call.rev callA) (e1 := revEdge br.1 br.2) (a := ⟨JbA, false⟩) (j := JbA)
    (g := GbA) (d := ⟨GA.fact, some Jw⟩) (g' := GbA) (r := GbA) (e2 := revEdge bx.1 bx.2)
    (r' := XbA) bsm_s02 hbM_a (List.Mem.head _) (by decide) bsm_init_w bsm_g_w handF_m_anyw
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms bsm_x01

/-- With `Cross`, the backward run crosses `anyw` and enters `mk` with the premise
    `(ret,.a,[any],T)`. -/
theorem bsm_init_mk : BSM (.init 2 Mk1.fact) := by
  have ad : BSM (.added 2 ⟨4, [], .any, .conc 1⟩) :=
    Backward.DB.added (c := Call.rev callM) (e := revEdge bm.1 bm.2)
      (a := ⟨⟨4, [], .any, .conc 1⟩, false⟩) bsm_x01 hbM_m (List.Mem.head _) (by decide)
  exact Backward.DB.initR ad handF_m_mk (by decide)

#print axioms bsm_init_mk

theorem bsm_g_mk : BSM (.edge 2 Mk1.fact 0 Zd) :=
  Backward.DB.step (Backward.DB.start bsm_init_mk) hbM_mk (by decide)

#print axioms bsm_g_mk

def demSM : MethodId → DemandEdge → Prop := demOfN PbM BSM (pubR (handF PM M1R pubD))

/-- With `Cross`, `mk` gets the demand edge `(zero, D-p = (ret,.a,[any],T))`. -/
theorem demSM_mk : demSM 2 ⟨zeroFact, some Mk1.fact⟩ :=
  Or.inr (Or.inr ⟨Mk1.fact, Zd, Zd, bsm_init_mk, by decide, bsm_g_mk, by decide,
    ⟨⟨Mk1.fact, some zeroFact⟩, handF_m_mk, by decide⟩, rfl⟩)

#print axioms demSM_mk

theorem demSM_w : demSM 1 ⟨GbA.fact, some JbA⟩ :=
  Or.inr (Or.inr ⟨JbA, GbA, GbA, bsm_init_w, by decide, bsm_g_w, by decide,
    ⟨⟨GA.fact, some Jw⟩, handF_m_anyw, by decide⟩, rfl⟩)

#print axioms demSM_w

/-- THE HAND-OFF WITH `Cross` KEEPS THE VULNERABILITY: the next forward run on the full program
    reports it, in the normal layer, for every record set. -/
theorem fsm_found (rc : Recs) :
    DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.vuln 0 2 sinkA false) := by
  have e00 : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.edge 0 zeroFact 0 Z) :=
    DR.start (DR.root (List.Mem.head _))
  have adm : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.added 2 zeroFact) :=
    DR.added (c := callM) (e := zb) (a := Z) e00 hEM00 (List.Mem.head _) (by decide)
  have im : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.init 2 zeroFact) :=
    DR.initR adm (Or.inl rfl) (by decide)
  have gm : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.edge 2 zeroFact 1 Mk3) :=
    DR.step (DR.start im) (s := mkS) hEM20 (by decide)
  have x01 : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 1 (limitF cnt 3 ⟨XsA, false⟩)) :=
    DR.ret (c := callM) (e1 := zb) (a := Z) (j := zeroFact) (g := Mk3)
      (d := ⟨zeroFact, some Mk1.fact⟩) (g' := Mk3) (r := Mk3) (e2 := bm) (r' := ⟨XsA, false⟩)
      e00 hEM00 (List.Mem.head _) (by decide) im gm demSM_mk (by decide) (by decide) (by decide)
      (List.Mem.head _) (by decide)
  have x01' : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 1 ⟨XsA, false⟩) := x01
  have ad : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.added 1 ⟨3, [1, 2], .exact, .conc 1⟩) :=
    DR.added (c := callA) (e := bx) (a := ⟨⟨3, [1, 2], .exact, .conc 1⟩, false⟩) x01' hEM01
      (List.Mem.head _) (by decide)
  have i1 : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.init 1 ⟨3, [1, 2], .exact, .conc 1⟩) := DR.initR ad demSM_w (by decide)
  have g1 : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.edge 1 ⟨3, [1, 2], .exact, .conc 1⟩ 1 ⟨⟨4, [], .any, .conc 1⟩, false⟩) :=
    DR.step (DR.start i1) (s := anyS) hEM10 (by decide)
  have r2 : DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0]
      (.edge 0 zeroFact 2 (limitF cnt 3 ⟨⟨2, [4], .exact, .conc 1⟩, false⟩)) :=
    DR.ret (c := callA) (e1 := bx) (a := ⟨⟨3, [1, 2], .exact, .conc 1⟩, false⟩)
      (j := ⟨3, [1, 2], .exact, .conc 1⟩) (g := ⟨⟨4, [], .any, .conc 1⟩, false⟩)
      (d := ⟨GbA.fact, some JbA⟩) (g' := ⟨⟨4, [4], .exact, .conc 1⟩, false⟩)
      (r := ⟨⟨4, [4], .exact, .conc 1⟩, false⟩) (e2 := br) (r' := ⟨⟨2, [4], .exact, .conc 1⟩, false⟩)
      x01' hEM01 (List.Mem.head _) (by decide) i1 g1 demSM_w (by decide) (by decide) (by decide)
      (List.Mem.head _) (by decide)
  exact DR.vuln r2 (s := sinkA) (List.Mem.head _) (by decide)

#print axioms fsm_found

/-- THE CEGAR OF `Cross` (ii'), in one statement: the vulnerability of ANYM is real and seeded;
    the next forward run of the design (`Cross`) reports it; the next forward run of the looser
    chain (`CrossL`), on the full program, reports nothing. -/
theorem cegar_cross_anym :
    (Reach PM [0] 0 2 ⟨2, [4], 1⟩ ∧ sinkA.covers ⟨2, [4], 1⟩) ∧ M1R (.vuln 0 2 sinkA true) ∧
    (∀ rc, DR PM cnt 3 demSM emitM satI restrictI rc sinksA [0] (.vuln 0 2 sinkA false)) ∧
    (∀ b, ¬ FLM (.vuln 0 2 sinkA b)) :=
  ⟨anym_real, m1_vuln, fsm_found, flm_lost⟩

#print axioms cegar_cross_anym

end AnyM

/-! ## Part 5. The getter: a demand-layer summary crossed by the reversed backward summary

```
root():  x.f.a = source();  r = get(x);  sink(r.a);   // method 0, sink at node 2
get(x):  ret = x.f;  return ret;                      // method 1
```
Accessors a=1, f=4; bases, bindings and field limits as in WRAP. In run 1 the getter reads `f`
ABOVE its premise `(arg,.,*)`: its summary `(arg,.,*) → (ret,.,[any])` is in the DEMAND layer
(`g1_exit_demand`), so it is handed off (`handF_g1_exact`). The backward run enters the getter
with the premise `(ret,.a,$,T)` and computes the NORMAL backward summary
`(ret,.a,$,T) → (arg,.f.a,$,T)`; it is normal and its reversal is crossable (`CrossB`,
`revRec_g_crossB`), so it is not handed off (`demG_exact`): it is a record of forward run 3. Forward run 3 has only the zero fact as
an initial fact of the getter (`fg_getter_zero_only`) and crosses the call by the record (by
`satI`, `fg_record_sat`): it reports the vulnerability in the NORMAL layer (`fg_found`). -/

namespace Getter

open Wrap (Z Jw Jwf bx br zb)

def XsG : PFact := ⟨1, [4, 1], .exact, .conc 1⟩
/-- `x.f.a = source()`. -/
def srcG : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, XsG)]⟩
/-- `r = get(x)` (with the zero binding, as in WRAP). -/
def callG : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
/-- `ret = arg.f`. -/
def gs : Stmt := ⟨[3, 4], [(⟨3, [4], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def PG : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt srcG, 1), (0, 1, .call callG, 2), (1, 0, .stmt gs, 1)]⟩
/-- `sink(r.a)` at node 2 of the root. -/
def sinkG : PFact := ⟨2, [1], .exact, .conc 1⟩
def sinksG : List (MethodId × Node × PFact) := [(0, 2, sinkG)]

theorem hEG00 : (0, 0, Instr.stmt srcG, 1) ∈ PG.edges := List.Mem.head _

#print axioms hEG00

theorem hEG01 : (0, 1, Instr.call callG, 2) ∈ PG.edges := List.Mem.tail _ (List.Mem.head _)

#print axioms hEG01

theorem hEG10 : (1, 0, Instr.stmt gs, 1) ∈ PG.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hEG10

theorem pg_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ PG.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pg_no_clean

theorem pg_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ PG.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

#print axioms pg_no_filt

/-- Run 1: the source cut to `(x,.f,[any],T)`, the added fact `(arg,.f,[any],T)`, the exit fact
    `(ret,.,[any],*)` of the getter (demand layer), the root fact `(r,.,[any],T)`. -/
def X1g : AFact := ⟨⟨1, [4], .any, .conc 1⟩, true⟩
def A1g : PFact := ⟨3, [4], .any, .conc 1⟩
def Gg : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
def R1g : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩

/-! ### Forward run 1, completely -/

abbrev G1 := D PG cnt 1 policy1 sinksG [0]

def initsG1 : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jw)]
def edgesG1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X1g), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, R1g), (1, zeroFact, 0, Z), (1, zeroFact, 1, Z), (1, Jw, 0, Jwf), (1, Jw, 1, Gg)]
def addedsG1 : List (MethodId × PFact) := [(1, zeroFact), (1, A1g)]

def InvG1 : Obj → Prop
  | .init M i => (M, i) ∈ initsG1
  | .edge M i n f => (M, i, n, f) ∈ edgesG1
  | .added M a => (M, a) ∈ addedsG1
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkG ∧ b = true

instance : DecidablePred InvG1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsG1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesG1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsG1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkG ∧ b = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 1 OF THE GETTER PROGRAM. -/
theorem inv_g1 {o : Obj} (h : G1 o) : InvG1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsG1,
      InvG1 (.edge x.1 x.2 (PG.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 1 srcG x.2.2.2).facts, InvG1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesG1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 1 gs x.2.2.2).facts, InvG1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 1 srcG x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesG1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 1 gs x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callG.touched = false → InvG1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callG.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvG1 (.added callG.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addedsG1, InvG1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callG.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsG1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edgesG1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callG.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvG1 (.edge 0 x.2.1 2 (limitF cnt 1 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkG = .none ∨ check x.2.1 x.2.2.2 sinkG = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesG1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkG = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pg_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pg_no_clean hE).elim
  | filt _ hE _ _ => exact (pg_no_filt hE).elim

#print axioms inv_g1

theorem g1_e00 : G1 (.edge 0 zeroFact 0 Z) := D.start (D.root (List.Mem.head _))

#print axioms g1_e00

theorem g1_x01 : G1 (.edge 0 zeroFact 1 X1g) := D.step g1_e00 (s := srcG) hEG00 (by decide)

#print axioms g1_x01

theorem g1_init : G1 (.init 1 Jw) := by
  have ad : G1 (.added 1 A1g) :=
    D.added (c := callG) (e := bx) (a := ⟨A1g, true⟩) g1_x01 hEG01 (List.Mem.head _) (by decide)
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinksG)
    (roots := [0]) (P := PG) ad
  have hp : policy1 1 A1g = Jw := by decide
  rw [hp] at h
  exact h

#print axioms g1_init

/-- The exit edge of the getter in run 1: `(arg,.,*) → (ret,.,[any])`, DEMAND layer (the read of
    `f` is above the premise). -/
theorem g1_exit : G1 (.edge 1 Jw 1 Gg) := D.step (D.start g1_init) (s := gs) hEG10 (by decide)

#print axioms g1_exit

theorem g1_r : G1 (.edge 0 zeroFact 2 R1g) :=
  D.ret (c := callG) (e1 := bx) (a := ⟨A1g, true⟩) (j := Jw) (g := Gg)
    (r := ⟨⟨4, [], .any, .conc 1⟩, true⟩) (e2 := br) (r' := R1g)
    g1_x01 hEG01 (List.Mem.head _) (by decide) g1_init (by decide) g1_exit (by decide)
    (List.Mem.head _) (by decide)

#print axioms g1_r

/-- Run 1 reports the vulnerability in the demand layer. -/
theorem g1_vuln : G1 (.vuln 0 2 sinkG true) := D.vuln g1_r (List.Mem.head _) (by decide)

#print axioms g1_vuln

/-- The run-1 summary of the getter is in the demand layer, so it is not crossable. -/
theorem g1_exit_demand : Gg.demand = true ∧ ¬ Cross Jw Gg := ⟨rfl, by decide⟩

#print axioms g1_exit_demand

/-! ### The forward hand-off and the backward run -/

def handListG : List (MethodId × DemandEdge) :=
  [(0, ⟨R1g.fact, some zeroFact⟩), (1, ⟨Gg.fact, some Jw⟩)]

/-- THE FORWARD HAND-OFF OF RUN 1, EXACTLY: the root edge, and the demand-layer summary of the
    getter `((ret,.,[any],*), D-p = (arg,.,*))`. -/
theorem handF_g1_exact (m : MethodId) (d : DemandEdge) : handF PG G1 pubD m d ↔ (m, d) ∈ handListG := by
  constructor
  · rintro ⟨j, g, g', _, hg, hnc, hpub, rfl⟩
    cases hpub
    exact (by decide : ∀ x ∈ edgesG1, x.2.2.1 = PG.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ handListG)
      (m, j, PG.exit m, g) (inv_g1 hg) rfl hnc
  · intro h
    cases h with
    | head => exact ⟨zeroFact, R1g, R1g, D.root (List.Mem.head _), g1_r, by decide, rfl, rfl⟩
    | tail _ h => cases h with
      | head => exact ⟨Jw, Gg, Gg, g1_init, g1_exit, g1_exit_demand.2, rfl, rfl⟩
      | tail _ h => cases h

#print axioms handF_g1_exact

/-- The backward records: the reversals of the crossable exit edges of run 1 (only zero edges). -/
def recsBG : Recs := fun m y =>
  ∃ x : PFact × AFact, G1 (.init m x.1) ∧ G1 (.edge m x.1 (PG.exit m) x.2) ∧ Cross x.1 x.2 ∧
    y = revRec x

def recListBG : List (MethodId × (PFact × AFact)) :=
  [(0, revRec (zeroFact, Z)), (1, revRec (zeroFact, Z))]

theorem recsBG_bound {m : MethodId} {y : PFact × AFact} (h : recsBG m y) : (m, y) ∈ recListBG := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ edgesG1, e.2.2.1 = PG.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ recListBG) (m, x.1, PG.exit m, x.2) (inv_g1 hx) rfl hc

#print axioms recsBG_bound

abbrev PbG : Program := Program.rev PG

theorem PbG_edges : PbG.edges =
    [(0, 1, .stmt (Stmt.rev srcG), 0), (0, 2, .call (Call.rev callG), 1),
     (1, 1, .stmt (Stmt.rev gs), 0)] := rfl

#print axioms PbG_edges

theorem hbG_src : (0, 1, Instr.stmt (Stmt.rev srcG), 0) ∈ PbG.edges := by
  rw [PbG_edges]; exact List.Mem.head _

#print axioms hbG_src

theorem hbG_c : (0, 2, Instr.call (Call.rev callG), 1) ∈ PbG.edges := by
  rw [PbG_edges]; exact List.Mem.tail _ (List.Mem.head _)

#print axioms hbG_c

theorem hbG_g : (1, 1, Instr.stmt (Stmt.rev gs), 0) ∈ PbG.edges := by
  rw [PbG_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hbG_g

/-- The seed `(r,.a,$,T)`, the requirement `(ret,.a,$,T)` at the exit of the getter, the backward
    conclusion `(arg,.f.a,$,T)` (normal layer), and the requirement `(x,.f.a,$,T)` at the source. -/
def SG : AFact := ⟨sinkG, false⟩
def JbG : PFact := ⟨4, [1], .exact, .conc 1⟩
def GbG : AFact := ⟨⟨3, [4, 1], .exact, .conc 1⟩, false⟩
def XbG : AFact := ⟨XsG, false⟩

abbrev BG : Obj → Prop :=
  Backward.DB PbG cnt 2 (handF PG G1 pubD) emitM satI restrictI recsBG [] [0] sinksG true

def initsBG : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, JbG)]
def edgesBG : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Z), (0, zeroFact, 2, SG), (0, zeroFact, 1, Z), (0, zeroFact, 1, XbG),
   (0, zeroFact, 0, Z), (0, zeroFact, 0, XbG), (1, zeroFact, 1, Z), (1, zeroFact, 0, Z),
   (1, JbG, 1, ⟨JbG, false⟩), (1, JbG, 0, GbG)]
def addedsBG : List (MethodId × PFact) := [(1, JbG)]

def InvBG : Obj → Prop
  | .init M i => (M, i) ∈ initsBG
  | .edge M i n f => (M, i, n, f) ∈ edgesBG
  | .added M a => (M, a) ∈ addedsBG
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvBG := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsBG))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesBG))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsBG))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN 2 OF THE GETTER PROGRAM. -/
theorem inv_bg {o : Obj} (h : BG o) : InvBG o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsBG, InvBG (.edge x.1 x.2 (PbG.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [PbG_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 2 (Stmt.rev srcG) x.2.2.2).facts, InvBG (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBG, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 2 (Stmt.rev gs) x.2.2.2).facts, InvBG (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [PbG_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 2 (Stmt.rev srcG) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesBG, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 2 (Stmt.rev gs) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Call.rev callG).touched = false →
            InvBG (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Call.rev callG).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvBG (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ handListG, ∀ y ∈ addedsBG, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvBG (.init x.1 j))
      (m, d) ((handF_g1_exact m d).mp hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callG).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsBG, y.1 = 1 →
          ∀ z ∈ edgesBG, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ handListG, dd.1 = 1 → ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Call.rev callG).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBG (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) ((handF_g1_exact 1 d).mp hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesBG, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Call.rev callG).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListBG, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ (Call.rev callG).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBG (.edge 0 x.2.1 1 (limitF cnt 2 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (recsBG_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [PbG_edges] at hE
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
    rw [PbG_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesBG, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Call.rev callG).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvBG (.edge 0 zeroFact 1 (limitF cnt 2 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms inv_bg

/-- The backward run enters the getter by the demand-layer summary: the premise `(ret,.a,$,T)`. -/
theorem bg_init : BG (.init 1 JbG) := by
  have s02 : BG (.edge 0 zeroFact 2 SG) :=
    Backward.DB.seed (s := sinkG) (List.Mem.head _)
      (Backward.DB.start (Backward.DB.root (List.Mem.head _)))
  have ad : BG (.added 1 JbG) :=
    Backward.DB.added (c := Call.rev callG) (e := revEdge br.1 br.2) (a := ⟨JbG, false⟩) s02
      hbG_c (List.Mem.head _) (by decide)
  exact Backward.DB.initR ad ((handF_g1_exact 1 _).mpr (List.Mem.tail _ (List.Mem.head _)))
    (by decide)

#print axioms bg_init

/-- The backward summary of the getter: `(ret,.a,$,T) → (arg,.f.a,$,T)`, NORMAL layer. -/
theorem bg_g : BG (.edge 1 JbG 0 GbG) :=
  Backward.DB.step (Backward.DB.start bg_init) hbG_g (by decide)

#print axioms bg_g

/-- Its reversal `(arg,.f.a,$,T) → (ret,.a,$,T)` is crossable. -/
theorem revRec_g_cross : Cross (revRec (JbG, GbG)).1 (revRec (JbG, GbG)).2 := by decide

#print axioms revRec_g_cross

/-- The backward summary of the getter is NORMAL and its reversal is crossable (`CrossB`). -/
theorem revRec_g_crossB : CrossB JbG GbG := ⟨rfl, revRec_g_cross⟩

#print axioms revRec_g_crossB

theorem bg_x00 : BG (.edge 0 zeroFact 0 XbG) := by
  have s02 : BG (.edge 0 zeroFact 2 SG) :=
    Backward.DB.seed (s := sinkG) (List.Mem.head _)
      (Backward.DB.start (Backward.DB.root (List.Mem.head _)))
  have x01 : BG (.edge 0 zeroFact 1 XbG) :=
    Backward.DB.ret (c := Call.rev callG) (e1 := revEdge br.1 br.2) (a := ⟨JbG, false⟩) (j := JbG)
      (g := GbG) (d := ⟨Gg.fact, some Jw⟩) (g' := GbG) (r := GbG) (e2 := revEdge bx.1 bx.2)
      (r' := XbG) s02 hbG_c (List.Mem.head _) (by decide) bg_init bg_g
      ((handF_g1_exact 1 _).mpr (List.Mem.tail _ (List.Mem.head _))) (by decide) (by decide)
      (by decide) (List.Mem.head _) (by decide)
  exact Backward.DB.step x01 hbG_src (by decide)

#print axioms bg_x00

/-! ### The backward hand-off: the normal backward summary is a record, not a demand -/

def demG : MethodId → DemandEdge → Prop := demOfN PbG BG (pubR (handF PG G1 pubD))

/-- THE BACKWARD HAND-OFF, EXACTLY: the zero demand and the root edge `((x,.f.a,$,T), none)`. The
    backward summary of the getter is crossable, so the getter gets only the zero demand. -/
theorem demG_exact (m : MethodId) (d : DemandEdge) :
    demG m d ↔ d = Backward.zeroDem ∨ (m = 0 ∧ d = ⟨XbG.fact, none⟩) := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, _, _⟩)
    · exact Or.inl h
    · exact (by decide : ∀ x ∈ edgesBG, x.2.1 = zeroFact → x.2.2.1 = PbG.exit x.1 →
        (⟨x.2.2.2.fact, none⟩ : DemandEdge) = Backward.zeroDem ∨
          (x.1 = 0 ∧ (⟨x.2.2.2.fact, none⟩ : DemandEdge) = ⟨XbG.fact, none⟩))
        (m, zeroFact, PbG.exit m, g) (inv_bg hg) rfl rfl
    · exact absurd ((by decide : ∀ x ∈ initsBG, x.2 ≠ zeroFact →
        ∀ y ∈ edgesBG, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = PbG.exit x.1 →
          CrossB x.2 y.2.2.2)
        (m, jb) (inv_bg hjb) hne (m, jb, PbG.exit m, gb) (inv_bg hgb) rfl rfl rfl) hnc
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨XbG, bg_x00, rfl⟩)

#print axioms demG_exact

def demListG : List DemandEdge := [Backward.zeroDem, ⟨XbG.fact, none⟩]

theorem demG_bound {m : MethodId} {d : DemandEdge} (h : demG m d) : d ∈ demListG := by
  rcases (demG_exact m d).mp h with rfl | ⟨_, rfl⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

#print axioms demG_bound

theorem demG_dout {m : MethodId} {d : DemandEdge} (h : demG m d) : d.dout = none :=
  (by decide : ∀ x ∈ demListG, x.dout = none) d (demG_bound h)

#print axioms demG_dout

/-! ### Forward run 3, completely -/

/-- The records of forward run 3 (`hrcN` of the brief): the crossable exit edges of run 1 and the
    reversed NORMAL backward summaries with a crossable reversal (`CrossB`). -/
def rcG3 : Recs := fun m x =>
  (G1 (.init m x.1) ∧ G1 (.edge m x.1 (PG.exit m) x.2) ∧ Cross x.1 x.2) ∨
  (∃ jb gb, BG (.init m jb) ∧ jb ≠ zeroFact ∧ BG (.edge m jb (PbG.exit m) gb) ∧
    CrossB jb gb ∧ x = revRec (jb, gb))

def recListFG : List (MethodId × (PFact × AFact)) :=
  [(0, (zeroFact, Z)), (1, (zeroFact, Z)), (1, revRec (JbG, GbG))]

theorem rcG3_bound {m : MethodId} {x : PFact × AFact} (h : rcG3 m x) : (m, x) ∈ recListFG := by
  rcases h with ⟨_, hx, hc⟩ | ⟨jb, gb, hjb, hne, hgb, _, rfl⟩
  · exact (by decide : ∀ e ∈ edgesG1, e.2.2.1 = PG.exit e.1 → Cross e.2.1 e.2.2.2 →
      (e.1, (e.2.1, e.2.2.2)) ∈ recListFG) (m, x.1, PG.exit m, x.2) (inv_g1 hx) rfl hc
  · exact (by decide : ∀ x ∈ initsBG, x.2 ≠ zeroFact →
      ∀ y ∈ edgesBG, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = PbG.exit x.1 →
        (x.1, revRec (x.2, y.2.2.2)) ∈ recListFG)
      (m, jb) (inv_bg hjb) hne (m, jb, PbG.exit m, gb) (inv_bg hgb) rfl rfl rfl

#print axioms rcG3_bound

/-- The record of the getter in forward run 3: the reversed backward summary. -/
theorem rcG3_g : rcG3 1 (revRec (JbG, GbG)) :=
  Or.inr ⟨JbG, GbG, bg_init, by decide, bg_g, revRec_g_crossB, rfl⟩

#print axioms rcG3_g

abbrev FG : Obj → Prop := DR PG cnt 3 demG emitM satI restrictI rcG3 sinksG [0]

def A3g : PFact := ⟨3, [4, 1], .exact, .conc 1⟩
def RG3 : AFact := ⟨⟨2, [1], .exact, .conc 1⟩, false⟩

def initsFG : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact)]
def edgesFG : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, XbG), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, RG3), (1, zeroFact, 0, Z), (1, zeroFact, 1, Z)]
def addedsFG : List (MethodId × PFact) := [(1, zeroFact), (1, A3g)]

def InvFG : Obj → Prop
  | .init M i => (M, i) ∈ initsFG
  | .edge M i n f => (M, i, n, f) ∈ edgesFG
  | .added M a => (M, a) ∈ addedsFG
  | .req _ _ _ => False
  | .vuln M n s b => M = 0 ∧ n = 2 ∧ s = sinkG ∧ b = false

instance : DecidablePred InvFG := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsFG))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesFG))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsFG))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s b => inferInstanceAs (Decidable (M = 0 ∧ n = 2 ∧ s = sinkG ∧ b = false))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE FORWARD RUN 3 OF THE GETTER PROGRAM. -/
theorem inv_fg {o : Obj} (h : FG o) : InvFG o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsFG,
      InvFG (.edge x.1 x.2 (PG.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 srcG x.2.2.2).facts, InvFG (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFG, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 gs x.2.2.2).facts, InvFG (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 srcG x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesFG, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 gs x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callG.touched = false → InvFG (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callG.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, InvFG (.added callG.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ demListG, ∀ y ∈ addedsFG,
      ∀ j ∈ (emitM x.din y.2).toList, InvFG (.init y.1 j))
      d (demG_bound hd) (m, a) ih j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hres _ _ _ _ _ _ _ =>
    rw [restrictI_none (demG_dout hd)] at hres
    cases hres
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callG.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ recListFG, y.1 = 1 →
          (satI y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts,
          ∀ e2 ∈ callG.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvFG (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (rcG3_bound hrec) rfl hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkG = .none ∨ check x.2.1 x.2.2.2 sinkG = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact ⟨rfl, rfl, rfl, (by decide : ∀ x ∈ edgesFG, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkG = .triggered → x.2.2.2.demand = false) (0, i, 2, f) ih rfl rfl hc⟩
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (pg_no_clean hE).elim
  | reqClean _ hE _ _ => exact (pg_no_clean hE).elim
  | filt _ hE _ _ => exact (pg_no_filt hE).elim

#print axioms inv_fg

/-- Forward run 3 has only the zero fact as an initial fact of the getter, and every edge of the
    getter has the zero premise. -/
theorem fg_getter_zero_only :
    (∀ j, FG (.init 1 j) → j = zeroFact) ∧ (∀ j n g, FG (.edge 1 j n g) → j = zeroFact) :=
  ⟨fun j h => (by decide : ∀ x ∈ initsFG, x.1 = 1 → x.2 = zeroFact) (1, j) (inv_fg h) rfl,
   fun j n g h => (by decide : ∀ x ∈ edgesFG, x.1 = 1 → x.2.1 = zeroFact) (1, j, n, g)
     (inv_fg h) rfl⟩

#print axioms fg_getter_zero_only

/-- The caller fact `(arg,.f.a,$,T)` satisfies the premise of the reversed backward summary. -/
theorem fg_record_sat : satI (revRec (JbG, GbG)).1 A3g = true := by decide

#print axioms fg_record_sat

/-- FORWARD RUN 3 REPORTS THE VULNERABILITY, in the NORMAL layer, by the record. -/
theorem fg_found : FG (.vuln 0 2 sinkG false) := by
  have e00 : FG (.edge 0 zeroFact 0 Z) := DR.start (DR.root (List.Mem.head _))
  have x01 : FG (.edge 0 zeroFact 1 XbG) := DR.step e00 (s := srcG) hEG00 (by decide)
  have r2 : FG (.edge 0 zeroFact 2 (limitF cnt 3 RG3)) :=
    DR.retRec (c := callG) (e1 := bx) (a := ⟨A3g, false⟩) (j := (revRec (JbG, GbG)).1)
      (g := (revRec (JbG, GbG)).2) (r := ⟨⟨4, [1], .exact, .conc 1⟩, false⟩) (e2 := br) (r' := RG3)
      x01 hEG01 (List.Mem.head _) (by decide) rcG3_g (Or.inl fg_record_sat) (by decide)
      (List.Mem.head _) (by decide)
  exact DR.vuln r2 (s := sinkG) (List.Mem.head _) (by decide)

#print axioms fg_found

end Getter

end ApSpec.HandoffCases
