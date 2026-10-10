/-
  A negative abstraction kernel for F72: an ATOMIC field cleaner can lose a flow after
  backward FLOW emission. The user's F74 construction instead reads the field into a fresh
  temporary, cleans that temporary, and strongly writes it back. This kernel omits those
  read/write edges, so its loss does not refute the lowered interpreter program. The corrected
  program is checked in ReviewFieldCleaner. The bounds below check the atomic closures, with
  their actual hand-offs, records, sink seeds and source-hit selection.
-/
import ApSpec.AbsClosure
import ApSpec.HandoffCases
import ApSpec.ForwardSeeds

namespace ApSpec.ReviewReversal
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def st : Kind := .star (.set [])
def cnt : Acc → Bool := fun _ => true
def id (b : Base) : MicroEdge := (⟨b, [], st, .star⟩, ⟨b, [], st, .star⟩)
def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def zb : MicroEdge := id 0
def br : MicroEdge := (⟨5, [], st, .star⟩, ⟨2, [], st, .star⟩)
def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [], .exact, .conc 1⟩)]⟩
def callC : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
def wn : MicroEdge := (⟨3, [], st, .star⟩, ⟨4, [4], st, .star⟩)
def wf : MicroEdge := (⟨4, [], st, .star⟩, ⟨5, [6], st, .star⟩)
/-- `p.n = arg`, with the unchanged argument and the strong-write keep row. -/
def writeN : Stmt := ⟨[3, 4], [id 3,
  (⟨3, [], st, .star⟩, ⟨4, [4], st, .star⟩),
  (⟨4, [], .star (.set [4]), .star⟩, ⟨4, [], .star (.set [4]), .star⟩)]⟩
/-- `clean_T(p.g)`, where n=4 and g=5 are different fields. -/
def cl : Cleaner := ⟨4, [5], .atAndBelow, some 1⟩
/-- `ret.f = p`, with unchanged p and the strong-write keep row; f=6. -/
def writeF : Stmt := ⟨[4, 5], [id 4,
  (⟨4, [], st, .star⟩, ⟨5, [6], st, .star⟩),
  (⟨5, [], .star (.set [6]), .star⟩, ⟨5, [], .star (.set [6]), .star⟩)]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 1 then 3 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callC, 2),
   (1, 0, .stmt writeN, 1), (1, 1, .clean cl, 2), (1, 2, .stmt writeF, 3)]⟩
abbrev Pb : Program := Program.rev P
def sink : PFact := ⟨2, [6, 4], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sink)]

def Jw : PFact := ⟨3, [], st, .star⟩
def PN : AFact := ⟨⟨4, [4], st, .star⟩, false⟩
def GF : AFact := ⟨⟨5, [6], .any, .star⟩, true⟩
def A1 : PFact := ⟨3, [], .exact, .conc 1⟩
def X1 : AFact := ⟨⟨1, [], .exact, .conc 1⟩, false⟩
def R1out : AFact := ⟨⟨2, [6], .any, .conc 1⟩, true⟩
def dC : DemandEdge := normDem ⟨GF.fact, some Jw⟩
def Z : AFact := Backward.zeroAF

def S1 : LS where
  inits := [(0, zeroFact), (1, zeroFact), (1, Jw)]
  edges := [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X1),
    (0, zeroFact, 2, Z), (0, zeroFact, 2, R1out),
    (1, zeroFact, 0, Z), (1, zeroFact, 1, Z), (1, zeroFact, 2, Z), (1, zeroFact, 3, Z),
    (1, Jw, 0, ⟨Jw, false⟩), (1, Jw, 1, ⟨Jw, false⟩), (1, Jw, 1, PN),
    (1, Jw, 2, ⟨Jw, false⟩), (1, Jw, 2, PN),
    (1, Jw, 3, ⟨Jw, false⟩), (1, Jw, 3, PN), (1, Jw, 3, GF)]
  addeds := [(1, zeroFact), (1, A1)]
  reqs := []
  vulns := [(0, 2, sink, true)]

def H1L : List (MethodId × DemandEdge) :=
  [(0, normDem ⟨R1out.fact, some zeroFact⟩), (1, dC)]
def RB1L : List (MethodId × (PFact × AFact)) :=
  [(0, (zeroFact, Z)), (1, (zeroFact, Z)),
   (1, revRec (Jw, ⟨Jw, false⟩)), (1, revRec (Jw, PN))]

abbrev R1 : Obj → Prop := D P cnt 1 policy1 sinks [0]
theorem closed1 : ClosedD P cnt 1 sinks [0] S1 := by decide
theorem inv1 {o : Obj} (h : R1 o) : S1.Inv o := closedD_sound P cnt 1 sinks [0] S1 closed1 h

theorem hand1_bound {m : MethodId} {d : DemandEdge} (h : handFA P R1 pubD m d) :
    (m, d) ∈ H1L := by
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, hpub, rfl⟩, rfl⟩ := h
  have hp : g' = g := hpub
  subst hp
  exact (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
    (x.1, normDem ⟨x.2.2.2.fact, some x.2.1⟩) ∈ H1L)
    (m, j, P.exit m, g') (inv1 hg) rfl hnc

def recsB1 : Recs := fun m y => ∃ x : PFact × AFact, R1 (.init m x.1) ∧
  R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2 ∧ y = revRec x
theorem recs1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) :
    (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

def Rq : PFact := ⟨5, [6], .any, .conc 1⟩
def Jb : PFact := ⟨5, [6], st, .star⟩
def PW : AFact := ⟨⟨4, [], st, .star⟩, false⟩
def PC : AFact := ⟨⟨4, [], st, .starEx [1]⟩, false⟩
def GB : AFact := ⟨⟨3, [], .any, .starEx [1]⟩, true⟩
def PB : AFact := ⟨⟨4, [], .star (.set [4, 4]), .starEx [1]⟩, false⟩

def S2 : LS where
  inits := [(0, zeroFact), (1, zeroFact), (1, Jb)]
  edges := [(0, zeroFact, 2, Z), (0, zeroFact, 2, R1out),
    (0, zeroFact, 1, Z), (0, zeroFact, 0, Z),
    (1, zeroFact, 3, Z), (1, zeroFact, 2, Z), (1, zeroFact, 1, Z), (1, zeroFact, 0, Z),
    (1, Jb, 3, ⟨Jb, false⟩), (1, Jb, 2, PW), (1, Jb, 1, PC),
    (1, Jb, 0, GB), (1, Jb, 0, PB)]
  addeds := [(1, Rq)]
  reqs := []
  vulns := []

abbrev B2 : Obj → Prop := DBW Pb cnt 1 (handFA P R1 pubD) recsB1 [0] sinks
theorem closed2 : ClosedBA Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (hand1_bound hd)) (fun _ _ hx => recs1_bound hx) h

/-! The positive derivations use the least closures, not just membership of the bounds. -/
theorem r1_source : R1 (.edge 0 zeroFact 1 X1) :=
  D.step (D.start (D.root (by decide))) (s := src) (by simp [P]) (by decide)
theorem r1_added : R1 (.added 1 A1) :=
  D.added (c := callC) (e := bx) (a := ⟨A1, false⟩) (n' := 2)
    r1_source (by simp [P]) (by decide) (by decide)
theorem r1_init : R1 (.init 1 Jw) := D.initA r1_added
theorem r1_written : R1 (.edge 1 Jw 1 PN) :=
  D.step (D.start r1_init) (s := writeN) (by simp [P]) (by decide)
theorem r1_clean : R1 (.edge 1 Jw 2 PN) :=
  D.clean r1_written (cl := cl) (by simp [P]) (by decide)
theorem r1_exit : R1 (.edge 1 Jw 3 GF) :=
  D.step r1_clean (s := writeF) (by simp [P]) (by decide)
theorem hand1_C : handFA P R1 pubD 1 dC :=
  ⟨_, ⟨Jw, GF, GF, r1_init, r1_exit, by decide, rfl, rfl⟩, rfl⟩
theorem r1_return : R1 (.edge 0 zeroFact 2 R1out) :=
  D.ret (c := callC) (e1 := bx) (a := ⟨A1, false⟩) (j := Jw) (g := GF)
    (r := ⟨⟨5, [6], .any, .conc 1⟩, true⟩) (e2 := br) (r' := R1out)
    r1_source (by simp [P]) (by decide) (by decide) r1_init (by decide) r1_exit
    (by decide) (by decide) (by decide)
theorem r1_found : R1 (.vuln 0 2 sink true) := D.vuln r1_return (by decide) (by decide)

/-- The cleaner is disjoint from the actual propagated run-1 fact. Run 1 has no request,
    and C has no concrete non-zero initial fact. -/
theorem run1_disjoint_no_request : cleanPos cl PN.fact = .disjoint ∧
    (∀ M j t, ¬ R1 (.req M j t)) ∧
    (∀ j, R1 (.init 1 j) → j = zeroFact ∨ j = Jw) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro M j t h
    exact List.not_mem_nil (inv1 h)
  · intro j h
    exact (by decide : ∀ x ∈ S1.inits, x.1 = 1 → x.2 = zeroFact ∨ x.2 = Jw)
      (1, j) (inv1 h) rfl

theorem b2_zero : B2 (.edge 0 zeroFact 2 Z) := DBA.start (DBA.root (by decide))
theorem b2_seed : B2 (.edge 0 zeroFact 2 R1out) := DBA.seed (s := sink) (by decide) b2_zero
theorem b2_added : B2 (.added 1 Rq) :=
  DBA.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨Rq, true⟩)
    (n' := 1) b2_seed (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide) (by decide)
theorem b2_init : B2 (.init 1 Jb) := DBA.initR (d := dC) b2_added hand1_C (by decide)
theorem b2_copy : B2 (.edge 1 Jb 2 PW) :=
  DBA.step (DBA.start b2_init) (s := Stmt.rev writeF)
    (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_clean : B2 (.edge 1 Jb 1 PC) :=
  DBA.clean b2_copy (cl := cl) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_exit : B2 (.edge 1 Jb 0 GB) :=
  DBA.step b2_clean (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)

/-- FLOW broadening makes the same cleaner partial in the backward run. Its surviving
    summary rejects the concrete T requirement at the call. -/
theorem backward_loss : cleanPos cl PW.fact = .part ∧
    cleanRes cl PW = ⟨[PC], [1]⟩ ∧ restrictI Jb GB dC = some GB ∧
    (applySummary ⟨Rq, true⟩ Jb GB).facts = [] := ⟨by decide, rfl, by decide, by decide⟩

def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))
def d3 : DemandEdge := normDem ⟨GB.fact, some Jb⟩
def D3L : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, none⟩), (1, ⟨zeroFact, none⟩), (1, d3)]
theorem dem3_C : dem3 1 d3 :=
  ⟨_, Or.inr (Or.inr ⟨Jb, GB, GB, b2_init, by decide, b2_exit, by decide,
    ⟨dC, hand1_C, by decide⟩, rfl⟩), rfl⟩
theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1)
      (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc
      (m, dd) (hand1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

def rc3 : Recs := fun m x =>
  (R1 (.init m x.1) ∧ R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2) ∨
  (∃ jb gb, B2 (.init m jb) ∧ jb ≠ zeroFact ∧ B2 (.edge m jb (Pb.exit m) gb) ∧
    CrossB jb gb ∧ x = revRec (jb, gb))
def RC3L : List (MethodId × (PFact × AFact)) :=
  [(0, (zeroFact, Z)), (1, (zeroFact, Z)), (1, (Jw, ⟨Jw, false⟩)),
   (1, (Jw, PN)), (1, revRec (Jb, PB))]
theorem rc3_bound {m : MethodId} {x : PFact × AFact} (h : rc3 m x) : (m, x) ∈ RC3L := by
  rcases h with ⟨_, hx, hc⟩ | ⟨jb, gb, hjb, hne, hgb, hc, rfl⟩
  · exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
      (e.1, (e.2.1, e.2.2.2)) ∈ RC3L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → CrossB y.2 z.2.2.2 → (y.1, revRec (y.2, z.2.2.2)) ∈ RC3L)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hc

def stmtEdges : Instr → List MicroEdge
  | .stmt s => s.edges
  | _ => []
/-- No backward requirement meets a source result at its forward target node. -/
theorem no_source_hit : ∀ M n e, ¬ FSeeds.srcHit P B2 M n e := by
  intro M n e h
  obtain ⟨s, n', i, f, lX, l1, l', hE, he, hz, hnz, hf, _, hd, hsrc⟩ := h
  have hbase : f.fact.base = e.2.base := hd.2.1.symm.trans hsrc.2.1
  have hno := (by decide : ∀ pe ∈ P.edges, ∀ e ∈ stmtEdges pe.2.2.1,
    e.1.base = zeroBase → e.2.base ≠ zeroBase → ∀ x ∈ S2.edges,
    x.1 = pe.1 → x.2.2.1 = pe.2.2.2 → x.2.2.2.fact.base ≠ e.2.base)
    (M, n, Instr.stmt s, n') hE e he hz hnz (M, i, n', f) (inv2 hf) rfl rfl
  exact hno hbase

def P3 : Program := FSeeds.keepSources P (fun _ _ _ => false)
abbrev F3 : Obj → Prop := DRW P3 cnt 2 dem3 rc3 sinks [0]
def S3 : LS where
  inits := [(0, zeroFact), (1, zeroFact)]
  edges := [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 2, Z),
    (1, zeroFact, 0, Z), (1, zeroFact, 1, Z), (1, zeroFact, 2, Z), (1, zeroFact, 3, Z)]
  addeds := [(1, zeroFact)]
  reqs := []
  vulns := []
theorem closed3 : ClosedRA P3 cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P3 cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h
theorem no_run3_sink : ∀ M n s b, ¬ F3 (.vuln M n s b) := by
  intro M n s b h
  exact List.not_mem_nil (inv3 h)

/-- The concrete execution carries T through p.n, while the cleaner acts on p.g. -/
def lx : Loc := ⟨1, [], 1⟩
def la : Loc := ⟨3, [], 1⟩
def lp : Loc := ⟨4, [4], 1⟩
def lr : Loc := ⟨5, [6, 4], 1⟩
def ls : Loc := ⟨2, [6, 4], 1⟩

theorem source_den : den zeroFact ⟨1, [], .exact, .conc 1⟩ zeroLoc lx :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
theorem arg_den : den bx.1 bx.2 lx la :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
theorem writeN_den : den wn.1 wn.2 la lp := by
  exact ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
theorem writeF_den : den wf.1 wf.2 lp lr := by
  exact ⟨rfl, rfl, trivial, rfl, trivial, [4], [4], rfl, rfl, rfl, rfl, rfl⟩
theorem ret_den : den br.1 br.2 lr ls :=
  ⟨rfl, rfl, trivial, rfl, trivial, [6, 4], [6, 4], rfl, rfl, rfl, rfl, rfl⟩

theorem concrete_source : Flow P 0 zeroLoc 1 lx :=
  Flow.step (Flow.start 0 zeroLoc) (s := src) (by simp [P])
    (Or.inr ⟨(zeroFact, ⟨1, [], .exact, .conc 1⟩), by decide, source_den⟩)
theorem concrete_C : Flow P 1 la 3 lr := by
  have h1 : Flow P 1 la 1 lp :=
    Flow.step (Flow.start 1 la) (s := writeN) (by simp [P])
      (Or.inr ⟨wn, by decide, writeN_den⟩)
  have h2 : Flow P 1 la 2 lp := Flow.clean h1 (cl := cl) (by simp [P]) (by decide)
  exact Flow.step h2 (s := writeF) (by simp [P])
    (Or.inr ⟨wf, by decide, writeF_den⟩)
theorem concrete_sink : Reach P [0] 0 2 ls :=
  Reach.root (by decide) (Flow.call (c := callC) (e1 := bx) (e2 := br)
    concrete_source (by simp [P]) (by decide) arg_den concrete_C (by decide) ret_den)

/-- The implementation's source-hit test also has no hit: no reversed source edge gives
    any output on an actual backward requirement at the corresponding node. -/
theorem no_source_application : ∀ M n s n' e i f,
    (M, n, Instr.stmt s, n') ∈ P.edges → e ∈ s.edges →
    e.1.base = zeroBase → e.2.base ≠ zeroBase → B2 (.edge M i n' f) →
    (applyEdge f (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts = [] := by
  intro M n s n' e i f hE he hz hnz hf
  exact (by decide : ∀ pe ∈ P.edges, ∀ e ∈ stmtEdges pe.2.2.1,
    e.1.base = zeroBase → e.2.base ≠ zeroBase → ∀ x ∈ S2.edges,
    x.1 = pe.1 → x.2.2.1 = pe.2.2.2 →
    (applyEdge x.2.2.2 (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts = [])
    (M, n, Instr.stmt s, n') hE e he hz hnz (M, i, n', f) (inv2 hf) rfl rfl

theorem hand1_exact (m : MethodId) (d : DemandEdge) :
    handFA P R1 pubD m d ↔ (m, d) ∈ H1L := by
  refine ⟨hand1_bound, ?_⟩
  intro h
  simp [H1L, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, ⟨zeroFact, R1out, R1out, D.root (by decide), r1_return,
      by decide, rfl, rfl⟩, rfl⟩
  · exact hand1_C

theorem dem3_exact (d : DemandEdge) : dem3 1 d ↔ d = Backward.zeroDem ∨ d = d3 := by
  constructor
  · intro h
    have hd := dem3_bound h
    simpa [demFor, D3L, Backward.zeroDem] using hd
  · rintro (rfl | rfl)
    · exact ⟨Backward.zeroDem, Or.inl rfl, rfl⟩
    · exact dem3_C

/-- A real sink reported in run 1 is absent in the next seeded forward closure, with
    nondecreasing limits. The default source selection is empty, including the stronger
    reversed-source-application test, and persistent records have been included. -/
theorem default_reversal_loss : Reach P [0] 0 2 ls ∧ R1 (.vuln 0 2 sink true) ∧
    1 ≤ 1 ∧ 1 ≤ 2 ∧ (∀ M n e, ¬ FSeeds.srcHit P B2 M n e) ∧
    (∀ M n s b, ¬ F3 (.vuln M n s b)) :=
  ⟨concrete_sink, r1_found, by decide, by decide, no_source_hit, no_run3_sink⟩

/-- Run 1 has no confirmed report to preserve separately. -/
theorem no_confirmed_run1 : ∀ M n s, ¬ R1 (.vuln M n s false) := by
  intro M n s h
  exact (by decide : ∀ x ∈ S1.vulns, x.2.2.2 ≠ false) (M, n, s, false) (inv1 h) rfl

/-- The record bounds include all normal run-1 exit summaries: every such summary is
    crossable in this program. -/
theorem all_normal1_cross {m : MethodId} {j : PFact} {g : AFact}
    (h : R1 (.edge m j (P.exit m) g)) (hn : g.demand = false) : Cross j g :=
  (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → x.2.2.2.demand = false →
    Cross x.2.1 x.2.2.2) (m, j, P.exit m, g) (inv1 h) rfl hn
/-- Every eligible normal backward exit summary is also crossed by its reversal. -/
theorem all_normal2_crossB {m : MethodId} {j : PFact} {g : AFact}
    (h : B2 (.edge m j (Pb.exit m) g)) (hn : g.demand = false) (hj : j ≠ zeroFact) : CrossB j g :=
  (by decide : ∀ x ∈ S2.edges, x.2.2.1 = Pb.exit x.1 → x.2.2.2.demand = false →
    x.2.1 ≠ zeroFact → CrossB x.2.1 x.2.2.2) (m, j, Pb.exit m, g) (inv2 h) rfl hn hj
theorem all_normal1_persisted {m : MethodId} {j : PFact} {g : AFact}
    (hi : R1 (.init m j)) (hg : R1 (.edge m j (P.exit m) g)) (hn : g.demand = false) :
    recsB1 m (revRec (j, g)) ∧ rc3 m (j, g) :=
  ⟨⟨(j, g), hi, hg, all_normal1_cross hg hn, rfl⟩,
   Or.inl ⟨hi, hg, all_normal1_cross hg hn⟩⟩
theorem all_normal2_persisted {m : MethodId} {j : PFact} {g : AFact}
    (hi : B2 (.init m j)) (hg : B2 (.edge m j (Pb.exit m) g)) (hn : g.demand = false)
    (hj : j ≠ zeroFact) : rc3 m (revRec (j, g)) :=
  Or.inr ⟨j, g, hi, hj, hg, all_normal2_crossB hg hn hj, rfl⟩

local instance (i f : PFact) : Decidable (MarkRev i f) :=
  decidable_of_iff _ (HandoffCases.markRev_iff i f).symm
local instance (i f : Kind) : Decidable (ExactShape i f) := by
  cases i <;> cases f <;> dsimp [ExactShape] <;> infer_instance

/-- A finite certificate for the usual program, mark and reversal hypotheses. -/
def scopeI : Instr → Prop
  | .stmt s =>
    (∀ e ∈ s.edges, memB e.1.base s.touched = true ∧
      Exact.markEdgeB e.1.mark e.2.mark = true ∧ ExactShape e.1.kind e.2.kind ∧ MarkRev e.1 e.2) ∧
    (memB zeroBase s.touched = true → (zeroFact, zeroFact) ∈ s.edges)
  | .call c =>
    (∀ e ∈ c.toCallee, e.1.mark = .star ∧ e.2.mark = .star ∧ BindRev e) ∧
    (∀ e ∈ c.fromCallee, e.1.mark = .star ∧ e.2.mark = .star ∧ BindRev e ∧ e.1.base ≠ zeroBase)
  | .clean c => c.base ≠ zeroBase
  | .filt _ _ => False
instance (i : Instr) : Decidable (scopeI i) := by
  cases i <;> dsimp [scopeI, BindRev] <;> infer_instance
theorem scope_checked : ∀ pe ∈ P.edges, scopeI pe.2.2.1 := by decide

theorem wf_program : P.WF where
  stmtTouched := by
    intro M n s n' hE e he
    exact ((scope_checked (M, n, .stmt s, n') hE).1 e he).1
  toStar := by
    intro M n c n' hE e he
    exact ((scope_checked (M, n, .call c, n') hE).1 e he).1
  fromStar := by
    intro M n c n' hE e he
    exact ((scope_checked (M, n, .call c, n') hE).2 e he).1
  filtPrefix := by
    intro M n b may n' hE
    exact False.elim (scope_checked (M, n, .filt b may, n') hE)
theorem wf_marks : Exact.MarkWF P where
  stmt := by
    intro M n s n' hE e he
    exact ((scope_checked (M, n, .stmt s, n') hE).1 e he).2.1
  toC := by
    intro M n c n' hE e he
    have hp := ((scope_checked (M, n, .call c, n') hE).1 e he).1
    have ht := ((scope_checked (M, n, .call c, n') hE).1 e he).2.1
    rw [hp, ht]; rfl
  fromC := by
    intro M n c n' hE e he
    have hp := ((scope_checked (M, n, .call c, n') hE).2 e he).1
    have ht := ((scope_checked (M, n, .call c, n') hE).2 e he).2.1
    rw [hp, ht]; rfl
theorem rev_stmts : RevStmts P := by
  intro M n s n' hE e he
  exact ((scope_checked (M, n, .stmt s, n') hE).1 e he).2.2
theorem mark_rev_stmts : Backward.StmtsMarkRev P := by
  intro M n s n' hE e he
  exact ((scope_checked (M, n, .stmt s, n') hE).1 e he).2.2.2
theorem rev_calls : RevCalls P := by
  intro M n c n' hE
  exact ⟨fun e he => ((scope_checked (M, n, .call c, n') hE).1 e he).2.2,
    fun e he => ((scope_checked (M, n, .call c, n') hE).2 e he).2.2.1⟩
theorem binding_targets_star : BindTargetsStar P := by
  intro M n c n' hE
  exact ⟨fun e he => ((scope_checked (M, n, .call c, n') hE).1 e he).2.1,
    fun e he => ((scope_checked (M, n, .call c, n') hE).2 e he).2.1⟩
theorem no_zero_back : Backward.NoZeroBack P := by
  intro M n c n' hE e he
  exact ((scope_checked (M, n, .call c, n') hE).2 e he).2.2.2
theorem zero_kept : Backward.ZeroKept P where
  stmt := by
    intro M n s n' hE
    exact (scope_checked (M, n, .stmt s, n') hE).2
  clean := by
    intro M n c n' hE
    exact scope_checked (M, n, .clean c, n') hE
  filt := by
    intro M n b may n' hE
    exact False.elim (scope_checked (M, n, .filt b may, n') hE)

/-! The same default failure with strictly increasing limits 1 / 2 / 3. -/
namespace Strict
def Rq : PFact := ⟨5, [6, 4], .exact, .conc 1⟩
def S2 : LS := { ReviewReversal.S2 with
  edges := [(0, zeroFact, 2, Z), (0, zeroFact, 2, ⟨sink, false⟩)] ++
    ReviewReversal.S2.edges.drop 2
  addeds := [(1, Rq)] }
abbrev B2 : Obj → Prop := DBW Pb cnt 2 (handFA P R1 pubD) recsB1 [0] sinks
theorem closed2 : ClosedBA Pb cnt 2 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 2 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (hand1_bound hd)) (fun _ _ hx => recs1_bound hx) h
theorem b2_zero : B2 (.edge 0 zeroFact 2 Z) := DBA.start (DBA.root (by decide))
theorem b2_seed : B2 (.edge 0 zeroFact 2 ⟨sink, false⟩) :=
  DBA.seed (s := sink) (by decide) b2_zero
theorem b2_added : B2 (.added 1 Rq) :=
  DBA.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨Rq, false⟩)
    (n' := 1) b2_seed (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide) (by decide)
theorem b2_init : B2 (.init 1 Jb) := DBA.initR (d := dC) b2_added hand1_C (by decide)
theorem b2_copy : B2 (.edge 1 Jb 2 PW) :=
  DBA.step (DBA.start b2_init) (s := Stmt.rev writeF)
    (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_clean : B2 (.edge 1 Jb 1 PC) :=
  DBA.clean b2_copy (cl := cl) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_exit : B2 (.edge 1 Jb 0 GB) :=
  DBA.step b2_clean (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)

def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))
theorem dem3_C : dem3 1 d3 :=
  ⟨_, Or.inr (Or.inr ⟨Jb, GB, GB, b2_init, by decide, b2_exit, by decide,
    ⟨dC, hand1_C, by decide⟩, rfl⟩), rfl⟩
theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1)
      (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc
      (m, dd) (hand1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

def rc3 : Recs := fun m x =>
  (R1 (.init m x.1) ∧ R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2) ∨
  (∃ jb gb, B2 (.init m jb) ∧ jb ≠ zeroFact ∧ B2 (.edge m jb (Pb.exit m) gb) ∧
    CrossB jb gb ∧ x = revRec (jb, gb))
theorem rc3_bound {m : MethodId} {x : PFact × AFact} (h : rc3 m x) : (m, x) ∈ RC3L := by
  rcases h with ⟨_, hx, hc⟩ | ⟨jb, gb, hjb, hne, hgb, hc, rfl⟩
  · exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
      (e.1, (e.2.1, e.2.2.2)) ∈ RC3L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → CrossB y.2 z.2.2.2 → (y.1, revRec (y.2, z.2.2.2)) ∈ RC3L)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hc
theorem all_normal2_crossB {m : MethodId} {j : PFact} {g : AFact}
    (h : B2 (.edge m j (Pb.exit m) g)) (hn : g.demand = false) (hj : j ≠ zeroFact) : CrossB j g :=
  (by decide : ∀ x ∈ S2.edges, x.2.2.1 = Pb.exit x.1 → x.2.2.2.demand = false →
    x.2.1 ≠ zeroFact → CrossB x.2.1 x.2.2.2) (m, j, Pb.exit m, g) (inv2 h) rfl hn hj
theorem all_normal2_persisted {m : MethodId} {j : PFact} {g : AFact}
    (hi : B2 (.init m j)) (hg : B2 (.edge m j (Pb.exit m) g)) (hn : g.demand = false)
    (hj : j ≠ zeroFact) : rc3 m (revRec (j, g)) :=
  Or.inr ⟨j, g, hi, hj, hg, all_normal2_crossB hg hn hj, rfl⟩

theorem no_source_hit : ∀ M n e, ¬ FSeeds.srcHit P B2 M n e := by
  intro M n e h
  obtain ⟨s, n', i, f, lX, l1, l', hE, he, hz, hnz, hf, _, hd, hsrc⟩ := h
  have hbase : f.fact.base = e.2.base := hd.2.1.symm.trans hsrc.2.1
  have hno := (by decide : ∀ pe ∈ P.edges, ∀ e ∈ stmtEdges pe.2.2.1,
    e.1.base = zeroBase → e.2.base ≠ zeroBase → ∀ x ∈ S2.edges,
    x.1 = pe.1 → x.2.2.1 = pe.2.2.2 → x.2.2.2.fact.base ≠ e.2.base)
    (M, n, Instr.stmt s, n') hE e he hz hnz (M, i, n', f) (inv2 hf) rfl rfl
  exact hno hbase
theorem no_source_application : ∀ M n s n' e i f,
    (M, n, Instr.stmt s, n') ∈ P.edges → e ∈ s.edges →
    e.1.base = zeroBase → e.2.base ≠ zeroBase → B2 (.edge M i n' f) →
    (applyEdge f (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts = [] := by
  intro M n s n' e i f hE he hz hnz hf
  exact (by decide : ∀ pe ∈ P.edges, ∀ e ∈ stmtEdges pe.2.2.1,
    e.1.base = zeroBase → e.2.base ≠ zeroBase → ∀ x ∈ S2.edges,
    x.1 = pe.1 → x.2.2.1 = pe.2.2.2 →
    (applyEdge x.2.2.2 (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts = [])
    (M, n, Instr.stmt s, n') hE e he hz hnz (M, i, n', f) (inv2 hf) rfl rfl

abbrev F3 : Obj → Prop := DRW P3 cnt 3 dem3 rc3 sinks [0]
theorem closed3 : ClosedRA P3 cnt 3 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P3 cnt 3 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h
theorem no_run3_sink : ∀ M n s b, ¬ F3 (.vuln M n s b) := by
  intro M n s b h
  exact List.not_mem_nil (inv3 h)
theorem dem3_exact (d : DemandEdge) : dem3 1 d ↔ d = Backward.zeroDem ∨ d = d3 := by
  constructor
  · intro h
    have hd := dem3_bound h
    simpa [demFor, D3L, Backward.zeroDem] using hd
  · rintro (rfl | rfl)
    · exact ⟨Backward.zeroDem, Or.inl rfl, rfl⟩
    · exact dem3_C
theorem default_reversal_loss : Reach P [0] 0 2 ls ∧ R1 (.vuln 0 2 sink true) ∧
    1 < 2 ∧ 2 < 3 ∧ (∀ M n e, ¬ FSeeds.srcHit P B2 M n e) ∧
    (∀ M n s b, ¬ F3 (.vuln M n s b)) :=
  ⟨concrete_sink, r1_found, by decide, by decide, no_source_hit, no_run3_sink⟩
#print axioms default_reversal_loss
#print axioms no_source_application
#print axioms dem3_exact
#print axioms all_normal2_persisted
end Strict

/-! Exact enumeration of the main 1 / 1 / 2 trace. Each listed object has a derivation. -/
theorem r1_root : R1 (.init 0 zeroFact) := D.root (by decide)
theorem r1_z00 : R1 (.edge 0 zeroFact 0 Z) := D.start r1_root
theorem r1_z01 : R1 (.edge 0 zeroFact 1 Z) :=
  D.step r1_z00 (s := src) (by simp [P]) (by decide)
theorem r1_z02 : R1 (.edge 0 zeroFact 2 Z) :=
  D.pass r1_z01 (c := callC) (by simp [P]) (by decide)
theorem r1_addZ : R1 (.added 1 zeroFact) :=
  D.added (c := callC) (e := zb) (a := Z) (n' := 2)
    r1_z01 (by simp [P]) (by decide) (by decide)
theorem r1_initZ : R1 (.init 1 zeroFact) := D.initA r1_addZ
theorem r1_z10 : R1 (.edge 1 zeroFact 0 Z) := D.start r1_initZ
theorem r1_z11 : R1 (.edge 1 zeroFact 1 Z) :=
  D.step r1_z10 (s := writeN) (by simp [P]) (by decide)
theorem r1_z12 : R1 (.edge 1 zeroFact 2 Z) :=
  D.clean r1_z11 (cl := cl) (by simp [P]) (by decide)
theorem r1_z13 : R1 (.edge 1 zeroFact 3 Z) :=
  D.step r1_z12 (s := writeF) (by simp [P]) (by decide)
theorem r1_j10 : R1 (.edge 1 Jw 0 ⟨Jw, false⟩) := D.start r1_init
theorem r1_j11 : R1 (.edge 1 Jw 1 ⟨Jw, false⟩) :=
  D.step r1_j10 (s := writeN) (by simp [P]) (by decide)
theorem r1_j12 : R1 (.edge 1 Jw 2 ⟨Jw, false⟩) :=
  D.clean r1_j11 (cl := cl) (by simp [P]) (by decide)
theorem r1_j13 : R1 (.edge 1 Jw 3 ⟨Jw, false⟩) :=
  D.step r1_j12 (s := writeF) (by simp [P]) (by decide)
theorem r1_p13 : R1 (.edge 1 Jw 3 PN) :=
  D.step r1_clean (s := writeF) (by simp [P]) (by decide)
theorem nil_all {α : Type} {Q : α → Prop} : ∀ x ∈ ([] : List α), Q x :=
  fun _ h => False.elim (List.not_mem_nil h)

theorem all1_inits : ∀ x ∈ S1.inits, R1 (.init x.1 x.2) := by
  simp only [S1, List.forall_mem_cons]
  exact ⟨r1_root, r1_initZ, r1_init, nil_all⟩
theorem all1_edges : ∀ x ∈ S1.edges, R1 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S1, List.forall_mem_cons]
  exact ⟨r1_z00, r1_z01, r1_source, r1_z02, r1_return,
    r1_z10, r1_z11, r1_z12, r1_z13, r1_j10, r1_j11, r1_written,
    r1_j12, r1_clean, r1_j13, r1_p13, r1_exit, nil_all⟩
theorem all1_addeds : ∀ x ∈ S1.addeds, R1 (.added x.1 x.2) := by
  simp only [S1, List.forall_mem_cons]
  exact ⟨r1_addZ, r1_added, nil_all⟩
theorem all1_vulns : ∀ x ∈ S1.vulns, R1 (.vuln x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S1, List.forall_mem_cons]
  exact ⟨r1_found, nil_all⟩
theorem complete1 {o : Obj} (h : S1.Inv o) : R1 o := by
  cases o with
  | init M i => exact all1_inits (M, i) h
  | edge M i n f => exact all1_edges (M, i, n, f) h
  | added M a => exact all1_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact all1_vulns (M, n, s, b) h
theorem exact1 (o : Obj) : R1 o ↔ S1.Inv o := ⟨inv1, complete1⟩

theorem b2_root : B2 (.init 0 zeroFact) := DBA.root (by decide)
theorem b2_z01 : B2 (.edge 0 zeroFact 1 Z) :=
  DBA.zpass b2_zero (c := Call.rev callC) (by simp [Pb, Program.rev, P, revE, revInstr])
theorem b2_z00 : B2 (.edge 0 zeroFact 0 Z) :=
  DBA.step b2_z01 (s := Stmt.rev src) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_initZ : B2 (.init 1 zeroFact) :=
  DBA.zin rfl b2_zero (c := Call.rev callC) (n' := 1)
    (by simp [Pb, Program.rev, P, revE, revInstr])
theorem b2_z13 : B2 (.edge 1 zeroFact 3 Z) := DBA.start b2_initZ
theorem b2_z12 : B2 (.edge 1 zeroFact 2 Z) :=
  DBA.step b2_z13 (s := Stmt.rev writeF) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z11 : B2 (.edge 1 zeroFact 1 Z) :=
  DBA.clean b2_z12 (cl := cl) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z10 : B2 (.edge 1 zeroFact 0 Z) :=
  DBA.step b2_z11 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_j13 : B2 (.edge 1 Jb 3 ⟨Jb, false⟩) := DBA.start b2_init
theorem b2_keep : B2 (.edge 1 Jb 0 PB) :=
  DBA.step b2_clean (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem all2_inits : ∀ x ∈ S2.inits, B2 (.init x.1 x.2) := by
  simp only [S2, List.forall_mem_cons]
  exact ⟨b2_root, b2_initZ, b2_init, nil_all⟩
theorem all2_edges : ∀ x ∈ S2.edges, B2 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S2, List.forall_mem_cons]
  exact ⟨b2_zero, b2_seed, b2_z01, b2_z00, b2_z13, b2_z12, b2_z11, b2_z10,
    b2_j13, b2_copy, b2_clean, b2_exit, b2_keep, nil_all⟩
theorem all2_addeds : ∀ x ∈ S2.addeds, B2 (.added x.1 x.2) := by
  simp only [S2, List.forall_mem_cons]
  exact ⟨b2_added, nil_all⟩
theorem complete2 {o : Obj} (h : S2.Inv o) : B2 o := by
  cases o with
  | init M i => exact all2_inits (M, i) h
  | edge M i n f => exact all2_edges (M, i, n, f) h
  | added M a => exact all2_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact False.elim (List.not_mem_nil h)
theorem exact2 (o : Obj) : B2 o ↔ S2.Inv o := ⟨inv2, complete2⟩

theorem dem3_zero (M : MethodId) : dem3 M Backward.zeroDem :=
  ⟨Backward.zeroDem, Or.inl rfl, rfl⟩
theorem f3_root : F3 (.init 0 zeroFact) := DRA.root (by decide)
theorem f3_z00 : F3 (.edge 0 zeroFact 0 Z) := DRA.start f3_root
theorem f3_z01 : F3 (.edge 0 zeroFact 1 Z) :=
  DRA.step f3_z00 (s := FSeeds.keepStmt (fun _ _ _ => false) 0 0 src)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z02 : F3 (.edge 0 zeroFact 2 Z) :=
  DRA.pass f3_z01 (c := callC)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_addZ : F3 (.added 1 zeroFact) :=
  DRA.added (c := callC) (e := zb) (a := Z) (n' := 2) f3_z01
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide) (by decide)
theorem f3_initZ : F3 (.init 1 zeroFact) :=
  DRA.initR (d := Backward.zeroDem) f3_addZ (dem3_zero 1) (by decide)
theorem f3_z10 : F3 (.edge 1 zeroFact 0 Z) := DRA.start f3_initZ
theorem f3_z11 : F3 (.edge 1 zeroFact 1 Z) :=
  DRA.step f3_z10 (s := FSeeds.keepStmt (fun _ _ _ => false) 1 0 writeN)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z12 : F3 (.edge 1 zeroFact 2 Z) :=
  DRA.clean f3_z11 (cl := cl)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z13 : F3 (.edge 1 zeroFact 3 Z) :=
  DRA.step f3_z12 (s := FSeeds.keepStmt (fun _ _ _ => false) 1 2 writeF)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem all3_inits : ∀ x ∈ S3.inits, F3 (.init x.1 x.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_root, f3_initZ, nil_all⟩
theorem all3_edges : ∀ x ∈ S3.edges, F3 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_z00, f3_z01, f3_z02, f3_z10, f3_z11, f3_z12, f3_z13, nil_all⟩
theorem all3_addeds : ∀ x ∈ S3.addeds, F3 (.added x.1 x.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_addZ, nil_all⟩
theorem complete3 {o : Obj} (h : S3.Inv o) : F3 o := by
  cases o with
  | init M i => exact all3_inits (M, i) h
  | edge M i n f => exact all3_edges (M, i, n, f) h
  | added M a => exact all3_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact False.elim (List.not_mem_nil h)
theorem exact3 (o : Obj) : F3 o ↔ S3.Inv o := ⟨inv3, complete3⟩

theorem all_records1 : ∀ x ∈ RB1L, recsB1 x.1 x.2 := by
  simp only [RB1L, List.forall_mem_cons]
  exact ⟨(all_normal1_persisted r1_root r1_z02 rfl).1,
    (all_normal1_persisted r1_initZ r1_z13 rfl).1,
    (all_normal1_persisted r1_init r1_j13 rfl).1,
    (all_normal1_persisted r1_init r1_p13 rfl).1, nil_all⟩
theorem records1_exact (m : MethodId) (x : PFact × AFact) :
    recsB1 m x ↔ (m, x) ∈ RB1L := ⟨recs1_bound, fun h => all_records1 (m, x) h⟩
theorem all_records3 : ∀ x ∈ RC3L, rc3 x.1 x.2 := by
  simp only [RC3L, List.forall_mem_cons]
  exact ⟨(all_normal1_persisted r1_root r1_z02 rfl).2,
    (all_normal1_persisted r1_initZ r1_z13 rfl).2,
    (all_normal1_persisted r1_init r1_j13 rfl).2,
    (all_normal1_persisted r1_init r1_p13 rfl).2,
    all_normal2_persisted b2_init b2_keep rfl (by decide), nil_all⟩
theorem records3_exact (m : MethodId) (x : PFact × AFact) :
    rc3 m x ↔ (m, x) ∈ RC3L := ⟨rc3_bound, fun h => all_records3 (m, x) h⟩

/-- The complete backward publication in the finite AP model. Raw local exit PB is
    persisted before restriction, but only JB → GB is published through these demands. -/
theorem published2_exact (m : MethodId) (j : PFact) (g g' : AFact) :
    (B2 (.init m j) ∧ B2 (.edge m j (Pb.exit m) g) ∧
      pubR (handFA P R1 pubD) m j g g') ↔ m = 1 ∧ j = Jb ∧ g = GB ∧ g' = GB := by
  constructor
  · rintro ⟨_, hg, d, hd, hr⟩
    exact (by decide : ∀ x ∈ S2.edges, x.2.2.1 = Pb.exit x.1 → ∀ dd ∈ H1L,
      dd.1 = x.1 → ∀ g' ∈ (restrictI x.2.1 x.2.2.2 dd.2).toList,
      x.1 = 1 ∧ x.2.1 = Jb ∧ x.2.2.2 = GB ∧ g' = GB)
      (m, j, Pb.exit m, g) (inv2 hg) rfl (m, d) (hand1_bound hd) rfl g'
      (RCases.mem_toList_of_eq_some hr)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨b2_init, b2_exit, dC, hand1_C, by decide⟩

theorem demand3_all_exact (m : MethodId) (d : DemandEdge) :
    dem3 m d ↔ d = Backward.zeroDem ∨ (m = 1 ∧ d = d3) := by
  constructor
  · intro h
    by_cases hm : m = 1
    · subst hm
      rcases (dem3_exact d).mp h with hz | hd
      · exact Or.inl hz
      · exact Or.inr ⟨rfl, hd⟩
    · have hd := dem3_bound h
      by_cases hm0 : m = 0
      · subst hm0
        exact Or.inl (by simpa [demFor, D3L, Backward.zeroDem] using hd)
      · exact Or.inl (by
          simpa [demFor, D3L, Backward.zeroDem, hm, hm0, Ne.symm hm, Ne.symm hm0] using hd)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact dem3_zero m
    · exact dem3_C

theorem hand3_empty : ∀ m d, ¬ handFA P3 F3 (pubR dem3) m d := by
  intro m d h
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, _, _⟩, _⟩ := h
  exact hnc ((by decide : ∀ x ∈ S3.edges, x.2.2.1 = P3.exit x.1 → Cross x.2.1 x.2.2.2)
    (m, j, P3.exit m, g) (inv3 hg) rfl)

/-! Exact enumeration of the 1 / 2 / 3 trace. -/
namespace Strict
theorem b2_root : B2 (.init 0 zeroFact) := DBA.root (by decide)
theorem b2_z01 : B2 (.edge 0 zeroFact 1 Z) :=
  DBA.zpass b2_zero (c := Call.rev callC) (by simp [Pb, Program.rev, P, revE, revInstr])
theorem b2_z00 : B2 (.edge 0 zeroFact 0 Z) :=
  DBA.step b2_z01 (s := Stmt.rev src) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_initZ : B2 (.init 1 zeroFact) :=
  DBA.zin rfl b2_zero (c := Call.rev callC) (n' := 1)
    (by simp [Pb, Program.rev, P, revE, revInstr])
theorem b2_z13 : B2 (.edge 1 zeroFact 3 Z) := DBA.start b2_initZ
theorem b2_z12 : B2 (.edge 1 zeroFact 2 Z) :=
  DBA.step b2_z13 (s := Stmt.rev writeF) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z11 : B2 (.edge 1 zeroFact 1 Z) :=
  DBA.clean b2_z12 (cl := cl) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z10 : B2 (.edge 1 zeroFact 0 Z) :=
  DBA.step b2_z11 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_j13 : B2 (.edge 1 Jb 3 ⟨Jb, false⟩) := DBA.start b2_init
theorem b2_keep : B2 (.edge 1 Jb 0 PB) :=
  DBA.step b2_clean (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem all2_inits : ∀ x ∈ S2.inits, B2 (.init x.1 x.2) := by
  simp only [S2, ReviewReversal.S2, List.forall_mem_cons]
  exact ⟨b2_root, b2_initZ, b2_init, nil_all⟩
theorem all2_edges : ∀ x ∈ S2.edges, B2 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S2, ReviewReversal.S2, List.drop, List.cons_append, List.nil_append, List.forall_mem_cons]
  exact ⟨b2_zero, b2_seed, b2_z01, b2_z00, b2_z13, b2_z12, b2_z11, b2_z10,
    b2_j13, b2_copy, b2_clean, b2_exit, b2_keep, nil_all⟩
theorem all2_addeds : ∀ x ∈ S2.addeds, B2 (.added x.1 x.2) := by
  simp only [S2, List.forall_mem_cons]
  exact ⟨b2_added, nil_all⟩
theorem complete2 {o : Obj} (h : S2.Inv o) : B2 o := by
  cases o with
  | init M i => exact all2_inits (M, i) h
  | edge M i n f => exact all2_edges (M, i, n, f) h
  | added M a => exact all2_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact False.elim (List.not_mem_nil h)
theorem exact2 (o : Obj) : B2 o ↔ S2.Inv o := ⟨inv2, complete2⟩

theorem dem3_zero (M : MethodId) : dem3 M Backward.zeroDem :=
  ⟨Backward.zeroDem, Or.inl rfl, rfl⟩
theorem f3_root : F3 (.init 0 zeroFact) := DRA.root (by decide)
theorem f3_z00 : F3 (.edge 0 zeroFact 0 Z) := DRA.start f3_root
theorem f3_z01 : F3 (.edge 0 zeroFact 1 Z) :=
  DRA.step f3_z00 (s := FSeeds.keepStmt (fun _ _ _ => false) 0 0 src)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z02 : F3 (.edge 0 zeroFact 2 Z) :=
  DRA.pass f3_z01 (c := callC)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_addZ : F3 (.added 1 zeroFact) :=
  DRA.added (c := callC) (e := zb) (a := Z) (n' := 2) f3_z01
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide) (by decide)
theorem f3_initZ : F3 (.init 1 zeroFact) :=
  DRA.initR (d := Backward.zeroDem) f3_addZ (dem3_zero 1) (by decide)
theorem f3_z10 : F3 (.edge 1 zeroFact 0 Z) := DRA.start f3_initZ
theorem f3_z11 : F3 (.edge 1 zeroFact 1 Z) :=
  DRA.step f3_z10 (s := FSeeds.keepStmt (fun _ _ _ => false) 1 0 writeN)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z12 : F3 (.edge 1 zeroFact 2 Z) :=
  DRA.clean f3_z11 (cl := cl)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem f3_z13 : F3 (.edge 1 zeroFact 3 Z) :=
  DRA.step f3_z12 (s := FSeeds.keepStmt (fun _ _ _ => false) 1 2 writeF)
    (by simp [P3, FSeeds.keepSources, P, FSeeds.keepE, FSeeds.keepInstr]) (by decide)
theorem all3_inits : ∀ x ∈ S3.inits, F3 (.init x.1 x.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_root, f3_initZ, nil_all⟩
theorem all3_edges : ∀ x ∈ S3.edges, F3 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_z00, f3_z01, f3_z02, f3_z10, f3_z11, f3_z12, f3_z13, nil_all⟩
theorem all3_addeds : ∀ x ∈ S3.addeds, F3 (.added x.1 x.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_addZ, nil_all⟩
theorem complete3 {o : Obj} (h : S3.Inv o) : F3 o := by
  cases o with
  | init M i => exact all3_inits (M, i) h
  | edge M i n f => exact all3_edges (M, i, n, f) h
  | added M a => exact all3_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact False.elim (List.not_mem_nil h)
theorem exact3 (o : Obj) : F3 o ↔ S3.Inv o := ⟨inv3, complete3⟩

theorem old_normal_record {m : MethodId} {j : PFact} {g : AFact}
    (hi : R1 (.init m j)) (hg : R1 (.edge m j (P.exit m) g)) (hn : g.demand = false) :
    rc3 m (j, g) := Or.inl ⟨hi, hg, all_normal1_cross hg hn⟩
theorem all_records3 : ∀ x ∈ RC3L, rc3 x.1 x.2 := by
  simp only [RC3L, List.forall_mem_cons]
  exact ⟨old_normal_record r1_root r1_z02 rfl,
    old_normal_record r1_initZ r1_z13 rfl,
    old_normal_record r1_init r1_j13 rfl,
    old_normal_record r1_init r1_p13 rfl,
    all_normal2_persisted b2_init b2_keep rfl (by decide), nil_all⟩
theorem records3_exact (m : MethodId) (x : PFact × AFact) :
    rc3 m x ↔ (m, x) ∈ RC3L := ⟨rc3_bound, fun h => all_records3 (m, x) h⟩
theorem published2_exact (m : MethodId) (j : PFact) (g g' : AFact) :
    (B2 (.init m j) ∧ B2 (.edge m j (Pb.exit m) g) ∧
      pubR (handFA P R1 pubD) m j g g') ↔ m = 1 ∧ j = Jb ∧ g = GB ∧ g' = GB := by
  constructor
  · rintro ⟨_, hg, d, hd, hr⟩
    exact (by decide : ∀ x ∈ S2.edges, x.2.2.1 = Pb.exit x.1 → ∀ dd ∈ H1L,
      dd.1 = x.1 → ∀ g' ∈ (restrictI x.2.1 x.2.2.2 dd.2).toList,
      x.1 = 1 ∧ x.2.1 = Jb ∧ x.2.2.2 = GB ∧ g' = GB)
      (m, j, Pb.exit m, g) (inv2 hg) rfl (m, d) (hand1_bound hd) rfl g'
      (RCases.mem_toList_of_eq_some hr)
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨b2_init, b2_exit, dC, hand1_C, by decide⟩
theorem demand3_all_exact (m : MethodId) (d : DemandEdge) :
    dem3 m d ↔ d = Backward.zeroDem ∨ (m = 1 ∧ d = d3) := by
  constructor
  · intro h
    by_cases hm : m = 1
    · subst hm
      rcases (dem3_exact d).mp h with hz | hd
      · exact Or.inl hz
      · exact Or.inr ⟨rfl, hd⟩
    · have hd := dem3_bound h
      by_cases hm0 : m = 0
      · subst hm0
        exact Or.inl (by simpa [demFor, D3L, Backward.zeroDem] using hd)
      · exact Or.inl (by
          simpa [demFor, D3L, Backward.zeroDem, hm, hm0, Ne.symm hm, Ne.symm hm0] using hd)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact dem3_zero m
    · exact dem3_C
theorem hand3_empty : ∀ m d, ¬ handFA P3 F3 (pubR dem3) m d := by
  intro m d h
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, _, _⟩, _⟩ := h
  exact hnc ((by decide : ∀ x ∈ S3.edges, x.2.2.1 = P3.exit x.1 → Cross x.2.1 x.2.2.2)
    (m, j, P3.exit m, g) (inv3 hg) rfl)
#print axioms exact2
#print axioms exact3
#print axioms records3_exact
#print axioms published2_exact
#print axioms demand3_all_exact
#print axioms hand3_empty
end Strict

#print axioms exact1
#print axioms exact2
#print axioms exact3
#print axioms records1_exact
#print axioms records3_exact
#print axioms published2_exact
#print axioms demand3_all_exact
#print axioms hand3_empty

#print axioms closed1
#print axioms closed2
#print axioms closed3
#print axioms r1_found
#print axioms hand1_C
#print axioms run1_disjoint_no_request
#print axioms backward_loss
#print axioms dem3_C
#print axioms no_source_hit
#print axioms no_run3_sink
#print axioms concrete_sink
#print axioms no_source_application
#print axioms hand1_exact
#print axioms dem3_exact
#print axioms default_reversal_loss
#print axioms no_confirmed_run1
#print axioms all_normal1_cross
#print axioms all_normal2_crossB
#print axioms all_normal1_persisted
#print axioms all_normal2_persisted
#print axioms wf_program
#print axioms wf_marks
#print axioms rev_stmts
#print axioms mark_rev_stmts
#print axioms rev_calls
#print axioms binding_targets_star
#print axioms no_zero_back
#print axioms zero_kept

end ApSpec.ReviewReversal
