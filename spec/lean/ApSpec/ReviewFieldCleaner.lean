/-
  The user's field-cleaner lowering (read, clean temporary, strong write), with limits 1/2/3.
  ReviewReversal keeps the separate atomic-field-cleaner counterexample.
-/
import ApSpec.ReviewReversal

namespace ApSpec.ReviewFieldCleaner
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs ApSpec.ReviewReversal
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- `tmp = p.g`; p stays unchanged. Bases p=4,tmp=6; fields n=4,g=5,f=6. -/
def readG : Stmt := ⟨[4, 6], [id 4,
  (⟨4, [5], st, .star⟩, ⟨6, [], st, .star⟩)]⟩
/-- The cleaner applies to the whole temporary, not directly to p.g. -/
def cleanTmp : Cleaner := ⟨6, [], .atAndBelow, some 1⟩
/-- `p.g = tmp`, with the strong-write keep row and unchanged temporary. -/
def writeG : Stmt := ⟨[4, 6], [
  (⟨4, [], .star (.set [5]), .star⟩, ⟨4, [], .star (.set [5]), .star⟩), id 6,
  (⟨6, [], st, .star⟩, ⟨4, [5], st, .star⟩)]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 1 then 5 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callC, 2), (1, 0, .stmt writeN, 1),
   (1, 1, .stmt readG, 2), (1, 2, .clean cleanTmp, 3),
   (1, 3, .stmt writeG, 4), (1, 4, .stmt writeF, 5)]⟩
abbrev Pb : Program := Program.rev P
def zEdges (m : MethodId) (ns : List Node) : List EdgeT := ns.map (fun n => (m, zeroFact, n, Z))
def jEdges (j : PFact) (ns : List Node) : List EdgeT := ns.map (fun n => (1, j, n, ⟨j, false⟩))
def pEdges (j : PFact) (ns : List Node) : List EdgeT := ns.map (fun n => (1, j, n, PN))

def S1 : LS where
  inits := ReviewReversal.S1.inits
  edges := [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X1),
    (0, zeroFact, 2, Z), (0, zeroFact, 2, R1out)] ++
    zEdges 1 [0, 1, 2, 3, 4, 5] ++ jEdges Jw [0, 1, 2, 3, 4, 5] ++ pEdges Jw [1, 2, 3, 4, 5] ++
    [(1, Jw, 5, GF)]
  addeds := ReviewReversal.S1.addeds
  reqs := []
  vulns := [(0, 2, sink, true)]
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
theorem recs1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

def Rq : PFact := ⟨5, [6, 4], .exact, .conc 1⟩
def PGkeep : AFact := ⟨⟨4, [], .star (.set [5, 5]), .star⟩, false⟩
def Tmp : AFact := ⟨⟨6, [], .any, .star⟩, true⟩
def TmpClean : AFact := ⟨⟨6, [], .any, .starEx [1]⟩, true⟩
def PG : AFact := ⟨⟨4, [5], .any, .starEx [1]⟩, true⟩
def GB : AFact := ⟨⟨3, [], .any, .star⟩, true⟩
def PB : AFact := ⟨⟨4, [], .star (.set [5, 5, 4, 4]), .star⟩, false⟩
def XB : AFact := ⟨⟨1, [], .any, .conc 1⟩, true⟩
def ZD : AFact := ⟨zeroFact, true⟩
def S2 : LS where
  inits := [(0, zeroFact), (1, zeroFact), (1, Jb)]
  edges := [(0, zeroFact, 2, Z), (0, zeroFact, 2, ⟨sink, false⟩),
    (0, zeroFact, 1, Z), (0, zeroFact, 1, XB),
    (0, zeroFact, 0, Z), (0, zeroFact, 0, ZD), (0, zeroFact, 0, XB)] ++
    zEdges 1 [5, 4, 3, 2, 1, 0] ++
    [(1, Jb, 5, ⟨Jb, false⟩), (1, Jb, 4, PW),
     (1, Jb, 3, PGkeep), (1, Jb, 3, Tmp), (1, Jb, 2, PGkeep), (1, Jb, 2, TmpClean),
     (1, Jb, 1, PGkeep), (1, Jb, 1, PG), (1, Jb, 0, GB), (1, Jb, 0, PB), (1, Jb, 0, PG)]
  addeds := [(1, Rq)]
  reqs := []
  vulns := []
abbrev B2 : Obj → Prop := DBW Pb cnt 2 (handFA P R1 pubD) recsB1 [0] sinks
theorem closed2 : ClosedBA Pb cnt 2 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 2 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (hand1_bound hd)) (fun _ _ hx => recs1_bound hx) h

theorem r1_source : R1 (.edge 0 zeroFact 1 X1) :=
  D.step (D.start (D.root (by decide))) (s := src) (by simp [P]) (by decide)
theorem r1_added : R1 (.added 1 A1) :=
  D.added (c := callC) (e := bx) (a := ⟨A1, false⟩) (n' := 2)
    r1_source (by simp [P]) (by decide) (by decide)
theorem r1_init : R1 (.init 1 Jw) := D.initA r1_added
theorem r1_p1 : R1 (.edge 1 Jw 1 PN) :=
  D.step (D.start r1_init) (s := writeN) (by simp [P]) (by decide)
theorem r1_p2 : R1 (.edge 1 Jw 2 PN) :=
  D.step r1_p1 (s := readG) (by simp [P]) (by decide)
theorem r1_p3 : R1 (.edge 1 Jw 3 PN) :=
  D.clean r1_p2 (cl := cleanTmp) (by simp [P]) (by decide)
theorem r1_p4 : R1 (.edge 1 Jw 4 PN) :=
  D.step r1_p3 (s := writeG) (by simp [P]) (by decide)
theorem r1_exit : R1 (.edge 1 Jw 5 GF) :=
  D.step r1_p4 (s := writeF) (by simp [P]) (by decide)
theorem hand1_C : handFA P R1 pubD 1 dC :=
  ⟨_, ⟨Jw, GF, GF, r1_init, r1_exit, by decide, rfl, rfl⟩, rfl⟩
theorem r1_return : R1 (.edge 0 zeroFact 2 R1out) :=
  D.ret (c := callC) (e1 := bx) (a := ⟨A1, false⟩) (j := Jw) (g := GF)
    (r := ⟨⟨5, [6], .any, .conc 1⟩, true⟩) (e2 := br) (r' := R1out)
    r1_source (by simp [P]) (by decide) (by decide) r1_init (by decide) r1_exit
    (by decide) (by decide) (by decide)
theorem r1_found : R1 (.vuln 0 2 sink true) := D.vuln r1_return (by decide) (by decide)
theorem b2_zero : B2 (.edge 0 zeroFact 2 Z) := DBA.start (DBA.root (by decide))
theorem b2_seed : B2 (.edge 0 zeroFact 2 ⟨sink, false⟩) := DBA.seed (s := sink) (by decide) b2_zero
theorem b2_added : B2 (.added 1 Rq) :=
  DBA.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨Rq, false⟩)
    (n' := 1) b2_seed (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide) (by decide)
theorem b2_init : B2 (.init 1 Jb) := DBA.initR (d := dC) b2_added hand1_C (by decide)
theorem b2_copy : B2 (.edge 1 Jb 4 PW) :=
  DBA.step (DBA.start b2_init) (s := Stmt.rev writeF)
    (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_keep3 : B2 (.edge 1 Jb 3 PGkeep) :=
  DBA.step b2_copy (s := Stmt.rev writeG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_tmp3 : B2 (.edge 1 Jb 3 Tmp) :=
  DBA.step b2_copy (s := Stmt.rev writeG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_keep2 : B2 (.edge 1 Jb 2 PGkeep) :=
  DBA.clean b2_keep3 (cl := cleanTmp) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_tmp2 : B2 (.edge 1 Jb 2 TmpClean) :=
  DBA.clean b2_tmp3 (cl := cleanTmp) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_keep1 : B2 (.edge 1 Jb 1 PGkeep) :=
  DBA.step b2_keep2 (s := Stmt.rev readG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_g1 : B2 (.edge 1 Jb 1 PG) :=
  DBA.step b2_tmp2 (s := Stmt.rev readG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_exit : B2 (.edge 1 Jb 0 GB) :=
  DBA.step b2_keep1 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_keep0 : B2 (.edge 1 Jb 0 PB) :=
  DBA.step b2_keep1 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_g0 : B2 (.edge 1 Jb 0 PG) :=
  DBA.step b2_g1 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)

def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))
def d3 : DemandEdge := normDem ⟨GB.fact, some Jb⟩
theorem dem3_C : dem3 1 d3 :=
  ⟨_, Or.inr (Or.inr ⟨Jb, GB, GB, b2_init, by decide, b2_exit, by decide,
    ⟨dC, hand1_C, by decide⟩, rfl⟩), rfl⟩
theorem b2_return : B2 (.edge 0 zeroFact 1 XB) :=
  DBA.ret (c := Call.rev callC) (e1 := revEdge br.1 br.2) (a := ⟨Rq, false⟩) (j := Jb)
    (g := GB) (d := dC) (g' := GB) (r := ⟨⟨3, [], .any, .conc 1⟩, true⟩)
    (e2 := revEdge bx.1 bx.2) (r' := XB) b2_seed
    (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide) (by decide)
    b2_init b2_exit hand1_C (by decide) (by decide) (by decide) (by decide) (by decide)
def sourceE : MicroEdge := (zeroFact, ⟨1, [], .exact, .conc 1⟩)
theorem source_hit : FSeeds.srcHit P B2 0 0 sourceE :=
  ⟨src, 1, zeroFact, XB, zeroLoc, zeroLoc, lx, by simp [P], by decide, rfl, by decide,
    b2_return, ⟨1, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial⟩, source_den⟩
theorem hits_exact (M : MethodId) (n : Node) (e : MicroEdge) :
    FSeeds.srcHit P B2 M n e ↔ M = 0 ∧ n = 0 ∧ e = sourceE := by
  constructor
  · rintro ⟨s, n', i, f, lX, l1, l', hE, he, hz, hnz, _⟩
    exact (by decide : ∀ pe ∈ P.edges, ∀ e ∈ stmtEdges pe.2.2.1,
      e.1.base = zeroBase → e.2.base ≠ zeroBase → pe.1 = 0 ∧ pe.2.1 = 0 ∧ e = sourceE)
      (M, n, .stmt s, n') hE e he hz hnz
  · rintro ⟨rfl, rfl, rfl⟩
    exact source_hit

def D3L : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, none⟩), (1, ⟨zeroFact, none⟩), (0, ⟨XB.fact, none⟩), (1, d3)]
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

/-- The seed mask is exactly the actual backward source-hit set. -/
def seeds (M : MethodId) (n : Node) (e : MicroEdge) : Bool :=
  Nat.beq M 0 && Nat.beq n 0 && decide (e = sourceE)
theorem seeds_exact (M : MethodId) (n : Node) (e : MicroEdge) :
    seeds M n e = true ↔ FSeeds.srcHit P B2 M n e := by simp [seeds, hits_exact, and_assoc]
def P3 : Program := FSeeds.keepSources P seeds
theorem kept : P3 = P := rfl
def G3 : AFact := ⟨⟨5, [6, 4], st, .star⟩, false⟩
def R3out : AFact := ⟨sink, false⟩
def S3 : LS where
  inits := ReviewReversal.S1.inits
  edges := [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X1),
    (0, zeroFact, 2, Z), (0, zeroFact, 2, R3out)] ++
    zEdges 1 [0, 1, 2, 3, 4, 5] ++ jEdges Jw [0, 1, 2, 3, 4, 5] ++ pEdges Jw [1, 2, 3, 4, 5] ++
    [(1, Jw, 5, G3)]
  addeds := ReviewReversal.S1.addeds
  reqs := []
  vulns := [(0, 2, sink, false)]
abbrev F3 : Obj → Prop := DRW P3 cnt 3 dem3 rc3 sinks [0]
theorem closed3 : ClosedRA P3 cnt 3 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P3 cnt 3 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h
theorem f3_source : F3 (.edge 0 zeroFact 1 X1) :=
  DRA.step (DRA.start (DRA.root (by decide))) (s := src) (by rw [kept]; simp [P]) (by decide)
theorem f3_added : F3 (.added 1 A1) :=
  DRA.added (c := callC) (e := bx) (a := ⟨A1, false⟩) (n' := 2)
    f3_source (by rw [kept]; simp [P]) (by decide) (by decide)
theorem f3_init : F3 (.init 1 Jw) := DRA.initR (d := d3) f3_added dem3_C (by decide)
theorem f3_p1 : F3 (.edge 1 Jw 1 PN) :=
  DRA.step (DRA.start f3_init) (s := writeN) (by rw [kept]; simp [P]) (by decide)
theorem f3_p2 : F3 (.edge 1 Jw 2 PN) :=
  DRA.step f3_p1 (s := readG) (by rw [kept]; simp [P]) (by decide)
theorem f3_p3 : F3 (.edge 1 Jw 3 PN) :=
  DRA.clean f3_p2 (cl := cleanTmp) (by rw [kept]; simp [P]) (by decide)
theorem f3_p4 : F3 (.edge 1 Jw 4 PN) :=
  DRA.step f3_p3 (s := writeG) (by rw [kept]; simp [P]) (by decide)
theorem f3_exit : F3 (.edge 1 Jw 5 G3) :=
  DRA.step f3_p4 (s := writeF) (by rw [kept]; simp [P]) (by decide)
theorem f3_return : F3 (.edge 0 zeroFact 2 R3out) :=
  DRA.ret (c := callC) (e1 := bx) (a := ⟨A1, false⟩) (j := Jw) (g := G3) (d := d3) (g' := G3)
    (r := ⟨⟨5, [6, 4], .exact, .conc 1⟩, false⟩) (e2 := br) (r' := R3out)
    f3_source (by rw [kept]; simp [P]) (by decide) (by decide)
    f3_init f3_exit dem3_C (by decide) (by decide) (by decide) (by decide) (by decide)
/-- A normal-layer sink report. Full analyzer Support confirmation is not claimed here. -/
theorem f3_normal_report : F3 (.vuln 0 2 sink false) := DRA.vuln f3_return (by decide) (by decide)
theorem lowered_pipeline_preserves : R1 (.vuln 0 2 sink true) ∧
    FSeeds.srcHit P B2 0 0 sourceE ∧ F3 (.vuln 0 2 sink false) :=
  ⟨r1_found, source_hit, f3_normal_report⟩

/-! Exact tables for the corrected lowered program at limits 1 / 2 / 3.
    Closedness bounds each least closure; the derivations below certify every listed object. -/
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
  D.step r1_z11 (s := readG) (by simp [P]) (by decide)
theorem r1_z13 : R1 (.edge 1 zeroFact 3 Z) :=
  D.clean r1_z12 (cl := cleanTmp) (by simp [P]) (by decide)
theorem r1_z14 : R1 (.edge 1 zeroFact 4 Z) :=
  D.step r1_z13 (s := writeG) (by simp [P]) (by decide)
theorem r1_z15 : R1 (.edge 1 zeroFact 5 Z) :=
  D.step r1_z14 (s := writeF) (by simp [P]) (by decide)
theorem r1_j10 : R1 (.edge 1 Jw 0 ⟨Jw, false⟩) := D.start r1_init
theorem r1_j11 : R1 (.edge 1 Jw 1 ⟨Jw, false⟩) :=
  D.step r1_j10 (s := writeN) (by simp [P]) (by decide)
theorem r1_j12 : R1 (.edge 1 Jw 2 ⟨Jw, false⟩) :=
  D.step r1_j11 (s := readG) (by simp [P]) (by decide)
theorem r1_j13 : R1 (.edge 1 Jw 3 ⟨Jw, false⟩) :=
  D.clean r1_j12 (cl := cleanTmp) (by simp [P]) (by decide)
theorem r1_j14 : R1 (.edge 1 Jw 4 ⟨Jw, false⟩) :=
  D.step r1_j13 (s := writeG) (by simp [P]) (by decide)
theorem r1_j15 : R1 (.edge 1 Jw 5 ⟨Jw, false⟩) :=
  D.step r1_j14 (s := writeF) (by simp [P]) (by decide)
theorem r1_p5 : R1 (.edge 1 Jw 5 PN) :=
  D.step r1_p4 (s := writeF) (by simp [P]) (by decide)

theorem all1_inits : ∀ x ∈ S1.inits, R1 (.init x.1 x.2) := by
  simp only [S1, ReviewReversal.S1, List.forall_mem_cons]
  exact ⟨r1_root, r1_initZ, r1_init, nil_all⟩
theorem all1_edges : ∀ x ∈ S1.edges, R1 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S1, zEdges, jEdges, pEdges, List.map, List.cons_append, List.nil_append,
    List.forall_mem_cons]
  exact ⟨r1_z00, r1_z01, r1_source, r1_z02, r1_return,
    r1_z10, r1_z11, r1_z12, r1_z13, r1_z14, r1_z15,
    r1_j10, r1_j11, r1_j12, r1_j13, r1_j14, r1_j15,
    r1_p1, r1_p2, r1_p3, r1_p4, r1_p5, r1_exit, nil_all⟩
theorem all1_addeds : ∀ x ∈ S1.addeds, R1 (.added x.1 x.2) := by
  simp only [S1, ReviewReversal.S1, List.forall_mem_cons]
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
theorem b2_source0 : B2 (.edge 0 zeroFact 0 ZD) :=
  DBA.step b2_return (s := Stmt.rev src) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_x00 : B2 (.edge 0 zeroFact 0 XB) :=
  DBA.step b2_return (s := Stmt.rev src) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_initZ : B2 (.init 1 zeroFact) :=
  DBA.zin rfl b2_zero (c := Call.rev callC) (n' := 1)
    (by simp [Pb, Program.rev, P, revE, revInstr])
theorem b2_z15 : B2 (.edge 1 zeroFact 5 Z) := DBA.start b2_initZ
theorem b2_z14 : B2 (.edge 1 zeroFact 4 Z) :=
  DBA.step b2_z15 (s := Stmt.rev writeF) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z13 : B2 (.edge 1 zeroFact 3 Z) :=
  DBA.step b2_z14 (s := Stmt.rev writeG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z12 : B2 (.edge 1 zeroFact 2 Z) :=
  DBA.clean b2_z13 (cl := cleanTmp) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z11 : B2 (.edge 1 zeroFact 1 Z) :=
  DBA.step b2_z12 (s := Stmt.rev readG) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_z10 : B2 (.edge 1 zeroFact 0 Z) :=
  DBA.step b2_z11 (s := Stmt.rev writeN) (by simp [Pb, Program.rev, P, revE, revInstr]) (by decide)
theorem b2_j15 : B2 (.edge 1 Jb 5 ⟨Jb, false⟩) := DBA.start b2_init

theorem all2_inits : ∀ x ∈ S2.inits, B2 (.init x.1 x.2) := by
  simp only [S2, List.forall_mem_cons]
  exact ⟨b2_root, b2_initZ, b2_init, nil_all⟩
theorem all2_edges : ∀ x ∈ S2.edges, B2 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S2, zEdges, List.map, List.cons_append, List.nil_append, List.forall_mem_cons]
  exact ⟨b2_zero, b2_seed, b2_z01, b2_return, b2_z00, b2_source0, b2_x00,
    b2_z15, b2_z14, b2_z13, b2_z12, b2_z11, b2_z10,
    b2_j15, b2_copy, b2_keep3, b2_tmp3, b2_keep2, b2_tmp2,
    b2_keep1, b2_g1, b2_exit, b2_keep0, b2_g0, nil_all⟩
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
  DRA.step f3_z00 (s := src) (by rw [kept]; simp [P]) (by decide)
theorem f3_z02 : F3 (.edge 0 zeroFact 2 Z) :=
  DRA.pass f3_z01 (c := callC) (by rw [kept]; simp [P]) (by decide)
theorem f3_addZ : F3 (.added 1 zeroFact) :=
  DRA.added (c := callC) (e := zb) (a := Z) (n' := 2)
    f3_z01 (by rw [kept]; simp [P]) (by decide) (by decide)
theorem f3_initZ : F3 (.init 1 zeroFact) :=
  DRA.initR (d := Backward.zeroDem) f3_addZ (dem3_zero 1) (by decide)
theorem f3_z10 : F3 (.edge 1 zeroFact 0 Z) := DRA.start f3_initZ
theorem f3_z11 : F3 (.edge 1 zeroFact 1 Z) :=
  DRA.step f3_z10 (s := writeN) (by rw [kept]; simp [P]) (by decide)
theorem f3_z12 : F3 (.edge 1 zeroFact 2 Z) :=
  DRA.step f3_z11 (s := readG) (by rw [kept]; simp [P]) (by decide)
theorem f3_z13 : F3 (.edge 1 zeroFact 3 Z) :=
  DRA.clean f3_z12 (cl := cleanTmp) (by rw [kept]; simp [P]) (by decide)
theorem f3_z14 : F3 (.edge 1 zeroFact 4 Z) :=
  DRA.step f3_z13 (s := writeG) (by rw [kept]; simp [P]) (by decide)
theorem f3_z15 : F3 (.edge 1 zeroFact 5 Z) :=
  DRA.step f3_z14 (s := writeF) (by rw [kept]; simp [P]) (by decide)
theorem f3_j10 : F3 (.edge 1 Jw 0 ⟨Jw, false⟩) := DRA.start f3_init
theorem f3_j11 : F3 (.edge 1 Jw 1 ⟨Jw, false⟩) :=
  DRA.step f3_j10 (s := writeN) (by rw [kept]; simp [P]) (by decide)
theorem f3_j12 : F3 (.edge 1 Jw 2 ⟨Jw, false⟩) :=
  DRA.step f3_j11 (s := readG) (by rw [kept]; simp [P]) (by decide)
theorem f3_j13 : F3 (.edge 1 Jw 3 ⟨Jw, false⟩) :=
  DRA.clean f3_j12 (cl := cleanTmp) (by rw [kept]; simp [P]) (by decide)
theorem f3_j14 : F3 (.edge 1 Jw 4 ⟨Jw, false⟩) :=
  DRA.step f3_j13 (s := writeG) (by rw [kept]; simp [P]) (by decide)
theorem f3_j15 : F3 (.edge 1 Jw 5 ⟨Jw, false⟩) :=
  DRA.step f3_j14 (s := writeF) (by rw [kept]; simp [P]) (by decide)
theorem f3_p5 : F3 (.edge 1 Jw 5 PN) :=
  DRA.step f3_p4 (s := writeF) (by rw [kept]; simp [P]) (by decide)

theorem all3_inits : ∀ x ∈ S3.inits, F3 (.init x.1 x.2) := by
  simp only [S3, ReviewReversal.S1, List.forall_mem_cons]
  exact ⟨f3_root, f3_initZ, f3_init, nil_all⟩
theorem all3_edges : ∀ x ∈ S3.edges, F3 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S3, zEdges, jEdges, pEdges, List.map, List.cons_append, List.nil_append,
    List.forall_mem_cons]
  exact ⟨f3_z00, f3_z01, f3_source, f3_z02, f3_return,
    f3_z10, f3_z11, f3_z12, f3_z13, f3_z14, f3_z15,
    f3_j10, f3_j11, f3_j12, f3_j13, f3_j14, f3_j15,
    f3_p1, f3_p2, f3_p3, f3_p4, f3_p5, f3_exit, nil_all⟩
theorem all3_addeds : ∀ x ∈ S3.addeds, F3 (.added x.1 x.2) := by
  simp only [S3, ReviewReversal.S1, List.forall_mem_cons]
  exact ⟨f3_addZ, f3_added, nil_all⟩
theorem all3_vulns : ∀ x ∈ S3.vulns, F3 (.vuln x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  simp only [S3, List.forall_mem_cons]
  exact ⟨f3_normal_report, nil_all⟩
theorem complete3 {o : Obj} (h : S3.Inv o) : F3 o := by
  cases o with
  | init M i => exact all3_inits (M, i) h
  | edge M i n f => exact all3_edges (M, i, n, f) h
  | added M a => exact all3_addeds (M, a) h
  | req M i t => exact False.elim (List.not_mem_nil h)
  | vuln M n s b => exact all3_vulns (M, n, s, b) h
theorem exact3 (o : Obj) : F3 o ↔ S3.Inv o := ⟨inv3, complete3⟩

/-- An executable source edge with its actual backward source-hit certificate. -/
def sourceHitWitness : {e : MicroEdge // FSeeds.srcHit P B2 0 0 e} :=
  ⟨sourceE, source_hit⟩
/-- The executable final fact and its normal-layer report certificate for this program. -/
def findingWitness : {g : AFact // F3 (.edge 0 zeroFact 2 g) ∧ g.demand = false ∧
    F3 (.vuln 0 2 sink false)} :=
  ⟨R3out, f3_return, rfl, f3_normal_report⟩
/-- The executable finite run-3 table, certified as exactly this program's closure. -/
def traceWitness : {s : LS // ∀ o, F3 o ↔ s.Inv o} := ⟨S3, exact3⟩

/-! Exact inter-run publications, demands and persistent records. -/
theorem hand1_root : handFA P R1 pubD 0 (normDem ⟨R1out.fact, some zeroFact⟩) :=
  ⟨_, ⟨zeroFact, R1out, R1out, r1_root, r1_return, by decide, rfl, rfl⟩, rfl⟩
theorem all_hands1 : ∀ x ∈ H1L, handFA P R1 pubD x.1 x.2 := by
  simp only [H1L, List.forall_mem_cons]
  exact ⟨hand1_root, hand1_C, nil_all⟩
theorem hands1_exact (m : MethodId) (d : DemandEdge) :
    handFA P R1 pubD m d ↔ (m, d) ∈ H1L :=
  ⟨hand1_bound, fun h => all_hands1 (m, d) h⟩

theorem all_records1 : ∀ x ∈ RB1L, recsB1 x.1 x.2 := by
  simp only [RB1L, List.forall_mem_cons]
  exact ⟨⟨(zeroFact, Z), r1_root, r1_z02, by decide, by decide⟩,
    ⟨(zeroFact, Z), r1_initZ, r1_z15, by decide, by decide⟩,
    ⟨(Jw, ⟨Jw, false⟩), r1_init, r1_j15, by decide, rfl⟩,
    ⟨(Jw, PN), r1_init, r1_p5, by decide, rfl⟩, nil_all⟩
theorem records1_exact (m : MethodId) (x : PFact × AFact) :
    recsB1 m x ↔ (m, x) ∈ RB1L := ⟨recs1_bound, fun h => all_records1 (m, x) h⟩
theorem all_records3 : ∀ x ∈ RC3L, rc3 x.1 x.2 := by
  simp only [RC3L, List.forall_mem_cons]
  exact ⟨Or.inl ⟨r1_root, r1_z02, by decide⟩,
    Or.inl ⟨r1_initZ, r1_z15, by decide⟩,
    Or.inl ⟨r1_init, r1_j15, by decide⟩,
    Or.inl ⟨r1_init, r1_p5, by decide⟩,
    Or.inr ⟨Jb, PB, b2_init, by decide, b2_keep0, by decide, rfl⟩, nil_all⟩
theorem records3_exact (m : MethodId) (x : PFact × AFact) :
    rc3 m x ↔ (m, x) ∈ RC3L := ⟨rc3_bound, fun h => all_records3 (m, x) h⟩

theorem dem3_source : dem3 0 (normDem ⟨XB.fact, none⟩) :=
  ⟨_, Or.inr (Or.inl ⟨XB, b2_x00, rfl⟩), rfl⟩
theorem all_demands3 : ∀ x ∈ D3L, dem3 x.1 x.2 := by
  simp only [D3L, List.forall_mem_cons]
  exact ⟨dem3_zero 0, dem3_zero 1, dem3_source, dem3_C, nil_all⟩
theorem demands3_exact (m : MethodId) (d : DemandEdge) :
    dem3 m d ↔ d ∈ demFor D3L m := by
  constructor
  · exact dem3_bound
  · intro h
    rcases List.mem_cons.mp h with hz | ht
    · subst hz
      exact dem3_zero m
    · obtain ⟨x, hx, hi⟩ := List.mem_filterMap.mp ht
      by_cases hm : x.1 = m
      · simp only [if_pos hm, Option.some.injEq] at hi
        rw [← hi, ← hm]
        exact all_demands3 x hx
      · simp only [if_neg hm] at hi
        cases hi

theorem demand3_all_exact (m : MethodId) (d : DemandEdge) :
    dem3 m d ↔ d = Backward.zeroDem ∨
      (m = 0 ∧ d = normDem ⟨XB.fact, none⟩) ∨ (m = 1 ∧ d = d3) := by
  constructor
  · intro h
    have hd := dem3_bound h
    by_cases hm0 : m = 0
    · subst hm0
      simpa [demFor, D3L, Backward.zeroDem, normDem, normFact, markNorm, XB] using hd
    · by_cases hm1 : m = 1
      · subst hm1
        simpa [demFor, D3L, Backward.zeroDem] using hd
      · exact Or.inl (by
          simpa [demFor, D3L, Backward.zeroDem, hm0, hm1, Ne.symm hm0, Ne.symm hm1] using hd)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact dem3_zero m
    · exact dem3_source
    · exact dem3_C

/-- Restriction publishes exactly the backward argument result; the raw keep row is a record. -/
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

/-- Every normal exit summary of run 1 is included in both next record sets. -/
theorem all_normal1_persisted {m : MethodId} {j : PFact} {g : AFact}
    (hi : R1 (.init m j)) (hg : R1 (.edge m j (P.exit m) g)) (hn : g.demand = false) :
    recsB1 m (revRec (j, g)) ∧ rc3 m (j, g) := by
  have hc : Cross j g :=
    (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → x.2.2.2.demand = false →
      Cross x.2.1 x.2.2.2) (m, j, P.exit m, g) (inv1 hg) rfl hn
  exact ⟨⟨(j, g), hi, hg, hc, rfl⟩, Or.inl ⟨hi, hg, hc⟩⟩
/-- Every eligible normal backward exit summary is included before demand restriction. -/
theorem all_normal2_persisted {m : MethodId} {j : PFact} {g : AFact}
    (hi : B2 (.init m j)) (hg : B2 (.edge m j (Pb.exit m) g)) (hn : g.demand = false)
    (hj : j ≠ zeroFact) : rc3 m (revRec (j, g)) := by
  have hc : CrossB j g :=
    (by decide : ∀ x ∈ S2.edges, x.2.2.1 = Pb.exit x.1 → x.2.2.2.demand = false →
      x.2.1 ≠ zeroFact → CrossB x.2.1 x.2.2.2) (m, j, Pb.exit m, g) (inv2 hg) rfl hn hj
  exact Or.inr ⟨j, g, hi, hj, hg, hc, rfl⟩

theorem all3_exit_cross {m : MethodId} {j : PFact} {g : AFact}
    (hg : F3 (.edge m j (P3.exit m) g)) : Cross j g :=
  (by decide : ∀ x ∈ S3.edges, x.2.2.1 = P3.exit x.1 → Cross x.2.1 x.2.2.2)
    (m, j, P3.exit m, g) (inv3 hg) rfl
/-- The raw Cross test leaves no demand to publish after the third run. -/
theorem hand3_empty : ∀ m d, ¬ handFA P3 F3 (pubR dem3) m d := by
  intro m d h
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, _, _⟩, _⟩ := h
  exact hnc (all3_exit_cross hg)

/-- Exact list lengths, including empty request sets and the normal-layer run-3 report. -/
theorem table_counts :
    (S1.inits.length, S1.edges.length, S1.addeds.length, S1.reqs.length, S1.vulns.length) =
      (3, 23, 2, 0, 1) ∧
    (S2.inits.length, S2.edges.length, S2.addeds.length, S2.reqs.length, S2.vulns.length) =
      (3, 24, 1, 0, 0) ∧
    (S3.inits.length, S3.edges.length, S3.addeds.length, S3.reqs.length, S3.vulns.length) =
      (3, 23, 2, 0, 1) := by decide
set_option synthInstance.maxSize 65536 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem tables_nodup :
    (S1.inits.Nodup ∧ S1.edges.Nodup ∧ S1.addeds.Nodup ∧ S1.reqs.Nodup ∧ S1.vulns.Nodup) ∧
    (S2.inits.Nodup ∧ S2.edges.Nodup ∧ S2.addeds.Nodup ∧ S2.reqs.Nodup ∧ S2.vulns.Nodup) ∧
    (S3.inits.Nodup ∧ S3.edges.Nodup ∧ S3.addeds.Nodup ∧ S3.reqs.Nodup ∧ S3.vulns.Nodup) := by
  simp only [S1, S2, S3, ReviewReversal.S1, zEdges, jEdges, pEdges, List.map,
    List.cons_append, List.nil_append, List.nodup_cons, List.nodup_nil]
  decide
#print axioms r1_found
#print axioms b2_exit
#print axioms dem3_C
#print axioms b2_return
#print axioms source_hit
#print axioms hits_exact
#print axioms seeds_exact
#print axioms kept
#print axioms closed3
#print axioms f3_normal_report
#print axioms lowered_pipeline_preserves
#print axioms exact1
#print axioms exact2
#print axioms exact3
#print axioms sourceHitWitness
#print axioms findingWitness
#print axioms traceWitness
#print axioms hands1_exact
#print axioms records1_exact
#print axioms records3_exact
#print axioms demands3_exact
#print axioms demand3_all_exact
#print axioms published2_exact
#print axioms all_normal1_persisted
#print axioms all_normal2_persisted
#print axioms all3_exit_cross
#print axioms hand3_empty
#print axioms table_counts
#print axioms tables_nodup
end ApSpec.ReviewFieldCleaner
