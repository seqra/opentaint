/-
  ApSpec.AbsCases — the CEGAR programs of F72 (abstract marks in restricted runs), with COMPLETE
  closure invariants (`AbsClosure.lean`: one `decide` per closure).

  These are finite micro-edge kernels. They are not the exact IR programs of the specification's
  test plan. A statement can contain alternative flows. Its micro edges apply as one relation;
  several assignments listed for that statement do not mean sequential strong writes.
-/
import ApSpec.AbsClosure
import ApSpec.HandoffCases

namespace ApSpec.AbsCases
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs

set_option maxRecDepth 100000

/-- The `*` tail with the Empty exclusion, and the field limit counter (every accessor counts). -/
def st : Kind := .star (.set [])
def cnt : Acc → Bool := fun _ => true

/-! ## Part 1. Program (i): THE GETTER WITH TWO MARKS (sharing)

```
root():  x.f.g = source_T_or_U();  r = get(x);  sink_T(r);  sink_U(r);                 // method 0
get(x):  ret = x.f.g;  return ret;                                                      // method 1
```
The source statement has two alternative micro edges to `x.f.g`, with marks T and U. It is one
statement, so neither micro edge overwrites the other in the closure.
Accessors f=4, g=5. Bases zero=0, x=1, r=2, arg=3 (the `x` of `get`), ret=4. Marks T=1, U=2. Field
limits: forward run 1 L=1, backward run 2 L=1, forward run 3 L=2. In run 1 the read `x.f.g` is
above the premise `(arg,.,*)`: the summary `(arg,.,*) → (ret,.,[any])` is in the demand layer, so
it is handed off as the `*` pattern `((ret,.,[any],*), D-p = (arg,.,*))`. Backward run 2 emits ONE
initial fact `(ret,.,*,{},*)` (the flow form) for the two requirements `(ret,.,$,T)` and
`(ret,.,$,U)`; its summary is cut at L=1 to `(arg,.f,[any],*)` (demand layer: not a record), so the
next forward pattern is `((arg,.f,[any],*), D-p = (ret,.,*))`. Forward run 3 emits ONE initial fact
`(arg,.f,*,{},*)` for the two added facts `(arg,.f.g,$,T)` and `(arg,.f.g,$,U)` (today's `emitM`
gives two), and it reports both vulnerabilities.

NOTE: without the cut, the backward summary of a getter is NORMAL with a `*` tail, so it is a record
(`crossB_of_star_concl`, vector `plain_getter_record`): forward run 3 crosses the getter and has no
initial fact in it. The sharing is visible only where the demand stays (a cut, an `[any]`). -/

namespace Getter2

def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def zb : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- One source statement with alternative outputs T and U at `x.f.g`. -/
def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [4, 5], .exact, .conc 1⟩),
  (zeroFact, ⟨1, [4, 5], .exact, .conc 2⟩)]⟩
def callG : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
/-- `ret = arg.f.g`. -/
def gs : Stmt := ⟨[3, 4], [(⟨3, [4, 5], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callG, 2), (1, 0, .stmt gs, 1)]⟩
def sinkT : PFact := ⟨2, [], .exact, .conc 1⟩
def sinkU : PFact := ⟨2, [], .exact, .conc 2⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkT), (0, 2, sinkU)]
abbrev Pb : Program := Program.rev P

theorem hE00 : (0, 0, Instr.stmt src, 1) ∈ P.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callG, 2) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.stmt gs, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hb_c : (0, 2, Instr.call (Call.rev callG), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem hb_g : (1, 1, Instr.stmt (Stmt.rev gs), 0) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hE00
#print axioms hE01
#print axioms hE10
#print axioms hb_c
#print axioms hb_g

/-! ### The named facts -/

/-- Run 1: the source cut to `(x,.f,[any],T)`, the added fact `(arg,.f,[any],T)`, the policy premise
    `(arg,.,*)` of the getter and its demand-layer summary `(ret,.,[any],*)`. -/
def X1T : AFact := ⟨⟨1, [4], .any, .conc 1⟩, true⟩
def A1T : PFact := ⟨3, [4], .any, .conc 1⟩
def Jw : PFact := ⟨3, [], st, .star⟩
def Gg : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
/-- Backward run 2: the requirements at the exit of the getter, the flow form, its summary. -/
def RqT : PFact := ⟨4, [], .exact, .conc 1⟩
def RqU : PFact := ⟨4, [], .exact, .conc 2⟩
def JbS : PFact := ⟨4, [], st, .star⟩
def GbS : AFact := ⟨⟨3, [4], .any, .star⟩, true⟩
/-- Forward run 3: the sources, the two added facts, the flow form, its summary. -/
def X3T : AFact := ⟨⟨1, [4, 5], .exact, .conc 1⟩, false⟩
def X3U : AFact := ⟨⟨1, [4, 5], .exact, .conc 2⟩, false⟩
def A3T : PFact := ⟨3, [4, 5], .exact, .conc 1⟩
def A3U : PFact := ⟨3, [4, 5], .exact, .conc 2⟩
def J3S : PFact := ⟨3, [4], st, .star⟩
def G3 : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
/-- The demand edge of the getter in backward run 2 and in forward run 3. -/
def dG : DemandEdge := normDem ⟨Gg.fact, some Jw⟩
def d3 : DemandEdge := normDem ⟨GbS.fact, some JbS⟩

/-! ### The complete closures (states from the executable simulation, checked by `decide`) -/

def S1 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], .any, .star⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 2)⟩, true⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [4], .any, (.conc 1)⟩),
    (1, ⟨3, [4], .any, (.conc 2)⟩)]
  reqs := []
  vulns := [(0, 2, ⟨2, [], .exact, (.conc 1)⟩, true),
    (0, 2, ⟨2, [], .exact, (.conc 2)⟩, true)]

def H1L : List (MethodId × DemandEdge) := [(0, ⟨⟨2, [], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (0, ⟨⟨2, [], .any, (.conc 2)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (1, ⟨⟨4, [], .any, .star⟩, some ⟨3, [], (.star (.set [])), .star⟩⟩)]

def RB1L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩))]

def S2 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .exact, (.conc 2)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [4], .any, .star⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [4], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [4], .any, (.conc 2)⟩, true⟩)]
  addeds := [(1, ⟨4, [], .exact, (.conc 1)⟩),
    (1, ⟨4, [], .exact, (.conc 2)⟩)]
  reqs := []
  vulns := []

def D3L : List (MethodId × DemandEdge) := [(0, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (1, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (0, ⟨⟨1, [4], .any, (.conc 1)⟩, none⟩),
    (0, ⟨⟨1, [4], .any, (.conc 2)⟩, none⟩),
    (1, ⟨⟨3, [4], .any, .star⟩, some ⟨4, [], (.star (.set [])), .star⟩⟩)]

def RC3L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩))]

def S3 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [4], (.star (.set [])), .star⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4, 5], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [4, 5], .exact, (.conc 2)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [4], (.star (.set [])), .star⟩, 0, ⟨⟨3, [4], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [4], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], .any, .star⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 2)⟩, true⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [4, 5], .exact, (.conc 1)⟩),
    (1, ⟨3, [4, 5], .exact, (.conc 2)⟩)]
  reqs := []
  vulns := [(0, 2, ⟨2, [], .exact, (.conc 1)⟩, true),
    (0, 2, ⟨2, [], .exact, (.conc 2)⟩, true)]

abbrev R1 : Obj → Prop := D P cnt 1 policy1 sinks [0]

theorem closed1 : ClosedD P cnt 1 sinks [0] S1 := by decide

/-- THE COMPLETE FORWARD RUN 1. -/
theorem inv1 {o : Obj} (h : R1 o) : S1.Inv o := closedD_sound P cnt 1 sinks [0] S1 closed1 h

#print axioms closed1
#print axioms inv1

/-- The forward hand-off of run 1 (normalized), bounded by the list. -/
theorem handFA1_bound {m : MethodId} {d : DemandEdge} (h : handFA P R1 pubD m d) : (m, d) ∈ H1L := by
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, hpub, rfl⟩, rfl⟩ := h
  have hp : g' = g := hpub
  subst hp
  exact (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
    (x.1, normDem ⟨x.2.2.2.fact, some x.2.1⟩) ∈ H1L) (m, j, P.exit m, g') (inv1 hg) rfl hnc

#print axioms handFA1_bound

/-- The backward records: the reversals of the crossable exit edges of run 1. -/
def recsB1 : Recs := fun m y => ∃ x : PFact × AFact, R1 (.init m x.1) ∧
  R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2 ∧ y = revRec x

theorem recsB1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

#print axioms recsB1_bound

abbrev B2 : Obj → Prop := DBW Pb cnt 1 (handFA P R1 pubD) recsB1 [0] sinks

theorem closed2 : ClosedBA Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide

/-- THE COMPLETE BACKWARD RUN 2. -/
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (handFA1_bound hd)) (fun _ _ hx => recsB1_bound hx) h

#print axioms closed2
#print axioms inv2

/-- The demand of forward run 3. -/
def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))

theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1) (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc (m, dd)
      (handFA1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

#print axioms dem3_bound

/-- The records of forward run 3: the crossable exit edges of run 1 and the reversed normal
    backward summaries with a crossable reversal. -/
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

#print axioms rc3_bound

abbrev F3 : Obj → Prop := DRW P cnt 2 dem3 rc3 sinks [0]

theorem closed3 : ClosedRA P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide

/-- THE COMPLETE FORWARD RUN 3. -/
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h

#print axioms closed3
#print axioms inv3

/-! ### The derivations -/

theorem r1_e00 : R1 (.edge 0 zeroFact 0 Backward.zeroAF) := D.start (D.root (List.Mem.head _))
theorem r1_x1 : R1 (.edge 0 zeroFact 1 X1T) := D.step r1_e00 (s := src) hE00 (by decide)
theorem r1_add : R1 (.added 1 A1T) :=
  D.added (c := callG) (e := bx) (a := ⟨A1T, true⟩) r1_x1 hE01 (List.Mem.head _) (by decide)
theorem r1_init : R1 (.init 1 Jw) := by
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinks) (roots := [0])
    (P := P) r1_add
  have hp : policy1 1 A1T = Jw := by decide
  rw [hp] at h
  exact h
/-- The run-1 summary of the getter, in the demand layer. -/
theorem r1_exit : R1 (.edge 1 Jw 1 Gg) := D.step (D.start r1_init) (s := gs) hE10 (by decide)
theorem handFA1_G : handFA P R1 pubD 1 dG :=
  ⟨_, ⟨Jw, Gg, Gg, r1_init, r1_exit, by decide, rfl, rfl⟩, rfl⟩

#print axioms r1_e00
#print axioms r1_x1
#print axioms r1_add
#print axioms r1_init
#print axioms r1_exit
#print axioms handFA1_G

theorem b2_e02 : B2 (.edge 0 zeroFact 2 Backward.zeroAF) := DBA.start (DBA.root (List.Mem.head _))
theorem b2_addT : B2 (.added 1 RqT) :=
  DBA.added (c := Call.rev callG) (e := revEdge br.1 br.2) (a := ⟨RqT, false⟩)
    (DBA.seed (s := sinkT) (List.Mem.head _) b2_e02) hb_c (List.Mem.head _) (by decide)
theorem b2_addU : B2 (.added 1 RqU) :=
  DBA.added (c := Call.rev callG) (e := revEdge br.1 br.2) (a := ⟨RqU, false⟩)
    (DBA.seed (s := sinkU) (List.Mem.tail _ (List.Mem.head _)) b2_e02) hb_c (List.Mem.head _)
    (by decide)
/-- Backward run 2 emits the flow form `(ret,.,*,{},*)` into the getter. -/
theorem b2_init : B2 (.init 1 JbS) := DBA.initR (d := dG) b2_addT handFA1_G (by decide)
theorem b2_exit : B2 (.edge 1 JbS 0 GbS) := DBA.step (DBA.start b2_init) hb_g (by decide)
theorem dem3_G : dem3 1 d3 :=
  ⟨_, Or.inr (Or.inr ⟨JbS, GbS, GbS, b2_init, by decide, b2_exit, by decide,
    ⟨dG, handFA1_G, by decide⟩, rfl⟩), rfl⟩

#print axioms b2_e02
#print axioms b2_addT
#print axioms b2_addU
#print axioms b2_init
#print axioms b2_exit
#print axioms dem3_G

theorem f3_e00 : F3 (.edge 0 zeroFact 0 Backward.zeroAF) := DRA.start (DRA.root (List.Mem.head _))
theorem f3_xT : F3 (.edge 0 zeroFact 1 X3T) := DRA.step f3_e00 (s := src) hE00 (by decide)
theorem f3_xU : F3 (.edge 0 zeroFact 1 X3U) := DRA.step f3_e00 (s := src) hE00 (by decide)
theorem f3_addT : F3 (.added 1 A3T) :=
  DRA.added (c := callG) (e := bx) (a := ⟨A3T, false⟩) f3_xT hE01 (List.Mem.head _) (by decide)
theorem f3_addU : F3 (.added 1 A3U) :=
  DRA.added (c := callG) (e := bx) (a := ⟨A3U, false⟩) f3_xU hE01 (List.Mem.head _) (by decide)
/-- Forward run 3 emits the flow form `(arg,.f,*,{},*)` into the getter (from the added fact with the
    mark `T`; the one with the mark `U` emits the same fact). -/
theorem f3_init : F3 (.init 1 J3S) := DRA.initR (d := d3) f3_addT dem3_G (by decide)
theorem f3_exit : F3 (.edge 1 J3S 1 G3) := DRA.step (DRA.start f3_init) (s := gs) hE10 (by decide)
theorem f3_rT : F3 (.edge 0 zeroFact 2 (limitF cnt 2 ⟨⟨2, [], .any, .conc 1⟩, true⟩)) :=
  DRA.ret (c := callG) (e1 := bx) (a := ⟨A3T, false⟩) (j := J3S) (g := G3) (d := d3) (g' := G3)
    (r := ⟨⟨4, [], .any, .conc 1⟩, true⟩) (e2 := br) f3_xT hE01 (List.Mem.head _) (by decide)
    f3_init f3_exit dem3_G (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)
theorem f3_rU : F3 (.edge 0 zeroFact 2 (limitF cnt 2 ⟨⟨2, [], .any, .conc 2⟩, true⟩)) :=
  DRA.ret (c := callG) (e1 := bx) (a := ⟨A3U, false⟩) (j := J3S) (g := G3) (d := d3) (g' := G3)
    (r := ⟨⟨4, [], .any, .conc 2⟩, true⟩) (e2 := br) f3_xU hE01 (List.Mem.head _) (by decide)
    f3_init f3_exit dem3_G (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms f3_e00
#print axioms f3_xT
#print axioms f3_xU
#print axioms f3_addT
#print axioms f3_addU
#print axioms f3_init
#print axioms f3_exit
#print axioms f3_rT
#print axioms f3_rU

/-! ### The results of program (i) -/

/-- BACKWARD RUN 2 SHARES: the two requirements `(ret,.,$,T)` and `(ret,.,$,U)` reach the getter,
    and its only non-zero initial fact is the flow form `(ret,.,*,{},*)`. -/
theorem getter_b2_one_init : B2 (.added 1 RqT) ∧ B2 (.added 1 RqU) ∧ B2 (.init 1 JbS) ∧
    ∀ j, B2 (.init 1 j) → j = zeroFact ∨ j = JbS :=
  ⟨b2_addT, b2_addU, b2_init, fun j h => (by decide : ∀ x ∈ S2.inits, x.1 = 1 →
    x.2 = zeroFact ∨ x.2 = JbS) (1, j) (inv2 h) rfl⟩

#print axioms getter_b2_one_init

/-- FORWARD RUN 3 SHARES: the two added facts `(arg,.f.g,$,T)` and `(arg,.f.g,$,U)` reach the
    getter, and its only non-zero initial fact is the flow form `(arg,.f,*,{},*)`. -/
theorem getter_f3_one_init : F3 (.added 1 A3T) ∧ F3 (.added 1 A3U) ∧ F3 (.init 1 J3S) ∧
    ∀ j, F3 (.init 1 j) → j = zeroFact ∨ j = J3S :=
  ⟨f3_addT, f3_addU, f3_init, fun j h => (by decide : ∀ x ∈ S3.inits, x.1 = 1 →
    x.2 = zeroFact ∨ x.2 = J3S) (1, j) (inv3 h) rfl⟩

#print axioms getter_f3_one_init

/-- THE SHARING IN ONE STEP: `emitW` gives the same flow form for both added facts; today's `emitM`
    gives two different initial facts (the mark product). -/
theorem getter_sharing : emitW d3.din A3T = some J3S ∧ emitW d3.din A3U = some J3S ∧
    emitM d3.din A3T = some A3T ∧ emitM d3.din A3U = some A3U ∧ A3T ≠ A3U := by decide

#print axioms getter_sharing

/-- FORWARD RUN 3 REPORTS BOTH VULNERABILITIES (demand layer: the read of the getter is above its
    premise), and nothing else. -/
theorem getter_f3_found : F3 (.vuln 0 2 sinkT true) ∧ F3 (.vuln 0 2 sinkU true) ∧
    ∀ M n s b, F3 (.vuln M n s b) → (M = 0 ∧ n = 2 ∧ (s = sinkT ∨ s = sinkU) ∧ b = true) :=
  ⟨DRA.vuln f3_rT (List.Mem.head _) (by decide),
   DRA.vuln f3_rU (List.Mem.tail _ (List.Mem.head _)) (by decide),
   fun M n s b h => (by decide : ∀ x ∈ S3.vulns, x.1 = 0 ∧ x.2.1 = 2 ∧
     (x.2.2.1 = sinkT ∨ x.2.2.1 = sinkU) ∧ x.2.2.2 = true) (M, n, s, b) (inv3 h)⟩

#print axioms getter_f3_found

/-- The plain getter (no cut): its normal backward summary with a `*` tail is a record. -/
theorem plain_getter_record : CrossB ⟨4, [], st, .star⟩ ⟨⟨3, [4], st, .star⟩, false⟩ := by decide

#print axioms plain_getter_record

end Getter2

/-! ## Part 2. Program (ii): A MARK-CHANGING PASS RULE `T → U` in a callee that a `*` pattern reaches

```
root():  x.a.b = source_T();  r = conv(x);  sink_U(r.a.b);                 // method 0
conv(x): choose {ret = TU(x) | ret.f = x | ret = x.g}; return ret;        // method 1, ONE statement
```
`choose` names alternative micro-edge flows in one statement. It does not execute the assignments
in sequence. Accessors a=1, b=2, f=4, g=5. Bases, bindings as in program (i). Marks T=1, U=2. The statement of
`conv` has three micro edges: the pass rule `(arg,.,*,T) → (ret,.,*,U)` (a concrete premise mark),
the write `(arg,.,*) → (ret,.f,*)` and the read `(arg,.g,*) → (ret,.,*)` (both mark-agnostic). Field
limits 1 / 1 / 2. Run 1: the policy premise `(arg,.,*)` raises the request `T` at the pass rule; the
answer is the concrete premise `(arg,.,*,T)` (start `[any]`), whose summary `(ret,.,[any],U)` is in
the demand layer: a CONCRETE pattern. The read gives the `*` summary `(ret,.,[any],*)` (demand
layer): a `*` pattern. Backward run 2 enters `conv` with the flow form `(ret,.,*,{},*)` and with the
concrete `(ret,.a,[any],U)`; the `*` analysis gives nothing at the reversed pass rule (its premise
mark is `U`), the concrete one gives `(arg,.a,[any],T)`. Forward run 3 has the flow form
`(arg,.,*,{},*)` AND the concrete `(arg,.a.b,$,T)` in `conv`: the `*` analysis gives no fact with
the mark `U` (the request of the pass rule is dropped, R4), the concrete one gives
`(ret,.a.b,$,U)`, and the vulnerability is reported in the NORMAL layer. -/

namespace Conv

def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def zb : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [1, 2], .exact, .conc 1⟩)]⟩
def callC : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
/-- One statement with alternatives `ret = TU(arg)`, `ret.f = arg`, and `ret = arg.g`. -/
def cs : Stmt := ⟨[3, 4], [(⟨3, [], st, .conc 1⟩, ⟨4, [], st, .conc 2⟩),
  (⟨3, [], st, .star⟩, ⟨4, [4], st, .star⟩), (⟨3, [5], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callC, 2), (1, 0, .stmt cs, 1)]⟩
def sinkU : PFact := ⟨2, [1, 2], .exact, .conc 2⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkU)]
abbrev Pb : Program := Program.rev P

theorem hE00 : (0, 0, Instr.stmt src, 1) ∈ P.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callC, 2) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.stmt cs, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hb_c : (0, 2, Instr.call (Call.rev callC), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem hb_s : (1, 1, Instr.stmt (Stmt.rev cs), 0) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

#print axioms hE00
#print axioms hE01
#print axioms hE10
#print axioms hb_c
#print axioms hb_s

/-! ### The named facts -/

def X1 : AFact := ⟨⟨1, [1], .any, .conc 1⟩, true⟩
def A1 : PFact := ⟨3, [1], .any, .conc 1⟩
/-- The policy premise of run 1, and the answer of the request `T`. -/
def Jw : PFact := ⟨3, [], st, .star⟩
def JT : PFact := ⟨3, [], st, .conc 1⟩
/-- The run-1 summaries: the `*` read (demand layer) and the concrete pass (demand layer). -/
def GsA : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
def GU : AFact := ⟨⟨4, [], .any, .conc 2⟩, true⟩
/-- Backward run 2: the requirement, the flow form, the concrete premise, their summaries. -/
def RqU : PFact := ⟨4, [1], .any, .conc 2⟩
def JbS : PFact := ⟨4, [], st, .star⟩
def JbU : PFact := ⟨4, [1], .any, .conc 2⟩
def GbS : AFact := ⟨⟨3, [], .any, .star⟩, true⟩
def GbU : AFact := ⟨⟨3, [1], .any, .conc 1⟩, true⟩
/-- Forward run 3: the source, the added fact (also the concrete premise), the concrete summary. -/
def X3 : AFact := ⟨⟨1, [1, 2], .exact, .conc 1⟩, false⟩
def A3 : PFact := ⟨3, [1, 2], .exact, .conc 1⟩
def G3U : AFact := ⟨⟨4, [1, 2], .exact, .conc 2⟩, false⟩
def dS : DemandEdge := normDem ⟨GsA.fact, some Jw⟩
def dU : DemandEdge := normDem ⟨GU.fact, some JT⟩
def dS3 : DemandEdge := normDem ⟨GbS.fact, some JbS⟩
def dT3 : DemandEdge := normDem ⟨GbU.fact, some JbU⟩

/-! ### The complete closures -/

def S1 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [1], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [4], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], .any, .star⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [4], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 0, ⟨⟨3, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 1, ⟨⟨4, [], .any, (.conc 2)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 1, ⟨⟨4, [4], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 1, ⟨⟨4, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 2)⟩, true⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [1], .any, (.conc 1)⟩)]
  reqs := [(1, ⟨3, [], (.star (.set [])), .star⟩, 1)]
  vulns := [(0, 2, ⟨2, [1, 2], .exact, (.conc 2)⟩, true)]

def H1L : List (MethodId × DemandEdge) := [(0, ⟨⟨2, [4], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (0, ⟨⟨2, [], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (0, ⟨⟨2, [], .any, (.conc 2)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (1, ⟨⟨4, [], .any, .star⟩, some ⟨3, [], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨4, [], .any, (.conc 2)⟩, some ⟨3, [], (.star (.set [])), (.conc 1)⟩⟩),
    (1, ⟨⟨4, [4], .any, (.conc 1)⟩, some ⟨3, [], (.star (.set [])), (.conc 1)⟩⟩),
    (1, ⟨⟨4, [], .any, (.conc 1)⟩, some ⟨3, [], (.star (.set [])), (.conc 1)⟩⟩)]

def RB1L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨4, [4], (.star (.set [])), .star⟩, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩))]

def S2 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩),
    (1, ⟨4, [1], .any, (.conc 2)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [1], .any, (.conc 2)⟩, 1, ⟨⟨4, [1], .any, (.conc 2)⟩, true⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], .any, .star⟩, true⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [5], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [1], .any, (.conc 2)⟩, 0, ⟨⟨3, [1], .any, (.conc 1)⟩, true⟩),
    (1, ⟨4, [1], .any, (.conc 2)⟩, 0, ⟨⟨3, [5], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [5], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [1], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [5], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [1], .any, (.conc 1)⟩, true⟩)]
  addeds := [(1, ⟨4, [1], .any, (.conc 2)⟩)]
  reqs := []
  vulns := []

def D3L : List (MethodId × DemandEdge) := [(0, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (1, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (0, ⟨⟨1, [], .any, (.conc 2)⟩, none⟩),
    (0, ⟨⟨1, [5], .any, (.conc 2)⟩, none⟩),
    (0, ⟨⟨1, [1], .any, (.conc 1)⟩, none⟩),
    (1, ⟨⟨3, [], .any, .star⟩, some ⟨4, [], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨3, [1], .any, (.conc 1)⟩, some ⟨4, [1], .any, (.conc 2)⟩⟩),
    (1, ⟨⟨3, [5], .any, (.conc 2)⟩, some ⟨4, [1], .any, (.conc 2)⟩⟩)]

def RC3L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨3, [], (.star (.set [])), .star⟩, ⟨⟨4, [4], (.star (.set [])), .star⟩, false⟩)),
    (1, (⟨3, [5], (.star (.set [])), .star⟩, ⟨⟨4, [], (.star (.set [])), .star⟩, false⟩))]

def S3 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [1, 2], .exact, (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [1, 2], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [4, 1], .any, (.conc 1)⟩, true⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [1, 2], .exact, (.conc 1)⟩, 0, ⟨⟨3, [1, 2], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [4], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], .any, .star⟩, true⟩),
    (1, ⟨3, [1, 2], .exact, (.conc 1)⟩, 1, ⟨⟨4, [1, 2], .exact, (.conc 2)⟩, false⟩),
    (1, ⟨3, [1, 2], .exact, (.conc 1)⟩, 1, ⟨⟨4, [4, 1], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1, 2], .exact, (.conc 2)⟩, false⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [1, 2], .exact, (.conc 1)⟩)]
  reqs := []
  vulns := [(0, 2, ⟨2, [1, 2], .exact, (.conc 2)⟩, false)]

abbrev R1 : Obj → Prop := D P cnt 1 policy1 sinks [0]

theorem closed1 : ClosedD P cnt 1 sinks [0] S1 := by decide

/-- THE COMPLETE FORWARD RUN 1. -/
theorem inv1 {o : Obj} (h : R1 o) : S1.Inv o := closedD_sound P cnt 1 sinks [0] S1 closed1 h

#print axioms closed1
#print axioms inv1

/-- The forward hand-off of run 1 (normalized), bounded by the list. -/
theorem handFA1_bound {m : MethodId} {d : DemandEdge} (h : handFA P R1 pubD m d) : (m, d) ∈ H1L := by
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, hpub, rfl⟩, rfl⟩ := h
  have hp : g' = g := hpub
  subst hp
  exact (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
    (x.1, normDem ⟨x.2.2.2.fact, some x.2.1⟩) ∈ H1L) (m, j, P.exit m, g') (inv1 hg) rfl hnc

#print axioms handFA1_bound

/-- The backward records: the reversals of the crossable exit edges of run 1. -/
def recsB1 : Recs := fun m y => ∃ x : PFact × AFact, R1 (.init m x.1) ∧
  R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2 ∧ y = revRec x

theorem recsB1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

#print axioms recsB1_bound

abbrev B2 : Obj → Prop := DBW Pb cnt 1 (handFA P R1 pubD) recsB1 [0] sinks

theorem closed2 : ClosedBA Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide

/-- THE COMPLETE BACKWARD RUN 2. -/
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (handFA1_bound hd)) (fun _ _ hx => recsB1_bound hx) h

#print axioms closed2
#print axioms inv2

/-- The demand of forward run 3. -/
def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))

theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1) (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc (m, dd)
      (handFA1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

#print axioms dem3_bound

/-- The records of forward run 3: the crossable exit edges of run 1 and the reversed normal
    backward summaries with a crossable reversal. -/
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

#print axioms rc3_bound

abbrev F3 : Obj → Prop := DRW P cnt 2 dem3 rc3 sinks [0]

theorem closed3 : ClosedRA P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide

/-- THE COMPLETE FORWARD RUN 3. -/
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h

#print axioms closed3
#print axioms inv3

/-! ### The derivations -/

theorem r1_e00 : R1 (.edge 0 zeroFact 0 Backward.zeroAF) := D.start (D.root (List.Mem.head _))
theorem r1_x1 : R1 (.edge 0 zeroFact 1 X1) := D.step r1_e00 (s := src) hE00 (by decide)
theorem r1_add : R1 (.added 1 A1) :=
  D.added (c := callC) (e := bx) (a := ⟨A1, true⟩) r1_x1 hE01 (List.Mem.head _) (by decide)
theorem r1_initW : R1 (.init 1 Jw) := by
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinks) (roots := [0])
    (P := P) r1_add
  have hp : policy1 1 A1 = Jw := by decide
  rw [hp] at h
  exact h
/-- RUN 1 RAISES THE REQUEST `T` at the pass rule (the policy premise has the mark `*`). -/
theorem r1_req : R1 (.req 1 Jw 1) := D.reqStmt (D.start r1_initW) (s := cs) hE10 (by decide)
/-- RUN 1 ANSWERS IT: the concrete premise `(arg,.,*,T)`. -/
theorem r1_initT : R1 (.init 1 JT) := by
  have h := D.answer (P := P) (counted := cnt) (L := 1) (α := policy1) (sinks := sinks)
    (roots := [0]) r1_req r1_add rfl (by decide)
  have hp : answerInit Jw A1 1 = JT := by decide
  rw [hp] at h
  exact h
theorem r1_exitS : R1 (.edge 1 Jw 1 GsA) := D.step (D.start r1_initW) (s := cs) hE10 (by decide)
/-- The concrete summary of the answer: `(arg,.,*,T) → (ret,.,[any],U)`, demand layer. -/
theorem r1_exitU : R1 (.edge 1 JT 1 GU) := D.step (D.start r1_initT) (s := cs) hE10 (by decide)
theorem handFA1_S : handFA P R1 pubD 1 dS :=
  ⟨_, ⟨Jw, GsA, GsA, r1_initW, r1_exitS, by decide, rfl, rfl⟩, rfl⟩
theorem handFA1_U : handFA P R1 pubD 1 dU :=
  ⟨_, ⟨JT, GU, GU, r1_initT, r1_exitU, by decide, rfl, rfl⟩, rfl⟩

#print axioms r1_e00
#print axioms r1_x1
#print axioms r1_add
#print axioms r1_initW
#print axioms r1_req
#print axioms r1_initT
#print axioms r1_exitS
#print axioms r1_exitU
#print axioms handFA1_S
#print axioms handFA1_U

theorem b2_e02 : B2 (.edge 0 zeroFact 2 Backward.zeroAF) := DBA.start (DBA.root (List.Mem.head _))
theorem b2_add : B2 (.added 1 RqU) :=
  DBA.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨RqU, true⟩)
    (DBA.seed (s := sinkU) (List.Mem.head _) b2_e02) hb_c (List.Mem.head _) (by decide)
theorem b2_initS : B2 (.init 1 JbS) := DBA.initR (d := dS) b2_add handFA1_S (by decide)
theorem b2_initU : B2 (.init 1 JbU) := DBA.initR (d := dU) b2_add handFA1_U (by decide)
theorem b2_exitS : B2 (.edge 1 JbS 0 GbS) := DBA.step (DBA.start b2_initS) hb_s (by decide)
theorem b2_exitU : B2 (.edge 1 JbU 0 GbU) := DBA.step (DBA.start b2_initU) hb_s (by decide)
theorem dem3_S : dem3 1 dS3 :=
  ⟨_, Or.inr (Or.inr ⟨JbS, GbS, GbS, b2_initS, by decide, b2_exitS, by decide,
    ⟨dS, handFA1_S, by decide⟩, rfl⟩), rfl⟩
theorem dem3_T : dem3 1 dT3 :=
  ⟨_, Or.inr (Or.inr ⟨JbU, GbU, GbU, b2_initU, by decide, b2_exitU, by decide,
    ⟨dU, handFA1_U, by decide⟩, rfl⟩), rfl⟩

#print axioms b2_e02
#print axioms b2_add
#print axioms b2_initS
#print axioms b2_initU
#print axioms b2_exitS
#print axioms b2_exitU
#print axioms dem3_S
#print axioms dem3_T

theorem f3_e00 : F3 (.edge 0 zeroFact 0 Backward.zeroAF) := DRA.start (DRA.root (List.Mem.head _))
theorem f3_x1 : F3 (.edge 0 zeroFact 1 X3) := DRA.step f3_e00 (s := src) hE00 (by decide)
theorem f3_add : F3 (.added 1 A3) :=
  DRA.added (c := callC) (e := bx) (a := ⟨A3, false⟩) f3_x1 hE01 (List.Mem.head _) (by decide)
/-- Forward run 3 emits the flow form `(arg,.,*,{},*)` (the `*` pattern) into `conv`. -/
theorem f3_initS : F3 (.init 1 Jw) := DRA.initR (d := dS3) f3_add dem3_S (by decide)
/-- Forward run 3 emits the concrete `(arg,.a.b,$,T)` (the concrete pattern) into `conv`. -/
theorem f3_initT : F3 (.init 1 A3) := DRA.initR (d := dT3) f3_add dem3_T (by decide)
theorem f3_exitU : F3 (.edge 1 A3 1 G3U) := DRA.step (DRA.start f3_initT) (s := cs) hE10 (by decide)
theorem f3_r : F3 (.edge 0 zeroFact 2 (limitF cnt 2 ⟨⟨2, [1, 2], .exact, .conc 2⟩, false⟩)) :=
  DRA.ret (c := callC) (e1 := bx) (a := ⟨A3, false⟩) (j := A3) (g := G3U) (d := dT3) (g' := G3U)
    (r := G3U) (e2 := br) f3_x1 hE01 (List.Mem.head _) (by decide) f3_initT f3_exitU dem3_T
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms f3_e00
#print axioms f3_x1
#print axioms f3_add
#print axioms f3_initS
#print axioms f3_initT
#print axioms f3_exitU
#print axioms f3_r

/-! ### The results of program (ii) -/

/-- RUN 1 MAKES THE CONCRETE PATTERN: the request `T` of the policy premise, its answer, and the
    concrete summary of the answer, which is NOT crossable (so it is a demand edge). -/
theorem conv_run1 : R1 (.req 1 Jw 1) ∧ R1 (.init 1 JT) ∧ R1 (.edge 1 JT 1 GU) ∧ ¬ Cross JT GU :=
  ⟨r1_req, r1_initT, r1_exitU, by decide⟩

#print axioms conv_run1

/-- BACKWARD RUN 2: `conv` is entered with the flow form and with the concrete requirement; the `*`
    analysis gives nothing with the mark `T` (the reversed pass rule has the premise mark `U`), the
    concrete one gives `(arg,.a,[any],T)`. -/
theorem conv_b2 : B2 (.init 1 JbS) ∧ B2 (.init 1 JbU) ∧ B2 (.edge 1 JbU 0 GbU) ∧
    (∀ j, B2 (.init 1 j) → j = zeroFact ∨ j = JbS ∨ j = JbU) ∧
    (∀ n g, B2 (.edge 1 JbS n g) → g.fact.mark ≠ .conc 1) :=
  ⟨b2_initS, b2_initU, b2_exitU,
   fun j h => (by decide : ∀ x ∈ S2.inits, x.1 = 1 → x.2 = zeroFact ∨ x.2 = JbS ∨ x.2 = JbU)
     (1, j) (inv2 h) rfl,
   fun n g h => (by decide : ∀ x ∈ S2.edges, x.1 = 1 → x.2.1 = JbS → x.2.2.2.fact.mark ≠ .conc 1)
     (1, JbS, n, g) (inv2 h) rfl rfl⟩

#print axioms conv_b2

/-- FORWARD RUN 3: `conv` has the flow form and the concrete premise (and the zero fact) as its
    initial facts. -/
theorem conv_f3_inits : F3 (.init 1 Jw) ∧ F3 (.init 1 A3) ∧
    ∀ j, F3 (.init 1 j) → j = zeroFact ∨ j = Jw ∨ j = A3 :=
  ⟨f3_initS, f3_initT, fun j h => (by decide : ∀ x ∈ S3.inits, x.1 = 1 →
    x.2 = zeroFact ∨ x.2 = Jw ∨ x.2 = A3) (1, j) (inv3 h) rfl⟩

#print axioms conv_f3_inits

/-- THE `*` ANALYSIS GIVES NOTHING FOR THE PASS RULE: no edge of the flow form has the mark `U`. In
    run 1 the same step raises the request `T` (`transfer … .reqs = [1]`); forward run 3 has no
    request rule, so the request is dropped (R4), and the run has no request at all. -/
theorem conv_star_nothing : (∀ n g, F3 (.edge 1 Jw n g) → g.fact.mark ≠ .conc 2) ∧
    (transfer cnt 2 cs (startFact Jw)).reqs = [1] ∧ ∀ M i t, ¬ F3 (.req M i t) :=
  ⟨fun n g h => (by decide : ∀ x ∈ S3.edges, x.1 = 1 → x.2.1 = Jw → x.2.2.2.fact.mark ≠ .conc 2)
     (1, Jw, n, g) (inv3 h) rfl rfl,
   by decide, fun _ _ _ => DRA_no_req P cnt 2 dem3 emitW satW restrictI rc3 sinks [0]⟩

#print axioms conv_star_nothing

/-- THE FLOW IS FOUND THROUGH THE CONCRETE PATTERN: the concrete premise gives `(ret,.a.b,$,U)`, and
    forward run 3 reports the vulnerability in the NORMAL layer, and nothing else. -/
theorem conv_found : F3 (.edge 1 A3 1 G3U) ∧ F3 (.vuln 0 2 sinkU false) ∧
    ∀ M n s b, F3 (.vuln M n s b) → (M = 0 ∧ n = 2 ∧ s = sinkU ∧ b = false) :=
  ⟨f3_exitU, DRA.vuln f3_r (List.Mem.head _) (by decide),
   fun M n s b h => (by decide : ∀ x ∈ S3.vulns, x.1 = 0 ∧ x.2.1 = 2 ∧ x.2.2.1 = sinkU ∧
     x.2.2.2 = false) (M, n, s, b) (inv3 h)⟩

#print axioms conv_found

end Conv

/-! ## Part 3. Program (iii): A PARTIAL CLEANER of `T` under a `*` premise

```
root():   x.g = source_T();  r = cln(x);  sink_T(r.h.g);                   // method 0
cln(x):   clean(x.f, T); choose {ret.h = x | ret = x.k}; return ret;      // method 1
```
The cleaner is one instruction. The next instruction has two alternative micro-edge flows,
`ret.h = x` and `ret = x.k`; the second does not overwrite the first in this kernel.
Accessors f=4, g=5, h=6, k=7. The cleaner `(arg,.f,at-and-below,T)` is partial for the premise
`(arg,.,*)`: the location `arg.g` is not cleaned, but its mark is `T`. Field limits 1 / 1 / 2.
Run 1: the policy premise continues as `(arg,.,*,*∖{T})` with the request `T`; the answer
`(arg,.,*,T)` carries the flow. The `*` summary `(ret,.,[any],*∖{T})` (the read `x.k`, demand
layer) is handed off as the `*` pattern `(ret,.,[any],*)` (R1: `*∖X` becomes `*`). Backward run 2
enters `cln` with the flow form `(ret,.,*,{},*)` and the concrete `(ret,.h,[any],T)`; at the
reversed cleaner the `*` analysis continues as `*∖{T}` with NO request (R4), and its summary
`(arg,.,[any],*∖{T})` is handed off as the `*` pattern `(arg,.,[any],*)` (R1 again). Forward run 3
has the flow form `(arg,.,*,{},*)` and the concrete `(arg,.g,$,T)` in `cln`: at the cleaner the `*`
analysis continues as `*∖{T}` with no request, so it gives no fact with the mark `T`; the concrete
premise passes the cleaner (its location is not cleaned) and the vulnerability is reported in the
NORMAL layer. -/

namespace Cln

def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def zb : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [5], .exact, .conc 1⟩)]⟩
def callC : Call := ⟨1, [1, 2], [bx, zb], [br]⟩
/-- `clean(x.f, T)`: the mark `T` at `arg.f` and below. -/
def cl : Cleaner := ⟨3, [4], .atAndBelow, some 1⟩
/-- One statement with alternatives `ret.h = arg` and `ret = arg.k`. -/
def cs : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨4, [6], st, .star⟩), (⟨3, [7], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def P : Program := ⟨fun _ => 0, fun _ => 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callC, 2), (1, 0, .clean cl, 1), (1, 1, .stmt cs, 2)]⟩
def sinkT : PFact := ⟨2, [6, 5], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkT)]
abbrev Pb : Program := Program.rev P

theorem hE00 : (0, 0, Instr.stmt src, 1) ∈ P.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callC, 2) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.clean cl, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hE11 : (1, 1, Instr.stmt cs, 2) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem hb_c : (0, 2, Instr.call (Call.rev callC), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem hb_cl : (1, 1, Instr.clean cl, 0) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hb_s : (1, 2, Instr.stmt (Stmt.rev cs), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

#print axioms hE00
#print axioms hE01
#print axioms hE10
#print axioms hE11
#print axioms hb_c
#print axioms hb_cl
#print axioms hb_s

/-! ### The named facts -/

def X1 : AFact := ⟨⟨1, [5], .exact, .conc 1⟩, false⟩
def A1 : PFact := ⟨3, [5], .exact, .conc 1⟩
def Jw : PFact := ⟨3, [], st, .star⟩
def JT : PFact := ⟨3, [], st, .conc 1⟩
/-- The policy premise after the cleaner: `(arg,.,*,*∖{T})`. -/
def Wc : AFact := ⟨⟨3, [], st, .starEx [1]⟩, false⟩
/-- The run-1 summaries: the `*` read (demand layer, mark `*∖{T}`) and the concrete one. -/
def Gx : AFact := ⟨⟨4, [], .any, .starEx [1]⟩, true⟩
def GT : AFact := ⟨⟨4, [6], .any, .conc 1⟩, true⟩
/-- Backward run 2. -/
def RqT : PFact := ⟨4, [6], .any, .conc 1⟩
def JbS : PFact := ⟨4, [], st, .star⟩
def JbT : PFact := ⟨4, [6], .any, .conc 1⟩
def GbS1 : AFact := ⟨⟨3, [], .any, .star⟩, true⟩
def GbS0 : AFact := ⟨⟨3, [], .any, .starEx [1]⟩, true⟩
def GbT0 : AFact := ⟨⟨3, [], .any, .conc 1⟩, true⟩
/-- Forward run 3. -/
def X3 : AFact := ⟨⟨1, [5], .exact, .conc 1⟩, false⟩
def A3 : PFact := ⟨3, [5], .exact, .conc 1⟩
def G3T : AFact := ⟨⟨4, [6, 5], .exact, .conc 1⟩, false⟩
def dS : DemandEdge := normDem ⟨Gx.fact, some Jw⟩
def dT : DemandEdge := normDem ⟨GT.fact, some JT⟩
def dS3 : DemandEdge := normDem ⟨GbS0.fact, some JbS⟩
def dT3 : DemandEdge := normDem ⟨GbT0.fact, some JbT⟩

/-! ### The complete closures -/

def S1 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [5], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], (.star (.set [])), (.starEx [1])⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨4, [6], (.star (.set [])), (.starEx [1])⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨4, [], .any, (.starEx [1])⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 0, ⟨⟨3, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 1, ⟨⟨3, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 2, ⟨⟨4, [6], .any, (.conc 1)⟩, true⟩),
    (1, ⟨3, [], (.star (.set [])), (.conc 1)⟩, 2, ⟨⟨4, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [6], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [], .any, (.conc 1)⟩, true⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩)]
  reqs := [(1, ⟨3, [], (.star (.set [])), .star⟩, 1)]
  vulns := [(0, 2, ⟨2, [6, 5], .exact, (.conc 1)⟩, true)]

def H1L : List (MethodId × DemandEdge) := [(0, ⟨⟨2, [6], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (0, ⟨⟨2, [], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (1, ⟨⟨4, [], .any, .star⟩, some ⟨3, [], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨4, [6], .any, (.conc 1)⟩, some ⟨3, [], (.star (.set [])), (.conc 1)⟩⟩),
    (1, ⟨⟨4, [], .any, (.conc 1)⟩, some ⟨3, [], (.star (.set [])), (.conc 1)⟩⟩)]

def RB1L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨4, [6], (.star (.set [])), .star⟩, ⟨⟨3, [], (.star (.set [])), (.starEx [1])⟩, false⟩))]

def S2 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [6], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 2, ⟨⟨4, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩, 2, ⟨⟨4, [6], .any, (.conc 1)⟩, true⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], .any, .star⟩, true⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [7], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩, 1, ⟨⟨3, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩, 1, ⟨⟨3, [7], .any, (.conc 1)⟩, true⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], .any, (.starEx [1])⟩, true⟩),
    (1, ⟨4, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [7], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩, 0, ⟨⟨3, [], .any, (.conc 1)⟩, true⟩),
    (1, ⟨4, [6], .any, (.conc 1)⟩, 0, ⟨⟨3, [7], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [7], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [7], .any, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [], .any, (.conc 1)⟩, true⟩)]
  addeds := [(1, ⟨4, [6], .any, (.conc 1)⟩)]
  reqs := []
  vulns := []

def D3L : List (MethodId × DemandEdge) := [(0, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (1, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (0, ⟨⟨1, [7], .any, (.conc 1)⟩, none⟩),
    (0, ⟨⟨1, [], .any, (.conc 1)⟩, none⟩),
    (1, ⟨⟨3, [], .any, .star⟩, some ⟨4, [], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨3, [], .any, (.conc 1)⟩, some ⟨4, [6], .any, (.conc 1)⟩⟩),
    (1, ⟨⟨3, [7], .any, (.conc 1)⟩, some ⟨4, [6], .any, (.conc 1)⟩⟩)]

def RC3L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨3, [], (.star (.set [])), .star⟩, ⟨⟨4, [6], (.star (.set [])), (.starEx [1])⟩, false⟩)),
    (1, (⟨3, [7], (.star (.set [])), .star⟩, ⟨⟨4, [], (.star (.set [])), .star⟩, false⟩))]

def S3 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [5], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩, 0, ⟨⟨3, [5], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], (.star (.set [])), (.starEx [1])⟩, false⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩, 1, ⟨⟨3, [5], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨4, [6], (.star (.set [])), (.starEx [1])⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨4, [], .any, (.starEx [1])⟩, true⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩, 2, ⟨⟨4, [6, 5], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [6, 5], .exact, (.conc 1)⟩, false⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [5], .exact, (.conc 1)⟩)]
  reqs := []
  vulns := [(0, 2, ⟨2, [6, 5], .exact, (.conc 1)⟩, false)]

abbrev R1 : Obj → Prop := D P cnt 1 policy1 sinks [0]

theorem closed1 : ClosedD P cnt 1 sinks [0] S1 := by decide

/-- THE COMPLETE FORWARD RUN 1. -/
theorem inv1 {o : Obj} (h : R1 o) : S1.Inv o := closedD_sound P cnt 1 sinks [0] S1 closed1 h

#print axioms closed1
#print axioms inv1

/-- The forward hand-off of run 1 (normalized), bounded by the list. -/
theorem handFA1_bound {m : MethodId} {d : DemandEdge} (h : handFA P R1 pubD m d) : (m, d) ∈ H1L := by
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, hpub, rfl⟩, rfl⟩ := h
  have hp : g' = g := hpub
  subst hp
  exact (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
    (x.1, normDem ⟨x.2.2.2.fact, some x.2.1⟩) ∈ H1L) (m, j, P.exit m, g') (inv1 hg) rfl hnc

#print axioms handFA1_bound

/-- The backward records: the reversals of the crossable exit edges of run 1. -/
def recsB1 : Recs := fun m y => ∃ x : PFact × AFact, R1 (.init m x.1) ∧
  R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2 ∧ y = revRec x

theorem recsB1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

#print axioms recsB1_bound

abbrev B2 : Obj → Prop := DBW Pb cnt 1 (handFA P R1 pubD) recsB1 [0] sinks

theorem closed2 : ClosedBA Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide

/-- THE COMPLETE BACKWARD RUN 2. -/
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (handFA1_bound hd)) (fun _ _ hx => recsB1_bound hx) h

#print axioms closed2
#print axioms inv2

/-- The demand of forward run 3. -/
def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))

theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1) (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc (m, dd)
      (handFA1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

#print axioms dem3_bound

/-- The records of forward run 3: the crossable exit edges of run 1 and the reversed normal
    backward summaries with a crossable reversal. -/
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

#print axioms rc3_bound

abbrev F3 : Obj → Prop := DRW P cnt 2 dem3 rc3 sinks [0]

theorem closed3 : ClosedRA P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide

/-- THE COMPLETE FORWARD RUN 3. -/
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h

#print axioms closed3
#print axioms inv3

/-! ### The derivations -/

theorem r1_e00 : R1 (.edge 0 zeroFact 0 Backward.zeroAF) := D.start (D.root (List.Mem.head _))
theorem r1_x1 : R1 (.edge 0 zeroFact 1 X1) := D.step r1_e00 (s := src) hE00 (by decide)
theorem r1_add : R1 (.added 1 A1) :=
  D.added (c := callC) (e := bx) (a := ⟨A1, false⟩) r1_x1 hE01 (List.Mem.head _) (by decide)
theorem r1_initW : R1 (.init 1 Jw) := by
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinks) (roots := [0])
    (P := P) r1_add
  have hp : policy1 1 A1 = Jw := by decide
  rw [hp] at h
  exact h
/-- RUN 1 AT THE PARTIAL CLEANER: the policy premise continues as `*∖{T}` and requests `T`. -/
theorem r1_clean : R1 (.edge 1 Jw 1 Wc) := D.clean (D.start r1_initW) (cl := cl) hE10 (by decide)
theorem r1_req : R1 (.req 1 Jw 1) := D.reqClean (D.start r1_initW) (cl := cl) hE10 (by decide)
theorem r1_initT : R1 (.init 1 JT) := by
  have h := D.answer (P := P) (counted := cnt) (L := 1) (α := policy1) (sinks := sinks)
    (roots := [0]) r1_req r1_add rfl (by decide)
  have hp : answerInit Jw A1 1 = JT := by decide
  rw [hp] at h
  exact h
theorem r1_exitS : R1 (.edge 1 Jw 2 Gx) := D.step r1_clean (s := cs) hE11 (by decide)
theorem r1_exitT : R1 (.edge 1 JT 2 GT) :=
  D.step (D.clean (D.start r1_initT) (cl := cl) (f' := ⟨⟨3, [], .any, .conc 1⟩, true⟩) hE10
    (by decide)) (s := cs) hE11 (by decide)
theorem handFA1_S : handFA P R1 pubD 1 dS :=
  ⟨_, ⟨Jw, Gx, Gx, r1_initW, r1_exitS, by decide, rfl, rfl⟩, rfl⟩
theorem handFA1_T : handFA P R1 pubD 1 dT :=
  ⟨_, ⟨JT, GT, GT, r1_initT, r1_exitT, by decide, rfl, rfl⟩, rfl⟩

#print axioms r1_e00
#print axioms r1_x1
#print axioms r1_add
#print axioms r1_initW
#print axioms r1_clean
#print axioms r1_req
#print axioms r1_initT
#print axioms r1_exitS
#print axioms r1_exitT
#print axioms handFA1_S
#print axioms handFA1_T

theorem b2_e02 : B2 (.edge 0 zeroFact 2 Backward.zeroAF) := DBA.start (DBA.root (List.Mem.head _))
theorem b2_add : B2 (.added 1 RqT) :=
  DBA.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨RqT, true⟩)
    (DBA.seed (s := sinkT) (List.Mem.head _) b2_e02) hb_c (List.Mem.head _) (by decide)
theorem b2_initS : B2 (.init 1 JbS) := DBA.initR (d := dS) b2_add handFA1_S (by decide)
theorem b2_initT : B2 (.init 1 JbT) := DBA.initR (d := dT) b2_add handFA1_T (by decide)
theorem b2_s1 : B2 (.edge 1 JbS 1 GbS1) := DBA.step (DBA.start b2_initS) hb_s (by decide)
/-- The backward `*` analysis at the reversed cleaner: `*∖{T}`, no request. -/
theorem b2_exitS : B2 (.edge 1 JbS 0 GbS0) := DBA.clean b2_s1 hb_cl (by decide)
theorem b2_exitT : B2 (.edge 1 JbT 0 GbT0) :=
  DBA.clean (DBA.step (DBA.start b2_initT) (f' := ⟨⟨3, [], .any, .conc 1⟩, true⟩) hb_s (by decide))
    hb_cl (by decide)
theorem dem3_S : dem3 1 dS3 :=
  ⟨_, Or.inr (Or.inr ⟨JbS, GbS0, GbS0, b2_initS, by decide, b2_exitS, by decide,
    ⟨dS, handFA1_S, by decide⟩, rfl⟩), rfl⟩
theorem dem3_T : dem3 1 dT3 :=
  ⟨_, Or.inr (Or.inr ⟨JbT, GbT0, GbT0, b2_initT, by decide, b2_exitT, by decide,
    ⟨dT, handFA1_T, by decide⟩, rfl⟩), rfl⟩

#print axioms b2_e02
#print axioms b2_add
#print axioms b2_initS
#print axioms b2_initT
#print axioms b2_s1
#print axioms b2_exitS
#print axioms b2_exitT
#print axioms dem3_S
#print axioms dem3_T

theorem f3_e00 : F3 (.edge 0 zeroFact 0 Backward.zeroAF) := DRA.start (DRA.root (List.Mem.head _))
theorem f3_x1 : F3 (.edge 0 zeroFact 1 X3) := DRA.step f3_e00 (s := src) hE00 (by decide)
theorem f3_add : F3 (.added 1 A3) :=
  DRA.added (c := callC) (e := bx) (a := ⟨A3, false⟩) f3_x1 hE01 (List.Mem.head _) (by decide)
theorem f3_initS : F3 (.init 1 Jw) := DRA.initR (d := dS3) f3_add dem3_S (by decide)
theorem f3_initT : F3 (.init 1 A3) := DRA.initR (d := dT3) f3_add dem3_T (by decide)
/-- Forward run 3 at the partial cleaner: the flow form continues as `*∖{T}`, with no request. -/
theorem f3_cleanS : F3 (.edge 1 Jw 1 Wc) := DRA.clean (DRA.start f3_initS) (cl := cl) hE10 (by decide)
theorem f3_exitT : F3 (.edge 1 A3 2 G3T) :=
  DRA.step (DRA.clean (DRA.start f3_initT) (cl := cl) (f' := ⟨A3, false⟩) hE10 (by decide))
    (s := cs) hE11 (by decide)
theorem f3_r : F3 (.edge 0 zeroFact 2 (limitF cnt 2 ⟨⟨2, [6, 5], .exact, .conc 1⟩, false⟩)) :=
  DRA.ret (c := callC) (e1 := bx) (a := ⟨A3, false⟩) (j := A3) (g := G3T) (d := dT3) (g' := G3T)
    (r := G3T) (e2 := br) f3_x1 hE01 (List.Mem.head _) (by decide) f3_initT f3_exitT dem3_T
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms f3_e00
#print axioms f3_x1
#print axioms f3_add
#print axioms f3_initS
#print axioms f3_initT
#print axioms f3_cleanS
#print axioms f3_exitT
#print axioms f3_r

/-! ### The results of program (iii) -/

/-- RUN 1 AT THE PARTIAL CLEANER: the policy premise continues as `*∖{T}` with the request `T`, and
    the answer `(arg,.,*,T)` gives the concrete summary (not crossable: a demand edge). -/
theorem cln_run1 : R1 (.edge 1 Jw 1 Wc) ∧ R1 (.req 1 Jw 1) ∧ R1 (.init 1 JT) ∧
    R1 (.edge 1 JT 2 GT) ∧ ¬ Cross JT GT :=
  ⟨r1_clean, r1_req, r1_initT, r1_exitT, by decide⟩

#print axioms cln_run1

/-- R1 ON THE FORWARD HAND-OFF: the `*∖{T}` summary gives the `*` pattern `(ret,.,[any],*)`. Without
    the normalization the requirement with the mark `T` would not enter it (`emitM` gives nothing);
    with it, the requirement emits the flow form. -/
theorem cln_norm_fwd : handFA P R1 pubD 1 dS ∧ dS.din = ⟨4, [], .any, .star⟩ ∧
    emitM Gx.fact RqT = none ∧ emitW dS.din RqT = some JbS :=
  ⟨handFA1_S, rfl, by decide, by decide⟩

#print axioms cln_norm_fwd

/-- BACKWARD RUN 2 AT THE REVERSED CLEANER: the `*` analysis continues as `*∖{T}` (the cleaner
    would request `T`: `cleanRes … .reqs = [1]`), the run has no request; R1 on the backward hand-off
    gives the `*` pattern `(arg,.,[any],*)` of forward run 3. -/
theorem cln_b2 : B2 (.edge 1 JbS 0 GbS0) ∧ (cleanRes cl GbS1).reqs = [1] ∧
    (∀ M i t, ¬ B2 (.req M i t)) ∧ dem3 1 dS3 ∧ dS3.din = ⟨3, [], .any, .star⟩ ∧ dem3 1 dT3 :=
  ⟨b2_exitS, by decide, fun _ _ _ => DBA_no_req Pb cnt 1 (handFA P R1 pubD) emitW satW restrictI
    recsB1 [] [0] sinks true, dem3_S, rfl, dem3_T⟩

#print axioms cln_b2

/-- FORWARD RUN 3: `cln` has the flow form and the concrete premise; at the cleaner the flow form
    continues as `*∖{T}` with no request (`cleanRes … .reqs = [1]` is dropped), so the `*` analysis
    gives no fact with the mark `T`. -/
theorem cln_f3 : F3 (.init 1 Jw) ∧ F3 (.init 1 A3) ∧
    (∀ j, F3 (.init 1 j) → j = zeroFact ∨ j = Jw ∨ j = A3) ∧ F3 (.edge 1 Jw 1 Wc) ∧
    (cleanRes cl (startFact Jw)).reqs = [1] ∧ (∀ M i t, ¬ F3 (.req M i t)) ∧
    (∀ n g, F3 (.edge 1 Jw n g) → g.fact.mark ≠ .conc 1) :=
  ⟨f3_initS, f3_initT,
   fun j h => (by decide : ∀ x ∈ S3.inits, x.1 = 1 → x.2 = zeroFact ∨ x.2 = Jw ∨ x.2 = A3)
     (1, j) (inv3 h) rfl,
   f3_cleanS, by decide, fun _ _ _ => DRA_no_req P cnt 2 dem3 emitW satW restrictI rc3 sinks [0],
   fun n g h => (by decide : ∀ x ∈ S3.edges, x.1 = 1 → x.2.1 = Jw → x.2.2.2.fact.mark ≠ .conc 1)
     (1, Jw, n, g) (inv3 h) rfl rfl⟩

#print axioms cln_f3

/-- THE FLOW IS FOUND THROUGH THE CONCRETE PATTERN, in the NORMAL layer, and nothing else. -/
theorem cln_found : F3 (.edge 1 A3 2 G3T) ∧ F3 (.vuln 0 2 sinkT false) ∧
    ∀ M n s b, F3 (.vuln M n s b) → (M = 0 ∧ n = 2 ∧ s = sinkT ∧ b = false) :=
  ⟨f3_exitT, DRA.vuln f3_r (List.Mem.head _) (by decide),
   fun M n s b h => (by decide : ∀ x ∈ S3.vulns, x.1 = 0 ∧ x.2.1 = 2 ∧ x.2.2.1 = sinkT ∧
     x.2.2.2 = false) (M, n, s, b) (inv3 h)⟩

#print axioms cln_found

end Cln

/-! ## Part 4. Program (iv): THE COUNTEREXAMPLE SEARCH for R6 (a concrete need behind a record)

```
root():  x = source_T();  r = A(x);  sink_U(r.a.a);                       // method 0
A(p):    q = E(p);  w.a.a = q;  w.a.b = p;  return w;                     // method 1
E(e):    f = TU(e);  return f;                                            // method 2
```
Accessors a=1, b=2. Bases zero=0, x=1, r=2, p=3, q=4, w=5, e=6, f=7. Marks T=1, U=2. Field
limits 1 / 1 / 2. The configuration the search asks for: run 1 answers a request in the callee `E`,
and the answer's summary `(e,.,$,T) → (f,.,$,U)` is CROSSABLE, so it becomes a RECORD and `E` gets no
demand edge after run 1 (`E` is never analysed again). Its caller `A` has a `*` pattern too (the
mark-agnostic write `w.a.b = p`, cut at L=1). Can a `*` analysis need the concrete flow through `E`
and not get it?
  * Backward run 2 enters `A` with the flow form `(w,.a,*,{},*)` and with the concrete
    `(w,.a,[any],U)`. The `*` requirement `(f,.,[any],*)` that the flow form gives to `E` does not
    satisfy `E`'s concrete record (`satW`, `applicable` false): the BACKWARD WEAKENING LOSES the path
    through `E` in the `*` analysis. The concrete requirement crosses `E` by the record and gives
    `(p,.,$,T)`: the concrete pattern of `A` survives.
  * Forward run 3 enters `A` with the flow form `(p,.,*,{},*)` AND the concrete `(p,.,$,T)`. The `*`
    analysis cannot cross `E` (the record needs `T`; `E` has no pattern), so it gives no `U`; the
    concrete premise crosses `E` by the record and the vulnerability is reported in the NORMAL layer.
No counterexample: the run-1 request climbs from `E` through EVERY abstract caller (`A`) to the first
concrete added fact, so every method on that chain gets a concrete premise in run 1; its summary is
a record (crossed with the concrete mark) or a concrete demand edge (kept concrete by both
hand-offs, `emitW` copies a concrete mark). The general argument is in `log-A1.md`. -/

namespace Nest

def zb : MicroEdge := (⟨0, [], st, .star⟩, ⟨0, [], st, .star⟩)
def xp : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def wr : MicroEdge := (⟨5, [], st, .star⟩, ⟨2, [], st, .star⟩)
def pe : MicroEdge := (⟨3, [], st, .star⟩, ⟨6, [], st, .star⟩)
def fq : MicroEdge := (⟨7, [], st, .star⟩, ⟨4, [], st, .star⟩)
def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [], .exact, .conc 1⟩)]⟩
def callA : Call := ⟨1, [1, 2], [xp, zb], [wr]⟩
def callE : Call := ⟨2, [4], [pe, zb], [fq]⟩
/-- `w.a.a = q; w.a.b = p` as one statement. -/
def s2 : Stmt := ⟨[3, 4, 5], [(⟨4, [], st, .star⟩, ⟨5, [1, 1], st, .star⟩),
  (⟨3, [], st, .star⟩, ⟨5, [1, 2], st, .star⟩)]⟩
/-- `f = TU(e)`: the pass rule with the concrete premise mark `T`. -/
def tu : Stmt := ⟨[6, 7], [(⟨6, [], st, .conc 1⟩, ⟨7, [], st, .conc 2⟩)]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 2 then 1 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callA, 2), (1, 0, .call callE, 1), (1, 1, .stmt s2, 2),
   (2, 0, .stmt tu, 1)]⟩
def sinkU : PFact := ⟨2, [1, 1], .exact, .conc 2⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkU)]
abbrev Pb : Program := Program.rev P

theorem hE00 : (0, 0, Instr.stmt src, 1) ∈ P.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callA, 2) ∈ P.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.call callE, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hE11 : (1, 1, Instr.stmt s2, 2) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem hE20 : (2, 0, Instr.stmt tu, 1) ∈ P.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
theorem hb_cA : (0, 2, Instr.call (Call.rev callA), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.head _)
theorem hb_cE : (1, 1, Instr.call (Call.rev callE), 0) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hb_s2 : (1, 2, Instr.stmt (Stmt.rev s2), 1) ∈ Pb.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

#print axioms hE00
#print axioms hE01
#print axioms hE10
#print axioms hE11
#print axioms hE20
#print axioms hb_cA
#print axioms hb_cE
#print axioms hb_s2

/-! ### The named facts -/

def X1 : AFact := ⟨⟨1, [], .exact, .conc 1⟩, false⟩
def A1 : PFact := ⟨3, [], .exact, .conc 1⟩
def JwA : PFact := ⟨3, [], st, .star⟩
def JwE : PFact := ⟨6, [], st, .star⟩
/-- The added facts of `E`: from the flow premise of `A` (mark `*`) and from its answer (mark `T`). -/
def AE : PFact := ⟨6, [], st, .star⟩
def AET : PFact := ⟨6, [], .exact, .conc 1⟩
/-- The answers of run 1. -/
def JTA : PFact := ⟨3, [], .exact, .conc 1⟩
def JTE : PFact := ⟨6, [], .exact, .conc 1⟩
/-- The summary of `E`'s answer (a record) and the summaries of `A` (demand layer). -/
def GE : AFact := ⟨⟨7, [], .exact, .conc 2⟩, false⟩
def GAS : AFact := ⟨⟨5, [1], .any, .star⟩, true⟩
def GAU : AFact := ⟨⟨5, [1], .any, .conc 2⟩, true⟩
/-- Backward run 2. -/
def RqA : PFact := ⟨5, [1], .any, .conc 2⟩
def JbS : PFact := ⟨5, [1], st, .star⟩
def JbU : PFact := ⟨5, [1], .any, .conc 2⟩
def GbS0 : AFact := ⟨⟨3, [], .any, .star⟩, true⟩
def GbU0 : AFact := ⟨⟨3, [], .exact, .conc 1⟩, true⟩
/-- The `*` requirement that the flow form of `A` gives to `E`. -/
def RqES : PFact := ⟨7, [], .any, .star⟩
/-- Forward run 3. -/
def X3 : AFact := ⟨⟨1, [], .exact, .conc 1⟩, false⟩
def A3 : PFact := ⟨3, [], .exact, .conc 1⟩
def Q3 : AFact := ⟨⟨4, [], .exact, .conc 2⟩, false⟩
def W3 : AFact := ⟨⟨5, [1, 1], .exact, .conc 2⟩, false⟩
def dS : DemandEdge := normDem ⟨GAS.fact, some JwA⟩
def dU : DemandEdge := normDem ⟨GAU.fact, some JTA⟩
def dS3 : DemandEdge := normDem ⟨GbS0.fact, some JbS⟩
def dT3 : DemandEdge := normDem ⟨GbU0.fact, some JbU⟩

/-! ### The complete closures -/

def S1 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩),
    (2, ⟨6, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩),
    (2, ⟨6, [], .exact, (.conc 1)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨5, [1], .any, .star⟩, true⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (2, ⟨6, [], (.star (.set [])), .star⟩, 0, ⟨⟨6, [], (.star (.set [])), .star⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1], .any, (.conc 1)⟩, true⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 0, ⟨⟨3, [], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 1, ⟨⟨3, [], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 2, ⟨⟨5, [1], .any, (.conc 1)⟩, true⟩),
    (2, ⟨6, [], .exact, (.conc 1)⟩, 0, ⟨⟨6, [], .exact, (.conc 1)⟩, false⟩),
    (2, ⟨6, [], .exact, (.conc 1)⟩, 1, ⟨⟨7, [], .exact, (.conc 2)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 1, ⟨⟨4, [], .exact, (.conc 2)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 2, ⟨⟨5, [1], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1], .any, (.conc 2)⟩, true⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩),
    (2, ⟨6, [], (.star (.set [])), .star⟩),
    (2, ⟨6, [], .exact, (.conc 1)⟩)]
  reqs := [(2, ⟨6, [], (.star (.set [])), .star⟩, 1),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1)]
  vulns := [(0, 2, ⟨2, [1, 1], .exact, (.conc 2)⟩, true)]

def H1L : List (MethodId × DemandEdge) := [(0, ⟨⟨2, [1], .any, (.conc 1)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (0, ⟨⟨2, [1], .any, (.conc 2)⟩, some ⟨0, [], .exact, (.conc 0)⟩⟩),
    (1, ⟨⟨5, [1], .any, .star⟩, some ⟨3, [], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨5, [1], .any, (.conc 1)⟩, some ⟨3, [], .exact, (.conc 1)⟩⟩),
    (1, ⟨⟨5, [1], .any, (.conc 2)⟩, some ⟨3, [], .exact, (.conc 1)⟩⟩)]

def RB1L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (2, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (2, (⟨7, [], .exact, (.conc 2)⟩, ⟨⟨6, [], .exact, (.conc 1)⟩, false⟩))]

def S2 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨5, [1], (.star (.set [])), .star⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨5, [1], (.star (.set [])), .star⟩, 2, ⟨⟨5, [1], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩, 2, ⟨⟨5, [1], .any, (.conc 2)⟩, true⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨5, [1], (.star (.set [])), .star⟩, 1, ⟨⟨4, [], .any, .star⟩, true⟩),
    (1, ⟨5, [1], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], .any, .star⟩, true⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩, 1, ⟨⟨4, [], .any, (.conc 2)⟩, true⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩, 1, ⟨⟨3, [], .any, (.conc 2)⟩, true⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨5, [1], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], .any, .star⟩, true⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩, 0, ⟨⟨3, [], .exact, (.conc 1)⟩, true⟩),
    (1, ⟨5, [1], .any, (.conc 2)⟩, 0, ⟨⟨3, [], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .exact, (.conc 1)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [], .any, (.conc 2)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, true⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨1, [], .exact, (.conc 1)⟩, true⟩)]
  addeds := [(1, ⟨5, [1], .any, (.conc 2)⟩),
    (2, ⟨7, [], .any, .star⟩),
    (2, ⟨7, [], .any, (.conc 2)⟩)]
  reqs := []
  vulns := []

def D3L : List (MethodId × DemandEdge) := [(0, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (1, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (2, ⟨⟨0, [], .exact, (.conc 0)⟩, none⟩),
    (0, ⟨⟨1, [], .any, (.conc 2)⟩, none⟩),
    (0, ⟨⟨1, [], .exact, (.conc 1)⟩, none⟩),
    (1, ⟨⟨3, [], .any, .star⟩, some ⟨5, [1], (.star (.set [])), .star⟩⟩),
    (1, ⟨⟨3, [], .exact, (.conc 1)⟩, some ⟨5, [1], .any, (.conc 2)⟩⟩),
    (1, ⟨⟨3, [], .any, (.conc 2)⟩, some ⟨5, [1], .any, (.conc 2)⟩⟩)]

def RC3L : List (MethodId × (PFact × AFact)) := [(0, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (1, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (2, (⟨0, [], .exact, (.conc 0)⟩, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)),
    (2, (⟨6, [], .exact, (.conc 1)⟩, ⟨⟨7, [], .exact, (.conc 2)⟩, false⟩))]

def S3 : LS where
  inits := [(0, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩)]
  edges := [(0, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨1, [], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 0, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 0, ⟨⟨3, [], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 1, ⟨⟨3, [], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 1, ⟨⟨3, [], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 1, ⟨⟨4, [], .exact, (.conc 2)⟩, false⟩),
    (1, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (1, ⟨3, [], (.star (.set [])), .star⟩, 2, ⟨⟨5, [1, 2], (.star (.set [])), .star⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 2, ⟨⟨5, [1, 2], .exact, (.conc 1)⟩, false⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩, 2, ⟨⟨5, [1, 1], .exact, (.conc 2)⟩, false⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 0, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1, 2], .exact, (.conc 1)⟩, false⟩),
    (0, ⟨0, [], .exact, (.conc 0)⟩, 2, ⟨⟨2, [1, 1], .exact, (.conc 2)⟩, false⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩, 1, ⟨⟨0, [], .exact, (.conc 0)⟩, false⟩)]
  addeds := [(1, ⟨0, [], .exact, (.conc 0)⟩),
    (1, ⟨3, [], .exact, (.conc 1)⟩),
    (2, ⟨0, [], .exact, (.conc 0)⟩),
    (2, ⟨6, [], (.star (.set [])), .star⟩),
    (2, ⟨6, [], .exact, (.conc 1)⟩)]
  reqs := []
  vulns := [(0, 2, ⟨2, [1, 1], .exact, (.conc 2)⟩, false)]

abbrev R1 : Obj → Prop := D P cnt 1 policy1 sinks [0]

theorem closed1 : ClosedD P cnt 1 sinks [0] S1 := by decide

/-- THE COMPLETE FORWARD RUN 1. -/
theorem inv1 {o : Obj} (h : R1 o) : S1.Inv o := closedD_sound P cnt 1 sinks [0] S1 closed1 h

#print axioms closed1
#print axioms inv1

/-- The forward hand-off of run 1 (normalized), bounded by the list. -/
theorem handFA1_bound {m : MethodId} {d : DemandEdge} (h : handFA P R1 pubD m d) : (m, d) ∈ H1L := by
  obtain ⟨d0, ⟨j, g, g', _, hg, hnc, hpub, rfl⟩, rfl⟩ := h
  have hp : g' = g := hpub
  subst hp
  exact (by decide : ∀ x ∈ S1.edges, x.2.2.1 = P.exit x.1 → ¬ Cross x.2.1 x.2.2.2 →
    (x.1, normDem ⟨x.2.2.2.fact, some x.2.1⟩) ∈ H1L) (m, j, P.exit m, g') (inv1 hg) rfl hnc

#print axioms handFA1_bound

/-- The backward records: the reversals of the crossable exit edges of run 1. -/
def recsB1 : Recs := fun m y => ∃ x : PFact × AFact, R1 (.init m x.1) ∧
  R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2 ∧ y = revRec x

theorem recsB1_bound {m : MethodId} {y : PFact × AFact} (h : recsB1 m y) : (m, y) ∈ RB1L := by
  obtain ⟨x, _, hx, hc, rfl⟩ := h
  exact (by decide : ∀ e ∈ S1.edges, e.2.2.1 = P.exit e.1 → Cross e.2.1 e.2.2.2 →
    (e.1, revRec (e.2.1, e.2.2.2)) ∈ RB1L) (m, x.1, P.exit m, x.2) (inv1 hx) rfl hc

#print axioms recsB1_bound

abbrev B2 : Obj → Prop := DBW Pb cnt 1 (handFA P R1 pubD) recsB1 [0] sinks

theorem closed2 : ClosedBA Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 := by decide

/-- THE COMPLETE BACKWARD RUN 2. -/
theorem inv2 {o : Obj} (h : B2 o) : S2.Inv o :=
  closedBA_sound Pb cnt 1 H1L emitW satW restrictI RB1L [] [0] sinks S2 closed2
    (fun _ _ hd => mem_demFor (handFA1_bound hd)) (fun _ _ hx => recsB1_bound hx) h

#print axioms closed2
#print axioms inv2

/-- The demand of forward run 3. -/
def dem3 : MethodId → DemandEdge → Prop := demOfNA Pb B2 (pubR (handFA P R1 pubD))

theorem dem3_bound {m : MethodId} {d : DemandEdge} (h : dem3 m d) : d ∈ demFor D3L m := by
  obtain ⟨d0, h0, rfl⟩ := h
  rcases h0 with rfl | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, hnc, ⟨dd, hdd, hres⟩, rfl⟩
  · exact zero_mem_demFor D3L m
  · exact (by decide : ∀ x ∈ S2.edges, x.2.1 = zeroFact → x.2.2.1 = Pb.exit x.1 →
      normDem ⟨x.2.2.2.fact, none⟩ ∈ demFor D3L x.1) (m, zeroFact, Pb.exit m, g) (inv2 hg) rfl rfl
  · exact (by decide : ∀ y ∈ S2.inits, y.2 ≠ zeroFact → ∀ z ∈ S2.edges, z.1 = y.1 → z.2.1 = y.2 →
      z.2.2.1 = Pb.exit y.1 → ¬ CrossB y.2 z.2.2.2 → ∀ dd ∈ H1L, dd.1 = y.1 →
      ∀ g' ∈ (restrictI y.2 z.2.2.2 dd.2).toList, normDem ⟨g'.fact, some y.2⟩ ∈ demFor D3L y.1)
      (m, jb) (inv2 hjb) hne (m, jb, Pb.exit m, gb) (inv2 hgb) rfl rfl rfl hnc (m, dd)
      (handFA1_bound hdd) rfl gb' (RCases.mem_toList_of_eq_some hres)

#print axioms dem3_bound

/-- The records of forward run 3: the crossable exit edges of run 1 and the reversed normal
    backward summaries with a crossable reversal. -/
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

#print axioms rc3_bound

abbrev F3 : Obj → Prop := DRW P cnt 2 dem3 rc3 sinks [0]

theorem closed3 : ClosedRA P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 := by decide

/-- THE COMPLETE FORWARD RUN 3. -/
theorem inv3 {o : Obj} (h : F3 o) : S3.Inv o :=
  closedRA_sound P cnt 2 D3L emitW satW restrictI RC3L sinks [0] S3 closed3
    (fun _ _ hd => dem3_bound hd) (fun _ _ hx => rc3_bound hx) h

#print axioms closed3
#print axioms inv3

/-! ### The derivations -/

theorem r1_e00 : R1 (.edge 0 zeroFact 0 Backward.zeroAF) := D.start (D.root (List.Mem.head _))
theorem r1_x1 : R1 (.edge 0 zeroFact 1 X1) := D.step r1_e00 (s := src) hE00 (by decide)
theorem r1_addA : R1 (.added 1 A1) :=
  D.added (c := callA) (e := xp) (a := ⟨A1, false⟩) r1_x1 hE01 (List.Mem.head _) (by decide)
theorem r1_initA : R1 (.init 1 JwA) := by
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinks) (roots := [0])
    (P := P) r1_addA
  have hp : policy1 1 A1 = JwA := by decide
  rw [hp] at h
  exact h
theorem r1_addE : R1 (.added 2 AE) :=
  D.added (c := callE) (e := pe) (a := ⟨AE, false⟩) (D.start r1_initA) hE10 (List.Mem.head _)
    (by decide)
theorem r1_initE : R1 (.init 2 JwE) := by
  have h := D.initA (α := policy1) (counted := cnt) (L := 1) (sinks := sinks) (roots := [0])
    (P := P) r1_addE
  have hp : policy1 2 AE = JwE := by decide
  rw [hp] at h
  exact h
/-- Run 1: the policy premise of `E` requests `T` at the pass rule. -/
theorem r1_reqE : R1 (.req 2 JwE 1) := D.reqStmt (D.start r1_initE) (s := tu) hE20 (by decide)
/-- The request CLIMBS to `A`: `A`'s added fact into `E` has the mark `*`. -/
theorem r1_reqA : R1 (.req 1 JwA 1) :=
  D.reqUp (c := callE) (e := pe) (a := ⟨AE, false⟩) r1_reqE (D.start r1_initA) hE10 rfl
    (List.Mem.head _) (by decide) (by decide) (by decide)
/-- It is answered in `A` (the root's added fact has the mark `T`), then in `E`. -/
theorem r1_initTA : R1 (.init 1 JTA) := by
  have h := D.answer (P := P) (counted := cnt) (L := 1) (α := policy1) (sinks := sinks)
    (roots := [0]) r1_reqA r1_addA rfl (by decide)
  have hp : answerInit JwA A1 1 = JTA := by decide
  rw [hp] at h
  exact h
theorem r1_addET : R1 (.added 2 AET) :=
  D.added (c := callE) (e := pe) (a := ⟨AET, false⟩) (D.start r1_initTA) hE10 (List.Mem.head _)
    (by decide)
theorem r1_initTE : R1 (.init 2 JTE) := by
  have h := D.answer (P := P) (counted := cnt) (L := 1) (α := policy1) (sinks := sinks)
    (roots := [0]) r1_reqE r1_addET rfl (by decide)
  have hp : answerInit JwE AET 1 = JTE := by decide
  rw [hp] at h
  exact h
theorem r1_exitE : R1 (.edge 2 JTE 1 GE) := D.step (D.start r1_initTE) (s := tu) hE20 (by decide)
theorem r1_exitAS : R1 (.edge 1 JwA 2 GAS) :=
  D.step (D.pass (D.start r1_initA) hE10 (by decide)) (s := s2) hE11 (by decide)
theorem r1_qA : R1 (.edge 1 JTA 1 (limitF cnt 1 Q3)) :=
  D.ret (c := callE) (e1 := pe) (a := ⟨AET, false⟩) (j := JTE) (g := GE) (r := GE) (e2 := fq)
    (D.start r1_initTA) hE10 (List.Mem.head _) (by decide) r1_initTE (by decide) r1_exitE
    (by decide) (List.Mem.head _) (by decide)
theorem r1_exitAU : R1 (.edge 1 JTA 2 GAU) := D.step r1_qA (s := s2) hE11 (by decide)
theorem handFA1_S : handFA P R1 pubD 1 dS :=
  ⟨_, ⟨JwA, GAS, GAS, r1_initA, r1_exitAS, by decide, rfl, rfl⟩, rfl⟩
theorem handFA1_U : handFA P R1 pubD 1 dU :=
  ⟨_, ⟨JTA, GAU, GAU, r1_initTA, r1_exitAU, by decide, rfl, rfl⟩, rfl⟩
/-- `E`'s concrete summary is CROSSABLE: a record, not a demand edge. -/
theorem nest_E_cross : Cross JTE GE := by decide

#print axioms r1_e00
#print axioms r1_x1
#print axioms r1_addA
#print axioms r1_initA
#print axioms r1_addE
#print axioms r1_initE
#print axioms r1_reqE
#print axioms r1_reqA
#print axioms r1_initTA
#print axioms r1_addET
#print axioms r1_initTE
#print axioms r1_exitE
#print axioms r1_exitAS
#print axioms r1_qA
#print axioms r1_exitAU
#print axioms handFA1_S
#print axioms handFA1_U
#print axioms nest_E_cross

theorem recsB1_E : recsB1 2 (revRec (JTE, GE)) := ⟨(JTE, GE), r1_initTE, r1_exitE, nest_E_cross, rfl⟩
theorem b2_e02 : B2 (.edge 0 zeroFact 2 Backward.zeroAF) := DBA.start (DBA.root (List.Mem.head _))
theorem b2_addA : B2 (.added 1 RqA) :=
  DBA.added (c := Call.rev callA) (e := revEdge wr.1 wr.2) (a := ⟨RqA, true⟩)
    (DBA.seed (s := sinkU) (List.Mem.head _) b2_e02) hb_cA (List.Mem.head _) (by decide)
theorem b2_initS : B2 (.init 1 JbS) := DBA.initR (d := dS) b2_addA handFA1_S (by decide)
theorem b2_initU : B2 (.init 1 JbU) := DBA.initR (d := dU) b2_addA handFA1_U (by decide)
theorem b2_S1q : B2 (.edge 1 JbS 1 ⟨⟨4, [], .any, .star⟩, true⟩) :=
  DBA.step (DBA.start b2_initS) hb_s2 (by decide)
/-- The flow form of `A` gives the `*` requirement `(f,.,[any],*)` to `E`. -/
theorem b2_addES : B2 (.added 2 RqES) :=
  DBA.added (c := Call.rev callE) (e := revEdge fq.1 fq.2) (a := ⟨RqES, true⟩) b2_S1q hb_cE
    (List.Mem.head _) (by decide)
theorem b2_S0 : B2 (.edge 1 JbS 0 GbS0) :=
  DBA.pass (DBA.step (DBA.start b2_initS) (f' := GbS0) hb_s2 (by decide)) hb_cE (by decide)
/-- The concrete requirement crosses `E` by its record and gives `(p,.,$,T)`. -/
theorem b2_U0 : B2 (.edge 1 JbU 0 GbU0) :=
  DBA.retRec (c := Call.rev callE) (e1 := revEdge fq.1 fq.2) (a := ⟨⟨7, [], .any, .conc 2⟩, true⟩)
    (j := (revRec (JTE, GE)).1) (g := (revRec (JTE, GE)).2) (r := ⟨⟨6, [], .exact, .conc 1⟩, true⟩)
    (e2 := revEdge pe.1 pe.2) (r' := GbU0)
    (DBA.step (DBA.start b2_initU) (f' := ⟨⟨4, [], .any, .conc 2⟩, true⟩) hb_s2 (by decide))
    hb_cE (List.Mem.head _) (by decide) recsB1_E (Or.inl (by decide)) (by decide) (List.Mem.head _)
    (by decide)
theorem dem3_S : dem3 1 dS3 :=
  ⟨_, Or.inr (Or.inr ⟨JbS, GbS0, GbS0, b2_initS, by decide, b2_S0, by decide,
    ⟨dS, handFA1_S, by decide⟩, rfl⟩), rfl⟩
theorem dem3_T : dem3 1 dT3 :=
  ⟨_, Or.inr (Or.inr ⟨JbU, GbU0, GbU0, b2_initU, by decide, b2_U0, by decide,
    ⟨dU, handFA1_U, by decide⟩, rfl⟩), rfl⟩

#print axioms recsB1_E
#print axioms b2_e02
#print axioms b2_addA
#print axioms b2_initS
#print axioms b2_initU
#print axioms b2_S1q
#print axioms b2_addES
#print axioms b2_S0
#print axioms b2_U0
#print axioms dem3_S
#print axioms dem3_T

theorem rc3_E : rc3 2 (JTE, GE) := Or.inl ⟨r1_initTE, r1_exitE, nest_E_cross⟩
theorem f3_e00 : F3 (.edge 0 zeroFact 0 Backward.zeroAF) := DRA.start (DRA.root (List.Mem.head _))
theorem f3_x1 : F3 (.edge 0 zeroFact 1 X3) := DRA.step f3_e00 (s := src) hE00 (by decide)
theorem f3_addA : F3 (.added 1 A3) :=
  DRA.added (c := callA) (e := xp) (a := ⟨A3, false⟩) f3_x1 hE01 (List.Mem.head _) (by decide)
theorem f3_initS : F3 (.init 1 JwA) := DRA.initR (d := dS3) f3_addA dem3_S (by decide)
theorem f3_initT : F3 (.init 1 A3) := DRA.initR (d := dT3) f3_addA dem3_T (by decide)
/-- The flow form of `A` gives the `*` added fact `(e,.,*,{},*)` to `E`. -/
theorem f3_addES : F3 (.added 2 AE) :=
  DRA.added (c := callE) (e := pe) (a := ⟨AE, false⟩) (DRA.start f3_initS) hE10 (List.Mem.head _)
    (by decide)
/-- The concrete premise of `A` crosses `E` by its record. -/
theorem f3_q : F3 (.edge 1 A3 1 (limitF cnt 2 Q3)) :=
  DRA.retRec (c := callE) (e1 := pe) (a := ⟨AET, false⟩) (j := JTE) (g := GE) (r := GE) (e2 := fq)
    (DRA.start f3_initT) hE10 (List.Mem.head _) (by decide) rc3_E (Or.inl (by decide)) (by decide)
    (List.Mem.head _) (by decide)
theorem f3_exitU : F3 (.edge 1 A3 2 W3) := DRA.step f3_q (s := s2) hE11 (by decide)
theorem f3_r : F3 (.edge 0 zeroFact 2 (limitF cnt 2 ⟨⟨2, [1, 1], .exact, .conc 2⟩, false⟩)) :=
  DRA.ret (c := callA) (e1 := xp) (a := ⟨A3, false⟩) (j := A3) (g := W3) (d := dT3) (g' := W3)
    (r := W3) (e2 := wr) f3_x1 hE01 (List.Mem.head _) (by decide) f3_initT f3_exitU dem3_T
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms rc3_E
#print axioms f3_e00
#print axioms f3_x1
#print axioms f3_addA
#print axioms f3_initS
#print axioms f3_initT
#print axioms f3_addES
#print axioms f3_q
#print axioms f3_exitU
#print axioms f3_r

/-! ### The results of program (iv) -/

/-- RUN 1: the request `T` of `E` climbs to `A` and is answered in `A` and in `E`. `E`'s concrete
    summary is crossable (a record); `A`'s concrete summary is not (a demand edge). -/
theorem nest_run1 : R1 (.req 2 JwE 1) ∧ R1 (.req 1 JwA 1) ∧ R1 (.init 1 JTA) ∧
    R1 (.init 2 JTE) ∧ R1 (.edge 2 JTE 1 GE) ∧ Cross JTE GE ∧ R1 (.edge 1 JTA 2 GAU) ∧
    ¬ Cross JTA GAU :=
  ⟨r1_reqE, r1_reqA, r1_initTA, r1_initTE, r1_exitE, nest_E_cross, r1_exitAU, by decide⟩

#print axioms nest_run1

/-- `E` IS NEVER ANALYSED AGAIN after run 1: no hand-off gives it a demand edge, and both restricted
    runs have only the zero fact as an initial fact of `E`. -/
theorem nest_E_never_again : (∀ d, ¬ handFA P R1 pubD 2 d) ∧ (∀ j, B2 (.init 2 j) → j = zeroFact) ∧
    (∀ d, dem3 2 d → d = Backward.zeroDem) ∧ (∀ j, F3 (.init 2 j) → j = zeroFact) :=
  ⟨fun d h => (by decide : ∀ x ∈ H1L, x.1 ≠ 2) (2, d) (handFA1_bound h) rfl,
   fun j h => (by decide : ∀ x ∈ S2.inits, x.1 = 2 → x.2 = zeroFact) (2, j) (inv2 h) rfl,
   fun d h => (by decide : ∀ x ∈ demFor D3L 2, x = Backward.zeroDem) d (dem3_bound h),
   fun j h => (by decide : ∀ x ∈ S3.inits, x.1 = 2 → x.2 = zeroFact) (2, j) (inv3 h) rfl⟩

#print axioms nest_E_never_again

/-- THE BACKWARD WEAKENING (backward run 2): the flow form of `A` gives `E` the `*` requirement,
    which does not satisfy `E`'s concrete record, so the `*` analysis of `A` loses the path through
    `E` (its only edge at the entry of `A` is the `p` path). The concrete analysis of `A` crosses `E`
    by the record and gives `(p,.,$,T)`: the concrete demand survives. -/
theorem nest_b2_weakening : B2 (.added 2 RqES) ∧ satW (revRec (JTE, GE)).1 RqES = false ∧
    applicable (revRec (JTE, GE)).1 RqES = false ∧ (∀ g, B2 (.edge 1 JbS 0 g) → g = GbS0) ∧
    B2 (.edge 1 JbU 0 GbU0) :=
  ⟨b2_addES, by decide, by decide,
   fun g h => (by decide : ∀ x ∈ S2.edges, x.1 = 1 → x.2.1 = JbS → x.2.2.1 = 0 → x.2.2.2 = GbS0)
     (1, JbS, 0, g) (inv2 h) rfl rfl rfl,
   b2_U0⟩

#print axioms nest_b2_weakening

/-- THE CONCRETE PATTERN OF `A` REACHES FORWARD RUN 3, next to its `*` pattern. -/
theorem nest_dem3 : dem3 1 dS3 ∧ dS3.din.mark = .star ∧ dem3 1 dT3 ∧
    dT3.din = ⟨3, [], .exact, .conc 1⟩ :=
  ⟨dem3_S, rfl, dem3_T, rfl⟩

#print axioms nest_dem3

/-- FORWARD RUN 3: `A` has the flow form and the concrete premise. The `*` added fact of the flow
    form does not use `E`'s concrete record (and `E` has no pattern), so the `*` analysis of `A` gives
    no fact with the mark `U`. -/
theorem nest_f3 : F3 (.init 1 JwA) ∧ F3 (.init 1 A3) ∧
    (∀ j, F3 (.init 1 j) → j = zeroFact ∨ j = JwA ∨ j = A3) ∧ F3 (.added 2 AE) ∧
    satW JTE AE = false ∧ applicable JTE AE = false ∧
    (∀ n g, F3 (.edge 1 JwA n g) → g.fact.mark ≠ .conc 2) :=
  ⟨f3_initS, f3_initT,
   fun j h => (by decide : ∀ x ∈ S3.inits, x.1 = 1 → x.2 = zeroFact ∨ x.2 = JwA ∨ x.2 = A3)
     (1, j) (inv3 h) rfl,
   f3_addES, by decide, by decide,
   fun n g h => (by decide : ∀ x ∈ S3.edges, x.1 = 1 → x.2.1 = JwA → x.2.2.2.fact.mark ≠ .conc 2)
     (1, JwA, n, g) (inv3 h) rfl rfl⟩

#print axioms nest_f3

/-- THE VULNERABILITY IS FOUND through the concrete pattern of `A` and the record of `E`, in the
    NORMAL layer, and nothing else is reported. -/
theorem nest_found : F3 (.edge 1 A3 2 W3) ∧ F3 (.vuln 0 2 sinkU false) ∧
    ∀ M n s b, F3 (.vuln M n s b) → (M = 0 ∧ n = 2 ∧ s = sinkU ∧ b = false) :=
  ⟨f3_exitU, DRA.vuln f3_r (List.Mem.head _) (by decide),
   fun M n s b h => (by decide : ∀ x ∈ S3.vulns, x.1 = 0 ∧ x.2.1 = 2 ∧ x.2.2.1 = sinkU ∧
     x.2.2.2 = false) (M, n, s, b) (inv3 h)⟩

#print axioms nest_found

end Nest

end ApSpec.AbsCases
