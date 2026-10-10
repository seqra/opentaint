/-
  Executable review of the F75 base-relevant cleaner correction.
  No historical AP definition is changed. RC, FC, and BC use exactly the existing
  forward run-1, restricted forward, and restricted backward rules, with the
  same BaseCleaner.cleanRes substituted at each cleaner. Requests exist only
  in RC. These are full closures with positive derivations. The review does not
  enumerate each full least closure or claim a global iteration theorem.

  The first root EXACT counterexample gets a concrete demand from the new
  run-1 request. The demand reaches its actual source at backward limit 2,
  supplies an eligible exact reversed record, and reports its real sink in
  the next forward run at limit 3. The second example's abstract hand-off and
  backward branch are also reached. Its eligible stored record excludes T
  after reversal, so this record cannot restore the cleaned root T. The review
  does not claim that the second example's entire next closure has no finding.
-/
import ApSpec.BaseCleaner
import ApSpec.ReviewBackwardCleaner
namespace ApSpec.ReviewBaseCleaner
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

section Run1
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)
inductive RC : Obj → Prop where
  | root {M} : M ∈ roots → RC (.init M zeroFact)
  | start {M i} : RC (.init M i) → RC (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      RC (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → RC (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      RC (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transfer counted L s f).reqs → RC (.req M i t)
  | pass {M i n f n' c} :
      RC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → RC (.edge M i n' f)
  | added {M i n f n' c e a} :
      RC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      RC (.added c.callee a.fact)
  | initA {m a} : RC (.added m a) → RC (.init m (α m a))
  -- The caller subscribes to EVERY summary edge whose premise its fact satisfies:
  -- the initial fact selected by the abstraction, the answers of requests, and any
  -- other initial fact of the callee that is applicable to the added fact.
  | ret {M i n f n' c e1 a j g r e2 r'} :
      RC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      RC (.init c.callee j) →
      applicable j a.fact = true →
      RC (.edge c.callee j (P.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      RC (.edge M i n' (limitF counted L r'))
  | reqSink {M i n f s t} :
      RC (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .request t →
      RC (.req M i t)
  | answer {M i t a} :
      RC (.req M i t) → RC (.added M a) → a.mark = .conc t →
      overlapB a i = true → RC (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      RC (.req m j t) → RC (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → RC (.req M ic t)
  | vuln {M i n f s} :
      RC (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      RC (.vuln M n s f.demand)
  -- a cleaner (spec §4.7)
  | clean {M i n f n' cl f'} :
      RC (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (BaseCleaner.cleanRes cl f).facts → RC (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      RC (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (BaseCleaner.cleanRes cl f).reqs → RC (.req M i t)
  -- a type filter (spec §4.8): a fact whose path may exist passes; another one is dropped
  | filt {M i n f n' b may} :
      RC (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → RC (.edge M i n' f)

end Run1
section Forward
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
inductive FC : Obj → Prop where
  | root {M} : M ∈ roots → FC (.init M zeroFact)
  | start {M i} : FC (.init M i) → FC (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      FC (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → FC (.edge M i n' f')
  | pass {M i n f n' c} :
      FC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → FC (.edge M i n' f)
  | added {M i n f n' c e a} :
      FC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      FC (.added c.callee a.fact)
  | initR {m a d j} :
      FC (.added m a) → demand m d → emit d.din a = some j → FC (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      FC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      FC (.init c.callee j) →
      FC (.edge c.callee j (P.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      FC (.edge M i n' (limitF counted L r'))
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      FC (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      FC (.edge M i n' (limitF counted L r'))
  | vuln {M i n f s} :
      FC (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      FC (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      FC (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (BaseCleaner.cleanRes cl f).facts → FC (.edge M i n' f')
  | filt {M i n f n' b may} :
      FC (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → FC (.edge M i n' f)

end Forward
section Backward
variable (Pb : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact)) (zbind : Bool)
inductive BC : Obj → Prop where
  | root {M} : M ∈ roots → BC (.init M zeroFact)
  | start {M i} : BC (.init M i) → BC (.edge M i (Pb.entry M) (startFact i))
  | step {M i n f n' s f'} :
      BC (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      f' ∈ (transfer counted L s f).facts → BC (.edge M i n' f')
  | pass {M i n f n' c} :
      BC (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      memB f.fact.base c.touched = false → BC (.edge M i n' f)
  | added {M i n f n' c e a} :
      BC (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      BC (.added c.callee a.fact)
  | initR {m a d j} :
      BC (.added m a) → demand m d → emit d.din a = some j → BC (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      BC (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      BC (.init c.callee j) →
      BC (.edge c.callee j (Pb.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      BC (.edge M i n' (limitF counted L r'))
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      BC (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      BC (.edge M i n' (limitF counted L r'))
  | vuln {M i n f s} :
      BC (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      BC (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      BC (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      f' ∈ (BaseCleaner.cleanRes cl f).facts → BC (.edge M i n' f')
  | filt {M i n f n' b may} :
      BC (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ Pb.edges →
      (f.fact.base = b → may f.fact.path = true) → BC (.edge M i n' f)
  | zpass {M n n' c} :
      BC (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      BC (.edge M zeroFact n' Backward.zeroAF)
  | zin {M n n' c} : zbind = true →
      BC (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      BC (.init c.callee zeroFact)
  | seed {M n s} : (M, n, s) ∈ seeds → BC (.edge M zeroFact n Backward.zeroAF) →
      BC (.edge M zeroFact n (limitF counted L ⟨s, false⟩))
  | zret {M n n' c g r e2 r'} : zbind = true →
      BC (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      BC (.edge c.callee zeroFact (Pb.exit c.callee) g) →
      r ∈ (applySummary Backward.zeroAF zeroFact g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      BC (.edge M zeroFact n' (limitF counted L r'))

end Backward

namespace Repaired
open ApSpec.ReviewRootCleaner (P Pb cnt st cl Jw PN A1 X1 R1out Z
  src callC bx br writeN writeF sink sinks)

abbrev R1 := RC P cnt 1 policy1 sinks [0]
def PNX : AFact := ⟨⟨4,[4],st,.starEx [1]⟩,false⟩
def PNT : AFact := ⟨⟨4,[4],.exact,.conc 1⟩,false⟩
def GFT : AFact := ⟨⟨5,[6],.any,.conc 1⟩,true⟩
def dT : DemandEdge := normDem ⟨GFT.fact,some A1⟩

theorem source : R1 (.edge 0 zeroFact 1 X1) :=
 RC.step (RC.start (RC.root (by decide))) (s := src) (by simp [P]) (by decide)
theorem added : R1 (.added 1 A1) :=
 RC.added (c := callC) (e := bx) (a := ⟨A1,false⟩) (n' := 2)
  source (by simp [P]) (by decide) (by decide)
theorem abstract_init : R1 (.init 1 Jw) := RC.initA added
theorem abstract_written : R1 (.edge 1 Jw 1 PN) :=
 RC.step (RC.start abstract_init) (s := writeN) (by simp [P]) (by decide)
theorem abstract_cleaned : R1 (.edge 1 Jw 2 PNX) :=
 RC.clean abstract_written (cl := cl) (by simp [P]) (by decide)
theorem request : R1 (.req 1 Jw 1) :=
 RC.reqClean abstract_written (cl := cl) (n' := 2) (by simp [P]) (by decide)
theorem concrete_init : R1 (.init 1 A1) := RC.answer request added rfl (by decide)
theorem concrete_written : R1 (.edge 1 A1 1 PNT) :=
 RC.step (RC.start concrete_init) (s := writeN) (by simp [P]) (by decide)
theorem concrete_cleaned : R1 (.edge 1 A1 2 PNT) :=
 RC.clean concrete_written (cl := cl) (by simp [P]) (by decide)
theorem concrete_exit : R1 (.edge 1 A1 3 GFT) :=
 RC.step concrete_cleaned (s := writeF) (by simp [P]) (by decide)
theorem concrete_demand : handFA P R1 pubD 1 dT :=
 ⟨_,⟨A1,GFT,GFT,concrete_init,concrete_exit,by decide,rfl,rfl⟩,rfl⟩
theorem demand_return : R1 (.edge 0 zeroFact 2 R1out) :=
 RC.ret (c := callC) (e1 := bx) (a := ⟨A1,false⟩) (j := A1) (g := GFT)
  (r := GFT) (e2 := br) (r' := R1out)
  source (by simp [P]) (by decide) (by decide) concrete_init (by decide) concrete_exit
  (by decide) (by decide) (by decide)
theorem demand_finding : R1 (.vuln 0 2 sink true) :=
 RC.vuln demand_return (by decide) (by decide)

/-- The request is necessary even though the run-1 fact is spatially disjoint. -/
theorem disjoint_requests : cleanPos cl PN.fact = .disjoint ∧
    BaseCleaner.cleanRes cl PN = ⟨[PNX],[1]⟩ ∧ R1 (.req 1 Jw 1) :=
 ⟨by decide,rfl,request⟩

def Rq : PFact := ⟨5,[6,4],.exact,.conc 1⟩
def Jr : PFact := Rq
def Aback : AFact := ⟨A1,false⟩
abbrev dem1 := handFA P R1 pubD
/-- All eligible normal run-1 records are retained as in the ordinary hand-off. -/
def recsB1 : Recs := fun m y => ∃ j g,
 R1 (.init m j) ∧ R1 (.edge m j (P.exit m) g) ∧ Cross j g ∧ y = revRec (j,g)
abbrev B2 := BC Pb cnt 2 dem1 emitW satW restrictI recsB1 [] [0] sinks true
theorem b_zero : B2 (.edge 0 zeroFact 2 Z) := BC.start (BC.root (by decide))
theorem b_seed : B2 (.edge 0 zeroFact 2 ⟨sink,false⟩) :=
 BC.seed (s := sink) (by decide) b_zero
theorem b_added : B2 (.added 1 Rq) :=
 BC.added (c := Call.rev callC) (e := revEdge br.1 br.2) (a := ⟨Rq,false⟩) (n' := 1)
  b_seed (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide) (by decide)
theorem b_init : B2 (.init 1 Jr) := BC.initR (d := dT) b_added concrete_demand (by decide)
theorem b_copy : B2 (.edge 1 Jr 2 PNT) :=
 BC.step (BC.start b_init) (s := Stmt.rev writeF)
  (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_clean : B2 (.edge 1 Jr 1 PNT) :=
 BC.clean b_copy (cl := cl) (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_exit : B2 (.edge 1 Jr 0 Aback) :=
 BC.step b_clean (s := Stmt.rev writeN)
  (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_return : B2 (.edge 0 zeroFact 1 X1) :=
 BC.ret (c := Call.rev callC) (e1 := revEdge br.1 br.2) (a := ⟨Rq,false⟩)
  (j := Jr) (g := Aback) (d := dT) (g' := Aback)
  (r := Aback) (e2 := revEdge bx.1 bx.2) (r' := X1)
  b_seed (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide) (by decide)
  b_init b_exit concrete_demand (by decide) (by decide) (by decide) (by decide) (by decide)

def lx : Loc := ⟨1,[],1⟩
def sourceEdge : MicroEdge := (zeroFact,⟨1,[],.exact,.conc 1⟩)
theorem source_hit : FSeeds.srcHit P B2 0 0 sourceEdge := by
 refine ⟨src,1,zeroFact,X1,zeroLoc,zeroLoc,lx,by simp [P],by decide,by decide,by decide,
  b_return,⟨1,rfl⟩,?_,?_⟩
 · exact ⟨rfl,rfl,rfl,rfl,trivial,[],[],rfl,rfl,rfl,rfl⟩
 · exact ⟨rfl,rfl,rfl,rfl,trivial,[],[],rfl,rfl,rfl,rfl⟩

theorem backward_record_eligible : Jr ≠ zeroFact ∧ Aback.complete = true ∧ CrossB Jr Aback :=
 ⟨by decide,by decide,
  by simp [CrossB,Cross,CrossK,MarkRev,revRec,revEdge,revKinds,Jr,Rq,Aback,A1]⟩

/-- The actual record store includes every normal crossed run-1 and backward record. -/
def rc3 : Recs := fun m x =>
 (R1 (.init m x.1) ∧ R1 (.edge m x.1 (P.exit m) x.2) ∧ Cross x.1 x.2) ∨
 (∃ j g, B2 (.init m j) ∧ j ≠ zeroFact ∧ B2 (.edge m j (Pb.exit m) g) ∧
   CrossB j g ∧ x = revRec (j,g))
theorem record_stored : rc3 1 (revRec (Jr,Aback)) :=
 Or.inr ⟨Jr,Aback,b_init,backward_record_eligible.1,b_exit,backward_record_eligible.2.2,rfl⟩
def dem3 := demOfNA Pb B2 (pubR dem1)
def sourceMask (M : MethodId) (n : Node) (e : MicroEdge) : Bool :=
 decide (M = 0 ∧ n = 0 ∧ e = sourceEdge)
def P3 := FSeeds.keepSources P sourceMask
theorem source_mask_program : P3 = P := rfl
theorem selected_source_hit : sourceMask 0 0 sourceEdge = true ∧ FSeeds.srcHit P B2 0 0 sourceEdge :=
 ⟨by decide,source_hit⟩
abbrev F3 := FC P3 cnt 3 dem3 emitW satW restrictI rc3 sinks [0]
def Out : AFact := ⟨sink,false⟩
def RetT : AFact := ⟨⟨5,[6,4],.exact,.conc 1⟩,false⟩
theorem r3_source : F3 (.edge 0 zeroFact 1 X1) :=
 FC.step (FC.start (FC.root (by decide))) (s := src) (by simp [source_mask_program,P]) (by decide)
theorem normal_return : F3 (.edge 0 zeroFact 2 Out) :=
 FC.retRec (c := callC) (e1 := bx) (a := ⟨A1,false⟩)
  (j := (revRec (Jr,Aback)).1) (g := (revRec (Jr,Aback)).2)
  (r := RetT) (e2 := br) (r' := Out)
  r3_source (by simp [source_mask_program,P]) (by decide) (by decide) record_stored
  (Or.inr (by decide)) (by decide) (by decide) (by decide)
theorem normal_finding : F3 (.vuln 0 2 sink false) := FC.vuln normal_return (by decide) (by decide)

/-- A value computes the exact record that repairs the old loss; its proof certifies
    the actual source hit, record persistence, and the next normal return. -/
def repairedWitness : {r : PFact × AFact //
    rc3 1 r ∧ FSeeds.srcHit P B2 0 0 sourceEdge ∧
    (applySummary ⟨A1,false⟩ r.1 r.2).facts = [RetT] ∧
    F3 (.vuln 0 2 sink false) ∧ Reach P [0] 0 2 ApSpec.ReviewRootCleaner.ls} :=
 ⟨revRec (Jr,Aback),record_stored,source_hit,by decide,normal_finding,
  ApSpec.ReviewRootCleaner.concrete_sink⟩

theorem repaired_counterexample :
    R1 (.req 1 Jw 1) ∧ handFA P R1 pubD 1 dT ∧
    FSeeds.srcHit P B2 0 0 sourceEdge ∧ rc3 1 (revRec (Jr,Aback)) ∧
    F3 (.vuln 0 2 sink false) ∧ 1 < 2 ∧ 2 < 3 :=
 ⟨request,concrete_demand,source_hit,record_stored,normal_finding,by decide,by decide⟩

#eval repairedWitness.val
#print axioms repairedWitness
#print axioms repaired_counterexample
end Repaired

namespace Blocked
open ApSpec.ReviewRootCleaner (cl PW PC Jb PB cnt src bx br Jw PN A1 X1 Z writeN writeF dC)
open ApSpec.ReviewBackwardCleaner (P Pb c sink sinks)

abbrev R1 := RC P cnt 1 policy1 sinks [0]
def GFX : AFact := ⟨⟨5,[6],.any,.starEx [1]⟩,true⟩
theorem source : R1 (.edge 0 zeroFact 1 X1) :=
 RC.step (RC.start (RC.root (by decide))) (s := src) (by simp [P]) (by decide)
theorem added : R1 (.added 1 A1) :=
 RC.added (c := c) (e := bx) (a := ⟨A1,false⟩) (n' := 2)
  source (by simp [P]) (by decide) (by decide)
theorem abstract_init : R1 (.init 1 Jw) := RC.initA added
theorem abstract_written : R1 (.edge 1 Jw 1 PN) :=
 RC.step (RC.start abstract_init) (s := writeN) (by simp [P]) (by decide)
theorem abstract_cleaned : R1 (.edge 1 Jw 2 Repaired.PNX) :=
 RC.clean abstract_written (cl := cl) (by simp [P]) (by decide)
theorem abstract_exit : R1 (.edge 1 Jw 3 GFX) :=
 RC.step abstract_cleaned (s := writeF) (by simp [P]) (by decide)
theorem abstract_demand : handFA P R1 pubD 1 dC :=
 ⟨_,⟨Jw,GFX,GFX,abstract_init,abstract_exit,by decide,rfl,rfl⟩,rfl⟩

abbrev dem1 := handFA P R1 pubD
def recsB1 : Recs := fun m y => ∃ j g,
 R1 (.init m j) ∧ R1 (.edge m j (P.exit m) g) ∧ Cross j g ∧ y = revRec (j,g)
abbrev B2 := BC Pb cnt 2 dem1 emitW satW restrictI recsB1 [] [0] sinks true
def Rq : PFact := ⟨5,[6],.exact,.conc 1⟩
theorem b_zero : B2 (.edge 0 zeroFact 2 Z) := BC.start (BC.root (by decide))
theorem b_seed : B2 (.edge 0 zeroFact 2 ⟨sink,false⟩) :=
 BC.seed (s := sink) (by decide) b_zero
theorem b_added : B2 (.added 1 Rq) :=
 BC.added (c := Call.rev c) (e := revEdge br.1 br.2) (a := ⟨Rq,false⟩) (n' := 1)
  b_seed (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide) (by decide)
theorem b_init : B2 (.init 1 Jb) := BC.initR (d := dC) b_added abstract_demand (by decide)
theorem b_copy : B2 (.edge 1 Jb 2 PW) :=
 BC.step (BC.start b_init) (s := Stmt.rev writeF)
  (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_clean : B2 (.edge 1 Jb 1 PC) :=
 BC.clean b_copy (cl := cl) (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_exit : B2 (.edge 1 Jb 0 PB) :=
 BC.step b_clean (s := Stmt.rev writeN)
  (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)

theorem record_eligible : Jb ≠ zeroFact ∧ PB.complete = true ∧ CrossB Jb PB :=
 ⟨by decide,by decide,
  by simp [CrossB,Cross,CrossK,MarkRev,revRec,revEdge,revKinds,Jb,PB,ApSpec.ReviewRootCleaner.st,
    Excl.union,Excl.empty]⟩
def rc3 : Recs := fun m x => ∃ j g,
 B2 (.init m j) ∧ j ≠ zeroFact ∧ B2 (.edge m j (Pb.exit m) g) ∧
 CrossB j g ∧ x = revRec (j,g)
theorem record_stored : rc3 1 (revRec (Jb,PB)) :=
 ⟨Jb,PB,b_init,record_eligible.1,b_exit,record_eligible.2.2,rfl⟩

/-- The proposed cleaner no longer permits the old abstract root record. -/
theorem abstract_clean : BaseCleaner.cleanRes cl PW = ⟨[PC],[1]⟩ := rfl
theorem abstract_write : PB ∈
    (transfer ApSpec.ReviewRootCleaner.cnt 2 (Stmt.rev ApSpec.ReviewRootCleaner.writeN) PC).facts :=
 by decide
def pT : AFact := ⟨⟨4,[],.exact,.conc 1⟩,false⟩
theorem actual_reversal : revRec (Jb,PB) =
    (⟨4,[],ApSpec.ReviewRootCleaner.st,.star⟩,
     ⟨⟨5,[6],.star (.set [4,4]),.starEx [1]⟩,false⟩) := by decide
theorem reversed_rejects_T :
    (applySummary pT (revRec (Jb,PB)).1 (revRec (Jb,PB)).2).facts = [] := by decide
theorem concrete_root_dropped : BaseCleaner.cleanRes cl pT = Res.none := rfl

def rejectedWitness : {r : PFact × AFact //
    rc3 1 r ∧ r = revRec (Jb,PB) ∧
    (applySummary pT r.1 r.2).facts = [] ∧
    BaseCleaner.cleanRes cl pT = Res.none} :=
 ⟨revRec (Jb,PB),record_stored,rfl,reversed_rejects_T,concrete_root_dropped⟩
#eval rejectedWitness.val
#print axioms rejectedWitness
end Blocked

end ApSpec.ReviewBaseCleaner
