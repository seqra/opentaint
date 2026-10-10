/-
  Experimental review of the user's proposed backward selected-mark cleaner.
  No normative cleaner or closure is changed.

  root() { x = source_T(); r = C(x, x); sink_T(r.f); }
  C(arg, p) { p.n = arg; clean(p, EXACT, T); ret.f = p; return ret; }

  Bases: zero=0, root x=1 and r=2; formal arg=3 and p=4, return ret=5.
  Accessors: n=4 and f=6. Mark T=1. Limits: forward 1, backward 2, forward 3.
  p is an exported formal parameter, so the new backward keep summary can be
  applied through its call binding. This is a primitive root cleaner; the two
  field writes use the existing strong-write edges. F74 field-action lowering
  is not bypassed by an atomic field cleaner.

  B below is only the positive-rule trace needed for the candidate backward
  run. It certifies reachability using its actual run-1 hand-off, not complete
  state enumeration. Every constructor is a proposed F72 backward rule.
  rec3 is a guaranteed subset of the candidate's persisted records. The generic
  forward_bad_of_stored_record theorem covers any next store containing it.
  Forward run 1 and run 3 use the unchanged normative D and DRW definitions.
-/
import ApSpec.ReviewRootCleaner
import ApSpec.CleanerLowering
namespace ApSpec.ReviewBackwardCleaner
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.Abs
open ApSpec.ReviewRootCleaner (st cnt id bx zb br src writeN writeF cl Jw PN GF A1 X1 R1out dC Z Jb PW)
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def bp : MicroEdge := (⟨1, [], st, .star⟩, ⟨4, [], st, .star⟩)
def c : Call := ⟨1, [1, 2], [bx, bp, zb], [br]⟩
def P : Program := ⟨fun _ => 0, fun m => if m = 1 then 3 else 2,
 [(0, 0, .stmt src, 1), (0, 1, .call c, 2),
  (1, 0, .stmt writeN, 1), (1, 1, .clean cl, 2), (1, 2, .stmt writeF, 3)]⟩
abbrev Pb := Program.rev P
def sink : PFact := ⟨2, [6], .exact, .conc 1⟩
def sinks := [(0, 2, sink)]
abbrev R1 := D P cnt 1 policy1 sinks [0]

theorem r1_source : R1 (.edge 0 zeroFact 1 X1) :=
 D.step (D.start (D.root (by decide))) (s := src) (by simp [P]) (by decide)
theorem r1_added : R1 (.added 1 A1) :=
 D.added (c := c) (e := bx) (a := ⟨A1, false⟩) (n' := 2)
  r1_source (by simp [P]) (by decide) (by decide)
theorem r1_init : R1 (.init 1 Jw) := D.initA r1_added
theorem r1_written : R1 (.edge 1 Jw 1 PN) :=
 D.step (D.start r1_init) (s := writeN) (by simp [P]) (by decide)
theorem r1_clean : R1 (.edge 1 Jw 2 PN) :=
 D.clean r1_written (cl := cl) (by simp [P]) (by decide)
theorem r1_exit : R1 (.edge 1 Jw 3 GF) :=
 D.step r1_clean (s := writeF) (by simp [P]) (by decide)
theorem demand_from_run1 : handFA P R1 pubD 1 dC :=
 ⟨_, ⟨Jw, GF, GF, r1_init, r1_exit, by decide, rfl, rfl⟩, rfl⟩
theorem r1_return : R1 (.edge 0 zeroFact 2 R1out) :=
 D.ret (c := c) (e1 := bx) (a := ⟨A1, false⟩) (j := Jw) (g := GF)
  (r := ⟨⟨5, [6], .any, .conc 1⟩, true⟩) (e2 := br) (r' := R1out)
  r1_source (by simp [P]) (by decide) (by decide) r1_init (by decide) r1_exit
  (by decide) (by decide) (by decide)
theorem r1_found : R1 (.vuln 0 2 sink true) := D.vuln r1_return (by decide) (by decide)

/-- The extra formal p is a genuine run-1 added fact and initial FLOW premise. -/
def Ap : PFact := ⟨4,[],.exact,.conc 1⟩
def Jp : PFact := ⟨4,[],st,.star⟩
def PK1 : AFact := ⟨⟨4,[],.star (.set [4,4]),.star⟩,false⟩
theorem r1_p_added : R1 (.added 1 Ap) :=
 D.added (c := c) (e := bp) (a := ⟨Ap,false⟩) (n' := 2)
  r1_source (by simp [P]) (by decide) (by decide)
theorem r1_p_init : R1 (.init 1 Jp) := D.initA r1_p_added
theorem r1_p_written : R1 (.edge 1 Jp 1 PK1) :=
 D.step (D.start r1_p_init) (s := writeN) (by simp [P]) (by decide)
theorem r1_p_request : R1 (.req 1 Jp 1) :=
 D.reqClean r1_p_written (cl := cl) (n' := 2) (by simp [P]) (by decide)
theorem r1_p_concrete_init : R1 (.init 1 Ap) :=
 D.answer r1_p_request r1_p_added rfl (by decide)
theorem r1_p_concrete_written : R1 (.edge 1 Ap 1 ⟨Ap,false⟩) :=
 D.step (D.start r1_p_concrete_init) (s := writeN) (by simp [P]) (by decide)
theorem forward_p_T_dropped : cleanRes cl ⟨Ap,false⟩ = Res.none := rfl

/-- Experimental selected-mark cleaner only; all other behavior delegated to current cleanRes. -/
def cleanB (cl : Cleaner) (f : AFact) : Res :=
 match cl.mark, f.fact.mark with
 | some _, .star => ⟨[f], []⟩
 | some _, .starEx _ => ⟨[f], []⟩
 | _, _ => cleanRes cl f

def G : AFact := ⟨⟨3, [], .any, .star⟩, true⟩
def K : AFact := ⟨⟨4, [], .star (.set [4, 4]), .star⟩, false⟩
def Rq : PFact := ⟨5, [6], .exact, .conc 1⟩
def Ax : AFact := ⟨⟨1, [], .any, .conc 1⟩, true⟩
abbrev dem1 := handFA P R1 pubD

/-- The relevant subset of proposed backward rules. Every constructor is a proposed
    F72 rule, so these positive paths occur in its full least closure. -/
inductive B : Obj → Prop where
 | root {M} : M ∈ [0] → B (.init M zeroFact)
 | start {M i} : B (.init M i) → B (.edge M i (Pb.entry M) (startFact i))
 | seed {M n s} : (M,n,s) ∈ sinks → B (.edge M zeroFact n Z) →
     B (.edge M zeroFact n (limitF cnt 2 ⟨s,false⟩))
 | added {M i n f n' cc e a} :
     B (.edge M i n f) → (M,n,Instr.call cc,n') ∈ Pb.edges → e ∈ cc.toCallee →
     a ∈ (applyEdge f e.1 e.2).facts → B (.added cc.callee a.fact)
 | initR {m a d j} : B (.added m a) → dem1 m d → emitW d.din a = some j → B (.init m j)
 | step {M i n f n' s f'} : B (.edge M i n f) → (M,n,Instr.stmt s,n') ∈ Pb.edges →
     f' ∈ (transfer cnt 2 s f).facts → B (.edge M i n' f')
 | clean {M i n f n' cl f'} : B (.edge M i n f) → (M,n,Instr.clean cl,n') ∈ Pb.edges →
     f' ∈ (cleanB cl f).facts → B (.edge M i n' f')
 | ret {M i n f n' cc e1 a j g d g' r e2 r'} :
     B (.edge M i n f) → (M,n,Instr.call cc,n') ∈ Pb.edges →
     e1 ∈ cc.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
     B (.init cc.callee j) → B (.edge cc.callee j (Pb.exit cc.callee) g) →
     dem1 cc.callee d → restrictI j g d = some g' → satW j a.fact = true →
     r ∈ (applySummary a j g').facts → e2 ∈ cc.fromCallee →
     r' ∈ (applyEdge r e2.1 e2.2).facts → B (.edge M i n' (limitF cnt 2 r'))

theorem b_zero : B (.edge 0 zeroFact 2 Z) := B.start (B.root (by decide))
theorem b_seed : B (.edge 0 zeroFact 2 ⟨sink,false⟩) := B.seed (s := sink) (by decide) b_zero
theorem b_added : B (.added 1 Rq) :=
 B.added (cc := Call.rev c) (e := revEdge br.1 br.2) (a := ⟨Rq,false⟩) (n' := 1)
  b_seed (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide) (by decide)
theorem b_init : B (.init 1 Jb) := B.initR (d := dC) b_added demand_from_run1 (by decide)
theorem b_copy : B (.edge 1 Jb 2 PW) :=
 B.step (B.start b_init) (s := Stmt.rev writeF)
  (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_clean : B (.edge 1 Jb 1 PW) :=
 B.clean b_copy (cl := cl) (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_exit_G : B (.edge 1 Jb 0 G) :=
 B.step b_clean (s := Stmt.rev writeN) (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_exit_K : B (.edge 1 Jb 0 K) :=
 B.step b_clean (s := Stmt.rev writeN) (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide)
theorem b_return : B (.edge 0 zeroFact 1 Ax) :=
 B.ret (cc := Call.rev c) (e1 := revEdge br.1 br.2) (a := ⟨Rq,false⟩)
  (j := Jb) (g := G) (d := dC) (g' := G)
  (r := ⟨⟨3,[],.any,.conc 1⟩,true⟩) (e2 := revEdge bx.1 bx.2) (r' := Ax)
  b_seed (by simp [Pb,Program.rev,P,revE,revInstr]) (by decide) (by decide)
  b_init b_exit_G demand_from_run1 (by decide) (by decide) (by decide) (by decide) (by decide)

def lx : Loc := ⟨1,[],1⟩
theorem source_hit : FSeeds.srcHit P B 0 0 (zeroFact,⟨1,[],.exact,.conc 1⟩) := by
 refine ⟨src,1,zeroFact,Ax,zeroLoc,zeroLoc,lx,by simp [P],by decide,by decide,by decide,
  b_return,⟨1,rfl⟩,?_,?_⟩
 · exact ⟨rfl,rfl,rfl,rfl,trivial,[],[],rfl,rfl,rfl,trivial⟩
 · exact ⟨rfl,rfl,rfl,rfl,trivial,[],[],rfl,rfl,rfl,rfl⟩

example : K.complete = true := by decide
example : Jb ≠ zeroFact := by decide
example : CrossB Jb K := by simp [CrossB,Cross,CrossK,MarkRev,revRec,revEdge,revKinds,Jb,K,st,Excl.union,Excl.empty]
example : revRec (Jb,K) =
 (⟨4,[],st,.star⟩,⟨⟨5,[6],.star (.set [4,4]),.star⟩,false⟩) := by decide
example : (applySummary ⟨⟨4,[],.exact,.conc 1⟩,false⟩
 (revRec (Jb,K)).1 (revRec (Jb,K)).2).facts = [⟨⟨5,[6],.exact,.conc 1⟩,false⟩] := by decide

/-- Actual unnormalized record storage, not restricted publication. -/
def rec3 : Recs := fun m x => ∃ j g, B (.init m j) ∧ j ≠ zeroFact ∧
 B (.edge m j (Pb.exit m) g) ∧ CrossB j g ∧ x = revRec (j,g)
theorem rec3_bad : rec3 1 (revRec (Jb,K)) :=
 ⟨Jb,K,b_init,by decide,b_exit_K,
  by simp [CrossB,Cross,CrossK,MarkRev,revRec,revEdge,revKinds,Jb,K,st,Excl.union,Excl.empty],rfl⟩
def dem3 := demOfNA Pb B (pubR dem1)
/-- This mask selects the sole source edge, which the actual backward trace hits. -/
def sourceEdge : MicroEdge := (zeroFact,⟨1,[],.exact,.conc 1⟩)
def sourceMask (M : MethodId) (n : Node) (e : MicroEdge) : Bool :=
 decide (M = 0 ∧ n = 0 ∧ e = sourceEdge)
def P3 : Program := FSeeds.keepSources P sourceMask
theorem source_mask_program : P3 = P := rfl
theorem selected_source_hit : sourceMask 0 0 sourceEdge = true ∧ FSeeds.srcHit P B 0 0 sourceEdge :=
 ⟨by decide,source_hit⟩
abbrev F3 := DRW P3 cnt 3 dem3 rec3 sinks [0]

theorem r3_source : F3 (.edge 0 zeroFact 1 X1) :=
 DRA.step (DRA.start (DRA.root (by decide))) (s := src) (by simp [source_mask_program,P]) (by decide)
def Out : AFact := ⟨sink,false⟩
theorem r3_bad_return : F3 (.edge 0 zeroFact 2 Out) :=
 DRA.retRec (c := c) (e1 := bp) (a := ⟨⟨4,[],.exact,.conc 1⟩,false⟩)
  (j := (revRec (Jb,K)).1) (g := (revRec (Jb,K)).2)
  (r := ⟨⟨5,[6],.exact,.conc 1⟩,false⟩) (e2 := br) (r' := Out)
  r3_source (by simp [source_mask_program,P]) (by decide) (by decide) rec3_bad
  (Or.inr (by decide)) (by decide) (by decide) (by decide)
theorem r3_bad_finding : F3 (.vuln 0 2 sink false) := DRA.vuln r3_bad_return (by decide) (by decide)

#print axioms demand_from_run1
#print axioms r1_found
#print axioms b_exit_K
#print axioms source_hit
#print axioms rec3_bad
#print axioms r3_bad_return
#print axioms r3_bad_finding
def lpRoot : Loc := ⟨4,[],1⟩
def lrRoot : Loc := ⟨5,[6],1⟩
def lsRoot : Loc := ⟨2,[6],1⟩

theorem no_cleaned_p (l0 : Loc) : ¬ Flow P 1 l0 2 lpRoot := by
 intro h
 cases h with
 | step _ hE _ => simp [P] at hE
 | pass _ hE _ => simp [P] at hE
 | call _ hE _ _ _ _ _ => simp [P] at hE
 | clean _ hE hcl =>
   simp [P] at hE
   rcases hE with ⟨rfl,rfl⟩
   exact absurd hcl (by decide)
 | filt _ hE _ => simp [P] at hE

theorem writeF_into_root {l : Loc} (hs : writeF.step l lrRoot) : l = lpRoot := by
 rcases hs with ⟨ht,he⟩ | ⟨e,he,hd⟩
 · subst l
   exact absurd ht (by decide)
 · simp [writeF] at he
   rcases he with rfl | rfl | rfl
   · exact absurd hd.2.1 (by decide)
   · have hd' := (ApSpec.CleanerLowering.write_pair (b := 5) (u := 4) (g := 6)).mp hd
     cases l
     simp_all [lrRoot,lpRoot]
   · have hd' := (ApSpec.CleanerLowering.keep_pair (b := 5) (g := 6)).mp hd
     have hx := hd'.2.2
     rw [← hd'.2.1] at hx
     exact absurd hx (by decide)

theorem no_callee_root (l0 : Loc) : ¬ Flow P 1 l0 3 lrRoot := by
 intro h
 cases h with
 | step h hE hs =>
   simp [P] at hE
   rcases hE with ⟨rfl,rfl⟩
   exact no_cleaned_p l0 ((writeF_into_root hs) ▸ h)
 | pass _ hE _ => simp [P] at hE
 | call _ hE _ _ _ _ _ => simp [P] at hE
 | clean _ hE _ => simp [P] at hE
 | filt _ hE _ => simp [P] at hE

theorem return_binding_root {l : Loc} (hd : den br.1 br.2 l lsRoot) : l = lrRoot := by
 rcases hd with ⟨hb0,hb,ha,hm,hpass,σ,τ,hp0,hp,ht,hτ⟩
 cases l
 simp_all [br,st,lsRoot,lrRoot,tailF,Excl.admits,MarkA.out]

theorem no_root_flow (l0 : Loc) : ¬ Flow P 0 l0 2 lsRoot := by
 intro h
 cases h with
 | step _ hE _ => simp [P] at hE
 | pass _ hE ht =>
   simp [P] at hE
   rcases hE with ⟨rfl,rfl⟩
   exact absurd ht (by decide)
 | @call M l0 n l n' cc e1 e2 l1 l2 l3 hf hE he1 hd1 hg he2 hd2 =>
   simp [P] at hE
   rcases hE with ⟨rfl,rfl⟩
   have he : e2 = br := by simpa [c] using he2
   subst e2
   exact no_callee_root l1 ((return_binding_root hd2) ▸ hg)
 | clean _ hE _ => simp [P] at hE
 | filt _ hE _ => simp [P] at hE

theorem reached_root_is_flow {m n l} (h : Reach P [0] m n l) :
 m = 0 → Flow P 0 zeroLoc n l := by
 induction h with
 | @root M n l hm hf =>
   intro hM
   subst M
   exact hf
 | @down M n l n' cc e l1 n2 l2 hr hE he hd hf ih =>
   intro hM
   have hx := hE
   simp [P] at hx
   rcases hx with ⟨_,_,hcc,_⟩
   have hc : cc.callee = 1 := by rw [hcc]; rfl
   rw [hc] at hM
   contradiction

theorem no_real_sink : ¬ Reach P [0] 0 2 lsRoot :=
 fun h => no_root_flow zeroLoc (reached_root_is_flow h rfl)

#print axioms no_callee_root
#print axioms no_real_sink
/-- Any next-run demand and record store containing the reached bad record gives
    the same normal return. Omitted unrelated records cannot block this derivation. -/
theorem forward_bad_of_stored_record
 (dem : MethodId → DemandEdge → Prop) (rc : Recs)
 (hr : rc 1 (revRec (Jb,K))) :
 DRW P3 cnt 3 dem rc sinks [0] (.edge 0 zeroFact 2 Out) := by
 have hs : DRW P3 cnt 3 dem rc sinks [0] (.edge 0 zeroFact 1 X1) :=
  DRA.step (DRA.start (DRA.root (by decide))) (s := src)
   (by simp [source_mask_program,P]) (by decide)
 exact DRA.retRec (c := c) (e1 := bp) (a := ⟨Ap,false⟩)
  (j := (revRec (Jb,K)).1) (g := (revRec (Jb,K)).2)
  (r := ⟨⟨5,[6],.exact,.conc 1⟩,false⟩) (e2 := br) (r' := Out)
  hs (by simp [source_mask_program,P]) (by decide) (by decide) hr
  (Or.inr (by decide)) (by decide) (by decide) (by decide)

theorem normal_finding_of_stored_record
 (dem : MethodId → DemandEdge → Prop) (rc : Recs)
 (hr : rc 1 (revRec (Jb,K))) :
 DRW P3 cnt 3 dem rc sinks [0] (.vuln 0 2 sink false) :=
 DRA.vuln (forward_bad_of_stored_record dem rc hr) (by decide) (by decide)

/-- The current mark exclusion prevents precisely the new false concrete propagation. -/
theorem current_keep_blocks_T :
 (applySummary ⟨Ap,false⟩
  (revRec (Jb,ApSpec.ReviewRootCleaner.PB)).1
  (revRec (Jb,ApSpec.ReviewRootCleaner.PB)).2).facts = [] := by decide

/-- A data-producing false record witness, with its reached derivation and concrete counterpair. -/
def badRecordWitness :
 {x : PFact × AFact // rec3 1 x ∧ x = revRec (Jb,K) ∧
  den x.1 x.2.fact lpRoot lrRoot ∧ ¬ Flow P 1 lpRoot 3 lrRoot} :=
 ⟨revRec (Jb,K),rec3_bad,rfl,
  ⟨rfl,rfl,trivial,rfl,trivial,[],[],rfl,rfl,rfl,rfl,rfl⟩,no_callee_root lpRoot⟩

/-- A data-producing normal finding whose sink location has no concrete reachability. -/
def normalFindingWitness :
 {f : AFact // F3 (.edge 0 zeroFact 2 f) ∧ f.demand = false ∧
  F3 (.vuln 0 2 sink false) ∧ ¬ Reach P [0] 0 2 lsRoot} :=
 ⟨Out,r3_bad_return,rfl,r3_bad_finding,no_real_sink⟩

theorem experimental_counterexample :
 R1 (.vuln 0 2 sink true) ∧ FSeeds.srcHit P B 0 0 sourceEdge ∧
 K.complete = true ∧ Jb ≠ zeroFact ∧ rec3 1 (revRec (Jb,K)) ∧
 F3 (.vuln 0 2 sink false) ∧ ¬ Reach P [0] 0 2 lsRoot ∧ 1 < 2 ∧ 2 < 3 :=
 ⟨r1_found,source_hit,by decide,by decide,rec3_bad,r3_bad_finding,no_real_sink,by decide,by decide⟩

#eval badRecordWitness.val
#eval normalFindingWitness.val
example : normalFindingWitness.val = ⟨sink,false⟩ := by decide
example : (applySummary ⟨Ap,false⟩ badRecordWitness.val.1 badRecordWitness.val.2).facts =
 [⟨⟨5,[6],.exact,.conc 1⟩,false⟩] := by decide
#print axioms r1_p_request
#print axioms r1_p_concrete_written
#print axioms source_mask_program
#print axioms badRecordWitness
#print axioms normalFindingWitness
#print axioms experimental_counterexample
#print axioms normal_finding_of_stored_record
end ApSpec.ReviewBackwardCleaner
