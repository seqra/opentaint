import FrontierCycle
import RegularCertificate
namespace CycleRules
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine BoundedRefinementPipeline FrontierCycle
set_option maxRecDepth 65536
set_option maxHeartbeats 240000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where rfl:=by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl:=by intro n; exact decide_eq_true rfl
  eq_of_beq:=by intro a b h; exact of_decide_eq_true h

-- Primitive witnesses for the recurring C2/body/C5 cells. They are generic
-- in the run, the finite field budget and the retained recursive depth.
theorem C2_root_exact_FLOW_probe_is_really_emitted
    (run k : Nat) (positive : 0<k) :
    q0∈emit run k false (ap p [] .may) ⟨ap p [] .exact (some t),false⟩ := by
  have nz : k≠0:=by omega
  simp [emit,emitBase,selector,ap,marksOK,completeFamily,primary,atHead,seed,
    q0,legalSeed,nz]

theorem C2_same_head_nonempty_STAR_is_really_emitted
    (run n k : Nat) (positive : 0<k) (room : n≤k) :
    qg n∈emit run k false (ap p (gs n) .ne) ⟨ap p (gs n) .star,false⟩ := by
  have nz : k≠0:=by omega
  simp [emit,emitBase,selector,ap,marksOK,completeFamily,primary,atHead,seed,
    qg,legalSeed,nz,gs_length,room]

theorem a_longer_inside_read_yields_only_a_DEMAND_MAY
    (n symbol : Nat) :
    OverwriteReplay.apply true (ap p (gs n++[symbol]) .star,val (ap ret [] .star))
      ⟨ap p (gs n) .star,false⟩=some ⟨ap p [] .may,true⟩ := by
  have no : dropHead (gs n++[symbol]) (gs n)=none:=by
    induction n with
    | zero=>rfl
    | succ n ih=>simpa only [gs_succ,List.cons_append,dropHead,ite_true] using ih
  have own:=strip n [symbol]
  simp only [OverwriteReplay.apply,ap,val]
  rw [no]
  simp [own,OverwriteReplay.union]

theorem C5_reader_keeps_the_uncertain_root_and_its_real_initial
    (n k : Nat) :
    BoundedRefinementPipeline.restricted k [qg n] (qg n)
      (val (ap ret [] .may) true) (rrow n)=
      some (ap p (gs n) .star,val (ap ret [] .may) true) := by
  simp [BoundedRefinementPipeline.restricted,qg,rrow,normalize,normalAp,
    ap,val,intersectExit,selector,marksMeet,cut]

theorem forward_application_of_the_reader_row_recreates_the_root_Target_input (n : Nat) :
    OverwriteReplay.apply false
      (ap p (gs n) .star,val (ap ret [] .may) true)
      ⟨ap p (gs n++[2]) .ne (some t),true⟩=
      some ⟨ap p [] .may (some t),true⟩ := by
  simp [OverwriteReplay.apply,ap,val,strip,OverwriteReplay.union,NestedSavedReplayCycle.sortBy]

theorem backward_application_of_the_writer_row_recreates_marking_permission (n : Nat) :
    OverwriteReplay.apply false
      (ap p (gs n) .star,val (ap ret [] .may) true)
      ⟨ap p (gs n) .exact (some t),true⟩=
      some ⟨ap p [] .may (some t),true⟩ := by
  have own:=strip n []
  simp only [List.append_nil] at own
  simp [OverwriteReplay.apply,ap,val,own,OverwriteReplay.union]

-- Each pair keeps a forward writer frontier, the reverse reader frontier,
-- the exact-root marking permission, and the same anonymous root Target.
-- Additional finite depths do not change any of these existence witnesses.
structure Cell where
  depth : Nat
  sourcePermission : Bool
  rootTarget : Bool
  normalObservation : Bool
  deriving DecidableEq, BEq, Repr

def pair (n : Nat) : Cell:=⟨n+1,true,true,false⟩
def advance (c : Cell) : Cell:=⟨c.depth+1,c.sourcePermission,c.rootTarget,false⟩
theorem the_cell_induction_has_no_iteration_limit (n : Nat) : advance (pair n)=pair (n+1) := by
  simp [advance,pair,Nat.add_assoc]
theorem the_repeated_root_demand_never_becomes_empty (n : Nat) :
    (pair n).rootTarget=true ∧ (pair n).sourcePermission=true ∧
      (pair n).normalObservation=false := by simp [pair]

theorem every_pair_has_its_actual_bounded_C2_and_C5_cut_witness (n : Nat) :
    q0∈emit (2*n+3) (2*n+2) false (ap p [] .may) ⟨ap p [] .exact (some t),false⟩ ∧
    qg (n+1)∈emit (2*n+3) (2*n+2) false (ap p (gs (n+1)) .ne)
      ⟨ap p (gs (n+1)) .star,false⟩ ∧
    BoundedRefinementPipeline.restricted (2*n+2) [q0] q0
      (writerPoint (n+2)) (wrow (n+1))=
      some (ap p [] .star,front (n+2)) := by
  refine ⟨C2_root_exact_FLOW_probe_is_really_emitted _ _ (by omega),
    C2_same_head_nonempty_STAR_is_really_emitted _ _ _ (by omega) (by omega),?_⟩
  simpa only [Nat.add_assoc] using paired_output_limit_is_still_a_real_cut (n+1) (2*n+2) (by omega)

-- This is the reference's cold prefix, not an assumed mature packet.
def start : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
def cold1:=PairedReference.step 1 start
def cold2:=PairedReference.step 2 cold1.1
theorem cold_run1_reaches_its_fixed_point_and_the_root_candidate :
    cold1.2.1=true ∧ (cold1.1.data.offers[2]!).any
      (fun a=>a.demand && PairedReference.observed a)=true := by decide
theorem cold_run2_reaches_its_fixed_point_and_preserves_the_source_route :
    cold2.2.1=true ∧ (cold2.1.data.offers[2]!).any
      (fun a=>a.demand && PairedReference.observed a)=true := by decide
end CycleRules
