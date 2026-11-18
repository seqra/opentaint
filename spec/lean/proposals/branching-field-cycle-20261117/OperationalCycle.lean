import CycleRules
namespace OperationalCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine
open BoundedRefinementPipeline FrontierCycle CycleRules
set_option maxRecDepth 65536
set_option maxHeartbeats 320000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
local instance : ReflBEq Nat where rfl:=by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl:=by intro n; exact decide_eq_true rfl
  eq_of_beq:=by intro a b h; exact of_decide_eq_true h

-- Stored cells are calculated with the actual AP operators. In particular,
-- the root candidate is not a Boolean set to true by the recurrence model.
def forwardWriter (n : Nat) :=
  restricted (2*n+2) [q0] q0 (writerPoint (n+2)) (wrow (n+1))
def forwardReader (n : Nat) :=
  (OverwriteReplay.apply true
    (ap p (gs (n+1)) .star,val (ap ret [] .star))
    ⟨ap p (gs n) .star,false⟩).bind fun result=>
      restricted (2*n+2) [qg (n+1)] (qg (n+1))
        (val {result.ap with base:=ret} result.demand) (rrow (n+1))
def offerRoot (n : Nat) : Option Offered:=do
  let writer ← forwardWriter n
  let produced ← OverwriteReplay.apply false writer ⟨ap p [] .exact (some t),false⟩
  let reader ← forwardReader n
  OverwriteReplay.apply false reader produced

theorem calculated_forward_writer_is_a_real_admitted_cut (n : Nat) :
    forwardWriter n=some (ap p [] .star,front (n+2)) := by
  exact (every_pair_has_its_actual_bounded_C2_and_C5_cut_witness n).2.2

theorem calculated_forward_reader_is_an_uncertain_relation (n : Nat) :
    forwardReader n=some (ap p (gs (n+1)) .star,val (ap ret [] .may) true) := by
  have same : gs (n+1)=gs n++[2]:=by simp only [gs,List.replicate_succ']
  unfold forwardReader
  rw [same,a_longer_inside_read_yields_only_a_DEMAND_MAY]
  change restricted (2*n+2) [qg (n+1)] (qg (n+1))
    (val (ap ret [] .may) true) (rrow (n+1))=_
  simpa only [same] using C5_reader_keeps_the_uncertain_root_and_its_real_initial (n+1) (2*n+2)

theorem every_forward_pair_computes_the_same_root_DEMAND (n : Nat) :
    offerRoot n=some ⟨ap p [] .may (some t),true⟩ := by
  unfold offerRoot
  rw [calculated_forward_writer_is_a_real_admitted_cut,
      calculated_forward_reader_is_an_uncertain_relation]
  have first : OverwriteReplay.apply false (ap p [] .star,front (n+2))
      ⟨ap p [] .exact (some t),false⟩=
      some ⟨ap p (gs (n+2)) .ne (some t),true⟩ := by
    simp [OverwriteReplay.apply,ap,val,front,dropHead,OverwriteReplay.union,NestedSavedReplayCycle.sortBy]
  change (OverwriteReplay.apply false (ap p [] .star,front (n+2))
    ⟨ap p [] .exact (some t),false⟩).bind
      (fun made=>OverwriteReplay.apply false
        (ap p (gs (n+1)) .star,val (ap ret [] .may) true) made)=_
  rw [first]
  have next : gs (n+2)=gs (n+1)++[2]:=by simpa only [gs,List.replicate_succ']
  change OverwriteReplay.apply false _ ⟨ap p (gs (n+2)) .ne (some t),true⟩=_
  rw [next]
  exact forward_application_of_the_reader_row_recreates_the_root_Target_input _

-- The reverse writer uses the actual saved NORMAL prefix g^(n+1).f after the first read.
-- The reverse inside read produces MAY at the marking point and hence a
-- real reverse source permission. Its published key gives the next Dc/Dp.
def reverseWriter (n : Nat) :=
  (OverwriteReplay.apply true
    (ap p (gs (n+1)++[1]) .star,val (ap ret [] .star))
    ⟨ap p (gs (n+1)) .star,false⟩).bind fun result=>
      restricted (2*n+3) [qg (n+2)] (qg (n+2))
        (val {result.ap with base:=ret} result.demand) (rrow (n+2))

theorem reverse_permission_is_calculated_from_the_saved_writer (n : Nat) :
    reverseWriter n=some (ap p (gs (n+2)) .star,val (ap ret [] .may) true) := by
  unfold reverseWriter
  rw [a_longer_inside_read_yields_only_a_DEMAND_MAY]
  change restricted (2*n+3) [qg (n+2)] (qg (n+2))
    (val (ap ret [] .may) true) (rrow (n+2))=_
  exact C5_reader_keeps_the_uncertain_root_and_its_real_initial _ _

def projected (e : NormalUniformNE.Edge) : Row:=⟨{e.2.ap with base:=p},{e.1 with base:=ret}⟩
theorem reverse_publication_supplies_the_next_forward_writer_row (n : Nat) :
    (reverseWriter n).map projected=some (wrow (n+2)) := by
  rw [reverse_permission_is_calculated_from_the_saved_writer]
  rfl

theorem the_next_pair_really_has_the_next_C2_and_C5_witnesses (n : Nat) :
    q0∈emit (2*(n+1)+3) (2*(n+1)+2) false (ap p [] .may)
      ⟨ap p [] .exact (some t),false⟩ ∧
    qg (n+2)∈emit (2*(n+1)+3) (2*(n+1)+2) false
      (ap p (gs (n+2)) .ne) ⟨ap p (gs (n+2)) .star,false⟩ := by
  have checks:=every_pair_has_its_actual_bounded_C2_and_C5_cut_witness (n+1)
  simpa only [Nat.add_assoc] using And.intro checks.1 checks.2.1
def reverseReader (n : Nat) :=
  restricted (2*n+3) [q0] q0 (val (ap ret (gs (n+3)) .exact)) (wrow (n+1))

theorem reverse_reader_C5_produces_the_next_nonempty_demand (n : Nat) :
    reverseReader n=some (ap p [] .star,front (n+2)) := by
  have own:=strip (n+1) [2,2]
  have shape : gs (n+3)=gs (n+1)++[2,2]:=by
    simp only [gs,List.replicate_succ',List.append_assoc,List.singleton_append]
    rfl
  have different : gs (n+3)≠gs (n+1):=by
    intro same
    have lengths:=congrArg List.length same
    simp only [gs_length] at lengths
    omega
  have selected : intersectExit (val (ap ret (gs (n+3)) .star)) (ap ret (gs (n+1)) .star)=
      some (val (ap ret (gs (n+3)) .star)) := by
    simp [intersectExit,selector,ap,val,marksMeet,different,
      beq_eq_false_iff_ne.mpr different,shape,own,admits]
  have cutResult : cut (n+2) (val (ap ret (gs (n+3)) .star))=front (n+2) := by
    simp [cut,val,ap,gs,front,List.take_replicate,
      Nat.min_eq_left (by omega : n+2≤n+3)]
  unfold reverseReader
  simp only [restricted,q0,List.any_cons,decide_true,Bool.true_or,List.any_nil,ite_true]
  simp only [normalize,ap,val,normalAp,Option.isNone_none,Bool.and_self,ite_true]
  change (do
    let c ← intersectExit (val (ap ret (gs (n+3)) .star)) (ap ret (gs (n+1)) .star)
    pure (normalize (ap p [] .star) (cut (min (2*n+3) ((gs (n+1)).length+1)) c))) =_
  rw [selected]
  change some (normalize (ap p [] .star) (cut (min (2*n+3) ((gs (n+1)).length+1))
      (val (ap ret (gs (n+3)) .star))))=_
  rw [gs_length,Nat.min_eq_right (by omega),cutResult]
  rfl

theorem reverse_reader_projection_supplies_the_next_forward_reader_row (n : Nat) :
    (reverseReader n).map projected=some (rrow (n+2)) := by
  rw [reverse_reader_C5_produces_the_next_nonempty_demand]
  rfl

theorem the_actual_reverse_nonempty_offer_preserves_root_marking_permission (n : Nat) :
    OverwriteReplay.apply false
      (ap p (gs (n+2)) .star,val (ap ret [] .may) true)
      ⟨ap p (gs (n+2)) .ne (some t),true⟩=
      some ⟨ap p [] .may (some t),true⟩ := by
  have own:=strip (n+2) []
  simp only [List.append_nil] at own
  simp [OverwriteReplay.apply,ap,val,own,OverwriteReplay.union,NestedSavedReplayCycle.sortBy]

theorem the_cold_global_cut_before_C5_gives_the_same_frontier :
    restricted 2 [q0] q0 (cut 2 (writerPoint 2)) (wrow 1)=forwardWriter 0 := by decide

theorem every_later_kernel_unroll_fits_the_global_limit_before_its_paired_cut
    (n : Nat) (later : 1≤n) : cut (2*n+2) (writerPoint (n+2))=writerPoint (n+2) := by
  apply no_cut_preserves_intrinsic_may
  simp only [writerPoint,val,ap,wp,List.length_append,List.length_singleton,gs_length]
  omega

end OperationalCycle
