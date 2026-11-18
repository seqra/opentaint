import PairedReference
namespace FrontierCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine BoundedRefinementPipeline
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where rfl:=by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl:=by intro n; exact decide_eq_true rfl
  eq_of_beq:=by intro a b h; exact of_decide_eq_true h

def gs (n : Nat) : Path:=List.replicate n 2
def wp (n : Nat) : Path:=gs n ++ [1]
def writerPoint (n : Nat) : Value:=val (ap ret (wp n) .exact)
def q0 : Seed:=⟨ap p [] .exact,false⟩
def qg (n : Nat) : Seed:=⟨ap p (gs n) .star,false⟩
def wrow (n : Nat) : Row:=⟨ap p [] .may,ap ret (gs n) .star⟩
def rrow (n : Nat) : Row:=⟨ap p (gs n) .ne,ap ret [] .star⟩
def front (n : Nat) : Value:=val (ap ret (gs n) .ne) true

theorem gs_length (n : Nat) : (gs n).length=n:=List.length_replicate
theorem gs_succ (n : Nat) : gs (n+1)=2::gs n:=by simp only [gs,List.replicate_succ]
theorem gs_add (a b : Nat) : gs (a+b)=gs a++gs b:=by simp only [gs,List.replicate_append_replicate]
theorem strip (a : Nat) (rest : Path) : dropHead (gs a) (gs a++rest)=some rest:=by
  induction a with
  | zero=>rfl
  | succ a ih=>simpa only [gs_succ,List.cons_append,dropHead,ite_true] using ih

theorem an_exact_writer_word_never_equals_a_reader_word (a b : Nat) :
    wp a ≠ gs (b+1) := by
  intro same
  have last:=congrArg List.getLast? same
  simp [wp,gs,List.getLast?_replicate] at last

theorem every_real_cut_loses_the_distinguishing_final_field (n : Nat) :
    cut n (writerPoint n)=front n := by
  have longer : (gs n++[1]).length>n:=by simp [gs_length]
  have take : (gs n++[1]).take n=gs n:=by
    simpa only [gs_length] using (List.take_left (l₁:=gs n) (l₂:=[1]))
  simp only [writerPoint,wp,val,ap,cut,longer,ite_true,take,front]

-- A reader can consume the entire retained prefix and one unknown field.
-- This is exactly the ordinary NE/STAR inside branch, not a pass rule.
def reader (n : Nat) : NormalUniformNE.Edge:=(ap p (gs (n+1)) .star,val (ap ret [] .star))
def candidate (n : Nat) : Option Offered:=
  OverwriteReplay.apply true (reader n) ⟨ap p (gs n) .ne (some t),true⟩
theorem every_finite_frontier_has_a_DEMAND_exact_observer_candidate (n : Nat) :
    candidate n=some ⟨ap p [] .may (some t),true⟩ := by
  have no : dropHead (gs (n+1)) (gs n)=none:=by
    induction n with
    | zero=>rfl
    | succ n ih=>simpa only [gs_succ,dropHead,ite_true] using ih
  have own:=strip n [2]
  have next : gs (n+1)=gs n++[2]:=by simpa only [gs,List.replicate_one] using gs_add n 1
  simp only [candidate,reader,OverwriteReplay.apply,ap,val]
  rw [no]
  simp [next,own,OverwriteReplay.union]


theorem the_exact_observer_can_match_that_MAY_only_on_DEMAND :
    intersectExit (val (ap ret [] .may (some t)) true) (ap ret [] .exact (some t))=
      some (val (ap ret [] .exact (some t)) true) := by decide

-- A concrete positive exact-root generator keeps its permission when the
-- reverse chain arrives as MAY. This is the ZERO/Target feedback route.
theorem backward_MAY_still_includes_the_real_root_marking_point :
    admits Tail.may [] []=true := rfl

def stateAt (pair : Nat) : Value:=front (pair+1)
def terminalAt (pair : Nat) : Option Offered:=candidate (pair+1)
theorem the_same_anonymous_Target_is_recreated_for_every_later_pair (pair : Nat) :
    terminalAt pair=some ⟨ap p [] .may (some t),true⟩ :=
  every_finite_frontier_has_a_DEMAND_exact_observer_candidate _

theorem neither_report_identity_nor_a_NORMAL_witness_can_retire_this_false_goal :
    OriginService.served [0] [(0,1)] [] 1 true=false := by decide

-- These local C5 checks retain the actual raw initial. They show why a
-- larger global budget does not make the output cap exact.
theorem paired_output_limit_is_still_a_real_cut (n k : Nat) (room : n+1≤k) :
    BoundedRefinementPipeline.restricted k [q0] q0 (writerPoint (n+1)) (wrow n)=
      some (ap p [] .star,front (n+1)) := by
  have own:=strip n [2,1]
  have wpNext : wp (n+1)=gs n++[2,1]:=by
    simp only [wp,gs,List.replicate_succ',List.append_assoc,List.singleton_append]
  have neq : wp (n+1)≠gs n:=by
    intro same
    have lengths:=congrArg List.length same
    simp only [wp,List.length_append,gs_length,List.length_singleton] at lengths
    omega
  have selected : intersectExit (val (ap ret (wp (n+1)) .star)) (ap ret (gs n) .star)=
      some (val (ap ret (wp (n+1)) .star)) := by
    simp [intersectExit,selector,ap,val,marksMeet,neq,beq_eq_false_iff_ne.mpr neq,wpNext,own,admits]
  have cutResult : cut (n+1) (val (ap ret (wp (n+1)) .star))=front (n+1) := by
    have longer : (gs (n+1)++[1]).length>n+1:=by simp [gs_length]
    have take : (gs (n+1)++[1]).take (n+1)=gs (n+1):=by
      simpa only [gs_length] using (List.take_left (l₁:=gs (n+1)) (l₂:=[1]))
    simp only [wp,val,ap,cut,longer,ite_true,take,front]
  simp only [BoundedRefinementPipeline.restricted,q0,List.any_cons,decide_true,Bool.true_or,
    List.any_nil,ite_true]
  simp only [normalize,ap,val,normalAp,Option.isNone_none,Bool.and_self,ite_true]
  change (do
    let c ← intersectExit (val (ap ret (wp (n+1)) .star)) (ap ret (gs n) .star)
    pure (normalize (ap p [] .star) (cut (min k ((gs n).length+1)) c))) =
      some (ap p [] .star,front (n+1))
  rw [selected]
  change some (normalize (ap p [] .star) (cut (min k ((gs n).length+1))
      (val (ap ret (wp (n+1)) .star)))) = some (ap p [] .star,front (n+1))
  rw [gs_length,Nat.min_eq_right room,cutResult]
  rfl


end FrontierCycle
