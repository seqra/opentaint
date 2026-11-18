import TwoSidedSearch
import RegularRepair
namespace NestedFieldLane
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine
open BoundedRefinementPipeline FrontierCycle OperationalCycle
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
set_option linter.unusedSimpArgs false
local instance : ReflBEq Nat where rfl := by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro n; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

def exactF (path : Path) : Offered := ⟨ap p path .exact,false⟩
def writerRecord (a : Nat) : NormalUniformNE.Edge :=
  (ap p [] .star,val (ap ret (wp a) .star))
def readerRecord (a : Nat) : NormalUniformNE.Edge :=
  (ap p (gs a) .star,val (ap ret [] .star))
def reverseReaderRecord (a : Nat) : NormalUniformNE.Edge :=
  (ap p [] .star,val (ap ret (gs a) .star))

theorem one_writer_unroll_uses_an_already_retained_normal_record (a : Nat) :
    (OverwriteReplay.apply false (writerRecord a) (exactF [])).bind
      (fun w => OverwriteReplay.move [] [2] w.ap) =
    some (val (ap p (wp (a+1)) .exact)) := by
  simp [writerRecord,exactF,OverwriteReplay.apply,OverwriteReplay.move,ap,val,wp,gs_succ,
    dropHead,OverwriteReplay.union,NestedSavedReplayCycle.sortBy]

theorem c5_keeps_the_next_short_normal_writer_provider (a k : Nat) (room : a+1 ≤ k) :
    restricted k [q0] q0 (writerPoint a) (wrow a) = some (writerRecord a) := by
  have neq : wp a ≠ gs a := by
    intro h
    have l := congrArg List.length h
    simp only [wp,List.length_append,List.length_singleton,gs_length] at l
    omega
  have step : dropHead (gs a) (gs a ++ [1])=some [1] := strip a [1]
  simp [restricted,q0,wrow,writerPoint,writerRecord,normalize,normalAp,ap,val,intersectExit,
    selector,marksMeet,neq,step,admits,gs_length,Nat.min_eq_right room,cut,wp,-Nat.add_eq_left,-Nat.left_eq_add]

theorem parent_produces_a_child_query_for_an_actual_deeper_cut
    (a run k : Nat) (room : a+1 ≤ k) :
    qg (a+1) ∈ emit run k false (rrow a).entry
      ⟨ap p (gs (a+1)) .ne (some t),true⟩ := by
  have step : gs (a+1) = gs a ++ [2] := by simp [gs,List.replicate_succ']
  have neq : gs a ≠ gs (a+1) := by
    intro h
    have l := congrArg List.length h
    simp only [gs_length] at l
    omega
  have d : dropHead (gs a) (gs (a+1)) = some [2] := by
    calc
      dropHead (gs a) (gs (a+1)) = dropHead (gs a) (gs a ++ [2]) := congrArg (dropHead (gs a)) step
      _ = some [2] := strip a [2]
  have nz : k≠0 := by omega
  simp [emit,emitBase,selector,rrow,ap,marksOK,completeFamily,primary,neq,d,admits,seed,
    qg,legalSeed,nz,gs_length,room,show a ≤ k by omega,← step,-Nat.add_eq_left,-Nat.left_eq_add]

theorem the_pure_reader_step_removes_one_known_g (a : Nat) :
    OverwriteReplay.move [2] [] (qg (a+1)).ap = some (val (qg a).ap) := by
  simp [OverwriteReplay.move,qg,ap,val,gs_succ,dropHead]

theorem normal_reader_provider_needs_only_definite_replay (a : Nat) :
    DirectPossibleReplay.savedApply (readerRecord a,false) ⟨(qg a).ap,false⟩ =
      some ⟨ap p [] .star,false⟩ := by
  have stripA : dropHead (gs a) (gs a) = some [] := by simpa using strip a []
  simp [DirectPossibleReplay.savedApply,OverwriteReplay.apply,readerRecord,qg,ap,val,stripA,
    OverwriteReplay.union,NestedSavedReplayCycle.sortBy]

-- Same-direction providers give the same uncertain result as opposite
-- providers on this branch. R34 is needed when compaction keeps only one.
theorem either_saved_direction_keeps_the_recursive_uncertain_read (a : Nat) (opposite : Bool) :
    DirectPossibleReplay.savedRoute (qg (a+1)).ap [] (readerRecord (a+1),opposite)
      ⟨(qg a).ap,false⟩ = some ⟨ap p [] .may,true⟩ := by
  have step : gs (a+1) = gs a ++ [2] := by simp [gs,List.replicate_succ']
  have short : dropHead (gs (a+1)) (gs a)=none := by
    clear step
    induction a with
    | zero => rfl
    | succ n ih => simpa only [gs_succ,dropHead,ite_true] using ih
  have wide : dropHead (gs a) (gs (a+1))=some [2] := by
    calc
      dropHead (gs a) (gs (a+1)) = dropHead (gs a) (gs a ++ [2]) := congrArg (dropHead (gs a)) step
      _ = some [2] := strip a [2]
  cases opposite <;>
    simp [DirectPossibleReplay.savedRoute,DirectPossibleReplay.extra,DirectPossibleReplay.possible,
      DirectPossibleReplay.permission,ExclusionChildReplay.route,ExclusionChildReplay.eligible,
      OverwriteReplay.apply,readerRecord,qg,ap,val,short,wide,OverwriteReplay.union]

theorem the_reverse_reader_step_grows_only_one_field (a : Nat) :
    (OverwriteReplay.apply false (reverseReaderRecord a) (exactF [])).bind
      (fun w => OverwriteReplay.move [] [2] w.ap) =
    some (val (ap p (gs (a+1)) .exact)) := by
  simp [reverseReaderRecord,exactF,OverwriteReplay.apply,OverwriteReplay.move,ap,val,
    gs_succ,dropHead,OverwriteReplay.union,NestedSavedReplayCycle.sortBy]

theorem extra_branch_head_is_preserved_by_any_nonzero_cut (k : Nat) (positive : 0 < k)
    (path : Path) (tail : Tail) :
    ((cut k (val (ap ret (3::path) tail))).ap.path).head? = some 3 := by
  cases k with
  | zero => omega
  | succ k => simp [cut,ap,val]; split <;> rfl

theorem the_nested_reverse_branch_cannot_replace_a_g_selector (path : Path) (tail : Tail) (a : Nat) :
    intersectExit (val (ap ret (3::path) tail)) (ap ret (gs (a+1)) .star) = none := by
  simp [intersectExit,selector,ap,val,marksMeet,gs_succ,dropHead]

-- The consumer and the writer read/write equations are both complete in
-- this fixture. The new branch has no exact route merely because its two
-- operations occur on opposite sides of a call.
theorem the_principal_fixture_has_no_exact_witness
    (w : RegularCertificate.Derives (RegularSearch.grammar [1] [[2]]) 0 word)
    (r : PairedContext.Derives PairedContext.reader 0 word) : False := by
  have v : (RegularSearch.grammar [1] [[2]]).all
      (RegularCertificate.validatesClause PairedContext.writer) = true := by decide
  have route := RegularCertificate.every_grammar_derivation_has_a_compiled_automaton_witness v w
  have accepts : RegularCertificate.Accepts PairedContext.writer word := route
  exact PairedContext.the_search_budget_cannot_change_certificate_safety
    PairedContext.the_nested_reader_has_no_shared_word r (by simpa using accepts)


theorem the_cold_program_establishes_the_first_reverse_rows :
    (TwoSidedSearch.coldTwo.1.rows[0]!).contains (wrow 1) = true ∧
    (TwoSidedSearch.coldTwo.1.rows[1]!).contains (rrow 1) = true := by decide

def nextRows (n : Nat) : Option (Row × Row) := do
  let w ← reverseWriter n
  let r ← reverseReader n
  pure (projected w, projected r)

def principalOffer (n : Nat) : Option Offered := offerRoot n

theorem ordinary_replay_advances_the_clean_return_cone (n : Nat) :
    principalOffer n = some ⟨ap p [] .may (some t),true⟩ ∧
    nextRows n = some (wrow (n+2),rrow (n+2)) := by
  constructor
  · exact every_forward_pair_computes_the_same_root_DEMAND n
  · have hw := reverse_publication_supplies_the_next_forward_writer_row n
    have hr := reverse_reader_projection_supplies_the_next_forward_reader_row n
    unfold nextRows
    cases ew : reverseWriter n <;> cases er : reverseReader n <;> simp_all

-- This is the signed clean return cone, with the same retained-provider
-- and prepared-child service premises as OperationalCycle. It is not the
-- entire scheduler state or a claim that arbitrary extra rows preserve it.
def cleanCone : Nat → Option (Row × Row)
  | 0 => some (wrow 1,rrow 1)
  | n+1 => (cleanCone n).bind (fun _ => nextRows n)

theorem the_clean_cone_has_a_target_and_its_backwards_carry_at_every_pair (n : Nat) :
    cleanCone n = some (wrow (n+1),rrow (n+1)) ∧
    principalOffer n = some ⟨ap p [] .may (some t),true⟩ := by
  constructor
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [cleanCone,ih,Option.bind_some]
      exact (ordinary_replay_advances_the_clean_return_cone n).2
  · exact (ordinary_replay_advances_the_clean_return_cone n).1

-- Terminal handoff has the same transitions as R39 once a permanent
-- origin-specific certificate has been sealed. The proof does not need a
-- deadline or a hard run limit.
def repairedCone : Nat → RegularRepair.Frame
  | 0 => ⟨PairedContext.check PairedContext.reader 1 PairedContext.writer,true,true,true,false⟩
  | n+1 =>
    let prior := repairedCone n
    if prior.target then ⟨prior.closedGoal,!prior.closedGoal,true,true,false⟩
    else ⟨prior.closedGoal,false,false,false,false⟩

theorem the_nested_certificate_removes_only_the_root_target_at_run3 :
    repairedCone 1 = ⟨true,false,true,true,false⟩ := by decide

theorem every_pair_from_run5_is_quiet_after_the_certified_omission (n : Nat) :
    repairedCone (n+2) = ⟨true,false,false,false,false⟩ := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.succ_add,repairedCone,ih]; rfl

end NestedFieldLane
