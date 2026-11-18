import NormalOnly

/- New candidate: never reject a concrete-field refinement. Add the demand's
   mask only to a raw STAR command at that SAME MAY head, before FLOW
   normalization. EXACT probes and MUST commands stay unchanged. -/
namespace StarOnlyHandoffExclusion
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle HandoffMayExclusion
open NormalOnlyHandoffExclusion

def attach (d : Ap) (fields : List Nat) (s : Seed) : Seed :=
  if d.tail == .may && s.ap.tail == .star && s.ap.path == d.path then
    {s with ap := {s.ap with e := s.ap.e ++ fields}}
  else s

def commands (run limit : Nat) (backward : Bool) (d : Ap)
    (fields : List Nat) (a : Offered) : List Seed :=
  (emit run limit backward d a).map (attach d fields)

/-- Give the candidate its consistent raw-C2-image C5 check. Other C5
    behavior, normalization, row-local bounds and persisted E are unchanged. -/
def restrictCandidate (run limit : Nat) (backward : Bool) (domain : List Offered)
    (fields : List Nat) (raw : Ap) (candidate : Value) (row : Row) : Option (Ap × Value) := do
  let image := domain.flatMap fun a => (commands run limit backward row.entry fields a).map Seed.ap
  if image.any (fun key => decide (key = raw)) then
    let normalized := normalize raw candidate
    let selected ← intersectExit normalized.2 row.exit
    return normalize normalized.1 (cut (min limit (row.exit.path.length+1)) selected)
  else none

def masked (a : Ap) : Ap := {a with e := [f]}
def k : Nat := 4
def wrapRet : Nat := 3
def wrapNeed : Offered := ⟨ap wrapRet [k,f] .exact (some t),false⟩
def limitedNeed : Offered := ⟨ap wrapRet [k] .ne (some t),true⟩
def wrapBack : Row := ⟨ap wrapRet [k] .may,ap p [] .star⟩
def wrapForward : Row := ⟨ap p [] .may,ap wrapRet [k] .star⟩

/-- Ordinary transfer with first-field E honored for an unknown-suffix read.
    The imported prefix move is used only after that guard. -/
def transfer (fromBase toBase : Nat) (fromPath toPath : Path)
    (a : Ap) : Option Value :=
  let blocked : Bool := match dropHead a.path fromPath with
    | some (field :: _) => (a.tail == .star || a.tail == .must) && a.e.contains field
    | _ => false
  if blocked then none
  else (move fromBase toBase fromPath toPath a).map fun value =>
    if value.ap.tail == .may then {value with ap := {value.ap with e := []}} else value

/-- Reached cells of applying a NORMAL correlated record with shared E.
    Reject an explicitly excluded input suffix; at the same head preserve E
    on the output suffix. No new native matching role is introduced. -/
def normalRecord (fromBase toBase : Nat) (fromPath toPath : Path)
    (excluded : List Nat) (a : Ap) : Option Value :=
  match dropHead fromPath a.path with
  | some [] => transfer fromBase toBase fromPath toPath {a with e := a.e ++ excluded}
  | some (field :: _) =>
    if excluded.contains field then none else transfer fromBase toBase fromPath toPath a
  | none => transfer fromBase toBase fromPath toPath a

theorem previous_exact_refinement_and_probe_are_unchanged :
    commands 2 1 true broad [f] need = emit 2 1 true broad need := by decide

theorem proper_descendant_star_refinement_is_unmasked :
    commands 3 2 false (ap p [] .may) [f] ⟨ap p [f] .ne (some t),true⟩ =
      [⟨ap p [f] .star,false⟩,⟨ap p [] .exact,false⟩] := by decide

theorem same_head_may_keeps_exact_but_masks_star :
    commands 2 1 true broad [f] ⟨ap ret [] .may (some t),true⟩ =
      [⟨ap ret [] .exact,false⟩,⟨masked (ap ret [] .star),false⟩] := by decide

theorem same_head_star_has_no_unmasked_exact_alternative :
    commands 2 1 true broad [f] ⟨ap ret [] .star,false⟩ =
      [⟨masked (ap ret [] .star),false⟩] := by decide

theorem same_head_must_is_unchanged :
    commands 3 2 false (ap p [] .may) [f] ⟨ap p [] .must (some t),false⟩ =
      [⟨ap p [] .must,false⟩] := by decide

theorem the_real_sink_seed_is_cut_to_ne :
    cut 1 (val wrapNeed.ap) = val limitedNeed.ap true := by decide

theorem wrapper_has_only_the_k_star_query :
    commands 2 1 true wrapBack.entry [] limitedNeed =
      [⟨ap wrapRet [k] .star,false⟩] := by decide

theorem reverse_wrapper_submits_star_at_choose_return :
    transfer wrapRet ret [k] [] (ap wrapRet [k] .star) =
      some (val (ap ret [] .star)) := by decide

theorem masked_choose_query_learns_only_the_clipped_reader :
    transfer ret p [] [g] (masked (ap ret [] .star)) =
      some (val (masked (ap p [g] .star))) ∧
    transfer ret p [f] [] (masked (ap ret [] .star)) = none := by decide

theorem candidate_raw_image_admits_its_masked_initial :
    restrictCandidate 2 1 true [⟨ap ret [] .star,false⟩] [f]
      (masked (ap ret [] .star)) (val (masked (ap p [g] .star))) pair =
        some (masked (ap ret [] .star),val (masked (ap p [g] .star))) := by decide

theorem current_choose_return_family_is_normal_and_clipped :
    [transfer ret p [] [g] (masked (ap ret [] .star)),
     transfer ret p [f] [] (masked (ap ret [] .star))].filterMap id =
       [val (masked (ap p [g] .star))] := by decide

theorem saved_writer_replay_on_the_original_star_still_runs :
    transfer ret p [f] [] (ap ret [] .star) =
      some (val (ap p [] .may) true) := by decide

theorem enclosing_backward_c5_keeps_the_clipped_normal_reader :
    restrictOne 2 1 true [limitedNeed] (ap wrapRet [k] .star)
      (val (masked (ap p [g] .star))) wrapBack =
        some (ap wrapRet [k] .star,val (masked (ap p [g] .star))) := by decide

theorem enclosing_backward_c5_also_keeps_the_coarse_request :
    restrictOne 2 1 true [limitedNeed] (ap wrapRet [k] .star)
      (val (ap p [] .may) true) wrapBack =
        some (ap wrapRet [k] .star,val (ap p [] .may) true) := by decide

theorem concrete_g_refinement_survives_the_later_g_mask :
    commands 3 2 false wrapForward.entry [g] actualSource =
      [⟨ap p [g] .star,false⟩,⟨ap p [] .exact,false⟩] := by decide

theorem choose_saved_reader_still_excludes_the_required_f_suffix :
    normalRecord p ret [g] [] [f] (ap p [g] .star) =
      some (val (masked (ap ret [] .star))) := by decide

theorem wrapper_preserves_that_exclusion_at_k :
    transfer ret wrapRet [] [k] (masked (ap ret [] .star)) =
      some (val (masked (ap wrapRet [k] .star))) := by decide

theorem wrapper_c5_keeps_that_normal_result :
    restrictOne 3 2 false [actualSource] (ap p [g] .star)
      (val (masked (ap wrapRet [k] .star))) wrapForward =
        some (ap p [g] .star,val (masked (ap wrapRet [k] .star))) := by decide

theorem precise_false_result_is_cut_to_the_kf_ne_demand :
    cut 2 (val (ap wrapRet [k,f,g] .star)) =
      val (ap wrapRet [k,f] .ne) true := by decide

theorem unmasked_exact_probe_learns_the_false_normal_relation :
    restrictOne 3 2 false [actualSource] (ap p [] .exact)
      (val (ap wrapRet [k,f] .exact)) wrapForward =
        some (ap p [] .star,val (ap wrapRet [k,f] .star)) := by decide

def laterNeed : Offered := ⟨ap wrapRet [k,f] .exact (some t),false⟩
theorem run4_exact_offer_cannot_start_the_new_ne_query :
    emit 4 3 true (ap wrapRet [k,f] .ne) laterNeed = [] := by decide

theorem clipped_normal_reader_cannot_answer_that_exact_offer :
    normalRecord wrapRet p [k] [g] [f] laterNeed.ap = none := by decide

theorem false_normal_replay_answers_only_the_unmarked_input_root :
    normalRecord wrapRet p [k,f] [] [] laterNeed.ap =
      some (val (ap p [] .exact (some t))) ∧
    sourceOverlap (ap p [] .exact (some t)) = false := by decide

theorem without_mask_the_backward_reader_would_be_unclipped :
    restrictOne 2 1 true [limitedNeed] (ap wrapRet [k] .star)
      (val (ap p [g] .star)) wrapBack =
        some (ap wrapRet [k] .star,val (ap p [g] .star)) := by decide

theorem without_mask_replay_preserves_the_real_uniform_source_at_k :
    normalRecord p wrapRet [g] [k] [] actualSource.ap =
      some (val (ap wrapRet [k] .must (some t))) ∧
    admits .must [] [f] = true := by decide

theorem masked_uniform_result_cannot_read_the_sink_field :
    normalRecord p wrapRet [g] [k] [f] actualSource.ap =
      some (val (masked (ap wrapRet [k] .must (some t)))) ∧
    transfer wrapRet ret [k,f] [] (masked (ap wrapRet [k] .must (some t))) = none := by decide

theorem cut_ne_result_cannot_satisfy_the_exact_same_head_sink :
    admits .ne [] [] = false := by decide

end StarOnlyHandoffExclusion

#print axioms StarOnlyHandoffExclusion.previous_exact_refinement_and_probe_are_unchanged
#print axioms StarOnlyHandoffExclusion.proper_descendant_star_refinement_is_unmasked
#print axioms StarOnlyHandoffExclusion.same_head_may_keeps_exact_but_masks_star
#print axioms StarOnlyHandoffExclusion.same_head_star_has_no_unmasked_exact_alternative
#print axioms StarOnlyHandoffExclusion.same_head_must_is_unchanged
#print axioms StarOnlyHandoffExclusion.the_real_sink_seed_is_cut_to_ne
#print axioms StarOnlyHandoffExclusion.wrapper_has_only_the_k_star_query
#print axioms StarOnlyHandoffExclusion.reverse_wrapper_submits_star_at_choose_return
#print axioms StarOnlyHandoffExclusion.masked_choose_query_learns_only_the_clipped_reader
#print axioms StarOnlyHandoffExclusion.candidate_raw_image_admits_its_masked_initial
#print axioms StarOnlyHandoffExclusion.current_choose_return_family_is_normal_and_clipped
#print axioms StarOnlyHandoffExclusion.saved_writer_replay_on_the_original_star_still_runs
#print axioms StarOnlyHandoffExclusion.enclosing_backward_c5_keeps_the_clipped_normal_reader
#print axioms StarOnlyHandoffExclusion.enclosing_backward_c5_also_keeps_the_coarse_request
#print axioms StarOnlyHandoffExclusion.concrete_g_refinement_survives_the_later_g_mask
#print axioms StarOnlyHandoffExclusion.choose_saved_reader_still_excludes_the_required_f_suffix
#print axioms StarOnlyHandoffExclusion.wrapper_preserves_that_exclusion_at_k
#print axioms StarOnlyHandoffExclusion.wrapper_c5_keeps_that_normal_result
#print axioms StarOnlyHandoffExclusion.precise_false_result_is_cut_to_the_kf_ne_demand
#print axioms StarOnlyHandoffExclusion.unmasked_exact_probe_learns_the_false_normal_relation
#print axioms StarOnlyHandoffExclusion.run4_exact_offer_cannot_start_the_new_ne_query
#print axioms StarOnlyHandoffExclusion.clipped_normal_reader_cannot_answer_that_exact_offer
#print axioms StarOnlyHandoffExclusion.false_normal_replay_answers_only_the_unmarked_input_root
#print axioms StarOnlyHandoffExclusion.without_mask_the_backward_reader_would_be_unclipped
#print axioms StarOnlyHandoffExclusion.without_mask_replay_preserves_the_real_uniform_source_at_k
#print axioms StarOnlyHandoffExclusion.masked_uniform_result_cannot_read_the_sink_field
#print axioms StarOnlyHandoffExclusion.cut_ne_result_cannot_satisfy_the_exact_same_head_sink
