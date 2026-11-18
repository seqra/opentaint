import StarOnly

/- A promotion ban is query-local operational metadata, never Ap.e. Only
   an unknown STAR read can be omitted. This model checks that distinction
   and the separate-branch counterexample; it is not a complete driver. -/
namespace SeparatePromotionBan
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle HandoffMayExclusion
open StarOnlyHandoffExclusion

structure Command where
  seed : Seed
  promotionBan : List Nat
  deriving DecidableEq, BEq, Repr

def attach (d : Ap) (fields : List Nat) (s : Seed) : Command :=
  ⟨s, if d.tail == .may && s.ap.tail == .star && s.ap.path == d.path
      then fields else []⟩

def commands (run limit : Nat) (backward : Bool) (d : Ap)
    (fields : List Nat) (a : Offered) : List Command :=
  (emit run limit backward d a).map (attach d fields)

def blocks (fields : List Nat) (fromBase : Nat) (fromPath : Path) (a : Ap) : Bool :=
  if a.base != fromBase || a.tail != .star then false
  else match dropHead a.path fromPath with
    | some (field :: _) => fields.contains field
    | _ => false

def ordinaryStep (fromBase toBase : Nat) (fromPath toPath : Path)
    (input : Value) : Option Value :=
  (StarOnlyHandoffExclusion.transfer fromBase toBase fromPath toPath input.ap).map
    fun c => {c with demand := input.demand || c.demand, h := input.h || c.h}

def step (fields : List Nat) (fromBase toBase : Nat) (fromPath toPath : Path)
    (input : Value) : Option Value :=
  if blocks fields fromBase fromPath input.ap then none
  else ordinaryStep fromBase toBase fromPath toPath input

theorem command_keeps_the_entire_original_seed (d : Ap) (fields : List Nat) (s : Seed) :
    (attach d fields s).seed = s := rfl

theorem c2_raw_image_is_unchanged (run limit : Nat) (backward : Bool)
    (d : Ap) (fields : List Nat) (a : Offered) :
    (commands run limit backward d fields a).map Command.seed = emit run limit backward d a := by
  simp [commands, List.map_map, Function.comp_def, attach]

theorem no_added_field_exclusion (d : Ap) (fields : List Nat) (s : Seed) :
    (attach d fields s).seed.ap.e = s.ap.e := rfl

theorem allowed_steps_are_the_original_steps (fields : List Nat)
    (fromBase toBase : Nat) (fromPath toPath : Path) (input : Value)
    (allowed : blocks fields fromBase fromPath input.ap = false) :
    step fields fromBase toBase fromPath toPath input =
      ordinaryStep fromBase toBase fromPath toPath input := by
  simp [step, allowed]

theorem a_ban_never_creates_a_new_result (fields : List Nat)
    (fromBase toBase : Nat) (fromPath toPath : Path) (input result : Value)
    (found : step fields fromBase toBase fromPath toPath input = some result) :
    ordinaryStep fromBase toBase fromPath toPath input = some result := by
  unfold step at found
  split at found
  · cases found
  · exact found

def hfield : Nat := 3
def tmp : Nat := 2
def sourceH : Offered := ⟨ap p [hfield] .must (some t), false⟩
def chooseBack : Row := ⟨ap ret [] .may, ap p [] .star⟩
def wrapFront : Row := ⟨ap p [] .may, ap wrapRet [k] .star⟩

/-- Three alternative source-level branches: return p.g; return a fresh
    box whose f is p.h; return a fresh box whose f is p. -/
def reverseBranches (fields : List Nat) (input : Value) : List Value :=
  [step fields ret p [] [g] input,
   (step fields ret tmp [f] [] input).bind
      (fun c => step fields tmp p [] [hfield] c),
   step fields ret p [f] [] input].filterMap id

def forwardMiddle (input : Value) : Option Value := do
  let read ← ordinaryStep p tmp [hfield] [] input
  ordinaryStep tmp ret [] [f] read

theorem unknown_star_read_is_omitted :
    step [f] ret p [f] [] (val (ap ret [] .star)) = none := by decide

theorem known_prefix_star_read_is_not_banned :
    step [f] ret p [f] [] (val (ap ret [f] .star)) =
      some (val (ap p [] .star)) := by decide

theorem uniform_read_is_not_banned :
    step [f] ret p [f] [] (val (ap ret [] .must (some t))) =
      some (val (ap p [] .must (some t))) := by decide

theorem may_read_is_not_a_star_promotion :
    step [f] ret p [f] [] (val (ap ret [] .may) true) =
      ordinaryStep ret p [f] [] (val (ap ret [] .may) true) := by decide

theorem exact_probe_has_no_ban :
    (attach (ap p [] .may) [f] ⟨ap p [] .exact, false⟩).promotionBan = [] := by decide

theorem refined_star_has_no_ban :
    (attach (ap p [] .may) [f] ⟨ap p [f] .star, false⟩).promotionBan = [] := by decide

/-- This repairs the old E counterexample: prefix g is not clipped, so a
    later uniform source can still carry f through the saved NORMAL row. -/
theorem old_reader_is_no_longer_clipped :
    step [f] ret p [] [g] (val (ap ret [] .star)) =
      some (val (ap p [g] .star)) := by decide

theorem old_reader_keeps_the_old_wrapper_sink :
    ordinaryStep p wrapRet [g] [k] (val actualSource.ap) =
      some (val (ap wrapRet [k] .must (some t))) := by decide

theorem all_three_run1_branches_exist :
    ordinaryStep p ret [g] [] (val (ap p [] .star)) =
      some (val (ap ret [] .may) true) ∧
    forwardMiddle (val (ap p [] .star)) =
      some (val (ap ret [f] .may) true) ∧
    ordinaryStep p ret [] [f] (val (ap p [] .star)) =
      some (val (ap ret [f] .star)) := by decide

theorem wrapper_still_submits_a_same_head_star :
    emit 2 1 true wrapBack.entry limitedNeed = [⟨ap wrapRet [k] .star, false⟩] ∧
    ordinaryStep wrapRet ret [k] [] (val (ap wrapRet [k] .star)) =
      some (val (ap ret [] .star)) := by decide

theorem same_head_star_attaches_only_operational_metadata :
    commands 2 1 true chooseBack.entry [f] ⟨ap ret [] .star,false⟩ =
      [⟨⟨ap ret [] .star,false⟩,[f]⟩] := by decide

theorem without_ban_the_hidden_branch_has_its_own_demand :
    reverseBranches [] (val (ap ret [] .star)) =
      [val (ap p [g] .star), val (ap p [hfield] .may) true,
       val (ap p [] .may) true] := by decide

theorem the_field_ban_removes_both_distinct_writer_routes :
    reverseBranches [f] (val (ap ret [] .star)) =
      [val (ap p [g] .star)] := by decide

theorem without_ban_own_coarse_demand_survives_c5 :
    restrictOne 2 1 true [⟨ap ret [] .star,false⟩] (ap ret [] .star)
      (val (ap p [] .may) true) chooseBack =
        some (ap ret [] .star,val (ap p [] .may) true) := by decide

theorem with_ban_own_surviving_summary_is_unclipped_normal :
    restrictOne 2 1 true [⟨ap ret [] .star,false⟩] (ap ret [] .star)
      (val (ap p [g] .star)) chooseBack =
        some (ap ret [] .star,val (ap p [g] .star)) := by decide

/-- Replay belongs to the enclosing wrapper query and is not a new demand
    summary with the callee's own ret.STAR initial. -/
theorem original_offer_saved_replay_is_preserved :
    ordinaryStep ret p [f] [] (val (ap ret [] .star)) =
      some (val (ap p [] .may) true) := by decide

theorem wrapper_demand_keeps_the_h_source_refinement :
    emit 3 2 false wrapFront.entry sourceH =
      [⟨ap p [hfield] .star,false⟩,⟨ap p [] .exact,false⟩] := by decide

theorem saved_g_reader_cannot_read_h :
    ordinaryStep p wrapRet [g] [k] (val sourceH.ap) = none := by decide

theorem saved_direct_writer_has_the_wrong_suffix_correlation :
    ordinaryStep p ret [] [f] (val sourceH.ap) =
      some (val (ap ret [f,hfield] .must (some t))) ∧
    cut 2 (val (ap wrapRet [k,f,hfield] .must (some t))) =
      val (ap wrapRet [k,f] .ne (some t)) true := by decide

theorem direct_writer_cut_cannot_satisfy_the_root_sink :
    intersectExit (val (ap wrapRet [k,f] .ne (some t)) true)
      (ap wrapRet [k,f] .exact (some t)) = none := by decide

theorem the_omitted_current_query_would_learn_a_distinct_normal_reader :
    forwardMiddle (val (ap p [hfield] .star)) =
      some (val (ap ret [f] .star)) := by decide

theorem that_reader_is_admitted_by_wrapper_c5 :
    restrictOne 3 2 false [sourceH] (ap p [hfield] .star)
      (val (ap wrapRet [k,f] .star)) wrapFront =
        some (ap p [hfield] .star,val (ap wrapRet [k,f] .star)) := by decide

theorem real_source_reaches_the_exact_sink_via_that_reader :
    forwardMiddle (val sourceH.ap) =
      some (val (ap ret [f] .must (some t))) ∧
    ordinaryStep ret wrapRet [] [k] (val (ap ret [f] .must (some t))) =
      some (val (ap wrapRet [k,f] .must (some t))) ∧
    intersectExit (val (ap wrapRet [k,f] .must (some t)))
      (ap wrapRet [k,f] .exact (some t)) =
        some (val (ap wrapRet [k,f] .exact (some t))) := by decide

/-- Keep the second row explicitly. Once the parent carries a promotion
    ban, old output-language inclusion is not a service-cover proof. -/
def chooseChildBack : Row := ⟨ap ret [f] .may, ap p [] .star⟩
def rootStarOffer : Offered := ⟨ap ret [] .star, false⟩
def rootMayOffer : Offered := ⟨ap ret [] .may, true⟩

def bothCommands (offer : Offered) : List Command :=
  commands 2 1 true chooseBack.entry [f] offer ++
  commands 2 1 true chooseChildBack.entry [] offer

theorem child_demand_does_not_admit_an_ancestor_star_offer :
    commands 2 1 true chooseChildBack.entry [] rootStarOffer = [] := by decide

theorem both_retained_demands_still_have_only_the_root_star_query :
    bothCommands rootStarOffer = [⟨⟨ap ret [] .star, false⟩, [f]⟩] := by decide

theorem child_demand_admits_an_ancestor_may_offer :
    commands 2 1 true chooseChildBack.entry [] rootMayOffer =
      [⟨⟨ap ret [f] .exact, false⟩, []⟩,
       ⟨⟨ap ret [f] .star, false⟩, []⟩] := by decide

theorem child_demand_also_admits_the_explicit_field_star :
    commands 2 1 true chooseChildBack.entry [] ⟨ap ret [f] .star, false⟩ =
      [⟨⟨ap ret [f] .star, false⟩, []⟩] := by decide

theorem known_field_query_preserves_both_writer_branches :
    reverseBranches [] (val (ap ret [f] .exact)) =
      [val (ap p [g,f] .exact), val (ap p [hfield] .exact),
       val (ap p [] .exact)] := by decide

theorem retained_child_row_can_publish_the_missing_normal_reader :
    restrictOne 2 1 true [rootMayOffer] (ap ret [f] .exact)
      (val (ap p [hfield] .exact)) chooseChildBack =
        some (ap ret [f] .star, val (ap p [hfield] .star)) := by decide

end SeparatePromotionBan

#print axioms SeparatePromotionBan.command_keeps_the_entire_original_seed
#print axioms SeparatePromotionBan.c2_raw_image_is_unchanged
#print axioms SeparatePromotionBan.no_added_field_exclusion
#print axioms SeparatePromotionBan.allowed_steps_are_the_original_steps
#print axioms SeparatePromotionBan.a_ban_never_creates_a_new_result
#print axioms SeparatePromotionBan.unknown_star_read_is_omitted
#print axioms SeparatePromotionBan.known_prefix_star_read_is_not_banned
#print axioms SeparatePromotionBan.uniform_read_is_not_banned
#print axioms SeparatePromotionBan.may_read_is_not_a_star_promotion
#print axioms SeparatePromotionBan.exact_probe_has_no_ban
#print axioms SeparatePromotionBan.refined_star_has_no_ban
#print axioms SeparatePromotionBan.old_reader_is_no_longer_clipped
#print axioms SeparatePromotionBan.old_reader_keeps_the_old_wrapper_sink
#print axioms SeparatePromotionBan.all_three_run1_branches_exist
#print axioms SeparatePromotionBan.wrapper_still_submits_a_same_head_star
#print axioms SeparatePromotionBan.same_head_star_attaches_only_operational_metadata
#print axioms SeparatePromotionBan.without_ban_the_hidden_branch_has_its_own_demand
#print axioms SeparatePromotionBan.the_field_ban_removes_both_distinct_writer_routes
#print axioms SeparatePromotionBan.without_ban_own_coarse_demand_survives_c5
#print axioms SeparatePromotionBan.with_ban_own_surviving_summary_is_unclipped_normal
#print axioms SeparatePromotionBan.original_offer_saved_replay_is_preserved
#print axioms SeparatePromotionBan.wrapper_demand_keeps_the_h_source_refinement
#print axioms SeparatePromotionBan.saved_g_reader_cannot_read_h
#print axioms SeparatePromotionBan.saved_direct_writer_has_the_wrong_suffix_correlation
#print axioms SeparatePromotionBan.direct_writer_cut_cannot_satisfy_the_root_sink
#print axioms SeparatePromotionBan.the_omitted_current_query_would_learn_a_distinct_normal_reader
#print axioms SeparatePromotionBan.that_reader_is_admitted_by_wrapper_c5
#print axioms SeparatePromotionBan.real_source_reaches_the_exact_sink_via_that_reader
#print axioms SeparatePromotionBan.child_demand_does_not_admit_an_ancestor_star_offer
#print axioms SeparatePromotionBan.both_retained_demands_still_have_only_the_root_star_query
#print axioms SeparatePromotionBan.child_demand_admits_an_ancestor_may_offer
#print axioms SeparatePromotionBan.child_demand_also_admits_the_explicit_field_star
#print axioms SeparatePromotionBan.known_field_query_preserves_both_writer_branches
#print axioms SeparatePromotionBan.retained_child_row_can_publish_the_missing_normal_reader
