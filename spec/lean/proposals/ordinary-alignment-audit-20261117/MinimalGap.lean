import ReplayCases
namespace MinimalGap
open NonEmptyPolicy NonEmptyRestriction NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

abbrev f:=ConcretePaths.f
abbrev g:=ConcretePaths.g
abbrev p:=AcyclicMayCycle.p
abbrev ret:=AcyclicMayCycle.ret

def flow (base : Nat) (path : Path) (tail : Tail := .star) : Ap :=
  ⟨base,path,tail,none,[],[]⟩
def source : Offered:=ReplayCases.source165
def state (n : Nat) : ReplayCases.Frame:=ReplayCases.history ReplayCases.methodsMinimal source 1 n

def learned : NormalUniformNE.Edge := (flow p [f],⟨flow ret [f],false,false⟩)
def learnedTag : Saved := ⟨learned,true⟩
def savedBasis : List (List Saved):=[[],[learnedTag]]

theorem all_five_cold_runs_reach_their_within_run_fixed_points :
    (List.range 5).all (fun n =>
      decide (UpdatedReplay.round (n+1) (max 1 n) 1 ReplayCases.methodsMinimal
        (state n).rows (state n).saved (state (n+1)).data=(state (n+1)).data))=true := by decide +kernel

theorem run1_keeps_both_owner_demand_rows :
    (state 1).rows=
      [[⟨flow p [g] .ne,flow ret []⟩],
       [⟨flow p [f] .may,flow ret []⟩]] := by decide +kernel

theorem run2_has_the_needed_NORMAL_helper_record :
    (state 2).saved=savedBasis ∧
    (state 2).rows=[[⟨flow p [g] .ne,flow ret [g]⟩],[]] := by decide +kernel

theorem the_run3_uniform_input_has_a_real_but_truncated_return :
    (state 3).data.current=
      [[(flow p [g] .must,⟨flow ret [g,g] .ne,true,false⟩)],[]] ∧
    (state 3).data.offers.getLast!=[⟨{flow p [g,g] .ne with mark:=some AcyclicMayCycle.t},true⟩] := by decide +kernel

theorem the_cut_is_mandatory_not_a_missing_field_limit_exception :
    cut 2 ⟨flow ret [g,g,f] .must,false,false⟩=
      ⟨flow ret [g,g] .ne,true,false⟩ ∧
    (flow ret [g,g,f]).path.length=3 ∧ 2<3 := by decide +kernel

theorem actual_run3_handoff_keeps_the_paired_row_and_projects_MUST :
    (state 3).rows=[[⟨flow p [g,g] .ne,flow ret [g] .may⟩],[]] := by decide +kernel

theorem run4_starts_STAR_at_the_own_NE_head_not_an_empty_point :
    UpdatedReplay.baseFamily 4 3 true ⟨flow p [g,g] .ne,flow ret [g] .may⟩ need=
      [⟨flow p [g,g],false⟩] := by decide +kernel

theorem no_wrapper_child_field_is_observed_from_its_own_snapshot :
    NestedColdMachine.fields ((state 3).rows[0]!) []
      ⟨flow p [g,g] .ne,flow ret [g] .may⟩=[] := by decide +kernel

theorem reverse_packing_delivers_an_unmasked_STAR_FLOW_offer_to_the_helper :
    ((state 4).data.domains[1]!)=[⟨flow p [],false⟩] := by decide +kernel

theorem the_existing_record_is_direct_and_cannot_handle_that_STAR_offer :
    OverwriteReplay.views true [learnedTag]=[(OverwriteReplay.reverseEdge learned,false)] ∧
    OverwriteReplay.apply false (OverwriteReplay.reverseEdge learned) ⟨flow p [],false⟩=none := by decide +kernel

theorem an_opposite_view_would_have_a_possible_reply_but_is_not_the_selected_role :
    OverwriteReplay.apply true (OverwriteReplay.reverseEdge learned) ⟨flow p [],false⟩=
      some ⟨flow p [f] .may,true⟩ := by decide +kernel

theorem no_current_helper_demand_can_start_the_missing_query :
    ((state 3).rows[1]!)=[] ∧
    UpdatedReplay.cells 4 3 true [] (OverwriteReplay.views true [learnedTag]) [⟨flow p [],false⟩]=[] := by decide +kernel

theorem run4_loses_all_DATA_service_and_run5_has_no_report_packet :
    (state 4).data.current=[[],[]] ∧ (state 4).rows=[[],[]] ∧
    (state 4).saved=savedBasis ∧
    (state 5).data.current=[[],[]] ∧ (state 5).rows=[[],[]] ∧
    (state 5).data.offers.getLast!=[] := by decide +kernel

theorem all_cold_output_paths_obey_the_run_global_limit :
    (List.range 5).all (fun n => ((state (n+1)).data.current.flatten).all
      (fun e => decide (e.1.path.length≤max 1 n ∧ e.2.ap.path.length≤max 1 n)))=true := by decide +kernel

theorem there_is_no_mask_or_protection_exception_in_this_counterexample :
    (List.range 5).all (fun n => ((state (n+1)).data.current.flatten).all
      (fun e => e.1.mx.isEmpty && e.2.ap.mx.isEmpty && !e.2.h))=true := by decide +kernel

-- A wrapper with no demand, no saved return record and no current reply
-- cannot deliver DATA for ANY actual or global limit. This is stronger
-- than relying on the actual source permission, which run-4 also loses.
theorem no_outer_service_at_any_larger_limit (run k : Nat) (actual : Offered) :
    UpdatedReplay.offer run k [] [] [] actual=[] := by
  simp [UpdatedReplay.offer,OverwriteReplay.views,executable,OverwriteReplay.values,unique,NestedSavedReplayCycle.sortBy]

theorem no_restricted_outer_body_can_restart_from_empty_rows
    (run k : Nat) (back : Bool) (actuals : List Offered) (not1 : run≠1) :
    UpdatedReplay.cells run k back [] [] actuals=[] := by
  simp [UpdatedReplay.cells,not1]

-- This terminal abstraction applies only after the fully checked cold
-- prefix. Its state says the outer owner has no return service or demand;
-- inner records stay retained. It grants the source again, optimistically.
def laterPacket (n : Nat) : List Offered:=
  UpdatedReplay.offer (n+5) (n+4) [] [] [] source

theorem no_uncapped_later_forward_offer_can_recreate_the_lost_route (n : Nat) :
    laterPacket n=[] := no_outer_service_at_any_larger_limit _ _ source

theorem the_returned_uniform_region_has_a_real_observed_point :
    ConcretePaths.wrapMinimal ConcretePaths.source165=
      some (ConcretePaths.value [g,g,f] .must) ∧
    admits .may [] [g,g,f]=true := by decide +kernel

-- Case 884 is a useful negative control for the search: the updated
-- reference does learn a NORMAL outer provider and returns the actual
-- exact T point by run-5, unlike the old diagnostic model.
theorem revised_884_reference_keeps_its_NORMAL_observation_at_run5 :
    (ReplayCases.history ReplayCases.methods884 ReplayCases.source884 2 5).data.offers.getLast!=
      [ReplayCases.source884] ∧
    (ReplayCases.history ReplayCases.methods884 ReplayCases.source884 2 5).rows=[[],[]] := by decide +kernel

end MinimalGap
