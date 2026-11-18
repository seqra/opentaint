import RepairCases
import MinimalGap
deriving instance DecidableEq for ReplayCases.Frame
namespace DirectPossibleProofs
open NonEmptyPolicy NonEmptyRestriction NestedSavedReplayCycle NestedColdMachine
open DirectPossibleReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

/-- Successful old reads are preserved literally, including their layer. -/
theorem successful_saved_read_is_unchanged (e : NormalUniformNE.Edge × Bool)
    (a result : Offered) (old : OverwriteReplay.apply e.2 e.1 a = some result) :
    savedApply e a = some result := by simp [savedApply,old]

theorem opposite_saved_read_is_unchanged (e : NormalUniformNE.Edge) (a : Offered) :
    savedApply (e,true) a = OverwriteReplay.apply true e a := by
  cases old : OverwriteReplay.apply true e a <;> simp [savedApply,extra,possible,old]

theorem ineligible_saved_read_is_unchanged (e : NormalUniformNE.Edge × Bool)
    (a : Offered) (no : possible e.1 e.2 a = false) :
    savedApply e a = OverwriteReplay.apply e.2 e.1 a := by
  cases old : OverwriteReplay.apply e.2 e.1 a <;> simp [savedApply,extra,no,old]

theorem extra_never_creates_a_NORMAL_reply (e : NormalUniformNE.Edge × Bool)
    (a result : Offered) (hit : extra e a = some result) : result.demand = true := by
  unfold extra at hit
  split at hit
  · split at hit
    · split at hit
      · contradiction
      · cases hit; rfl
    · contradiction
  · contradiction

theorem every_new_reply_is_DEMAND (e : NormalUniformNE.Edge × Bool)
    (a result : Offered) (none : OverwriteReplay.apply e.2 e.1 a = none)
    (hit : savedApply e a = some result) : result.demand = true := by
  exact extra_never_creates_a_NORMAL_reply e a result (by simpa [savedApply,none] using hit)

theorem a_NORMAL_reply_has_the_old_exact_derivation (e : NormalUniformNE.Edge × Bool)
    (a result : Offered) (hit : savedApply e a = some result) (normal : result.demand=false) :
    OverwriteReplay.apply e.2 e.1 a = some result := by
  cases old : OverwriteReplay.apply e.2 e.1 a with
  | some r => simpa [savedApply,old] using hit
  | none => have impossible := every_new_reply_is_DEMAND e a result old hit; simp_all

theorem successful_routed_read_is_unchanged (q : Ap) (mask : List Nat)
    (e : NormalUniformNE.Edge × Bool) (a result : Offered)
    (old : ExclusionChildReplay.route true q mask e a = some result) :
    savedRoute q mask e a = some result := by simp [savedRoute,old]

theorem new_reply_keeps_the_stored_result_head_and_offered_mark
    (e : NormalUniformNE.Edge × Bool) (a result : Offered)
    (hit : extra e a = some result) :
    result.ap.path = e.1.2.ap.path ∧ result.ap.mark=a.ap.mark ∧
    result.ap.tail = .may ∧ result.ap.e=[] := by
  unfold extra at hit
  split at hit
  · split at hit
    · split at hit
      · contradiction
      · cases hit; exact ⟨rfl,rfl,rfl,rfl⟩
    · contradiction
  · contradiction

/-- No full marked, MUST-guarded, MAY-output or DEMAND record enters this lane. -/
theorem marked_record_is_ineligible (e : NormalUniformNE.Edge) (opposite : Bool)
    (a : Offered) (mark : e.1.mark.isNone=false) : possible e opposite a=false := by
  simp [possible,mark]

theorem DEMAND_record_is_ineligible (e : NormalUniformNE.Edge) (opposite : Bool)
    (a : Offered) (d : e.2.demand=true) : possible e opposite a=false := by
  simp [possible,d]

theorem nonSTAR_actual_is_ineligible (e : NormalUniformNE.Edge) (opposite : Bool)
    (a : Offered) (different : a.ap.tail ≠ .star) : possible e opposite a=false := by
  cases t : a.ap.tail <;> simp_all [possible]

/-- A concrete ordinary prefix relation has one correlated residual. A
    possible reply forgets this residual but contains every successful point.
    Native E, mx, ports and original filters can only remove witnesses. -/
def concrete (inputHead guard output : Path) (operandE premiseE resultE : List Nat)
    (input result : Path) : Prop :=
  ∃ gap residual,
    guard=inputHead++gap ∧ gap≠[] ∧
    input=guard++residual ∧
    ExclusionChildCover.permits operandE (gap++residual)=true ∧
    ExclusionChildCover.permits premiseE residual=true ∧
    ExclusionChildCover.permits resultE residual=true ∧ result=output++residual

theorem possible_MAY_contains_every_successful_concrete_reply
    (inputHead guard output : Path) (operandE premiseE resultE : List Nat)
    (input result : Path)
    (witness : concrete inputHead guard output operandE premiseE resultE input result) :
    NonEmptyMay.rooted output .may result := by
  obtain ⟨_,residual,_,_,_,_,_,_,shape⟩:=witness
  exact ⟨residual,shape,True.intro⟩

theorem the_same_witness_preserves_any_fixed_native_qualification
    (inputHead guard output : Path) (operandE premiseE resultE : List Nat)
    (input result : Path) (qualified : Path → Prop)
    (witness : concrete inputHead guard output operandE premiseE resultE input result)
    (allowed : qualified result) :
    NonEmptyMay.rooted output .may result ∧ qualified result :=
  ⟨possible_MAY_contains_every_successful_concrete_reply _ _ _ _ _ _ _ _ witness,allowed⟩

/-- Per-record scalar replay emits zero or one reply, no suffix product. -/
theorem no_more_than_one_reply_per_existing_record (e : NormalUniformNE.Edge × Bool) (a : Offered) :
    (savedApply e a).toList.length ≤ 1 := by cases savedApply e a <;> simp

-- The checked cold run includes own paired C5, current C2, real cuts,
-- saved-first service and within-run closure; it is not a warm interface.
def minimal (n : Nat) : ReplayCases.Frame :=
  RepairCases.history ReplayCases.methodsMinimal ReplayCases.source165 1 n

theorem all_five_repaired_runs_are_within_run_fixed_points :
    (List.range 5).all (fun n=>decide
      (DirectPossibleReplay.round (n+1) (max 1 n) 1 (RepairCases.convert ReplayCases.methodsMinimal)
        (minimal n).rows (minimal n).saved (minimal (n+1)).data=(minimal (n+1)).data))=true := by decide +kernel

theorem the_first_three_cold_runs_are_unchanged :
    (List.range 3).all (fun n=>decide (minimal (n+1)=MinimalGap.state (n+1)))=true := by decide +kernel

theorem blocked_direct_record_adds_only_the_possible_helper_reply :
    savedApply (OverwriteReplay.reverseEdge MinimalGap.learned,false)
      ⟨MinimalGap.flow AcyclicMayCycle.p [],false⟩=
      some ⟨MinimalGap.flow AcyclicMayCycle.p [ConcretePaths.f] .may,true⟩ := by decide +kernel

theorem run4_keeps_the_missing_own_paired_DEMAND :
    (minimal 4).rows=
      [[⟨MinimalGap.flow AcyclicMayCycle.p [ConcretePaths.g,ConcretePaths.g] .ne,
          MinimalGap.flow AcyclicMayCycle.ret [ConcretePaths.g,ConcretePaths.g]⟩],[]] ∧
    (minimal 4).saved=MinimalGap.savedBasis := by decide +kernel

theorem run5_retains_the_real_NORMAL_observation_and_empties_demand :
    (minimal 5).rows=[[],[]] ∧
    (minimal 5).data.offers.getLast!=
      [⟨{MinimalGap.flow AcyclicMayCycle.p [ConcretePaths.g,ConcretePaths.g,ConcretePaths.f] .must
        with mark:=some AcyclicMayCycle.t},false⟩] := by decide +kernel

theorem the_repaired_cold_prefix_keeps_all_global_field_limits :
    (List.range 5).all (fun n=>((minimal (n+1)).data.current.flatten).all
      (fun e=>decide (e.1.path.length≤max 1 n ∧ e.2.ap.path.length≤max 1 n)))=true := by decide +kernel

theorem run3_still_performs_the_mandatory_cut :
    (minimal 3).data.current=(MinimalGap.state 3).data.current := by decide +kernel

theorem full_165_keeps_its_NORMAL_observation_at_run5 :
    (RepairCases.history ReplayCases.methods165 ReplayCases.source165 2 5).rows=[[],[]] ∧
    (RepairCases.history ReplayCases.methods165 ReplayCases.source165 2 5).data.offers.getLast!=
      [⟨{MinimalGap.flow AcyclicMayCycle.p [ConcretePaths.g,ConcretePaths.g,ConcretePaths.f] .must
        with mark:=some AcyclicMayCycle.t},false⟩] := by decide +kernel

theorem existing_884_control_has_the_same_complete_run5_state :
    RepairCases.history ReplayCases.methods884 ReplayCases.source884 2 5=
      ReplayCases.history ReplayCases.methods884 ReplayCases.source884 2 5 := by decide +kernel

-- Negative field-hole control: the new read does not ignore an excluded first field.
theorem excluded_helper_field_still_has_no_reply :
    savedApply (OverwriteReplay.reverseEdge MinimalGap.learned,false)
      ⟨{MinimalGap.flow AcyclicMayCycle.p [] with e:=[ConcretePaths.f]},false⟩=none := by decide +kernel

-- Ready child suppression uses the existing constructive suffix cover.
-- No query is started from this predicate.
theorem ready_child_uses_the_same_concrete_coverage
    (initial current : List Nat) (field : Nat) (rest write : List Nat)
    (operandE premiseE resultE : List Nat) (input output : List Nat) :
    ExclusionChildCover.parent initial current field rest write operandE premiseE resultE input output ↔
      ExclusionChildCover.child initial current field rest write operandE premiseE resultE input output :=
  ExclusionChildCover.complete_child_cover_with_arbitrary_real_exclusions _ _ _ _ _ _ _ _ _ _
end DirectPossibleProofs
