/-
Prepared extension of checked General19, with no changed definitions/claims.
Every C2 root template stays at the demanded head; every child template adds
exactly one counted field. Thus key depth <= demand depth+1, independently of
how deep the actual input is. This is a theorem about the existing operator,
not a new clipping or admission policy.
-/
import GeneralLoopAdmissionBound

namespace GeneralLoopAdmissionOneStep
open PlainStarRelativeAdmission
open ExactFlowInputBridge
open GeneralLoopAdmissionBound

theorem raw_C2_key_at_most_one_past_demand
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : emit mode d a = some seed) :
    seed.initial.path.length ≤ d.path.length+1 := by
  have image := arbitrary_actual_emission_is_in_raw_image mode d a seed emitted
  obtain ⟨baseSame,markSame,bounded,noANY,pathShape⟩ :=
    raw_image_preserves_base_mark_budget_and_has_no_ANY mode d seed.initial image
  rcases pathShape with same | ⟨field,child⟩
  · rw [same]
    exact Nat.le_succ _
  · rw [child]
    simp

theorem native_C2_key_at_most_one_past_demand
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : nativeEmit mode d a = some seed) :
    seed.initial.path.length ≤ d.path.length+1 := by
  rw [native_emit_is_old_query_emit] at emitted
  exact raw_C2_key_at_most_one_past_demand mode d (queryView a) seed emitted

theorem native_public_key_at_most_one_past_demand
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : nativeEmit mode d a = some seed) :
    (publicInitial seed.initial).path.length ≤ d.path.length+1 := by
  rw [public_normalization_keeps_key_depth]
  exact native_C2_key_at_most_one_past_demand mode d a seed emitted

theorem C5_queried_member_at_most_one_past_demand
    (mode : Mode) (d : Demand) (stored : Pattern)
    (permitted : canStoreInitial mode d stored = true) :
    stored.path.length ≤ d.path.length+1 := by
  obtain ⟨witness,found,legal,emitted,normal,inside⟩ :=
    C5_permission_has_executable_raw_actual_witness mode d stored permitted
  rw [← normal,public_normalization_keeps_key_depth]
  exact raw_C2_key_at_most_one_past_demand mode d witness.actual
    ⟨witness.rawInitial,intrinsic witness.rawInitial⟩ emitted

universe u
theorem ALL_commands_at_most_one_past_query_heads {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (actual : Actual) (h : Nat)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ h) (command : Command Label)
    (member : command ∈ commands mode query actual) :
    command.seed.initial.path.length ≤ h+1 := by
  obtain ⟨row,present,seed,emitted,labelSame,seedSame⟩ :=
    each_command_keeps_a_real_query_family mode query actual command member
  rw [seedSame]
  exact Nat.le_trans (native_C2_key_at_most_one_past_demand mode row.entry actual seed emitted)
    (Nat.add_le_add_right (heads row present) 1)

theorem ALL_public_keys_at_most_one_past_query_heads {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (actual : Actual) (h : Nat)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ h) (command : Command Label)
    (member : command ∈ commands mode query actual) :
    (publicInitial command.seed.initial).path.length ≤ h+1 := by
  rw [public_normalization_keeps_key_depth]
  exact ALL_commands_at_most_one_past_query_heads mode query actual h heads command member

theorem ALL_B4_initials_at_most_two_from_depth_one_heads {Label : Type u}
    (query : List (Query Label)) (actual : Actual)
    (heads : ∀ row ∈ query, row.entry.path.length ≤ 1) (command : Command Label)
    (member : command ∈ commands ⟨4,3,.backward⟩ query actual) :
    command.seed.initial.path.length ≤ 2 :=
  ALL_commands_at_most_one_past_query_heads ⟨4,3,.backward⟩ query actual 1 heads command member

theorem actual_B4_depth_three_can_emit_only_the_first_new_field :
    nativeEmit ⟨4,3,.backward⟩ ⟨0,[4],.any,.flow,[]⟩
      ⟨⟨0,[4,5,6],.exact,.full 7,[]⟩,.normal,false⟩ =
      some ⟨⟨0,[4,5],.star,.flow,[]⟩,.normal⟩ := by decide

#print axioms raw_C2_key_at_most_one_past_demand
#print axioms native_C2_key_at_most_one_past_demand
#print axioms native_public_key_at_most_one_past_demand
#print axioms C5_queried_member_at_most_one_past_demand
#print axioms ALL_commands_at_most_one_past_query_heads
#print axioms ALL_public_keys_at_most_one_past_query_heads
#print axioms ALL_B4_initials_at_most_two_from_depth_one_heads
#print axioms actual_B4_depth_three_can_emit_only_the_first_new_field

end GeneralLoopAdmissionOneStep
