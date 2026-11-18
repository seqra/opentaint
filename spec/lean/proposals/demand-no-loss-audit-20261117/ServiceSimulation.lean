import CoveredOrigin
import AuditKernel
import TargetSupport

namespace ServiceSimulation
local instance : ReflBEq Nat where rfl := by intro n; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro n; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

-- The key is an adapter view, not a field added to stored AP values.
-- Logical service keeps controls separate from point coverage.
inductive Kind where
  | data | query | publication | target | sourcePermission | savedReplay
  | aliasEffect | ruleEffect | track | continueRun
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Need where
  kind : Kind
  run : Nat
  frame : Nat
  item : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Action where
  premises : List Need
  result : Need
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Action.rule (a : Action) : AuditKernel.Rule Need := ⟨a.premises,a.result⟩
def nativeRules (actions : List Action) := actions.map Action.rule

def ready (available : List Need) (need : Need) : Bool := available.contains need
def step (available : List Need) (action : Action) : Option (List Need) :=
  if action.premises.all (fun x => ready available x && decide (x.run ≤ action.result.run))
  then some (action.result :: available) else none

def replay (enabled : List Action) : List Action → List Need → Option (List Need)
  | [], available => some available
  | action::rest, available =>
    if enabled.contains action then (step available action).bind (replay enabled rest) else none

def check (enabled plan : List Action) (available obligations : List Need) : Bool :=
  match replay enabled plan available with
  | none => false
  | some final => obligations.all (ready final)

theorem a_checked_replay_step_has_all_of_its_inputs
    (hit : step available action = some result) :
    result = action.result :: available ∧ ∀ x ∈ action.premises, x ∈ available := by
  unfold step at hit
  split at hit
  · rename_i hp
    exact ⟨(Option.some.inj hit).symm,
      fun x hx => List.mem_of_elem_eq_true ((Bool.and_eq_true_iff.mp
        (List.all_eq_true.mp hp x hx)).1)⟩
  · cases hit

theorem replay_produces_a_native_derivation_for_each_available_service
    (enabled plan : List Action) (seed after : List Need)
    (valid : replay enabled plan before = some after)
    (fromSeed : ∀ x ∈ before, AuditKernel.Derives (nativeRules enabled) (· ∈ seed) x)
    (hit : needed ∈ after) :
    AuditKernel.Derives (nativeRules enabled) (· ∈ seed) needed := by
  induction plan generalizing before with
  | nil =>
    change some before = some after at valid
    cases valid
    exact fromSeed _ hit
  | cons action rest ih =>
    simp only [replay] at valid
    split at valid
    · rename_i inActions
      cases next : step before action with
      | none => simp [next] at valid
      | some intermediate =>
        have result := a_checked_replay_step_has_all_of_its_inputs next
        simp only [next,Option.bind_some] at valid
        apply ih valid
        intro x hx
        rw [result.1] at hx
        rcases List.mem_cons.mp hx with same | old
        · subst x
          exact AuditKernel.Derives.apply action.rule
            (List.mem_map.mpr ⟨action,List.mem_of_elem_eq_true inActions,rfl⟩) (fun n hn => fromSeed n (result.2 n hn))
        · exact fromSeed _ old
    · cases valid

theorem checked_service_supplies_each_obligation
    (verified : check enabled plan seed obligations = true) (wanted : needed ∈ obligations) :
    AuditKernel.Derives (nativeRules enabled) (· ∈ seed) needed := by
  unfold check at verified
  split at verified
  · contradiction
  · rename_i after replayed
    exact replay_produces_a_native_derivation_for_each_available_service
      enabled plan seed after replayed (fun x hx => .initial x hx)
      (List.mem_of_elem_eq_true (List.all_eq_true.mp verified _ wanted))

-- One recipe for each replaced native action suffices. A recipe uses the
-- final basis of the whole selected bundle and can reuse services proved
-- earlier in the same finite derivation. No cyclic self-certificate works.
theorem all_baseline_services_survive_the_joint_replacement
    (old new : List Action) (base retained : List Need)
    (seeds : ∀ x ∈ base, AuditKernel.Derives (nativeRules new) (· ∈ retained) x)
    (recipes : ∀ a ∈ old, ∃ plan, check new plan a.premises [a.result] = true)
    (trace : AuditKernel.Derives (nativeRules old) (· ∈ base) need) :
    AuditKernel.Derives (nativeRules new) (· ∈ retained) need := by
  apply AuditKernel.changing_a_policy_requires_seed_and_rule_simulation
    (nativeRules old) (nativeRules new) (· ∈ base) (· ∈ retained) seeds _ need trace
  intro rule hr inputs
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
  obtain ⟨recipe,checked⟩ := recipes a ha
  have result := checked_service_supplies_each_obligation checked
    (show a.result ∈ [a.result] by simp)
  exact AuditKernel.positive_ND_closure_preserves_every_derivation
    (nativeRules new) (· ∈ a.premises) (· ∈ retained) inputs a.result result

structure Recipe where
  original : Action
  plan : List Action

structure Bundle where
  seedPlan : List Action
  recipes : List Recipe

def validBundle (old new : List Action) (base retained : List Need) (bundle : Bundle) : Bool :=
  check new bundle.seedPlan retained base &&
  old.all (fun a => bundle.recipes.any (fun r =>
    r.original == a && check new r.plan a.premises [a.result]))

-- This checks a finite adapter, not a whole-program search for recipes.
-- No admissible certificate selects the unchanged native rule graph.
def selected (old new : List Action) (base retained : List Need) (bundle : Bundle) :
    List Action × List Need :=
  if validBundle old new base retained bundle then (new,retained) else (old,base)

theorem invalid_bundle_uses_the_native_scope_without_partial_activation
    (unchecked : validBundle old new base retained bundle = false) :
    selected old new base retained bundle = (old,base) := by simp [selected,unchecked]

theorem a_checked_bundle_or_native_fallback_cannot_lose_a_baseline_track
    (old new : List Action) (base retained : List Need) (bundle : Bundle)
    (trace : AuditKernel.Derives (nativeRules old) (· ∈ base) track) :
    let use := selected old new base retained bundle
    AuditKernel.Derives (nativeRules use.1) (· ∈ use.2) track := by
  cases verified : validBundle old new base retained bundle
  · simpa [selected,verified] using trace
  · simp only [selected,verified,ite_true]
    have gates := Bool.and_eq_true_iff.mp verified
    apply all_baseline_services_survive_the_joint_replacement old new base retained _ _ trace
    · intro k present
      exact checked_service_supplies_each_obligation gates.1 present
    · intro action present
      obtain ⟨recipe,_,ok⟩ := List.any_eq_true.mp (List.all_eq_true.mp gates.2 action present)
      exact ⟨recipe.plan,(Bool.and_eq_true_iff.mp ok).2⟩

def coveredData : Need := ⟨.data,3,0,1⟩
def secondSourcePermission : Need := ⟨.sourcePermission,5,0,2⟩

theorem a_bound_data_witness_does_not_certify_source_permission :
    check [] [] [coveredData] [secondSourcePermission] = false := by decide

theorem a_recipe_cannot_use_future_permission_even_if_its_key_is_present :
    let usePermission : Action := ⟨[secondSourcePermission],coveredData⟩
    check [usePermission] [usePermission] [secondSourcePermission] [coveredData] = false := by decide

-- A completed replacement trace has materialized all its derivations.
-- Therefore a stopped new analysis may certify a baseline track only
-- using a witness that already exists in its sealed result.
theorem a_sealed_stop_has_every_baseline_track
    (old new : List Action) (base retained : List Need) (sealed : Need → Prop)
    (seeds : ∀ x ∈ base, AuditKernel.Derives (nativeRules new) (· ∈ retained) x)
    (recipes : ∀ a ∈ old, ∃ plan, check new plan a.premises [a.result] = true)
    (closed : AuditKernel.Closed (nativeRules new) (· ∈ retained) sealed)
    (trace : AuditKernel.Derives (nativeRules old) (· ∈ base) track) :
    sealed track :=
  AuditKernel.every_closed_store_contains_the_least_positive_result
    (nativeRules new) (· ∈ retained) sealed closed track
    (all_baseline_services_survive_the_joint_replacement old new base retained seeds recipes trace)

inductive Original where
  | zero | single | nd
  deriving DecidableEq

def select (demand backward : Bool) : Original → Bool
  | .zero => demand || backward
  | .single => demand
  | .nd => true

theorem demand_only_skips_two_native_guidance_classes :
    select false false .nd = true ∧ select false true .zero = true := by decide

theorem the_restored_gate_preserves_every_selected_native_row
    (demand backward : Bool) (original : Original) :
    select demand backward original =
      (demand || decide (original = .nd) || (backward && decide (original = .zero))) := by
  cases demand <;> cases backward <;> cases original <;> decide

def retainReply (complete dataCovered controlCovered : Bool) : Bool :=
  !(complete && dataCovered && controlCovered)

theorem if_the_source_control_witness_is_missing_keep_the_original_reply :
    retainReply true true false = true := by decide

theorem a_complete_certificate_can_still_remove_a_duplicate :
    retainReply true true true = false := by decide

theorem the_origin_aware_guard_retains_the_native_late_track :
    let kept := retainReply true true false
    (CoveredOrigin.cold (!kept) 2).deepTrack = true := by decide

end ServiceSimulation
