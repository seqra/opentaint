import Domain

/- Exact guidance is not a lower bound on the next execution's layer.
   Actual layer and matching uncertainty determine the new starting layer. -/
namespace ExactDemand
set_option autoImplicit false

/-- The selected proof core is concrete FULL data only. FLOW keeps its existing policy. -/
def concreteCoreMark : Mark → Bool
  | .flow _ => false
  | .concrete _ => true

def validExactDemand (limit : Nat) (demand : Pattern) : Bool :=
  decide (demand.tail = .exact) && decide (demand.path.length ≤ limit) &&
    concreteCoreMark demand.mark && decide (0 < limit) && demand.excludedFields.isEmpty

def validActual (actual : Pattern) : Bool :=
  match actual.tail with
  | .exact | .may => actual.excludedFields.isEmpty
  | .star | .must => true

/-- MAY-to-EXACT is a provisional hypothesis even if an input header is NORMAL. -/
def exactSeedLayer (actual : Actual) : Layer :=
  match actual.pattern.tail with | .may => .demand | _ => actual.layer

def emitExact (limit : Nat) (demand : Demand) (actual : Actual) : Option Seed :=
  if validExactDemand limit demand.pattern && validActual actual.pattern &&
      exactGuards limit demand.pattern actual.pattern then
    some ⟨exactKey demand.pattern, exactSeedLayer actual⟩
  else none

/-- Previous guidance DEMAND does not make the new layer sticky. -/
theorem guidance_layer_is_not_starting_layer (limit : Nat) (pattern : Pattern)
    (left right : Layer) (actual : Actual) :
    emitExact limit ⟨pattern,left⟩ actual = emitExact limit ⟨pattern,right⟩ actual := rfl

theorem may_exact_admission_is_demand (limit : Nat) (demand : Demand) (actual : Pattern)
    (layer : Layer) (may : actual.tail = .may) (seed : Seed)
    (emitted : emitExact limit demand ⟨actual,layer⟩ = some seed) : seed.layer = .demand := by
  unfold emitExact at emitted
  split at emitted
  · cases emitted
    exact congrArg (fun tail => match tail with | .may => Layer.demand | _ => layer) may
  · cases emitted

theorem demand_actual_starts_demand (limit : Nat) (demand : Demand) (actual : Pattern)
    (seed : Seed) (emitted : emitExact limit demand ⟨actual,.demand⟩ = some seed) :
    seed.layer = .demand := by
  unfold emitExact at emitted
  split at emitted
  · cases emitted
    cases actual with
    | mk base path tail mark excluded => cases tail <;> rfl
  · cases emitted

theorem emitted_key_is_requested_exact (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) :
    seed.initial = exactKey demand.pattern := by
  unfold emitExact at emitted
  split at emitted
  · cases emitted; rfl
  · cases emitted

theorem emitted_key_is_never_zero (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) :
    seed.initial ≠ .zero := by
  rw [emitted_key_is_requested_exact limit demand actual seed emitted]
  intro impossible
  cases impossible

theorem guard_failure_emits_nothing (limit : Nat) (demand : Demand) (actual : Actual)
    (failed : exactGuards limit demand.pattern actual.pattern = false) :
    emitExact limit demand actual = none := by
  simp only [emitExact, failed, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- Every successful admission retains all unchanged matching guards. -/
theorem emitted_has_all_guards (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) :
    validExactDemand limit demand.pattern = true ∧ validActual actual.pattern = true ∧
    commonGuards limit (normalizeDemand demand.pattern) actual.pattern = true ∧
    exactGeometry demand.pattern actual.pattern = true := by
  unfold emitExact at emitted
  split at emitted
  next accepted =>
    have ⟨both, geometry⟩ := Bool.and_eq_true_iff.mp accepted
    have ⟨validDemand, validInput⟩ := Bool.and_eq_true_iff.mp both
    have ⟨common, shape⟩ := Bool.and_eq_true_iff.mp geometry
    exact ⟨validDemand, validInput, common, shape⟩
  next => cases emitted

theorem emitted_has_matching_base_mark_and_budgets (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) :
    demand.pattern.base = actual.pattern.base ∧
    markSub demand.pattern.mark actual.pattern.mark = true ∧
    demand.pattern.path.length ≤ limit ∧ actual.pattern.path.length ≤ limit := by
  obtain ⟨_, _, common, _⟩ := emitted_has_all_guards limit demand actual seed emitted
  obtain ⟨left, actualBudget⟩ := Bool.and_eq_true_iff.mp common
  obtain ⟨baseAndMark, demandBudget⟩ := Bool.and_eq_true_iff.mp left
  obtain ⟨baseMatch, markMatch⟩ := Bool.and_eq_true_iff.mp baseAndMark
  exact ⟨of_decide_eq_true baseMatch, markMatch,
    of_decide_eq_true demandBudget, of_decide_eq_true actualBudget⟩

/-- The start fact carries the admitted layer. Its intrinsic key shape does not reset it. -/
structure InitialEdge where
  premise : InitialKey
  conclusion : InitialKey
  layer : Layer
  deriving DecidableEq, Repr

/-- The ordinary AP initial table remains separate from admission. ZERO
    keeps its existing policy, supplied by admitZero's legacy adapter. -/
def intrinsicInitialLayer : InitialKey → Layer
  | .zero => .normal
  | .data pattern => match pattern.mark, pattern.tail with
    | .flow _, .may => .demand
    | .flow _, _ => .normal
    | .concrete _, .star | .concrete _, .may => .demand
    | .concrete _, _ => .normal

/-- Canonicalize before seen bits and coverage accounting. -/
def canonicalSeed (seed : Seed) : Seed :=
  ⟨seed.initial,join (intrinsicInitialLayer seed.initial) seed.layer⟩

theorem canonical_seed_is_idempotent (seed : Seed) :
    canonicalSeed (canonicalSeed seed) = canonicalSeed seed := by
  cases seed with
  | mk key layer =>
    unfold canonicalSeed
    cases intrinsicInitialLayer key <;> cases layer <;> rfl

def start (seed : Seed) : InitialEdge :=
  ⟨seed.initial,seed.initial,join (intrinsicInitialLayer seed.initial) seed.layer⟩

theorem demand_seed_starts_demand (key : InitialKey) :
    (start ⟨key,.demand⟩).layer = .demand := join_demand_right _

theorem exact_key_intrinsic_layer_is_normal (demand : Pattern) :
    intrinsicInitialLayer (exactKey demand) = .normal := by
  cases demand with
  | mk base path tail mark excluded => cases mark <;> rfl

theorem emitted_exact_seed_is_canonical (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) : canonicalSeed seed = seed := by
  have keyEq := emitted_key_is_requested_exact limit demand actual seed emitted
  cases seed with
  | mk key layer =>
    change key = exactKey demand.pattern at keyEq
    subst key
    unfold canonicalSeed
    rw [exact_key_intrinsic_layer_is_normal]
    cases layer <;> rfl

theorem concrete_star_cannot_be_promoted_by_descriptor (base : Nat) (path : List Nat)
    (mark : Nat) (descriptorLayer : Layer) :
    (start ⟨.data ⟨base,path,.star,.concrete mark,[]⟩,descriptorLayer⟩).layer = .demand := rfl

theorem start_preserves_initial_geometry (seed : Seed) :
    (start seed).premise = seed.initial ∧ (start seed).conclusion = seed.initial := ⟨rfl,rfl⟩

inductive Submitted where
  | zero (layer : Layer)
  | data (actual : Actual)
  deriving DecidableEq, Repr

/-- Permission is explicit. No data AP, including MAY, is a ZERO source. -/
def admitZero (explicitPermission : Bool) (existingZeroLayerPolicy : Layer) : Submitted → Option Seed
  | .zero _ => if explicitPermission then some ⟨.zero,existingZeroLayerPolicy⟩ else none
  | .data _ => none

theorem data_never_becomes_zero (permission : Bool) (zeroPolicy : Layer) (actual : Actual) :
    admitZero permission zeroPolicy (.data actual) = none := rfl

theorem zero_requires_permission (actualLayer policy : Layer) :
    admitZero false policy (.zero actualLayer) = none := rfl

theorem zero_preserves_existing_layer_policy (actualLayer policy : Layer) :
    admitZero true policy (.zero actualLayer) = some ⟨.zero,policy⟩ := rfl

namespace Controls

def demanded (path : List Nat := [1]) : Pattern := ⟨0,path,.exact,.concrete 7,[]⟩
def sameMay : Pattern := ⟨0,[1],.may,.concrete 7,[]⟩
def ancestorMay : Pattern := ⟨0,[],.may,.concrete 7,[]⟩
def exactActual : Pattern := ⟨0,[1],.exact,.concrete 7,[]⟩

theorem same_prefix_may_emits_exact_demand :
    emitExact 2 ⟨demanded,.demand⟩ ⟨sameMay,.normal⟩ =
      some ⟨exactKey demanded,.demand⟩ := rfl

theorem ancestor_may_emits_requested_exact_demand :
    emitExact 2 ⟨demanded,.normal⟩ ⟨ancestorMay,.demand⟩ =
      some ⟨exactKey demanded,.demand⟩ := rfl

theorem later_exact_normal_discharges_old_demand_layer :
    emitExact 2 ⟨demanded,.demand⟩ ⟨exactActual,.normal⟩ =
      some ⟨exactKey demanded,.normal⟩ := rfl

theorem exact_demand_input_keeps_demand :
    emitExact 2 ⟨demanded,.normal⟩ ⟨exactActual,.demand⟩ =
      some ⟨exactKey demanded,.demand⟩ := rfl

theorem different_mark_is_still_rejected :
    emitExact 2 ⟨demanded,.demand⟩ ⟨{sameMay with mark := .concrete 8},.normal⟩ = none := rfl

theorem wrong_base_is_still_rejected :
    emitExact 2 ⟨demanded,.demand⟩ ⟨{sameMay with base := 1},.normal⟩ = none := rfl

theorem unrelated_path_is_still_rejected :
    emitExact 2 ⟨demanded,.demand⟩ ⟨{sameMay with path := [2]},.normal⟩ = none := rfl

theorem descendant_actual_does_not_satisfy_exact_parent :
    emitExact 2 ⟨demanded,.demand⟩ ⟨{sameMay with path := [1,2]},.normal⟩ = none := rfl

theorem actual_field_exclusion_is_preserved :
    emitExact 2 ⟨demanded,.normal⟩
      ⟨⟨0,[],.must,.concrete 7,[1]⟩,.normal⟩ = none := rfl

theorem illegal_concrete_exact_demand_exclusion_is_rejected :
    emitExact 2 ⟨{demanded with excludedFields := [1,2]},.demand⟩ ⟨sameMay,.normal⟩ = none := rfl

theorem demand_budget_is_not_bypassed :
    emitExact 1 ⟨demanded [1,2],.normal⟩ ⟨ancestorMay,.normal⟩ = none := rfl

theorem actual_budget_is_not_bypassed :
    emitExact 1 ⟨demanded,.normal⟩ ⟨{sameMay with path := [1,2]},.normal⟩ = none := rfl

end Controls

end ExactDemand
