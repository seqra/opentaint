import TargetZeroKernel

/-!
Constructive ND and seed-event controls for the selected Target design.

General result: finite layer aggregation is NORMAL iff every contributor is
NORMAL. Binary result: two distinct required slots, at one actual call, use the
complete origin union and the aggregate layer. The exact AP/mark/field binding
that supplies a contributor is an external adapter. This module does not infer
a complete ND witness from the existence of one fact or from duplicate seeds.

Output equality includes Target ids, premise and layer. Duplicate insertion is
proved independent of output membership for the finite all-pairs join. This is
not a proof of production cache, queue or scheduler idempotence.
-/
namespace TargetZeroND
open TargetZeroKernel
set_option autoImplicit false
set_option linter.constructorNameAsVariable false

def joinLayers : List Layer → Layer
  | [] => .normal
  | head :: rest => composeLayer head (joinLayers rest)

theorem compose_normal_iff (a b : Layer) :
    composeLayer a b = .normal ↔ a = .normal ∧ b = .normal := by
  cases a <;> cases b <;> simp [composeLayer]

theorem join_normal_iff_all_normal (layers : List Layer) :
    joinLayers layers = .normal ↔ ∀ layer ∈ layers, layer = .normal := by
  induction layers with
  | nil =>
      constructor
      · intro _ layer member; cases member
      · intro _; rfl
  | cons head rest ih =>
      constructor
      · intro normal layer member
        have parts := (compose_normal_iff head (joinLayers rest)).mp normal
        rcases List.mem_cons.mp member with same | later
        · exact same.trans parts.1
        · exact ih.mp parts.2 layer later
      · intro allNormal
        apply (compose_normal_iff head (joinLayers rest)).mpr
        refine ⟨allNormal head (List.mem_cons.mpr (.inl rfl)), ?_⟩
        apply ih.mpr
        intro layer member
        exact allNormal layer (List.mem_cons.mpr (.inr member))

inductive Slot where
  | left | right
  deriving DecidableEq, Repr

/-- Binary scope: each contributing binding has ZERO or one ordinary origin. -/
inductive Origin where
  | zero | atom (a : Atom)
  deriving DecidableEq, Repr

def unionOrigin : Origin → Origin → Premise
  | .zero, .zero => .zero
  | .zero, .atom a => .ap a
  | .atom a, .zero => .ap a
  | .atom a, .atom b => if a == b then .ap a else .both a b

theorem union_zero_iff_both_zero (left right : Origin) :
    unionOrigin left right = .zero ↔ left = .zero ∧ right = .zero := by
  cases left <;> cases right <;> simp [unionOrigin]
  split <;> simp

structure Contributor where
  call : Nat
  slot : Slot
  origin : Origin
  layer : Layer
  deriving DecidableEq, Repr

def ndAt (owner call reportId : Nat) (left right : Contributor) : Option Summary :=
  if left.call == call && right.call == call && left.slot == .left && right.slot == .right then
    some (forwardSinkTarget owner (unionOrigin left.origin right.origin)
      (joinLayers [left.layer, right.layer]) reportId)
  else none

def dedupExact {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: rest => if x ∈ rest then dedupExact rest else x :: dedupExact rest

theorem dedup_membership {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    x ∈ dedupExact xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedupExact]
  | cons head rest ih =>
      by_cases present : head ∈ rest
      · simp [dedupExact, present, ih]
        intro same
        simpa [same] using present
      · simp [dedupExact, present, ih]

def ndOutputs (owner call reportId : Nat) (state : List Contributor) : List Summary :=
  dedupExact (state.flatMap fun left => state.filterMap (ndAt owner call reportId left))

theorem output_iff_complete_pair (owner call reportId : Nat) (state : List Contributor)
    (summary : Summary) : summary ∈ ndOutputs owner call reportId state ↔
      ∃ left ∈ state, ∃ right ∈ state, ndAt owner call reportId left right = some summary := by
  simp only [ndOutputs, dedup_membership, List.mem_flatMap, List.mem_filterMap]

/-- Executable witnesses are reused from the finite state; no choice is needed. -/
theorem output_membership_transport (owner call reportId : Nat)
    (old fresh : List Contributor) (sameMembers : ∀ c, c ∈ old ↔ c ∈ fresh)
    (summary : Summary) :
    summary ∈ ndOutputs owner call reportId old ↔ summary ∈ ndOutputs owner call reportId fresh := by
  rw [output_iff_complete_pair, output_iff_complete_pair]
  constructor
  · rintro ⟨left, leftMember, right, rightMember, paired⟩
    exact ⟨left, (sameMembers left).mp leftMember, right, (sameMembers right).mp rightMember, paired⟩
  · rintro ⟨left, leftMember, right, rightMember, paired⟩
    exact ⟨left, (sameMembers left).mpr leftMember, right, (sameMembers right).mpr rightMember, paired⟩

theorem duplicate_seed_independent (owner call reportId : Nat) (state : List Contributor)
    (seed : Contributor) (summary : Summary) :
    summary ∈ ndOutputs owner call reportId (state ++ [seed, seed]) ↔
      summary ∈ ndOutputs owner call reportId (state ++ [seed]) := by
  apply output_membership_transport
  intro contributor
  simp

def pairCandidates (state : List Contributor) : List (Contributor × Contributor) :=
  state.flatMap fun left => state.map fun right => (left, right)

def findCompletePair (owner call reportId : Nat) (state : List Contributor)
    (summary : Summary) : Option (Contributor × Contributor) :=
  (pairCandidates state).find? fun pair => decide (ndAt owner call reportId pair.1 pair.2 = some summary)

theorem pair_search_succeeds (owner call reportId : Nat) (state : List Contributor)
    (summary : Summary) (member : summary ∈ ndOutputs owner call reportId state) :
    (findCompletePair owner call reportId state summary).isSome = true := by
  obtain ⟨left, leftMember, right, rightMember, paired⟩ :=
    (output_iff_complete_pair owner call reportId state summary).mp member
  apply List.find?_isSome.mpr
  refine ⟨(left, right), ?_, decide_eq_true paired⟩
  exact List.mem_flatMap.mpr ⟨left, leftMember, List.mem_map.mpr ⟨right, rightMember, rfl⟩⟩

/-- Finite search returns the actual complete pair, not merely a Prop-level
    existence claim. This witness can be evaluated without any choice axiom. -/
def outputPairWitness (owner call reportId : Nat) (state : List Contributor)
    (summary : Summary) (member : summary ∈ ndOutputs owner call reportId state) :
    {pair : Contributor × Contributor // pair.1 ∈ state ∧ pair.2 ∈ state ∧
      ndAt owner call reportId pair.1 pair.2 = some summary} := by
  let result := findCompletePair owner call reportId state summary
  have found := pair_search_succeeds owner call reportId state summary member
  let pair := result.get found
  have foundPair : findCompletePair owner call reportId state summary = some pair :=
    Option.eq_some_of_isSome found
  refine ⟨pair, ?_⟩
  have pairMember := List.mem_of_find?_eq_some foundPair
  obtain ⟨left, leftMember, rightMap⟩ := List.mem_flatMap.mp pairMember
  obtain ⟨right, rightMember, same⟩ := List.mem_map.mp rightMap
  have leftMember' : pair.1 ∈ state := by
    rw [← congrArg Prod.fst same]
    exact leftMember
  have rightMember' : pair.2 ∈ state := by
    rw [← congrArg Prod.snd same]
    exact rightMember
  have pairMatchesProof : decide (ndAt owner call reportId pair.1 pair.2 = some summary) = true :=
    List.find?_some (p := fun (candidate : Contributor × Contributor) =>
      decide (ndAt owner call reportId candidate.1 candidate.2 = some summary)) foundPair
  exact ⟨leftMember', rightMember', of_decide_eq_true pairMatchesProof⟩

namespace Controls

def leftNormal : Contributor := ⟨4, .left, .zero, .normal⟩
def rightNormal : Contributor := ⟨4, .right, .zero, .normal⟩
def leftDemand : Contributor := ⟨4, .left, .zero, .demand⟩
def rightDemand : Contributor := ⟨4, .right, .zero, .demand⟩
def rightWrongCall : Contributor := ⟨5, .right, .zero, .normal⟩
def leftOrigin : Contributor := ⟨4, .left, .atom .a, .normal⟩
def normalResult : Summary := layeredTargetSummary 2 .zero .normal 9
def demandResult : Summary := targetSummary 2 .zero

def normalPairWitness := outputPairWitness 2 4 9 [leftNormal, rightNormal] normalResult (by decide)

theorem complete_normal_keeps_interned_id :
    ndOutputs 2 4 9 [leftNormal, rightNormal] = [normalResult] := by decide

theorem either_demand_contributor_makes_anonymous_target :
    ndOutputs 2 4 9 [leftDemand, rightNormal] = [demandResult] ∧
    ndOutputs 2 4 9 [leftNormal, rightDemand] = [demandResult] := by decide

theorem partial_and_duplicate_seed_do_not_complete_nd :
    ndOutputs 2 4 9 [leftNormal] = [] ∧
    ndOutputs 2 4 9 [leftNormal, leftNormal] = [] := by decide

theorem different_calls_do_not_complete_nd :
    ndOutputs 2 4 9 [leftNormal, rightWrongCall] = [] := by decide

theorem complete_origin_union_prevents_false_zero_report :
    ndOutputs 2 4 9 [leftOrigin, rightNormal] = [layeredTargetSummary 2 (.ap .a) .normal 9] ∧
    collectReports [2] (ndOutputs 2 4 9 [leftOrigin, rightNormal]) = [] := by decide

theorem normal_and_demand_routes_both_survive :
    normalResult ∈ ndOutputs 2 4 9 [leftNormal, leftDemand, rightNormal] ∧
    demandResult ∈ ndOutputs 2 4 9 [leftNormal, leftDemand, rightNormal] ∧
    collectReports [2] (ndOutputs 2 4 9 [leftNormal, leftDemand, rightNormal]) = [9] ∧
    continuationRelevant demandResult = true := by decide

theorem duplicate_seed_same_reports_and_guidance :
    ndOutputs 2 4 9 [leftNormal, rightNormal, rightNormal] = [normalResult] ∧
    ndOutputs 2 4 9 [leftDemand, rightNormal, rightNormal] = [demandResult] := by decide

def checks : Bool :=
  decide (ndOutputs 2 4 9 [leftNormal, rightNormal] = [normalResult]) &&
  decide (ndOutputs 2 4 9 [leftDemand, rightNormal] = [demandResult]) &&
  decide (ndOutputs 2 4 9 [leftNormal, rightDemand] = [demandResult]) &&
  decide (ndOutputs 2 4 9 [leftNormal, leftNormal] = []) &&
  decide (ndOutputs 2 4 9 [leftNormal, rightWrongCall] = []) &&
  decide (collectReports [2] (ndOutputs 2 4 9 [leftOrigin, rightNormal]) = [])

theorem checks_pass : checks = true := rfl
end Controls

#print axioms join_normal_iff_all_normal
#print axioms union_zero_iff_both_zero
#print axioms output_iff_complete_pair
#print axioms output_membership_transport
#print axioms duplicate_seed_independent
#print axioms outputPairWitness
#print axioms Controls.normalPairWitness
#print axioms Controls.checks_pass
#eval Controls.checks
#eval Controls.normalPairWitness.val

end TargetZeroND
