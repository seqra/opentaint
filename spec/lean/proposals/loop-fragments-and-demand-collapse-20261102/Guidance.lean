import Geometry
import Admission

/-!
ND flattening is LOOP-RESTRICTION METADATA ONLY.

One fully formed executable ND edge keeps its complete original premise.
Its restriction view has one unary row for each real member. The view can
conservatively keep a fact when any member is relevant. It is never used
as a collection of executable unary rules or stored executable summaries.

Scope: finite concrete FULL-mark nonstatic patterns, positive conjunctive
member binding, typed ZERO, direction orientation, original/layer/protection
retention. The ordinary rule evaluator supplies these already formed
premises and bound witnesses. Negative guards, AP overlap/C2 matching,
packed facts, scheduling and the JVM adapter are outside this module.
The generic matching theorem below accepts the existing match predicate;
it does not replace that predicate with endpoint equality in production.
-/
namespace LoopFragments.Guidance
open LoopFragments.Geometry
set_option autoImplicit false

abbrev Pattern (bases marks fields : Nat) := Admission.Initial bases marks fields

inductive Endpoint (bases marks fields : Nat) where
  | zero
  | data (pattern : Pattern bases marks fields)
  deriving DecidableEq, Repr

inductive Premise (bases marks fields : Nat) where
  | zero
  | all (members : List (Pattern bases marks fields))
  deriving DecidableEq, Repr

structure Edge (bases marks fields : Nat) where
  original : Premise bases marks fields
  conclusion : Pattern bases marks fields
  layer : Layer
  protection : Bool := false
  deriving DecidableEq, Repr

structure UnaryGuidance (bases marks fields : Nat) where
  source : Endpoint bases marks fields
  image : Endpoint bases marks fields
  deriving DecidableEq, Repr

variable {bases marks fields : Nat}

def flatten (edge : Edge bases marks fields) : List (UnaryGuidance bases marks fields) :=
  match edge.original with
  | .zero => [⟨.zero, .data edge.conclusion⟩]
  | .all members => members.map fun member => ⟨.data member, .data edge.conclusion⟩

/-- Building the restriction view retains the one full executable edge. -/
def restrictionView (edge : Edge bases marks fields) :
    Edge bases marks fields × List (UnaryGuidance bases marks fields) := ⟨edge, flatten edge⟩

theorem restriction_view_retains_executable_edge (edge : Edge bases marks fields) :
    (restrictionView edge).1 = edge := rfl

/-- The actual C2/replay matching predicate can be supplied here unchanged. -/
def metadataEligible (matching : Endpoint bases marks fields → Bool)
    (rows : List (UnaryGuidance bases marks fields)) : Bool :=
  rows.any fun row => matching row.source

theorem flatten_has_each_real_member (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (member : Pattern bases marks fields) (belongs : member ∈ members) :
    (⟨.data member, .data edge.conclusion⟩ : UnaryGuidance bases marks fields) ∈ flatten edge := by
  simp only [flatten, same]
  exact List.mem_map.mpr ⟨member, belongs, rfl⟩

theorem any_relevant_member_keeps_metadata (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (member : Pattern bases marks fields) (belongs : member ∈ members)
    (matching : Endpoint bases marks fields → Bool) (relevant : matching (.data member) = true) :
    metadataEligible matching (flatten edge) = true := by
  apply List.any_eq_true.mpr
  exact ⟨⟨.data member, .data edge.conclusion⟩,
    flatten_has_each_real_member edge members same member belongs, relevant⟩

theorem flattened_rows_have_real_members (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (row : UnaryGuidance bases marks fields) (belongs : row ∈ flatten edge) :
    ∃ member ∈ members, row.source = .data member ∧ row.image = .data edge.conclusion := by
  rw [flatten, same] at belongs
  obtain ⟨member, contained, equals⟩ := List.mem_map.mp belongs
  subst row
  exact ⟨member, contained, rfl, rfl⟩

theorem nonzero_flatten_never_invents_zero (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (row : UnaryGuidance bases marks fields) (belongs : row ∈ flatten edge) : row.source ≠ .zero := by
  obtain ⟨_, _, source, _⟩ := flattened_rows_have_real_members edge members same row belongs
  rw [source]
  intro impossible
  cases impossible

theorem empty_members_have_no_guidance (conclusion : Pattern bases marks fields)
    (layer : Layer) (protection : Bool) :
    flatten (⟨.all [], conclusion, layer, protection⟩ : Edge bases marks fields) = [] := rfl

theorem genuine_zero_has_only_explicit_zero_guidance (conclusion : Pattern bases marks fields)
    (layer : Layer) (protection : Bool) :
    flatten (⟨.zero, conclusion, layer, protection⟩ : Edge bases marks fields) =
      [⟨.zero, .data conclusion⟩] := rfl

/-- This finite binding model is the EXISTING complete-premise execution lane.
    An invalid empty member list does not become an unconditional ZERO rule. -/
def bound (original : Premise bases marks fields) (available : List (Endpoint bases marks fields)) : Bool :=
  match original with
  | .zero => available.contains .zero
  | .all members => !members.isEmpty && members.all fun member => available.contains (.data member)

structure Result (bases marks fields : Nat) where
  original : Premise bases marks fields
  conclusion : Pattern bases marks fields
  layer : Layer
  protection : Bool
  deriving DecidableEq, Repr

/-- Edge.layer already includes the ordinary engine's binding-layer join.
    Metadata has no operation that can construct or promote this result. -/
def execute (edge : Edge bases marks fields) (available : List (Endpoint bases marks fields)) :
    Option (Result bases marks fields) :=
  if bound edge.original available then
    some ⟨edge.original, edge.conclusion, edge.layer, edge.protection⟩
  else none

theorem emitted_result_keeps_full_original (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (result : Result bases marks fields)
    (produced : execute edge available = some result) :
    result.original = edge.original ∧ result.conclusion = edge.conclusion ∧
      result.layer = edge.layer ∧ result.protection = edge.protection := by
  unfold execute at produced
  split at produced
  · cases Option.some.inj produced
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases produced

theorem incomplete_premise_has_no_execution (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (incomplete : bound edge.original available = false) :
    execute edge available = none := by simp only [execute, incomplete, Bool.false_eq_true, ↓reduceIte]

theorem empty_members_never_execute (conclusion : Pattern bases marks fields) (layer : Layer)
    (protection : Bool) (available : List (Endpoint bases marks fields)) :
    execute (⟨.all [], conclusion, layer, protection⟩ : Edge bases marks fields) available = none := rfl

theorem fully_bound_nonzero_has_member_witness (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (available : List (Endpoint bases marks fields)) (complete : bound edge.original available = true) :
    ∃ member ∈ members, available.contains (.data member) = true := by
  cases members with
  | nil => simp [bound, same] at complete
  | cons head rest =>
      rw [same] at complete
      change (head :: rest).all (fun member => available.contains (.data member)) = true at complete
      exact ⟨head, List.mem_cons_self, List.all_eq_true.mp complete head List.mem_cons_self⟩

theorem fully_bound_execution_is_metadata_eligible (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (complete : bound edge.original available = true) :
    metadataEligible (fun endpoint => available.contains endpoint) (flatten edge) = true := by
  cases same : edge.original with
  | zero => simpa only [bound, same, flatten, metadataEligible, List.any_cons, List.any_nil, Bool.or_false] using complete
  | all members =>
      obtain ⟨member, belongs, reached⟩ := fully_bound_nonzero_has_member_witness edge members same available complete
      exact any_relevant_member_keeps_metadata edge members same member belongs _ reached

/-- Restriction may keep an existing result; it cannot manufacture a result
    from a unary guidance row. Source/rule execution remains `execute`. -/
def restrictExecution (edge : Edge bases marks fields) (available : List (Endpoint bases marks fields))
    (matching : Endpoint bases marks fields → Bool) : Option (Result bases marks fields) :=
  (execute edge available).filter fun _ => metadataEligible matching (flatten edge)

theorem restriction_result_was_really_executed (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (matching : Endpoint bases marks fields → Bool)
    (result : Result bases marks fields) (kept : restrictExecution edge available matching = some result) :
    execute edge available = some result := by
  unfold restrictExecution at kept
  cases actual : execute edge available with
  | none =>
      simp only [actual, Option.filter_none] at kept
      cases kept
  | some raw =>
      rw [actual] at kept
      by_cases eligible : metadataEligible matching (flatten edge) = true
      · simpa [Option.filter_some, eligible] using kept
      · simp [Option.filter_some, eligible] at kept

theorem guidance_cannot_create_normal (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (matching : Endpoint bases marks fields → Bool)
    (result : Result bases marks fields) (kept : restrictExecution edge available matching = some result)
    (normal : result.layer = .normal) :
    bound edge.original available = true ∧ edge.layer = .normal ∧ result.original = edge.original := by
  have actual := restriction_result_was_really_executed edge available matching result kept
  have same := emitted_result_keeps_full_original edge available result actual
  refine ⟨?_, same.2.2.1.symm.trans normal, same.1⟩
  unfold execute at actual
  split at actual
  next complete => exact complete
  next => cases actual

theorem metadata_for_all_bound_members_does_not_remove_execution (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) (complete : bound edge.original available = true) :
    restrictExecution edge available (fun endpoint => available.contains endpoint) = execute edge available := by
  simp only [restrictExecution, fully_bound_execution_is_metadata_eligible edge available complete]
  cases execute edge available <;> rfl

inductive Direction where | forward | backward deriving DecidableEq, Repr

def opposite : Direction → Direction
  | .forward => .backward
  | .backward => .forward

structure DemandRow (bases marks fields : Nat) where
  entry : Endpoint bases marks fields
  exit : Endpoint bases marks fields
  deriving DecidableEq, Repr

def orient (producer consumer : Direction) (row : UnaryGuidance bases marks fields) : DemandRow bases marks fields :=
  if producer = consumer then ⟨row.source, row.image⟩ else ⟨row.image, row.source⟩

def orientedRows (producer consumer : Direction) (edge : Edge bases marks fields) :
    List (DemandRow bases marks fields) := (flatten edge).map (orient producer consumer)

theorem opposite_guidance_has_entry_conclusion_exit_member (producer : Direction)
    (member conclusion : Pattern bases marks fields) :
    orient producer (opposite producer) ⟨.data member, .data conclusion⟩ =
      (⟨.data conclusion, .data member⟩ : DemandRow bases marks fields) := by cases producer <;> rfl

theorem same_direction_guidance_keeps_orientation (producer : Direction)
    (row : UnaryGuidance bases marks fields) :
    orient producer producer row = (⟨row.source, row.image⟩ : DemandRow bases marks fields) := by simp [orient]

theorem each_member_has_an_opposite_demand_row (producer : Direction) (edge : Edge bases marks fields)
    (members : List (Pattern bases marks fields)) (same : edge.original = .all members)
    (member : Pattern bases marks fields) (belongs : member ∈ members) :
    (⟨.data edge.conclusion, .data member⟩ : DemandRow bases marks fields) ∈
      orientedRows producer (opposite producer) edge := by
  have source := flatten_has_each_real_member edge members same member belongs
  apply List.mem_map.mpr
  exact ⟨⟨.data member, .data edge.conclusion⟩, source,
    opposite_guidance_has_entry_conclusion_exit_member producer member edge.conclusion⟩

def xT : Pattern 3 3 1 := ⟨0, 0, [], .exact⟩
def yU : Pattern 3 3 1 := ⟨1, 1, [], .exact⟩
def retV : Pattern 3 3 1 := ⟨2, 2, [], .exact⟩
def conjunction : Edge 3 3 1 := ⟨.all [xT, yU], retV, .normal, true⟩

theorem example_both_guidance_rows :
    flatten conjunction = [⟨.data xT, .data retV⟩, ⟨.data yU, .data retV⟩] := rfl

theorem example_one_member_keeps_guidance :
    metadataEligible (fun endpoint => ([Endpoint.data xT] : List (Endpoint 3 3 1)).contains endpoint)
      (flatten conjunction) = true := by decide

theorem example_one_member_cannot_emit_v :
    execute conjunction [.data xT] = none ∧
    restrictExecution conjunction [.data xT] (fun endpoint => ([Endpoint.data xT] : List (Endpoint 3 3 1)).contains endpoint) = none := by decide

theorem example_complete_binding_emits_once_with_full_original :
    execute conjunction [.data xT, .data yU] =
      some ⟨.all [xT, yU], retV, .normal, true⟩ := by decide

theorem example_opposite_rows_are_c_to_each_i :
    orientedRows .forward .backward conjunction =
      [⟨.data retV, .data xT⟩, ⟨.data retV, .data yU⟩] := by decide

end LoopFragments.Guidance
