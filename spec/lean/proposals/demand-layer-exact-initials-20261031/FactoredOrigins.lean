import NDProjection

/- One already compatible canonical header/proof partition. Each column lists
   accepted NORMAL origins for one required literal. No rule/header/context
   compatibility is inferred by this membership algorithm. -/
namespace ExactDemand.FactoredOrigins
open NDProjection
set_option autoImplicit false

inductive Binding : List (List Origin) → List Origin → Type where
  | nil : Binding [] []
  | cons {column : List Origin} {columns : List (List Origin)}
      {origin : Origin} {origins : List Origin}
      (member : origin ∈ column) (rest : Binding columns origins) :
      Binding (column :: columns) (origin :: origins)

structure Witness (allowed : Origin → Bool) (columns : List (List Origin)) where
  origins : List Origin
  binding : Binding columns origins
  accepted : origins.all allowed = true

def test (allowed : Origin → Bool) (columns : List (List Origin)) : Bool :=
  columns.all fun column => column.any allowed

/-- List.find? returns the executable choice; the proof never uses choice. -/
def chooseColumn (allowed : Origin → Bool) (column : List Origin)
    (existsAllowed : column.any allowed = true) :
    {origin : Origin // origin ∈ column ∧ allowed origin = true} :=
  match found : column.find? allowed with
  | some origin => ⟨origin, List.mem_of_find?_eq_some found, List.find?_some found⟩
  | none => by
      have impossible : False := by
        obtain ⟨origin, member, accepted⟩ := List.any_eq_true.mp existsAllowed
        exact (List.find?_eq_none.mp found) origin member accepted
      exact False.elim impossible

def choose (allowed : Origin → Bool) (columns : List (List Origin))
    (accepted : test allowed columns = true) : Witness allowed columns :=
  match columns with
  | [] => ⟨[], .nil, rfl⟩
  | column :: rest => by
      have split : column.any allowed = true ∧ test allowed rest = true :=
        Bool.and_eq_true_iff.mp accepted
      let first := chooseColumn allowed column split.1
      let remaining := choose allowed rest split.2
      exact ⟨first.val :: remaining.origins, .cons first.property.1 remaining.binding,
        by simp only [List.all_cons, first.property.2, remaining.accepted, Bool.and_self]⟩

theorem binding_implies_test (allowed : Origin → Bool)
    {columns : List (List Origin)} {origins : List Origin}
    (binding : Binding columns origins) (accepted : origins.all allowed = true) :
    test allowed columns = true := by
  induction binding with
  | nil => rfl
  | @cons column columns origin origins member rest ih =>
    have split := Bool.and_eq_true_iff.mp accepted
    have first : column.any allowed = true := List.any_eq_true.mpr ⟨origin,member,split.1⟩
    have remaining := ih split.2
    change (column.any allowed && test allowed columns) = true
    rw [first, remaining]
    rfl

theorem test_iff_complete_binding (allowed : Origin → Bool) (columns : List (List Origin)) :
    test allowed columns = true ↔ Nonempty (Witness allowed columns) := by
  constructor
  · intro accepted; exact ⟨choose allowed columns accepted⟩
  · intro ⟨witness⟩; exact binding_implies_test allowed witness.binding witness.accepted

def product : List (List Origin) → List (List Origin)
  | [] => [[]]
  | column :: rest => column.flatMap fun origin => (product rest).map (origin :: ·)

theorem binding_is_product_member {columns : List (List Origin)} {origins : List Origin}
    (binding : Binding columns origins) : origins ∈ product columns := by
  induction binding with
  | nil => exact List.mem_singleton_self _
  | cons member rest ih =>
    exact List.mem_flatMap.mpr ⟨_,member,List.mem_map.mpr ⟨_,ih,rfl⟩⟩

theorem product_member_implies_test (allowed : Origin → Bool)
    (columns : List (List Origin)) (origins : List Origin)
    (member : origins ∈ product columns) (accepted : origins.all allowed = true) :
    test allowed columns = true := by
  induction columns generalizing origins with
  | nil => rfl
  | cons column rest ih =>
    obtain ⟨origin, inColumn, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨tail, inProduct, same⟩ := List.mem_map.mp mapped
    subst origins
    have split := Bool.and_eq_true_iff.mp accepted
    have headAccepted : column.any allowed = true := List.any_eq_true.mpr ⟨origin,inColumn,split.1⟩
    have tailAccepted := ih tail inProduct split.2
    change (column.any allowed && test allowed rest) = true
    rw [headAccepted, tailAccepted]
    rfl

def eagerTest (allowed : Origin → Bool) (columns : List (List Origin)) : Bool :=
  (product columns).any fun origins => origins.all allowed

theorem eager_iff_factored (allowed : Origin → Bool) (columns : List (List Origin)) :
    eagerTest allowed columns = true ↔ test allowed columns = true := by
  constructor
  · intro accepted
    obtain ⟨origins, member, supported⟩ := List.any_eq_true.mp accepted
    exact product_member_implies_test allowed columns origins member supported
  · intro accepted
    let witness := choose allowed columns accepted
    exact List.any_eq_true.mpr ⟨witness.origins,binding_is_product_member witness.binding,witness.accepted⟩

def originOrZero (wanted : Origin) (candidate : Origin) : Bool :=
  decide (candidate = wanted) || decide (candidate = .zero)

def zeroOnly (candidate : Origin) : Bool := decide (candidate = .zero)

/-- The arm must already occur in the union; all-ZERO support cannot invent P. -/
def normalArm (wanted : Origin) (columns : List (List Origin)) : Bool :=
  decide (wanted ∈ columns.flatten) && test (originOrZero wanted) columns

theorem absent_origin_cannot_be_invented (wanted : Origin) (columns : List (List Origin))
    (absent : wanted ∉ columns.flatten) : normalArm wanted columns = false := by
  simp only [normalArm, decide_eq_false absent, Bool.false_and]

def normalArmWitness (wanted : Origin) (columns : List (List Origin))
    (accepted : normalArm wanted columns = true) : Witness (originOrZero wanted) columns :=
  choose _ _ (Bool.and_eq_true_iff.mp accepted).2

theorem normal_arm_iff_existing_origin_and_complete_supported_binding
    (wanted : Origin) (columns : List (List Origin)) :
    normalArm wanted columns = true ↔
      wanted ∈ columns.flatten ∧ Nonempty (Witness (originOrZero wanted) columns) := by
  constructor
  · intro accepted
    have split := Bool.and_eq_true_iff.mp accepted
    exact ⟨of_decide_eq_true split.1, ⟨choose _ _ split.2⟩⟩
  · intro ⟨member, supported⟩
    have tested := (test_iff_complete_binding (originOrZero wanted) columns).mpr supported
    unfold normalArm
    rw [decide_eq_true member, tested]
    rfl

def zeroWitness (columns : List (List Origin)) (accepted : test zeroOnly columns = true) :
    Witness zeroOnly columns := choose _ _ accepted

def normalInputs (origins : List Origin) : List Input :=
  origins.map fun origin => ⟨origin,.normal,0⟩

theorem selected_normal_binding_has_normal_cube (origins : List Origin) :
    cubeLayer (normalInputs origins) = .normal := by
  induction origins with
  | nil => rfl
  | cons origin rest ih =>
    change join .normal (cubeLayer (normalInputs rest)) = .normal
    rw [ih]
    rfl

theorem selected_binding_has_same_support_test (wanted : Origin) (origins : List Origin) :
    supportsWholeWitness wanted (normalInputs origins) = origins.all (originOrZero wanted) := by
  induction origins with
  | nil => rfl
  | cons origin rest ih =>
    change ((decide (origin = .zero) || decide (origin = wanted)) &&
      supportsWholeWitness wanted (normalInputs rest)) = _
    rw [ih, Bool.or_comm]
    rfl

theorem normal_factored_arm_has_a_whole_normal_dependency_witness
    (wanted : Origin) (columns : List (List Origin))
    (accepted : normalArm wanted columns = true) :
    armLayer wanted (normalInputs (normalArmWitness wanted columns accepted).origins) = .normal := by
  unfold armLayer
  rw [selected_binding_has_same_support_test,
    (normalArmWitness wanted columns accepted).accepted]
  exact selected_normal_binding_has_normal_cube _

def scanChecks (allowed : Origin → Bool) : List Origin → Nat
  | [] => 0
  | origin :: rest => if allowed origin then 1 else 1 + scanChecks allowed rest

theorem scan_checks_bounded_by_column_length (allowed : Origin → Bool) (column : List Origin) :
    scanChecks allowed column ≤ column.length := by
  induction column with
  | nil => exact Nat.le_refl _
  | cons origin rest ih =>
    unfold scanChecks
    split
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · rw [Nat.add_comm 1 (scanChecks allowed rest)]
      exact Nat.succ_le_succ ih

def binaryColumns (n : Nat) : List (List Origin) := List.replicate n [.input 0,.zero]

def scanBudget (columns : List (List Origin)) : Nat := (columns.map List.length).sum

theorem binary_product_cardinality (n : Nat) : (product (binaryColumns n)).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have previous : (product (List.replicate n [.input 0,.zero])).length = 2 ^ n := ih
    simp only [binaryColumns, List.replicate_succ, product, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.length_append, List.length_map]
    rw [previous]
    simp only [Nat.pow_succ, Nat.mul_two]

theorem binary_scan_budget (n : Nat) : scanBudget (binaryColumns n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 + scanBudget (binaryColumns n) = 2 * (n + 1)
    rw [ih, Nat.mul_succ]
    exact Nat.add_comm _ _

/-- A fresh membership in one existing canonical column. Arity and all
    header/context compatibility are unchanged. An out-of-range index is a no-op. -/
def growColumn : List (List Origin) → Nat → Origin → List (List Origin)
  | [], _, _ => []
  | column :: rest, 0, added => (added :: column) :: rest
  | column :: rest, index + 1, added => column :: growColumn rest index added

theorem irrelevant_growth_preserves_column_test (allowed : Origin → Bool)
    (columns : List (List Origin)) (index : Nat) (added : Origin)
    (irrelevant : allowed added = false) :
    test allowed (growColumn columns index added) = test allowed columns := by
  induction columns generalizing index with
  | nil => rfl
  | cons column rest ih =>
    cases index with
    | zero =>
      change ((allowed added || column.any allowed) && test allowed rest) = _
      rw [irrelevant]
      rfl
    | succ index =>
      change (column.any allowed && test allowed (growColumn rest index added)) = _
      rw [ih index]
      rfl

theorem distinct_nonzero_origin_is_irrelevant (wanted added : Nat) (different : added ≠ wanted) :
    originOrZero (.input wanted) (.input added) = false := by
  simp [originOrZero, different]

theorem nonzero_growth_only_changes_its_own_origin_test (columns : List (List Origin))
    (index wanted added : Nat) (different : added ≠ wanted) :
    test (originOrZero (.input wanted)) (growColumn columns index (.input added)) =
      test (originOrZero (.input wanted)) columns :=
  irrelevant_growth_preserves_column_test _ _ _ _ (distinct_nonzero_origin_is_irrelevant wanted added different)

theorem nonzero_growth_preserves_all_zero_test (columns : List (List Origin)) (index added : Nat) :
    test zeroOnly (growColumn columns index (.input added)) = test zeroOnly columns :=
  irrelevant_growth_preserves_column_test _ _ _ _ rfl

theorem growth_preserves_existing_origin_membership (columns : List (List Origin))
    (index : Nat) (added wanted : Origin) (present : wanted ∈ columns.flatten) :
    wanted ∈ (growColumn columns index added).flatten := by
  induction columns generalizing index with
  | nil => cases present
  | cons column rest ih =>
    cases index with
    | zero =>
      rcases List.mem_append.mp present with inColumn | inRest
      · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ inColumn))
      · exact List.mem_append.mpr (Or.inr inRest)
    | succ index =>
      rcases List.mem_append.mp present with inColumn | inRest
      · exact List.mem_append.mpr (Or.inl inColumn)
      · exact List.mem_append.mpr (Or.inr (ih index inRest))

theorem nonzero_growth_preserves_other_existing_normal_arm (columns : List (List Origin))
    (index wanted added : Nat) (different : added ≠ wanted)
    (present : Origin.input wanted ∈ columns.flatten) :
    normalArm (.input wanted) (growColumn columns index (.input added)) =
      normalArm (.input wanted) columns := by
  unfold normalArm
  rw [decide_eq_true present,
    decide_eq_true (growth_preserves_existing_origin_membership columns index (.input added) (.input wanted) present),
    nonzero_growth_only_changes_its_own_origin_test columns index wanted added different]

/-- Runtime candidates come from the existing origin union. ZERO membership
    growth must revisit that union; nonzero growth tests just the added origin. -/
def revisitOrigins (existing : List Origin) : Origin → List Origin
  | .zero => existing
  | added@(.input _) => [added]

theorem omitted_existing_origin_is_unchanged_after_incremental_growth
    (columns : List (List Origin)) (index wanted : Nat) (added : Origin)
    (present : Origin.input wanted ∈ columns.flatten)
    (omitted : Origin.input wanted ∉ revisitOrigins columns.flatten added) :
    normalArm (.input wanted) (growColumn columns index added) = normalArm (.input wanted) columns := by
  cases added with
  | zero => exact False.elim (omitted present)
  | input added =>
    have different : added ≠ wanted := by
      intro same
      subst added
      exact omitted (List.mem_singleton_self _)
    exact nonzero_growth_preserves_other_existing_normal_arm columns index wanted added different present

namespace Controls

theorem p_or_zero_chooses_a_full_binding_without_products :
    test (originOrZero (.input 0)) [[.input 0,.input 1],[.zero],[.input 0]] = true := rfl

theorem one_missing_column_blocks_normal_arm :
    normalArm (.input 0) [[.input 0],[.input 1]] = false := rfl

theorem all_zero_binding_is_checked_separately :
    test zeroOnly [[.input 0,.zero],[.zero,.input 1]] = true ∧
    test zeroOnly [[.input 0,.zero],[.input 1]] = false := ⟨rfl,rfl⟩

theorem zero_alternatives_do_not_invent_an_absent_origin :
    normalArm (.input 99) [[.zero],[.zero]] = false := rfl

theorem nonzero_membership_growth_can_unlock_its_own_old_origin :
    normalArm (.input 0) [[.input 0],[.input 1]] = false ∧
    normalArm (.input 0) (growColumn [[.input 0],[.input 1]] 1 (.input 0)) = true := ⟨rfl,rfl⟩

theorem zero_membership_growth_can_unlock_multiple_existing_origins :
    normalArm (.input 0) [[.input 0,.input 1],[.input 2]] = false ∧
    normalArm (.input 1) [[.input 0,.input 1],[.input 2]] = false ∧
    normalArm (.input 0) (growColumn [[.input 0,.input 1],[.input 2]] 1 .zero) = true ∧
    normalArm (.input 1) (growColumn [[.input 0,.input 1],[.input 2]] 1 .zero) = true := ⟨rfl,rfl,rfl,rfl⟩

theorem zero_growth_can_unlock_the_all_zero_binding :
    test zeroOnly [[.zero],[.input 2]] = false ∧
    test zeroOnly (growColumn [[.zero],[.input 2]] 1 .zero) = true := ⟨rfl,rfl⟩

end Controls
end ExactDemand.FactoredOrigins
