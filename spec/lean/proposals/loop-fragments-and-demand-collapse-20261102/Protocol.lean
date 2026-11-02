import Control
import Geometry
import Std

/-!
Local protocol laws for loop feedback projection.

The query supplies an eligibility answer and complete scoped precision paths.
This module does not prove that the three AP consumer adapters compute them. A
complete original is an opaque identity; it is not an enumerated ND member.
Projection changes only the scalar fact. Source/rule/static observations are
producer effects before this operation. C5 remains a separate complete-row
predicate. No result of the geometry query is publication permission.
-/
namespace LoopFragments.Protocol
open LoopFragments.Geometry
set_option autoImplicit false

structure State (nodes bases marks fields : Nat) where
  unit : Nat
  context : Nat
  wholeOriginal : Nat
  port : LoopFragments.Port nodes
  fact : Fact bases marks fields
  deriving DecidableEq, Repr

variable {nodes bases marks fields : Nat}

def gate (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw : State nodes bases marks fields) : Option (State nodes bases marks fields) :=
  (selectProject eligible global paths raw.fact).map fun fact => {raw with fact := fact}

theorem ineligible_is_dropped (global : Nat) (paths : List (Path fields))
    (raw : State nodes bases marks fields) : gate false global paths raw = none := rfl

theorem eligible_has_explicit_image (global : Nat) (paths : List (Path fields))
    (raw : State nodes bases marks fields) :
    gate true global paths raw = some {raw with fact := project global paths raw.fact} := rfl

theorem produced_has_source (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw result : State nodes bases marks fields)
    (found : gate eligible global paths raw = some result) :
    eligible = true ∧ result = {raw with fact := project global paths raw.fact} := by
  cases eligible with
  | false => cases found
  | true => exact ⟨rfl, (Option.some.inj found).symm⟩

theorem complete_scope_is_preserved (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw result : State nodes bases marks fields)
    (found : gate eligible global paths raw = some result) :
    result.unit = raw.unit ∧ result.context = raw.context ∧
    result.wholeOriginal = raw.wholeOriginal ∧ result.port = raw.port := by
  obtain ⟨_, same⟩ := produced_has_source eligible global paths raw result found
  rw [same]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem protected_support_is_preserved (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw result : State nodes bases marks fields)
    (found : gate eligible global paths raw = some result) :
    result.fact.base = raw.fact.base ∧ result.fact.mark = raw.fact.mark ∧
    result.fact.protection = raw.fact.protection := by
  obtain ⟨_, same⟩ := produced_has_source eligible global paths raw result found
  rw [same]
  exact ⟨project_base global paths raw.fact, project_mark global paths raw.fact,
    project_protection global paths raw.fact⟩

theorem useful_location_is_covered (global : Nat) (paths : List (Path fields))
    (raw : State nodes bases marks fields) (base : Fin bases) (mark : Fin marks)
    (location : Path fields) (actual : possible raw.fact base mark location) :
    ∃ result, gate true global paths raw = some result ∧
      possible result.fact base mark location := by
  exact ⟨{raw with fact := project global paths raw.fact}, rfl,
    project_possible_coverage global paths raw.fact base mark location actual⟩

theorem normal_result_is_original (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw result : State nodes bases marks fields)
    (found : gate eligible global paths raw = some result)
    (normal : result.fact.layer = .normal) : result = raw := by
  obtain ⟨_, same⟩ := produced_has_source eligible global paths raw result found
  have value : (project global paths raw.fact).layer = .normal := by simpa [same] using normal
  have unchanged := project_normal_is_unchanged global paths raw.fact value
  rw [same, unchanged]

theorem demand_result_remains_demand (eligible : Bool) (global : Nat) (paths : List (Path fields))
    (raw result : State nodes bases marks fields)
    (found : gate eligible global paths raw = some result)
    (demand : raw.fact.layer = .demand) : result.fact.layer = .demand := by
  obtain ⟨_, same⟩ := produced_has_source eligible global paths raw result found
  rw [same]
  exact project_demand_stays_demand global paths raw.fact demand

structure Produced (nodes bases marks fields : Nat) (Event : Type) where
  effects : List Event
  values : List (State nodes bases marks fields)

def finishProducer {Event : Type} (global : Nat)
    (eligible : State nodes bases marks fields → Bool)
    (paths : State nodes bases marks fields → List (Path fields))
    (raw : Produced nodes bases marks fields Event) : Produced nodes bases marks fields Event :=
  { effects := raw.effects,
    values := raw.values.filterMap fun value => gate (eligible value) global (paths value) value }

theorem producer_effects_preserved {Event : Type} (global : Nat)
    (eligible : State nodes bases marks fields → Bool)
    (paths : State nodes bases marks fields → List (Path fields))
    (raw : Produced nodes bases marks fields Event) :
    (finishProducer global eligible paths raw).effects = raw.effects := rfl

/-- Each row contains its own original and its own exit predicate. -/
structure PairedRow (nodes bases marks fields : Nat) where
  wholeOriginal : Nat
  port : LoopFragments.Port nodes
  accepts : Fact bases marks fields → Bool

def acceptsCompleteRow (row : PairedRow nodes bases marks fields)
    (state : State nodes bases marks fields) : Bool :=
  decide (row.wholeOriginal = state.wholeOriginal ∧ row.port = state.port) && row.accepts state.fact

def publish (rows : List (PairedRow nodes bases marks fields))
    (state : State nodes bases marks fields) : Option (State nodes bases marks fields) :=
  if rows.any (fun row => acceptsCompleteRow row state) then some state else none

theorem publication_requires_complete_row (rows : List (PairedRow nodes bases marks fields))
    (state result : State nodes bases marks fields)
    (found : publish rows state = some result) :
    result = state ∧ ∃ row ∈ rows, row.wholeOriginal = state.wholeOriginal ∧
      row.port = state.port ∧ row.accepts state.fact = true := by
  unfold publish at found
  split at found
  next admitted =>
    refine ⟨(Option.some.inj found).symm, ?_⟩
    obtain ⟨row, member, accepted⟩ := List.any_eq_true.mp admitted
    have separated : decide (row.wholeOriginal = state.wholeOriginal ∧ row.port = state.port) = true ∧
        row.accepts state.fact = true := by simpa only [acceptsCompleteRow, Bool.and_eq_true] using accepted
    obtain ⟨scope, exit⟩ := separated
    obtain ⟨original, port⟩ := of_decide_eq_true scope
    exact ⟨row, member, original, port, exit⟩
  next => cases found

theorem no_rows_no_publication (state : State nodes bases marks fields) :
    publish [] state = none := rfl

theorem gate_does_not_supply_a_missing_row (eligible : Bool) (global : Nat)
    (paths : List (Path fields)) (raw result : State nodes bases marks fields)
    (_found : gate eligible global paths raw = some result) :
    publish [] result = none := rfl

end LoopFragments.Protocol
