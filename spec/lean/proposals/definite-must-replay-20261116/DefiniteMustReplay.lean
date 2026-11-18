import DifferentReply
import PriorSupport

/- Saved native MUSTs use the existing definite lane only. This is a read
   policy change, not a record compactor, Target cancellation or new query.
   Old opposite-direction views and non-MUST saved reads are unchanged. -/
namespace DefiniteMustReplay
open NonEmptyPolicy NonEmptyRestriction
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768

structure Lane (α : Type) where
  actual : α
  pendingDemotion : Bool
  deriving DecidableEq, Repr

def lanes (mustPremise : Bool) (xs : List (Lane α)) : List (Lane α) :=
  if mustPremise then xs.filter (fun x => !x.pendingDemotion) else xs

theorem non_must_is_unchanged (xs : List (Lane α)) : lanes false xs = xs := rfl
theorem retained_lanes_are_old_lanes (xs : List (Lane α)) (x : Lane α)
    (h : x ∈ lanes true xs) : x ∈ xs := (List.mem_filter.mp h).1
theorem every_definite_lane_is_retained (xs : List (Lane α)) (x : Lane α)
    (h : x ∈ xs) (definite : x.pendingDemotion = false) : x ∈ lanes true xs := by
  exact List.mem_filter.mpr ⟨h,by simp [definite]⟩
theorem no_provisional_lane_is_retained (xs : List (Lane α)) (x : Lane α)
    (h : x ∈ lanes true xs) : x.pendingDemotion = false := by
  simpa using (List.mem_filter.mp h).2
theorem no_lanes_are_added (xs : List (Lane α)) : (lanes true xs).length ≤ xs.length :=
  List.length_filter_le _ _
theorem order_independent (xs ys : List (Lane α))
    (same : ∀ x, x ∈ xs ↔ x ∈ ys) (x : Lane α) :
    x ∈ lanes true xs ↔ x ∈ lanes true ys := by simp [lanes,same]
theorem idempotent (xs : List (Lane α)) : lanes true (lanes true xs) = lanes true xs := by
  simp [lanes,List.filter_filter]

def commit (pending : Bool) (v : Value) : Value := {v with demand := v.demand || pending}
def outputs (step : α → List Value) (xs : List (Lane α)) : List Value :=
  xs.flatMap fun lane => (step lane.actual).map (commit lane.pendingDemotion)

theorem no_new_output (step : α → List Value) (xs : List (Lane α)) (v : Value)
    (h : v ∈ outputs step (lanes true xs)) : v ∈ outputs step xs := by
  rcases List.mem_flatMap.mp h with ⟨lane,present,out⟩
  exact List.mem_flatMap.mpr ⟨lane,retained_lanes_are_old_lanes xs lane present,out⟩

theorem every_old_normal_data_output_is_preserved (step : α → List Value)
    (xs : List (Lane α)) (v : Value) (h : v ∈ outputs step xs)
    (normal : v.demand = false) : v ∈ outputs step (lanes true xs) := by
  rcases List.mem_flatMap.mp h with ⟨lane,present,out⟩
  rcases List.mem_map.mp out with ⟨raw,generated,same⟩
  have definite : lane.pendingDemotion = false := by
    have hn := congrArg Value.demand same
    rw [normal] at hn
    cases hp : lane.pendingDemotion
    · rfl
    · simp [commit,hp] at hn
  exact List.mem_flatMap.mpr ⟨lane,every_definite_lane_is_retained xs lane present definite,
    List.mem_map.mpr ⟨raw,generated,same⟩⟩

theorem retained_effect_input_is_literal (x : Lane α) :
    x ∈ lanes true [x] → (lanes true [x]) = [x] := by
  intro h
  have definite := no_provisional_lane_is_retained [x] x h
  simp [lanes,definite]

def covers (a required : Ap) : Bool :=
  a.tail == .must && match dropHead a.path required.path with
    | none => false
    | some [] => a.e.all required.e.contains
    | some (field :: _) => !a.e.contains field

def represents (path : Path) (excluded : List Nat) (location : Path) : Prop :=
  ∃ rest, location = path ++ rest ∧ admits .must excluded rest = true

theorem dropped_prefix_constructs_suffix (head word suffix : Path)
    (h : dropHead head word = some suffix) : word = head ++ suffix := by
  induction head generalizing word with
  | nil => simpa [dropHead] using h
  | cons a rest ih =>
      cases word with
      | nil => simp [dropHead] at h
      | cons b tail =>
          simp only [dropHead] at h
          split at h
          · rename_i same
            subst b
            simp [ih tail h]
          · contradiction

/-- Every required location is known uniform in the actual. Exclusions at
    an ancestor remain there; they are never moved onto a child. -/
theorem definite_geometry_covers_every_required_location (a required : Ap)
    (yes : covers a required = true) (location : Path)
    (needed : represents required.path required.e location) :
    represents a.path a.e location := by
  rcases needed with ⟨rest,located,allowed⟩
  unfold covers at yes
  simp only [Bool.and_eq_true] at yes
  have selected := yes.2
  cases suffix : dropHead a.path required.path with
  | none => simp [suffix] at selected
  | some lead =>
      have parent := dropped_prefix_constructs_suffix a.path required.path lead suffix
      rw [parent,List.append_assoc] at located
      refine ⟨lead ++ rest,located,?_⟩
      cases lead with
      | nil =>
          simp only [suffix] at selected
          cases rest with
          | nil => rfl
          | cons field more =>
              have forbid : required.e.contains field = false := by
                simpa [admits] using allowed
              have subset := List.all_eq_true.mp selected
              have notHere : a.e.contains field = false := by
                cases hc : a.e.contains field
                · rfl
                · have member := List.mem_of_elem_eq_true hc
                  have mustBe := subset field member
                  rw [forbid] at mustBe
                  contradiction
              simpa [admits] using notHere
      | cons field more => simpa [suffix,admits] using selected

def saved (record : Ap × Value) (actual : Offered) : Option Value :=
  if record.1.tail == .must && actual.ap.base == record.1.base &&
      actual.ap.mark == record.1.mark && covers actual.ap record.1 then
    some {record.2 with demand := actual.demand || record.2.demand}
  else none

theorem actual_demand_never_becomes_normal (record : Ap × Value) (a : Offered)
    (v : Value) (hit : saved record a = some v) (demand : a.demand = true) :
    v.demand = true := by
  unfold saved at hit
  split at hit
  · cases hit; simp [demand]
  · contradiction

theorem a_child_uniform_fact_cannot_prove_the_parent :
    covers DifferentUniformReply.fieldActual.ap DifferentUniformReply.rootUniform.1 = false := by decide

theorem real_exclusion_cases :
    covers ⟨0,[],.must,some 1,[1],[]⟩ ⟨0,[],.must,some 1,[1,2],[]⟩ = true ∧
    covers ⟨0,[],.must,some 1,[1],[]⟩ ⟨0,[],.must,some 1,[],[]⟩ = false ∧
    covers ⟨0,[],.must,some 1,[2],[]⟩ ⟨0,[1],.must,some 1,[2],[]⟩ = true ∧
    covers ⟨0,[],.must,some 1,[1],[]⟩ ⟨0,[1],.must,some 1,[],[]⟩ = false := by decide

theorem parent_root_is_an_explicit_missing_location :
    represents [] [] [] ∧ ¬ represents [1] [] [] := by
  constructor
  · exact ⟨[],rfl,rfl⟩
  · rintro ⟨rest,impossible,_⟩
    cases impossible

end DefiniteMustReplay
