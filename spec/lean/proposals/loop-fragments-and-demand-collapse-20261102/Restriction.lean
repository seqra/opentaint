import Geometry
import Std

/-!
Executable reference restriction without a native-composition preimage oracle.

Scope: Geometry.Fact, hence scalar finite bases/FULL marks, EXACT/MAY,
empty exclusions and one carried protection bit. A fixed pure observer returns
the normalized COMPLETE signatures in the selected query context: AL C2
emissions, F composed with persisted NORMAL AL then full-B paired C5 results,
next-body L C2 emissions, and ND restriction metadata arms. Batch counts are not semantic signatures.
The observer adapter, its complete scope and its AP transfer laws are explicit
external obligations. This module does not replace them with a geometry test.

If the raw observation is empty, drop the fact. Otherwise test the positive
proper prefixes shortest first. Each cut is MAY/DEMAND. Accept a cut only when
its complete observation equals the raw observation. Raw is the safe fallback.
The same fixed observer gives a deterministic and idempotent restriction.

This is a finite reference, not an efficient production pullback algorithm.
An optimized trie/pullback must return the same result or establish the same
complete-observation guard. ND arms are guidance only, not executable unary
summaries. The finite native-read example is not a production AP proof.
-/
namespace LoopFragments.Restriction
open LoopFragments.Geometry
set_option autoImplicit false

/-- Each component is an already normalized set/signature, not callback counts. -/
structure CompleteObservation (Admission Composition LoopAdmission NdMetadata : Type) where
  alAdmission : Admission
  nativeCompositionAndB : Composition
  lAdmission : LoopAdmission
  ndMetadata : NdMetadata
  deriving DecidableEq, Repr

/-- Executable first accepted natural below bound, in ascending order. -/
def leastAccepted (accept : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | bound + 1 =>
      match leastAccepted accept bound with
      | some depth => some depth
      | none => if accept bound then some bound else none

theorem leastAccepted_spec (accept : Nat → Bool) (bound : Nat) :
    match leastAccepted accept bound with
    | none => ∀ depth, depth < bound → accept depth = false
    | some depth => depth < bound ∧ accept depth = true ∧
        ∀ earlier, earlier < depth → accept earlier = false := by
  induction bound with
  | zero =>
      intro depth impossible
      exact False.elim (Nat.not_lt_zero _ impossible)
  | succ bound ih =>
      simp only [leastAccepted]
      cases previous : leastAccepted accept bound with
      | some depth =>
          simp only [previous] at ih ⊢
          exact ⟨Nat.lt_trans ih.1 (Nat.lt_succ_self _), ih.2⟩
      | none =>
          simp only [previous] at ih ⊢
          cases accepted : accept bound with
          | true => simp only [↓reduceIte]; exact ⟨Nat.lt_succ_self _, by trivial, ih⟩
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              intro depth within
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ within) with earlier | equal
              · exact ih depth earlier
              · simpa only [equal] using accepted

theorem leastAccepted_some (accept : Nat → Bool) (bound depth : Nat)
    (found : leastAccepted accept bound = some depth) :
    depth < bound ∧ accept depth = true ∧
      ∀ earlier, earlier < depth → accept earlier = false := by
  have result := leastAccepted_spec accept bound
  simpa only [found] using result

theorem leastAccepted_none_iff (accept : Nat → Bool) (bound : Nat) :
    leastAccepted accept bound = none ↔ ∀ depth, depth < bound → accept depth = false := by
  constructor
  · intro absent
    have result := leastAccepted_spec accept bound
    simpa only [absent] using result
  · intro allRejected
    cases found : leastAccepted accept bound with
    | none => rfl
    | some depth =>
        have result := leastAccepted_some accept bound depth found
        have incompatible := allRejected depth result.1
        rw [result.2.1] at incompatible
        cases incompatible

variable {bases marks fields : Nat}

def cut (raw : Fact bases marks fields) (depth : Nat) : Fact bases marks fields :=
  { raw with path := raw.path.take depth, tail := .may, layer := .demand }

def acceptedDepth {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) (depth : Nat) : Bool :=
  decide (0 < depth) && decide (observe (cut raw depth) = observe raw)

def chosen {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    Fact bases marks fields :=
  match leastAccepted (acceptedDepth observe raw) raw.path.length with
  | none => raw
  | some depth => cut raw depth

def restrict {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw : Fact bases marks fields) : Option (Fact bases marks fields) :=
  if isEmpty (observe raw) then none else some (chosen observe raw)

theorem acceptedDepth_iff {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) (depth : Nat) :
    acceptedDepth observe raw depth = true ↔
      0 < depth ∧ observe (cut raw depth) = observe raw := by
  simp [acceptedDepth, Bool.and_eq_true]

theorem chosen_shape {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    chosen observe raw = raw ∨
      ∃ depth, 0 < depth ∧ depth < raw.path.length ∧
        chosen observe raw = cut raw depth ∧ observe (cut raw depth) = observe raw ∧
        ∀ earlier, 0 < earlier → earlier < depth →
          observe (cut raw earlier) ≠ observe raw := by
  cases found : leastAccepted (acceptedDepth observe raw) raw.path.length with
  | none => exact Or.inl (by simp [chosen, found])
  | some depth =>
      have result := leastAccepted_some _ _ _ found
      have accepted := (acceptedDepth_iff observe raw depth).mp result.2.1
      refine Or.inr ⟨depth, accepted.1, result.1, by simp [chosen, found], accepted.2, ?_⟩
      intro earlier positive before equal
      have rejected := result.2.2 earlier before
      have included := (acceptedDepth_iff observe raw earlier).mpr ⟨positive, equal⟩
      rw [included] at rejected
      cases rejected

theorem chosen_observation_equal {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    observe (chosen observe raw) = observe raw := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]
  · rw [selected]; exact equal

theorem chosen_base {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    (chosen observe raw).base = raw.base := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]
  · rw [selected]; rfl

theorem chosen_mark {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    (chosen observe raw).mark = raw.mark := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]
  · rw [selected]; rfl

theorem chosen_protection {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    (chosen observe raw).protection = raw.protection := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]
  · rw [selected]; rfl

theorem cut_possible_coverage (raw : Fact bases marks fields) (depth : Nat)
    (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) : possible (cut raw depth) base mark location := by
  obtain ⟨sameBase, sameMark, path⟩ := actual
  refine ⟨sameBase, sameMark, ?_⟩
  change (raw.path.take depth).IsPrefix location
  cases tail : raw.tail with
  | exact =>
      have same : location = raw.path := by simpa only [possiblePath, tail] using path
      rw [same]
      exact List.take_prefix depth raw.path
  | may =>
      exact prefix_transitive (List.take_prefix depth raw.path)
        (by simpa only [possiblePath, tail] using path)

theorem chosen_possible_coverage {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields)
    (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) :
    possible (chosen observe raw) base mark location := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]; exact actual
  · rw [selected]; exact cut_possible_coverage raw depth base mark location actual

theorem chosen_normal_is_raw {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields)
    (normal : (chosen observe raw).layer = .normal) : chosen observe raw = raw := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · exact unchanged
  · rw [selected] at normal; cases normal

theorem chosen_real_loss_is_may_demand {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields)
    (loss : chosen observe raw ≠ raw) :
    (chosen observe raw).tail = .may ∧ (chosen observe raw).layer = .demand := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · exact False.elim (loss unchanged)
  · rw [selected]; exact ⟨rfl, rfl⟩

theorem restrict_none_iff {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw : Fact bases marks fields) : restrict observe isEmpty raw = none ↔ isEmpty (observe raw) = true := by
  unfold restrict
  cases empty : isEmpty (observe raw) <;> simp

theorem restrict_some_iff {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields) :
    restrict observe isEmpty raw = some result ↔
      isEmpty (observe raw) = false ∧ result = chosen observe raw := by
  unfold restrict
  cases empty : isEmpty (observe raw) <;> simp [eq_comm]

theorem restricted_observation_equal {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields)
    (selected : restrict observe isEmpty raw = some result) : observe result = observe raw := by
  rw [((restrict_some_iff observe isEmpty raw result).mp selected).2]
  exact chosen_observation_equal observe raw

/-- Thus every component, including all full-B pairs and every ND arm, is equal. -/
theorem every_observation_projection_equal {Obs Component : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (component : Obs → Component) (raw result : Fact bases marks fields)
    (selected : restrict observe isEmpty raw = some result) :
    component (observe result) = component (observe raw) :=
  congrArg component (restricted_observation_equal observe isEmpty raw result selected)

theorem restriction_never_manufactures_eligibility {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields) (selected : restrict observe isEmpty raw = some result) :
    isEmpty (observe raw) = false ∧ isEmpty (observe result) = false := by
  have original := ((restrict_some_iff observe isEmpty raw result).mp selected).1
  exact ⟨original, by rw [restricted_observation_equal observe isEmpty raw result selected]; exact original⟩

theorem restricted_metadata_retained {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields) (selected : restrict observe isEmpty raw = some result) :
    result.base = raw.base ∧ result.mark = raw.mark ∧ result.protection = raw.protection := by
  rw [((restrict_some_iff observe isEmpty raw result).mp selected).2]
  exact ⟨chosen_base observe raw, chosen_mark observe raw, chosen_protection observe raw⟩

theorem restricted_possible_coverage {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields) (selected : restrict observe isEmpty raw = some result)
    (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) : possible result base mark location := by
  rw [((restrict_some_iff observe isEmpty raw result).mp selected).2]
  exact chosen_possible_coverage observe raw base mark location actual

theorem restricted_normal_requires_raw {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw result : Fact bases marks fields) (selected : restrict observe isEmpty raw = some result)
    (normal : result.layer = .normal) : result = raw := by
  have shape := ((restrict_some_iff observe isEmpty raw result).mp selected).2
  rw [shape] at normal ⊢
  exact chosen_normal_is_raw observe raw normal

def candidateDirectory (raw : Fact bases marks fields) : List Nat :=
  (List.range raw.path.length).filter fun depth => decide (0 < depth)

theorem candidate_directory_finite (raw : Fact bases marks fields) :
    (candidateDirectory raw).length ≤ raw.path.length := by
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem chosen_cut_belongs_to_finite_directory {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) (depth : Nat)
    (found : leastAccepted (acceptedDepth observe raw) raw.path.length = some depth) :
    depth ∈ candidateDirectory raw := by
  have result := leastAccepted_some _ _ _ found
  have accepted := (acceptedDepth_iff observe raw depth).mp result.2.1
  simp [candidateDirectory, result.1, accepted.1]

theorem cut_cut_shallower (raw : Fact bases marks fields) (first second : Nat)
    (shallower : second ≤ first) : cut (cut raw first) second = cut raw second := by
  simp [cut, List.take_take, Nat.min_eq_left shallower]

theorem chosen_idempotent {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (raw : Fact bases marks fields) :
    chosen observe (chosen observe raw) = chosen observe raw := by
  rcases chosen_shape observe raw with unchanged | ⟨depth, positive, shorter, selected, equal, minimal⟩
  · rw [unchanged]; exact unchanged
  · rw [selected]
    have size : (cut raw depth).path.length = depth := by
      simp [cut, List.length_take, Nat.min_eq_left (Nat.le_of_lt shorter)]
    have none : leastAccepted (acceptedDepth observe (cut raw depth)) depth = none := by
      apply (leastAccepted_none_iff _ _).mpr
      intro earlier before
      cases accepted : acceptedDepth observe (cut raw depth) earlier with
      | false => rfl
      | true =>
          have membership := (acceptedDepth_iff observe (cut raw depth) earlier).mp accepted
          rw [cut_cut_shallower raw depth earlier (Nat.le_of_lt before), equal] at membership
          exact False.elim (minimal earlier membership.1 before membership.2)
    simp [chosen, size, none]

theorem restrict_idempotent {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw : Fact bases marks fields) :
    (restrict observe isEmpty raw).bind (restrict observe isEmpty) = restrict observe isEmpty raw := by
  unfold restrict
  cases empty : isEmpty (observe raw) with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some]
      simp [chosen_observation_equal observe raw, chosen_idempotent observe raw, empty]

theorem restriction_is_deterministic {Obs : Type} [DecidableEq Obs]
    (observe : Fact bases marks fields → Obs) (isEmpty : Obs → Bool)
    (raw left right : Fact bases marks fields)
    (first : restrict observe isEmpty raw = some left)
    (second : restrict observe isEmpty raw = some right) : left = right :=
  Option.some.inj (first.symm.trans second)

/-- Finite geometric toy: a frozen NORMAL read f strips f. Full-B C5
    retains the first remaining field as MAY/DEMAND. The AL C2 result is
    the same scoped permission key. The complete observer includes both.
    This is intentionally not an assertion about the production AP API. -/
abbrev ToyFact := Fact 2 1 3
abbrev ToyObservation := CompleteObservation (List ToyFact) (List ToyFact) (List ToyFact) (List Nat)

def toyObserve (fact : ToyFact) : ToyObservation :=
  if fact.base = 0 ∧ fact.path.head? = some 0 then
    let alInitial : ToyFact := ⟨0, fact.mark, [0], .may, .demand, fact.protection⟩
    let nativeResult : ToyFact :=
      { fact with base := 1, path := fact.path.drop 1 }
    let bResult : ToyFact :=
      { nativeResult with path := nativeResult.path.take 1, tail := .may, layer := .demand }
    ⟨[alInitial], [bResult], [alInitial], [0]⟩
  else ⟨[], [], [], []⟩

def toyEmpty (observation : ToyObservation) : Bool :=
  observation.alAdmission.isEmpty && observation.nativeCompositionAndB.isEmpty && observation.lAdmission.isEmpty

def toyRaw : ToyFact := ⟨0, 0, [0, 1, 2], .exact, .demand, true⟩
def toyExpectedB : ToyFact := ⟨1, 0, [1], .may, .demand, true⟩

theorem toy_raw_native_read_then_b_selects_g_may :
    (toyObserve toyRaw).nativeCompositionAndB = [toyExpectedB] := by decide

theorem toy_one_field_cut_changes_full_b_observation :
    toyObserve (cut toyRaw 1) ≠ toyObserve toyRaw := by decide

theorem toy_two_field_cut_keeps_all_observations :
    toyObserve (cut toyRaw 2) = toyObserve toyRaw := by decide

theorem toy_shortest_safe_cut_is_two_fields :
    restrict toyObserve toyEmpty toyRaw = some (cut toyRaw 2) := by decide

theorem toy_selected_result_is_idempotent :
    restrict toyObserve toyEmpty (cut toyRaw 2) = some (cut toyRaw 2) := by decide

end LoopFragments.Restriction
