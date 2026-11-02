import Geometry
import Guidance

/-!
Strict shape-growth gate for loop SUMMARY restriction.

ZERO has depth zero. A unary summary needs the new restriction exactly
when its conclusion prefix is strictly deeper than its premise prefix.
Equal/shrinking summaries pass unchanged through this shape gate.

An ND edge supplies the existing metadata-only unary arms. Classifying
them neither replaces its whole executable premise nor changes ordinary
ND execution. No minimum/maximum depth is assigned to a full ND premise.

Scope: counted nonstatic fields, finite concrete mark labels, typed ZERO,
and summary prefix geometry in the CURRENT summary direction. The gate
does not create source permissions or replace ordinary call processing.
Static uncounted anchors, typed Targets, E/mx, aliases and packed forests
require the integration adapters. The exact-suffix depth theorem assumes
a definite prefix match and suffix-preserving transfer. It is NOT a depth
theorem for ancestor MAY inputs. An executable MAY counterexample states
that distinction below.
-/
namespace LoopFragments.Shape
open LoopFragments.Geometry
open LoopFragments.Guidance
set_option autoImplicit false

variable {bases marks fields : Nat}

def depth : Endpoint bases marks fields → Nat
  | .zero => 0
  | .data pattern => pattern.path.length

def needsRestriction (summary : UnaryGuidance bases marks fields) : Bool :=
  decide (depth summary.source < depth summary.image)

/-- The restriction operation is supplied by the selected loop protocol.
    This function only decides whether the shape gate invokes it. -/
def applyGate {α : Type} (summary : UnaryGuidance bases marks fields)
    (restriction : α → α) (candidate : α) : α :=
  if needsRestriction summary then restriction candidate else candidate

theorem zero_depth : depth (Endpoint.zero : Endpoint bases marks fields) = 0 := rfl

theorem data_depth (pattern : Pattern bases marks fields) :
    depth (.data pattern) = pattern.path.length := rfl

theorem strict_growth_requires_restriction (summary : UnaryGuidance bases marks fields)
    (grows : depth summary.source < depth summary.image) : needsRestriction summary = true := by
  simp only [needsRestriction, grows, decide_true]

theorem nonincreasing_shape_does_not_require_restriction (summary : UnaryGuidance bases marks fields)
    (bound : depth summary.image ≤ depth summary.source) : needsRestriction summary = false := by
  simp only [needsRestriction, Nat.not_lt.mpr bound, decide_false]

theorem equal_shape_passes_unchanged {α : Type} (summary : UnaryGuidance bases marks fields)
    (same : depth summary.image = depth summary.source) (restriction : α → α) (candidate : α) :
    applyGate summary restriction candidate = candidate := by
  simp only [applyGate, nonincreasing_shape_does_not_require_restriction summary (Nat.le_of_eq same),
    Bool.false_eq_true, ↓reduceIte]

theorem shrinking_shape_passes_unchanged {α : Type} (summary : UnaryGuidance bases marks fields)
    (smaller : depth summary.image < depth summary.source) (restriction : α → α) (candidate : α) :
    applyGate summary restriction candidate = candidate := by
  simp only [applyGate, nonincreasing_shape_does_not_require_restriction summary (Nat.le_of_lt smaller),
    Bool.false_eq_true, ↓reduceIte]

theorem growing_shape_invokes_only_supplied_restriction {α : Type}
    (summary : UnaryGuidance bases marks fields) (grows : depth summary.source < depth summary.image)
    (restriction : α → α) (candidate : α) :
    applyGate summary restriction candidate = restriction candidate := by
  simp only [applyGate, strict_growth_requires_restriction summary grows, ↓reduceIte]

/-- Ordinary definite-prefix transfer carries the same suffix to the target. -/
def exactSuffixApplication (target suffix : Path fields) : Path fields := target ++ suffix

theorem ordinary_exact_suffix_nonincrease (source target suffix : Path fields)
    (bound : target.length ≤ source.length) :
    (exactSuffixApplication target suffix).length ≤ (source ++ suffix).length := by
  simp only [exactSuffixApplication, List.length_append]
  exact Nat.add_le_add_right bound suffix.length

theorem ordinary_exact_suffix_equal (source target suffix : Path fields)
    (same : target.length = source.length) :
    (exactSuffixApplication target suffix).length = (source ++ suffix).length := by
  simp only [exactSuffixApplication, List.length_append, same]

theorem ordinary_exact_suffix_strict_decrease (source target suffix : Path fields)
    (smaller : target.length < source.length) :
    (exactSuffixApplication target suffix).length < (source ++ suffix).length := by
  simp only [exactSuffixApplication, List.length_append]
  exact Nat.add_lt_add_right smaller suffix.length

theorem ordinary_exact_suffix_has_same_depth_delta (source target suffix : Path fields) :
    (exactSuffixApplication target suffix).length + source.length =
      (source ++ suffix).length + target.length := by
  simp [exactSuffixApplication, List.length_append, Nat.add_comm, Nat.add_left_comm]

/-- A narrow executable AP cell: empty-E, full T carried through a STAR/FLOW
    summary, actual MAY strictly above the premise. Its image is target MAY/D.
    This is not the complete summary application interpreter. -/
def mayAncestorApplication (source target actual : Path fields) : Option (Path fields × Tail × Layer) :=
  if actual.IsPrefix source ∧ actual ≠ source then some (target, .may, .demand) else none

def rootT : Pattern 3 3 2 := ⟨0, 0, [], .exact⟩
def fieldT : Pattern 3 3 2 := ⟨0, 0, [0], .exact⟩
def deepU : Pattern 3 3 2 := ⟨1, 1, [0, 1], .exact⟩
def resultV : Pattern 3 3 2 := ⟨2, 2, [1], .exact⟩

theorem zero_to_named_field_is_growth :
    needsRestriction (⟨Endpoint.zero, .data fieldT⟩ : UnaryGuidance 3 3 2) = true := by decide

theorem zero_to_root_is_not_growth :
    needsRestriction (⟨Endpoint.zero, .data rootT⟩ : UnaryGuidance 3 3 2) = false := by decide

theorem zero_to_root_passes_unchanged {α : Type} (restriction : α → α) (candidate : α) :
    applyGate (⟨Endpoint.zero, .data rootT⟩ : UnaryGuidance 3 3 2) restriction candidate = candidate := rfl

theorem equal_prefixes_can_increase_a_may_actual :
    ([1] : Path 2).length = ([0] : Path 2).length ∧
    mayAncestorApplication ([0] : Path 2) [1] [] = some ([1], .may, .demand) ∧
    ([] : Path 2).length < ([1] : Path 2).length := by decide

theorem shrinking_prefixes_can_increase_a_may_actual :
    ([1] : Path 2).length < ([0, 0, 0] : Path 2).length ∧
    mayAncestorApplication ([0, 0, 0] : Path 2) [1] [] = some ([1], .may, .demand) ∧
    ([] : Path 2).length < ([1] : Path 2).length := by decide

/-- The classified list is metadata; retain the complete original edge beside it. -/
def classifiedView (edge : Edge bases marks fields) :
    Edge bases marks fields × List (UnaryGuidance bases marks fields × Bool) :=
  ⟨edge, (flatten edge).map fun arm => (arm, needsRestriction arm)⟩

theorem classification_keeps_whole_executable_edge (edge : Edge bases marks fields) :
    (classifiedView edge).1 = edge := rfl

theorem classification_does_not_change_execution (edge : Edge bases marks fields)
    (available : List (Endpoint bases marks fields)) :
    execute (classifiedView edge).1 available = execute edge available := rfl

theorem classification_preserves_every_unary_metadata_arm (edge : Edge bases marks fields)
    (arm : UnaryGuidance bases marks fields) (belongs : arm ∈ flatten edge) :
    (arm, needsRestriction arm) ∈ (classifiedView edge).2 :=
  List.mem_map.mpr ⟨arm, belongs, rfl⟩

def mixedDepthNd : Edge 3 3 2 := ⟨.all [rootT, deepU], resultV, .normal, true⟩

theorem nd_arms_receive_different_shape_decisions :
    (classifiedView mixedDepthNd).2 =
      [(⟨.data rootT, .data resultV⟩, true),
       (⟨.data deepU, .data resultV⟩, false)] := by decide

theorem nd_shape_metadata_does_not_enable_single_member_execution :
    execute (classifiedView mixedDepthNd).1 [.data rootT] = none := by decide

theorem nd_shape_metadata_preserves_complete_execution :
    execute (classifiedView mixedDepthNd).1 [.data rootT, .data deepU] =
      some ⟨.all [rootT, deepU], resultV, .normal, true⟩ := by decide

end LoopFragments.Shape
