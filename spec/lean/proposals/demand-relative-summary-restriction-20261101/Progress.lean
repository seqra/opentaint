import Geometry
import Std

/-!
Finite progress and work witnesses. These results do not assert that arbitrary
programs reach a fixed point, or that every opposite run supplies the concrete
input required by this recurrence. The recurrence has an explicit finite target
and an available compatible derivation. It is not the analyzer's scheduler.
-/
namespace RelativeRestriction.Progress
set_option autoImplicit false

/-- An endpoint can expose one more counted field, up to its finite target. -/
def advance (target previous : Nat) : Nat := min target (previous + 1)

def advances (target : Nat) : Nat → Nat → Nat
  | 0, previous => min target previous
  | rounds + 1, previous => advance target (advances target rounds previous)

theorem advance_bounded (target previous : Nat) : advance target previous ≤ target :=
  Nat.min_le_left _ _

theorem advance_strict_before_target (target previous : Nat) (unfinished : previous < target) :
    advance target previous = previous + 1 := by
  simp only [advance]
  exact Nat.min_eq_right (by omega)

theorem advance_does_not_lose_depth (target previous : Nat) (within : previous ≤ target) :
    previous ≤ advance target previous := by
  unfold advance
  omega

theorem advances_closed (target rounds previous : Nat) :
    advances target rounds previous = min target (previous + rounds) := by
  induction rounds with
  | zero => simp [advances]
  | succ rounds ih =>
    simp only [advances, advance, ih]
    omega

theorem finite_target_is_reached (target previous : Nat) :
    advances target target previous = target := by
  rw [advances_closed]
  omega

theorem positive_pair_budget (global : Nat) (dp : Pattern) (positive : 1 ≤ global) :
    1 ≤ pairBudget global dp := by
  unfold pairBudget
  omega

theorem no_cut_once_guide_reaches_target (global : Nat) (dp : Pattern) (raw : Scalar)
    (globalFits : depth raw.path ≤ global)
    (guideFits : depth raw.path ≤ depth dp.path + 1) :
    limit (pairBudget global dp) raw = raw := by
  apply limit_within_identity
  unfold pairBudget
  omega

/- Executable summary-boundary slice of:
   wrap(p) { inner.g=p; outer.f=inner; return outer; }
   A valid opposite-run guide has Dc=p.[any]/T, Dp=ret.f.[any]/T.
   Exact root evidence admits p.$/T NORMAL under the unchanged C2 rule.
   The body needs global limit2 to construct ret.f.g.$/T.
   This witness starts from that complete guide; it does not fabricate a
   backward source action or claim a complete F1/B2/F3 driver execution. -/
def rootInitial : Pattern := ⟨0, [], .exact, 7⟩
def entryGuide : Pattern := ⟨0, [], .may, 7⟩
def exitGuide : Pattern := ⟨1, [.field 10], .may, 7⟩
def wrapResult : Scalar := ⟨⟨1, [.field 10, .field 11], .exact, 7⟩, .normal, false⟩

def fixedOriginalCapResult : Scalar := limit (depth rootInitial.path + 1) wrapResult
def pairedCapResult : Scalar := limit (pairBudget 2 exitGuide) wrapResult

theorem finite_wrap_needs_body_room :
    (limit 1 wrapResult).layer = .demand ∧ limit 2 wrapResult = wrapResult := by decide

theorem fixed_original_cap_still_loses_the_second_field :
    fixedOriginalCapResult.path = [.field 10] ∧
    fixedOriginalCapResult.tail = .may ∧
    fixedOriginalCapResult.layer = .demand := by decide

theorem paired_exit_cap_keeps_both_fields_and_normal :
    pairedCapResult = wrapResult ∧ pairedCapResult.layer = .normal := by decide

/-- No raw NORMAL record is kept when the actual admitted slice was cut. -/
def nativeCandidate (value : Scalar) : Option Scalar :=
  match value.layer with | .normal => some value | .demand => none

theorem no_uncut_record_rescue_in_fixed_cap_witness :
    nativeCandidate fixedOriginalCapResult = none := rfl

theorem admitted_precise_result_itself_is_record_candidate :
    nativeCandidate pairedCapResult = some wrapResult := rfl

/- A finite packed-leaf witness. The tree implementation can retain one shared
   prefix rather than 16 distinct terminal paths. This counts output memberships,
   not JVM time, internal body work, or all practical project workloads. -/
def deepLeaf (branch : Nat) : Scalar :=
  ⟨⟨0, [.field 1, .field branch, .field 100], .exact, 7⟩, .normal, true⟩
def leaves : List Scalar := (List.range 16).map deepLeaf
def compressed : List Scalar := (leaves.map (limit 1)).eraseDups
def sharedPrefix : Scalar := ⟨⟨0, [.field 1], .may, 7⟩, .demand, true⟩

theorem sixteen_deep_results_share_one_admitted_prefix :
    leaves.length = 16 ∧ compressed = [sharedPrefix] := by decide

theorem prefix_compression_retains_mark_and_protection :
    sharedPrefix.mark = 7 ∧ sharedPrefix.protection = true ∧ sharedPrefix.layer = .demand := by decide

/- A boundary-only cap cannot bound the number of operations already performed
   to construct its candidate. The exponential inverse-loop leaf family remains
   a valid counterexample to a whole-body complexity claim. -/
def inverseLeaves (bodyLimit : Nat) : Nat := 2 ^ (bodyLimit + 1) - 1

theorem inverse_body_work_is_not_a_publication_bound :
    inverseLeaves 1 = 3 ∧ inverseLeaves 3 = 15 ∧ inverseLeaves 7 = 255 := by decide

end RelativeRestriction.Progress
