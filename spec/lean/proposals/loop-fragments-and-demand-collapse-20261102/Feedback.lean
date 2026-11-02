import Shape

/-!
Counterexample to testing growing feedback only at AL and the enclosing exit.

One field symbol is sufficient. A natural denotes an exact T path made of
that many f fields relative to the current x. `sourceFF` assigns at depth2
without clearing other paths. Reading x.f drops one field and cannot carry
an exact mark at the old root into the child. A root sink observes depth0.

The normal body is `sourceFF(x); x = x.f; sinkRootT(x)`. The first body's
ZERO-derived result is depth1; the second body consumes that result and
reaches the root sink. An empty AL and an enclosing Target-only exit have
no DATA consumer for depth1. The selected two-test gate therefore removes
the required value. Producer effects before that gate cannot repair this:
the first sink check has not succeeded.

This is an executable exact-path reference counterexample, not an AP
extractor, source-permission or whole-driver theorem. The separate native
driver controls in controls.md cover the current Kotlin pieces. The selected repair also checks next-body L demand. The model proves
that a successful L check retains the value and restores the observation.
Constructing production L demand is an AP/outline adapter obligation.
-/
namespace LoopFragments.Feedback
open LoopFragments.Geometry
open LoopFragments.Guidance
set_option autoImplicit false

def sourceFF (facts : List Nat) : List Nat := 2 :: facts

def readF (facts : List Nat) : List Nat :=
  facts.filterMap fun depth => match depth with
    | 0 => none
    | depth + 1 => some depth

def body (facts : List Nat) : List Nat := readF (sourceFF facts)

def sinkHit (facts : List Nat) : Bool := facts.contains 0

def intermediate : Pattern 1 1 1 := ⟨0, 0, [0], .exact⟩

def sourceBodySummary : UnaryGuidance 1 1 1 := ⟨.zero, .data intermediate⟩

def twoTests (alAccepts enclosingDataExitAccepts : Bool) : Bool :=
  alAccepts || enclosingDataExitAccepts

def selectedFeedback (facts : List Nat) : List Nat :=
  Shape.applyGate sourceBodySummary
    (fun values => if twoTests false false then values else []) facts

theorem first_body_produces_exact_field : body [] = [1] := rfl

theorem first_body_has_no_root_hit : sinkHit (body []) = false := by decide

theorem source_body_summary_is_growing :
    Shape.depth sourceBodySummary.source = 0 ∧
    Shape.depth sourceBodySummary.image = 1 ∧
    Shape.needsRestriction sourceBodySummary = true := by decide

theorem second_body_preserves_old_field_until_read :
    sourceFF (body []) = [2, 1] := rfl

theorem second_body_reaches_root : body (body []) = [1, 0] := rfl

theorem second_body_has_root_hit : sinkHit (body (body [])) = true := by decide

theorem two_selected_consumers_reject : twoTests false false = false := rfl

theorem selected_feedback_drops_required_field : selectedFeedback (body []) = [] := rfl

theorem gated_second_body_misses_root :
    sinkHit (body (selectedFeedback (body []))) = false := by decide

theorem in_loop_observation_is_not_preserved :
    sinkHit (body (body [])) ≠ sinkHit (body (selectedFeedback (body []))) := by decide

theorem effects_before_first_gate_do_not_close_gap :
    sinkHit (body []) = false ∧ sinkHit (body (body [])) = true := by decide

/-- The three selected consumers; metadata checks do not execute the body. -/
def threeTests (alAccepts enclosingDataExitAccepts lAccepts : Bool) : Bool :=
  alAccepts || enclosingDataExitAccepts || lAccepts

def selectedThreeFeedback (lAccepts : Bool) (facts : List Nat) : List Nat :=
  Shape.applyGate sourceBodySummary
    (fun values => if threeTests false false lAccepts then values else []) facts

theorem l_consumer_is_sufficient (alAccepts enclosingDataExitAccepts : Bool) :
    threeTests alAccepts enclosingDataExitAccepts true = true := by
  cases alAccepts <;> cases enclosingDataExitAccepts <;> rfl

theorem three_tests_reject_exactly_when_all_reject
    (alAccepts enclosingDataExitAccepts lAccepts : Bool) :
    threeTests alAccepts enclosingDataExitAccepts lAccepts = false ↔
      alAccepts = false ∧ enclosingDataExitAccepts = false ∧ lAccepts = false := by
  cases alAccepts <;> cases enclosingDataExitAccepts <;> cases lAccepts <;> decide

theorem third_family_preserves_previous_acceptance
    (alAccepts enclosingDataExitAccepts lAccepts : Bool)
    (previous : twoTests alAccepts enclosingDataExitAccepts = true) :
    threeTests alAccepts enclosingDataExitAccepts lAccepts = true := by
  cases alAccepts <;> cases enclosingDataExitAccepts <;> cases lAccepts <;> simp_all [twoTests, threeTests]

theorem selected_l_image_keeps_required_field :
    selectedThreeFeedback true (body []) = [1] := rfl

theorem selected_l_image_restores_next_sink :
    sinkHit (body (selectedThreeFeedback true (body []))) = true := by decide

theorem selected_repair_preserves_this_observation :
    sinkHit (body (selectedThreeFeedback true (body []))) = sinkHit (body (body [])) := rfl

end LoopFragments.Feedback
