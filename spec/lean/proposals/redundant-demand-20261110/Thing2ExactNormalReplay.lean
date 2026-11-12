import Std

/- A component law, not a retirement proof. This table models the concrete
   mark selected at one root coordinate. `excluded` is arbitrary field E.
   The source bridge is Summary.kt's same-path EXACT reader, the non-MUST
   branch of nativeRecordLanes, and EXACT -> EXACT edge application. -/
namespace Thing2ExactNormalReplay

inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, Repr
inductive Role where | direct | opposite
  deriving DecidableEq, Repr

structure Actual where
  tail : Tail
  layer : Layer
  excluded : List Nat
  hasT : Bool
  flag : Bool
  deriving DecidableEq, Repr

structure Leaves where
  exact : Bool
  any : Bool
  deriving DecidableEq, Repr

def rootLeaves (a : Actual) : Leaves :=
  if a.tail == .exact then ⟨a.hasT, false⟩ else ⟨false, a.hasT⟩

/- In insidePart at the identical empty path, j.tail=EXACT sets all three
   selectors to true. E is tested only on a strict path descent, which is
   absent here. Role changes strict-ancestor STAR reads, not this cell. -/
def selectRootExact (a : Actual) (_role : Role) : Leaves :=
  let p := rootLeaves a
  let takeStar := true
  let takeAny := true
  let takeExact := true
  if a.tail == .star then
    ⟨takeExact && p.exact, takeStar && p.any⟩
  else
    ⟨takeExact && p.exact, takeAny && p.any⟩

structure Result where
  tail : Tail
  layer : Layer
  excluded : List Nat
  flag : Bool
  deriving DecidableEq, Repr

/- The native read premise is EXACT, so nativeRecordLanes returns one lane
   without pending demotion. Folding the selected root mark through the
   EXACT -> EXACT transfer yields an exact output at its incoming layer.
   The retained membership itself has the protected flag. -/
def applyRootExact (a : Actual) (role : Role) : Option Result :=
  let selected := selectRootExact a role
  if selected.exact || selected.any then
    some ⟨.exact, a.layer, [], true⟩
  else none

def legal (a : Actual) : Prop :=
  match a.tail with
  | .exact => a.excluded = []
  | .star => a.layer = .demand
  | .may => a.layer = .demand ∧ a.excluded = []
  | .must => True

def layerCovers : Layer → Layer → Prop
  | .normal, _ => True
  | .demand, .demand => True
  | .demand, .normal => False

def coversExactDemand (r : Result) : Prop :=
  r.tail = .exact ∧ r.excluded = [] ∧ r.flag = true ∧ layerCovers r.layer .demand

theorem selected_mark_present (a : Actual) (role : Role) :
    ((selectRootExact a role).exact || (selectRootExact a role).any) = a.hasT := by
  cases a with | mk tail layer excluded hasT flag =>
    cases tail <;> cases role <;> cases hasT <;> rfl

theorem exact_replay_present (a : Actual) (role : Role) (h : a.hasT = true) :
    applyRootExact a role = some ⟨.exact, a.layer, [], true⟩ := by
  simp [applyRootExact, selected_mark_present, h]

theorem no_selected_mark_no_replay (a : Actual) (role : Role) (h : a.hasT = false) :
    applyRootExact a role = none := by
  simp [applyRootExact, selected_mark_present, h]

theorem exact_reader_roles_equal (a : Actual) :
    applyRootExact a .direct = applyRootExact a .opposite := by
  simp only [applyRootExact, selected_mark_present]

theorem field_exclusions_do_not_change_root_result (a : Actual) (e : List Nat) (role : Role) :
    applyRootExact { a with excluded := e } role = applyRootExact a role := by
  simp only [applyRootExact, selected_mark_present]

theorem incoming_protection_does_not_remove_output_flag (a : Actual) (flag : Bool) (role : Role) :
    applyRootExact { a with flag := flag } role = applyRootExact a role := by
  simp only [applyRootExact, selected_mark_present]

theorem replay_covers_exact_demand (a : Actual) (role : Role) (h : a.hasT = true) :
    ∃ r, applyRootExact a role = some r ∧ coversExactDemand r := by
  refine ⟨⟨.exact, a.layer, [], true⟩, exact_replay_present a role h, ?_⟩
  cases a.layer <;> simp [coversExactDemand, layerCovers]

theorem normal_support_keeps_normal (a : Actual) (role : Role)
    (h : a.hasT = true) (l : a.layer = .normal) :
    applyRootExact a role = some ⟨.exact, .normal, [], true⟩ := by
  simpa only [l] using exact_replay_present a role h

theorem demand_support_keeps_demand (a : Actual) (role : Role)
    (h : a.hasT = true) (l : a.layer = .demand) :
    applyRootExact a role = some ⟨.exact, .demand, [], true⟩ := by
  simpa only [l] using exact_replay_present a role h

theorem legal_root_star_is_demand (a : Actual) (h : legal a) (s : a.tail = .star) :
    a.layer = .demand := by simpa [legal, s] using h

theorem legal_root_may_is_demand (a : Actual) (h : legal a) (s : a.tail = .may) :
    a.layer = .demand := by
  have hh : a.layer = .demand ∧ a.excluded = [] := by simpa [legal, s] using h
  exact hh.1

theorem layer_of_protected_replay_not_widened (a : Actual) (role : Role)
    (r : Result) (h : applyRootExact a role = some r) : r.layer = a.layer := by
  simp only [applyRootExact, selected_mark_present] at h
  cases e : a.hasT <;> simp [e] at h
  cases h
  rfl

/- The literal MUST reader has a different STAR input guard. Keep this
   counter-cell explicit: an exact-root reader avoids relying on it. -/
def literalMustAcceptsStar (excluded : List Nat) : Bool := excluded.isEmpty

theorem nonempty_star_exclusion_rejects_literal_must (f : Nat) (es : List Nat) :
    literalMustAcceptsStar (f :: es) = false := by rfl

theorem same_star_offer_has_exact_reader (f : Nat) (es : List Nat) (role : Role) :
    applyRootExact ⟨.star, .demand, f :: es, true, false⟩ role =
      some ⟨.exact, .demand, [], true⟩ := by
  exact exact_replay_present _ _ rfl

end Thing2ExactNormalReplay

#print axioms Thing2ExactNormalReplay.selected_mark_present
#print axioms Thing2ExactNormalReplay.exact_replay_present
#print axioms Thing2ExactNormalReplay.no_selected_mark_no_replay
#print axioms Thing2ExactNormalReplay.exact_reader_roles_equal
#print axioms Thing2ExactNormalReplay.field_exclusions_do_not_change_root_result
#print axioms Thing2ExactNormalReplay.incoming_protection_does_not_remove_output_flag
#print axioms Thing2ExactNormalReplay.replay_covers_exact_demand
#print axioms Thing2ExactNormalReplay.normal_support_keeps_normal
#print axioms Thing2ExactNormalReplay.demand_support_keeps_demand
#print axioms Thing2ExactNormalReplay.legal_root_star_is_demand
#print axioms Thing2ExactNormalReplay.legal_root_may_is_demand
#print axioms Thing2ExactNormalReplay.layer_of_protected_replay_not_widened
#print axioms Thing2ExactNormalReplay.nonempty_star_exclusion_rejects_literal_must
#print axioms Thing2ExactNormalReplay.same_star_offer_has_exact_reader
