import Run2Relay

namespace NativeAdmissionCells

open NonEmptyPolicy

-- Scalar same-head native C2 in the valid nonstatic empty-mask fragment.
-- This is the emitAdmissions family, including the concrete STAR companion.
-- The current Kotlin precise-STAR branch returns an EXACT start on every
-- legal same-head actual, including STAR (RestrictedInitialPolicy.emit).
def nativeTail (d actual : Tail) : Option Tail :=
  match d with
  | .exact | .star => some .exact
  | .may => match actual with
    | .star | .may => some .star
    | .exact => some .exact
    | .must => some .must
    | .ne => none
  | _ => none

def nativeFamily (d : Ap) (a : Offered) : List Seed :=
  if d.base != a.ap.base || d.path != a.ap.path || !marksOK d a.ap then []
  else match nativeTail d.tail a.ap.tail with
    | none => []
    | some kind =>
      let q := seed d a d.path kind
      if kind == .star && d.mark.isSome then
        [q,⟨{q.ap with mark := none},false⟩]
      else [q]

def flowStar : Ap := ⟨0,[],.star,none,[],[]⟩
def flowPoint : Ap := {flowStar with tail := .exact}
def flowOffer : Offered := ⟨flowStar,false⟩
def markedStar : Ap := {flowStar with mark := some 7}
def markedPoint : Ap := {markedStar with tail := .exact}
def markedOffer : Offered := ⟨markedStar,true⟩

theorem run2_relay_replaces_the_native_exact_flow_probe :
    nativeFamily flowStar flowOffer = [⟨flowPoint,false⟩] ∧
    Run2Relay.emit 2 1 true flowStar flowOffer = [⟨flowStar,false⟩] := by decide

theorem later_precise_star_has_a_native_probe_but_no_selected_start :
    nativeFamily flowStar flowOffer = [⟨flowPoint,false⟩] ∧
    Run2Relay.emit 3 2 false flowStar flowOffer = [] := by decide

theorem a_marked_star_offered_to_an_exact_demand_is_a_native_DEMAND_start :
    nativeFamily markedPoint markedOffer = [⟨markedPoint,true⟩] ∧
    Run2Relay.emit 2 1 true markedPoint markedOffer = [] := by decide

theorem the_same_head_MAY_split_keeps_the_native_STAR_and_companion :
    let d : Ap := {markedStar with tail := .may}
    let a : Offered := ⟨d,true⟩
    let after := Run2Relay.emit 3 2 false d a
    (nativeFamily d a).all after.contains = true ∧ after.contains ⟨markedPoint,true⟩ = true := by decide

theorem when_a_native_point_is_submitted_the_precise_star_still_starts_it :
    let a : Offered := ⟨flowPoint,false⟩
    nativeFamily flowStar a = Run2Relay.emit 3 2 false flowStar a := by decide

end NativeAdmissionCells
