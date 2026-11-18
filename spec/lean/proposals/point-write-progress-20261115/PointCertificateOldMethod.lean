import PointWriteProperties

import TargetZeroKernel

import ExclusionCertificateOldMethod

namespace PointOldMethod

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay PointWriteReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List PointWriteReplay.Method := [[[PointWriteReplay.Op.move [] [f]],[PointWriteReplay.Op.move [f] [],PointWriteReplay.Op.move [g] []]]]

def source : Offered := ⟨point p [f] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .star) false)]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩]]

theorem cold_1 : PointWriteReplay.rounds 6 1 1 2 methods rows0 saved0 PointOldMethod.source = state1 := by decide

theorem quiescent_1 : PointWriteReplay.round 1 1 2 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

theorem old_complete_state_equality_1 : state1 = ExclusionOldMethod.state1 ∧ rows1 = ExclusionOldMethod.rows1 ∧ saved1 = ExclusionOldMethod.saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩]]

theorem cold_2 : PointWriteReplay.rounds 6 2 1 2 methods rows1 saved1 PointOldMethod.source = state2 := by decide

theorem quiescent_2 : PointWriteReplay.round 2 1 2 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem old_complete_state_equality_2 : state2 = ExclusionOldMethod.state2 ∧ rows2 = ExclusionOldMethod.rows2 ∧ saved2 = ExclusionOldMethod.saved2 := by decide

theorem producer_permission_2 : (state2.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [f] a.ap.path).isSome || match dropHead a.ap.path [f] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f] .must (some t),false⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,f] .must (some t),false⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [f] .must,val (point ret [] .must) false),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .must,val (point ret [f] .must) false),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved3 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [f] .must,val (point ret [f] .must) false),false⟩]]

theorem cold_3 : PointWriteReplay.rounds 6 3 2 2 methods rows2 saved2 PointOldMethod.source = state3 := by decide

theorem quiescent_3 : PointWriteReplay.round 3 2 2 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

theorem old_complete_state_equality_3 : state3 = ExclusionOldMethod.state3 ∧ rows3 = ExclusionOldMethod.rows3 ∧ saved3 = ExclusionOldMethod.saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [f,g] .star) false),(point p [f] .star,val (point ret [f,g] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [f,g] .ne,point ret [f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [f] .must,val (point ret [f] .must) false),false⟩,⟨(point p [f,g] .star,val (point ret [] .star) false),true⟩]]

theorem cold_4 : PointWriteReplay.rounds 6 4 3 2 methods rows3 saved3 PointOldMethod.source = state4 := by decide

theorem quiescent_4 : PointWriteReplay.round 4 3 2 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem old_complete_state_equality_4 : state4 = ExclusionOldMethod.state4 ∧ rows4 = ExclusionOldMethod.rows4 ∧ saved4 = ExclusionOldMethod.saved4 := by decide

theorem producer_permission_4 : (state4.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [f] a.ap.path).isSome || match dropHead a.ap.path [f] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [] .must (some t),false⟩,⟨point p [f] .must (some t),false⟩]],[[]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩]]⟩

def rows5 : List (List Row) := [[]]

def saved5 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [f] .must,val (point ret [f] .must) false),false⟩,⟨(point p [f,g] .star,val (point ret [] .star) false),true⟩]]

theorem cold_5 : PointWriteReplay.rounds 6 5 4 2 methods rows4 saved4 PointOldMethod.source = state5 := by decide

theorem quiescent_5 : PointWriteReplay.round 5 4 2 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

theorem old_complete_state_equality_5 : state5 = ExclusionOldMethod.state5 ∧ rows5 = ExclusionOldMethod.rows5 ∧ saved5 = ExclusionOldMethod.saved5 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows5.all List.isEmpty = true ∧ (((state5.offers[2]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state5.offers[2]!).map terminal) = [0] := by decide

end PointOldMethod

#print axioms PointOldMethod.cold_1

#print axioms PointOldMethod.quiescent_1

#print axioms PointOldMethod.handoff_1

#print axioms PointOldMethod.old_complete_state_equality_1

#print axioms PointOldMethod.cold_2

#print axioms PointOldMethod.quiescent_2

#print axioms PointOldMethod.handoff_2

#print axioms PointOldMethod.old_complete_state_equality_2

#print axioms PointOldMethod.producer_permission_2

#print axioms PointOldMethod.cold_3

#print axioms PointOldMethod.quiescent_3

#print axioms PointOldMethod.handoff_3

#print axioms PointOldMethod.old_complete_state_equality_3

#print axioms PointOldMethod.cold_4

#print axioms PointOldMethod.quiescent_4

#print axioms PointOldMethod.handoff_4

#print axioms PointOldMethod.old_complete_state_equality_4

#print axioms PointOldMethod.producer_permission_4

#print axioms PointOldMethod.cold_5

#print axioms PointOldMethod.quiescent_5

#print axioms PointOldMethod.handoff_5

#print axioms PointOldMethod.old_complete_state_equality_5

#print axioms PointOldMethod.natural_stop_and_expected_observations
