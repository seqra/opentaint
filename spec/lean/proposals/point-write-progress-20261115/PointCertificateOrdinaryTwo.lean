import PointWriteProperties

import TargetZeroKernel

import ExclusionCertificateOrdinaryTwo

namespace PointOrdinaryTwo

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay PointWriteReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List PointWriteReplay.Method := [[[PointWriteReplay.Op.move [] [f],PointWriteReplay.Op.move [] [f]],[PointWriteReplay.Op.move [f] [],PointWriteReplay.Op.move [f] []]]]

def source : Offered := ⟨point p [] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[]]

theorem cold_1 : PointWriteReplay.rounds 6 1 1 2 methods rows0 saved0 PointOrdinaryTwo.source = state1 := by decide

theorem quiescent_1 : PointWriteReplay.round 1 1 2 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

theorem old_complete_state_equality_1 : state1 = ExclusionOrdinaryTwo.state1 ∧ rows1 = ExclusionOrdinaryTwo.rows1 ∧ saved1 = ExclusionOrdinaryTwo.saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[]]

theorem cold_2 : PointWriteReplay.rounds 6 2 1 2 methods rows1 saved1 PointOrdinaryTwo.source = state2 := by decide

theorem quiescent_2 : PointWriteReplay.round 2 1 2 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem old_complete_state_equality_2 : state2 = ExclusionOrdinaryTwo.state2 ∧ rows2 = ExclusionOrdinaryTwo.rows2 ∧ saved2 = ExclusionOrdinaryTwo.saved2 := by decide

theorem producer_permission_2 : (state2.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [] a.ap.path).isSome || match dropHead a.ap.path [] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .must (some t),false⟩]],[[(point p [f] .must,val (point ret [] .must) false),(point p [] .must,val (point ret [f] .must) false),(point p [f] .must,val (point ret [f] .must) false),(point p [] .must,val (point ret [f,f] .must) false)]],[[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩]]⟩

def rows3 : List (List Row) := [[]]

def saved3 : List (List Saved) := [[⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [] .must,val (point ret [f] .must) false),false⟩,⟨(point p [f] .must,val (point ret [f] .must) false),false⟩,⟨(point p [] .must,val (point ret [f,f] .must) false),false⟩]]

theorem cold_3 : PointWriteReplay.rounds 6 3 2 2 methods rows2 saved2 PointOrdinaryTwo.source = state3 := by decide

theorem quiescent_3 : PointWriteReplay.round 3 2 2 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

theorem old_complete_state_equality_3 : state3 = ExclusionOrdinaryTwo.state3 ∧ rows3 = ExclusionOrdinaryTwo.rows3 ∧ saved3 = ExclusionOrdinaryTwo.saved3 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows3.all List.isEmpty = true ∧ (((state3.offers[2]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state3.offers[2]!).map terminal) = [0] := by decide

end PointOrdinaryTwo

#print axioms PointOrdinaryTwo.cold_1

#print axioms PointOrdinaryTwo.quiescent_1

#print axioms PointOrdinaryTwo.handoff_1

#print axioms PointOrdinaryTwo.old_complete_state_equality_1

#print axioms PointOrdinaryTwo.cold_2

#print axioms PointOrdinaryTwo.quiescent_2

#print axioms PointOrdinaryTwo.handoff_2

#print axioms PointOrdinaryTwo.old_complete_state_equality_2

#print axioms PointOrdinaryTwo.producer_permission_2

#print axioms PointOrdinaryTwo.cold_3

#print axioms PointOrdinaryTwo.quiescent_3

#print axioms PointOrdinaryTwo.handoff_3

#print axioms PointOrdinaryTwo.old_complete_state_equality_3

#print axioms PointOrdinaryTwo.natural_stop_and_expected_observations
