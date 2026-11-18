import PointWriteProperties

import TargetZeroKernel

namespace PointNestedPositive

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay PointWriteReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List PointWriteReplay.Method := [[[PointWriteReplay.Op.nestedWrite [f,g],PointWriteReplay.Op.move [f] [],PointWriteReplay.Op.nestedWrite [f,g]],[PointWriteReplay.Op.nestedWrite [f,g],PointWriteReplay.Op.move [] [f],PointWriteReplay.Op.nestedWrite [f,g]]]]

def source : Offered := ⟨point p [f] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def state1 : State := ⟨[[⟨point p [f] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .star) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .star,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[]]

theorem cold_1 : PointWriteReplay.rounds 6 1 1 1 methods rows0 saved0 PointNestedPositive.source = state1 := by decide

theorem quiescent_1 : PointWriteReplay.round 1 1 1 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_2 : PointWriteReplay.rounds 6 2 1 1 methods rows1 saved1 PointNestedPositive.source = state2 := by decide

theorem quiescent_2 : PointWriteReplay.round 2 1 1 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem producer_permission_2 : (state2.offers[1]!).any (fun a => a.ap.mark == some t && ((dropHead [f] a.ap.path).isSome || match dropHead a.ap.path [f] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [f] .must (some t),false⟩]],[[(point p [f] .must,val ({point ret [f] .must with e := [g]}) false),(point p [f] .must,val ({point ret [f,f] .must with e := [g]}) false)]],[[⟨point p [f] .must (some t),false⟩],[⟨{point p [] .must (some t) with e := [f,g]},false⟩,⟨{point p [f] .must (some t) with e := [g]},false⟩]]⟩

def rows3 : List (List Row) := [[]]

def saved3 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩,⟨(point p [f] .must,val ({point ret [f] .must with e := [g]}) false),false⟩,⟨(point p [f] .must,val ({point ret [f,f] .must with e := [g]}) false),false⟩]]

theorem cold_3 : PointWriteReplay.rounds 6 3 2 1 methods rows2 saved2 PointNestedPositive.source = state3 := by decide

theorem quiescent_3 : PointWriteReplay.round 3 2 1 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows3.all List.isEmpty = true ∧ (((state3.offers[1]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state3.offers[1]!).map terminal) = [0] := by decide

end PointNestedPositive

#print axioms PointNestedPositive.cold_1

#print axioms PointNestedPositive.quiescent_1

#print axioms PointNestedPositive.handoff_1

#print axioms PointNestedPositive.cold_2

#print axioms PointNestedPositive.quiescent_2

#print axioms PointNestedPositive.handoff_2

#print axioms PointNestedPositive.producer_permission_2

#print axioms PointNestedPositive.cold_3

#print axioms PointNestedPositive.quiescent_3

#print axioms PointNestedPositive.handoff_3

#print axioms PointNestedPositive.natural_stop_and_expected_observations
