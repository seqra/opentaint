import ExclusionCover

import TargetZeroKernel

namespace ExclusionOrdinaryTwo

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay ExclusionChildReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List Method := [[[Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [f] []]]]

def source : Offered := ⟨point p [] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[]]

theorem cold_1 : ExclusionChildReplay.rounds true 6 1 1 2 methods rows0 saved0 ExclusionOrdinaryTwo.source = state1 := by decide

theorem quiescent_1 : ExclusionChildReplay.round true 1 1 2 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[]]

theorem cold_2 : ExclusionChildReplay.rounds true 6 2 1 2 methods rows1 saved1 ExclusionOrdinaryTwo.source = state2 := by decide

theorem quiescent_2 : ExclusionChildReplay.round true 2 1 2 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem actual_producer_permission_2 : (state2.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [] a.ap.path).isSome || match dropHead a.ap.path [] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .must (some t),false⟩]],[[(point p [f] .must,val (point ret [] .must) false),(point p [] .must,val (point ret [f] .must) false),(point p [f] .must,val (point ret [f] .must) false),(point p [] .must,val (point ret [f,f] .must) false)]],[[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩]]⟩

def rows3 : List (List Row) := [[]]

def saved3 : List (List Saved) := [[⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [] .must,val (point ret [f] .must) false),false⟩,⟨(point p [f] .must,val (point ret [f] .must) false),false⟩,⟨(point p [] .must,val (point ret [f,f] .must) false),false⟩]]

theorem cold_3 : ExclusionChildReplay.rounds true 6 3 2 2 methods rows2 saved2 ExclusionOrdinaryTwo.source = state3 := by decide

theorem quiescent_3 : ExclusionChildReplay.round true 3 2 2 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows3.all List.isEmpty = true ∧ (((state3.offers[2]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state3.offers[2]!).map terminal) = [0] := by decide

end ExclusionOrdinaryTwo

#print axioms ExclusionOrdinaryTwo.cold_1

#print axioms ExclusionOrdinaryTwo.quiescent_1

#print axioms ExclusionOrdinaryTwo.handoff_1

#print axioms ExclusionOrdinaryTwo.cold_2

#print axioms ExclusionOrdinaryTwo.quiescent_2

#print axioms ExclusionOrdinaryTwo.handoff_2

#print axioms ExclusionOrdinaryTwo.actual_producer_permission_2

#print axioms ExclusionOrdinaryTwo.cold_3

#print axioms ExclusionOrdinaryTwo.quiescent_3

#print axioms ExclusionOrdinaryTwo.handoff_3

#print axioms ExclusionOrdinaryTwo.natural_stop_and_expected_observations
