import PartitionMachine

import TargetZeroKernel

namespace PartitionOldMethod

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine

open ProgressiveMachine

set_option maxRecDepth 16384

set_option maxHeartbeats 60000000

def methods : List ProgressiveMachine.Method := [[[Op.move [] [f]],[Op.move [f] [],Op.move [g] []]]]

def source : Offered := ⟨point p [f] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def tree1 : ProgressiveMachine.Trees := [[]]

def state1 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .star) false)]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[some [f]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩]]

theorem cold_1 : ProgressiveMachine.rounds 6 1 1 2 methods tree1 rows0 saved0 source = state1 := by decide

theorem quiescent_1 : ProgressiveMachine.round 1 1 2 methods tree1 rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : outputRows state1.cold = rows1 ∧ ProgressiveMachine.outputSaved 1 saved0 state1 = saved1 ∧ ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) = [[[f]]] := by decide

def tree2 : ProgressiveMachine.Trees := [[]]

def state2 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[some [f]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved2 : List (List Saved) := [[⟨(point p [] .star,val (point ret [f] .star) false),false⟩]]

theorem cold_2 : ProgressiveMachine.rounds 6 2 1 2 methods tree2 rows1 saved1 source = state2 := by decide

theorem quiescent_2 : ProgressiveMachine.round 2 1 2 methods tree2 rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : outputRows state2.cold = rows2 ∧ ProgressiveMachine.outputSaved 2 saved1 state2 = saved2 ∧ ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) = [[[f]]] := by decide

theorem producer_permission_2 : (state2.cold.offers[2]!).any (fun a => admits a.ap.tail a.ap.e [f] && a.ap.mark == some t) = true := by decide

def tree3 : ProgressiveMachine.Trees := [[[f]]]

def state3 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩]],[[(point p [] .must,val (point ret [] .must) false),(point p [f] .star,val (point ret [] .may) true),(point p [f] .must,val (point ret [] .must) false),(point p [f,f] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [] .must (some t),false⟩]]⟩,[some [f,g]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩]]

def saved3 : List (List Saved) := [[⟨(point p [] .must,val (point ret [] .must) false),false⟩,⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩]]

theorem cold_3 : ProgressiveMachine.rounds 6 3 2 2 methods tree3 rows2 saved2 source = state3 := by decide

theorem quiescent_3 : ProgressiveMachine.round 3 2 2 methods tree3 rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : outputRows state3.cold = rows3 ∧ ProgressiveMachine.outputSaved 3 saved2 state3 = saved3 ∧ ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) = [[[f],[f,g]]] := by decide

theorem persistent_tree_3 : tree3 = ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) := by decide

def tree4 : ProgressiveMachine.Trees := [[[f]]]

def state4 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [f,g] .star) false),(point p [f] .star,val (point ret [f,g] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[none]⟩

def rows4 : List (List Row) := [[⟨point p [f,g] .ne,point ret [f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [] .must,val (point ret [] .must) false),false⟩,⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [f,g] .star,val (point ret [] .star) false),true⟩]]

theorem cold_4 : ProgressiveMachine.rounds 6 4 3 2 methods tree4 rows3 saved3 source = state4 := by decide

theorem quiescent_4 : ProgressiveMachine.round 4 3 2 methods tree4 rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : outputRows state4.cold = rows4 ∧ ProgressiveMachine.outputSaved 4 saved3 state4 = saved4 ∧ ((ProgressiveMachine.install tree4 state4).map (unique pathKey)) = [[[f]]] := by decide

theorem persistent_tree_4 : tree4 = ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) := by decide

theorem producer_permission_4 : (state4.cold.offers[2]!).any (fun a => admits a.ap.tail a.ap.e [f] && a.ap.mark == some t) = true := by decide

def tree5 : ProgressiveMachine.Trees := [[[f],[f,g]]]

def state5 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .must (some t),false⟩,⟨point p [f] .must (some t),false⟩]],[[]],[[⟨point p [f] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩],[⟨point p [] .must (some t),false⟩]]⟩,[none]⟩

def rows5 : List (List Row) := [[]]

def saved5 : List (List Saved) := [[⟨(point p [] .must,val (point ret [] .must) false),false⟩,⟨(point p [] .star,val (point ret [f] .star) false),false⟩,⟨(point p [f] .must,val (point ret [] .must) false),false⟩,⟨(point p [f,g] .star,val (point ret [] .star) false),true⟩]]

theorem cold_5 : ProgressiveMachine.rounds 6 5 4 2 methods tree5 rows4 saved4 source = state5 := by decide

theorem quiescent_5 : ProgressiveMachine.round 5 4 2 methods tree5 rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : outputRows state5.cold = rows5 ∧ ProgressiveMachine.outputSaved 5 saved4 state5 = saved5 ∧ ((ProgressiveMachine.install tree5 state5).map (unique pathKey)) = [[[f],[f,g]]] := by decide

theorem persistent_tree_5 : tree5 = ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem complete_frontier_and_expected_observations : rows5.all List.isEmpty = true ∧ (((state5.cold.offers[2]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state5.cold.offers[2]!).map terminal) = [0] := by decide

end PartitionOldMethod

#print axioms PartitionOldMethod.cold_1

#print axioms PartitionOldMethod.quiescent_1

#print axioms PartitionOldMethod.handoff_1

#print axioms PartitionOldMethod.cold_2

#print axioms PartitionOldMethod.quiescent_2

#print axioms PartitionOldMethod.handoff_2

#print axioms PartitionOldMethod.producer_permission_2

#print axioms PartitionOldMethod.cold_3

#print axioms PartitionOldMethod.quiescent_3

#print axioms PartitionOldMethod.handoff_3

#print axioms PartitionOldMethod.persistent_tree_3

#print axioms PartitionOldMethod.cold_4

#print axioms PartitionOldMethod.quiescent_4

#print axioms PartitionOldMethod.handoff_4

#print axioms PartitionOldMethod.persistent_tree_4

#print axioms PartitionOldMethod.producer_permission_4

#print axioms PartitionOldMethod.cold_5

#print axioms PartitionOldMethod.quiescent_5

#print axioms PartitionOldMethod.handoff_5

#print axioms PartitionOldMethod.persistent_tree_5

#print axioms PartitionOldMethod.complete_frontier_and_expected_observations
