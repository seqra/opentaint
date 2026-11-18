import PartitionMachine

import TargetZeroKernel

namespace PartitionPrefix

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine

open ProgressiveMachine

set_option maxRecDepth 16384

set_option maxHeartbeats 60000000

def methods : List ProgressiveMachine.Method := [[[Op.move [g] [],Op.call 1]],[[Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [f] []]]]

def source : Offered := ⟨point p [g,f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def tree1 : ProgressiveMachine.Trees := [[],[]]

def state1 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may,true⟩]],[[(point p [] .star,val (point ret [] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[some [g],some [f]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : ProgressiveMachine.rounds 6 1 1 3 methods tree1 rows0 saved0 source = state1 := by decide

theorem quiescent_1 : ProgressiveMachine.round 1 1 3 methods tree1 rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : outputRows state1.cold = rows1 ∧ ProgressiveMachine.outputSaved 1 saved0 state1 = saved1 ∧ ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) = [[[g]],[[f]]] := by decide

def tree2 : ProgressiveMachine.Trees := [[],[]]

def state2 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩]],[[(point p [] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[none,some [f]]⟩

def rows2 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩,⟨point p [g] .may,point ret [g] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : ProgressiveMachine.rounds 6 2 1 3 methods tree2 rows1 saved1 source = state2 := by decide

theorem quiescent_2 : ProgressiveMachine.round 2 1 3 methods tree2 rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : outputRows state2.cold = rows2 ∧ ProgressiveMachine.outputSaved 2 saved1 state2 = saved2 ∧ ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) = [[],[[f]]] := by decide

theorem producer_permission_2 : (state2.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree3 : ProgressiveMachine.Trees := [[[g]],[[f]]]

def state3 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩]],[[(point p [g] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [] .may) true),(point p [g,f] .star,val (point ret [g] .may) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[none,some [f,f]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [g] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩,⟨point p [g] .may,point ret [g] .star⟩,⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [g] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : ProgressiveMachine.rounds 6 3 2 3 methods tree3 rows2 saved2 source = state3 := by decide

theorem quiescent_3 : ProgressiveMachine.round 3 2 3 methods tree3 rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : outputRows state3.cold = rows3 ∧ ProgressiveMachine.outputSaved 3 saved2 state3 = saved3 ∧ ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) = [[[g]],[[f],[f,f]]] := by decide

theorem persistent_tree_3 : tree3 = ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) := by decide

def tree4 : ProgressiveMachine.Trees := [[],[[f]]]

def state4 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩]],[[(point p [] .star,val (point ret [g] .may) true),(point p [f] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [g,f] .may) true),(point p [] .star,val (point ret [g,f] .ne) true),(point p [g] .star,val (point ret [g,f] .ne) true),(point p [] .star,val (point ret [g,f,f] .star) false),(point p [g] .star,val (point ret [g,f,f] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [g] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[some [f],some [f,f]]⟩

def rows4 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩,⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .may,point ret [] .star⟩,⟨point p [g,f] .ne,point ret [] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩,⟨point p [g,f,f] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [g] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : ProgressiveMachine.rounds 6 4 3 3 methods tree4 rows3 saved3 source = state4 := by decide

theorem quiescent_4 : ProgressiveMachine.round 4 3 3 methods tree4 rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : outputRows state4.cold = rows4 ∧ ProgressiveMachine.outputSaved 4 saved3 state4 = saved4 ∧ ((ProgressiveMachine.install tree4 state4).map (unique pathKey)) = [[[f]],[[f],[f,f]]] := by decide

theorem persistent_tree_4 : tree4 = ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) := by decide

theorem producer_permission_4 : (state4.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree5 : ProgressiveMachine.Trees := [[[g]],[[f],[f,f]]]

def state5 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g,f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .star,false⟩]],[[(point p [g] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f] .may) true),(point p [g] .star,val (point ret [f] .ne) true),(point p [g,f] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f,f] .star) false),(point p [g,f] .star,val (point ret [f] .may) true),(point p [g,f] .star,val (point ret [f] .ne) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [f,f] .ne) true),(point p [g,f,g] .star,val (point ret [f] .ne) true)],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩,[some [g,f],none]⟩

def rows5 : List (List Row) := [[⟨point p [] .may,point ret [g] .star⟩,⟨point p [f] .may,point ret [g] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩,⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [f] .may,point ret [g,f] .star⟩,⟨point p [f] .ne,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [f,f] .ne,point ret [g,f] .star⟩,⟨point p [f] .ne,point ret [g,f,g] .star⟩],[]]

def saved5 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : ProgressiveMachine.rounds 6 5 4 3 methods tree5 rows4 saved4 source = state5 := by decide

theorem quiescent_5 : ProgressiveMachine.round 5 4 3 methods tree5 rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : outputRows state5.cold = rows5 ∧ ProgressiveMachine.outputSaved 5 saved4 state5 = saved5 ∧ ((ProgressiveMachine.install tree5 state5).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_5 : tree5 = ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) := by decide

def tree6 : ProgressiveMachine.Trees := [[[f]],[[f],[f,f]]]

def state6 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [g,f] .star,false⟩]],[[(point p [f] .star,val (point ret [g] .may) true),(point p [f] .star,val (point ret [g,f] .may) true),(point p [f] .star,val (point ret [g,f,g] .may) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [g,f,f,g,f] .ne (some t),true⟩]]⟩,[some [f,f],none]⟩

def rows6 : List (List Row) := [[⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .may,point ret [f] .star⟩,⟨point p [g,f,g] .may,point ret [f] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : ProgressiveMachine.rounds 6 6 5 3 methods tree6 rows5 saved5 source = state6 := by decide

theorem quiescent_6 : ProgressiveMachine.round 6 5 3 methods tree6 rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : outputRows state6.cold = rows6 ∧ ProgressiveMachine.outputSaved 6 saved5 state6 = saved6 ∧ ((ProgressiveMachine.install tree6 state6).map (unique pathKey)) = [[[f],[f,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_6 : tree6 = ((ProgressiveMachine.install tree4 state4).map (unique pathKey)) := by decide

theorem producer_permission_6 : (state6.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree7 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state7 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩]],[[],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[],[]]⟩,[none,none]⟩

def rows7 : List (List Row) := [[],[]]

def saved7 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : ProgressiveMachine.rounds 6 7 6 3 methods tree7 rows6 saved6 source = state7 := by decide

theorem quiescent_7 : ProgressiveMachine.round 7 6 3 methods tree7 rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : outputRows state7.cold = rows7 ∧ ProgressiveMachine.outputSaved 7 saved6 state7 = saved7 ∧ ((ProgressiveMachine.install tree7 state7).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_7 : tree7 = ((ProgressiveMachine.install tree5 state5).map (unique pathKey)) := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem complete_frontier_and_expected_observations : rows7.all List.isEmpty = true ∧ (((state7.cold.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state7.cold.offers[3]!).map terminal) = [] := by decide

end PartitionPrefix

#print axioms PartitionPrefix.cold_1

#print axioms PartitionPrefix.quiescent_1

#print axioms PartitionPrefix.handoff_1

#print axioms PartitionPrefix.cold_2

#print axioms PartitionPrefix.quiescent_2

#print axioms PartitionPrefix.handoff_2

#print axioms PartitionPrefix.producer_permission_2

#print axioms PartitionPrefix.cold_3

#print axioms PartitionPrefix.quiescent_3

#print axioms PartitionPrefix.handoff_3

#print axioms PartitionPrefix.persistent_tree_3

#print axioms PartitionPrefix.cold_4

#print axioms PartitionPrefix.quiescent_4

#print axioms PartitionPrefix.handoff_4

#print axioms PartitionPrefix.persistent_tree_4

#print axioms PartitionPrefix.producer_permission_4

#print axioms PartitionPrefix.cold_5

#print axioms PartitionPrefix.quiescent_5

#print axioms PartitionPrefix.handoff_5

#print axioms PartitionPrefix.persistent_tree_5

#print axioms PartitionPrefix.cold_6

#print axioms PartitionPrefix.quiescent_6

#print axioms PartitionPrefix.handoff_6

#print axioms PartitionPrefix.persistent_tree_6

#print axioms PartitionPrefix.producer_permission_6

#print axioms PartitionPrefix.cold_7

#print axioms PartitionPrefix.quiescent_7

#print axioms PartitionPrefix.handoff_7

#print axioms PartitionPrefix.persistent_tree_7

#print axioms PartitionPrefix.complete_frontier_and_expected_observations
