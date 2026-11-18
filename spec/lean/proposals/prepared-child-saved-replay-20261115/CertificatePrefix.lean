import ChildCover

import TargetZeroKernel

namespace PreparedPrefix

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine

open PreparedChildReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List Method := [[[Op.move [g] [],Op.call 1]],[[Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [f] []]]]

def source : Offered := ⟨point p [g,f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may,true⟩]],[[(point p [] .star,val (point ret [] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : PreparedChildReplay.rounds true 6 1 1 3 methods rows0 saved0 source = state1 := by decide

theorem quiescent_1 : PreparedChildReplay.round true 1 1 3 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : outputRows state1 = rows1 ∧ PreparedChildReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩]],[[(point p [] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [g] .ne) true),(point p [g] .star,val (point ret [g] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩,⟨point p [g] .ne,point ret [] .star⟩,⟨point p [g] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : PreparedChildReplay.rounds true 6 2 1 3 methods rows1 saved1 source = state2 := by decide

theorem quiescent_2 : PreparedChildReplay.round true 2 1 3 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : outputRows state2 = rows2 ∧ PreparedChildReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem actual_uniform_producer_permission_2 : (state2.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [g,f,g] a.ap.path).isSome || match dropHead a.ap.path [g,f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩]],[[(point p [g] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [] .may) true),(point p [g,f] .star,val (point ret [g] .may) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [g] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩,⟨point p [g] .may,point ret [g] .star⟩,⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [g] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : PreparedChildReplay.rounds true 6 3 2 3 methods rows2 saved2 source = state3 := by decide

theorem quiescent_3 : PreparedChildReplay.round true 3 2 3 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : outputRows state3 = rows3 ∧ PreparedChildReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩]],[[(point p [] .star,val (point ret [g] .may) true),(point p [f] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [g,f] .may) true),(point p [] .star,val (point ret [g,f] .ne) true),(point p [f] .star,val (point ret [g,f] .may) true),(point p [g] .star,val (point ret [g,f] .ne) true),(point p [] .star,val (point ret [g,f,f] .star) false),(point p [g] .star,val (point ret [g,f,f] .ne) true)],[(point p [f] .star,val (point ret [f] .may) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [g] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩,⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .may,point ret [] .star⟩,⟨point p [g,f] .ne,point ret [] .star⟩,⟨point p [g,f] .may,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩,⟨point p [g,f,f] .ne,point ret [g] .star⟩],[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [g] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : PreparedChildReplay.rounds true 6 4 3 3 methods rows3 saved3 source = state4 := by decide

theorem quiescent_4 : PreparedChildReplay.round true 4 3 3 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : outputRows state4 = rows4 ∧ PreparedChildReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem actual_uniform_producer_permission_4 : (state4.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [g,f,g] a.ap.path).isSome || match dropHead a.ap.path [g,f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g,f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .star,false⟩]],[[(point p [g] .star,val (point ret [f] .ne) true),(point p [g,f] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f,f] .star) false),(point p [g,f] .star,val (point ret [f] .may) true),(point p [g,f] .star,val (point ret [f] .ne) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [f,f] .ne) true),(point p [g,f,f] .star,val (point ret [f] .ne) true),(point p [g,f,g] .star,val (point ret [f] .ne) true),(point p [g,f,f] .star,val (point ret [f,f] .ne) true),(point p [g,f,g] .star,val (point ret [f,f] .ne) true)],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [f] .ne,point ret [g] .star⟩,⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [f] .may,point ret [g,f] .star⟩,⟨point p [f] .ne,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [f,f] .ne,point ret [g,f] .star⟩,⟨point p [f] .ne,point ret [g,f,f] .star⟩,⟨point p [f] .ne,point ret [g,f,g] .star⟩,⟨point p [f,f] .ne,point ret [g,f,f] .star⟩,⟨point p [f,f] .ne,point ret [g,f,g] .star⟩],[]]

def saved5 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : PreparedChildReplay.rounds true 6 5 4 3 methods rows4 saved4 source = state5 := by decide

theorem quiescent_5 : PreparedChildReplay.round true 5 4 3 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : outputRows state5 = rows5 ∧ PreparedChildReplay.outputSaved 5 saved4 state5 = saved5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [g,f] .star,false⟩]],[[(point p [f] .star,val (point ret [g] .may) true),(point p [f] .star,val (point ret [g,f] .may) true),(point p [f] .star,val (point ret [g,f,f] .may) true),(point p [f] .star,val (point ret [g,f,g] .may) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [g,f,f,g,f] .ne (some t),true⟩]]⟩

def rows6 : List (List Row) := [[⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .may,point ret [f] .star⟩,⟨point p [g,f,f] .may,point ret [f] .star⟩,⟨point p [g,f,g] .may,point ret [f] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : PreparedChildReplay.rounds true 6 6 5 3 methods rows5 saved5 source = state6 := by decide

theorem quiescent_6 : PreparedChildReplay.round true 6 5 3 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : outputRows state6 = rows6 ∧ PreparedChildReplay.outputSaved 6 saved5 state6 = saved6 := by decide

theorem actual_uniform_producer_permission_6 : (state6.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [g,f,g] a.ap.path).isSome || match dropHead a.ap.path [g,f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = false := by decide

def state7 : State := ⟨[[⟨point p [f] .may (some t),true⟩,⟨point p [g,f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩]],[[(point p [g,f] .star,val (point ret [f] .may) true)],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[],[]]⟩

def rows7 : List (List Row) := [[⟨point p [f] .may,point ret [g,f] .star⟩],[]]

def saved7 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : PreparedChildReplay.rounds true 6 7 6 3 methods rows6 saved6 source = state7 := by decide

theorem quiescent_7 : PreparedChildReplay.round true 7 6 3 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : outputRows state7 = rows7 ∧ PreparedChildReplay.outputSaved 7 saved6 state7 = saved7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g,f,f,g] .may (some t),true⟩],[⟨point p [g,f,f,g,f,f,g] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[],[]]

def saved8 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_8 : PreparedChildReplay.rounds true 6 8 7 3 methods rows7 saved7 source = state8 := by decide

theorem quiescent_8 : PreparedChildReplay.round true 8 7 3 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : outputRows state8 = rows8 ∧ PreparedChildReplay.outputSaved 8 saved7 state8 = saved8 := by decide

theorem actual_uniform_producer_permission_8 : (state8.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [g,f,g] a.ap.path).isSome || match dropHead a.ap.path [g,f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = false := by decide

def state9 : State := ⟨[[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[],[]]⟩

def rows9 : List (List Row) := [[],[]]

def saved9 : List (List Saved) := [[⟨(point p [g] .star,val (point ret [f,f] .star) false),false⟩,⟨(point p [g,f,f] .star,val (point ret [] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_9 : PreparedChildReplay.rounds true 6 9 8 3 methods rows8 saved8 source = state9 := by decide

theorem quiescent_9 : PreparedChildReplay.round true 9 8 3 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : outputRows state9 = rows9 ∧ PreparedChildReplay.outputSaved 9 saved8 state9 = saved9 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem complete_frontier_and_expected_observations : rows9.all List.isEmpty = true ∧ (((state9.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state9.offers[3]!).map terminal) = [] := by decide

end PreparedPrefix

#print axioms PreparedPrefix.cold_1

#print axioms PreparedPrefix.quiescent_1

#print axioms PreparedPrefix.handoff_1

#print axioms PreparedPrefix.cold_2

#print axioms PreparedPrefix.quiescent_2

#print axioms PreparedPrefix.handoff_2

#print axioms PreparedPrefix.actual_uniform_producer_permission_2

#print axioms PreparedPrefix.cold_3

#print axioms PreparedPrefix.quiescent_3

#print axioms PreparedPrefix.handoff_3

#print axioms PreparedPrefix.cold_4

#print axioms PreparedPrefix.quiescent_4

#print axioms PreparedPrefix.handoff_4

#print axioms PreparedPrefix.actual_uniform_producer_permission_4

#print axioms PreparedPrefix.cold_5

#print axioms PreparedPrefix.quiescent_5

#print axioms PreparedPrefix.handoff_5

#print axioms PreparedPrefix.cold_6

#print axioms PreparedPrefix.quiescent_6

#print axioms PreparedPrefix.handoff_6

#print axioms PreparedPrefix.actual_uniform_producer_permission_6

#print axioms PreparedPrefix.cold_7

#print axioms PreparedPrefix.quiescent_7

#print axioms PreparedPrefix.handoff_7

#print axioms PreparedPrefix.cold_8

#print axioms PreparedPrefix.quiescent_8

#print axioms PreparedPrefix.handoff_8

#print axioms PreparedPrefix.actual_uniform_producer_permission_8

#print axioms PreparedPrefix.cold_9

#print axioms PreparedPrefix.quiescent_9

#print axioms PreparedPrefix.handoff_9

#print axioms PreparedPrefix.complete_frontier_and_expected_observations
