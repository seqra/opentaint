import PartitionMachine

import TargetZeroKernel

namespace PartitionPrefixPostfix

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine

open ProgressiveMachine

set_option maxRecDepth 16384

set_option maxHeartbeats 60000000

def methods : List ProgressiveMachine.Method := [[[Op.move [g] [],Op.call 1,Op.move [] [g]]],[[Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [f] []]]]

def source : Offered := ⟨point p [g,f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def tree1 : ProgressiveMachine.Trees := [[],[]]

def state1 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may,true⟩]],[[(point p [] .star,val (point ret [g] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .ne (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[some [g],some [f]]⟩

def rows1 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : ProgressiveMachine.rounds 6 1 1 3 methods tree1 rows0 saved0 source = state1 := by decide

theorem quiescent_1 : ProgressiveMachine.round 1 1 3 methods tree1 rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : outputRows state1.cold = rows1 ∧ ProgressiveMachine.outputSaved 1 saved0 state1 = saved1 ∧ ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) = [[[g]],[[f]]] := by decide

def tree2 : ProgressiveMachine.Trees := [[],[]]

def state2 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩]],[[(point p [g] .star,val (point ret [g] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[none,some [f]]⟩

def rows2 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : ProgressiveMachine.rounds 6 2 1 3 methods tree2 rows1 saved1 source = state2 := by decide

theorem quiescent_2 : ProgressiveMachine.round 2 1 3 methods tree2 rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : outputRows state2.cold = rows2 ∧ ProgressiveMachine.outputSaved 2 saved1 state2 = saved2 ∧ ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) = [[],[[f]]] := by decide

theorem producer_permission_2 : (state2.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree3 : ProgressiveMachine.Trees := [[[g]],[[f]]]

def state3 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g] .may (some t),true⟩,⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩]],[[(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g,f] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [g,f] .ne (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[none,some [f,f]]⟩

def rows3 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : ProgressiveMachine.rounds 6 3 2 3 methods tree3 rows2 saved2 source = state3 := by decide

theorem quiescent_3 : ProgressiveMachine.round 3 2 3 methods tree3 rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : outputRows state3.cold = rows3 ∧ ProgressiveMachine.outputSaved 3 saved2 state3 = saved3 ∧ ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) = [[[g]],[[f],[f,f]]] := by decide

theorem persistent_tree_3 : tree3 = ((ProgressiveMachine.install tree1 state1).map (unique pathKey)) := by decide

def tree4 : ProgressiveMachine.Trees := [[],[[f]]]

def state4 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩]],[[(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g,f] .may) true),(point p [g] .star,val (point ret [g,f] .ne) true),(point p [g] .star,val (point ret [g,f,f] .star) false)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[some [g],some [f,f]]⟩

def rows4 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩,⟨point p [g,f] .may,point ret [g] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : ProgressiveMachine.rounds 6 4 3 3 methods tree4 rows3 saved3 source = state4 := by decide

theorem quiescent_4 : ProgressiveMachine.round 4 3 3 methods tree4 rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : outputRows state4.cold = rows4 ∧ ProgressiveMachine.outputSaved 4 saved3 state4 = saved4 ∧ ((ProgressiveMachine.install tree4 state4).map (unique pathKey)) = [[[g]],[[f],[f,f]]] := by decide

theorem persistent_tree_4 : tree4 = ((ProgressiveMachine.install tree2 state2).map (unique pathKey)) := by decide

theorem producer_permission_4 : (state4.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree5 : ProgressiveMachine.Trees := [[[g]],[[f],[f,f]]]

def state5 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g] .may (some t),true⟩,⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,g] .star,false⟩]],[[(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g,f] .may) true),(point p [g] .star,val (point ret [g,f] .ne) true),(point p [g,f] .star,val (point ret [g,f] .may) true),(point p [g,f] .star,val (point ret [g,f] .ne) true),(point p [g] .star,val (point ret [g,f,f] .star) false),(point p [g,f] .star,val (point ret [g,f,f] .ne) true),(point p [g,f,g] .star,val (point ret [g,f] .ne) true)],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[some [g,f],none]⟩

def rows5 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩,⟨point p [g,f] .may,point ret [g] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩,⟨point p [g,f] .may,point ret [g,f] .star⟩,⟨point p [g,f] .ne,point ret [g,f] .star⟩,⟨point p [g,f,f] .ne,point ret [g,f] .star⟩,⟨point p [g,f] .ne,point ret [g,f,g] .star⟩],[]]

def saved5 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : ProgressiveMachine.rounds 6 5 4 3 methods tree5 rows4 saved4 source = state5 := by decide

theorem quiescent_5 : ProgressiveMachine.round 5 4 3 methods tree5 rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : outputRows state5.cold = rows5 ∧ ProgressiveMachine.outputSaved 5 saved4 state5 = saved5 ∧ ((ProgressiveMachine.install tree5 state5).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_5 : tree5 = ((ProgressiveMachine.install tree3 state3).map (unique pathKey)) := by decide

def tree6 : ProgressiveMachine.Trees := [[[g]],[[f],[f,f]]]

def state6 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .star,false⟩]],[[(point p [g] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g,f] .may) true),(point p [g,f] .star,val (point ret [g,f] .may) true),(point p [g,f] .star,val (point ret [g,f,g] .may) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[some [g,f],none]⟩

def rows6 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩,⟨point p [g,f] .may,point ret [g] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [g,f] .may,point ret [g,f] .star⟩,⟨point p [g,f,g] .may,point ret [g,f] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : ProgressiveMachine.rounds 6 6 5 3 methods tree6 rows5 saved5 source = state6 := by decide

theorem quiescent_6 : ProgressiveMachine.round 6 5 3 methods tree6 rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : outputRows state6.cold = rows6 ∧ ProgressiveMachine.outputSaved 6 saved5 state6 = saved6 ∧ ((ProgressiveMachine.install tree6 state6).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_6 : tree6 = ((ProgressiveMachine.install tree4 state4).map (unique pathKey)) := by decide

theorem producer_permission_6 : (state6.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree7 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state7 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩]],[[],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f] .ne (some t),true⟩],[⟨point p [g,f,f,f] .ne (some t),true⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f] .ne (some t),true⟩]]⟩,[none,none]⟩

def rows7 : List (List Row) := [[],[]]

def saved7 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : ProgressiveMachine.rounds 6 7 6 3 methods tree7 rows6 saved6 source = state7 := by decide

theorem quiescent_7 : ProgressiveMachine.round 7 6 3 methods tree7 rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : outputRows state7.cold = rows7 ∧ ProgressiveMachine.outputSaved 7 saved6 state7 = saved7 ∧ ((ProgressiveMachine.install tree7 state7).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_7 : tree7 = ((ProgressiveMachine.install tree5 state5).map (unique pathKey)) := by decide

def tree8 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state8 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[none,none]⟩

def rows8 : List (List Row) := [[],[]]

def saved8 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_8 : ProgressiveMachine.rounds 6 8 7 3 methods tree8 rows7 saved7 source = state8 := by decide

theorem quiescent_8 : ProgressiveMachine.round 8 7 3 methods tree8 rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : outputRows state8.cold = rows8 ∧ ProgressiveMachine.outputSaved 8 saved7 state8 = saved8 ∧ ((ProgressiveMachine.install tree8 state8).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_8 : tree8 = ((ProgressiveMachine.install tree6 state6).map (unique pathKey)) := by decide

theorem producer_permission_8 : (state8.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree9 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state9 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,f,f] .ne (some t),true⟩]]⟩,[none,none]⟩

def rows9 : List (List Row) := [[],[]]

def saved9 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_9 : ProgressiveMachine.rounds 6 9 8 3 methods tree9 rows8 saved8 source = state9 := by decide

theorem quiescent_9 : ProgressiveMachine.round 9 8 3 methods tree9 rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : outputRows state9.cold = rows9 ∧ ProgressiveMachine.outputSaved 9 saved8 state9 = saved9 ∧ ((ProgressiveMachine.install tree9 state9).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_9 : tree9 = ((ProgressiveMachine.install tree7 state7).map (unique pathKey)) := by decide

def tree10 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state10 : ProgressiveMachine.State := ⟨⟨[[⟨point p [] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩,[none,none]⟩

def rows10 : List (List Row) := [[],[]]

def saved10 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_10 : ProgressiveMachine.rounds 6 10 9 3 methods tree10 rows9 saved9 source = state10 := by decide

theorem quiescent_10 : ProgressiveMachine.round 10 9 3 methods tree10 rows9 saved9 state10 = state10 := by decide

theorem handoff_10 : outputRows state10.cold = rows10 ∧ ProgressiveMachine.outputSaved 10 saved9 state10 = saved10 ∧ ((ProgressiveMachine.install tree10 state10).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_10 : tree10 = ((ProgressiveMachine.install tree8 state8).map (unique pathKey)) := by decide

theorem producer_permission_10 : (state10.cold.offers[3]!).any (fun a => admits a.ap.tail a.ap.e [g,f,g] && a.ap.mark == some t) = true := by decide

def tree11 : ProgressiveMachine.Trees := [[[g],[g,f]],[[f],[f,f]]]

def state11 : ProgressiveMachine.State := ⟨⟨[[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [g,f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,f,f,f,f,f,g] .must (some t),false⟩]]⟩,[none,none]⟩

def rows11 : List (List Row) := [[],[]]

def saved11 : List (List Saved) := [[⟨(point p [g,f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [g] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_11 : ProgressiveMachine.rounds 6 11 10 3 methods tree11 rows10 saved10 source = state11 := by decide

theorem quiescent_11 : ProgressiveMachine.round 11 10 3 methods tree11 rows10 saved10 state11 = state11 := by decide

theorem handoff_11 : outputRows state11.cold = rows11 ∧ ProgressiveMachine.outputSaved 11 saved10 state11 = saved11 ∧ ((ProgressiveMachine.install tree11 state11).map (unique pathKey)) = [[[g],[g,f]],[[f],[f,f]]] := by decide

theorem persistent_tree_11 : tree11 = ((ProgressiveMachine.install tree9 state9).map (unique pathKey)) := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem complete_frontier_and_expected_observations : rows11.all List.isEmpty = true ∧ (((state11.cold.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state11.cold.offers[3]!).map terminal) = [0] := by decide

end PartitionPrefixPostfix

#print axioms PartitionPrefixPostfix.cold_1

#print axioms PartitionPrefixPostfix.quiescent_1

#print axioms PartitionPrefixPostfix.handoff_1

#print axioms PartitionPrefixPostfix.cold_2

#print axioms PartitionPrefixPostfix.quiescent_2

#print axioms PartitionPrefixPostfix.handoff_2

#print axioms PartitionPrefixPostfix.producer_permission_2

#print axioms PartitionPrefixPostfix.cold_3

#print axioms PartitionPrefixPostfix.quiescent_3

#print axioms PartitionPrefixPostfix.handoff_3

#print axioms PartitionPrefixPostfix.persistent_tree_3

#print axioms PartitionPrefixPostfix.cold_4

#print axioms PartitionPrefixPostfix.quiescent_4

#print axioms PartitionPrefixPostfix.handoff_4

#print axioms PartitionPrefixPostfix.persistent_tree_4

#print axioms PartitionPrefixPostfix.producer_permission_4

#print axioms PartitionPrefixPostfix.cold_5

#print axioms PartitionPrefixPostfix.quiescent_5

#print axioms PartitionPrefixPostfix.handoff_5

#print axioms PartitionPrefixPostfix.persistent_tree_5

#print axioms PartitionPrefixPostfix.cold_6

#print axioms PartitionPrefixPostfix.quiescent_6

#print axioms PartitionPrefixPostfix.handoff_6

#print axioms PartitionPrefixPostfix.persistent_tree_6

#print axioms PartitionPrefixPostfix.producer_permission_6

#print axioms PartitionPrefixPostfix.cold_7

#print axioms PartitionPrefixPostfix.quiescent_7

#print axioms PartitionPrefixPostfix.handoff_7

#print axioms PartitionPrefixPostfix.persistent_tree_7

#print axioms PartitionPrefixPostfix.cold_8

#print axioms PartitionPrefixPostfix.quiescent_8

#print axioms PartitionPrefixPostfix.handoff_8

#print axioms PartitionPrefixPostfix.persistent_tree_8

#print axioms PartitionPrefixPostfix.producer_permission_8

#print axioms PartitionPrefixPostfix.cold_9

#print axioms PartitionPrefixPostfix.quiescent_9

#print axioms PartitionPrefixPostfix.handoff_9

#print axioms PartitionPrefixPostfix.persistent_tree_9

#print axioms PartitionPrefixPostfix.cold_10

#print axioms PartitionPrefixPostfix.quiescent_10

#print axioms PartitionPrefixPostfix.handoff_10

#print axioms PartitionPrefixPostfix.persistent_tree_10

#print axioms PartitionPrefixPostfix.producer_permission_10

#print axioms PartitionPrefixPostfix.cold_11

#print axioms PartitionPrefixPostfix.quiescent_11

#print axioms PartitionPrefixPostfix.handoff_11

#print axioms PartitionPrefixPostfix.persistent_tree_11

#print axioms PartitionPrefixPostfix.complete_frontier_and_expected_observations
