import NestedWriteReplay

import TargetZeroKernel

namespace NestedWriteCold

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay NestedWriteReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List NestedWriteReplay.Method := [[[Op.nestedWrite [f,g],Op.move [f] [],Op.nestedWrite [f,g]],[Op.nestedWrite [f,g],Op.move [] [f],Op.nestedWrite [f,g]]]]

def source : Offered := ⟨point p [g] .must (some t),false⟩

def rows0 : List (List Row) := [[]]

def saved0 : List (List Saved) := [[]]

def state1 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .star) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .star,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[]]

theorem cold_1 : NestedWriteReplay.rounds 6 1 1 1 methods rows0 saved0 NestedWriteCold.source = state1 := by decide

theorem quiescent_1 : NestedWriteReplay.round 1 1 1 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_2 : NestedWriteReplay.rounds 6 2 1 1 methods rows1 saved1 NestedWriteCold.source = state2 := by decide

theorem quiescent_2 : NestedWriteReplay.round 2 1 1 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

def state3 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved3 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_3 : NestedWriteReplay.rounds 6 3 2 1 methods rows2 saved2 NestedWriteCold.source = state3 := by decide

theorem quiescent_3 : NestedWriteReplay.round 3 2 1 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_4 : NestedWriteReplay.rounds 6 4 3 1 methods rows3 saved3 NestedWriteCold.source = state4 := by decide

theorem quiescent_4 : NestedWriteReplay.round 4 3 1 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

def state5 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved5 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_5 : NestedWriteReplay.rounds 6 5 4 1 methods rows4 saved4 NestedWriteCold.source = state5 := by decide

theorem quiescent_5 : NestedWriteReplay.round 5 4 1 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved6 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_6 : NestedWriteReplay.rounds 6 6 5 1 methods rows5 saved5 NestedWriteCold.source = state6 := by decide

theorem quiescent_6 : NestedWriteReplay.round 6 5 1 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

def state7 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows7 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved7 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_7 : NestedWriteReplay.rounds 6 7 6 1 methods rows6 saved6 NestedWriteCold.source = state7 := by decide

theorem quiescent_7 : NestedWriteReplay.round 7 6 1 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved8 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_8 : NestedWriteReplay.rounds 6 8 7 1 methods rows7 saved7 NestedWriteCold.source = state8 := by decide

theorem quiescent_8 : NestedWriteReplay.round 8 7 1 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

def state9 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows9 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved9 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_9 : NestedWriteReplay.rounds 6 9 8 1 methods rows8 saved8 NestedWriteCold.source = state9 := by decide

theorem quiescent_9 : NestedWriteReplay.round 9 8 1 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

def state10 : State := ⟨[[⟨point p [] .may (some t),true⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows10 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved10 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_10 : NestedWriteReplay.rounds 6 10 9 1 methods rows9 saved9 NestedWriteCold.source = state10 := by decide

theorem quiescent_10 : NestedWriteReplay.round 10 9 1 methods rows9 saved9 state10 = state10 := by decide

theorem handoff_10 : OverwriteReplay.outputRows state10 = rows10 ∧ OverwriteReplay.outputSaved 10 saved9 state10 = saved10 := by decide

def state11 : State := ⟨[[⟨point p [g] .must (some t),false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows11 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved11 : List (List Saved) := [[⟨(point p [f] .star,val ({point ret [] .star with e := [f,g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f] .star with e := [f,g]}) false),true⟩]]

theorem cold_11 : NestedWriteReplay.rounds 6 11 10 1 methods rows10 saved10 NestedWriteCold.source = state11 := by decide

theorem quiescent_11 : NestedWriteReplay.round 11 10 1 methods rows10 saved10 state11 = state11 := by decide

theorem handoff_11 : OverwriteReplay.outputRows state11 = rows11 ∧ OverwriteReplay.outputSaved 11 saved10 state11 = saved11 := by decide

end NestedWriteCold

#print axioms NestedWriteCold.cold_1

#print axioms NestedWriteCold.quiescent_1

#print axioms NestedWriteCold.handoff_1

#print axioms NestedWriteCold.cold_2

#print axioms NestedWriteCold.quiescent_2

#print axioms NestedWriteCold.handoff_2

#print axioms NestedWriteCold.cold_3

#print axioms NestedWriteCold.quiescent_3

#print axioms NestedWriteCold.handoff_3

#print axioms NestedWriteCold.cold_4

#print axioms NestedWriteCold.quiescent_4

#print axioms NestedWriteCold.handoff_4

#print axioms NestedWriteCold.cold_5

#print axioms NestedWriteCold.quiescent_5

#print axioms NestedWriteCold.handoff_5

#print axioms NestedWriteCold.cold_6

#print axioms NestedWriteCold.quiescent_6

#print axioms NestedWriteCold.handoff_6

#print axioms NestedWriteCold.cold_7

#print axioms NestedWriteCold.quiescent_7

#print axioms NestedWriteCold.handoff_7

#print axioms NestedWriteCold.cold_8

#print axioms NestedWriteCold.quiescent_8

#print axioms NestedWriteCold.handoff_8

#print axioms NestedWriteCold.cold_9

#print axioms NestedWriteCold.quiescent_9

#print axioms NestedWriteCold.handoff_9

#print axioms NestedWriteCold.cold_10

#print axioms NestedWriteCold.quiescent_10

#print axioms NestedWriteCold.handoff_10

#print axioms NestedWriteCold.cold_11

#print axioms NestedWriteCold.quiescent_11

#print axioms NestedWriteCold.handoff_11
