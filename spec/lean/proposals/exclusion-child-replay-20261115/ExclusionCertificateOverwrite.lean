import ExclusionCover

import TargetZeroKernel

namespace ExclusionOverwrite

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay ExclusionChildReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List Method := [[[Op.call 1]],[[Op.overwrite g,Op.move [] [f],Op.move [] [f],Op.overwrite g],[Op.overwrite g,Op.move [f] [],Op.move [f] [],Op.overwrite g]]]

def source : Offered := ⟨point p [f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .ne (some t),true⟩],[⟨point p [] .star,false⟩]],[[(point p [] .star,val (point ret [] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : ExclusionChildReplay.rounds true 6 1 1 3 methods rows0 saved0 ExclusionOverwrite.source = state1 := by decide

theorem quiescent_1 : ExclusionChildReplay.round true 1 1 3 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : ExclusionChildReplay.rounds true 6 2 1 3 methods rows1 saved1 ExclusionOverwrite.source = state2 := by decide

theorem quiescent_2 : ExclusionChildReplay.round true 2 1 3 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem actual_producer_permission_2 : (state2.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,g] .star,false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f,g] .star,val (point ret [] .may) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [] .may,point ret [f,g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_3 : ExclusionChildReplay.rounds true 6 3 2 3 methods rows2 saved2 ExclusionOverwrite.source = state3 := by decide

theorem quiescent_3 : ExclusionChildReplay.round true 3 2 3 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),(point p [] .star,val (point ret [f,g] .may) true)],[(point p [f] .star,val (point ret [f] .may) true),(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f] .star,val (point ret [f,g] .may) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [] .star⟩],[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_4 : ExclusionChildReplay.rounds true 6 4 3 3 methods rows3 saved3 ExclusionOverwrite.source = state4 := by decide

theorem quiescent_4 : ExclusionChildReplay.round true 4 3 3 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem actual_producer_permission_4 : (state4.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true),(point p [f,g] .must,val (point ret [f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .ne) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩,⟨point p [f] .ne,point ret [f,g] .must⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩],[]]

def saved5 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_5 : ExclusionChildReplay.rounds true 6 5 4 3 methods rows4 saved4 ExclusionOverwrite.source = state5 := by decide

theorem quiescent_5 : ExclusionChildReplay.round true 5 4 3 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f,f] .may) true),(point p [f] .star,val (point ret [f,g] .may) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .may,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [f] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_6 : ExclusionChildReplay.rounds true 6 6 5 3 methods rows5 saved5 ExclusionOverwrite.source = state6 := by decide

theorem quiescent_6 : ExclusionChildReplay.round true 6 5 3 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

theorem actual_producer_permission_6 : (state6.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state7 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩,⟨point p [f,f,f] .star,false⟩]],[[(point p [f] .star,val (point ret [f] .may) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩]]⟩

def rows7 : List (List Row) := [[⟨point p [f] .may,point ret [f] .star⟩],[]]

def saved7 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_7 : ExclusionChildReplay.rounds true 6 7 6 3 methods rows6 saved6 ExclusionOverwrite.source = state7 := by decide

theorem quiescent_7 : ExclusionChildReplay.round true 7 6 3 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[],[]]

def saved8 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_8 : ExclusionChildReplay.rounds true 6 8 7 3 methods rows7 saved7 ExclusionOverwrite.source = state8 := by decide

theorem quiescent_8 : ExclusionChildReplay.round true 8 7 3 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

theorem actual_producer_permission_8 : (state8.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state9 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,g] .must (some t),false⟩]]⟩

def rows9 : List (List Row) := [[],[]]

def saved9 : List (List Saved) := [[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩],[⟨(point p [f,f] .star,val ({point ret [] .star with e := [g]}) false),true⟩,⟨(point p [] .star,val ({point ret [f,f] .star with e := [g]}) false),false⟩]]

theorem cold_9 : ExclusionChildReplay.rounds true 6 9 8 3 methods rows8 saved8 ExclusionOverwrite.source = state9 := by decide

theorem quiescent_9 : ExclusionChildReplay.round true 9 8 3 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows9.all List.isEmpty = true ∧ (((state9.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state9.offers[3]!).map terminal) = [0] := by decide

end ExclusionOverwrite

#print axioms ExclusionOverwrite.cold_1

#print axioms ExclusionOverwrite.quiescent_1

#print axioms ExclusionOverwrite.handoff_1

#print axioms ExclusionOverwrite.cold_2

#print axioms ExclusionOverwrite.quiescent_2

#print axioms ExclusionOverwrite.handoff_2

#print axioms ExclusionOverwrite.actual_producer_permission_2

#print axioms ExclusionOverwrite.cold_3

#print axioms ExclusionOverwrite.quiescent_3

#print axioms ExclusionOverwrite.handoff_3

#print axioms ExclusionOverwrite.cold_4

#print axioms ExclusionOverwrite.quiescent_4

#print axioms ExclusionOverwrite.handoff_4

#print axioms ExclusionOverwrite.actual_producer_permission_4

#print axioms ExclusionOverwrite.cold_5

#print axioms ExclusionOverwrite.quiescent_5

#print axioms ExclusionOverwrite.handoff_5

#print axioms ExclusionOverwrite.cold_6

#print axioms ExclusionOverwrite.quiescent_6

#print axioms ExclusionOverwrite.handoff_6

#print axioms ExclusionOverwrite.actual_producer_permission_6

#print axioms ExclusionOverwrite.cold_7

#print axioms ExclusionOverwrite.quiescent_7

#print axioms ExclusionOverwrite.handoff_7

#print axioms ExclusionOverwrite.cold_8

#print axioms ExclusionOverwrite.quiescent_8

#print axioms ExclusionOverwrite.handoff_8

#print axioms ExclusionOverwrite.actual_producer_permission_8

#print axioms ExclusionOverwrite.cold_9

#print axioms ExclusionOverwrite.quiescent_9

#print axioms ExclusionOverwrite.handoff_9

#print axioms ExclusionOverwrite.natural_stop_and_expected_observations
