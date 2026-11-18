import ExclusionCover

import TargetZeroKernel

namespace ExclusionDouble

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay ExclusionChildReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List Method := [[[Op.call 1,Op.call 1]],[[Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [f] []]]]

def source : Offered := ⟨point p [f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .ne (some t),true⟩],[⟨point p [] .star,false⟩,⟨point p [] .may,true⟩]],[[(point p [] .star,val (point ret [] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : ExclusionChildReplay.rounds true 6 1 1 3 methods rows0 saved0 ExclusionDouble.source = state1 := by decide

theorem quiescent_1 : ExclusionChildReplay.round true 1 1 3 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [f] .ne,true⟩]],[[(point p [] .star,val (point ret [] .may) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : ExclusionChildReplay.rounds true 6 2 1 3 methods rows1 saved1 ExclusionDouble.source = state2 := by decide

theorem quiescent_2 : ExclusionChildReplay.round true 2 1 3 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem actual_producer_permission_2 : (state2.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[(point p [] .star,val (point ret [] .star) false),(point p [] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [] .may) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [f,f] .star,val (point ret [] .star) false),(point p [] .star,val (point ret [f,f] .star) false),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [] .may,point ret [f] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved3 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : ExclusionChildReplay.rounds true 6 3 2 3 methods rows2 saved2 ExclusionDouble.source = state3 := by decide

theorem quiescent_3 : ExclusionChildReplay.round true 3 2 3 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .ne) true)],[(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f,f] .may) true),(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f,f] .ne,point ret [] .star⟩],[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : ExclusionChildReplay.rounds true 6 4 3 3 methods rows3 saved3 ExclusionDouble.source = state4 := by decide

theorem quiescent_4 : ExclusionChildReplay.round true 4 3 3 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem actual_producer_permission_4 : (state4.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [] .ne (some t),true⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,f] .ne,true⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f] .ne,true⟩,⟨point p [f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,g] .star,false⟩]],[[(point p [] .star,val (point ret [] .ne) true),(point p [f] .star,val (point ret [] .ne) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [f,f] .star,val (point ret [] .ne) true),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true)],[(point p [f,f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f,f] .ne) true),(point p [f,f,f,f] .star,val (point ret [f,f,f] .ne) true),(point p [f,f,f,g] .star,val (point ret [f,f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .ne (some t),true⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .ne (some t),true⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .ne (some t),true⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [] .ne,point ret [f,f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩],[⟨point p [f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f,f,g] .star⟩]]

def saved5 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : ExclusionChildReplay.rounds true 6 5 4 3 methods rows4 saved4 ExclusionDouble.source = state5 := by decide

theorem quiescent_5 : ExclusionChildReplay.round true 5 4 3 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩]],[[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .ne) true),(point p [f] .star,val (point ret [f,f] .may) true),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f] .star,val (point ret [f,g] .may) true),(point p [] .star,val (point ret [f,f,f] .ne) true),(point p [f] .star,val (point ret [f,f,f] .ne) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [] .star⟩,⟨point p [f,f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [f] .star⟩,⟨point p [f,f,f] .ne,point ret [] .star⟩,⟨point p [f,f,f] .ne,point ret [f] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : ExclusionChildReplay.rounds true 6 6 5 3 methods rows5 saved5 ExclusionDouble.source = state6 := by decide

theorem quiescent_6 : ExclusionChildReplay.round true 6 5 3 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

theorem actual_producer_permission_6 : (state6.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state7 : State := ⟨[[⟨point p [f] .ne (some t),true⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,g] .exact,false⟩,⟨point p [f,f,f,g] .star,false⟩,⟨point p [f,f,f,g] .must,false⟩,⟨point p [f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f] .star,false⟩]],[[(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .ne) true),(point p [f,g] .must,val (point ret [f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f] .ne) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f] .ne (some t),true⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [f] .ne (some t),true⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [f] .ne (some t),true⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩]]⟩

def rows7 : List (List Row) := [[⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .must⟩,⟨point p [f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f,f] .star⟩],[]]

def saved7 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : ExclusionChildReplay.rounds true 6 7 6 3 methods rows6 saved6 ExclusionDouble.source = state7 := by decide

theorem quiescent_7 : ExclusionChildReplay.round true 7 6 3 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f] .star,false⟩]],[[(point p [f,f] .star,val (point ret [] .may) true),(point p [f,f] .star,val (point ret [f] .may) true),(point p [f,f] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f] .may) true),(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,g] .may) true),(point p [f] .star,val (point ret [f,f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,f] .may) true),(point p [f,f] .star,val (point ret [f,f,f] .ne) true),(point p [f] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,f,f] .ne) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[⟨point p [] .may,point ret [f,f] .star⟩,⟨point p [f] .may,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .may,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,g] .may,point ret [f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f] .star⟩,⟨point p [f,f,f] .may,point ret [f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,f] .star⟩],[]]

def saved8 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_8 : ExclusionChildReplay.rounds true 6 8 7 3 methods rows7 saved7 ExclusionDouble.source = state8 := by decide

theorem quiescent_8 : ExclusionChildReplay.round true 8 7 3 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

theorem actual_producer_permission_8 : (state8.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state9 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,g] .exact,false⟩,⟨point p [f,f,f,g] .star,false⟩,⟨point p [f,f,f,g] .must,false⟩,⟨point p [f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f] .star,false⟩,⟨point p [f,f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f,f] .star,false⟩]],[[(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [] .star,val (point ret [f,f,f] .ne) true),(point p [f] .star,val (point ret [f,f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f,f] .ne) true),(point p [f,g] .must,val (point ret [f,f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f,f] .ne) true),(point p [f,f,f,f] .star,val (point ret [] .star) false),(point p [f,f,f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f,f,f] .star,val (point ret [f,f,f] .ne) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩]]⟩

def rows9 : List (List Row) := [[⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [] .star⟩,⟨point p [f,f,f] .ne,point ret [f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,f] .ne,point ret [f,g] .must⟩,⟨point p [f,f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f] .ne,point ret [f,f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f,f,f] .star⟩],[]]

def saved9 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_9 : ExclusionChildReplay.rounds true 6 9 8 3 methods rows8 saved8 ExclusionDouble.source = state9 := by decide

theorem quiescent_9 : ExclusionChildReplay.round true 9 8 3 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

def state10 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f] .star,false⟩]],[[(point p [f,f,f] .star,val (point ret [] .may) true),(point p [f,f,f] .star,val (point ret [f] .may) true),(point p [f,f,f] .star,val (point ret [f,f] .may) true),(point p [f,f,f] .star,val (point ret [f,g] .may) true),(point p [f,f,f] .star,val (point ret [f,f,f] .may) true),(point p [f,f,f] .star,val (point ret [f,f,f,f] .may) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows10 : List (List Row) := [[⟨point p [] .may,point ret [f,f,f] .star⟩,⟨point p [f] .may,point ret [f,f,f] .star⟩,⟨point p [f,f] .may,point ret [f,f,f] .star⟩,⟨point p [f,g] .may,point ret [f,f,f] .star⟩,⟨point p [f,f,f] .may,point ret [f,f,f] .star⟩,⟨point p [f,f,f,f] .may,point ret [f,f,f] .star⟩],[]]

def saved10 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_10 : ExclusionChildReplay.rounds true 6 10 9 3 methods rows9 saved9 ExclusionDouble.source = state10 := by decide

theorem quiescent_10 : ExclusionChildReplay.round true 10 9 3 methods rows9 saved9 state10 = state10 := by decide

theorem handoff_10 : OverwriteReplay.outputRows state10 = rows10 ∧ OverwriteReplay.outputSaved 10 saved9 state10 = saved10 := by decide

theorem actual_producer_permission_10 : (state10.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state11 : State := ⟨[[⟨point p [] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .exact,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,g] .exact,false⟩,⟨point p [f,f,f,g] .star,false⟩,⟨point p [f,f,f,g] .must,false⟩,⟨point p [f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f] .star,false⟩,⟨point p [f,f,f,f,f,f] .exact,false⟩,⟨point p [f,f,f,f,f,f] .star,false⟩,⟨point p [f,f,f,f,f,f,f] .star,false⟩]],[[(point p [] .star,val (point ret [f,f,f,f] .star) false),(point p [f] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,g] .must,val (point ret [f,f,f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,f,f,f] .star,val (point ret [f,f,f,f] .ne) true),(point p [f,f,f,f,f] .star,val (point ret [f,f,f,f] .ne) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩]]⟩

def rows11 : List (List Row) := [[⟨point p [f,f,f,f] .ne,point ret [f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,g] .must⟩,⟨point p [f,f,f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,f,f,f] .star⟩,⟨point p [f,f,f,f] .ne,point ret [f,f,f,f,f] .star⟩],[]]

def saved11 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_11 : ExclusionChildReplay.rounds true 6 11 10 3 methods rows10 saved10 ExclusionDouble.source = state11 := by decide

theorem quiescent_11 : ExclusionChildReplay.round true 11 10 3 methods rows10 saved10 state11 = state11 := by decide

theorem handoff_11 : OverwriteReplay.outputRows state11 = rows11 ∧ OverwriteReplay.outputSaved 11 saved10 state11 = saved11 := by decide

def state12 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [f,f] .star,false⟩,⟨point p [f,f,f,f] .star,false⟩,⟨point p [f,f,f,f,f,f] .star,false⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows12 : List (List Row) := [[],[]]

def saved12 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_12 : ExclusionChildReplay.rounds true 6 12 11 3 methods rows11 saved11 ExclusionDouble.source = state12 := by decide

theorem quiescent_12 : ExclusionChildReplay.round true 12 11 3 methods rows11 saved11 state12 = state12 := by decide

theorem handoff_12 : OverwriteReplay.outputRows state12 = rows12 ∧ OverwriteReplay.outputSaved 12 saved11 state12 = saved12 := by decide

theorem actual_producer_permission_12 : (state12.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state13 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,f,f,f] .ne (some t),true⟩]]⟩

def rows13 : List (List Row) := [[],[]]

def saved13 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_13 : ExclusionChildReplay.rounds true 6 13 12 3 methods rows12 saved12 ExclusionDouble.source = state13 := by decide

theorem quiescent_13 : ExclusionChildReplay.round true 13 12 3 methods rows12 saved12 state13 = state13 := by decide

theorem handoff_13 : OverwriteReplay.outputRows state13 = rows13 ∧ OverwriteReplay.outputSaved 13 saved12 state13 = saved13 := by decide

def state14 : State := ⟨[[⟨point p [] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows14 : List (List Row) := [[],[]]

def saved14 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_14 : ExclusionChildReplay.rounds true 6 14 13 3 methods rows13 saved13 ExclusionDouble.source = state14 := by decide

theorem quiescent_14 : ExclusionChildReplay.round true 14 13 3 methods rows13 saved13 state14 = state14 := by decide

theorem handoff_14 : OverwriteReplay.outputRows state14 = rows14 ∧ OverwriteReplay.outputSaved 14 saved13 state14 = saved14 := by decide

theorem actual_producer_permission_14 : (state14.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state15 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,f,f,f,f,f,f,g] .must (some t),false⟩]]⟩

def rows15 : List (List Row) := [[],[]]

def saved15 : List (List Saved) := [[⟨(point p [] .star,val (point ret [] .star) false),false⟩,⟨(point p [f,f,f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),false⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_15 : ExclusionChildReplay.rounds true 6 15 14 3 methods rows14 saved14 ExclusionDouble.source = state15 := by decide

theorem quiescent_15 : ExclusionChildReplay.round true 15 14 3 methods rows14 saved14 state15 = state15 := by decide

theorem handoff_15 : OverwriteReplay.outputRows state15 = rows15 ∧ OverwriteReplay.outputSaved 15 saved14 state15 = saved15 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows15.all List.isEmpty = true ∧ (((state15.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state15.offers[3]!).map terminal) = [0] := by decide

end ExclusionDouble

#print axioms ExclusionDouble.cold_1

#print axioms ExclusionDouble.quiescent_1

#print axioms ExclusionDouble.handoff_1

#print axioms ExclusionDouble.cold_2

#print axioms ExclusionDouble.quiescent_2

#print axioms ExclusionDouble.handoff_2

#print axioms ExclusionDouble.actual_producer_permission_2

#print axioms ExclusionDouble.cold_3

#print axioms ExclusionDouble.quiescent_3

#print axioms ExclusionDouble.handoff_3

#print axioms ExclusionDouble.cold_4

#print axioms ExclusionDouble.quiescent_4

#print axioms ExclusionDouble.handoff_4

#print axioms ExclusionDouble.actual_producer_permission_4

#print axioms ExclusionDouble.cold_5

#print axioms ExclusionDouble.quiescent_5

#print axioms ExclusionDouble.handoff_5

#print axioms ExclusionDouble.cold_6

#print axioms ExclusionDouble.quiescent_6

#print axioms ExclusionDouble.handoff_6

#print axioms ExclusionDouble.actual_producer_permission_6

#print axioms ExclusionDouble.cold_7

#print axioms ExclusionDouble.quiescent_7

#print axioms ExclusionDouble.handoff_7

#print axioms ExclusionDouble.cold_8

#print axioms ExclusionDouble.quiescent_8

#print axioms ExclusionDouble.handoff_8

#print axioms ExclusionDouble.actual_producer_permission_8

#print axioms ExclusionDouble.cold_9

#print axioms ExclusionDouble.quiescent_9

#print axioms ExclusionDouble.handoff_9

#print axioms ExclusionDouble.cold_10

#print axioms ExclusionDouble.quiescent_10

#print axioms ExclusionDouble.handoff_10

#print axioms ExclusionDouble.actual_producer_permission_10

#print axioms ExclusionDouble.cold_11

#print axioms ExclusionDouble.quiescent_11

#print axioms ExclusionDouble.handoff_11

#print axioms ExclusionDouble.cold_12

#print axioms ExclusionDouble.quiescent_12

#print axioms ExclusionDouble.handoff_12

#print axioms ExclusionDouble.actual_producer_permission_12

#print axioms ExclusionDouble.cold_13

#print axioms ExclusionDouble.quiescent_13

#print axioms ExclusionDouble.handoff_13

#print axioms ExclusionDouble.cold_14

#print axioms ExclusionDouble.quiescent_14

#print axioms ExclusionDouble.handoff_14

#print axioms ExclusionDouble.actual_producer_permission_14

#print axioms ExclusionDouble.cold_15

#print axioms ExclusionDouble.quiescent_15

#print axioms ExclusionDouble.handoff_15

#print axioms ExclusionDouble.natural_stop_and_expected_observations
