import ExclusionCover

import TargetZeroKernel

namespace ExclusionGrowth

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay ExclusionChildReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List Method := [[[Op.move [g] [],Op.move [g] [],Op.call 1],[Op.move [f] [],Op.call 1,Op.move [] [f],Op.move [] [f]],[Op.move [f] [],Op.move [g] [],Op.move [f] [],Op.call 1,Op.call 1]],[[Op.move [g] [],Op.move [g] [],Op.move [g] [],Op.move [] [f],Op.move [] [g],Op.move [] [f]],[Op.move [f] [],Op.move [f] [],Op.move [] [g]],[Op.move [] [f],Op.move [] [f],Op.move [] [g]],[Op.move [g] [],Op.move [g] [],Op.move [] [f],Op.move [] [f]]]]

def source : Offered := ⟨point p [g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[⟨point p [f] .ne (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [g] .must (some t),false⟩],[⟨point p [] .may,true⟩,⟨point p [f] .ne,true⟩,⟨point p [g] .may,true⟩]],[[(point p [] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [g] .may) true)],[(point p [] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [g] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [f] .ne (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [f] .ne (some t),true⟩,⟨point p [g] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [f] .ne,point ret [] .star⟩,⟨point p [g] .may,point ret [] .star⟩],[⟨point p [f] .ne,point ret [] .star⟩,⟨point p [g] .may,point ret [] .star⟩,⟨point p [g] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : ExclusionChildReplay.rounds true 6 1 1 2 methods rows0 saved0 ExclusionGrowth.source = state1 := by decide

theorem quiescent_1 : ExclusionChildReplay.round true 1 1 2 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

theorem complete_growth_control_equality_1 : ExclusionChildReplay.rounds false 6 1 1 2 methods rows0 saved0 ExclusionGrowth.source = state1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩],[⟨point p [] .may,true⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .ne,true⟩]],[[(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [g] .ne) true),(point p [g] .star,val (point ret [g] .ne) true)],[(point p [g] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [g] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .ne (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [g] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩,⟨point p [g] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [g] .star⟩,⟨point p [g] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : ExclusionChildReplay.rounds true 6 2 1 2 methods rows1 saved1 ExclusionGrowth.source = state2 := by decide

theorem quiescent_2 : ExclusionChildReplay.round true 2 1 2 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem complete_growth_control_equality_2 : ExclusionChildReplay.rounds false 6 2 1 2 methods rows1 saved1 ExclusionGrowth.source = state2 := by decide

theorem actual_producer_permission_2 : (state2.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [g] a.ap.path).isSome || match dropHead a.ap.path [g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [g] .may (some t),true⟩,⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .may,true⟩,⟨point p [] .must,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [f,f] .may,true⟩,⟨point p [f,g] .ne,true⟩]],[[(point p [g] .star,val (point ret [g] .may) true),(point p [g] .must,val (point ret [g] .may) true),(point p [g] .must,val (point ret [g] .must) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [g] .star,val (point ret [f,f] .may) true),(point p [g] .must,val (point ret [f,f] .may) true),(point p [f,g] .star,val (point ret [g] .may) true),(point p [g] .must,val (point ret [f,f] .must) false),(point p [g] .star,val (point ret [f,g] .ne) true),(point p [g] .must,val (point ret [f,g] .ne) true),(point p [f,f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .may) true),(point p [f,g] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f,g] .ne) true)],[(point p [] .must,val (point ret [g] .must) false),(point p [f] .star,val (point ret [g] .may) true),(point p [f] .must,val (point ret [g] .must) false),(point p [] .star,val (point ret [g,f] .ne) true),(point p [f,f] .star,val (point ret [g] .star) false),(point p [g] .star,val (point ret [f,f] .may) true),(point p [g] .must,val (point ret [f,f] .must) false),(point p [g] .star,val (point ret [f,g] .ne) true),(point p [g] .must,val (point ret [f,g] .ne) true),(point p [f] .star,val (point ret [g,f] .ne) true),(point p [g] .star,val (point ret [g,f] .ne) true),(point p [f,f] .star,val (point ret [g,f] .ne) true),(point p [f,g] .star,val (point ret [g,f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [g] .may (some t),true⟩,⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g] .ne (some t),true⟩],[⟨point p [g] .may (some t),true⟩,⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g] .ne (some t),true⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [g] .may,point ret [g] .star⟩,⟨point p [g] .may,point ret [g] .must⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,f] .may,point ret [g] .star⟩,⟨point p [f,f] .may,point ret [g] .must⟩,⟨point p [g] .may,point ret [f,g] .star⟩,⟨point p [f,g] .ne,point ret [g] .star⟩,⟨point p [f,g] .ne,point ret [g] .must⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f] .may,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,g] .ne,point ret [f,g] .star⟩],[⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [] .star⟩,⟨point p [f,f] .may,point ret [g] .star⟩,⟨point p [f,g] .ne,point ret [g] .star⟩,⟨point p [f,g] .ne,point ret [g] .must⟩,⟨point p [g,f] .ne,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩,⟨point p [g,f] .ne,point ret [f,f] .star⟩,⟨point p [g,f] .ne,point ret [f,g] .star⟩]]

def saved3 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩]]

theorem cold_3 : ExclusionChildReplay.rounds true 6 3 2 2 methods rows2 saved2 ExclusionGrowth.source = state3 := by decide

theorem quiescent_3 : ExclusionChildReplay.round true 3 2 2 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

theorem complete_growth_control_equality_3 : ExclusionChildReplay.rounds false 6 3 2 2 methods rows2 saved2 ExclusionGrowth.source = state3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [g,g] .exact,false⟩,⟨point p [g,g] .star,false⟩,⟨point p [g,g] .ne,true⟩]],[[(point p [f,f] .star,val (point ret [f] .may) true),(point p [g] .star,val (point ret [g,g] .may) true),(point p [f,f] .star,val (point ret [f,f] .may) true),(point p [f,f] .star,val (point ret [f,g] .may) true),(point p [f,f] .star,val (point ret [f,g] .ne) true),(point p [f,f] .star,val (point ret [g,g] .ne) true),(point p [f,g] .star,val (point ret [g,g] .ne) true),(point p [g] .star,val (point ret [f,g,f] .may) true),(point p [f,f] .star,val (point ret [f,g,f] .may) true),(point p [f,g] .star,val (point ret [f,g,f] .may) true)],[(point p [g,f] .star,val (point ret [] .may) true),(point p [g,f] .star,val (point ret [f] .may) true),(point p [g,f] .star,val (point ret [g] .may) true),(point p [g,f] .star,val (point ret [f,f] .may) true),(point p [f,f] .star,val (point ret [g,g] .star) false),(point p [g,f] .star,val (point ret [f,g] .may) true),(point p [f,g] .star,val (point ret [g,g] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [f] .may,point ret [f,f] .star⟩,⟨point p [g,g] .may,point ret [g] .star⟩,⟨point p [f,f] .may,point ret [f,f] .star⟩,⟨point p [f,g] .may,point ret [f,f] .star⟩,⟨point p [f,g] .ne,point ret [f,f] .star⟩,⟨point p [g,g] .ne,point ret [f,f] .star⟩,⟨point p [g,g] .ne,point ret [f,g] .star⟩,⟨point p [f,g,f] .may,point ret [g] .star⟩,⟨point p [f,g,f] .may,point ret [f,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,g] .star⟩],[⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [f] .may,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩,⟨point p [f,f] .may,point ret [g,f] .star⟩,⟨point p [f,g] .may,point ret [g,f] .star⟩,⟨point p [g,g] .ne,point ret [f,g] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩]]

theorem cold_4 : ExclusionChildReplay.rounds true 6 4 3 2 methods rows3 saved3 ExclusionGrowth.source = state4 := by decide

theorem quiescent_4 : ExclusionChildReplay.round true 4 3 2 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem complete_growth_control_equality_4 : ExclusionChildReplay.rounds false 6 4 3 2 methods rows3 saved3 ExclusionGrowth.source = state4 := by decide

theorem actual_producer_permission_4 : (state4.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [g] a.ap.path).isSome || match dropHead a.ap.path [g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [g,f] .may (some t),true⟩,⟨point p [f,g,f] .may (some t),true⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [] .must,false⟩,⟨point p [f] .star,false⟩,⟨point p [f] .must,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [g] .must,false⟩,⟨point p [f,f] .may,true⟩,⟨point p [f,f] .must,false⟩,⟨point p [g,f] .exact,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,f] .may,true⟩,⟨point p [g,f] .must,false⟩,⟨point p [f,g,f] .may,true⟩,⟨point p [f,g,f] .must,false⟩,⟨point p [g,f,f] .exact,false⟩,⟨point p [g,f,f] .star,false⟩]],[[(point p [g,g] .must,val (point ret [g] .must) false),(point p [f,g] .star,val (point ret [f,f] .may) true),(point p [g,g] .must,val (point ret [f,f] .must) false),(point p [g,g] .must,val (point ret [g,f] .may) true),(point p [f] .star,val (point ret [f,f,g] .ne) true),(point p [f,g,f] .star,val (point ret [g] .may) true),(point p [f,g,f] .must,val (point ret [g] .must) false),(point p [f,g] .star,val (point ret [f,f,f] .ne) true),(point p [f,f] .star,val (point ret [f,f,g] .ne) true),(point p [f,f] .must,val (point ret [f,f,g] .must) false),(point p [f,g] .star,val (point ret [f,f,g] .ne) true),(point p [f,g,f] .must,val (point ret [f,f] .must) false),(point p [f,g,f] .star,val (point ret [g,f] .ne) true),(point p [f,g,f] .must,val (point ret [g,f] .may) true),(point p [g,g] .must,val (point ret [f,g,f] .may) true),(point p [g,g] .must,val (point ret [f,g,f] .must) false),(point p [f,g,f] .star,val (point ret [f,f,g] .ne) true),(point p [f,g,f] .must,val (point ret [f,g,f] .may) true),(point p [f,g,f] .must,val (point ret [f,g,f] .must) false)],[(point p [f] .star,val (point ret [g,f] .may) true),(point p [] .star,val (point ret [g,f,f] .star) false),(point p [] .must,val (point ret [g,f,f] .must) false),(point p [f] .star,val (point ret [g,f,f] .ne) true),(point p [g] .star,val (point ret [g,f,f] .ne) true),(point p [g] .must,val (point ret [g,f,f] .ne) true),(point p [g,g] .star,val (point ret [f,g,f] .may) true),(point p [g,g] .must,val (point ret [f,g,f] .must) false),(point p [f,f] .star,val (point ret [g,f,f] .ne) true),(point p [f,g] .star,val (point ret [g,f,f] .ne) true),(point p [f,g] .must,val (point ret [g,f,f] .ne) true),(point p [g,f] .star,val (point ret [g,f,f] .ne) true),(point p [g,g] .star,val (point ret [g,f,f] .ne) true),(point p [f,g,f] .star,val (point ret [g,f,f] .ne) true)]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [g,f] .may (some t),true⟩,⟨point p [f,g,f] .may (some t),true⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [g] .may (some t),true⟩,⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .may (some t),true⟩,⟨point p [f,g,f] .must (some t),false⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [f,f] .may,point ret [f,g] .star⟩,⟨point p [g,f] .may,point ret [g,g] .must⟩,⟨point p [f,f,g] .ne,point ret [f] .star⟩,⟨point p [g] .may,point ret [f,g,f] .star⟩,⟨point p [f,f,g] .ne,point ret [f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,g] .ne,point ret [f,g] .star⟩,⟨point p [g,f] .ne,point ret [f,g,f] .star⟩,⟨point p [g,f] .may,point ret [f,g,f] .must⟩,⟨point p [f,g,f] .may,point ret [g,g] .must⟩,⟨point p [f,f,g] .ne,point ret [f,g,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,g,f] .must⟩],[⟨point p [g,f] .may,point ret [f] .star⟩,⟨point p [g,f,f] .ne,point ret [f] .star⟩,⟨point p [g,f,f] .ne,point ret [g] .star⟩,⟨point p [g,f,f] .ne,point ret [g] .must⟩,⟨point p [f,g,f] .may,point ret [g,g] .star⟩,⟨point p [g,f,f] .ne,point ret [f,f] .star⟩,⟨point p [g,f,f] .ne,point ret [f,g] .star⟩,⟨point p [g,f,f] .ne,point ret [f,g] .must⟩,⟨point p [g,f,f] .ne,point ret [g,f] .star⟩,⟨point p [g,f,f] .ne,point ret [g,g] .star⟩,⟨point p [g,f,f] .ne,point ret [f,g,f] .star⟩]]

def saved5 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩]]

theorem cold_5 : ExclusionChildReplay.rounds true 6 5 4 2 methods rows4 saved4 ExclusionGrowth.source = state5 := by decide

theorem quiescent_5 : ExclusionChildReplay.round true 5 4 2 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

theorem complete_growth_control_equality_5 : ExclusionChildReplay.rounds false 6 5 4 2 methods rows4 saved4 ExclusionGrowth.source = state5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,g,f] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩,⟨point p [g,f] .exact,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,g] .exact,false⟩,⟨point p [g,g] .star,false⟩,⟨point p [g,g] .may,true⟩,⟨point p [f,f,f] .exact,false⟩,⟨point p [f,f,f] .star,false⟩,⟨point p [f,f,g] .exact,false⟩,⟨point p [f,f,g] .star,false⟩,⟨point p [f,g,f] .exact,false⟩,⟨point p [f,g,f] .star,false⟩,⟨point p [g,g,f] .exact,false⟩,⟨point p [g,g,f] .star,false⟩,⟨point p [g,g,g] .exact,false⟩,⟨point p [g,g,g] .star,false⟩]],[[(point p [f,f] .star,val (point ret [f,g] .may) true),(point p [g,f] .star,val (point ret [g,g] .may) true),(point p [f,f,g] .star,val (point ret [f] .may) true),(point p [g] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g] .star,val (point ret [f,f] .may) true),(point p [f,f,f] .star,val (point ret [f,g] .may) true),(point p [f,f,g] .star,val (point ret [f,f] .ne) true),(point p [f,f,g] .star,val (point ret [f,g] .may) true),(point p [f,f,g] .star,val (point ret [f,g] .ne) true),(point p [f,f] .star,val (point ret [f,g,f] .may) true),(point p [g,f] .star,val (point ret [f,g,f] .may) true),(point p [g,f] .star,val (point ret [g,g,f] .ne) true),(point p [f,f,g] .star,val (point ret [f,f,f] .star) false),(point p [f,f,f] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g] .star,val (point ret [f,g,f] .may) true),(point p [f,g,f] .star,val (point ret [f,g,f] .may) true),(point p [f,g,f] .star,val (point ret [g,g,g] .ne) true),(point p [g] .star,val (point ret [f,g,f,g] .ne) true)],[(point p [f,g,f] .star,val (point ret [g,g,g] .star) false)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[⟨point p [f,g] .may,point ret [f,f] .star⟩,⟨point p [g,g] .may,point ret [g,f] .star⟩,⟨point p [f] .may,point ret [f,f,g] .star⟩,⟨point p [f,g,f] .may,point ret [g] .star⟩,⟨point p [f,g] .may,point ret [f,f,f] .star⟩,⟨point p [f,f] .may,point ret [f,f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,f,g] .star⟩,⟨point p [f,g] .may,point ret [f,f,g] .star⟩,⟨point p [f,g] .ne,point ret [f,f,g] .star⟩,⟨point p [f,g,f] .may,point ret [f,f] .star⟩,⟨point p [f,g,f] .may,point ret [g,f] .star⟩,⟨point p [g,g,f] .ne,point ret [g,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,g] .star⟩,⟨point p [f,g,f] .may,point ret [f,g,f] .star⟩,⟨point p [g,g,g] .ne,point ret [f,g,f] .star⟩,⟨point p [f,g,f,g] .ne,point ret [g] .star⟩],[]]

def saved6 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_6 : ExclusionChildReplay.rounds true 6 6 5 2 methods rows5 saved5 ExclusionGrowth.source = state6 := by decide

theorem quiescent_6 : ExclusionChildReplay.round true 6 5 2 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

theorem complete_growth_control_equality_6 : ExclusionChildReplay.rounds false 6 6 5 2 methods rows5 saved5 ExclusionGrowth.source = state6 := by decide

theorem actual_producer_permission_6 : (state6.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [g] a.ap.path).isSome || match dropHead a.ap.path [g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state7 : State := ⟨[[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [] .must,false⟩,⟨point p [f] .star,false⟩,⟨point p [f] .must,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [g] .must,false⟩,⟨point p [f,f] .may,true⟩,⟨point p [f,f] .must,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,f] .must,false⟩,⟨point p [f,g,f] .may,true⟩,⟨point p [f,g,f] .must,false⟩,⟨point p [g,f,f] .star,false⟩,⟨point p [g,f,g] .must,false⟩,⟨point p [g,f,f,g] .must,false⟩]],[[(point p [g,g] .must,val (point ret [g,f] .must) false),(point p [f,g,f] .must,val (point ret [g] .must) false),(point p [f,g] .star,val (point ret [f,f,g] .may) true),(point p [f,g] .star,val (point ret [f,f,g] .ne) true),(point p [f,g,f] .must,val (point ret [f,f] .must) false),(point p [f,g,f] .must,val (point ret [g,f] .must) false),(point p [g,g,f] .must,val (point ret [g,f] .must) false),(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),(point p [f,g,f] .star,val (point ret [f,f,g] .ne) true),(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),(point p [f] .star,val (point ret [f,f,g,f] .ne) true),(point p [f,g,f,g] .must,val (point ret [g] .must) false),(point p [f,f] .star,val (point ret [f,f,g,f] .ne) true),(point p [f,g] .star,val (point ret [f,f,g,f] .ne) true),(point p [f,g,f] .star,val (point ret [f,f,g,f] .ne) true)],[]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,f,g] .may (some t),true⟩,⟨point p [f,g,f] .must (some t),false⟩]]⟩

def rows7 : List (List Row) := [[⟨point p [f,f,g] .may,point ret [f,g] .star⟩,⟨point p [f,f,g] .ne,point ret [f,g] .star⟩,⟨point p [f,f,g] .ne,point ret [f,g,f] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f,g,f] .star⟩],[]]

def saved7 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f,g] .must,val (point ret [g] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_7 : ExclusionChildReplay.rounds true 6 7 6 2 methods rows6 saved6 ExclusionGrowth.source = state7 := by decide

theorem quiescent_7 : ExclusionChildReplay.round true 7 6 2 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

theorem complete_growth_control_equality_7 : ExclusionChildReplay.rounds false 6 7 6 2 methods rows6 saved6 ExclusionGrowth.source = state7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩,⟨point p [f,f] .may (some t),true⟩,⟨point p [f,g,f] .may (some t),true⟩],[⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [g,f] .exact,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [f,f,g] .exact,false⟩,⟨point p [f,f,g] .star,false⟩,⟨point p [g,g,g] .exact,false⟩,⟨point p [g,g,g] .star,false⟩,⟨point p [f,f,g,f] .exact,false⟩,⟨point p [f,f,g,f] .star,false⟩,⟨point p [g,g,g,f] .exact,false⟩,⟨point p [g,g,g,f] .star,false⟩]],[[(point p [f,f,g] .star,val (point ret [f,g] .may) true),(point p [f,f,g] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g] .star,val (point ret [f,g,f] .ne) true),(point p [f,f,g,f] .star,val (point ret [f] .may) true),(point p [f,f,g,f] .star,val (point ret [f,f] .may) true),(point p [f,f,g,f] .star,val (point ret [f,g] .may) true),(point p [f,f,g,f] .star,val (point ret [f,g] .ne) true),(point p [f,f,g,f] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g] .star,val (point ret [f,g,f,f] .ne) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[⟨point p [f,g] .may,point ret [f,f,g] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,g] .star⟩,⟨point p [f,g,f] .ne,point ret [f,f,g] .star⟩,⟨point p [f] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,f] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,g] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,g] .ne,point ret [f,f,g,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,g,f,f] .ne,point ret [f,f,g] .star⟩],[]]

def saved8 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f,g] .must,val (point ret [g] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_8 : ExclusionChildReplay.rounds true 6 8 7 2 methods rows7 saved7 ExclusionGrowth.source = state8 := by decide

theorem quiescent_8 : ExclusionChildReplay.round true 8 7 2 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

theorem complete_growth_control_equality_8 : ExclusionChildReplay.rounds false 6 8 7 2 methods rows7 saved7 ExclusionGrowth.source = state8 := by decide

theorem actual_producer_permission_8 : (state8.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [g] a.ap.path).isSome || match dropHead a.ap.path [g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state9 : State := ⟨[[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [] .may,true⟩,⟨point p [] .must,false⟩,⟨point p [f] .star,false⟩,⟨point p [f] .must,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [g] .may,true⟩,⟨point p [g] .must,false⟩,⟨point p [f,f] .may,true⟩,⟨point p [f,f] .must,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,f] .must,false⟩,⟨point p [f,g,f] .may,true⟩,⟨point p [f,g,f] .must,false⟩,⟨point p [g,f,f] .star,false⟩,⟨point p [g,f,f] .must,false⟩]],[[(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),(point p [f,g] .star,val (point ret [f,f,g,f] .may) true),(point p [f,g] .star,val (point ret [f,f,g,f] .ne) true),(point p [f,g,f] .star,val (point ret [f,f,g,f] .ne) true),(point p [f,g,f] .must,val (point ret [f,f,g,f] .must) false),(point p [f,g,f,f] .must,val (point ret [f,f,g] .must) false),(point p [f] .star,val (point ret [f,f,g,f,f] .star) false),(point p [f,f] .star,val (point ret [f,f,g,f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f,g,f,f] .ne) true),(point p [f,g,f] .star,val (point ret [f,f,g,f,f] .ne) true)],[]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩,⟨point p [f,f,g,f] .may (some t),true⟩]]⟩

def rows9 : List (List Row) := [[⟨point p [f,f,g,f] .may,point ret [f,g] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,g,f] .ne,point ret [f,g,f] .star⟩,⟨point p [f,f,g,f,f] .ne,point ret [f,f] .star⟩,⟨point p [f,f,g,f,f] .ne,point ret [f,g] .star⟩,⟨point p [f,f,g,f,f] .ne,point ret [f,g,f] .star⟩],[]]

def saved9 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g,f] .must) false),false⟩,⟨(point p [f,g,f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f] .star,val (point ret [f,f,g,f,f] .star) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_9 : ExclusionChildReplay.rounds true 6 9 8 2 methods rows8 saved8 ExclusionGrowth.source = state9 := by decide

theorem quiescent_9 : ExclusionChildReplay.round true 9 8 2 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

theorem complete_growth_control_equality_9 : ExclusionChildReplay.rounds false 6 9 8 2 methods rows8 saved8 ExclusionGrowth.source = state9 := by decide

def state10 : State := ⟨[[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may,true⟩,⟨point p [g,f] .exact,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,f,f] .exact,false⟩,⟨point p [g,f,f] .star,false⟩,⟨point p [f,f,g,f] .exact,false⟩,⟨point p [f,f,g,f] .star,false⟩,⟨point p [g,g,g,f] .exact,false⟩,⟨point p [g,g,g,f] .star,false⟩,⟨point p [f,f,g,f,f] .exact,false⟩,⟨point p [f,f,g,f,f] .star,false⟩,⟨point p [g,g,g,f,f] .exact,false⟩,⟨point p [g,g,g,f,f] .star,false⟩]],[[(point p [f,f,g,f] .star,val (point ret [f,g] .may) true),(point p [f,f,g,f] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g,f] .star,val (point ret [f,g,f] .ne) true),(point p [f,f,g,f] .star,val (point ret [f,g,f,f] .ne) true),(point p [f,f,g,f,f] .star,val (point ret [f,f] .may) true),(point p [f,f,g,f,f] .star,val (point ret [f,g] .may) true),(point p [f,f,g,f,f] .star,val (point ret [f,g,f] .may) true),(point p [f,f,g,f,f] .star,val (point ret [f,g,f] .ne) true),(point p [f,f,g,f,f] .star,val (point ret [f,g,f,f] .ne) true)],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [f] .may (some t),true⟩,⟨point p [g] .may (some t),true⟩]]⟩

def rows10 : List (List Row) := [[⟨point p [f,g] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,g,f] .star⟩,⟨point p [f,g,f] .ne,point ret [f,f,g,f] .star⟩,⟨point p [f,g,f,f] .ne,point ret [f,f,g,f] .star⟩,⟨point p [f,f] .may,point ret [f,f,g,f,f] .star⟩,⟨point p [f,g] .may,point ret [f,f,g,f,f] .star⟩,⟨point p [f,g,f] .may,point ret [f,f,g,f,f] .star⟩,⟨point p [f,g,f] .ne,point ret [f,f,g,f,f] .star⟩,⟨point p [f,g,f,f] .ne,point ret [f,f,g,f,f] .star⟩],[]]

def saved10 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g,f] .must) false),false⟩,⟨(point p [f,g,f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f] .star,val (point ret [f,f,g,f,f] .star) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_10 : ExclusionChildReplay.rounds true 6 10 9 2 methods rows9 saved9 ExclusionGrowth.source = state10 := by decide

theorem quiescent_10 : ExclusionChildReplay.round true 10 9 2 methods rows9 saved9 state10 = state10 := by decide

theorem handoff_10 : OverwriteReplay.outputRows state10 = rows10 ∧ OverwriteReplay.outputSaved 10 saved9 state10 = saved10 := by decide

theorem complete_growth_control_equality_10 : ExclusionChildReplay.rounds false 6 10 9 2 methods rows9 saved9 ExclusionGrowth.source = state10 := by decide

theorem actual_producer_permission_10 : (state10.offers[2]!).any (fun a => a.ap.mark == some t && ((dropHead [g] a.ap.path).isSome || match dropHead a.ap.path [g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state11 : State := ⟨[[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [] .star,false⟩,⟨point p [] .must,false⟩,⟨point p [f] .must,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .must,false⟩,⟨point p [f,f] .may,true⟩,⟨point p [f,f] .must,false⟩,⟨point p [g,f] .star,false⟩,⟨point p [g,f] .must,false⟩,⟨point p [f,g,f] .may,true⟩,⟨point p [f,g,f] .must,false⟩,⟨point p [g,f,f] .star,false⟩,⟨point p [g,f,f] .must,false⟩]],[[(point p [f,g,f] .must,val (point ret [f,f,g,f] .must) false),(point p [f,g,f,f] .must,val (point ret [f,f,g,f] .must) false),(point p [f,g,f] .must,val (point ret [f,f,g,f,f] .must) false),(point p [f,g,f,f] .must,val (point ret [f,f,g,f,f] .must) false)],[]],[[⟨point p [g] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩],[⟨point p [g] .must (some t),false⟩,⟨point p [f,f] .must (some t),false⟩,⟨point p [f,g,f] .must (some t),false⟩]]⟩

def rows11 : List (List Row) := [[],[]]

def saved11 : List (List Saved) := [[⟨(point p [g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,f] .must,val (point ret [g,f] .must) false),false⟩,⟨(point p [f,f,f] .star,val (point ret [f,f,g] .star) false),true⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,f] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [f,g,f,g] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g,f] .must) false),false⟩,⟨(point p [f,g,f,f] .must,val (point ret [f,f,g] .must) false),false⟩,⟨(point p [f,g,f,f] .must,val (point ret [f,f,g,f] .must) false),false⟩,⟨(point p [f] .star,val (point ret [f,f,g,f,f] .star) false),false⟩,⟨(point p [f,g,f] .must,val (point ret [f,f,g,f,f] .must) false),false⟩,⟨(point p [f,g,f,f] .must,val (point ret [f,f,g,f,f] .must) false),false⟩],[⟨(point p [] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f] .must,val (point ret [g] .must) false),false⟩,⟨(point p [f,f] .star,val (point ret [g] .star) false),false⟩,⟨(point p [g] .must,val (point ret [f,f] .must) false),false⟩,⟨(point p [g,g] .star,val (point ret [f,f] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩,⟨(point p [] .must,val (point ret [g,f,f] .must) false),false⟩,⟨(point p [g,g] .must,val (point ret [f,g,f] .must) false),false⟩,⟨(point p [g,g,g] .star,val (point ret [f,g,f] .star) false),true⟩]]

theorem cold_11 : ExclusionChildReplay.rounds true 6 11 10 2 methods rows10 saved10 ExclusionGrowth.source = state11 := by decide

theorem quiescent_11 : ExclusionChildReplay.round true 11 10 2 methods rows10 saved10 state11 = state11 := by decide

theorem handoff_11 : OverwriteReplay.outputRows state11 = rows11 ∧ OverwriteReplay.outputSaved 11 saved10 state11 = saved11 := by decide

theorem complete_growth_control_equality_11 : ExclusionChildReplay.rounds false 6 11 10 2 methods rows10 saved10 ExclusionGrowth.source = state11 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows11.all List.isEmpty = true ∧ (((state11.offers[2]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state11.offers[2]!).map terminal) = [0] := by decide

end ExclusionGrowth

#print axioms ExclusionGrowth.cold_1

#print axioms ExclusionGrowth.quiescent_1

#print axioms ExclusionGrowth.handoff_1

#print axioms ExclusionGrowth.complete_growth_control_equality_1

#print axioms ExclusionGrowth.cold_2

#print axioms ExclusionGrowth.quiescent_2

#print axioms ExclusionGrowth.handoff_2

#print axioms ExclusionGrowth.complete_growth_control_equality_2

#print axioms ExclusionGrowth.actual_producer_permission_2

#print axioms ExclusionGrowth.cold_3

#print axioms ExclusionGrowth.quiescent_3

#print axioms ExclusionGrowth.handoff_3

#print axioms ExclusionGrowth.complete_growth_control_equality_3

#print axioms ExclusionGrowth.cold_4

#print axioms ExclusionGrowth.quiescent_4

#print axioms ExclusionGrowth.handoff_4

#print axioms ExclusionGrowth.complete_growth_control_equality_4

#print axioms ExclusionGrowth.actual_producer_permission_4

#print axioms ExclusionGrowth.cold_5

#print axioms ExclusionGrowth.quiescent_5

#print axioms ExclusionGrowth.handoff_5

#print axioms ExclusionGrowth.complete_growth_control_equality_5

#print axioms ExclusionGrowth.cold_6

#print axioms ExclusionGrowth.quiescent_6

#print axioms ExclusionGrowth.handoff_6

#print axioms ExclusionGrowth.complete_growth_control_equality_6

#print axioms ExclusionGrowth.actual_producer_permission_6

#print axioms ExclusionGrowth.cold_7

#print axioms ExclusionGrowth.quiescent_7

#print axioms ExclusionGrowth.handoff_7

#print axioms ExclusionGrowth.complete_growth_control_equality_7

#print axioms ExclusionGrowth.cold_8

#print axioms ExclusionGrowth.quiescent_8

#print axioms ExclusionGrowth.handoff_8

#print axioms ExclusionGrowth.complete_growth_control_equality_8

#print axioms ExclusionGrowth.actual_producer_permission_8

#print axioms ExclusionGrowth.cold_9

#print axioms ExclusionGrowth.quiescent_9

#print axioms ExclusionGrowth.handoff_9

#print axioms ExclusionGrowth.complete_growth_control_equality_9

#print axioms ExclusionGrowth.cold_10

#print axioms ExclusionGrowth.quiescent_10

#print axioms ExclusionGrowth.handoff_10

#print axioms ExclusionGrowth.complete_growth_control_equality_10

#print axioms ExclusionGrowth.actual_producer_permission_10

#print axioms ExclusionGrowth.cold_11

#print axioms ExclusionGrowth.quiescent_11

#print axioms ExclusionGrowth.handoff_11

#print axioms ExclusionGrowth.complete_growth_control_equality_11

#print axioms ExclusionGrowth.natural_stop_and_expected_observations
