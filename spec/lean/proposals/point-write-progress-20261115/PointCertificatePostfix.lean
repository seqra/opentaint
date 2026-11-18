import PointWriteProperties

import TargetZeroKernel

import ExclusionCertificatePostfix

namespace PointPostfix

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay PointWriteReplay

set_option maxRecDepth 16384

set_option maxHeartbeats 80000000

def methods : List PointWriteReplay.Method := [[[PointWriteReplay.Op.call 1,PointWriteReplay.Op.move [] [g]]],[[PointWriteReplay.Op.move [] [f],PointWriteReplay.Op.move [] [f]],[PointWriteReplay.Op.move [f] [],PointWriteReplay.Op.move [f] []]]]

def source : Offered := ⟨point p [f,g] .must (some t),false⟩

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[⟨point p [f] .ne (some t),true⟩,⟨point p [g] .may (some t),true⟩],[⟨point p [] .star,false⟩]],[[(point p [] .star,val (point ret [g] .may) true)],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .ne (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[⟨point p [g] .may,point ret [] .star⟩],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : PointWriteReplay.rounds 6 1 1 3 methods rows0 saved0 PointPostfix.source = state1 := by decide

theorem quiescent_1 : PointWriteReplay.round 1 1 3 methods rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : OverwriteReplay.outputRows state1 = rows1 ∧ OverwriteReplay.outputSaved 1 saved0 state1 = saved1 := by decide

theorem old_complete_state_equality_1 : state1 = ExclusionPostfix.state1 ∧ rows1 = ExclusionPostfix.rows1 ∧ saved1 = ExclusionPostfix.saved1 := by decide

def state2 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩]],[[(point p [g] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[⟨point p [] .may,point ret [g] .star⟩,⟨point p [f] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : PointWriteReplay.rounds 6 2 1 3 methods rows1 saved1 PointPostfix.source = state2 := by decide

theorem quiescent_2 : PointWriteReplay.round 2 1 3 methods rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : OverwriteReplay.outputRows state2 = rows2 ∧ OverwriteReplay.outputSaved 2 saved1 state2 = saved2 := by decide

theorem old_complete_state_equality_2 : state2 = ExclusionPostfix.state2 ∧ rows2 = ExclusionPostfix.rows2 ∧ saved2 = ExclusionPostfix.saved2 := by decide

theorem producer_permission_2 : (state2.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state3 : State := ⟨[[⟨point p [g] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [f,g] .star,false⟩]],[[(point p [f] .star,val (point ret [g] .may) true),(point p [] .star,val (point ret [g,f] .ne) true),(point p [f,g] .star,val (point ret [g] .may) true),(point p [g] .star,val (point ret [g,f] .ne) true)],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true),(point p [g] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g] .may (some t),true⟩],[⟨point p [g,f] .ne (some t),true⟩],[⟨point p [g,f] .ne (some t),true⟩]]⟩

def rows3 : List (List Row) := [[⟨point p [g] .may,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [] .star⟩,⟨point p [g] .may,point ret [f,g] .star⟩,⟨point p [g,f] .ne,point ret [g] .star⟩],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [g] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : PointWriteReplay.rounds 6 3 2 3 methods rows2 saved2 PointPostfix.source = state3 := by decide

theorem quiescent_3 : PointWriteReplay.round 3 2 3 methods rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : OverwriteReplay.outputRows state3 = rows3 ∧ OverwriteReplay.outputSaved 3 saved2 state3 = saved3 := by decide

theorem old_complete_state_equality_3 : state3 = ExclusionPostfix.state3 ∧ rows3 = ExclusionPostfix.rows3 ∧ saved3 = ExclusionPostfix.saved3 := by decide

def state4 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .star,false⟩]],[[(point p [g] .star,val (point ret [f] .may) true),(point p [g,f] .star,val (point ret [] .may) true),(point p [g] .star,val (point ret [f,f] .star) false),(point p [g] .star,val (point ret [f,g] .may) true),(point p [g,f] .star,val (point ret [f] .ne) true),(point p [g,f] .star,val (point ret [g] .may) true)],[(point p [f] .star,val (point ret [f] .may) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f] .star,val (point ret [f,g] .may) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[⟨point p [f] .may,point ret [g] .star⟩,⟨point p [] .may,point ret [g,f] .star⟩,⟨point p [f,g] .may,point ret [g] .star⟩,⟨point p [f] .ne,point ret [g,f] .star⟩,⟨point p [g] .may,point ret [g,f] .star⟩],[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : PointWriteReplay.rounds 6 4 3 3 methods rows3 saved3 PointPostfix.source = state4 := by decide

theorem quiescent_4 : PointWriteReplay.round 4 3 3 methods rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : OverwriteReplay.outputRows state4 = rows4 ∧ OverwriteReplay.outputSaved 4 saved3 state4 = saved4 := by decide

theorem old_complete_state_equality_4 : state4 = ExclusionPostfix.state4 ∧ rows4 = ExclusionPostfix.rows4 ∧ saved4 = ExclusionPostfix.saved4 := by decide

theorem producer_permission_4 : (state4.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state5 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f] .may (some t),true⟩,⟨point p [g,f,f] .ne (some t),true⟩,⟨point p [g,f,f,g] .ne (some t),true⟩],[⟨point p [] .exact,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [g] .exact,false⟩,⟨point p [g] .star,false⟩,⟨point p [f,g] .star,false⟩,⟨point p [f,g] .must,false⟩,⟨point p [g,f] .exact,false⟩,⟨point p [g,f] .star,false⟩]],[[(point p [f] .star,val (point ret [g,f] .may) true),(point p [f] .star,val (point ret [g,f] .ne) true),(point p [f,g] .star,val (point ret [g,f] .ne) true),(point p [f,g] .must,val (point ret [g,f] .ne) true),(point p [] .star,val (point ret [g,f,f] .star) false),(point p [f] .star,val (point ret [g,f,f] .ne) true),(point p [g] .star,val (point ret [g,f,f] .ne) true),(point p [f,g] .star,val (point ret [g,f,f] .ne) true),(point p [g,f] .star,val (point ret [g,f,f] .ne) true)],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g,f] .may (some t),true⟩],[⟨point p [g,f,f] .ne (some t),true⟩,⟨point p [g,f,f,g] .ne (some t),true⟩],[⟨point p [g,f,f] .ne (some t),true⟩,⟨point p [g,f,f,g] .ne (some t),true⟩]]⟩

def rows5 : List (List Row) := [[⟨point p [g,f] .may,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [f] .star⟩,⟨point p [g,f] .ne,point ret [f,g] .star⟩,⟨point p [g,f] .ne,point ret [f,g] .must⟩,⟨point p [g,f,f] .ne,point ret [f] .star⟩,⟨point p [g,f,f] .ne,point ret [g] .star⟩,⟨point p [g,f,f] .ne,point ret [f,g] .star⟩,⟨point p [g,f,f] .ne,point ret [g,f] .star⟩],[]]

def saved5 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : PointWriteReplay.rounds 6 5 4 3 methods rows4 saved4 PointPostfix.source = state5 := by decide

theorem quiescent_5 : PointWriteReplay.round 5 4 3 methods rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : OverwriteReplay.outputRows state5 = rows5 ∧ OverwriteReplay.outputSaved 5 saved4 state5 = saved5 := by decide

theorem old_complete_state_equality_5 : state5 = ExclusionPostfix.state5 ∧ rows5 = ExclusionPostfix.rows5 ∧ saved5 = ExclusionPostfix.saved5 := by decide

def state6 : State := ⟨[[⟨point p [] .may (some t),true⟩],[⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[],[]]

def saved6 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : PointWriteReplay.rounds 6 6 5 3 methods rows5 saved5 PointPostfix.source = state6 := by decide

theorem quiescent_6 : PointWriteReplay.round 6 5 3 methods rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : OverwriteReplay.outputRows state6 = rows6 ∧ OverwriteReplay.outputSaved 6 saved5 state6 = saved6 := by decide

theorem old_complete_state_equality_6 : state6 = ExclusionPostfix.state6 ∧ rows6 = ExclusionPostfix.rows6 ∧ saved6 = ExclusionPostfix.saved6 := by decide

theorem producer_permission_6 : (state6.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state7 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,g,f,f] .ne (some t),true⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f] .ne (some t),true⟩],[⟨point p [g,f,f,g,f,f] .ne (some t),true⟩]]⟩

def rows7 : List (List Row) := [[],[]]

def saved7 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : PointWriteReplay.rounds 6 7 6 3 methods rows6 saved6 PointPostfix.source = state7 := by decide

theorem quiescent_7 : PointWriteReplay.round 7 6 3 methods rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : OverwriteReplay.outputRows state7 = rows7 ∧ OverwriteReplay.outputSaved 7 saved6 state7 = saved7 := by decide

theorem old_complete_state_equality_7 : state7 = ExclusionPostfix.state7 ∧ rows7 = ExclusionPostfix.rows7 ∧ saved7 = ExclusionPostfix.saved7 := by decide

def state8 : State := ⟨[[⟨point p [] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[],[]]

def saved8 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_8 : PointWriteReplay.rounds 6 8 7 3 methods rows7 saved7 PointPostfix.source = state8 := by decide

theorem quiescent_8 : PointWriteReplay.round 8 7 3 methods rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : OverwriteReplay.outputRows state8 = rows8 ∧ OverwriteReplay.outputSaved 8 saved7 state8 = saved8 := by decide

theorem old_complete_state_equality_8 : state8 = ExclusionPostfix.state8 ∧ rows8 = ExclusionPostfix.rows8 ∧ saved8 = ExclusionPostfix.saved8 := by decide

theorem producer_permission_8 : (state8.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state9 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,g,f] .ne (some t),true⟩]]⟩

def rows9 : List (List Row) := [[],[]]

def saved9 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_9 : PointWriteReplay.rounds 6 9 8 3 methods rows8 saved8 PointPostfix.source = state9 := by decide

theorem quiescent_9 : PointWriteReplay.round 9 8 3 methods rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : OverwriteReplay.outputRows state9 = rows9 ∧ OverwriteReplay.outputSaved 9 saved8 state9 = saved9 := by decide

theorem old_complete_state_equality_9 : state9 = ExclusionPostfix.state9 ∧ rows9 = ExclusionPostfix.rows9 ∧ saved9 = ExclusionPostfix.saved9 := by decide

def state10 : State := ⟨[[⟨point p [] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows10 : List (List Row) := [[],[]]

def saved10 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_10 : PointWriteReplay.rounds 6 10 9 3 methods rows9 saved9 PointPostfix.source = state10 := by decide

theorem quiescent_10 : PointWriteReplay.round 10 9 3 methods rows9 saved9 state10 = state10 := by decide

theorem handoff_10 : OverwriteReplay.outputRows state10 = rows10 ∧ OverwriteReplay.outputSaved 10 saved9 state10 = saved10 := by decide

theorem old_complete_state_equality_10 : state10 = ExclusionPostfix.state10 ∧ rows10 = ExclusionPostfix.rows10 ∧ saved10 = ExclusionPostfix.saved10 := by decide

theorem producer_permission_10 : (state10.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state11 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,g,f,f,f] .ne (some t),true⟩]]⟩

def rows11 : List (List Row) := [[],[]]

def saved11 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_11 : PointWriteReplay.rounds 6 11 10 3 methods rows10 saved10 PointPostfix.source = state11 := by decide

theorem quiescent_11 : PointWriteReplay.round 11 10 3 methods rows10 saved10 state11 = state11 := by decide

theorem handoff_11 : OverwriteReplay.outputRows state11 = rows11 ∧ OverwriteReplay.outputSaved 11 saved10 state11 = saved11 := by decide

theorem old_complete_state_equality_11 : state11 = ExclusionPostfix.state11 ∧ rows11 = ExclusionPostfix.rows11 ∧ saved11 = ExclusionPostfix.saved11 := by decide

def state12 : State := ⟨[[⟨point p [] .may (some t),true⟩],[]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows12 : List (List Row) := [[],[]]

def saved12 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_12 : PointWriteReplay.rounds 6 12 11 3 methods rows11 saved11 PointPostfix.source = state12 := by decide

theorem quiescent_12 : PointWriteReplay.round 12 11 3 methods rows11 saved11 state12 = state12 := by decide

theorem handoff_12 : OverwriteReplay.outputRows state12 = rows12 ∧ OverwriteReplay.outputSaved 12 saved11 state12 = saved12 := by decide

theorem old_complete_state_equality_12 : state12 = ExclusionPostfix.state12 ∧ rows12 = ExclusionPostfix.rows12 ∧ saved12 = ExclusionPostfix.saved12 := by decide

theorem producer_permission_12 : (state12.offers[3]!).any (fun a => a.ap.mark == some t && ((dropHead [f,g] a.ap.path).isSome || match dropHead a.ap.path [f,g] with | some rest => admits a.ap.tail a.ap.e rest | none => false)) = true := by decide

def state13 : State := ⟨[[⟨point p [f,g] .must (some t),false⟩,⟨point p [g,f,f,f,g] .must (some t),false⟩,⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,f,g] .must (some t),false⟩],[⟨point p [g,f,f,g,f,f,g,f,f,f,g] .must (some t),false⟩]]⟩

def rows13 : List (List Row) := [[],[]]

def saved13 : List (List Saved) := [[⟨(point p [f,f] .star,val (point ret [g] .star) false),true⟩,⟨(point p [] .star,val (point ret [g,f,f] .star) false),false⟩],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_13 : PointWriteReplay.rounds 6 13 12 3 methods rows12 saved12 PointPostfix.source = state13 := by decide

theorem quiescent_13 : PointWriteReplay.round 13 12 3 methods rows12 saved12 state13 = state13 := by decide

theorem handoff_13 : OverwriteReplay.outputRows state13 = rows13 ∧ OverwriteReplay.outputSaved 13 saved12 state13 = saved13 := by decide

theorem old_complete_state_equality_13 : state13 = ExclusionPostfix.state13 ∧ rows13 = ExclusionPostfix.rows13 ∧ saved13 = ExclusionPostfix.saved13 := by decide

def terminal (a : Offered) : TargetZeroKernel.Summary := TargetZeroKernel.forwardSinkTarget 0 .zero (if a.demand then .demand else .normal) 0

theorem natural_stop_and_expected_observations : rows13.all List.isEmpty = true ∧ (((state13.offers[3]!).map terminal).filter TargetZeroKernel.continuationRelevant) = [] ∧ TargetZeroKernel.collectReports [0] ((state13.offers[3]!).map terminal) = [0] := by decide

end PointPostfix

#print axioms PointPostfix.cold_1

#print axioms PointPostfix.quiescent_1

#print axioms PointPostfix.handoff_1

#print axioms PointPostfix.old_complete_state_equality_1

#print axioms PointPostfix.cold_2

#print axioms PointPostfix.quiescent_2

#print axioms PointPostfix.handoff_2

#print axioms PointPostfix.old_complete_state_equality_2

#print axioms PointPostfix.producer_permission_2

#print axioms PointPostfix.cold_3

#print axioms PointPostfix.quiescent_3

#print axioms PointPostfix.handoff_3

#print axioms PointPostfix.old_complete_state_equality_3

#print axioms PointPostfix.cold_4

#print axioms PointPostfix.quiescent_4

#print axioms PointPostfix.handoff_4

#print axioms PointPostfix.old_complete_state_equality_4

#print axioms PointPostfix.producer_permission_4

#print axioms PointPostfix.cold_5

#print axioms PointPostfix.quiescent_5

#print axioms PointPostfix.handoff_5

#print axioms PointPostfix.old_complete_state_equality_5

#print axioms PointPostfix.cold_6

#print axioms PointPostfix.quiescent_6

#print axioms PointPostfix.handoff_6

#print axioms PointPostfix.old_complete_state_equality_6

#print axioms PointPostfix.producer_permission_6

#print axioms PointPostfix.cold_7

#print axioms PointPostfix.quiescent_7

#print axioms PointPostfix.handoff_7

#print axioms PointPostfix.old_complete_state_equality_7

#print axioms PointPostfix.cold_8

#print axioms PointPostfix.quiescent_8

#print axioms PointPostfix.handoff_8

#print axioms PointPostfix.old_complete_state_equality_8

#print axioms PointPostfix.producer_permission_8

#print axioms PointPostfix.cold_9

#print axioms PointPostfix.quiescent_9

#print axioms PointPostfix.handoff_9

#print axioms PointPostfix.old_complete_state_equality_9

#print axioms PointPostfix.cold_10

#print axioms PointPostfix.quiescent_10

#print axioms PointPostfix.handoff_10

#print axioms PointPostfix.old_complete_state_equality_10

#print axioms PointPostfix.producer_permission_10

#print axioms PointPostfix.cold_11

#print axioms PointPostfix.quiescent_11

#print axioms PointPostfix.handoff_11

#print axioms PointPostfix.old_complete_state_equality_11

#print axioms PointPostfix.cold_12

#print axioms PointPostfix.quiescent_12

#print axioms PointPostfix.handoff_12

#print axioms PointPostfix.old_complete_state_equality_12

#print axioms PointPostfix.producer_permission_12

#print axioms PointPostfix.cold_13

#print axioms PointPostfix.quiescent_13

#print axioms PointPostfix.handoff_13

#print axioms PointPostfix.old_complete_state_equality_13

#print axioms PointPostfix.natural_stop_and_expected_observations
