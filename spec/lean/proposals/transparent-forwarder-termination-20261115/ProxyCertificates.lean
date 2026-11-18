import DirectMachine

namespace ProxyCertificates

open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NormalUniformNE NestedSavedReplayCycle NestedColdMachine

set_option maxRecDepth 8192

set_option maxHeartbeats 16000000

def rows0 : List (List Row) := [[],[]]

def saved0 : List (List Saved) := [[],[]]

def state1 : State := ⟨[[],[⟨point p [] .may (some t),true⟩,⟨point p [f] .ne (some t),true⟩]],[[],[(point p [] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true)]],[[⟨point p [f] .ne (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows1 : List (List Row) := [[],[⟨point p [] .may,point ret [] .star⟩,⟨point p [f] .ne,point ret [] .star⟩]]

def saved1 : List (List Saved) := [[],[]]

theorem cold_1 : DirectOwnerMachine.rounds 3 1 1 rows0 saved0 = state1 := by decide

theorem quiescent_1 : DirectOwnerMachine.round 1 1 rows0 saved0 state1 = state1 := by decide

theorem handoff_1 : outputRows state1 = rows1 ∧ outputSaved 1 saved0 state1 = saved1 := by decide

def state2 : State := ⟨[[],[⟨point p [] .may (some t),true⟩]],[[],[(point p [f] .star,val (point ret [] .may) true),(point p [] .star,val (point ret [f] .ne) true),(point p [f] .star,val (point ret [f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows2 : List (List Row) := [[],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩]]

def saved2 : List (List Saved) := [[],[]]

theorem cold_2 : DirectOwnerMachine.rounds 3 2 1 rows1 saved1 = state2 := by decide

theorem quiescent_2 : DirectOwnerMachine.round 2 1 rows1 saved1 state2 = state2 := by decide

theorem handoff_2 : outputRows state2 = rows2 ∧ outputSaved 2 saved1 state2 = saved2 := by decide

def state3 : State := ⟨[[],[⟨point p [] .may (some t),true⟩,⟨point p [f] .may (some t),true⟩,⟨point p [f,g] .must (some t),false⟩]],[[],[(point p [f] .star,val (point ret [] .may) true),(point p [f] .star,val (point ret [f] .may) true),(point p [f] .star,val (point ret [f] .ne) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f,g] .star,val (point ret [f] .ne) true),(point p [f,g] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows3 : List (List Row) := [[],[⟨point p [] .may,point ret [f] .star⟩,⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f] .ne,point ret [f,g] .star⟩,⟨point p [f,f] .ne,point ret [f,g] .star⟩]]

def saved3 : List (List Saved) := [[],[⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_3 : DirectOwnerMachine.rounds 3 3 2 rows2 saved2 = state3 := by decide

theorem quiescent_3 : DirectOwnerMachine.round 3 2 rows2 saved2 state3 = state3 := by decide

theorem handoff_3 : outputRows state3 = rows3 ∧ outputSaved 3 saved2 state3 = saved3 := by decide

def state4 : State := ⟨[[],[⟨point p [] .may (some t),true⟩]],[[],[(point p [f] .star,val (point ret [f] .may) true),(point p [] .star,val (point ret [f,f] .star) false),(point p [f] .star,val (point ret [f,f] .ne) true),(point p [f] .star,val (point ret [f,g] .may) true),(point p [f,f] .star,val (point ret [f,f] .ne) true)]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows4 : List (List Row) := [[],[⟨point p [f] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f] .star⟩,⟨point p [f,g] .may,point ret [f] .star⟩,⟨point p [f,f] .ne,point ret [f,f] .star⟩]]

def saved4 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_4 : DirectOwnerMachine.rounds 3 4 3 rows3 saved3 = state4 := by decide

theorem quiescent_4 : DirectOwnerMachine.round 4 3 rows3 saved3 state4 = state4 := by decide

theorem handoff_4 : outputRows state4 = rows4 ∧ outputSaved 4 saved3 state4 = saved4 := by decide

def state5 : State := ⟨[[],[⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩]],[[],[(point p [f,f,f] .star,val (point ret [f,f] .ne) true),(point p [f,f,f] .star,val (point ret [f,f,f] .ne) true)]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f] .ne (some t),true⟩],[⟨point p [] .ne (some t),true⟩,⟨point p [f] .ne (some t),true⟩,⟨point p [f,f] .ne (some t),true⟩,⟨point p [f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,f] .ne (some t),true⟩,⟨point p [f,f,f,g] .must (some t),false⟩]]⟩

def rows5 : List (List Row) := [[],[⟨point p [f,f] .ne,point ret [f,f,f] .star⟩,⟨point p [f,f,f] .ne,point ret [f,f,f] .star⟩]]

def saved5 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_5 : DirectOwnerMachine.rounds 3 5 4 rows4 saved4 = state5 := by decide

theorem quiescent_5 : DirectOwnerMachine.round 5 4 rows4 saved4 state5 = state5 := by decide

theorem handoff_5 : outputRows state5 = rows5 ∧ outputSaved 5 saved4 state5 = saved5 := by decide

def state6 : State := ⟨[[],[⟨point p [] .may (some t),true⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows6 : List (List Row) := [[],[]]

def saved6 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_6 : DirectOwnerMachine.rounds 3 6 5 rows5 saved5 = state6 := by decide

theorem quiescent_6 : DirectOwnerMachine.round 6 5 rows5 saved5 state6 = state6 := by decide

theorem handoff_6 : outputRows state6 = rows6 ∧ outputSaved 6 saved5 state6 = saved6 := by decide

def state7 : State := ⟨[[],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f] .ne (some t),true⟩]]⟩

def rows7 : List (List Row) := [[],[]]

def saved7 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_7 : DirectOwnerMachine.rounds 3 7 6 rows6 saved6 = state7 := by decide

theorem quiescent_7 : DirectOwnerMachine.round 7 6 rows6 saved6 state7 = state7 := by decide

theorem handoff_7 : outputRows state7 = rows7 ∧ outputSaved 7 saved6 state7 = saved7 := by decide

def state8 : State := ⟨[[],[⟨point p [] .may (some t),true⟩]],[[],[]],[[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩],[⟨point p [] .may (some t),true⟩]]⟩

def rows8 : List (List Row) := [[],[]]

def saved8 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_8 : DirectOwnerMachine.rounds 3 8 7 rows7 saved7 = state8 := by decide

theorem quiescent_8 : DirectOwnerMachine.round 8 7 rows7 saved7 state8 = state8 := by decide

theorem handoff_8 : outputRows state8 = rows8 ∧ outputSaved 8 saved7 state8 = saved8 := by decide

def state9 : State := ⟨[[],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩]],[[],[]],[[⟨point p [f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩],[⟨point p [f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,g] .must (some t),false⟩],[⟨point p [f,f,f,g] .must (some t),false⟩,⟨point p [f,f,f,f,f,f,f,g] .must (some t),false⟩]]⟩

def rows9 : List (List Row) := [[],[]]

def saved9 : List (List Saved) := [[],[⟨(point p [f,f] .star,val (point ret [] .star) false),true⟩,⟨(point p [] .star,val (point ret [f,f] .star) false),false⟩]]

theorem cold_9 : DirectOwnerMachine.rounds 3 9 8 rows8 saved8 = state9 := by decide

theorem quiescent_9 : DirectOwnerMachine.round 9 8 rows8 saved8 state9 = state9 := by decide

theorem handoff_9 : outputRows state9 = rows9 ∧ outputSaved 9 saved8 state9 = saved9 := by decide

theorem natural_completion_at_run9 : rows9 = [[],[]] ∧
    (state9.offers[3]!).all (fun a => !a.demand) = true ∧
    (state9.offers[3]!).any (fun a => !a.demand && a.ap.mark == some t) = true := by decide

theorem the_real_run7_cut_is_kept_until_refinement :
    (state7.offers[3]!).any (fun a => a.demand && a.ap.tail == .ne) = true := by decide

theorem no_proxy_owned_query_or_frontier_is_created :
    (state9.domains[0]!).isEmpty = true ∧ (state9.current[0]!).isEmpty = true := by decide

end ProxyCertificates

#print axioms ProxyCertificates.cold_1

#print axioms ProxyCertificates.quiescent_1

#print axioms ProxyCertificates.handoff_1

#print axioms ProxyCertificates.cold_2

#print axioms ProxyCertificates.quiescent_2

#print axioms ProxyCertificates.handoff_2

#print axioms ProxyCertificates.cold_3

#print axioms ProxyCertificates.quiescent_3

#print axioms ProxyCertificates.handoff_3

#print axioms ProxyCertificates.cold_4

#print axioms ProxyCertificates.quiescent_4

#print axioms ProxyCertificates.handoff_4

#print axioms ProxyCertificates.cold_5

#print axioms ProxyCertificates.quiescent_5

#print axioms ProxyCertificates.handoff_5

#print axioms ProxyCertificates.cold_6

#print axioms ProxyCertificates.quiescent_6

#print axioms ProxyCertificates.handoff_6

#print axioms ProxyCertificates.cold_7

#print axioms ProxyCertificates.quiescent_7

#print axioms ProxyCertificates.handoff_7

#print axioms ProxyCertificates.cold_8

#print axioms ProxyCertificates.quiescent_8

#print axioms ProxyCertificates.handoff_8

#print axioms ProxyCertificates.cold_9

#print axioms ProxyCertificates.quiescent_9

#print axioms ProxyCertificates.handoff_9

#print axioms ProxyCertificates.natural_completion_at_run9

#print axioms ProxyCertificates.the_real_run7_cut_is_kept_until_refinement

#print axioms ProxyCertificates.no_proxy_owned_query_or_frontier_is_created
