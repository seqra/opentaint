import AuditIntersection
import RootCleanerPolicy
namespace AuditCleanerGetter
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

deriving instance ReflBEq, LawfulBEq for Value

def p : Nat := 0
def ret : Nat := 1
def g : Nat := 1
def h : Nat := 2
abbrev t := AcyclicMayCycle.t
abbrev Edge := Ap × Value

def a (b : Nat) (path : Path) (tail : Tail) (mark : Option Nat := some t) : Ap :=
  ⟨b,path,tail,mark,[],[]⟩
def source : Value := ⟨a p [g,h] .must,false,false⟩
def need : Offered := ⟨a ret [] .may,true⟩

-- This is the selected root-cleaner contract. The FLOW branch is the native
-- selected nonstatic cleaner: mx is changed even on a disjoint field path.
def clean (v : Value) : Option Value :=
  if v.ap.mark.isNone then some {v with ap:={v.ap with mx:=v.ap.mx++[t]}}
  else (UniformRootCleanerPolicy.revisedCleanRoot
    {v with ap:={v.ap with base:=UniformRootCleanerCycle.x}}).map fun w =>
      {w with ap:={w.ap with base:=p}}

def moveValue (back : Bool) (v : Value) : Option Value :=
  (if back then BoundedRefinementPipeline.moveE ret p [] [g] v.ap
   else BoundedRefinementPipeline.moveE p ret [g] [] v.ap).map fun w =>
      {w with demand:=w.demand || v.demand,h:=v.h}

-- Forward has both the unchanged argument result and the returned read.
-- Backward from the return port has only the reversed read then root clean.
def body (back : Bool) (q : Seed) : List Value :=
  let v : Value := ⟨q.ap,q.demand,false⟩
  if back then ((moveValue true v).bind clean).toList
  else match clean v with
    | none => []
    | some w => w :: (moveValue false w).toList

def starts1 : List Seed := [⟨a p [] .star none,false⟩,⟨a p [] .star,true⟩]
def summaries1 : List Edge := starts1.flatMap fun q =>
  (body false q).map fun v => (q.ap,cut 1 v)
def handoff (xs : List Edge) : List Row := xs.filterMap fun e =>
  if e.2.demand then some ⟨e.2.ap,e.1⟩ else none

def queries (run limit : Nat) (back : Bool) (rows : List Row) (actual : Offered) : List Seed :=
  rows.flatMap fun row => HeadPolicy.emit run limit back row.entry actual

def summaries2 : List Edge := (handoff summaries1).flatMap fun row =>
  (HeadPolicy.emit 2 1 true row.entry need).flatMap fun q =>
    (body true q).filterMap fun v =>
      HeadPolicy.restrictOne 2 1 true [need] q.ap (cut 1 v) row

-- Keep the native NORMAL structural companion too, even though the scalar
-- reference's marksMeet rejects it under a concrete Dp. This stronger
-- retained basis still excludes T, so it cannot repair the missing route.
def normalBack : Edge := (a ret [] .star none,
  ⟨{a p [g] .star none with mx:=[t]},false,false⟩)
def all2 : List Edge := summaries2++[normalBack]

def queries3 (limit : Nat) : List Seed :=
  queries 3 limit false (handoff all2) ⟨source.ap,false⟩

-- The return actual is the only marked call output offered in the backward
-- root: a is a local dead after the call, not a root method argument.
theorem cold_source_is_cut_to_nonempty_MAY_in_run1 :
    cut 1 source=⟨a p [g] .ne,true,false⟩ := by decide +kernel

theorem both_run1_marked_outputs_are_retained :
    ((a p [] .star,⟨a ret [] .may,true,true⟩) : Edge)∈summaries1 ∧
    ((a p [] .star,⟨a p [] .may,true,true⟩) : Edge)∈summaries1 := by decide +kernel

theorem run2_selected_complete_family :
    queries 2 1 true (handoff summaries1) need =
      [⟨a ret [] .exact,true⟩,⟨a ret [] .star,true⟩,
       ⟨a ret [] .star none,false⟩] := by decide +kernel

theorem run2_retains_the_precise_marked_guides :
    summaries2=[(a ret [] .exact,⟨a p [g] .exact,true,true⟩),
                (a ret [] .star,⟨a p [g] .star,true,true⟩)] := by decide +kernel

theorem native_FLOW_companion_does_not_add_refinement_demand :
    handoff all2=handoff summaries2 ∧ normalBack.2.demand=false := by decide +kernel

theorem run3_rejects_every_complete_selected_query : queries3 2=[] := by decide +kernel

theorem more_global_room_cannot_make_the_STAR_demand_refine
    (limit : Nat) : queries3 limit=[] := by
  rw [queries3]
  have rows : handoff all2=
      [⟨a p [g] .exact,a ret [] .exact⟩,⟨a p [g] .star,a ret [] .star⟩] := by decide +kernel
  rw [rows]
  simp [queries,
    source,a,p,ret,g,h,HeadPolicy.emit,CarryPolicy.emit,NonEmptyPolicy.emit,
    emitBase,selector,completeFamily,primary,marksOK,dropHead,admits]

-- Optimistic source permission is granted: even with the best possible
-- source offer in run-3, the selected callee admission emits no current data.
def current3 : List Edge := (queries3 2).flatMap fun q =>
  (body false q).map fun v => (q.ap,v)

def nativeSavedAllowsT : Bool :=
  !(normalBack.2.ap.mx.contains t)

theorem missing_return_is_not_a_source_permission_artifact :
    source.demand=false ∧ current3=[] ∧ nativeSavedAllowsT=false := by decide +kernel

-- Concrete program derivation: clear p itself; the distinct known point
-- p.g.h survives and becomes ret.h after the ordinary known-prefix read.
theorem a_real_normal_marked_observation_exists :
    (clean source).bind (moveValue false)=
      some ⟨a ret [h] .must,false,true⟩ := by decide +kernel

theorem the_normalized_structural_provider_cannot_subsume_the_T_route :
    marksMeet normalBack.2.ap (a p [g] .star)=false ∧
    HeadPolicy.emit 3 2 false (a p [g] .star) ⟨source.ap,false⟩=[] := by decide +kernel

-- The ordinary STAR-correlated/MAY-independent application fragment used
-- in this straight-line program. No inside read, alias or ND product occurs.
def bind (edge : Edge) (actual : Offered) : Option Offered := do
  if edge.1.base != actual.ap.base || !marksOK edge.1 actual.ap then none else
  if !marksMeet edge.2.ap actual.ap then none else
  let rest ← dropHead edge.1.path actual.ap.path
  if edge.2.ap.tail==.may then
    some ⟨{edge.2.ap with mark:=actual.ap.mark},true⟩
  else if edge.1.tail==.star && edge.2.ap.tail==.star then
    some ⟨{edge.2.ap with path := edge.2.ap.path ++ rest, tail := actual.ap.tail, mark := actual.ap.mark}, edge.2.demand || actual.demand⟩
  else none

def run1MarkedReturn : Edge :=
  (a p [] .star,⟨a ret [] .may,true,true⟩)
def run2MarkedReturn : Edge :=
  (a ret [] .star,⟨a p [g] .star,true,true⟩)
def saved1 : Edge := (a p [] .star none,
  ⟨{a p [] .star none with mx:=[t]},false,false⟩)
def reverseNormalBack : Edge := (a p [g] .star none,
  ⟨{a ret [] .star none with mx:=[t]},false,false⟩)

theorem run1_call_and_observation_have_a_real_demand_witness :
    bind run1MarkedReturn ⟨(cut 1 source).ap,true⟩=some need := by decide +kernel

theorem backward_renewal_reaches_the_source_region :
    bind run2MarkedReturn need=some ⟨a p [g] .may,true⟩ ∧
    admits .may [] [h]=true := by decide +kernel

theorem neither_retained_NORMAL_structural_route_can_supply_T :
    bind saved1 ⟨source.ap,false⟩=none ∧
    bind reverseNormalBack ⟨source.ap,false⟩=none := by decide +kernel

-- A precise known child point is a semantic witness at the observation.
-- No same-head MUST-cleaner coarsening or nonempty root assertion is used.
theorem the_concrete_child_observation_is_not_the_accepted_cleaner_false_positive :
    source.ap.path=[g,h] ∧ source.ap.path≠[] ∧
    (clean source).bind (moveValue false)=some ⟨a ret [h] .must,false,true⟩ ∧
    admits .may [] [h]=true := by decide +kernel

-- A formal zero/Target controller: run-1 has a candidate, backward permits
-- the source, run-3 obtains no reply and no outgoing Target. With no other
-- data/control work, stopping here loses the concrete observation above.
inductive Result where | candidate | permit | empty
  deriving DecidableEq

def cold : Nat → Result
  | 0 => .candidate
  | 1 => .permit
  | _ => if current3.isEmpty && !nativeSavedAllowsT then .empty else .candidate

theorem every_later_round_is_empty_not_confirmed (n : Nat) : cold (n+2)=.empty := by
  simp [cold,current3,run3_rejects_every_complete_selected_query,nativeSavedAllowsT,normalBack,a,t]

end AuditCleanerGetter
