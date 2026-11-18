import CleanerRepairTrace
namespace NestedSTAR
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

abbrev Edge := Ap × Value
def p : Nat := 0
def ret : Nat := 1
def f : Nat := 1
def g : Nat := 2
def t : Nat := 7
def ap (base : Nat) (tail : Tail := .star) (path : Path := [])
    (mark : Option Nat := none) (e : List Nat := []) : Ap := ⟨base,path,tail,mark,e,[]⟩
def flowStart : Seed := ⟨ap p,false⟩
def source : Offered := ⟨ap p .exact [g] (some t),false⟩
def backwardOffer : Offered := ⟨ap ret .exact [g] (some t),false⟩

-- The only field assignment is p.f = new Box(). Run-1 must not update
-- a field exclusion, so a root FLOW/STAR result moves to DEMAND.
-- In run-2, a NORMAL root FLOW keeps its actual write exclusion {f},
-- including an EXACT probe before its later STAR normalization.
def write (run1 : Bool) (v : Value) : Option Value :=
  if v.ap.path.isEmpty then
    if v.ap.mark.isNone && (v.ap.tail==.star || v.ap.tail==.exact) then
      some {v with ap:={v.ap with e:=if run1 then [] else v.ap.e++[f]},demand:=v.demand || run1}
    else some v
  else if v.ap.path.head?==some f then none else some v

def moveBase (base : Nat) (v : Value) : Value := {v with ap:={v.ap with base:=base}}
def forwardBody (q : Seed) : List Value :=
  match write true ⟨q.ap,q.demand,false⟩ with
  | none => []
  | some v => [v,moveBase ret v]
def inner1 : List Edge := (forwardBody flowStart).map fun c => (flowStart.ap,c)
def wrapper1 : List Edge := inner1

def handoff (xs : List Edge) : List Row := xs.filterMap fun e =>
  if e.2.demand then some ⟨e.2.ap,e.1⟩ else none

def outerQueries : List Seed := (handoff wrapper1).flatMap fun row =>
  HeadPolicy.emit 2 1 true row.entry backwardOffer

def asInnerOffer (q : Seed) : Offered := ⟨{q.ap with base:=ret},q.demand⟩
def innerQueries (actual : Offered) : List Seed := (handoff inner1).flatMap fun row =>
  HeadPolicy.emit 2 1 true row.entry actual

def backwardBody (q : Seed) : List Value :=
  (write false ⟨{q.ap with base:=p},q.demand,false⟩).toList

-- C5's raw permission is the full legal C2 image. The legal deeper offer
-- backwardOffer witnesses STAR in this image. It does not start a query for
-- the current, different, same-head STAR offer.
def restrictCandidate (q : Seed) (v : Value) (row : Row) : Option Edge :=
  HeadPolicy.restrictOne 2 1 true [backwardOffer] q.ap v row

def inner2 (actual : Offered) : List Edge := (handoff inner1).flatMap fun row =>
  (HeadPolicy.emit 2 1 true row.entry actual).flatMap fun q =>
    (backwardBody q).filterMap fun v => restrictCandidate q v row

def wrapper2 : List Edge := outerQueries.flatMap fun q => inner2 (asInnerOffer q)

theorem run1_publishes_both_demand_relations_without_any_real_cut :
    inner1=[(ap p,⟨ap p,true,false⟩),(ap p,⟨ap ret,true,false⟩)] ∧
    wrapper1=inner1 := by decide +kernel

theorem there_is_no_run1_NORMAL_DATA_provider_to_replay :
    (inner1++wrapper1).all (fun e => e.2.demand)=true := by decide +kernel

theorem outer_run2_starts_the_requested_STAR_FLOW_query :
    outerQueries=[⟨ap ret,false⟩] := by decide +kernel

theorem inner_sees_the_same_head_STAR_offer :
    outerQueries.map asInnerOffer=[⟨ap ret,false⟩] := by decide +kernel

theorem same_head_STAR_rejects_at_every_larger_global_limit (k : Nat) :
    HeadPolicy.emit 2 k true (ap ret) ⟨ap ret,false⟩=[] := by
  simp [HeadPolicy.emit,CarryPolicy.emit,NonEmptyPolicy.emit,emitBase,selector,
    completeFamily,primary,atHead,ap,marksOK]

theorem no_inner_DATA_query_or_reply_is_created :
    innerQueries ⟨ap ret,false⟩=[] ∧ inner2 ⟨ap ret,false⟩=[] := by decide +kernel

theorem outer_has_no_current_backward_DATA_or_next_forward_rows :
    wrapper2=[] ∧ handoff wrapper2=[] := by decide +kernel

theorem even_an_optimistic_precise_forward_source_does_not_restart_the_wrapper :
    ((handoff wrapper2).flatMap fun row => HeadPolicy.emit 3 2 false row.entry source)=[] := by decide +kernel

-- Native-prefix semantics of the actual code: f and g are distinct.
-- The assigned f subtree cannot kill the marked g point.
theorem the_concrete_program_has_a_NORMAL_marked_return :
    (write false ⟨source.ap,false,false⟩).map (moveBase ret)=
      some ⟨ap ret .exact [g] (some t),false,false⟩ := by decide +kernel

theorem no_fact_or_summary_needs_a_cut_for_this_case :
    source.ap.path.length=1 ∧ backwardOffer.ap.path.length=1 ∧
    (inner1++wrapper1).all (fun e => decide (e.1.path.length=0 ∧ e.2.ap.path.length=0))=true := by decide +kernel

-- A direct call sends the concrete g requirement, which the existing
-- run-2 deeper-actual exception already admits.
def normalBackward : Edge := (ap ret,⟨ap p .star [] none [f],false,false⟩)
def direct2 : List Edge := inner2 backwardOffer

theorem direct_run2_can_publish_the_missing_NORMAL_record : direct2=[normalBackward] := by decide +kernel

theorem the_candidate_would_pass_raw_C5_but_is_not_started_for_STAR :
    restrictCandidate ⟨ap ret,false⟩ normalBackward.2 ⟨ap ret,ap p⟩=some normalBackward ∧
    HeadPolicy.emit 2 1 true (ap ret) ⟨ap ret,false⟩=[] := by decide +kernel

-- Ordinary correlated saved application with the strong-write exclusion.
def saved (e : Edge) (actual : Offered) : Option Offered := do
  if !marksOK e.1 actual.ap then none else
  let suffix ← dropHead e.1.path actual.ap.path
  if !admits .star e.1.e suffix || !admits .star e.2.ap.e suffix then none else
  some ⟨{actual.ap with base:=e.2.ap.base,path:=e.2.ap.path++suffix},actual.demand || e.2.demand⟩
def normalForward : Edge := (ap p .star [] none [f],⟨ap ret,false,false⟩)

theorem the_preserving_saved_record_can_carry_g_but_not_overwritten_f :
    saved normalForward source=some ⟨ap ret .exact [g] (some t),false⟩ ∧
    saved normalForward ⟨ap p .exact [f] (some t),false⟩=none := by decide +kernel

-- These terminals keep ZERO identity distinct from source/observation
-- discovery. A ZERO identity has no marked DATA premise to feed the rule.
inductive Control where | zero | target
  deriving DecidableEq

def zeroIdentity (c : Control) : Control := c

theorem ordinary_ZERO_identity_is_not_a_marked_source_or_target :
    zeroIdentity .zero=.zero ∧ zeroIdentity .zero≠.target := by decide +kernel

def hasMarkedRoute : Bool := !wrapper2.isEmpty
def forwardResult : Bool := hasMarkedRoute -- even with an allowed source

theorem the_selected_handoff_stops_without_its_real_observation :
    forwardResult=false ∧ hasMarkedRoute=false := by decide +kernel

-- Quiet absent service remains absent under any uncapped schedule.
-- This models the empty-demand/no-saved-DATA call policy, not a cutoff.
def next (report : Bool) : Bool := report || forwardResult

theorem no_later_empty_handoff_can_recreate_the_missing_route (n : Nat) :
    Nat.rec false (fun _ report => next report) n=false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change next (Nat.rec false (fun _ report => next report) n)=false
      rw [ih]
      simp [next,the_selected_handoff_stops_without_its_real_observation.1]

end NestedSTAR
