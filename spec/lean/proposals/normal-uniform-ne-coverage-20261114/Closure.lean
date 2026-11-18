import UniformCoverage

/- Complete run-3 return candidates for the required finite owner graphs.
   Both branches and every own-row C2 initial are evaluated. Coverage is
   applied only after ordinary global cuts and paired C5. -/
namespace UniformNEClosure
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE

structure Program where
  readPath : Path
  writePath : Path
  deriving Repr

def oldProgram : Program := ⟨[f,g],[f]⟩
def newProgram : Program := ⟨[f,f],[f,f]⟩

def writerCovered (program : Program) (q : Ap) (c : Value) : Bool :=
  program.writePath == [f] && !c.demand && !c.h &&
    (moveE p ret [] [f] q == some c)

def ownerRun3 (program : Program) (rows : List Row) (a : Offered) : List Edge :=
  rows.flatMap fun row =>
    let commands := plan 3 2 false row a
    let seeds := commands.map Command.seed
    commands.flatMap fun command =>
      [moveE p ret program.readPath [] command.seed.ap,
       moveE p ret [] program.writePath command.seed.ap].filterMap id |>.filterMap fun raw =>
        if raw.ap.path.length ≤ 2 && writerCovered program command.seed.ap raw then none
        else restricted 2 seeds command.seed (cut 2 raw) row

/-- Run-1 NEW outputs: the read gives root MAY, the double write gives
    the retained field-NE head. Both rows keep the same original root. -/
def newRows2 : List Row :=
  [⟨data ret 0 .may,data p 0 .star⟩,
   ⟨data ret 1 .ne,data p 0 .star⟩]

def newRun2 : List Edge :=
  newRows2.flatMap fun row =>
    let commands := plan 2 1 true row actualSink
    let seeds := commands.map Command.seed
    commands.flatMap fun command =>
      [routedMove command ret p [] [f,f],
       routedMove command ret p [f,f] []].filterMap id |>.filterMap fun raw =>
        restricted 1 seeds command.seed (cut 1 raw) row

def newRows3 : List Row := handoff newRun2
def oldRows3 : List Row := BoundedLocalRouting.rows3

def normalWriter : Edge := (data p 0 .star,val (data ret 1 .star))
def rootUniform : Offered := ⟨data p 0 .must (some t),false⟩
def fieldUniform : Offered := ⟨data p 1 .must (some t),false⟩

/-- Existing forward native lanes used by these candidate packets:
    complete uniform premise with covering actual, or ordinary STAR
    writer. This does not change normal/weak reverse MUST policy. -/
def normalApply (edge : Edge) (a : Offered) : Option Offered :=
  if edge.2.demand then none else
  if edge.1.tail == .must && a.ap.tail == .must &&
      (dropHead a.ap.path edge.1.path).isSome then
    some ⟨{edge.2.ap with mark := a.ap.mark},a.demand⟩
  else if edge.1.tail == .star then
    (moveE edge.1.base edge.2.ap.base edge.1.path edge.2.ap.path a.ap).map fun c =>
      ⟨{c.ap with mark := a.ap.mark},a.demand || c.demand⟩
  else none

/-- Existing same-layer MUST canonicalization of caller actual facts.
    NE and all D memberships remain separate. There is no new local rule. -/
def actualCovers (whole child : Offered) : Bool :=
  whole.ap.base == child.ap.base && decide (whole.ap.mark = child.ap.mark) &&
    whole.demand == child.demand && whole.ap.tail == .must && child.ap.tail == .must &&
    (dropHead whole.ap.path child.ap.path).isSome

def canonicalActuals (all : List Offered) : List Offered :=
  (all.filter fun a => !(all.any fun b => decide (a.ap ≠ b.ap) && actualCovers b a)).eraseDups

def replayAll (edges : List Edge) (a : Offered) : List Offered :=
  canonicalActuals (edges.filterMap fun e => (normalApply e a).map bindArgument)

def oldPacket : List Edge := ownerRun3 oldProgram oldRows3 fieldUniform
def newPacket : List Edge := ownerRun3 newProgram newRows3 rootUniform
def oldBasis := (compact true oldPacket).eraseDups
def newBasis := (compact true newPacket).eraseDups

theorem new_run2_derives_all_three_paired_rows :
    newRows3 =
      [⟨data p 1 .ne,data ret 0 .star⟩,
       ⟨data p 1 .ne,data ret 1 .star⟩,
       ⟨data p 0 .may,data ret 1 .star⟩] := by decide

theorem the_raw_new_packet_really_contains_global_cut_demand :
    newPacket.any (fun edge => edge.2.demand) = true := by decide

theorem the_new_complete_packet_has_no_demand_after_uniform_coverage :
    newBasis.any (fun edge => edge.2.demand) = false ∧
    newBasis.isEmpty = false := by decide

theorem the_old_complete_packet_still_has_no_demand :
    oldBasis.any (fun edge => edge.2.demand) = false ∧
    oldBasis.isEmpty = false := by decide

def oldFirst := replayAll (normalWriter :: oldBasis) fieldUniform
def newFirst := replayAll newBasis rootUniform

theorem old_first_call_returns_the_normal_uniform_root :
    oldFirst = [rootUniform] := by decide

theorem new_first_call_returns_the_normal_uniform_root :
    newFirst = [rootUniform] := by decide

theorem the_second_old_offer_adds_no_query_or_summary :
    (compact true (oldPacket ++ ownerRun3 oldProgram oldRows3 rootUniform)).eraseDups =
      oldBasis := by decide

theorem the_second_new_offer_adds_no_query_or_summary :
    (compact true (newPacket ++ ownerRun3 newProgram newRows3 rootUniform)).eraseDups =
      newBasis := by decide

def oldSecond := oldFirst.flatMap (replayAll (normalWriter :: oldBasis))
def newSecond := newFirst.flatMap (replayAll newBasis)

theorem old_and_new_second_calls_reach_the_sink_normally :
    oldSecond = [rootUniform] ∧ newSecond = [rootUniform] := by decide

/-- No D actual reaches the sink; only a persistent NormalTarget is
    produced. There are no other DATA outputs of the void root. -/
def rootDemand (actuals : List Offered) : Bool := actuals.any Offered.demand
def confirmed (actuals : List Offered) : Bool :=
  actuals.any fun a => !a.demand && a.ap.mark == some t && a.ap.tail == .must

theorem complete_run3_handoffs_are_empty_and_findings_are_preserved :
    handoff oldBasis = [] ∧ handoff newBasis = [] ∧
    rootDemand oldSecond = false ∧ rootDemand newSecond = false ∧
    confirmed oldSecond = true ∧ confirmed newSecond = true := by decide

/-- This is a within-run fixed point: second-call admission gives the
    same final basis, and replay gives the same offered actual root. -/
theorem further_two_call_closure_rounds_change_nothing :
    replayAll (normalWriter :: oldBasis) rootUniform = oldFirst ∧
    replayAll newBasis rootUniform = newFirst := by decide

end UniformNEClosure

#print axioms UniformNEClosure.new_run2_derives_all_three_paired_rows
#print axioms UniformNEClosure.the_raw_new_packet_really_contains_global_cut_demand
#print axioms UniformNEClosure.the_new_complete_packet_has_no_demand_after_uniform_coverage
#print axioms UniformNEClosure.the_old_complete_packet_still_has_no_demand
#print axioms UniformNEClosure.old_first_call_returns_the_normal_uniform_root
#print axioms UniformNEClosure.new_first_call_returns_the_normal_uniform_root
#print axioms UniformNEClosure.the_second_old_offer_adds_no_query_or_summary
#print axioms UniformNEClosure.the_second_new_offer_adds_no_query_or_summary
#print axioms UniformNEClosure.old_and_new_second_calls_reach_the_sink_normally
#print axioms UniformNEClosure.complete_run3_handoffs_are_empty_and_findings_are_preserved
#print axioms UniformNEClosure.further_two_call_closure_rounds_change_nothing
