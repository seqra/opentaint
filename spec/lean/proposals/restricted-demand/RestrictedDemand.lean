/-
  Proposal model. No production behavior changes.
  Original AP demand gates, plus local witnesses for static-erasure gaps.
  The wrapper raw answers are checked by a separate actual AP control.
  No whole-JVM, complete-run or selected repair-policy theorem is claimed.
-/
import ApSpec.AbsDefs

namespace RestrictedDemandDesign
open ApSpec ApSpec.Abs ApSpec.Handoff
set_option autoImplicit false

def emitBatch (ds : List DemandEdge) (a : PFact) : List PFact :=
  ds.filterMap (fun d => emitW d.din a)

def publishBatch (ds : List DemandEdge) (j : PFact) (g : AFact) : List AFact :=
  ds.filterMap (fun d => restrictI j g d)

theorem emitted_has_demand (ds : List DemandEdge) (a j : PFact)
    (h : j ∈ emitBatch ds a) :
    ∃ d, d ∈ ds ∧ emitW d.din a = some j := by
  exact List.mem_filterMap.mp h

theorem published_has_pair (ds : List DemandEdge) (j : PFact) (g out : AFact)
    (h : out ∈ publishBatch ds j g) :
    ∃ d, d ∈ ds ∧ restrictI j g d = some out := by
  exact List.mem_filterMap.mp h

theorem empty_demand_starts_none (a : PFact) : emitBatch [] a = [] := rfl
theorem empty_demand_publishes_none (j : PFact) (g : AFact) :
    publishBatch [] j g = [] := rfl

-- S=1, return=2, argument=3; class accessor=4, named fields=5 and 6.
def staticOut : PFact := ⟨1,[4,5],.star (.set []),.star⟩
def staticIn : PFact := ⟨1,[4,6],.star (.set []),.star⟩
def argument : PFact := ⟨3,[],.star (.set []),.star⟩
def returned : PFact := ⟨2,[],.star (.set []),.star⟩
def retEntry : PFact := ⟨2,[],.any,.star⟩
def getGuide : DemandEdge := ⟨retEntry,some staticOut⟩
def writerGuide : DemandEdge :=
  ⟨⟨1,[4,5],.any,.star⟩,some argument⟩
def actualReturn (t : Mark) : PFact := ⟨2,[],.any,.conc t⟩
def rawStatic : AFact := ⟨staticIn,false⟩
def rawArgument : AFact := ⟨argument,false⟩
def staticCarry : DemandEdge :=
  ⟨⟨1,[],.any,.star⟩,some ⟨1,[],.star (.set []),.star⟩⟩

theorem flow_initial_shared (t : Mark) :
    emitBatch [getGuide] (actualReturn t) = [returned] := rfl

theorem static_callee_answer_is_permitted :
    publishBatch [staticCarry] staticOut rawStatic = [rawStatic] := rfl

theorem wrapper_rejects_changed_static_exit :
    publishBatch [getGuide] returned rawStatic = [] := rfl

theorem wrapper_rejects_nonstatic_exit_even_with_writer_pair :
    publishBatch [getGuide,writerGuide] returned rawArgument = [] := rfl

-- Executable exact missing pairs, not a selected completion algorithm.
def missingStaticPair : DemandEdge := ⟨retEntry,some staticIn⟩
def missingArgumentPair : DemandEdge := ⟨retEntry,some argument⟩

theorem missing_static_pair_permits_answer :
    publishBatch [getGuide,missingStaticPair] returned rawStatic = [rawStatic] := rfl

theorem missing_argument_pair_permits_answer :
    publishBatch [getGuide,writerGuide,missingArgumentPair] returned rawArgument =
      [rawArgument] := rfl

#print axioms emitted_has_demand
#print axioms published_has_pair
#print axioms empty_demand_starts_none
#print axioms empty_demand_publishes_none
#print axioms flow_initial_shared
#print axioms static_callee_answer_is_permitted
#print axioms wrapper_rejects_changed_static_exit
#print axioms wrapper_rejects_nonstatic_exit_even_with_writer_pair
#print axioms missing_static_pair_permits_answer
#print axioms missing_argument_pair_permits_answer
end RestrictedDemandDesign
