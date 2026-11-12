import Std
namespace ProtectedChildCleanerDemand
/- A closed selected-kernel candidate. It is not a complete native execution
   certificate or a retirement counterexample. The native test decides whether
   the whole driver supplies an additional route. -/
inductive Tail where | exact | star | any deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr
structure Fact where
  path : List Nat
  tail : Tail
  layer : Layer
  guarded : Bool
  deriving DecidableEq, Repr

def child : Nat := 1
def markedField : Nat := 2
def starBefore : Fact := ⟨[child],.star,.demand,false⟩
def selectRootT (f : Fact) : List Fact :=
  if f.path.isEmpty then
    match f.tail with
    | .star => [⟨[],.any,.demand,true⟩]
    | .any => [{f with layer := .demand, guarded := true}]
    | .exact => []
  else [{f with guarded := true}]
def starAfter : Fact := (selectRootT starBefore).headD starBefore
/- The post-cleaner child is disjoint from the exact root cleaner. -/
theorem disjoint_child_is_star : starAfter.tail = .star := by decide
theorem disjoint_child_keeps_demand : starAfter.layer = .demand := by decide
theorem disjoint_child_is_protected : starAfter.guarded = true := by decide
theorem partial_root_uses_selected_repair :
    selectRootT ⟨[],.star,.demand,false⟩ = [⟨[],.any,.demand,true⟩] := by decide

/- Same-head concrete STAR demand + MAY actual gives a provisional exact start. -/
def backwardStart : Fact := ⟨[child],.exact,.demand,false⟩
def backwardsCleaner : Fact := (selectRootT backwardStart).headD backwardStart
def inverseWrite (f : Fact) : Fact :=
  {f with path := f.path.drop 1}
def nextDataExit : Fact := inverseWrite backwardsCleaner

theorem reverse_child_cleaner_keeps_exact : backwardsCleaner.tail = .exact := by decide
theorem inverse_write_yields_exact_root :
    nextDataExit = ⟨[],.exact,.demand,true⟩ := by decide

def c2ExactAtRoot (actual : Fact) : Option Fact :=
  if actual.path.isEmpty then some {actual with path := [],tail := .exact} else none
def savedSourcePoint : Fact := ⟨[markedField],.exact,.normal,false⟩
theorem saved_source_is_present_and_precise :
    savedSourcePoint.path = [markedField] ∧ savedSourcePoint.layer = .normal := by decide
theorem precise_source_does_not_answer_exact_root : c2ExactAtRoot savedSourcePoint = none := by decide

/- The ordinary wrapper's NORMAL FLOW has mx={T}; it is not a T supplier. -/
def flowAdmitsT (excludedT : Bool) : Bool := !excludedT
theorem cleaned_flow_cannot_supply_T : flowAdmitsT true = false := by decide

/- Concrete point semantics of the intended code: root-only cleaning does not
   clean a field below the newly written child. -/
def rootCleanerKeepsPoint (p : List Nat) : Bool := !p.isEmpty
def concreteOutput : List Nat := [child,markedField]
theorem required_point_survives_root_cleaner : rootCleanerKeepsPoint concreteOutput = true := by decide

/- Protection is a subsumption flag. It is not an AP admission permission. -/
theorem protection_does_not_imply_admission :
    nextDataExit.guarded = true ∧ c2ExactAtRoot savedSourcePoint = none := by decide
end ProtectedChildCleanerDemand
#print axioms ProtectedChildCleanerDemand.disjoint_child_is_star
#print axioms ProtectedChildCleanerDemand.disjoint_child_keeps_demand
#print axioms ProtectedChildCleanerDemand.disjoint_child_is_protected
#print axioms ProtectedChildCleanerDemand.partial_root_uses_selected_repair
#print axioms ProtectedChildCleanerDemand.reverse_child_cleaner_keeps_exact
#print axioms ProtectedChildCleanerDemand.inverse_write_yields_exact_root
#print axioms ProtectedChildCleanerDemand.saved_source_is_present_and_precise
#print axioms ProtectedChildCleanerDemand.precise_source_does_not_answer_exact_root
#print axioms ProtectedChildCleanerDemand.cleaned_flow_cannot_supply_T
#print axioms ProtectedChildCleanerDemand.required_point_survives_root_cleaner
#print axioms ProtectedChildCleanerDemand.protection_does_not_imply_admission
