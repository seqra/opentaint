import Handoff

/- Single-argument neutral-prefix call binding. Bases are explicit and
   never treated as fields. Native call stages and rule effects are not
   reimplemented here. -/
namespace CallLossEvidence
open NonEmptyPolicy DemandProgress RelationalLossHandoff

structure Point where
  base : Nat
  path : Path
  deriving DecidableEq, Repr

structure BasedRule where
  src : Nat
  dst : Nat
  fields : PrefixRule
  deriving DecidableEq, Repr

def bind (actualArgument actualResult : Nat) (formal : BasedRule) : BasedRule :=
  ⟨actualArgument,actualResult,formal.fields⟩

def applyBased (rule : BasedRule) (input : Point) : Option Point :=
  if input.base = rule.src then
    (applyRule rule.fields input.path).map fun path => ⟨rule.dst,path⟩
  else none

def composeBased (first second : BasedRule) : Option BasedRule :=
  if first.dst = second.src then
    (compose first.fields second.fields).map fun fields => ⟨first.src,second.dst,fields⟩
  else none

def reverseBased (rule : BasedRule) : BasedRule :=
  ⟨rule.dst,rule.src,⟨rule.fields.write,rule.fields.read⟩⟩

abbrev CallEvidence := Option (List BasedRule)

def throughCall (before : BasedRule) (argument result : Nat)
    (callee : CallEvidence) : CallEvidence :=
  callee.map fun alternatives =>
    alternatives.filterMap fun r => composeBased before (bind argument result r)

theorem binding_preserves_all_field_information (arg result : Nat) (formal : BasedRule) :
    (bind arg result formal).fields = formal.fields ∧
    (bind arg result formal).src = arg ∧ (bind arg result formal).dst = result := by
  exact ⟨rfl,rfl,rfl⟩

theorem binding_commutes_with_point_application (arg result : Nat)
    (formal : BasedRule) (path : Path) :
    applyBased (bind arg result formal) ⟨arg,path⟩ =
      (applyRule formal.fields path).map (fun suffix => (⟨result,suffix⟩ : Point)) := by
  simp [applyBased,bind]

theorem different_bases_are_not_composed (a b : BasedRule) (separate : a.dst ≠ b.src) :
    composeBased a b = none := by simp [composeBased,separate]

theorem missing_callee_evidence_is_not_an_identity (before : BasedRule) (arg result : Nat) :
    throughCall before arg result none = none := rfl

theorem callee_union_is_preserved_at_the_caller (before : BasedRule) (arg result : Nat)
    (old added : List BasedRule) :
    throughCall before arg result (some (old ++ added)) =
      some (((old.filterMap fun r => composeBased before (bind arg result r))) ++
        (added.filterMap fun r => composeBased before (bind arg result r))) := by
  simp [throughCall,List.filterMap_append]

def a : Nat := 10
def x : Nat := 11
def y : Nat := 12
def callerRet : Nat := 13
def p : Nat := 100
def calleeRet : Nat := 101
def f : Nat := AcyclicMayCycle.f
def g : Nat := AcyclicMayCycle.g
def h : Nat := 3

def beforeCall : BasedRule := ⟨a,x,⟨[h],[]⟩⟩
def getReader : BasedRule := ⟨p,calleeRet,⟨[f,g],[]⟩⟩
def getWriter : BasedRule := ⟨p,calleeRet,⟨[],[f]⟩⟩
def returnBinding : BasedRule := ⟨y,callerRet,⟨[],[]⟩⟩

theorem reader_evidence_crosses_the_call_without_losing_its_guard :
    throughCall beforeCall x y (some [getReader]) =
      some [⟨a,y,⟨[h,f,g],[]⟩⟩] := by decide

theorem ordinary_return_binding_finishes_the_caller_evidence :
    composeBased ⟨a,y,⟨[h,f,g],[]⟩⟩ returnBinding =
      some ⟨a,callerRet,⟨[h,f,g],[]⟩⟩ := by decide

theorem all_callee_alternatives_are_composed :
    throughCall beforeCall x y (some [getReader,getWriter]) =
      some [⟨a,y,⟨[h,f,g],[]⟩⟩,⟨a,y,⟨[h],[f]⟩⟩] := by decide

theorem a_second_call_site_reuses_the_formal_relation_with_its_own_bases :
    throughCall ⟨20,21,⟨[h],[]⟩⟩ 21 22 (some [getReader]) =
      some [⟨20,22,⟨[h,f,g],[]⟩⟩] := by decide

theorem backward_call_uses_the_reverse_bindings_and_order :
    ((composeBased (reverseBased returnBinding) (bind y x (reverseBased getReader))).bind
      (fun carried => composeBased carried (reverseBased beforeCall))) =
        some ⟨callerRet,a,⟨[],[h,f,g]⟩⟩ := by decide

/-- Store the caller prefix and the callee reference, not a destructive
    replacement by the result of today's incomplete evidence lookup. -/
structure DemandCallNode where
  before : BasedRule
  argument : Nat
  result : Nat
  calleeHandle : Nat

structure DemandCallView where
  demand : Bool
  evidence : CallEvidence

def resolveDemandCall (node : DemandCallNode) (repository : Nat → CallEvidence) : DemandCallView :=
  ⟨true, throughCall node.before node.argument node.result (repository node.calleeHandle)⟩

def demandGet : DemandCallNode := ⟨beforeCall,x,y,7⟩

theorem demand_summary_with_complete_evidence_keeps_demand_support :
    (resolveDemandCall demandGet (fun _ => some [getReader])).demand = true ∧
    (resolveDemandCall demandGet (fun _ => some [getReader])).evidence =
      some [⟨a,y,⟨[h,f,g],[]⟩⟩] := by decide

theorem unresolved_callee_does_not_erase_the_stored_caller_relation :
    (resolveDemandCall demandGet (fun _ => none)).evidence = none ∧
    demandGet.before = beforeCall := by decide

theorem the_same_node_can_resolve_after_callee_evidence_arrives :
    (resolveDemandCall demandGet (fun _ => none)).evidence = none ∧
    (resolveDemandCall demandGet (fun _ => some [getReader])).evidence =
      some [⟨a,y,⟨[h,f,g],[]⟩⟩] := by decide

theorem evidence_resolution_never_promotes_the_runtime_layer
    (node : DemandCallNode) (old newer : Nat → CallEvidence) :
    (resolveDemandCall node old).demand = true ∧
    (resolveDemandCall node newer).demand = true := ⟨rfl,rfl⟩

theorem callee_cut_evidence_preserves_the_full_output_chain :
    throughCall beforeCall x y (some [⟨p,calleeRet,⟨[],[f,g]⟩⟩]) =
      some [⟨a,y,⟨[h],[f,g]⟩⟩] := by decide

end CallLossEvidence

#print axioms CallLossEvidence.binding_preserves_all_field_information
#print axioms CallLossEvidence.binding_commutes_with_point_application
#print axioms CallLossEvidence.different_bases_are_not_composed
#print axioms CallLossEvidence.missing_callee_evidence_is_not_an_identity
#print axioms CallLossEvidence.callee_union_is_preserved_at_the_caller
#print axioms CallLossEvidence.reader_evidence_crosses_the_call_without_losing_its_guard
#print axioms CallLossEvidence.ordinary_return_binding_finishes_the_caller_evidence
#print axioms CallLossEvidence.all_callee_alternatives_are_composed
#print axioms CallLossEvidence.a_second_call_site_reuses_the_formal_relation_with_its_own_bases
#print axioms CallLossEvidence.backward_call_uses_the_reverse_bindings_and_order
#print axioms CallLossEvidence.demand_summary_with_complete_evidence_keeps_demand_support
#print axioms CallLossEvidence.unresolved_callee_does_not_erase_the_stored_caller_relation
#print axioms CallLossEvidence.the_same_node_can_resolve_after_callee_evidence_arrives
#print axioms CallLossEvidence.evidence_resolution_never_promotes_the_runtime_layer
#print axioms CallLossEvidence.callee_cut_evidence_preserves_the_full_output_chain
