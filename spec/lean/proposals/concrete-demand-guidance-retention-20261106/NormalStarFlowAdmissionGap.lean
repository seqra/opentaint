/-
Counterexample only. The existing C2 cell rejects same-head ANY demand with a
supplied NORMAL STAR/FLOW value. A typed NORMAL STAR/FLOW read relation can still
transport its suffix, including an exact full-T caller with empty suffix.
No admission change, termination result or program recovery is selected/proved.
Scope: ordinary bases, counted fields, Empty E, FULL scalar marks, no MUST.
-/
import RestrictedInitialPolicy

namespace NormalStarFlowAdmissionGap
open ApSpec
abbrev Input := RestrictedInitialPolicy.Input
abbrev Demand := RestrictedInitialPolicy.Demand

inductive Layer where | normal | demand
deriving DecidableEq, Repr
structure Actual where
  fact : Input
  layer : Layer
deriving DecidableEq, Repr

def starFlow (base : Nat) (path : List Acc) : Input := ⟨base,path,.star,.flow,false⟩
def anyFlowDemand (base : Nat) (path : List Acc) : Demand := ⟨base,path,.any,.flow⟩

theorem current_C2_same_head_ANY_STAR_FLOW_rejects
    (base : Nat) (field : Acc) (rest : List Acc) :
    RestrictedInitialPolicy.emit (anyFlowDemand base (field :: rest))
      (starFlow base (field :: rest)) = none := by
  have same : dropPrefix (field :: rest) (field :: rest) = some [] :=
    ApSpec.Handoff.RAux.dropPrefix_self' (field :: rest)
  simp [RestrictedInitialPolicy.emit,RestrictedInitialPolicy.selectTemplate,
    RestrictedInitialPolicy.rawTemplate,RestrictedInitialPolicy.validInput,
    RestrictedInitialPolicy.acceptsMark,RestrictedInitialPolicy.shapeEq,
    anyFlowDemand,starFlow,relate,same]

theorem supplied_STAR_FLOW_is_not_MUST (base : Nat) (field : Acc) (rest : List Acc) :
    (starFlow base (field :: rest)).shape = .star ∧
    (starFlow base (field :: rest)).mark = .flow ∧
    (starFlow base (field :: rest)).must = false ∧
    RestrictedInitialPolicy.validInput (starFlow base (field :: rest)) = true := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The transfer type fixes the stored entry/result heads to STAR/FLOW/NORMAL.
Its entry path is nonempty. It does not assert that C2 admitted this entry. -/
structure NormalStarRead where
  sourceBase : Nat
  resultBase : Nat
  field : Acc
deriving DecidableEq, Repr
def entry (read : NormalStarRead) : Actual := ⟨starFlow read.sourceBase [read.field],.normal⟩
def summary (read : NormalStarRead) : Actual := ⟨starFlow read.resultBase [],.normal⟩

def applyRead (read : NormalStarRead) (actual : Actual) : Option Actual :=
  if Nat.beq read.sourceBase actual.fact.base then
    (dropPrefix [read.field] actual.fact.path).map (fun suffix =>
      ⟨{ actual.fact with base := read.resultBase,path := suffix },actual.layer⟩)
  else none

theorem normal_STAR_FLOW_relation_has_nonempty_entry (read : NormalStarRead) :
    (entry read).fact.path = [read.field] ∧
    (entry read).fact.shape = .star ∧ (entry read).fact.mark = .flow ∧
    (summary read).fact.shape = .star ∧ (summary read).fact.mark = .flow ∧
    (entry read).layer = .normal ∧ (summary read).layer = .normal := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Structural suffix law for this NORMAL, non-MUST typed read adapter.
Mark and shape come from the actual; no concrete mark is manufactured. -/
theorem suffix_transport (read : NormalStarRead) (suffix : List Acc)
    (shape : RestrictedInitialPolicy.Shape) (mark : RestrictedInitialPolicy.Mark) :
    applyRead read ⟨⟨read.sourceBase,[read.field] ++ suffix,shape,mark,false⟩,.normal⟩ =
      some ⟨⟨read.resultBase,suffix,shape,mark,false⟩,.normal⟩ := by
  have prefixEquation : dropPrefix [read.field] ([read.field] ++ suffix) = some suffix :=
    CoreAux.dropPrefix_some.mpr rfl
  simp only [applyRead, Nat.beq_refl, if_true, prefixEquation, Option.map_some]

theorem universal_normal_STAR_FLOW_to_ret_STAR_FLOW_suffix
    (read : NormalStarRead) (suffix : List Acc) :
    applyRead read ⟨starFlow read.sourceBase ([read.field] ++ suffix),.normal⟩ =
      some ⟨starFlow read.resultBase suffix,.normal⟩ :=
  suffix_transport read suffix .star .flow

theorem universal_normal_exact_T_suffix (read : NormalStarRead) (suffix : List Acc) (t : Nat) :
    applyRead read ⟨⟨read.sourceBase,[read.field] ++ suffix,.exact,.full t,false⟩,.normal⟩ =
      some ⟨⟨read.resultBase,suffix,.exact,.full t,false⟩,.normal⟩ :=
  suffix_transport read suffix .exact (.full t)

def composeReads (first second : NormalStarRead) (actual : Actual) : Option Actual :=
  (applyRead first actual).bind (applyRead second)

theorem two_getters_transport_every_normal_exact_T_suffix
    (arg gotF ret : Nat) (f g : Acc) (suffix : List Acc) (t : Nat) :
    composeReads ⟨arg,gotF,f⟩ ⟨gotF,ret,g⟩
      ⟨⟨arg,[f,g] ++ suffix,.exact,.full t,false⟩,.normal⟩ =
      some ⟨⟨ret,suffix,.exact,.full t,false⟩,.normal⟩ := by
  unfold composeReads
  have first := universal_normal_exact_T_suffix ⟨arg,gotF,f⟩ ([g] ++ suffix) t
  have second := universal_normal_exact_T_suffix ⟨gotF,ret,g⟩ suffix t
  have firstAtCaller : applyRead ⟨arg,gotF,f⟩
      ⟨⟨arg,[f,g] ++ suffix,.exact,.full t,false⟩,.normal⟩ =
      some ⟨⟨gotF,[g] ++ suffix,.exact,.full t,false⟩,.normal⟩ := by
    simpa only [List.cons_append,List.nil_append] using first
  rw [firstAtCaller]
  exact second

def arg : Nat := 1
def gotF : Nat := 2
def ret : Nat := 3
def f : Acc := 7
def g : Acc := 8
def T : Nat := 11
def getF : NormalStarRead := ⟨arg,gotF,f⟩
def getG : NormalStarRead := ⟨gotF,ret,g⟩

theorem existing_run3_policy_rejects_frozen_getG_cell :
    RestrictedInitialPolicy.DemandStarPolicy.decisionForRun 3 (anyFlowDemand gotF [g])
      (starFlow gotF [g]) = .decided none := by decide

theorem rejected_metadata_still_has_NORMAL_STAR_FLOW_read_image :
    RestrictedInitialPolicy.emit (anyFlowDemand gotF [g]) (starFlow gotF [g]) = none ∧
    applyRead getG ⟨starFlow gotF [g],.normal⟩ = some ⟨starFlow ret [],.normal⟩ := by decide

theorem concrete_empty_suffix_survives_both_normal_getters :
    composeReads getF getG ⟨⟨arg,[f,g],.exact,.full T,false⟩,.normal⟩ =
      some ⟨⟨ret,[],.exact,.full T,false⟩,.normal⟩ := by decide

theorem a_different_first_field_is_not_transferred :
    applyRead getG ⟨⟨gotF,[f],.exact,.full T,false⟩,.normal⟩ = none := by decide

def witness : Bool :=
  decide (RestrictedInitialPolicy.emit (anyFlowDemand gotF [g]) (starFlow gotF [g]) = none) &&
  decide (composeReads getF getG ⟨⟨arg,[f,g],.exact,.full T,false⟩,.normal⟩ =
    some ⟨⟨ret,[],.exact,.full T,false⟩,.normal⟩)
theorem executable_gap_witness : witness = true := by decide
#eval (if witness then "NORMAL_STAR_FLOW_GAP=true" else "NORMAL_STAR_FLOW_GAP=false")

-- One audit command per theorem.
#print axioms current_C2_same_head_ANY_STAR_FLOW_rejects
#print axioms supplied_STAR_FLOW_is_not_MUST
#print axioms normal_STAR_FLOW_relation_has_nonempty_entry
#print axioms suffix_transport
#print axioms universal_normal_STAR_FLOW_to_ret_STAR_FLOW_suffix
#print axioms universal_normal_exact_T_suffix
#print axioms two_getters_transport_every_normal_exact_T_suffix
#print axioms existing_run3_policy_rejects_frozen_getG_cell
#print axioms rejected_metadata_still_has_NORMAL_STAR_FLOW_read_image
#print axioms concrete_empty_suffix_survives_both_normal_getters
#print axioms a_different_first_field_is_not_transferred
#print axioms executable_gap_witness

end NormalStarFlowAdmissionGap
