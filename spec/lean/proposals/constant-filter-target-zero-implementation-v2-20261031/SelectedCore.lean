import Init

/-! Selected Target control kernel. AP payload/matching and full MethodKey/
PremiseKey equality are adapters. No reference promotion policy is included. -/
namespace SelectedCore
set_option autoImplicit false
set_option linter.constructorNameAsVariable false

inductive Direction where | forward | backward deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr
inductive Atom where | a | b | c deriving DecidableEq, Repr
inductive Premise where
  | zero | ap (a : Atom) | both (a b : Atom)
  deriving DecidableEq, Repr
inductive Target where
  | normalTarget (reportId : Nat) | demandTarget
  deriving DecidableEq, Repr
def Target.layer : Target → Layer
  | .normalTarget _ => .normal | .demandTarget => .demand
def Target.fromLayer : Layer → Nat → Target
  | .normal, id => .normalTarget id | .demand, _ => .demandTarget
inductive Fact where
  | zero | ap (a : Atom) | target (label : Target)
  deriving DecidableEq, Repr
inductive Pattern where
  | zero | ap (a : Atom) | both (a b : Atom) | target
  deriving DecidableEq, Repr
def Fact.pattern : Fact → Pattern
  | .zero => .zero | .ap a => .ap a | .target _ => .target
structure Summary where
  owner : Nat
  premise : Premise
  conclusion : Fact
  layer : Layer
  deriving DecidableEq, Repr
structure Demand where
  owner : Nat
  entry : Pattern
  exit : Premise
  deriving DecidableEq, Repr
def layeredTargetSummary (owner : Nat) (p : Premise) (layer : Layer) (id : Nat := 0) : Summary :=
  ⟨owner, p, .target (Target.fromLayer layer id), layer⟩
def targetSummary (owner : Nat) (p : Premise) : Summary := layeredTargetSummary owner p .demand
def premiseMembers : Premise → List Premise
  | .zero => [.zero] | .ap a => [.ap a] | .both a b => [.ap a,.ap b]
def handoff (s : Summary) : List Demand :=
  (premiseMembers s.premise).map fun member => ⟨s.owner,s.conclusion.pattern,member⟩
def handoffTarget (owner : Nat) (p : Premise) : List Demand := handoff (targetSummary owner p)
def forwardSinkTarget (owner : Nat) (p : Premise) (layer : Layer) (id : Nat := 0) : Summary :=
  layeredTargetSummary owner p layer id

/-- Ordinary finite layer aggregation, used only after a complete binding. -/
def composeLayer : Layer → Layer → Layer
  | .normal, .normal => .normal | _, _ => .demand

def entryIntersects (ordinary : Premise → Premise → Bool) : Pattern → Premise → Bool
  | .target, .zero | .zero, .zero => true
  | .target, _ | .zero, _ => false
  | .ap a, p => ordinary (.ap a) p
  | .both a b, p => ordinary (.both a b) p
def exitIntersect (ordinary : Premise → Atom → Option Atom) : Premise → Fact → Option Fact
  | .zero, .zero => some .zero
  | .zero, .target label => some (.target label)
  | .zero, .ap _ => none
  | .ap a, .ap b => (ordinary (.ap a) b).map Fact.ap
  | .both a b, .ap c => (ordinary (.both a b) c).map Fact.ap
  | _, _ => none
def c5Accept (entryAP : Premise → Premise → Bool) (exitAP : Premise → Atom → Option Atom)
    (d : Demand) (s : Summary) : Bool :=
  (d.owner == s.owner) && entryIntersects entryAP d.entry s.premise &&
    (exitIntersect exitAP d.exit s.conclusion).isSome
def c5Restrict (entryAP : Premise → Premise → Bool) (exitAP : Premise → Atom → Option Atom)
    (d : Demand) (s : Summary) : Option Summary :=
  if (d.owner == s.owner) && entryIntersects entryAP d.entry s.premise then
    (exitIntersect exitAP d.exit s.conclusion).map fun f => {s with conclusion := f}
  else none
theorem target_entry_zero_only (ordinary : Premise → Premise → Bool) (p : Premise) :
    entryIntersects ordinary .target p = true ↔ p = .zero := by cases p <;> simp [entryIntersects]
theorem c5_accept_target_iff (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat) (p : Premise)
    (label : Target) (layer : Layer) :
    c5Accept entryAP exitAP d ⟨owner,p,.target label,layer⟩ = true ↔
      (d.owner == owner) = true ∧ entryIntersects entryAP d.entry p = true ∧ d.exit = .zero := by
  cases d with | mk owner entry exit => cases exit <;> simp [c5Accept, exitIntersect, Bool.and_eq_true]
theorem c5_target_label_preserved (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat) (p : Premise)
    (label : Target) (layer : Layer)
    (accepted : c5Accept entryAP exitAP d ⟨owner,p,.target label,layer⟩ = true) :
    c5Restrict entryAP exitAP d ⟨owner,p,.target label,layer⟩ = some ⟨owner,p,.target label,layer⟩ := by
  obtain ⟨ownerMatch,premiseMatch,zeroExit⟩ := (c5_accept_target_iff _ _ _ _ _ _ _).mp accepted
  simp only [c5Restrict, ownerMatch, premiseMatch, Bool.true_and, ↓reduceIte, zeroExit,
    exitIntersect, Option.map_some]
theorem ordinary_ap_exit_unchanged (ordinary : Premise → Atom → Option Atom) (a b : Atom) :
    exitIntersect ordinary (.ap a) (.ap b) = (ordinary (.ap a) b).map Fact.ap := rfl
def exactEntry (p q : Premise) : Bool := p == q
def exactExit (p : Premise) (a : Atom) : Option Atom := if p == .ap a then some a else none

inductive Phase where | run1 | restricted deriving DecidableEq, Repr
def zeroEntry : Pattern → Bool | .zero | .target => true | _ => false
def zeroAdmit (phase : Phase) (rows : List Demand) (owner : Nat) : Fact → Bool
  | .zero => match phase with
    | .run1 => true
    | .restricted => rows.any fun d => d.owner == owner && zeroEntry d.entry
  | _ => false
def emittedZero (phase : Phase) (rows : List Demand) (owner : Nat) (actual : Fact) : List Fact :=
  if zeroAdmit phase rows owner actual then [.zero] else []
theorem nonzero_has_no_zero_fallback (phase : Phase) (rows : List Demand) (owner : Nat) (a : Atom) :
    emittedZero phase rows owner (.ap a) = [] := rfl
theorem no_restricted_guide_no_zero (owner : Nat) : emittedZero .restricted [] owner .zero = [] := rfl
theorem target_actual_never_initial (phase : Phase) (rows : List Demand) (owner : Nat) (label : Target) :
    emittedZero phase rows owner (.target label) = [] := rfl
theorem discovery_zero (rows : List Demand) (owner : Nat) : emittedZero .run1 rows owner .zero = [.zero] := rfl

def targetGuidanceSelected (s : Summary) : Bool :=
  match s.conclusion with | .target .demandTarget => true | _ => false
def selectedTargetHandoff (s : Summary) : List Demand :=
  if targetGuidanceSelected s then handoff s else []
def selectHandoff (ordinary : Direction → Summary → Bool) (direction : Direction) (s : Summary) : List Demand :=
  match s.conclusion with
  | .target _ => selectedTargetHandoff s
  | _ => if ordinary direction s then handoff s else []
def continuationRelevant (s : Summary) : Bool :=
  match s.conclusion with
  | .target (.normalTarget _) => false | .target .demandTarget => true | _ => s.layer == .demand
theorem normal_not_guidance (owner id : Nat) (p : Premise) :
    selectedTargetHandoff (layeredTargetSummary owner p .normal id) = [] := rfl
theorem demand_guidance (owner : Nat) (p : Premise) :
    selectedTargetHandoff (targetSummary owner p) = handoffTarget owner p := rfl
theorem normal_does_not_continue (owner id : Nat) (p : Premise) :
    continuationRelevant (layeredTargetSummary owner p .normal id) = false := rfl
theorem demand_continues (owner : Nat) (p : Premise) : continuationRelevant (targetSummary owner p) = true := rfl
theorem normal_overrides_generic_selector (ordinary : Direction → Summary → Bool)
    (direction : Direction) (owner id : Nat) (p : Premise) :
    selectHandoff ordinary direction (layeredTargetSummary owner p .normal id) = [] := rfl

def ordinarySelected (direction : Direction) (s : Summary) : Bool :=
  s.layer == .demand || (match s.premise with | .both _ _ => true | _ => false) ||
    (direction == .backward && s.premise == .zero)
theorem normal_backward_zero_ap_guidance (owner : Nat) (a : Atom) :
    selectHandoff ordinarySelected .backward ⟨owner,.zero,.ap a,.normal⟩ = [⟨owner,.ap a,.zero⟩] := rfl
theorem normal_forward_zero_singleton_not_selected (owner : Nat) (a : Atom) :
    selectHandoff ordinarySelected .forward ⟨owner,.zero,.ap a,.normal⟩ = [] := rfl

structure CgControlDelta where
  method : Nat
  original : Premise
  deriving DecidableEq, Repr
/-- Typed control transport. No normal ReportId can enter this delta type. -/
def CgControlDelta.handoff (delta : CgControlDelta) : List Demand := handoffTarget delta.method delta.original
theorem control_delta_full_pair (delta : CgControlDelta) :
    delta.handoff = (premiseMembers delta.original).map (fun member => ⟨delta.method,.target,member⟩) := rfl
theorem zero_control_delta_keeps_zero (method : Nat) :
    (CgControlDelta.mk method .zero).handoff = [⟨method,.target,.zero⟩] := rfl
theorem nd_control_delta_has_both_pairs (method : Nat) (a b : Atom) :
    (CgControlDelta.mk method (.both a b)).handoff = [⟨method,.target,.ap a⟩,⟨method,.target,.ap b⟩] := rfl

structure SinkKey where
  location : Nat
  rule : Nat
  deriving DecidableEq, Repr
def internSink : List SinkKey → SinkKey → Option Nat
  | [], _ => none
  | key :: rest, wanted => if wanted == key then some 0 else (internSink rest wanted).map Nat.succ
def registerSink (catalog : List SinkKey) (key : SinkKey) : Nat × List SinkKey :=
  match internSink catalog key with | some id => (id,catalog) | none => (catalog.length,catalog ++ [key])
def finalReport (roots : List Nat) (s : Summary) : Option Nat :=
  if s.owner ∈ roots then match s.premise,s.conclusion with
    | .zero,.target (.normalTarget id) => some id | _,_ => none
  else none
def dedupReportIds : List Nat → List Nat
  | [] => [] | id :: rest => if id ∈ rest then dedupReportIds rest else id :: dedupReportIds rest
theorem dedup_report_membership (id : Nat) (ids : List Nat) :
    id ∈ dedupReportIds ids ↔ id ∈ ids := by
  induction ids with
  | nil => simp [dedupReportIds]
  | cons head rest ih =>
      by_cases present : head ∈ rest
      · simp [dedupReportIds,present,ih]
        intro same
        simpa [same] using present
      · simp [dedupReportIds,present,ih]
def collectReports (roots : List Nat) (summaries : List Summary) : List Nat :=
  dedupReportIds (summaries.filterMap (finalReport roots))
theorem final_report_iff (roots : List Nat) (s : Summary) (id : Nat) :
    finalReport roots s = some id ↔ s.owner ∈ roots ∧ s.premise = .zero ∧
      s.conclusion = .target (.normalTarget id) := by
  cases s with
  | mk owner premise conclusion layer =>
      by_cases rooted : owner ∈ roots
      · cases premise <;> cases conclusion with
        | zero => simp [finalReport,rooted]
        | ap a => simp [finalReport,rooted]
        | target label => cases label <;> simp [finalReport,rooted]
      · simp [finalReport,rooted]

inductive OriginalFact where | zero | ap (a : Atom) deriving DecidableEq, Repr
structure OriginalEdge where
  forwardFrom : OriginalFact
  forwardTo : OriginalFact
  deriving DecidableEq, Repr
def actualGen : OriginalEdge → Bool | ⟨.zero,.ap _⟩ => true | _ => false
inductive SourceEvent where | actualReverseTransfer | recordReplay deriving DecidableEq, Repr
def backwardGenEventTarget (event : SourceEvent) (edge : OriginalEdge) (accepted : Bool)
    (_downstreamAllowed : Bool) (owner : Nat) (p : Premise) : Option Summary :=
  match event with
  | .recordReplay => none
  | .actualReverseTransfer => if accepted && actualGen edge then some (targetSummary owner p) else none
theorem conditional_source_not_terminal (a b : Atom) (accepted downstream : Bool) (owner : Nat) (p : Premise) :
    backwardGenEventTarget .actualReverseTransfer ⟨.ap a,.ap b⟩ accepted downstream owner p = none := by
  cases accepted <;> rfl
theorem actual_gen_precedes_downstream (a : Atom) (downstream : Bool) (owner : Nat) (p : Premise) :
    backwardGenEventTarget .actualReverseTransfer ⟨.zero,.ap a⟩ true downstream owner p = some (targetSummary owner p) := rfl
theorem record_replay_not_new_gen (edge : OriginalEdge) (accepted downstream : Bool) (owner : Nat) (p : Premise) :
    backwardGenEventTarget .recordReplay edge accepted downstream owner p = none := rfl

/-- NORMAL is raw local terminal publication; DEMAND needs one exact C5 row. -/
def publishTerminal (rows : List Demand) (s : Summary) : Option Summary :=
  match s.conclusion with
  | .target (.normalTarget _) => some s
  | .target .demandTarget =>
      (rows.find? fun d => c5Accept exactEntry exactExit d s).map fun _ => s
  | _ => none
theorem raw_normal_publication (rows : List Demand) (owner id : Nat) (p : Premise) :
    publishTerminal rows (layeredTargetSummary owner p .normal id) = some (layeredTargetSummary owner p .normal id) := rfl

def demandPairWitness (rows : List Demand) (owner : Nat) (p : Premise)
    (published : publishTerminal rows (targetSummary owner p) = some (targetSummary owner p)) :
    {row : Demand // row ∈ rows ∧ c5Restrict exactEntry exactExit row (targetSummary owner p) =
      some (targetSummary owner p)} := by
  change (rows.find? fun d => c5Accept exactEntry exactExit d (targetSummary owner p)).map
    (fun _ => targetSummary owner p) = some (targetSummary owner p) at published
  cases found : rows.find? (fun d => c5Accept exactEntry exactExit d (targetSummary owner p)) with
  | none => simp only [found,Option.map_none] at published; cases published
  | some row =>
      have accepted := List.find?_some (p := fun d => c5Accept exactEntry exactExit d (targetSummary owner p)) found
      exact ⟨row,List.mem_of_find?_eq_some found,c5_target_label_preserved _ _ row owner p .demandTarget .demand accepted⟩

end SelectedCore
