import TargetZeroKernel

/-!
Selected terminal publication laws plus a historical pre-correction fixture.

The HistoricalPreCorrection namespace records a withdrawn fixture: in F3 at limit 2,
an existing source permission emits path f.g.h/T with a DEMAND image; at limit 4
a missing source permission emits no source image; with the permission the same
path has a NORMAL image. Production must establish these adapter observations using its real AP,
mark, source and field-budget gates. This file does not replace them by length.

A NORMAL helper terminal effect composes with the DEMAND F3 caller input into
anonymous DemandTarget. ZERO-only B4 has no marked backward requirement, so it
cannot accept reverse actual GEN, and creates no source permission. Raising the
budget in F5 does not by itself repair that missing permission. A separately
supplied marked requirement repairs this finite route; no mechanism that creates
that requirement is selected here. The fixture assumed a NORMAL helper terminal
was available after an ANY actual entered its exact-$ demand. The new selected
C2 rule rejects that actual, so this fixture is NOT a required selected route
and proves no need for a backward NormalTarget workaround. InitialEmissionExact
models the correction and the absence of any helper witness on that call path.
The old NORMAL+DEMAND promotion is also reference only: the selected application
guard in SelectedTargetApplication rejects that NormalTarget application.

NORMAL terminal effects publish locally as raw summaries. DEMAND terminal
publication still requires one exact paired C5 row. Root reporting reads the
NORMAL local terminal independently of future-run Target selection.
-/
namespace TargetZeroSourcePermission
open TargetZeroKernel
set_option autoImplicit false
set_option linter.constructorNameAsVariable false

namespace HistoricalPreCorrection

inductive Field where
  | f | g | h
  deriving DecidableEq, Repr

def deepPath : List Field := [.f, .g, .h]

structure SourceImage where
  path : List Field
  mark : Nat
  layer : Layer
  deriving DecidableEq, Repr

def deepImage (layer : Layer) : SourceImage := ⟨deepPath, 1, layer⟩

structure BackwardRequirement where
  path : List Field
  mark : Nat
  deriving DecidableEq, Repr

def suppliedRequirement : BackwardRequirement := ⟨deepPath, 1⟩

/-- Explicit observations from the real AP/source-permission gates are required.
    These premises are not a proof that all deep paths behave this way. -/
structure APGateAdapter where
  forwardImage : Nat → Bool → Option SourceImage
  acceptRequirement : BackwardRequirement → Bool
  f3Demand : forwardImage 2 true = some (deepImage .demand)
  f5WithoutPermission : forwardImage 4 false = none
  f5WithPermission : forwardImage 4 true = some (deepImage .normal)
  acceptsSupplied : acceptRequirement suppliedRequirement = true

/-- One executable finite instance of the adapter observations. The real
    production path/mark/budget implementation is deliberately not modeled. -/
def finiteAPAdapter : APGateAdapter where
  forwardImage := fun budget permission =>
    if permission then some (if budget == 4 then deepImage .normal else deepImage .demand) else none
  acceptRequirement := fun requirement => requirement == suppliedRequirement
  f3Demand := rfl
  f5WithoutPermission := rfl
  f5WithPermission := rfl
  acceptsSupplied := rfl

def helperBinding : Binding := ⟨2, 0, .ap .a, .zero, true⟩
def helperNormalTarget : Summary := layeredTargetSummary 0 (.ap .a) .normal 7

def rootTerminal (adapter : APGateAdapter) (budget : Nat) (permission : Bool) : Option Summary :=
  (adapter.forwardImage budget permission).bind fun image =>
    composeBoundTarget helperBinding image.layer helperNormalTarget

/-- ZERO identity has no marked requirement to apply to the source GEN edge. -/
def acceptedBackwardGen (adapter : APGateAdapter) : Option BackwardRequirement → Bool
  | none => false
  | some requirement => adapter.acceptRequirement requirement

def b4SourceTarget (adapter : APGateAdapter) (requirement : Option BackwardRequirement) : Option Summary :=
  backwardGenEventTarget .actualReverseTransfer ⟨.zero, .ap .a⟩
    (acceptedBackwardGen adapter requirement) false 2 .zero

def b4SourcePermission (adapter : APGateAdapter) (requirement : Option BackwardRequirement) : Bool :=
  acceptedBackwardGen adapter requirement

def f5Report (adapter : APGateAdapter) (requirement : Option BackwardRequirement) : Option Nat :=
  (rootTerminal adapter 4 (b4SourcePermission adapter requirement)).bind (finalReport [2])

theorem f3_normal_helper_becomes_demand_caller (adapter : APGateAdapter) :
    rootTerminal adapter 2 true = some (targetSummary 2 .zero) := by
  simp only [rootTerminal, adapter.f3Demand]
  rfl

theorem zero_only_b4_has_no_gen_hit_or_permission (adapter : APGateAdapter) :
    b4SourceTarget adapter none = none ∧ b4SourcePermission adapter none = false := by
  exact ⟨rfl, rfl⟩

theorem raising_budget_without_backward_requirement_loses_normal_report (adapter : APGateAdapter) :
    f5Report adapter none = none := by
  simp only [f5Report, b4SourcePermission, acceptedBackwardGen, rootTerminal,
    adapter.f5WithoutPermission]
  rfl

theorem supplied_backward_requirement_restores_finite_route (adapter : APGateAdapter) :
    b4SourcePermission adapter (some suppliedRequirement) = true ∧
    b4SourceTarget adapter (some suppliedRequirement) = some (targetSummary 2 .zero) ∧
    f5Report adapter (some suppliedRequirement) = some 7 := by
  simp only [b4SourcePermission, b4SourceTarget, acceptedBackwardGen, adapter.acceptsSupplied,
    f5Report, rootTerminal, adapter.f5WithPermission]
  constructor
  · trivial
  · constructor <;> rfl

end HistoricalPreCorrection

/-- This is paired publication, not an entry/exit union across different rows. -/
def pairedDemandRow (rows : List Demand) (summary : Summary) : Option Demand :=
  rows.find? fun row => c5Accept exactEntry exactExit row summary

def publishTerminal (rows : List Demand) (summary : Summary) : Option Summary :=
  match summary.conclusion with
  | .target (.normalTarget _) => some summary
  | .target .demandTarget => (pairedDemandRow rows summary).map fun _ => summary
  | _ => none

theorem raw_normal_terminal_publication (rows : List Demand) (owner : Nat)
    (p : Premise) (reportId : Nat) :
    publishTerminal rows (layeredTargetSummary owner p .normal reportId) =
      some (layeredTargetSummary owner p .normal reportId) := rfl

/-- Every published DEMAND Target has a computed witness for one complete C5
    row. It cannot borrow Dc from one row and Dp from another. -/
def demandPublicationPairWitness (rows : List Demand) (owner : Nat) (p : Premise)
    (published : publishTerminal rows (targetSummary owner p) = some (targetSummary owner p)) :
    {row : Demand // row ∈ rows ∧ c5Accept exactEntry exactExit row (targetSummary owner p) = true} := by
  change (pairedDemandRow rows (targetSummary owner p)).map (fun _ => targetSummary owner p) =
    some (targetSummary owner p) at published
  cases found : pairedDemandRow rows (targetSummary owner p) with
  | none =>
      simp only [found, Option.map_none] at published
      cases published
  | some row =>
      exact ⟨row, List.mem_of_find?_eq_some found,
        List.find?_some (p := fun (candidate : Demand) =>
          c5Accept exactEntry exactExit candidate (targetSummary owner p)) found⟩

def demandRestrictionWitness (rows : List Demand) (owner : Nat) (p : Premise)
    (published : publishTerminal rows (targetSummary owner p) = some (targetSummary owner p)) :
    {row : Demand // row ∈ rows ∧ c5Restrict exactEntry exactExit row (targetSummary owner p) =
      some (targetSummary owner p)} :=
  let witness := demandPublicationPairWitness rows owner p published
  ⟨witness.val, witness.property.1,
    c5_target_label_preserved exactEntry exactExit witness.val owner p .demandTarget .demand
      witness.property.2⟩

theorem demand_publication_requires_zero_exit_same_pair (rows : List Demand) (owner : Nat)
    (p : Premise)
    (published : publishTerminal rows (targetSummary owner p) = some (targetSummary owner p)) :
    ∃ row ∈ rows, row.exit = .zero ∧ entryIntersects exactEntry row.entry p = true := by
  let witness := demandPublicationPairWitness rows owner p published
  have paired := (c5_accept_target_iff exactEntry exactExit witness.val owner p .demandTarget .demand).mp
    witness.property.2
  exact ⟨witness.val, witness.property.1, paired.2.2, paired.2.1⟩

namespace Controls
open HistoricalPreCorrection

def b4ZeroIdentity : Summary := ⟨2, .zero, .zero, .normal⟩
def b4Guide : Demand := handoffTarget 2 .zero
def f5Guide : Demand := handoff b4ZeroIdentity

theorem historical_zero_only_b4_can_pass_c5_without_any_marked_requirement :
    c5Accept exactEntry exactExit b4Guide b4ZeroIdentity = true ∧
    emittedZero .restricted [f5Guide] 2 .zero = [.zero] ∧
    b4SourcePermission finiteAPAdapter none = false ∧
    f5Report finiteAPAdapter none = none := by decide

theorem historical_abstract_marked_requirement_repairs_the_same_f5_budget :
    f5Report finiteAPAdapter none = none ∧
    f5Report finiteAPAdapter (some suppliedRequirement) = some 7 := by decide

theorem raw_root_report_survives_future_selector :
    publishTerminal [] (layeredTargetSummary 2 .zero .normal 7) =
      some (layeredTargetSummary 2 .zero .normal 7) ∧
    finalReport [2] (layeredTargetSummary 2 .zero .normal 7) = some 7 ∧
    selectedTargetHandoff (layeredTargetSummary 2 .zero .normal 7) = none := by decide

def wrongSplitRows : List Demand := [⟨2, .zero, .ap .a⟩, ⟨2, .ap .a, .zero⟩]
theorem split_rows_cannot_publish_demand_target :
    publishTerminal wrongSplitRows (targetSummary 2 .zero) = none ∧
    publishTerminal [⟨2, .zero, .zero⟩] (targetSummary 2 .zero) =
      some (targetSummary 2 .zero) := by decide

def checks : Bool :=
  decide (rootTerminal finiteAPAdapter 2 true = some (targetSummary 2 .zero)) &&
  decide (rootTerminal finiteAPAdapter 4 false = none) &&
  decide (b4SourceTarget finiteAPAdapter none = none) &&
  decide (f5Report finiteAPAdapter none = none) &&
  decide (f5Report finiteAPAdapter (some suppliedRequirement) = some 7) &&
  decide (publishTerminal wrongSplitRows (targetSummary 2 .zero) = none) &&
  decide (finalReport [2] (layeredTargetSummary 2 .zero .normal 7) = some 7)

theorem checks_pass : checks = true := rfl
end Controls

#print axioms HistoricalPreCorrection.f3_normal_helper_becomes_demand_caller
#print axioms HistoricalPreCorrection.zero_only_b4_has_no_gen_hit_or_permission
#print axioms HistoricalPreCorrection.raising_budget_without_backward_requirement_loses_normal_report
#print axioms HistoricalPreCorrection.supplied_backward_requirement_restores_finite_route
#print axioms raw_normal_terminal_publication
#print axioms demandPublicationPairWitness
#print axioms demandRestrictionWitness
#print axioms demand_publication_requires_zero_exit_same_pair
#print axioms Controls.checks_pass
#eval Controls.checks

end TargetZeroSourcePermission
