/-
PROPOSAL ONLY, 2026-10-28. No demand policy is selected by this model.

Local certificate theorem. Every modeled marked output either starts at an
actual marked input and follows FLOW, or has a last residual followed by FLOW.
No-residual reachability therefore suffices for FLOW replay of exports.
Method observations need a separate complete barrier certificate.

Residual is a proof-model classification of frozen rows/operation footprints,
not a runtime support label. The JVM adapter must classify every real step,
preserve scope, AP geometry, layers/exclusions/protection, and include sources,
cleaners, hidden observations and caller-bound seeds. The model does not infer
these obligations from normalized static geometry.
-/
import Init

namespace DemandStorageNext.FlowOnlyCertificate
set_option autoImplicit false

abbrev Node := Nat
abbrev Mark := Nat
abbrev Original := Nat

inductive FlowPath (flow : Node → Node → Type) : Node → Node → Type where
  | refl (atNode : Node) : FlowPath flow atNode atNode
  | step {source middle target : Node} : FlowPath flow source middle →
      flow middle target → FlowPath flow source target

structure FlowCarried (input : Original → Node → Mark → Type)
    (flow : Node → Node → Type) (original : Original) (target : Node) (mark : Mark) where
  source : Node
  actualInput : input original source mark
  suffix : FlowPath flow source target

structure ResidualCarried (residual : Original → Node → Mark → Type)
    (flow : Node → Node → Type) (original : Original) (target : Node) (mark : Mark) where
  source : Node
  opaqueRow : residual original source mark
  suffix : FlowPath flow source target

inductive MarkedTrace (input : Original → Node → Mark → Type)
    (flow : Node → Node → Type) (residual : Original → Node → Mark → Type)
    (original : Original) : Node → Mark → Type where
  | actual {atNode : Node} {mark : Mark} : input original atNode mark →
      MarkedTrace input flow residual original atNode mark
  | throughFlow {source target : Node} {mark : Mark} :
      MarkedTrace input flow residual original source mark → flow source target →
      MarkedTrace input flow residual original target mark
  | lastResidual {atNode : Node} {mark : Mark} : residual original atNode mark →
      MarkedTrace input flow residual original atNode mark

/-- Executable decomposition chooses the last nontransparent operation. -/
def split {input : Original → Node → Mark → Type} {flow : Node → Node → Type}
    {residual : Original → Node → Mark → Type} {original : Original}
    {target : Node} {mark : Mark}
    (trace : MarkedTrace input flow residual original target mark) :
    Sum (FlowCarried input flow original target mark)
      (ResidualCarried residual flow original target mark) :=
  match trace with
  | .actual entered => .inl ⟨_, entered, .refl _⟩
  | .lastResidual frontier => .inr ⟨_, frontier, .refl _⟩
  | .throughFlow before edge => match split before with
    | .inl carried => .inl ⟨carried.source, carried.actualInput, .step carried.suffix edge⟩
    | .inr carried => .inr ⟨carried.source, carried.opaqueRow, .step carried.suffix edge⟩

/-- A negative query certificate may overapproximate geometry/visibility safely.
    It must never omit a real residual-to-target FLOW suffix. -/
abbrev NoResidual (residual : Original → Node → Mark → Type)
    (flow : Node → Node → Type) (original : Original) (target : Node) (mark : Mark) :=
  ∀ source, residual original source mark → FlowPath flow source target → False

def replayFromFlow {input : Original → Node → Mark → Type} {flow : Node → Node → Type}
    {residual : Original → Node → Mark → Type} {original : Original}
    {target : Node} {mark : Mark}
    (certificate : NoResidual residual flow original target mark)
    (trace : MarkedTrace input flow residual original target mark) :
    FlowCarried input flow original target mark :=
  match split trace with
  | .inl carried => carried
  | .inr carried => False.elim (certificate carried.source carried.opaqueRow carried.suffix)

theorem replay_keeps_original_input {input : Original → Node → Mark → Type}
    {flow : Node → Node → Type} {residual : Original → Node → Mark → Type}
    {original : Original} {target : Node} {mark : Mark}
    (certificate : NoResidual residual flow original target mark)
    (trace : MarkedTrace input flow residual original target mark) :
    Nonempty (FlowCarried input flow original target mark) :=
  ⟨replayFromFlow certificate trace⟩

/-- The export theorem says nothing about a dead local sink. This separate
    obligation covers every relevant mark-sensitive observation footprint. -/
abbrev NoBarrier (barrier : Original → Node → Mark → Type)
    (original : Original) (mark : Mark) :=
  ∀ atNode, barrier original atNode mark → False

theorem no_hidden_observation {barrier : Original → Node → Mark → Type}
    {original : Original} {mark : Mark}
    (certificate : NoBarrier barrier original mark) (atNode : Node)
    (observation : barrier original atNode mark) : False := certificate atNode observation

/-- Residual rows whose output is the requested atom are sufficient witnesses;
    their input color need not be enumerated to reject the optimization. -/
def residualRejects {residual : Original → Node → Mark → Type} {flow : Node → Node → Type}
    {original : Original} {target source : Node} {mark : Mark}
    (row : residual original source mark) (suffix : FlowPath flow source target) :
    ResidualCarried residual flow original target mark := ⟨source, row, suffix⟩

#print axioms split
#print axioms replayFromFlow
#print axioms replay_keeps_original_input
#print axioms no_hidden_observation
#print axioms residualRejects

end DemandStorageNext.FlowOnlyCertificate
