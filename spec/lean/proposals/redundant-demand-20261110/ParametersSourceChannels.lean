import Std

/-
Component model for the frozen ParametersUtils source-channel audit.
It is not a demand-retirement predicate or a complete callee interpreter.
The source adapter checks all complete source/cleaner objects. Ordinary AP
transports, C2/C5, CFG cuts and dynamic callees stay outside this component.
-/
namespace ParametersSourceChannels

inductive Family where
  | zero
  | flow
  | marked (mark : Nat)
  deriving DecidableEq, Repr

structure Shape where
  base : Nat
  path : List Nat
  /- Audit encoding: STAR=0, EXACT=1, MAY=2, MUST=3. -/
  tail : Nat
  fieldsExcluded : List Nat := []
  demand : Bool := false
  deriving DecidableEq, Repr

structure Packet where
  family : Family
  shape : Shape
  marksExcluded : List Nat := []
  deriving DecidableEq, Repr

structure SelectedPattern where
  mark : Nat
  shape : Shape
  deriving DecidableEq, Repr

structure SourceDecl where
  site : Nat
  backward : Bool
  leaves : List SelectedPattern
  target : SelectedPattern
  deriving DecidableEq, Repr

/- The packed MarkGate rejects a FLOW input for every concrete premise.
The geometric matcher remains an arbitrary executable function. Its result
cannot rescue a failed concrete mark gate. -/
def selectedGate (required : Nat) (input : Family) : Bool :=
  match input with
  | .marked actual => actual == required
  | .zero => required == 0
  | .flow => false

def selectedTransfer (project : Shape → Shape → Shape → Option Shape)
    (src dst : SelectedPattern) (input : Packet) : List Packet :=
  if selectedGate src.mark input.family then
    match project src.shape dst.shape input.shape with
    | none => []
    | some shape => [{ family := .marked dst.mark, shape := shape }]
  else []

def sourceRun (project : Shape → Shape → Shape → Option Shape)
    (source : SourceDecl) (input : Packet) : List Packet :=
  source.leaves.flatMap fun leaf =>
    if source.backward then selectedTransfer project source.target leaf input
    else selectedTransfer project leaf source.target input

theorem selected_gate_flow (required : Nat) : selectedGate required .flow = false := rfl

theorem selected_transfer_flow_empty (project) (src dst : SelectedPattern)
    (shape : Shape) (mx : List Nat) :
    selectedTransfer project src dst ⟨.flow, shape, mx⟩ = [] := by
  simp [selectedTransfer, selectedGate]

theorem source_run_flow_empty (project) (source : SourceDecl)
    (shape : Shape) (mx : List Nat) :
    sourceRun project source ⟨.flow, shape, mx⟩ = [] := by
  simp [sourceRun, selectedTransfer, selectedGate]

theorem selected_transfer_never_flow (project) (src dst : SelectedPattern)
    (input output : Packet) (h : output ∈ selectedTransfer project src dst input) :
    output.family ≠ .flow := by
  unfold selectedTransfer at h
  split at h
  · split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      subst output
      simp
  · simp at h

theorem source_run_never_flow (project) (source : SourceDecl)
    (input output : Packet) (h : output ∈ sourceRun project source input) :
    output.family ≠ .flow := by
  simp only [sourceRun, List.mem_flatMap] at h
  obtain ⟨leaf, _, h⟩ := h
  split at h
  · exact selected_transfer_never_flow project source.target leaf input output h
  · exact selected_transfer_never_flow project leaf source.target input output h

/- Constant source GEN is independent of nonzero FLOW. In this actual
capture SOURCES stages contain only the ZERO keep, not a nonzero GEN. -/
def zeroGen (target : Packet) (input : Packet) : List Packet :=
  if input.family == .zero then [target] else []

theorem zero_gen_flow_empty (target : Packet) (shape : Shape) (mx : List Nat) :
    zeroGen target ⟨.flow, shape, mx⟩ = [] := by
  simp [zeroGen]

structure FlowPacket where
  shape : Shape
  marksExcluded : List Nat := []
  deriving DecidableEq, Repr

structure SelectedCleaner where
  base : Nat
  mark : Nat
  deriving DecidableEq, Repr

/- Native selected FLOW cleaning changes only mx. The adapter excludes
whole-position cleaners, field cleaner chains, Kill and unselected marks. -/
def cleanSelected (cleaner : SelectedCleaner) (input : FlowPacket) : FlowPacket :=
  if input.shape.base == cleaner.base then
    { input with marksExcluded := (cleaner.mark :: input.marksExcluded).eraseDups }
  else input

theorem selected_cleaner_keeps_shape (cleaner : SelectedCleaner) (input : FlowPacket) :
    (cleanSelected cleaner input).shape = input.shape := by
  simp [cleanSelected]
  split <;> rfl

def cleanChain : List SelectedCleaner → FlowPacket → FlowPacket
  | [], input => input
  | cleaner :: rest, input => cleanChain rest (cleanSelected cleaner input)

theorem ordered_selected_cleaners_keep_shape (cleaners : List SelectedCleaner)
    (input : FlowPacket) : (cleanChain cleaners input).shape = input.shape := by
  induction cleaners generalizing input with
  | nil => rfl
  | cons cleaner rest ih =>
    simp only [cleanChain, ih, selected_cleaner_keeps_shape]

def metadataEffect (run : Nat) (run1 : FlowPacket → List FlowPacket)
    (input : FlowPacket) : List FlowPacket :=
  if run == 1 then run1 input else [input]

theorem later_static_metadata_identity (run : Nat) (h : run ≠ 1)
    (run1 : FlowPacket → List FlowPacket) (input : FlowPacket) :
    metadataEffect run run1 input = [input] := by
  simp [metadataEffect, h]

/- A native type filter removes complete scalar memberships. It does not
rename their paths or change their FLOW family/header. -/
def filterScalar (keep : Bool) (input : FlowPacket) : List FlowPacket :=
  if keep then [input] else []

theorem flow_filter_keeps_shape (keep : Bool) (input output : FlowPacket)
    (h : output ∈ filterScalar keep input) : output.shape = input.shape := by
  cases keep <;> simp [filterScalar] at h
  subst output
  rfl

inductive SideStage where
  | source
  | zeroKeep
  | selectedClean (cleaner : SelectedCleaner)
  | staticMetadata
  | filter (keep : Bool)
  | pass
  deriving DecidableEq, Repr

/- The FLOW projection of selected sources and ZERO keeps is empty by the
theorems above. This executor intentionally excludes ordinary AP copies,
prefix reads/writes, saved summaries, unknown-call transfers and cuts. -/
def sideStep (stage : SideStage) (input : FlowPacket) : List FlowPacket :=
  match stage with
  | .source | .zeroKeep => []
  | .selectedClean cleaner => [cleanSelected cleaner input]
  | .staticMetadata | .pass => [input]
  | .filter keep => filterScalar keep input

theorem side_step_keeps_flow_geometry (stage : SideStage) (input output : FlowPacket)
    (h : output ∈ sideStep stage input) : output.shape = input.shape := by
  cases stage with
  | source => simp [sideStep] at h
  | zeroKeep => simp [sideStep] at h
  | selectedClean cleaner =>
    simp only [sideStep, List.mem_singleton] at h
    subst output
    exact selected_cleaner_keeps_shape cleaner input
  | staticMetadata =>
    exact congrArg FlowPacket.shape (by simpa [sideStep] using h)
  | pass =>
    exact congrArg FlowPacket.shape (by simpa [sideStep] using h)
  | filter keep => exact flow_filter_keeps_shape keep input output h

def sideRun : List SideStage → FlowPacket → List FlowPacket
  | [], input => [input]
  | stage :: rest, input => (sideStep stage input).flatMap (sideRun rest)

theorem side_run_keeps_flow_geometry (stages : List SideStage) (input output : FlowPacket)
    (h : output ∈ sideRun stages input) : output.shape = input.shape := by
  induction stages generalizing input with
  | nil =>
    exact congrArg FlowPacket.shape (by simpa [sideRun] using h)
  | cons stage rest ih =>
    simp only [sideRun, List.mem_flatMap] at h
    obtain ⟨middle, hstep, hrest⟩ := h
    exact (ih middle hrest).trans (side_step_keeps_flow_geometry stage input middle hstep)

theorem side_run_cannot_create_uri_may (stages : List SideStage)
    (input output : FlowPacket) (h : output ∈ sideRun stages input) :
    (output.shape.path = [20] ∧ output.shape.tail = 2) →
      (input.shape.path = [20] ∧ input.shape.tail = 2) := by
  intro huri
  simpa only [side_run_keeps_flow_geometry stages input output h] using huri

end ParametersSourceChannels

#print axioms ParametersSourceChannels.selected_gate_flow
#print axioms ParametersSourceChannels.selected_transfer_flow_empty
#print axioms ParametersSourceChannels.source_run_flow_empty
#print axioms ParametersSourceChannels.selected_transfer_never_flow
#print axioms ParametersSourceChannels.source_run_never_flow
#print axioms ParametersSourceChannels.zero_gen_flow_empty
#print axioms ParametersSourceChannels.selected_cleaner_keeps_shape
#print axioms ParametersSourceChannels.ordered_selected_cleaners_keep_shape
#print axioms ParametersSourceChannels.later_static_metadata_identity
#print axioms ParametersSourceChannels.flow_filter_keeps_shape
#print axioms ParametersSourceChannels.side_step_keeps_flow_geometry
#print axioms ParametersSourceChannels.side_run_keeps_flow_geometry
#print axioms ParametersSourceChannels.side_run_cannot_create_uri_may
