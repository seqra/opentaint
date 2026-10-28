/-
  PROPOSAL CHECK ONLY. No runtime or normative specification change.

  New proposed composition removes mapped ; FLOW, and proposed C2 admission
  removes colors obtained through a FLOW suffix. The witnesses below check
  those decisions directly; the earlier symmetric closure is not used as a
  semantic authority. The fixed complete-program premise is an ordinary
  mark-changing rule: concrete U is required to reverse its output to T.

  Code schema (source/sink models are part of the analyzed program):
    convert(x) has rule CM(x,T) -> AssignMark(return,U), with no x->return FLOW.
    setF(p) { C.f = p; }
    transform() { C.g = convert(C.f); }
    getG() { return C.g; }
    wrap(p) { setF(p); transform(); return getG(); }
    main() { sinkU(wrap(sourceT())); }

  Possible run-1 frozen inventory for wrap:
    W p/FLOW -> C.f/FLOW
    B C.f/T -> C.g/U       (transform, inherited into wrap)
    R C.g/FLOW -> ret/FLOW
  The external sink refines its saved point, not wrap's earlier return.
  A direct static read emits FLOW until its own point needs a concrete mark.

  The finite model proves the local failure mechanism and non-associativity.
  It does NOT prove the full JVM builds exactly that inventory: capture, source
  provider binding, AP tails/limits/E/mx, current point scheduling and C5 are
  explicit production adapters. ZERO/carry cannot manufacture a concrete mark
  from unknown; this file does not model their full engine protocol.
-/
import Init

namespace DemandStorageNext.DirectionalCompositionCheck
set_option autoImplicit false

inductive Mark where
  | t
  | u
  | v
  deriving DecidableEq, Repr

inductive Label where
  | flow
  | mapped (input output : Mark)
  deriving DecidableEq, Repr

/-- The proposed direction: a concrete right premise can refine a FLOW
    left output, but a concrete left output cannot instantiate right FLOW. -/
inductive Directional : Label → Label → Label → Type where
  | flowLeft (right : Label) : Directional .flow right right
  | mapped (a middle d : Mark) :
      Directional (.mapped a middle) (.mapped middle d) (.mapped a d)

theorem noMappedThenFlow {a b : Mark} {result : Label} :
    ¬ Nonempty (Directional (.mapped a b) .flow result) :=
  fun ⟨impossible⟩ => nomatch impossible

def flowThenMapped : Directional .flow (.mapped .t .u) (.mapped .t .u) := .flowLeft _

structure LeftThree (a b c : Label) where
  middle : Label
  result : Label
  first : Directional a b middle
  second : Directional middle c result

structure RightThree (a b c : Label) where
  middle : Label
  result : Label
  first : Directional b c middle
  second : Directional a middle result

theorem flowMappedFlowNoLeft :
    ¬ Nonempty (LeftThree .flow (.mapped .t .u) .flow) := by
  intro ⟨path⟩
  cases path with
  | mk middle result first second =>
      cases first with
      | flowLeft _ => exact noMappedThenFlow ⟨second⟩

theorem flowMappedFlowNoRight :
    ¬ Nonempty (RightThree .flow (.mapped .t .u) .flow) :=
  fun ⟨path⟩ => noMappedThenFlow ⟨path.first⟩

def mappedFlowMappedRight : RightThree (.mapped .t .u) .flow (.mapped .u .v) :=
  ⟨.mapped .u .v,.mapped .t .v,.flowLeft _,.mapped _ _ _⟩

theorem mappedFlowMappedNoLeft :
    ¬ Nonempty (LeftThree (.mapped .t .u) .flow (.mapped .u .v)) :=
  fun ⟨path⟩ => noMappedThenFlow ⟨path.first⟩

theorem proposedJoinIsNotAssociative :
    Nonempty (RightThree (.mapped .t .u) .flow (.mapped .u .v)) ∧
    ¬ Nonempty (LeftThree (.mapped .t .u) .flow (.mapped .u .v)) :=
  ⟨⟨mappedFlowMappedRight⟩,mappedFlowMappedNoLeft⟩

inductive Value where
  | unknown
  | colored (mark : Mark)
  deriving DecidableEq, Repr

/-- Existing AP behavior being preserved in the question: FLOW summaries
    can carry a caller's actual mark; a concrete rule cannot fire from FLOW
    in a restricted run. The latter is not a request or a new query. -/
inductive Apply : Label → Value → Value → Type where
  | flow (value : Value) : Apply .flow value value
  | mapped (a b : Mark) : Apply (.mapped a b) (.colored a) (.colored b)

theorem noConcreteRuleFromFlow {a b : Mark} {result : Value} :
    ¬ Nonempty (Apply (.mapped a b) .unknown result) :=
  fun ⟨impossible⟩ => nomatch impossible

inductive Entry where
  | flow
  | marked (mark : Mark)

/-- A FLOW demand emits shared FLOW. A concrete demand intersects an
    actual marked input; it is not inferred from abstract input. -/
inductive Admit : Entry → Value → Value → Type where
  | shared (actual : Value) : Admit .flow actual .unknown
  | concrete (mark : Mark) : Admit (.marked mark) (.colored mark) (.colored mark)

theorem flowEntryForgetsActualU {start : Value}
    (admitted : Admit .flow (.colored .u) start) : start = .unknown :=
  match admitted with | .shared _ => rfl

/-- Backward body steps: getG, reverse convert(T->U), then setF.
    The mark-changing step is inside the wrapper, so its caller has no
    smaller FLOW summary boundary at which to reinstate actual U. -/
structure BackwardWrapper (start : Value) where
  atG : Value
  atF : Value
  atP : Value
  read : Apply .flow start atG
  convert : Apply (.mapped .u .t) atG atF
  write : Apply .flow atF atP

def markedWrapperWitness : BackwardWrapper (.colored .u) :=
  ⟨.colored .u,.colored .t,.colored .t,.flow _,.mapped _ _,.flow _⟩

theorem noSharedFlowWrapperWitness : ¬ Nonempty (BackwardWrapper .unknown) := by
  intro ⟨path⟩
  cases path with
  | mk atG atF atP read convert write =>
      cases read with
      | flow _ => exact noConcreteRuleFromFlow ⟨convert⟩

theorem onlyFlowReturnDemandMissesWrapper {start : Value}
    (admitted : Admit .flow (.colored .u) start) : ¬ Nonempty (BackwardWrapper start) :=
  (flowEntryForgetsActualU admitted).symm ▸ noSharedFlowWrapperWitness

/-- A plain getter is different: its complete FLOW summary can be applied
    directly to U in its caller. This is why the getter-only example does
    not establish safety for a wrapper containing the converter. -/
def plainGetterPreservesCallerU : Apply .flow (.colored .u) (.colored .u) := .flow _

/-- A same-slot carry is also FLOW-preserving; it cannot satisfy the
    concrete reverse converter after the wrapper starts shared FLOW. -/
theorem carryDoesNotRepairUnknown {carried : Value} (carry : Apply .flow .unknown carried) :
    ¬ Nonempty (Apply (.mapped .u .t) carried (.colored .t)) := by
  cases carry with
  | flow _ => exact noConcreteRuleFromFlow

#print axioms noMappedThenFlow
#print axioms flowThenMapped
#print axioms flowMappedFlowNoLeft
#print axioms flowMappedFlowNoRight
#print axioms mappedFlowMappedRight
#print axioms mappedFlowMappedNoLeft
#print axioms proposedJoinIsNotAssociative
#print axioms noConcreteRuleFromFlow
#print axioms flowEntryForgetsActualU
#print axioms markedWrapperWitness
#print axioms noSharedFlowWrapperWitness
#print axioms onlyFlowReturnDemandMissesWrapper
#print axioms plainGetterPreservesCallerU
#print axioms carryDoesNotRepairUnknown

end DemandStorageNext.DirectionalCompositionCheck
