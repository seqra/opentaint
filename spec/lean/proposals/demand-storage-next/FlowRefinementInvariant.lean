/-
  PROPOSAL ONLY. A bounded executable kernel for semantic body reuse.

  This model does NOT change C2's conceptual initial set and does NOT authorize
  a new FLOW initial. A certificate requires an actually admitted FLOW peer
  with exactly the same initial geometry and a supported STAR cell. EXACT,
  MUST and ANY are conservative fallbacks in this first kernel.

  Unlike a final-geometry-only test, the kernel result includes protection
  and observations. Its per-mark classifier covers copies, certified backed
  copies, complete selected kills and unrelated selected operations. Relevant
  generation, mark change, protected survivors, checks and UNKNOWN reject reuse.
  A real adapter must provide a COMPLETE relevant footprint: a summary-only or
  fired-rule-only inventory does not establish it. Generic application and
  next-run guidance/native service remain explicit retained-boundary duties.

  The separate graph model already proves the last-residual decomposition.
  This file adds a local commuting-transfer proof and early-admission gate;
  it does not repeat a graph theorem or assert whole-JVM equivalence.
-/
import Init

namespace DemandStorageNext.FlowRefinementInvariant
set_option autoImplicit false

inductive Mark where
  | t
  | u
  deriving DecidableEq, Repr

def same : Mark → Mark → Bool
  | .t,.t => true
  | .u,.u => true
  | .t,.u => false
  | .u,.t => false

inductive Event where
  | source (mark : Mark)
  | check (mark : Mark)
  deriving DecidableEq, Repr

structure Result where
  value : Option Mark
  protection : Bool
  events : List Event
  deriving DecidableEq, Repr

abbrev Mask := Mark → Bool

def instantiate (mark : Mark) (allowed : Mask) : Result :=
  bif allowed mark then ⟨some mark,false,[]⟩ else ⟨none,false,[]⟩

inductive Op where
  | copy
  | backedCopy
  | killWhole (selected : Mark)
  | cleanBelow (selected : Mark)
  | change (input output : Mark)
  | assignSame (selected : Mark)
  | observe (selected : Mark)
  | gen (output : Mark)
  | unknown
  deriving Repr

def onSelected (selected : Mark) (result : Result) : Bool :=
  match result.value with
  | none => false
  | some actual => same actual selected

def markedStep (op : Op) (result : Result) : Result :=
  match op with
  | .copy | .backedCopy => result
  | .killWhole selected =>
      bif onSelected selected result then ⟨none,false,result.events⟩ else result
  | .cleanBelow selected | .assignSame selected =>
      bif onSelected selected result then { result with protection := true } else result
  | .change input output =>
      bif onSelected input result then { result with value := some output } else result
  | .observe selected =>
      bif onSelected selected result then { result with events := result.events ++ [.check selected] } else result
  | .gen output => ⟨some output,false,result.events ++ [.source output]⟩
  | .unknown => result -- no claim is allowed for this missing-evidence case

/-- A selected FLOW cleaner filters the caller's eventual mark. A concrete
    mark gate cannot fire on shared FLOW. These selected local cells are the
    explicit kernel contract, not a proof of every JVM cleaner shape. -/
def flowStep (op : Op) (allowed : Mask) : Mask :=
  match op with
  | .killWhole selected | .cleanBelow selected => fun actual => allowed actual && !same actual selected
  | .copy => allowed
  | .backedCopy => allowed
  | .change _ _ => allowed
  | .assignSame _ => allowed
  | .observe _ => allowed
  | .gen _ => allowed
  | .unknown => allowed

def replayable (op : Op) (queried : Mark) : Bool :=
  match op with
  | .copy | .backedCopy | .killWhole _ => true
  | .cleanBelow selected | .assignSame selected | .observe selected => !same queried selected
  | .change input _ => !same queried input
  | .gen _ | .unknown => false

def checked (ops : List Op) (queried : Mark) : Bool :=
  match ops with
  | [] => true
  | op :: rest => replayable op queried && checked rest queried

def runMarked (ops : List Op) (state : Result) : Result :=
  match ops with
  | [] => state
  | op :: rest => runMarked rest (markedStep op state)

def runFlow (ops : List Op) (state : Mask) : Mask :=
  match ops with
  | [] => state
  | op :: rest => runFlow rest (flowStep op state)

theorem falseNotTrue (bad : (false : Bool) = true) : False := nomatch bad

theorem andLeft {a b : Bool} (yes : (a && b) = true) : a = true :=
  match a,b,yes with | true,_,_ => rfl

theorem andRight {a b : Bool} (yes : (a && b) = true) : b = true :=
  match a,b,yes with | true,true,_ => rfl

/-- One accepted transfer commutes with caller instantiation, including its
    protection and observation payload. This is stronger than equal geometry. -/
theorem localReplay (op : Op) (queried : Mark) (allowed : Mask)
    (yes : replayable op queried = true) :
    markedStep op (instantiate queried allowed) = instantiate queried (flowStep op allowed) := by
  cases op with
  | copy => rfl
  | backedCopy => rfl
  | gen output => exact False.elim (falseNotTrue yes)
  | unknown => exact False.elim (falseNotTrue yes)
  | killWhole selected =>
      cases queried <;> cases selected <;>
        cases ht : allowed Mark.t <;> cases hu : allowed Mark.u <;>
        (dsimp only [markedStep,flowStep,instantiate,onSelected,same];
           first | (rw [ht]; rfl) | (rw [hu]; rfl))
  | cleanBelow selected =>
      cases queried <;> cases selected <;>
        cases ht : allowed Mark.t <;> cases hu : allowed Mark.u <;>
        first | exact False.elim (falseNotTrue yes) |
          (dsimp only [markedStep,flowStep,instantiate,onSelected,same];
           first | (rw [ht]; rfl) | (rw [hu]; rfl))
  | assignSame selected =>
      cases queried <;> cases selected <;>
        cases ht : allowed Mark.t <;> cases hu : allowed Mark.u <;>
        first | exact False.elim (falseNotTrue yes) |
          (dsimp only [markedStep,flowStep,instantiate,onSelected,same];
           first | (rw [ht]; rfl) | (rw [hu]; rfl))
  | observe selected =>
      cases queried <;> cases selected <;>
        cases ht : allowed Mark.t <;> cases hu : allowed Mark.u <;>
        first | exact False.elim (falseNotTrue yes) |
          (dsimp only [markedStep,flowStep,instantiate,onSelected,same];
           first | (rw [ht]; rfl) | (rw [hu]; rfl))
  | change input output =>
      cases queried <;> cases input <;>
        cases ht : allowed Mark.t <;> cases hu : allowed Mark.u <;>
        first | exact False.elim (falseNotTrue yes) |
          (dsimp only [markedStep,flowStep,instantiate,onSelected,same];
           first | (rw [ht]; rfl) | (rw [hu]; rfl))

/-- Constructive whole-kernel replay follows the actual operation order.
    No summary-application reassociation is used. -/
theorem replayChecked (ops : List Op) (queried : Mark) (allowed : Mask)
    (yes : checked ops queried = true) :
    runMarked ops (instantiate queried allowed) = instantiate queried (runFlow ops allowed) :=
  match ops with
  | [] => rfl
  | op :: rest =>
      let head := andLeft yes
      let tail := andRight yes
      (congrArg (runMarked rest) (localReplay op queried allowed head)).trans
        (replayChecked rest queried (flowStep op allowed) tail)

inductive Tail where
  | star
  | any
  | exact
  | must
  deriving DecidableEq, Repr

structure Geometry where
  base : Nat
  path : List Nat
  tail : Tail
  fieldExclusion : List Nat
  deriving DecidableEq, Repr

def supportedPeer (geometry : Geometry) : Bool :=
  match geometry.tail with | .star => true | .any => false | .exact => false | .must => false

/-- `admitted` is supplied by ordinary current-run C2, never manufactured by
    this certificate. A backedCopy must already own its retained FLOW reference
    and approved geometry/layer/E/mx/protection cell in the production adapter. -/
structure ReuseCertificate (admitted : List Geometry) (initial : Geometry)
    (ops : List Op) (queried : Mark) where
  peer : Geometry
  legalAndAdmitted : peer ∈ admitted
  sameGeometry : peer = initial
  supported : supportedPeer initial = true
  noRelevantResidual : checked ops queried = true

/-- Completeness includes every relevant returned effect AND observation of
    this omitted marked run. A log of only fired rules or W/B/R rows is not an
    implementation of this contract. Unknown metadata must reject certificate
    construction rather than hide an operation from the kernel. -/
structure CompleteFootprint (Actual : Type) (ops : List Op) (queried : Mark) (allowed : Mask) where
  markedRun : Actual
  observe : Actual → Result
  complete : observe markedRun = runMarked ops (instantiate queried allowed)

/-- Either the generic body with retained C5 or an applicable normal record
    can implement these two service ports. No new query permission is granted. -/
structure RetainedBoundaryService (Application Guidance : Result → Type)
    (ops : List Op) (queried : Mark) (allowed : Mask) where
  apply : Application (instantiate queried (runFlow ops allowed))
  handoff : Guidance (instantiate queried (runFlow ops allowed))

structure Served (Application Guidance : Result → Type) (result : Result) where
  apply : Application result
  handoff : Guidance result

/-- This is boundary service for the omitted marked work, NOT equality of
    old/new initial queues or a whole-JVM footprint-completeness theorem. -/
def serveOmittedMarked {Actual : Type} {admitted : List Geometry} {initial : Geometry}
    {ops : List Op} {queried : Mark} {allowed : Mask} {Application Guidance : Result → Type}
    (certificate : ReuseCertificate admitted initial ops queried)
    (footprint : CompleteFootprint Actual ops queried allowed)
    (service : RetainedBoundaryService Application Guidance ops queried allowed) :
    Served Application Guidance (footprint.observe footprint.markedRun) :=
  let sameResult := footprint.complete.trans (replayChecked ops queried allowed certificate.noRelevantResidual)
  ⟨sameResult.symm ▸ service.apply,sameResult.symm ▸ service.handoff⟩

theorem reuseNeverCreatesFlowPeer {admitted : List Geometry} {initial : Geometry}
    {ops : List Op} {queried : Mark} (certificate : ReuseCertificate admitted initial ops queried) :
    initial ∈ admitted := certificate.sameGeometry ▸ certificate.legalAndAdmitted

theorem noPeerNoReuse {initial : Geometry} {ops : List Op} {queried : Mark} :
    ¬ Nonempty (ReuseCertificate [] initial ops queried) :=
  fun ⟨certificate⟩ => nomatch certificate.legalAndAdmitted

def allMarks : Mask := fun _ => true
def starInput : Geometry := ⟨0,[],.star,[]⟩
def echo : List Op := [.copy,.backedCopy,.copy]

def getterCertificate : ReuseCertificate [starInput] starInput [.copy] .t :=
  ⟨starInput,.head _,rfl,rfl,rfl⟩

def echoCertificate : ReuseCertificate [starInput] starInput echo .t :=
  ⟨starInput,.head _,rfl,rfl,rfl⟩

theorem echoReplaysCallerT :
    runMarked echo (instantiate .t allMarks) = ⟨some .t,false,[]⟩ ∧
    instantiate .t (runFlow echo allMarks) = ⟨some .t,false,[]⟩ := ⟨rfl,rfl⟩

theorem genBlocksReuse : checked [.gen .t,.copy] .t = false ∧
    runMarked [.gen .t,.copy] (instantiate .t allMarks) ≠
      instantiate .t (runFlow [.gen .t,.copy] allMarks) :=
  ⟨rfl,(fun impossible => nomatch impossible)⟩

theorem crossMarkBlocksReuse : checked [.change .t .u,.copy] .t = false ∧
    runMarked [.change .t .u,.copy] (instantiate .t allMarks) ≠
      instantiate .t (runFlow [.change .t .u,.copy] allMarks) :=
  ⟨rfl,(fun impossible => nomatch impossible)⟩

theorem protectedSameBlocksReuse : checked [.assignSame .t,.copy] .t = false ∧
    runMarked [.assignSame .t,.copy] (instantiate .t allMarks) ≠
      instantiate .t (runFlow [.assignSame .t,.copy] allMarks) :=
  ⟨rfl,(fun impossible => nomatch impossible)⟩

theorem hiddenObservationBlocksReuse : checked [.observe .t,.copy] .t = false ∧
    runMarked [.observe .t,.copy] (instantiate .t allMarks) ≠
      instantiate .t (runFlow [.observe .t,.copy] allMarks) :=
  ⟨rfl,(fun impossible => nomatch impossible)⟩

theorem backedCopyDoesNotHideEarlierSource :
    replayable .backedCopy .t = true ∧ checked [.gen .t,.backedCopy,.copy] .t = false := ⟨rfl,rfl⟩

theorem selectedUCanReplayT : checked [.killWhole .u,.copy] .t = true ∧
    runMarked [.killWhole .u,.copy] (instantiate .t allMarks) =
      instantiate .t (runFlow [.killWhole .u,.copy] allMarks) :=
  ⟨rfl,replayChecked _ _ _ rfl⟩

theorem completeTKillReplaysEmpty : checked [.killWhole .t] .t = true ∧
    runMarked [.killWhole .t] (instantiate .t allMarks) = ⟨none,false,[]⟩ ∧
    instantiate .t (runFlow [.killWhole .t] allMarks) = ⟨none,false,[]⟩ := ⟨rfl,rfl,rfl⟩

theorem belowTCleanerRetainsProtectedRoot : checked [.cleanBelow .t] .t = false ∧
    runMarked [.cleanBelow .t] (instantiate .t allMarks) = ⟨some .t,true,[]⟩ ∧
    instantiate .t (runFlow [.cleanBelow .t] allMarks) = ⟨none,false,[]⟩ := ⟨rfl,rfl,rfl⟩

theorem unrelatedCheckIsMarkSpecific : checked [.observe .u,.copy] .t = true ∧
    checked [.observe .u,.copy] .u = false := ⟨rfl,rfl⟩

theorem unknownAlwaysFallsBack : checked [.unknown] .t = false ∧ checked [.unknown] .u = false := ⟨rfl,rfl⟩

theorem exactMustAnyFallBack :
    supportedPeer { starInput with tail := .exact } = false ∧
    supportedPeer { starInput with tail := .must } = false ∧
    supportedPeer { starInput with tail := .any } = false := ⟨rfl,rfl,rfl⟩

#print axioms localReplay
#print axioms replayChecked
#print axioms serveOmittedMarked
#print axioms reuseNeverCreatesFlowPeer
#print axioms noPeerNoReuse
#print axioms getterCertificate
#print axioms echoCertificate
#print axioms echoReplaysCallerT
#print axioms genBlocksReuse
#print axioms crossMarkBlocksReuse
#print axioms protectedSameBlocksReuse
#print axioms hiddenObservationBlocksReuse
#print axioms backedCopyDoesNotHideEarlierSource
#print axioms selectedUCanReplayT
#print axioms completeTKillReplaysEmpty
#print axioms belowTCleanerRetainsProtectedRoot
#print axioms unrelatedCheckIsMarkSpecific
#print axioms unknownAlwaysFallsBack
#print axioms exactMustAnyFallBack

end DemandStorageNext.FlowRefinementInvariant
