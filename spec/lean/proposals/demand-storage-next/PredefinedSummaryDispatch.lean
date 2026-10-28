/-
  PROPOSAL ONLY. Selected complete-model dispatch, not JVM implementation.

  ResolvedBody is a tag: Analyze or Complete(model). Complete has no
  isComplete boolean and never falls back because an actual input has no
  matching data outcome. The model supplies control and actual-input data.
  No body analyzer, default/unresolved lane or body-boundary rules execute.
  Skipping predefined body-boundary rules is an EXPLICIT selected semantic
  change; no baseline body-observation equivalence is claimed. External
  call-site reports stay on their common invocation path.

  The data function is evaluated for the actual input and can represent a
  lazy schema; no complete method/input product is required. Registered method
  identity, not a spelling, chooses the model. Schema provenance stays outside
  the semantic outcome key.

  Real AP subtree selection, layer/protection handling, both frontend call
  planners, registered-ID construction, control/exception outcomes, external
  rule ordering and lifecycle remain explicit production adapter obligations.
-/
import Init

namespace DemandStorageNext.PredefinedSummaryDispatch
set_option autoImplicit false

inductive Owner where
  | registry
  | external
  deriving DecidableEq, Repr

inductive Data where
  | caller (slot payload : Nat)
  | field (owner : Owner) (slot payload : Nat)
  deriving DecidableEq, Repr

inductive Action where
  | analyzeBody
  | defaultSummary
  | unresolvedSummary
  | boundaryRules
  | definedControl
  | definedData
  deriving DecidableEq, Repr

structure BodyOutcome where
  normalControlReturn : Bool
  values : List Data
  bodyReports : List Nat
  actions : List Action
  deriving DecidableEq, Repr

/-- Complete return/control model. `valuesFor` is an actual-input selector,
    not an eagerly enumerated set of method/mark/field combinations. -/
structure Model where
  normalControlReturn : Bool
  valuesFor : Data → List Data

inductive ResolvedBody where
  | analyze
  | complete (model : Model)

def dispatch (resolved : ResolvedBody) (actual : Data) (analyzer : Data → BodyOutcome) : BodyOutcome :=
  match resolved with
  | .analyze => analyzer actual
  | .complete model => ⟨model.normalControlReturn,model.valuesFor actual,[],[.definedControl,.definedData]⟩

def forbidden (action : Action) : Bool :=
  match action with
  | .analyzeBody | .defaultSummary | .unresolvedSummary | .boundaryRules => true
  | .definedControl | .definedData => false

def anyForbidden : List Action → Bool
  | [] => false
  | first :: rest => forbidden first || anyForbidden rest

theorem completeHasExactlyModelOutcomes (model : Model) (actual : Data) (analyzer : Data → BodyOutcome) :
    (dispatch (.complete model) actual analyzer).values = model.valuesFor actual ∧
    (dispatch (.complete model) actual analyzer).normalControlReturn = model.normalControlReturn ∧
    (dispatch (.complete model) actual analyzer).bodyReports = [] := ⟨rfl,rfl,rfl⟩

theorem completeIgnoresAnalyzer (model : Model) (actual : Data) (left right : Data → BodyOutcome) :
    dispatch (.complete model) actual left = dispatch (.complete model) actual right := rfl

theorem completeHasNoFallbackOrBoundary (model : Model) (actual : Data) (analyzer : Data → BodyOutcome) :
    anyForbidden (dispatch (.complete model) actual analyzer).actions = false := rfl

theorem emptyDataIsKillNotFallback (model : Model) (actual : Data) (analyzer : Data → BodyOutcome)
    (missing : model.valuesFor actual = []) : (dispatch (.complete model) actual analyzer).values = [] := missing

theorem analyzeKeepsExistingPath (actual : Data) (analyzer : Data → BodyOutcome) :
    dispatch .analyze actual analyzer = analyzer actual := rfl

/-- External call-site rules execute independently of body resolution. -/
def invocationReports (externalReports : List Nat) (body : BodyOutcome) : List Nat :=
  externalReports ++ body.bodyReports

theorem appendEmpty {α : Type} (items : List α) : items ++ [] = items :=
  match items with
  | [] => rfl
  | first :: rest => congrArg (List.cons first) (appendEmpty rest)

theorem completePreservesExternalReports (externalReports : List Nat) (model : Model)
    (actual : Data) (analyzer : Data → BodyOutcome) :
    invocationReports externalReports (dispatch (.complete model) actual analyzer) = externalReports := by
  unfold invocationReports dispatch
  exact appendEmpty _

def natSame (left : Nat) : Nat → Bool :=
  Nat.rec
    (fun right => match right with | 0 => true | .succ _ => false)
    (fun _ prior right => match right with | 0 => false | .succ rest => prior rest)
    left

structure MethodRef where
  registeredIdentity : Nat
  spelling : Nat

def resolve (registered : MethodRef) (model : Model) (requested : MethodRef) : ResolvedBody :=
  bif natSame registered.registeredIdentity requested.registeredIdentity then .complete model else .analyze

theorem registeredIdentitySelectsModel (registered : MethodRef) (model : Model) :
    resolve registered model registered = .complete model := by
  have same : natSame registered.registeredIdentity registered.registeredIdentity = true :=
    Nat.rec rfl (fun _ prior => prior) registered.registeredIdentity
  unfold resolve
  rw [same]
  rfl

theorem sameSpellingDoesNotCapture (model : Model) :
    resolve ⟨0,77⟩ model ⟨1,77⟩ = .analyze := rfl

def preserveRegistry : Data → Bool
  | .caller _ _ => true
  | .field .registry _ _ => true
  | .field .external _ _ => false

def identityKernel (actual : Data) : List Data := bif preserveRegistry actual then [actual] else []

def cleanup : Model := ⟨true,identityKernel⟩

theorem cleanupPreservesRegistry (slot payload : Nat) :
    cleanup.valuesFor (.field .registry slot payload) = [.field .registry slot payload] := rfl

theorem cleanupKillsOtherStatics (slot payload : Nat) :
    cleanup.valuesFor (.field .external slot payload) = [] := rfl

theorem memberSingleton {α : Type} {row first : α} (member : row ∈ [first]) : row = first :=
  match member with | .head _ => rfl | .tail _ impossible => nomatch impossible

theorem identityKernelMember {actual result : Data} (member : result ∈ identityKernel actual) :
    result = actual := by
  unfold identityKernel at member
  cases keep : preserveRegistry actual with
  | false => rw [keep] at member; cases member
  | true => rw [keep] at member; exact memberSingleton member

/-- A partial identity filter is its own backward relation. This does not
    reverse arbitrary AP summaries or introduce a class-shaped initial. -/
theorem reverseIdentityKernel (need before : Data) :
    before ∈ identityKernel need ↔ need ∈ identityKernel before := by
  constructor
  · intro member
    have same := identityKernelMember member
    cases same
    exact member
  · intro member
    have same := identityKernelMember member
    cases same
    exact member

structure SchemaOutcome where
  semanticPayload : Nat
  schemaMetadata : Nat

def semanticKey (outcome : SchemaOutcome) : Nat := outcome.semanticPayload
def semanticHash (outcome : SchemaOutcome) : Nat := semanticKey outcome

theorem schemaMetadataOutsideSemanticKey (payload leftMetadata rightMetadata : Nat) :
    semanticKey ⟨payload,leftMetadata⟩ = semanticKey ⟨payload,rightMetadata⟩ ∧
    semanticHash ⟨payload,leftMetadata⟩ = semanticHash ⟨payload,rightMetadata⟩ := ⟨rfl,rfl⟩

def baselineWithBoundarySink (sink : Nat) : Data → BodyOutcome :=
  fun actual => ⟨true,identityKernel actual,[sink],[.analyzeBody,.boundaryRules]⟩

theorem skippingBoundaryIsIntentionalDifference (sink : Nat) (actual : Data) :
    (dispatch (.complete cleanup) actual (baselineWithBoundarySink sink)).values =
      (baselineWithBoundarySink sink actual).values ∧
    (dispatch (.complete cleanup) actual (baselineWithBoundarySink sink)).bodyReports ≠
      (baselineWithBoundarySink sink actual).bodyReports :=
  ⟨rfl,fun impossible => nomatch impossible⟩

#print axioms completeHasExactlyModelOutcomes
#print axioms completeIgnoresAnalyzer
#print axioms completeHasNoFallbackOrBoundary
#print axioms emptyDataIsKillNotFallback
#print axioms analyzeKeepsExistingPath
#print axioms completePreservesExternalReports
#print axioms registeredIdentitySelectsModel
#print axioms sameSpellingDoesNotCapture
#print axioms cleanupPreservesRegistry
#print axioms cleanupKillsOtherStatics
#print axioms identityKernelMember
#print axioms reverseIdentityKernel
#print axioms schemaMetadataOutsideSemanticKey
#print axioms skippingBoundaryIsIntentionalDifference

end DemandStorageNext.PredefinedSummaryDispatch
