import InitialEmissionExact

/-!
Selected unanswered-demand behavior, 2026-10-31.

An unsatisfied offer emits no initial and performs no special action, including
when every offer in the finite iteration is unsatisfied. There is no blocked
obligation store, demand carry, retry, synthetic Target, or ZERO fallback here.

The logical admission/work state is opaque. The only state adapter is `enqueue`,
called once per actually emitted nonzero initial. Admission emits no Target
event. Other independent source/sink transfers and method entries are outside
this boundary. The generic emitter can be the selected exact-$ emitter or any
other C2 demand emitter; positive ANY-demand behavior is not constrained here.
-/
namespace UnansweredDemand
open InitialEmissionExact
open TargetZeroKernel
set_option autoImplicit false

structure Offer where
  actual : AP
  demand : ExactDemand
  deriving DecidableEq, Repr

inductive AdmissionEvent where
  | initial (value : AP)
  | syntheticTarget (label : Target)
  deriving DecidableEq, Repr

structure Outcome (State : Type) where
  state : State
  initials : List AP
  events : List AdmissionEvent

def noAction {State : Type} (state : State) : Outcome State := ⟨state, [], []⟩

def deliver {State : Type} (enqueue : State → AP → State) (state : State)
    (emitted : List AP) : Outcome State :=
  ⟨emitted.foldl enqueue state, emitted, emitted.map AdmissionEvent.initial⟩

def runOffer {State : Type} (emit : Offer → List AP) (enqueue : State → AP → State)
    (state : State) (offer : Offer) : Outcome State := deliver enqueue state (emit offer)

def runBatch {State : Type} (emit : Offer → List AP) (enqueue : State → AP → State) :
    State → List Offer → Outcome State
  | state, [] => noAction state
  | state, offer :: rest =>
      let current := runOffer emit enqueue state offer
      let remaining := runBatch emit enqueue current.state rest
      ⟨remaining.state, current.initials ++ remaining.initials, current.events ++ remaining.events⟩

def newTargets : List AdmissionEvent → List Target
  | [] => []
  | .initial _ :: rest => newTargets rest
  | .syntheticTarget label :: rest => label :: newTargets rest

def exactEmitter (adapter : EmitterAdapter) (offer : Offer) : List AP :=
  emitExact adapter offer.actual offer.demand

theorem rejected_offer_leaves_state_unchanged {State : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (state : State) (offer : Offer) (rejected : emit offer = []) :
    runOffer emit enqueue state offer = noAction state := by
  rw [runOffer, rejected]
  rfl

theorem rejected_offer_changes_no_observation {State View : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (observe : State → View) (state : State)
    (offer : Offer) (rejected : emit offer = []) :
    observe (runOffer emit enqueue state offer).state = observe state := by
  rw [rejected_offer_leaves_state_unchanged emit enqueue state offer rejected]
  rfl

theorem rejected_offer_before_batch_is_noop {State : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (state : State) (offer : Offer) (rest : List Offer)
    (rejected : emit offer = []) :
    runBatch emit enqueue state (offer :: rest) = runBatch emit enqueue state rest := by
  simp only [runBatch, rejected_offer_leaves_state_unchanged emit enqueue state offer rejected,
    noAction, List.nil_append]

theorem all_unsatisfied_batch_unchanged {State : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (state : State) (offers : List Offer)
    (unsatisfied : ∀ offer ∈ offers, emit offer = []) :
    runBatch emit enqueue state offers = noAction state := by
  induction offers with
  | nil => rfl
  | cons offer rest ih =>
      rw [rejected_offer_before_batch_is_noop emit enqueue state offer rest
        (unsatisfied offer (List.mem_cons.mpr (.inl rfl)))]
      apply ih
      intro later member
      exact unsatisfied later (List.mem_cons.mpr (.inr member))

theorem all_unsatisfied_no_initial_no_auto_target {State : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (state : State) (offers : List Offer)
    (unsatisfied : ∀ offer ∈ offers, emit offer = []) :
    (runBatch emit enqueue state offers).initials = [] ∧
      newTargets (runBatch emit enqueue state offers).events = [] := by
  rw [all_unsatisfied_batch_unchanged emit enqueue state offers unsatisfied]
  exact ⟨rfl, rfl⟩

theorem duplicate_unsatisfied_no_effect {State : Type} (emit : Offer → List AP)
    (enqueue : State → AP → State) (state : State) (beforeOffers afterOffers : List Offer)
    (offer : Offer) (rejected : emit offer = []) :
    runBatch emit enqueue state (beforeOffers ++ [offer, offer] ++ afterOffers) =
      runBatch emit enqueue state (beforeOffers ++ afterOffers) := by
  induction beforeOffers generalizing state with
  | nil =>
      change runBatch emit enqueue state (offer :: offer :: afterOffers) = runBatch emit enqueue state afterOffers
      rw [rejected_offer_before_batch_is_noop emit enqueue state offer (offer :: afterOffers) rejected,
        rejected_offer_before_batch_is_noop emit enqueue state offer afterOffers rejected]
  | cons head rest ih =>
      simp only [List.cons_append, runBatch]
      rw [ih]

theorem exact_any_offer_is_noop {State : Type} (adapter : EmitterAdapter)
    (enqueue : State → AP → State) (state : State) (base mark : Nat) (path : List Nat)
    (demand : ExactDemand) :
    runOffer (exactEmitter adapter) enqueue state ⟨⟨base, path, .any, mark⟩, demand⟩ = noAction state :=
  rejected_offer_leaves_state_unchanged _ _ _ _ rfl

namespace Controls
open InitialEmissionExact.Controls

structure WorkState where
  admitted : List AP
  workCount : Nat
  deriving DecidableEq, Repr

def enqueue (state : WorkState) (initial : AP) : WorkState :=
  ⟨state.admitted ++ [initial], state.workCount + 1⟩

def initialState : WorkState := ⟨[exactActual], 5⟩
def rejectedSamePrefix : Offer := ⟨samePrefixAny, exactDemand⟩
def rejectedAncestor : Offer := ⟨ancestorAny, exactDemand⟩
def acceptedExact : Offer := ⟨exactActual, exactDemand⟩
def emitter : Offer → List AP := exactEmitter permissiveAdapter

theorem complete_unsatisfied_iteration_has_no_special_end_action :
    (runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).state = initialState ∧
    (runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).initials = [] ∧
    (runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).events = [] := by decide

theorem duplicate_rejection_cannot_enqueue_or_generate_target :
    (runBatch emitter enqueue initialState [rejectedAncestor, rejectedAncestor]).state = initialState ∧
    newTargets (runBatch emitter enqueue initialState [rejectedAncestor, rejectedAncestor]).events = [] := by decide

theorem accepted_offer_still_enqueues_once :
    (runBatch emitter enqueue initialState [acceptedExact]).state = ⟨[exactActual, exactActual], 6⟩ ∧
    (runBatch emitter enqueue initialState [acceptedExact]).initials = [exactActual] := by decide

def checks : Bool :=
  decide ((runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).state = initialState) &&
  decide ((runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).initials = []) &&
  decide ((runBatch emitter enqueue initialState [rejectedSamePrefix, rejectedAncestor]).events = []) &&
  decide ((runBatch emitter enqueue initialState [acceptedExact]).state.workCount = 6)

theorem checks_pass : checks = true := rfl
end Controls

#print axioms rejected_offer_leaves_state_unchanged
#print axioms rejected_offer_changes_no_observation
#print axioms all_unsatisfied_batch_unchanged
#print axioms all_unsatisfied_no_initial_no_auto_target
#print axioms duplicate_unsatisfied_no_effect
#print axioms exact_any_offer_is_noop
#print axioms Controls.checks_pass
#eval Controls.checks

end UnansweredDemand
