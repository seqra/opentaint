import FiniteHistory

namespace ObservationFiber

-- All definitions are polymorphic in the real history and safety contract.
-- No transfer semantics or finite-corpus impossibility is assumed.
def Sound (obs : Program → History) (safe : Program → Prop)
    (remove : History → Bool) : Prop :=
  ∀ w, remove (obs w) = true → safe w

def Complete (obs : Program → History) (safe : Program → Prop)
    (remove : History → Bool) : Prop :=
  ∀ w, safe w → remove (obs w) = true

def FiberCertificate (obs : Program → History) (safe : Program → Prop)
    (h : History) : Prop :=
  ∀ w, obs w = h → safe w

structure UnsafeTwin (obs : Program → History) (safe : Program → Prop)
    (h : History) where
  world : Program
  sameHistory : obs world = h
  notSafe : ¬ safe world

theorem decisions_equal (obs : Program → History) (remove : History → Bool)
    (a b : Program) (same : obs a = obs b) :
    remove (obs a) = remove (obs b) := congrArg remove same

theorem universal_removal_requires_certificate
    (obs : Program → History) (safe : Program → Prop) (remove : History → Bool)
    (sound : Sound obs safe remove) (h : History) (selected : remove h = true) :
    FiberCertificate obs safe h := by
  intro w same
  apply sound w
  rw [same]
  exact selected

theorem certificate_on_selected_histories_is_sufficient
    (obs : Program → History) (safe : Program → Prop) (remove : History → Bool)
    (cert : ∀ h, remove h = true → FiberCertificate obs safe h) :
    Sound obs safe remove := by
  intro w selected
  exact cert (obs w) selected w rfl

theorem unsafe_twin_forces_rejection
    (obs : Program → History) (safe : Program → Prop) (remove : History → Bool)
    (sound : Sound obs safe remove) (h : History) (twin : UnsafeTwin obs safe h) :
    remove h = false := by
  cases answer : remove h with
  | false => rfl
  | true =>
      exact False.elim (twin.notSafe
        (universal_removal_requires_certificate obs safe remove sound h answer
          twin.world twin.sameHistory))

theorem same_history_safe_and_unsafe_excludes_sound_complete
    (obs : Program → History) (safe : Program → Prop) (remove : History → Bool)
    (a b : Program) (same : obs a = obs b) (safeA : safe a) (unsafeB : ¬ safe b)
    (sound : Sound obs safe remove) : ¬ Complete obs safe remove := by
  intro complete
  apply unsafeB
  apply sound b
  rw [← same]
  exact complete a safeA

-- A stronger domain contract could exclude an unsafe twin. This theorem
-- states the obligation; it grants no new proof-input permission.
theorem firing_under_extra_contract_must_exclude_unsafe_twin
    (obs : Program → History) (safe allowed : Program → Prop)
    (remove : History → Bool)
    (soundUnder : ∀ w, allowed w → remove (obs w) = true → safe w)
    (a b : Program) (same : obs a = obs b) (unsafeB : ¬ safe b)
    (selected : remove (obs a) = true) : ¬ allowed b := by
  intro allowedB
  apply unsafeB
  apply soundUnder b allowedB
  rw [← same]
  exact selected

-- Existing concept binding. The native sealed four-control package supplies
-- real 203-event equality and completed finding sets separately.
def conceptObs (w : FiniteHistory.World) := FiniteHistory.observedPrefix w 5

def conceptSafe (w : FiniteHistory.World) : Prop :=
  FiniteHistory.observedULoss w = false

def unsafeConceptTwin : UnsafeTwin conceptObs conceptSafe (conceptObs .a) where
  world := .b
  sameHistory := FiniteHistory.same_five_run_prefix.symm
  notSafe := by intro impossible; cases impossible

theorem concept_sound_policy_rejects_shared_history
    (remove : List FiniteHistory.Observation → Bool)
    (sound : Sound conceptObs conceptSafe remove) :
    remove (conceptObs .a) = false :=
  unsafe_twin_forces_rejection conceptObs conceptSafe remove sound
    (conceptObs .a) unsafeConceptTwin

#print axioms decisions_equal
#print axioms universal_removal_requires_certificate
#print axioms certificate_on_selected_histories_is_sufficient
#print axioms unsafe_twin_forces_rejection
#print axioms same_history_safe_and_unsafe_excludes_sound_complete
#print axioms firing_under_extra_contract_must_exclude_unsafe_twin
#print axioms unsafeConceptTwin
#print axioms concept_sound_policy_rejects_shared_history

end ObservationFiber
