import Std

/- Local work reduction, separate from demand subsumption. Native keys are
   opaque encodings of complete patterns/layers/scopes/families. A missing
   descriptor is a negative witness, never an acceptance certificate. -/
namespace WorkReduction
set_option autoImplicit false

inductive Tail where | star | exact | may | must
  deriving DecidableEq
def descends : Tail → Bool
  | .may | .must => true
  | .star | .exact => false
def deeperPrimary {α : Type} (tail : Tail) (rest : Option α) : Option α :=
  if descends tail then rest else none
def family {α : Type} (primary : Option α) (companions : α → List α) : List α :=
  match primary with
  | none => []
  | some p => p :: companions p

theorem star_descendant_empty {α : Type} (rest : Option α) (companions : α → List α) :
    family (deeperPrimary .star rest) companions = [] := rfl
theorem exact_descendant_empty {α : Type} (rest : Option α) (companions : α → List α) :
    family (deeperPrimary .exact rest) companions = [] := rfl
theorem may_descends {α : Type} (rest : Option α) : deeperPrimary .may rest = rest := rfl
theorem must_descends {α : Type} (rest : Option α) : deeperPrimary .must rest = rest := rfl

theorem ordered_empty_filter {α β : Type} (items : List β) (keep : β → Bool)
    (emit : β → List α) (empty : ∀ x, keep x = false → emit x = []) :
    (items.filter keep).flatMap emit = items.flatMap emit := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
    cases hx : keep x with
    | false => simp [hx, empty x hx, ih]
    | true => simp [hx, ih]

/- A Native initial may have a manager-admissions interner identity. Comparison
   uses the complete descriptor obtained by decoding, not that allocation ID.
   The native bridge must establish the round trip on every emitted key. -/
theorem materialized_membership {Key Native : Type}
    (materialize : Key → Native) (decode : Native → Key)
    (roundtrip : ∀ k, decode (materialize k) = k) (keys : List Key) (key : Key) :
    materialize key ∈ keys.map materialize ↔ key ∈ keys := by
  constructor
  · intro h
    obtain ⟨other, mem, eq⟩ := List.mem_map.mp h
    have same : other = key := by
      have := congrArg decode eq
      simpa only [roundtrip] using this
    exact same ▸ mem
  · intro h
    exact List.mem_map.mpr ⟨key,h,rfl⟩

def firstExtra (baseline : List Nat) : List Nat → Option Nat
  | [] => none
  | key :: rest => if key ∈ baseline then firstExtra baseline rest else some key

theorem first_extra_witness (baseline seen : List Nat) (key : Nat)
    (h : firstExtra baseline seen = some key) : key ∈ seen ∧ key ∉ baseline := by
  induction seen with
  | nil => simp [firstExtra] at h
  | cons x xs ih =>
    by_cases mem : x ∈ baseline
    · have tail : firstExtra baseline xs = some key := by simpa [firstExtra,mem] using h
      obtain ⟨hk, absent⟩ := ih tail
      exact ⟨List.mem_cons_of_mem _ hk,absent⟩
    · have same : x = key := by simpa [firstExtra,mem] using h
      subst key
      exact ⟨by simp,mem⟩

def sameObservation (left right : List Nat) : Bool :=
  left.all (fun k => decide (k ∈ right)) && right.all (fun k => decide (k ∈ left))

theorem same_observation_membership (left right : List Nat)
    (h : sameObservation left right = true) : ∀ key, key ∈ left ↔ key ∈ right := by
  have parts := Bool.and_eq_true_iff.mp h
  intro key
  exact ⟨fun hk => of_decide_eq_true (List.all_eq_true.mp parts.1 key hk),
         fun hk => of_decide_eq_true (List.all_eq_true.mp parts.2 key hk)⟩

theorem extra_rejects_full_observation (baseline admissions full : List Nat) (key : Nat)
    (subset : ∀ k, k ∈ admissions → k ∈ full)
    (h : firstExtra baseline admissions = some key) : sameObservation full baseline = false := by
  obtain ⟨mem,absent⟩ := first_extra_witness baseline admissions key h
  cases eq : sameObservation full baseline with
  | false => rfl
  | true => exact False.elim (absent ((same_observation_membership full baseline eq key).mp
      (subset key mem)))

def fastTrial (baseline admissions full : List Nat) : Bool :=
  match firstExtra baseline admissions with
  | some _ => false
  | none => sameObservation full baseline

theorem trial_decision_equal (baseline admissions full : List Nat)
    (subset : ∀ k, k ∈ admissions → k ∈ full) :
    fastTrial baseline admissions full = sameObservation full baseline := by
  cases h : firstExtra baseline admissions with
  | none => simp [fastTrial,h]
  | some key => simp [fastTrial,h,extra_rejects_full_observation baseline admissions full key subset h]

def firstAccepted {α : Type} (test : α → Bool) : List α → Option α
  | [] => none
  | candidate :: rest => if test candidate then some candidate else firstAccepted test rest

theorem selected_budget_equal {α : Type} (candidates : List α) (baseline : List Nat)
    (admissions full : α → List Nat)
    (subset : ∀ candidate k, k ∈ admissions candidate → k ∈ full candidate) :
    firstAccepted (fun c => fastTrial baseline (admissions c) (full c)) candidates =
    firstAccepted (fun c => sameObservation (full c) baseline) candidates := by
  have same : (fun c => fastTrial baseline (admissions c) (full c)) =
      (fun c => sameObservation (full c) baseline) :=
    funext (fun c => trial_decision_equal baseline (admissions c) (full c) (subset c))
  rw [same]

theorem no_extra_does_not_accept :
    firstExtra [1,2] [1] = none ∧ fastTrial [1,2] [1] [1] = false := by decide
theorem late_companion_rejects :
    firstExtra [1] [1,2] = some 2 ∧ fastTrial [1] [1,2] [1,2,3] = false := by decide
theorem same_geometry_other_scope_rejects :
    firstExtra [10] [20] = some 20 := by decide

/- Observer configuration is stable for this run. The disabled callback has
   no external effect. Its old archive is not read by semantic transfers.
   Enabled processing is intentionally identical, including old deduplication. -/
structure DiagnosticState where
  archive : List Nat
  callbacks : List Nat
  deriving DecidableEq, Repr

def oldStep (enabled : Bool) (state : DiagnosticState) (item : Nat) : DiagnosticState :=
  if item ∈ state.archive then state else
    ⟨item :: state.archive, if enabled then state.callbacks ++ [item] else state.callbacks⟩
def newStep (enabled : Bool) (state : DiagnosticState) (item : Nat) : DiagnosticState :=
  if enabled then oldStep enabled state item else state
def runDiagnostic (step : DiagnosticState → Nat → DiagnosticState)
    (state : DiagnosticState) (items : List Nat) : DiagnosticState := items.foldl step state

theorem disabled_old_callbacks (state : DiagnosticState) (item : Nat) :
    (oldStep false state item).callbacks = state.callbacks := by
  by_cases mem : item ∈ state.archive <;> simp [oldStep,mem]
theorem disabled_new_no_archive (state : DiagnosticState) (item : Nat) :
    newStep false state item = state := rfl
theorem enabled_exact_step (state : DiagnosticState) (item : Nat) :
    newStep true state item = oldStep true state item := rfl

theorem old_disabled_run_callbacks (items : List Nat) (state : DiagnosticState) :
    (runDiagnostic (oldStep false) state items).callbacks = state.callbacks := by
  induction items generalizing state with
  | nil => rfl
  | cons x xs ih =>
    exact (ih (oldStep false state x)).trans (disabled_old_callbacks state x)

theorem new_disabled_run_empty_work (items : List Nat) (state : DiagnosticState) :
    runDiagnostic (newStep false) state items = state := by
  induction items with
  | nil => rfl
  | cons x xs ih => exact ih

theorem enabled_exact_run (items : List Nat) (state : DiagnosticState) :
    runDiagnostic (newStep true) state items = runDiagnostic (oldStep true) state items := rfl

theorem disabled_output_equal (items : List Nat) (state : DiagnosticState) :
    (runDiagnostic (newStep false) state items).callbacks =
      (runDiagnostic (oldStep false) state items).callbacks := by
  rw [new_disabled_run_empty_work, old_disabled_run_callbacks]

/- A shared semantic transfer never reads DiagnosticState. This is the
   ownership/noninterference premise audited in RunMethodCallServices. -/
def combinedStep {State : Type} (transfer : State → Nat → State)
    (diagnostic : DiagnosticState → Nat → DiagnosticState)
    (state : State × DiagnosticState) (item : Nat) : State × DiagnosticState :=
  (transfer state.1 item, diagnostic state.2 item)

theorem combined_projection {State : Type} (transfer : State → Nat → State)
    (diagnostic : DiagnosticState → Nat → DiagnosticState)
    (items : List Nat) (state : State) (tracker : DiagnosticState) :
    (items.foldl (combinedStep transfer diagnostic) (state,tracker)).1 =
      items.foldl transfer state := by
  induction items generalizing state tracker with
  | nil => rfl
  | cons x xs ih => exact ih (transfer state x) (diagnostic tracker x)

theorem semantic_state_unchanged {State : Type} (transfer : State → Nat → State)
    (enabled : Bool) (items : List Nat) (state : State) (tracker : DiagnosticState) :
    (items.foldl (combinedStep transfer (oldStep enabled)) (state,tracker)).1 =
      (items.foldl (combinedStep transfer (newStep enabled)) (state,tracker)).1 := by
  rw [combined_projection,combined_projection]

#print axioms star_descendant_empty
#print axioms exact_descendant_empty
#print axioms may_descends
#print axioms must_descends
#print axioms ordered_empty_filter
#print axioms materialized_membership
#print axioms first_extra_witness
#print axioms same_observation_membership
#print axioms extra_rejects_full_observation
#print axioms trial_decision_equal
#print axioms selected_budget_equal
#print axioms no_extra_does_not_accept
#print axioms late_companion_rejects
#print axioms same_geometry_other_scope_rejects
#print axioms disabled_old_callbacks
#print axioms disabled_new_no_archive
#print axioms enabled_exact_step
#print axioms old_disabled_run_callbacks
#print axioms new_disabled_run_empty_work
#print axioms enabled_exact_run
#print axioms disabled_output_equal
#print axioms combined_projection
#print axioms semantic_state_unchanged
end WorkReduction
