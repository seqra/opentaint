import SelectedTargetApplication

/-!
Selected NormalTarget persistence laws, 2026-10-31.

Owned rows are keyed by exact method, full premise and ReportId. An already
persisted owned candidate creates no insertion or publication effect. That does
not globally disable reading a nonzero-premise saved relation for a new eligible
NORMAL caller input: the caller may create a fresh row under its own key.

NormalTarget is ignored backward. Persisted ZERO-premise replay has no new
effect only under an explicit settled-effect/report certificate. This model
does not derive settlement from the fact that the premise happens to be ZERO.
Report ids accumulate monotonically, including across iteration barriers.

Full premise equality and admitted/complete/all-NORMAL support are adapters;
the code does not replace them with AP prefix equality or generic applicability.
-/
namespace NormalTargetPersistence
open TargetZeroKernel
open SelectedTargetApplication
set_option autoImplicit false

structure OwnedRow (P : Type) where
  owner : Nat
  premise : P
  reportId : Nat
  deriving DecidableEq, Repr

structure Store (P : Type) where
  rows : List (OwnedRow P)
  rootIds : List Nat
  deriving DecidableEq, Repr

structure Insertion (P : Type) where
  store : Store P
  published : List (OwnedRow P)
  deriving DecidableEq, Repr

def addId (ids : List Nat) (id : Nat) : List Nat := if id ∈ ids then ids else id :: ids

def insertCandidate {P : Type} [DecidableEq P] (roots : List Nat) (zero : P)
    (store : Store P) (row : OwnedRow P) : Insertion P :=
  if row ∈ store.rows then ⟨store, []⟩
  else
    let ids := if row.owner ∈ roots ∧ row.premise = zero then addId store.rootIds row.reportId
      else store.rootIds
    ⟨⟨row :: store.rows, ids⟩, [row]⟩

theorem contains_means_no_owned_insertion_or_publication {P : Type} [DecidableEq P]
    (roots : List Nat) (zero : P) (store : Store P) (row : OwnedRow P) (saved : row ∈ store.rows) :
    insertCandidate roots zero store row = ⟨store, []⟩ := by
  exact if_pos saved

theorem fresh_owned_candidate_publishes_once {P : Type} [DecidableEq P]
    (roots : List Nat) (zero : P) (store : Store P) (row : OwnedRow P) (fresh : row ∉ store.rows) :
    (insertCandidate roots zero store row).published = [row] ∧
      row ∈ (insertCandidate roots zero store row).store.rows := by
  unfold insertCandidate
  rw [if_neg fresh]
  exact ⟨rfl, List.mem_cons.mpr (.inl rfl)⟩

theorem addId_preserves_members (ids : List Nat) (id old : Nat) (present : old ∈ ids) :
    old ∈ addId ids id := by
  unfold addId
  split
  · exact present
  · exact List.mem_cons.mpr (.inr present)

theorem insertion_root_ids_monotone {P : Type} [DecidableEq P] (roots : List Nat)
    (zero : P) (store : Store P) (row : OwnedRow P) (id : Nat) (present : id ∈ store.rootIds) :
    id ∈ (insertCandidate roots zero store row).store.rootIds := by
  unfold insertCandidate
  split
  · exact present
  · split
    · exact addId_preserves_members _ _ _ present
    · exact present

/-- A phase barrier emits no new owned rows and does not reset accumulated ids. -/
def barrier {P : Type} (store : Store P) : Store P := store

theorem barrier_preserves_root_ids {P : Type} (store : Store P) :
    (barrier store).rootIds = store.rootIds := rfl

/-- Required production invariant for ZERO replay suppression. `settledEffect`
    includes the original owned publication/propagation effect. Every retained
    ZERO row's id, including a non-root row, is already in committed rootIds.
    This rooted closure/commitment fact is assumed, not derived from ZERO. -/
structure ReplayCertificate {P : Type} (settledEffect : OwnedRow P → Prop)
    (roots : List Nat) (zero : P) (store : Store P) : Prop where
  zeroEffectsSettled : ∀ row ∈ store.rows, row.premise = zero → settledEffect row
  zeroIdCommitted : ∀ row ∈ store.rows, row.premise = zero → row.reportId ∈ store.rootIds

def readRelation {P : Type} [DecidableEq P] (settledEffect : OwnedRow P → Prop)
    (roots : List Nat) (zero : P) (store : Store P)
    (_certificate : ReplayCertificate settledEffect roots zero store)
    (direction : Direction) (row : OwnedRow P) (caller : Nat) (callerPremise : P)
    (support : Support) : Option (OwnedRow P) :=
  match direction with
  | .backward => none
  | .forward =>
      if row ∈ store.rows ∧ row.premise ≠ zero ∧ ready support = true ∧ allNormal support = true then
        some ⟨caller, callerPremise, row.reportId⟩
      else none

theorem all_backward_normal_reads_none {P : Type} [DecidableEq P]
    (settled : OwnedRow P → Prop) (roots : List Nat) (zero : P) (store : Store P)
    (certificate : ReplayCertificate settled roots zero store) (row : OwnedRow P)
    (caller : Nat) (callerPremise : P) (support : Support) :
    readRelation settled roots zero store certificate .backward row caller callerPremise support = none := rfl

theorem settled_zero_replay_none {P : Type} [DecidableEq P]
    (settled : OwnedRow P → Prop) (roots : List Nat) (zero : P) (store : Store P)
    (certificate : ReplayCertificate settled roots zero store) (row : OwnedRow P)
    (caller : Nat) (callerPremise : P) (support : Support) (isZero : row.premise = zero) :
    readRelation settled roots zero store certificate .forward row caller callerPremise support = none := by
  unfold readRelation
  have impossible : ¬ (row ∈ store.rows ∧ row.premise ≠ zero ∧ ready support = true ∧ allNormal support = true) :=
    fun condition => condition.2.1 isZero
  exact if_neg impossible

theorem saved_nonzero_new_normal_caller_can_apply {P : Type} [DecidableEq P]
    (settled : OwnedRow P → Prop) (roots : List Nat) (zero : P) (store : Store P)
    (certificate : ReplayCertificate settled roots zero store) (row : OwnedRow P)
    (caller : Nat) (callerPremise : P) (support : Support)
    (saved : row ∈ store.rows) (nonzero : row.premise ≠ zero)
    (admittedComplete : ready support = true) (normal : allNormal support = true) :
    readRelation settled roots zero store certificate .forward row caller callerPremise support =
      some ⟨caller, callerPremise, row.reportId⟩ := by
  exact if_pos ⟨saved, nonzero, admittedComplete, normal⟩

theorem saved_zero_effect_is_assumed_not_inferred {P : Type}
    (settled : OwnedRow P → Prop) (roots : List Nat) (zero : P) (store : Store P)
    (certificate : ReplayCertificate settled roots zero store) (row : OwnedRow P)
    (saved : row ∈ store.rows) (isZero : row.premise = zero) : settled row :=
  certificate.zeroEffectsSettled row saved isZero

/-- Skipping a settled ZERO marker cannot add a new final report id. This is
    the report observation equivalence, beyond a replay function returning NONE. -/
theorem skipped_zero_adds_no_final_report_id {P : Type}
    (settled : OwnedRow P → Prop) (roots : List Nat) (zero : P) (store : Store P)
    (certificate : ReplayCertificate settled roots zero store) (row : OwnedRow P)
    (saved : row ∈ store.rows) (isZero : row.premise = zero) :
    addId store.rootIds row.reportId = store.rootIds :=
  if_pos (certificate.zeroIdCommitted row saved isZero)

def insertBatch {P : Type} [DecidableEq P] (roots : List Nat) (zero : P) :
    Store P → List (OwnedRow P) → Store P
  | store, [] => barrier store
  | store, row :: rest => insertBatch roots zero (insertCandidate roots zero store row).store rest

theorem root_ids_monotone_across_batch_and_barrier {P : Type} [DecidableEq P]
    (roots : List Nat) (zero : P) (store : Store P) (rows : List (OwnedRow P))
    (id : Nat) (present : id ∈ store.rootIds) : id ∈ (insertBatch roots zero store rows).rootIds := by
  induction rows generalizing store with
  | nil => exact present
  | cons row rest ih =>
      apply ih
      exact insertion_root_ids_monotone roots zero store row id present

namespace Controls
def calleeRow : OwnedRow Premise := ⟨0, .ap .a, 7⟩
def zeroRoot : OwnedRow Premise := ⟨2, .zero, 7⟩
def store : Store Premise := ⟨[calleeRow, zeroRoot], [7]⟩
def normalSupport : Support := ⟨true, true, [.normal], .normal⟩
def demandSupport : Support := ⟨true, true, [.demand], .normal⟩

/-- Explicit finite fixture assumption; this is not a proof of production
    propagation settlement or of future caller closure. -/
def fixtureSettled (_row : OwnedRow Premise) : Prop := True
theorem fixtureCertificate : ReplayCertificate fixtureSettled [2] Premise.zero store where
  zeroEffectsSettled := by intro _ _ _; trivial
  zeroIdCommitted := by
    intro row saved isZero
    simp only [store, List.mem_cons, List.not_mem_nil, or_false] at saved
    rcases saved with same | same
    · subst row; cases isZero
    · subst row; exact List.mem_cons.mpr (.inl rfl)

theorem existing_owned_candidate_emits_nothing :
    insertCandidate [2] Premise.zero store calleeRow = ⟨store, []⟩ := by decide

theorem nonzero_saved_relation_can_create_fresh_caller_owned_row :
    readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .forward
      calleeRow 1 (.ap .b) normalSupport = some ⟨1, .ap .b, 7⟩ ∧
    (insertCandidate [2] Premise.zero store ⟨1, .ap .b, 7⟩).published = [⟨1, .ap .b, 7⟩] ∧
    (insertCandidate [2] Premise.zero store calleeRow).published = [] := by decide

theorem zero_replay_backward_and_demand_support_emit_nothing :
    readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .forward
      zeroRoot 3 .zero normalSupport = none ∧
    readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .backward
      calleeRow 1 (.ap .b) normalSupport = none ∧
    readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .forward
      calleeRow 1 (.ap .b) demandSupport = none := by decide

theorem root_ids_survive_multiple_barriers_and_new_report :
    7 ∈ (barrier (insertBatch [2] Premise.zero (barrier store) [⟨2, .zero, 9⟩])).rootIds ∧
    9 ∈ (barrier (insertBatch [2] Premise.zero (barrier store) [⟨2, .zero, 9⟩])).rootIds := by decide

def checks : Bool :=
  decide ((insertCandidate [2] Premise.zero store calleeRow).published = []) &&
  decide (readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .forward
    calleeRow 1 (.ap .b) normalSupport = some ⟨1, .ap .b, 7⟩) &&
  decide (readRelation fixtureSettled [2] Premise.zero store fixtureCertificate .forward
    zeroRoot 3 .zero normalSupport = none) &&
  decide (9 ∈ (insertBatch [2] Premise.zero store [⟨2, .zero, 9⟩]).rootIds)
theorem checks_pass : checks = true := rfl
end Controls

#print axioms contains_means_no_owned_insertion_or_publication
#print axioms fresh_owned_candidate_publishes_once
#print axioms all_backward_normal_reads_none
#print axioms settled_zero_replay_none
#print axioms saved_nonzero_new_normal_caller_can_apply
#print axioms saved_zero_effect_is_assumed_not_inferred
#print axioms skipped_zero_adds_no_final_report_id
#print axioms root_ids_monotone_across_batch_and_barrier
#print axioms Controls.checks_pass
#eval Controls.checks

end NormalTargetPersistence
