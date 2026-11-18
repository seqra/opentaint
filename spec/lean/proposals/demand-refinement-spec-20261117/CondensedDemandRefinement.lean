import AuditKernel
import Run2Relay
import TargetSupport
import PairedContext
import LaneProof

namespace CondensedDemandRefinement

open NonEmptyPolicy NonEmptyRestriction

-- Coverage arguments compose only after both stages exhibit their witnesses
-- under the same positive semantics, with complete conjunctions.
theorem transitive_replacement_keeps_the_complete_observation
    (rules : List (AuditKernel.Rule α)) (old ready final : α → Prop)
    (first : AuditKernel.SeedCover rules old ready)
    (second : AuditKernel.SeedCover rules ready final)
    (witness : AuditKernel.Derives rules old observation) :
    AuditKernel.Derives rules final observation :=
  AuditKernel.positive_ND_closure_preserves_every_derivation rules old final
    (AuditKernel.seed_coverage_is_transitive rules old ready final first second) _ witness

def entryNE : Ap := ⟨0,[],.ne,none,[],[]⟩
def point : Ap := ⟨0,[],.exact,none,[],[]⟩
def star : Ap := {point with tail := .star}
def outcome : Value := ⟨⟨1,[2,3],.exact,none,[],[]⟩,false,false⟩
def ownRow : Row := ⟨entryNE,⟨1,[],.star,none,[],[]⟩⟩
def offer : Offered := ⟨star,false⟩

theorem the_same_public_key_does_not_authorize_the_other_raw_start :
    normalAp point = normalAp star ∧
    Run2Relay.restrictOne 3 2 false [offer] point outcome ownRow = none := by decide

theorem the_legal_raw_start_obeys_the_original_output_budget :
    Run2Relay.restrictOne 3 2 false [offer] star outcome ownRow =
      some (star,⟨⟨1,[2],.ne,none,[],[]⟩,true,false⟩) := by decide

def incompatibleOutputRow : Row := ⟨entryNE,⟨1,[9],.star,none,[],[]⟩⟩
def pointOnlyRow : Row := ⟨⟨0,[],.exact,some 7,[],[]⟩,ownRow.exit⟩

-- A permissive exit and a usable entry from different rows do not combine.
theorem a_row_join_cannot_borrow_another_rows_exit :
    Run2Relay.restrictOne 3 2 false [offer] star outcome incompatibleOutputRow = none ∧
    Run2Relay.restrictOne 3 2 false [offer] star outcome pointOnlyRow = none := by decide

-- A positive required origin refutes the NoRoute branch of a certificate.
theorem mixed_origin_service_keeps_each_required_witness
    (required kept : Nat → Prop) (catalogue : List Nat)
    (complete : ∀ s, required s → s ∈ catalogue)
    (certified : ∀ s ∈ catalogue, kept s ∨ (required s → False))
    (hit : required source) : kept source :=
  (certified _ (complete _ hit)).elim id (fun absent => False.elim (absent hit))

theorem frozen_terminal_retirement_keeps_all_required_witnesses
    (required kept : Nat → Nat → Prop) (catalogue : Nat → List Nat)
    (certificate : RecursiveTargetSupport.ClosedCertificate known seeds links needs)
    (eligible : RecursiveTargetSupport.retire true true true true (needs key) = true)
    (derived : RecursiveTargetSupport.Derivation seeds links key (.report goal))
    (complete : ∀ g s, required g s → s ∈ catalogue g)
    (served : ∀ g, known g = true → ∀ s ∈ catalogue g,
      kept g s ∨ (required g s → False))
    (hit : required goal source) : kept goal source := by
  have closed := RecursiveTargetSupport.a_retired_root_row_cannot_contain_an_unconfirmed_observation
    certificate eligible derived
  exact mixed_origin_service_keeps_each_required_witness
    (required goal) (kept goal) (catalogue goal) (complete goal) (served goal closed) hit

-- These are separate controls. Same-head support, a real field cut, and
-- the terminal reachability certificate serve different consumers.
theorem the_nested_repair_uses_the_same_stopping_boundary_from_run5 (n : Nat) :
    NestedFieldLane.repairedCone (n+2) = ⟨true,false,false,false,false⟩ :=
  NestedFieldLane.every_pair_from_run5_is_quiet_after_the_certified_omission n

end CondensedDemandRefinement
