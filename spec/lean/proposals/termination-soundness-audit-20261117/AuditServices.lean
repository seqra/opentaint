import AuditGeometry
import DefiniteMustReplay
namespace AuditServices
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

deriving instance ReflBEq, LawfulBEq for Tail, Ap, Seed

-- C5's semantic image ranges over the full legal offer grammar. It is not
-- the set of offers observed so far. emit itself applies the legal guards.
def fullRawImage (run k : Nat) (back : Bool) (d raw : Ap) : Prop :=
  ∃ actual command,command∈HeadPolicy.emit run k back d actual ∧ command.ap=raw

theorem every_actual_C2_start_is_a_full_raw_C5_witness
    (run k : Nat) (back : Bool) (d : Ap) (actual : Offered) (command : Seed)
    (present : command∈HeadPolicy.emit run k back d actual) :
    fullRawImage run k back d command.ap := ⟨actual,command,present,rfl⟩

theorem every_full_raw_C5_witness_constructs_an_eligible_C2_start
    (run k : Nat) (back : Bool) (d raw : Ap) (present : fullRawImage run k back d raw) :
    ∃ actual command,command∈HeadPolicy.emit run k back d actual ∧ command.ap=raw := present

def need : Ap := ⟨1,[],.may,some 2,[],[]⟩
def normal : ExactSupport.Item := UniformActual.item .must false

def uncertainChild : ExactSupport.Item := UniformActual.item .may true [1]
def childPoint : Seed := ⟨⟨1,[1],.exact,some 2,[],[]⟩,true⟩

theorem geometric_cover_does_not_imply_equal_raw_query_service :
    UniformActual.covers normal uncertainChild=true ∧
    childPoint∈HeadPolicy.emit 5 4 false need ⟨uncertainChild.key.ap,true⟩ ∧
    childPoint∉HeadPolicy.emit 5 4 false need ⟨normal.key.ap,false⟩ := by decide +kernel

theorem all_concrete_points_remain_even_when_raw_query_service_changes
    (point : UniformSafety.Point) (present : UniformSafety.supports uncertainChild point) :
    UniformSafety.supports normal point :=
  UniformSafety.every_possible_point_has_the_retained_definite_support normal uncertainChild
    (by decide) point present

-- This is an interface countermodel, not a cold reachable-program claim.
-- It refutes the argument "the record remains, so every future call works".
def parentRequirement : Ap := ⟨0,[],.must,some 7,[],[]⟩
def childOffer : Offered := ⟨⟨0,[1],.must,some 7,[],[]⟩,false⟩
def parentRecord : Ap × Value :=
  (parentRequirement,⟨⟨1,[],.must,some 8,[],[]⟩,false,false⟩)

theorem retaining_a_NORMAL_record_does_not_serve_every_legal_future_input :
    parentRecord.2.demand=false ∧
    DefiniteMustReplay.saved parentRecord childOffer=none := by decide +kernel

-- A query token is distinct from a data point. A policy proof must show
-- how the needed query is replaced or why it is not needed in a reachable
-- history. Point containment alone supplies neither conclusion.
inductive Token where | data | query | demand | target
  deriving DecidableEq

def serviceProgram : List (AuditKernel.Rule Token) := [⟨[.query],.target⟩]
def before : Token → Prop := fun t => t=.data ∨ t=.query
def after : Token → Prop := fun t => t=.data

theorem retaining_all_data_can_still_lose_a_required_query_service :
    AuditKernel.Derives serviceProgram before .target ∧
    ¬AuditKernel.Derives serviceProgram after .target := by
  constructor
  · apply AuditKernel.Derives.apply (rules:=serviceProgram) (seed:=before)
      (⟨[Token.query],Token.target⟩ : AuditKernel.Rule Token) (by simp [serviceProgram])
    intro t ht
    have same : t=.query := by simpa using ht
    subst t
    exact AuditKernel.Derives.initial (rules:=serviceProgram) (seed:=before) Token.query (Or.inr rfl)
  · intro reached
    have invariant : ∀ t,after t → t=.data := fun _ h => h
    have rules : ∀ r∈serviceProgram,(∀ t∈r.premises,t=.data) → r.conclusion=.data := by
      intro r hr inputs
      have same : r=⟨[.query],.target⟩ := by simpa [serviceProgram] using hr
      subst r
      have impossible := inputs .query (by simp)
      cases impossible
    have impossible := AuditKernel.every_normal_claim_is_valid_under_valid_seeds_and_transfers
      serviceProgram after (fun t => t=.data) invariant rules .target reached
    cases impossible

theorem full_service_simulation_preserves_targets_as_well_as_data
    (oldRules newRules : List (AuditKernel.Rule Token)) (oldSeed newSeed : Token → Prop)
    (seedProof : ∀ t,oldSeed t → AuditKernel.Derives newRules newSeed t)
    (ruleProof : ∀ r∈oldRules,
      (∀ t∈r.premises,AuditKernel.Derives newRules newSeed t) →
        AuditKernel.Derives newRules newSeed r.conclusion)
    (old : AuditKernel.Derives oldRules oldSeed .target) :
    AuditKernel.Derives newRules newSeed .target :=
  AuditKernel.changing_a_policy_requires_seed_and_rule_simulation
    oldRules newRules oldSeed newSeed seedProof ruleProof .target old

end AuditServices
