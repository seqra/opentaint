import TargetClosure
import Acceptance

/- Proposed analysis-owner projection. Production is unchanged.
   A certificate describes a sole call and identity copies/return, with
   no rules on the relay's own boundaries or call instruction. -/
namespace TransparentOwner
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline NormalUniformNE

structure Shape where
  root : Bool := false
  copiesOnly : Bool := true
  calls : Nat := 1
  normalExitIsCallReturn : Bool := true
  exceptionExitIsCallThrow : Bool := true
  wrapperRulesEmpty : Bool := true
  innerCallRulesEmpty : Bool := true
  argumentsIdentical : Bool := true
  targets : Nat := 1
  cycleFree : Bool := true
  ordinaryBodies : Bool := true
  supportedContext : Bool := true
  deriving DecidableEq, BEq, Repr

def eligible (s : Shape) : Bool :=
  !s.root && s.copiesOnly && s.calls == 1 && s.normalExitIsCallReturn &&
  s.exceptionExitIsCallThrow && s.wrapperRulesEmpty && s.innerCallRulesEmpty &&
  s.argumentsIdentical && s.targets == 1 && s.cycleFree && s.ordinaryBodies && s.supportedContext

inductive Port where | normal | exceptional
  deriving DecidableEq, Repr
structure Result (α β : Type) where
  values : α
  port : Port
  observations : List β
  deriving DecidableEq, Repr

inductive PC (α β : Type) where
  | entry (a : α)
  | call (a : α)
  | afterCall (out : Result α β)
  | exit (out : Result α β)

/-- The only executable steps in the certified relay shape. No field read,
    write, rule, cleaner or other observation is hidden in an identity copy. -/
inductive Step (body : α → Result α β → Prop) : PC α β → PC α β → Prop where
  | enter (a : α) : Step body (.entry a) (.call a)
  | invoke {a out} (callee : body a out) : Step body (.call a) (.afterCall out)
  | returnOrThrow (out : Result α β) : Step body (.afterCall out) (.exit out)

def Executes (body : α → Result α β → Prop) (a : α) (out : Result α β) : Prop :=
  ∃ pc1 pc2, Step body (.entry a) pc1 ∧ Step body pc1 pc2 ∧ Step body pc2 (.exit out)

theorem relay_has_exactly_the_callee_behavior
    (body : α → Result α β → Prop) (a : α) (out : Result α β) :
    Executes body a out ↔ body a out := by
  constructor
  · rintro ⟨pc1,pc2,first,second,last⟩
    cases first
    cases second with
    | invoke hit => cases last; exact hit
  · intro hit
    exact ⟨.call a,.afterCall out,.enter a,.invoke hit,.returnOrThrow out⟩

theorem relay_preserves_the_complete_observation_sequence_and_port
    (body : α → Result α β → Prop) (a : α) (out : Result α β)
    (run : Executes body a out) :
    ∃ same, body a same ∧ same.values = out.values ∧ same.port = out.port ∧
      same.observations = out.observations :=
  ⟨out,(relay_has_exactly_the_callee_behavior body a out).mp run,rfl,rfl,rfl⟩

/-- An owner view changes a boundary base, never the field path or mark. -/
def rename (f : Nat → Nat) (a : Ap) : Ap := {a with base := f a.base}

theorem projection_keeps_fields_marks_exclusions_and_tail (f : Nat → Nat) (a : Ap) :
    (rename f a).path = a.path ∧ (rename f a).tail = a.tail ∧
    (rename f a).mark = a.mark ∧ (rename f a).e = a.e ∧ (rename f a).mx = a.mx :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem a_bijective_frame_has_a_constructive_inverse
    (f inv : Nat → Nat) (left : ∀ b, inv (f b) = b) (a : Ap) :
    rename inv (rename f a) = a := by
  cases a
  simp [rename,left]

theorem base_compatibility_is_preserved
    (f : Nat → Nat) (injective : ∀ a b, f a = f b → a = b) (a b : Ap) :
    (rename f a).base = (rename f b).base ↔ a.base = b.base := by
  constructor
  · exact injective _ _
  · intro h; exact congrArg f h

def renameValue (f : Nat → Nat) (a : Value) : Value := {a with ap := rename f a.ap}

theorem projection_preserves_support_and_literal_protection (f : Nat → Nat) (a : Value) :
    (renameValue f a).demand = a.demand ∧ (renameValue f a).h = a.h := ⟨rfl,rfl⟩

theorem projection_commutes_with_real_field_cuts (f : Nat → Nat) (limit : Nat) (a : Value) :
    renameValue f (cut limit a) = cut limit (renameValue f a) := by
  by_cases h : a.ap.path.length > limit <;> simp [renameValue,rename,cut,h]

theorem projection_commutes_with_flow_normalization (f : Nat → Nat) (a : Ap) :
    rename f (normalAp a) = normalAp (rename f a) := by
  cases a with
  | mk base path tail mark e mx => cases tail <;> rfl

/-- A chain only inserts/removes certified unobservable relay frames.
    It does not compose suffix evidence or make a new AP query. -/
def ChainExec : Nat → (α → Result α β → Prop) → α → Result α β → Prop
  | 0, body => body
  | n+1, body => Executes (ChainExec n body)

theorem arbitrarily_many_certified_relays_keep_the_same_behavior
    (n : Nat) (body : α → Result α β → Prop) (a : α) (out : Result α β) :
    ChainExec n body a out ↔ body a out := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (relay_has_exactly_the_callee_behavior (ChainExec n body) a out).trans ih

/-- Reject uncertain templates. Ordinary analysis is the total fallback. -/
def dispatch (s : Shape) (ordinary proxy : α) : α := if eligible s then proxy else ordinary

theorem every_rejected_owner_keeps_ordinary_analysis (s : Shape) (ordinary proxy : α)
    (rejected : eligible s = false) : dispatch s ordinary proxy = ordinary := by
  simp [dispatch,rejected]

theorem new_wrapper_is_eligible_but_observable_or_nontrivial_wrappers_are_not :
    eligible {} = true ∧
    eligible {wrapperRulesEmpty := false} = false ∧
    eligible {innerCallRulesEmpty := false} = false ∧
    eligible {copiesOnly := false} = false ∧
    eligible {argumentsIdentical := false} = false ∧
    eligible {exceptionExitIsCallThrow := false} = false ∧
    eligible {root := true} = false ∧ eligible {cycleFree := false} = false ∧
    eligible {ordinaryBodies := false} = false := by decide

theorem projection_adds_no_query_and_no_suffix_storage (f : Nat → Nat) (a : Ap) :
    (rename f a).path.length = a.path.length := rfl

end TransparentOwner

#print axioms TransparentOwner.relay_has_exactly_the_callee_behavior
#print axioms TransparentOwner.relay_preserves_the_complete_observation_sequence_and_port
#print axioms TransparentOwner.projection_keeps_fields_marks_exclusions_and_tail
#print axioms TransparentOwner.a_bijective_frame_has_a_constructive_inverse
#print axioms TransparentOwner.base_compatibility_is_preserved
#print axioms TransparentOwner.projection_preserves_support_and_literal_protection
#print axioms TransparentOwner.projection_commutes_with_real_field_cuts
#print axioms TransparentOwner.projection_commutes_with_flow_normalization
#print axioms TransparentOwner.arbitrarily_many_certified_relays_keep_the_same_behavior
#print axioms TransparentOwner.every_rejected_owner_keeps_ordinary_analysis
#print axioms TransparentOwner.new_wrapper_is_eligible_but_observable_or_nontrivial_wrappers_are_not
#print axioms TransparentOwner.projection_adds_no_query_and_no_suffix_storage
