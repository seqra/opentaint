import MainMigration

/- Implementation-seam laws. This file imports the pinned specification
   model; it does not redefine the AP engine or prove native correspondence. -/
namespace MainMigrationPlan
open MainMigration
set_option autoImplicit false

structure Row where
  ordinal : Nat
  guard : Bool
  valid : Bool
  payload : Nat
  deriving DecidableEq, Repr

def prepare (rows : List Row) : List Row := rows.filter Row.guard

def choose (explicit defaults : List Row) : List Row :=
  let prepared := prepare explicit
  if prepared.isEmpty then defaults else prepared

def lowerRows (rows : List Row) : List (Nat × Nat) :=
  (rows.filter Row.valid).map (fun row => (row.ordinal,row.payload))

theorem prepared_nonempty_suppresses_fallback (explicit defaults : List Row)
    (present : (prepare explicit).isEmpty = false) :
    choose explicit defaults = prepare explicit := by
  simp only [choose,present,Bool.false_eq_true,if_false]

theorem prepared_empty_uses_defaults (explicit defaults : List Row)
    (absent : (prepare explicit).isEmpty = true) :
    choose explicit defaults = defaults := by
  simp only [choose,absent,if_true]

theorem false_rule_does_not_suppress_fallback (ordinal payload : Nat) (defaults : List Row) :
    choose [⟨ordinal,false,true,payload⟩] defaults = defaults := rfl

theorem invalid_present_rule_does_not_enable_fallback (ordinal payload : Nat) (defaults : List Row) :
    choose [⟨ordinal,true,false,payload⟩] defaults = [⟨ordinal,true,false,payload⟩] := rfl

theorem invalid_present_rule_has_no_partial_output (ordinal payload : Nat) (defaults : List Row) :
    lowerRows (choose [⟨ordinal,true,false,payload⟩] defaults) = [] := rfl

theorem filtering_keeps_original_ordinals :
    lowerRows (choose [⟨4,false,true,40⟩,⟨9,true,true,90⟩] []) = [(9,90)] := rfl

def atomic (actions : List Nat) (allowed : Nat → Bool) : Option (List Nat) :=
  if actions.all allowed then some actions else none

theorem rejected_rule_emits_no_partial_vector (actions : List Nat) (allowed : Nat → Bool)
    (invalid : actions.all allowed = false) : atomic actions allowed = none := by
  simp only [atomic,invalid,Bool.false_eq_true,if_false]

theorem accepted_rule_preserves_the_complete_vector (actions : List Nat) (allowed : Nat → Bool)
    (valid : actions.all allowed = true) : atomic actions allowed = some actions := by
  simp only [atomic,valid,if_true]

def assumedLeaf (position : Desc) (mark : Nat) : Condition := .cm position mark

def assume (leaf : Condition) : Condition → Condition
  | .truth value => .truth value
  | .cm position mark => if .cm position mark = leaf then .truth true else .cm position mark
  | .neg child => .neg (assume leaf child)
  | .conj left right => .conj (assume leaf left) (assume leaf right)
  | .disj left right => .disj (assume leaf left) (assume leaf right)

theorem cleaner_assumption_preserves_truth_when_applicable
    (facts : List Marked) (leaf c : Condition) (holds : eval facts leaf = true) :
    eval facts (assume leaf c) = eval facts c := by
  induction c with
  | truth value => rfl
  | cm position mark =>
      by_cases same : Condition.cm position mark = leaf
      · rw [assume,if_pos same]
        change true = eval facts (.cm position mark)
        rw [same,holds]
      · rw [assume,if_neg same]
  | neg child ih => simp only [assume,eval,ih]
  | conj left right il ir => simp only [assume,eval,il,ir]
  | disj left right il ir => simp only [assume,eval,il,ir]

theorem any_cleaner_assumption_is_not_a_root_assumption (p : Pos) (mark : Nat) :
    assumedLeaf ⟨p,true⟩ mark ≠ assumedLeaf ⟨p,false⟩ mark := by
  intro equality
  cases equality

theorem assumptions_keep_AND_structure (leaf a b : Condition) :
    assume leaf (.conj a b) = .conj (assume leaf a) (assume leaf b) := rfl

def effectiveCap (bidirectional : Bool) (requested : Option Nat) : Option Nat :=
  if bidirectional then none else requested

theorem cap_cannot_leak_to_bidi_prescan (requested : Option Nat) :
    effectiveCap true requested = none := rfl

theorem legacy_cap_passes_through (requested : Option Nat) :
    effectiveCap false requested = requested := rfl

theorem cap_change_does_not_change_bidi_schedule (schedule : List Nat) (requested : Option Nat) :
    (bidiConfig ⟨schedule,effectiveCap true requested⟩).schedule = schedule := rfl

theorem selected_cleaner_and_source_reset_use_distinct_existing_primitives (p : Pos) :
    selectedCleanReach ⟨p,true⟩ = .below ∧
    returnResetReach true ⟨p,true⟩ = .atAndBelow := ⟨rfl,rfl⟩

theorem source_actions_keep_value_region_and_original_ids (p : Pos) (mark : Nat) :
    ([⟨⟨3,5,7⟩,⟨p,false⟩,mark⟩,⟨⟨3,5,8⟩,⟨p,true⟩,mark⟩] : List SourceAction).map bindSource =
      [⟨⟨3,5,7⟩,⟨p,.exact,mark⟩⟩,⟨⟨3,5,8⟩,⟨p,.must,mark⟩⟩] := rfl

namespace Examples
def root : Pos := ⟨1,[]⟩
def child : Pos := ⟨1,[8]⟩

theorem below_clean_does_not_assume_a_concrete_root_mark :
    eval [⟨child,7⟩] (assumedLeaf ⟨root,true⟩ 7) = true ∧
    eval [⟨child,7⟩] (assumedLeaf ⟨root,false⟩ 7) = false := by decide

theorem action_assumption_simplifies_only_its_own_mark :
    assume (.cm ⟨root,false⟩ 7)
      (.conj (.cm ⟨root,false⟩ 7) (.cm ⟨child,false⟩ 9)) =
      .conj (.truth true) (.cm ⟨child,false⟩ 9) := by decide

theorem false_first_row_does_not_renumber_the_second_action :
    lowerRows (choose [⟨11,false,true,8⟩,⟨19,true,true,9⟩] [⟨20,true,true,10⟩]) = [(19,9)] := rfl
end Examples
end MainMigrationPlan
