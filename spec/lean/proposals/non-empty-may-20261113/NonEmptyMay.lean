import Std

namespace NonEmptyMay

abbrev Path := List Nat
inductive Tail where | exact | may | nonEmpty
  deriving DecidableEq, BEq, Repr
inductive Slot where | empty | nonEmpty
  deriving DecidableEq, BEq, Repr
inductive Actual where | exact | star | may | nonEmpty
  deriving DecidableEq, BEq, Repr

def denotes : Tail → Path → Prop
  | .exact, suffix => suffix = []
  | .may, _ => True
  | .nonEmpty, suffix => suffix ≠ []

def rooted (head : Path) (tail : Tail) (location : Path) : Prop :=
  ∃ suffix, location = head ++ suffix ∧ denotes tail suffix

theorem may_partition (suffix : Path) :
    denotes .may suffix ↔ denotes .exact suffix ∨ denotes .nonEmpty suffix := by
  constructor
  · intro _
    cases suffix with
    | nil => exact Or.inl rfl
    | cons f rest => exact Or.inr (by simp [denotes])
  · intro _; trivial

theorem branches_disjoint (suffix : Path)
    (empty : denotes .exact suffix) (nonempty : denotes .nonEmpty suffix) : False :=
  nonempty empty

theorem rooted_may_partition (head location : Path) :
    rooted head .may location ↔
      rooted head .exact location ∨ rooted head .nonEmpty location := by
  constructor
  · rintro ⟨suffix,shape,inside⟩
    rcases (may_partition suffix).mp inside with empty | nonempty
    · exact Or.inl ⟨suffix,shape,empty⟩
    · exact Or.inr ⟨suffix,shape,nonempty⟩
  · intro h
    rcases h with ⟨suffix,shape,_⟩ | ⟨suffix,shape,_⟩ <;>
      exact ⟨suffix,shape,True.intro⟩

theorem nonempty_has_first_field (suffix : Path)
    (nonempty : denotes .nonEmpty suffix) :
    ∃ field rest, suffix = field :: rest := by
  cases suffix with
  | nil => exact False.elim (nonempty rfl)
  | cons field rest => exact ⟨field,rest,rfl⟩

-- Native guards and the full path selector are deliberately outside this
-- tail-only admission model. It makes no choice of a concrete new field.
def slots : Actual → List Slot
  | .exact => [.empty]
  | .star | .nonEmpty => [.nonEmpty]
  | .may => [.empty,.nonEmpty]
def demandSlots : Tail → List Slot
  | .exact => [.empty]
  | .nonEmpty => [.nonEmpty]
  | .may => [.empty,.nonEmpty]
def admitted (demand : Tail) (actual : Actual) : List Slot :=
  (demandSlots demand).filter (slots actual).contains

-- User clarification: these alternatives start ordinary EXACT and STAR
-- queries, not MAY or non-empty-MAY originals.
inductive InitialTail where | exact | star
  deriving DecidableEq, BEq, Repr
def startKind : Slot → InitialTail
  | .empty => .exact
  | .nonEmpty => .star
def starts (demand : Tail) (actual : Actual) : List InitialTail :=
  (admitted demand actual).map startKind

theorem may_offer_under_may_demand_starts_both :
    starts .may .may = [.exact,.star] := rfl
theorem may_offer_under_nonempty_demand_starts_only_star :
    starts .nonEmpty .may = [.star] := rfl
theorem star_offer_under_may_demand_starts_only_star :
    starts .may .star = [.star] := rfl
theorem all_initials_are_exact_or_star (i : InitialTail) :
    i = .exact ∨ i = .star := by
  cases i with
  | exact => exact Or.inl rfl
  | star => exact Or.inr rfl

-- y = p.g: the exact-p start does not reach a descendant. Consuming
-- the nonempty branch can exhaust the entire suffix g, giving y's root.
def firstReadResult : InitialTail → Option Tail
  | .exact => none
  | .star => some .may
theorem split_first_read_keeps_only_the_nonempty_branch :
    (starts .may .may).map firstReadResult = [none,some .may] := rfl

theorem star_cannot_supply_empty : admitted .exact .star = [] := rfl
theorem star_can_supply_nonempty : admitted .nonEmpty .star = [.nonEmpty] := rfl
theorem exact_cannot_supply_nonempty : admitted .nonEmpty .exact = [] := rfl
theorem may_supplies_both : admitted .may .may = [.empty,.nonEmpty] := rfl
theorem may_can_supply_empty : admitted .exact .may = [.empty] := rfl
theorem may_can_supply_nonempty : admitted .nonEmpty .may = [.nonEmpty] := rfl
theorem may_demand_retains_every_nonempty_admission (a : Actual) (s : Slot)
    (h : s ∈ admitted .nonEmpty a) : s ∈ admitted .may a := by
  cases a <;> cases s <;> simp_all [admitted,demandSlots,slots]

-- A known nonempty read prefix has been consumed. Empty output is valid.
theorem read_nonempty_to_may (field : Nat) (rest : Path) :
    denotes .nonEmpty (field :: rest) ↔ denotes .may rest := by
  simp [denotes]
theorem read_can_produce_exact_root (field : Nat) :
    denotes .nonEmpty [field] ∧ denotes .may [] := by
  exact ⟨by simp [denotes],True.intro⟩

-- Write `x.f = y`: f is a nonempty prefix at x, not an additional
-- nonemptiness constraint AFTER x.f.
theorem write_may_is_nonempty_at_parent (field : Nat) (suffix : Path) :
    rooted [] .nonEmpty (field :: suffix) := by
  exact ⟨field :: suffix,rfl,by simp [denotes]⟩

theorem write_may_retains_empty_at_child (field : Nat) :
    rooted [field] .may [field] := by
  exact ⟨[],by simp,True.intro⟩

theorem nonempty_at_child_loses_written_root (field : Nat) :
    ¬ rooted [field] .nonEmpty [field] := by
  rintro ⟨suffix,shape,nonempty⟩
  have empty : suffix = [] := (List.cons.inj shape).2.symm
  exact nonempty empty

theorem write_child_may_includes_every_input_binding
    (field : Nat) (suffix : Path) : rooted [field] .may (field :: suffix) := by
  exact ⟨suffix,rfl,True.intro⟩

-- A real cut removes at least one concrete field. The removed pattern
-- stays nonempty for every binding of its old tail, including epsilon.
theorem real_cut_is_nonempty (kept : Path) (field : Nat) (rest suffix : Path) :
    rooted kept .nonEmpty (kept ++ (field :: rest) ++ suffix) := by
  refine ⟨field :: (rest ++ suffix),?_,by simp [denotes]⟩
  simp [List.append_assoc]

theorem uncut_may_is_not_nonempty :
    denotes .may [] ∧ ¬ denotes .nonEmpty [] := by
  exact ⟨True.intro,by simp [denotes]⟩

-- Same complete premise, coordinates, marks, scope, support and literal
-- protection class are fixed before applying this output-only inclusion.
theorem may_covers_nonempty (head location : Path)
    (h : rooted head .nonEmpty location) : rooted head .may location := by
  rcases h with ⟨suffix,shape,_⟩
  exact ⟨suffix,shape,True.intro⟩

theorem dropping_covered_nonempty_preserves_union (head location : Path) :
    (rooted head .may location ∨ rooted head .nonEmpty location) ↔
      rooted head .may location := by
  constructor
  · intro h; cases h with
    | inl kept => exact kept
    | inr covered => exact may_covers_nonempty head location covered
  · exact Or.inl

-- Scalar retained basis; this is not a proposed extra runtime store.
def basis (hasMay hasNonEmpty : Bool) : Bool × Bool :=
  (hasMay,hasNonEmpty && !hasMay)
theorem covered_member_absent_regardless_of_arrival (firstMay secondMay : Bool) :
    basis (firstMay || secondMay) true = basis (secondMay || firstMay) true := by
  cases firstMay <;> cases secondMay <;> rfl
theorem may_provider_discards_nonempty : basis true true = (true,false) := rfl

-- A nonempty language need not expose a named first field in an offered
-- pattern. The selected tail test alone admits the same head again.
theorem nonempty_admission_does_not_force_a_known_field :
    admitted .nonEmpty .nonEmpty = [.nonEmpty] ∧
    admitted .nonEmpty .star = [.nonEmpty] ∧
    admitted .nonEmpty .may = [.nonEmpty] := by
  decide

-- This local read/write reset is not a complete-driver demand cycle.
def consumeOne : Tail → Tail
  | .nonEmpty => .may
  | t => t
def abstractWriteAtParent : Tail → Tail
  | .may => .nonEmpty
  | t => t
theorem read_write_can_reset_the_tail :
    abstractWriteAtParent (consumeOne .nonEmpty) = .nonEmpty := rfl

#print axioms may_partition
#print axioms branches_disjoint
#print axioms rooted_may_partition
#print axioms nonempty_has_first_field
#print axioms may_offer_under_may_demand_starts_both
#print axioms may_offer_under_nonempty_demand_starts_only_star
#print axioms star_offer_under_may_demand_starts_only_star
#print axioms all_initials_are_exact_or_star
#print axioms split_first_read_keeps_only_the_nonempty_branch
#print axioms star_cannot_supply_empty
#print axioms star_can_supply_nonempty
#print axioms exact_cannot_supply_nonempty
#print axioms may_supplies_both
#print axioms may_can_supply_empty
#print axioms may_can_supply_nonempty
#print axioms may_demand_retains_every_nonempty_admission
#print axioms read_nonempty_to_may
#print axioms read_can_produce_exact_root
#print axioms write_may_is_nonempty_at_parent
#print axioms write_may_retains_empty_at_child
#print axioms nonempty_at_child_loses_written_root
#print axioms write_child_may_includes_every_input_binding
#print axioms real_cut_is_nonempty
#print axioms uncut_may_is_not_nonempty
#print axioms may_covers_nonempty
#print axioms dropping_covered_nonempty_preserves_union
#print axioms covered_member_absent_regardless_of_arrival
#print axioms may_provider_discards_nonempty
#print axioms nonempty_admission_does_not_force_a_known_field
#print axioms read_write_can_reset_the_tail

end NonEmptyMay
