import Relations

/-!
Implementation bridge obligations for the packed input-residual index and
transitive FLOW-to-marked coverage. Native DAG operations and mask catalog
correspondence still need the production differential tests.
-/
namespace FlowAntichains.Implementation
open FlowAntichains.Relations
set_option autoImplicit false

variable {Field : Type}

theorem covers_requires_input_prefix (short long : Row Field) (cover : Covers short long) :
    short.inputPrefix.IsPrefix long.inputPrefix := by
  obtain ⟨residual, rfl⟩ := cover
  exact ⟨residual, rfl⟩

theorem covers_has_exact_output_residual (short long : Row Field) (cover : Covers short long) :
    ∃ residual, long.inputPrefix = short.inputPrefix ++ residual ∧
      long.outputPrefix = short.outputPrefix ++ residual := by
  obtain ⟨residual, rfl⟩ := cover
  exact ⟨residual, rfl, rfl⟩

theorem implicit_specialization_transitive (flow : Row Field) (first second : List Field) :
    Covers flow (specialize (specialize flow first) second) := by
  exact covers_trans flow (specialize flow first) (specialize (specialize flow first) second)
    ⟨first, rfl⟩ ⟨second, rfl⟩

/-- A full concrete mark is fixed; this is not a GROUP-token approximation. -/
def MarkedRelation (geometry : Row Field) (mark : Nat) (pair : Pair Field) : Prop :=
  pair.mark = mark ∧ denotes geometry pair

/-- `allows` is the native catalog-aware output-mask predicate, supplied intact. -/
def FlowRelation (geometry : Row Field) (allows : Nat → Bool) (pair : Pair Field) : Prop :=
  allows pair.mark = true ∧ denotes geometry pair

/-- Protection is an eligibility guard, not something inferred from ordinary pair inclusion. -/
def CanAbsorbMarked (flow marked : Row Field) (allows : Nat → Bool) (mark : Nat)
    (isProtected : Bool) : Prop :=
  isProtected = false ∧ ∀ pair, MarkedRelation marked mark pair → FlowRelation flow allows pair

theorem flow_absorbs_allowed_unprotected_marked_cover (flow marked : Row Field)
    (allows : Nat → Bool) (mark : Nat) (cover : Covers flow marked) (allowed : allows mark = true) :
    CanAbsorbMarked flow marked allows mark false := by
  refine ⟨rfl, ?_⟩
  intro pair member
  obtain ⟨sameMark, included⟩ := member
  exact ⟨by simpa only [sameMark] using allowed, cover_denotation flow marked cover pair included⟩

theorem marked_specialization_needs_no_admitted_intermediate (flow : Row Field)
    (first second : List Field) (allows : Nat → Bool) (mark : Nat) (allowed : allows mark = true) :
    CanAbsorbMarked flow (specialize (specialize flow first) second) allows mark false :=
  flow_absorbs_allowed_unprotected_marked_cover flow (specialize (specialize flow first) second)
    allows mark (implicit_specialization_transitive flow first second) allowed

theorem marked_cover_transitive (first middle marked : Row Field) (allows : Nat → Bool)
    (mark : Nat) (isProtected : Bool) (cover : Covers first middle)
    (absorbs : CanAbsorbMarked middle marked allows mark isProtected) :
    CanAbsorbMarked first marked allows mark isProtected := by
  refine ⟨absorbs.1, ?_⟩
  intro pair member
  have result := absorbs.2 pair member
  exact ⟨result.1, cover_denotation first middle cover pair result.2⟩

theorem protected_marked_relation_is_not_absorbable (flow marked : Row Field)
    (allows : Nat → Bool) (mark : Nat) : ¬ CanAbsorbMarked flow marked allows mark true := by
  intro impossible
  cases impossible.1

theorem excluded_full_mark_is_not_absorbable (flow marked : Row Field)
    (allows : Nat → Bool) (mark : Nat) (isProtected : Bool) (excluded : allows mark = false) :
    ¬ CanAbsorbMarked flow marked allows mark isProtected := by
  intro impossible
  let witness := produce marked mark []
  have member : MarkedRelation marked mark witness := ⟨rfl, ⟨[], rfl⟩⟩
  have result := impossible.2 witness member
  have accepted : allows mark = true := result.1
  rw [excluded] at accepted
  cases accepted

/-- The output mask is separate from the exact owner/geometry interface in this bridge. -/
def AllowsIncluded (broad narrow : Nat → Bool) : Prop :=
  ∀ mark, narrow mark = true → broad mark = true

theorem allowed_mask_transitive (first middle last : Nat → Bool)
    (left : AllowsIncluded first middle) (right : AllowsIncluded middle last) :
    AllowsIncluded first last := fun mark member => left mark (right mark member)

theorem compatible_mask_and_geometry_cover (short long : Row Field)
    (broad narrow : Nat → Bool) (geometry : Covers short long)
    (marks : AllowsIncluded broad narrow) (pair : Pair Field)
    (member : FlowRelation long narrow pair) : FlowRelation short broad pair :=
  ⟨marks pair.mark member.1, cover_denotation short long geometry pair member.2⟩

theorem mx_chain_needs_no_retained_intermediate (flow : Row Field) (residual : List Field)
    (broad middle narrow : Nat → Bool)
    (first : AllowsIncluded broad middle) (second : AllowsIncluded middle narrow)
    (pair : Pair Field) (member : FlowRelation (specialize flow residual) narrow pair) :
    FlowRelation flow broad pair :=
  compatible_mask_and_geometry_cover flow (specialize flow residual) broad narrow
    ⟨residual, rfl⟩ (allowed_mask_transitive broad middle narrow first second) pair member

/-- Cofinite support union is dual to intersection of exclusion predicates.
    Native FULL/GROUP catalog correspondence is not replaced by raw atom sets. -/
theorem allowed_union_is_exclusion_intersection (left right : Nat → Bool) (mark : Nat) :
    ((!left mark) || (!right mark)) = !(left mark && right mark) := by
  cases a : left mark <;> cases b : right mark <;> rfl

theorem cofinite_union_retains_each_allowed_side (left right : Nat → Bool) :
    AllowsIncluded (fun mark => !(left mark && right mark)) (fun mark => !left mark) ∧
    AllowsIncluded (fun mark => !(left mark && right mark)) (fun mark => !right mark) := by
  constructor
  · intro mark allowed
    cases a : left mark <;> cases b : right mark <;> simp_all
  · intro mark allowed
    cases a : left mark <;> cases b : right mark <;> simp_all

end FlowAntichains.Implementation
