import Std

/- This is a bounded review model. It separates literal relation inclusion,
   scalar STAR correlation and demand-query comparison. It does not prove
   a new Kotlin compactor, arbitrary AP precondition weakening, or ND replay.
   Existing full native subsumption proofs retain their stated domains. -/
namespace HandoffSubsumptionReview
set_option autoImplicit false

section LiteralPayload
variable {Leaf Offer Reply : Type}

def answers (applyLeaf : Leaf → Offer → List Reply) (payload : List Leaf)
    (offer : Offer) : List Reply := payload.flatMap (fun leaf => applyLeaf leaf offer)

theorem literal_payload_inclusion (applyLeaf : Leaf → Offer → List Reply)
    (small large : List Leaf) (included : ∀ leaf ∈ small, leaf ∈ large)
    (offer : Offer) (reply : Reply) (found : reply ∈ answers applyLeaf small offer) :
    reply ∈ answers applyLeaf large offer := by
  obtain ⟨leaf, member, result⟩ := List.mem_flatMap.mp found
  exact List.mem_flatMap.mpr ⟨leaf, included leaf member, result⟩

theorem redundant_payload_union (applyLeaf : Leaf → Offer → List Reply)
    (small large : List Leaf) (included : ∀ leaf ∈ small, leaf ∈ large)
    (offer : Offer) (reply : Reply) :
    (reply ∈ answers applyLeaf small offer ∨ reply ∈ answers applyLeaf large offer) ↔
      reply ∈ answers applyLeaf large offer := by
  constructor
  · intro member
    cases member with
    | inl h => exact literal_payload_inclusion applyLeaf small large included offer reply h
    | inr h => exact h
  · exact Or.inr
end LiteralPayload

inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr

def guidanceTail : Tail → Tail
  | .must => .may
  | t => t

theorem must_and_may_have_equal_projection : guidanceTail .must = guidanceTail .may := rfl
theorem projection_is_not_injective : Tail.must ≠ Tail.may ∧
    guidanceTail .must = guidanceTail .may := by decide

/- Late FULL concrete-point entry comparison. No actual is needed to compute
   this key. The native C2 theorem, not this definition, proves key adequacy. -/
def pointEntryKey : Tail → Tail
  | .star => .exact
  | t => t

theorem late_point_keys_equal : pointEntryKey .star = pointEntryKey .exact := rfl

/- Both rules have input a.STAR/T. These are the scalar below-input cases:
   STAR output carries the actual suffix; EXACT output resets it to empty. -/
def scalarOutput (tail : Tail) (actualSuffix : List Nat) : List Nat :=
  if tail == .star then actualSuffix else []

theorem correlated_output_keeps_suffix (suffix : List Nat) :
    scalarOutput .star suffix = suffix := rfl
theorem exact_output_has_no_suffix (suffix : List Nat) :
    scalarOutput .exact suffix = [] := rfl
theorem equal_demand_entry_keys_do_not_equal_raw_transfer (field : Nat) :
    pointEntryKey .star = pointEntryKey .exact ∧
    scalarOutput .star [field] ≠ scalarOutput .exact [field] := by
  constructor
  · rfl
  · simp [scalarOutput]

/- One native C2 comparison cell: point demand at a.f and ancestor MAY at a.
   The actual is a.f.STAR/T on DEMAND. These are initial tags, not facts
   ordered by a newly asserted subsumption relation. -/
inductive Initial where | concreteExact | concreteStar | flowStar | flowExact
  deriving DecidableEq, Repr
def pointFamily : List Initial := [.concreteExact]
def ancestorMayFamily : List Initial := [.concreteStar, .flowStar, .flowExact]

theorem point_family_has_exact : Initial.concreteExact ∈ pointFamily := by decide
theorem ancestor_family_has_no_exact : Initial.concreteExact ∉ ancestorMayFamily := by decide
theorem c2_families_are_not_literal_cover :
    ¬(∀ initial ∈ pointFamily, initial ∈ ancestorMayFamily) := by
  intro included
  exact ancestor_family_has_no_exact (included _ point_family_has_exact)

/- Positive Horn logic only. This does not erase complete originals, change
   layers or establish equality of current native ND application services. -/
def fires (truth : Nat → Bool) (premise : List Nat) : Bool := premise.all truth

theorem weaker_horn_premise (truth : Nat → Bool) (weak strong : List Nat)
    (included : ∀ p ∈ weak, p ∈ strong) (h : fires truth strong = true) :
    fires truth weak = true := by
  apply List.all_eq_true.mpr
  intro p member
  exact List.all_eq_true.mp h p (included p member)

theorem unary_horn_covers_conjunction (truth : Nat → Bool) (p q : Nat)
    (h : fires truth [p,q] = true) : fires truth [p] = true := by
  exact weaker_horn_premise truth [p] [p,q] (by simp) h

#print axioms literal_payload_inclusion
#print axioms redundant_payload_union
#print axioms must_and_may_have_equal_projection
#print axioms projection_is_not_injective
#print axioms late_point_keys_equal
#print axioms correlated_output_keeps_suffix
#print axioms exact_output_has_no_suffix
#print axioms equal_demand_entry_keys_do_not_equal_raw_transfer
#print axioms point_family_has_exact
#print axioms ancestor_family_has_no_exact
#print axioms c2_families_are_not_literal_cover
#print axioms weaker_horn_premise
#print axioms unary_horn_covers_conjunction
end HandoffSubsumptionReview
