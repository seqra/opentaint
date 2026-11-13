import RowCut

namespace RetainedDemandRowCut.Observed
open RetainedServiceBasis
open AncestorMayPointQuery (firstCountedLength firstExtension)

structure Triple where
  x : Row
  z : Row
  y : Row
  deriving DecidableEq, Repr

def check (counted : Nat → Bool) (originalSize : Nat) (t : Triple) : Bool :=
  decide (t.x.nativeKey < originalSize) && decide (t.z.nativeKey < originalSize) &&
  decide (t.y.nativeKey < originalSize) &&
  (t.x.nativeKey != t.z.nativeKey) && (t.x.nativeKey != t.y.nativeKey) &&
  c2Check t.x t.z && c5Check counted t.x t.y

def checkBatch (counted : Nat → Bool) (originalSize : Nat) (triples : List Triple) : Bool :=
  triples.all (check counted originalSize)

theorem checked_services (counted : Nat → Bool) (originalSize : Nat) (t : Triple)
    (h : check counted originalSize t = true) :
    checkRow counted t.x [t.z,t.y] = true := by
  simp only [check, Bool.and_eq_true] at h
  simp [checkRow, h.1.2, h.2]

theorem checked_distinct (counted : Nat → Bool) (originalSize : Nat) (t : Triple)
    (h : check counted originalSize t = true) : t.x ≠ t.z ∧ t.x ≠ t.y := by
  simp only [check, Bool.and_eq_true, bne_iff_ne] at h
  constructor
  · intro same
    exact h.1.1.1.2 (congrArg Row.nativeKey same)
  · intro same
    exact h.1.1.2 (congrArg Row.nativeKey same)

theorem checked_original_keys (counted : Nat → Bool) (originalSize : Nat) (t : Triple)
    (h : check counted originalSize t = true) :
    t.x.nativeKey < originalSize ∧ t.z.nativeKey < originalSize ∧ t.y.nativeKey < originalSize := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1,h.1.1.1.1.1.2,h.1.1.1.1.2⟩

def AgreeOn (finite actual : Nat → Bool) (word : List Nat) : Prop :=
  ∀ field ∈ word, finite field = actual field

theorem first_counted_congr (finite actual : Nat → Bool) (word : List Nat)
    (h : AgreeOn finite actual word) :
    firstCountedLength finite word = firstCountedLength actual word := by
  induction word with
  | nil => rfl
  | cons first rest ih =>
    have head := h first (List.mem_cons.mpr (Or.inl rfl))
    have tail : AgreeOn finite actual rest := by
      intro field member
      exact h field (List.mem_cons.mpr (Or.inr member))
    simp only [firstCountedLength,head,ih tail]

theorem first_extension_congr (finite actual : Nat → Bool) (parent child : List Nat)
    (h : AgreeOn finite actual child) :
    firstExtension finite parent child = firstExtension actual parent child := by
  have drop : AgreeOn finite actual (child.drop parent.length) := by
    intro field member
    exact h field (List.mem_of_mem_drop member)
  simp only [firstExtension,first_counted_congr finite actual (child.drop parent.length) drop]

theorem checked_actual_classifier (finite actual : Nat → Bool) (originalSize : Nat) (t : Triple)
    (h : check finite originalSize t = true) (agree : AgreeOn finite actual t.x.entry.path) :
    check actual originalSize t = true := by
  have eq : c5Check finite t.x t.y = c5Check actual t.x t.y := by
    simp only [c5Check, pointMayCheck,
      first_extension_congr finite actual t.y.entry.path t.x.entry.path agree]
  simpa only [check, eq] using h

theorem batch_member (counted : Nat → Bool) (originalSize : Nat) (triples : List Triple)
    (h : checkBatch counted originalSize triples = true) (t : Triple) (member : t ∈ triples) :
    check counted originalSize t = true := by
  exact List.all_eq_true.mp h t member

#print axioms checked_services
#print axioms checked_distinct
#print axioms checked_original_keys
#print axioms first_counted_congr
#print axioms first_extension_congr
#print axioms checked_actual_classifier
#print axioms batch_member
end RetainedDemandRowCut.Observed
