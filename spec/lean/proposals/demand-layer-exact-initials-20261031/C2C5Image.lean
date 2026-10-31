import ExactAdmission

/- Structural C5 entry selection is exactly the C2 image. Existence is
   constructive: every accepted exact seed has a canonical exact actual.
   Actual MAY admission is separate and never claims a NORMAL witness. -/
namespace ExactDemand
set_option autoImplicit false

theorem mark_sub_refl (mark : Mark) : markSub mark mark = true := by
  cases mark with
  | concrete value => simp only [markSub, decide_true]
  | flow excluded => simp [markSub]

theorem prefix_refl (path : List Nat) : isPrefix path path = true := by
  induction path with
  | nil => rfl
  | cons field rest ih => simp only [isPrefix, decide_true, Bool.true_and, ih]

theorem exact_geometry_self (demand : Pattern) :
    exactGeometry demand (exactPattern demand) = true := by
  simp only [exactGeometry, exactPattern, normalizeDemand, prefix_refl,
    List.drop_length, tailAdmits, Bool.and_self]

theorem exact_guards_self (limit : Nat) (demand : Pattern)
    (valid : validExactDemand limit demand = true) :
    exactGuards limit demand (exactPattern demand) = true := by
  have budget : decide (demand.path.length ≤ limit) = true :=
    ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp valid).1).1).1).2)
  unfold exactGuards
  rw [exact_geometry_self]
  change (decide (demand.base = demand.base) && markSub demand.mark demand.mark &&
    decide (demand.path.length ≤ limit) && decide (demand.path.length ≤ limit) && true) = true
  rw [decide_eq_true (Eq.refl demand.base), mark_sub_refl, budget]
  rfl

theorem exact_canonical_actual_emits (limit : Nat) (demand : Demand)
    (valid : validExactDemand limit demand.pattern = true) (layer : Layer) :
    emitExact limit demand ⟨exactPattern demand.pattern,layer⟩ =
      some ⟨exactKey demand.pattern,layer⟩ := by
  have geometry := exact_guards_self limit demand.pattern valid
  have actualValid : validActual (exactPattern demand.pattern) = true := rfl
  unfold emitExact
  rw [valid, actualValid, geometry]
  rfl

/-- C5 tests the structural exact key, not arbitrary geometric overlap. -/
def c5EntryImage (limit : Nat) (demand : Demand) (seed : Seed) : Bool :=
  validExactDemand limit demand.pattern && decide (seed.initial = exactKey demand.pattern)

theorem emitted_seed_is_in_c5_image (limit : Nat) (demand : Demand) (actual : Actual)
    (seed : Seed) (emitted : emitExact limit demand actual = some seed) :
    c5EntryImage limit demand seed = true := by
  unfold emitExact at emitted
  split at emitted
  next accepted =>
    have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1).1
    cases emitted
    simp only [c5EntryImage, valid, decide_true, Bool.and_self]
  next => cases emitted

/-- Executable C2 witness for every accepted C5 entry, with the same layer. -/
def c5ImageWitness (limit : Nat) (demand : Demand) (seed : Seed)
    (accepted : c5EntryImage limit demand seed = true) :
    {actual : Actual // emitExact limit demand actual = some seed} := by
  obtain ⟨valid, same⟩ := Bool.and_eq_true_iff.mp accepted
  have keyEq : seed.initial = exactKey demand.pattern := of_decide_eq_true same
  cases seed with
  | mk key layer =>
    change key = exactKey demand.pattern at keyEq
    subst key
    exact ⟨⟨exactPattern demand.pattern,layer⟩, exact_canonical_actual_emits limit demand valid layer⟩

theorem c5_image_iff_c2_emittable (limit : Nat) (demand : Demand) (seed : Seed) :
    c5EntryImage limit demand seed = true ↔
      ∃ actual, emitExact limit demand actual = some seed := by
  constructor
  · intro accepted
    exact ⟨(c5ImageWitness limit demand seed accepted).val,
      (c5ImageWitness limit demand seed accepted).property⟩
  · intro ⟨actual, emitted⟩
    exact emitted_seed_is_in_c5_image limit demand actual seed emitted

/-- Layered intersection keeps the raw result's DEMAND; it never upgrades it. -/
structure Result where
  key : Pattern
  layer : Layer
  deriving DecidableEq, Repr

def restrictC5 (limit : Nat) (demand : Demand) (seed : Seed) (raw : Result)
    (exitAccepted : Bool) : Option Result :=
  if c5EntryImage limit demand seed && exitAccepted then some raw else none

theorem c5_keeps_demand_layer (limit : Nat) (demand : Demand) (seed : Seed)
    (pattern : Pattern) (exitAccepted : Bool) (kept : Result)
    (accepted : restrictC5 limit demand seed ⟨pattern,.demand⟩ exitAccepted = some kept) :
    kept.layer = .demand := by
  unfold restrictC5 at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem c5_rejection_does_not_create_an_initial (limit : Nat) (demand : Demand)
    (seed : Seed) (raw : Result) (noImage : c5EntryImage limit demand seed = false)
    (exitAccepted : Bool) : restrictC5 limit demand seed raw exitAccepted = none := by
  simp only [restrictC5, noImage, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end ExactDemand
