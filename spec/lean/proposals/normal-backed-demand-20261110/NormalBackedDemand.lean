import Std

/-! Pure-copy boundary relations. Marks are opaque. No cut is interpreted as
an additional concrete transfer. A certificate covers every original relation,
including every path that has merged into one displayed MAY debt. -/
namespace NormalBackedDemand
set_option autoImplicit false

structure Row where
  scope : Nat
  inputBase : Nat
  outputBase : Nat
  inputPrefix : List Nat
  outputPrefix : List Nat
  deriving DecidableEq, Repr

structure Point where
  base : Nat
  path : List Nat
  mark : Nat
  deriving DecidableEq, Repr

def denote (r : Row) (scope : Nat) (a b : Point) : Prop :=
  scope = r.scope ∧ a.base = r.inputBase ∧ b.base = r.outputBase ∧
  a.mark = b.mark ∧ ∃ suffix, a.path = r.inputPrefix ++ suffix ∧
    b.path = r.outputPrefix ++ suffix

def specialize (r : Row) (suffix : List Nat) : Row :=
  { r with inputPrefix := r.inputPrefix ++ suffix,
           outputPrefix := r.outputPrefix ++ suffix }

def reverse (r : Row) : Row :=
  { r with inputBase := r.outputBase, outputBase := r.inputBase,
           inputPrefix := r.outputPrefix, outputPrefix := r.inputPrefix }

theorem reverse_reverse (r : Row) : reverse (reverse r) = r := rfl

theorem specialization_covered (r : Row) (shift : List Nat) (scope : Nat) (a b : Point)
    (h : denote (specialize r shift) scope a b) : denote r scope a b := by
  obtain ⟨hs, hi, ho, hm, suffix, hp, hq⟩ := h
  exact ⟨hs, hi, ho, hm, shift ++ suffix, by simpa [specialize, List.append_assoc] using hp,
    by simpa [specialize, List.append_assoc] using hq⟩

theorem reverse_denote (r : Row) (scope : Nat) (a b : Point) :
    denote (reverse r) scope b a ↔ denote r scope a b := by
  constructor
  · rintro ⟨hs, ho, hi, hm, suffix, hq, hp⟩
    exact ⟨hs, hi, ho, hm.symm, suffix, hp, hq⟩
  · rintro ⟨hs, hi, ho, hm, suffix, hp, hq⟩
    exact ⟨hs, ho, hi, hm.symm, suffix, hq, hp⟩

structure Witness where
  origin : Row
  native : Row
  opposite : Bool
  shift : List Nat
  deriving Repr

def view (w : Witness) : Row := if w.opposite then reverse w.native else w.native

def prefixB (p q : List Nat) : Bool := p == q.take p.length

def valid (normal : List (Bool × Row)) (entry : List Nat) (w : Witness) : Bool :=
  decide ((w.opposite, w.native) ∈ normal) && (w.origin == specialize (view w) w.shift) &&
    (w.opposite || prefixB (view w).inputPrefix entry)

/-- guard certifies restricted FULL FLOW DATA, same endpoint scope and the
complete eligible pure-copy slice. The source adapter must establish it. -/
def P (guard : Bool) (normal : List (Bool × Row)) (entry : List Nat)
    (origins : List Row) (certificate : List Witness) : Bool :=
  guard && origins.all (fun r => certificate.any (fun w => (w.origin == r) && valid normal entry w))

-- Each retained row keeps its real role in this run: false=direct, true=opposite.
def known (normal : List (Bool × Row)) (scope : Nat) (a b : Point) : Prop :=
  ∃ tagged ∈ normal, denote (if tagged.1 then reverse tagged.2 else tagged.2) scope a b

def owed (origins : List Row) (scope : Nat) (a b : Point) : Prop :=
  ∃ r ∈ origins, denote r scope a b

theorem valid_origin_has_native (normal : List (Bool × Row)) (entry : List Nat) (w : Witness)
    (checked : valid normal entry w = true) (scope : Nat) (a b : Point)
    (h : denote w.origin scope a b) : known normal scope a b := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at checked
  obtain ⟨⟨member, aligned⟩, _⟩ := checked
  rw [aligned] at h
  have hview := specialization_covered (view w) w.shift scope a b h
  exact ⟨(w.opposite, w.native), member, by simpa [view] using hview⟩

theorem checked_all_origins_covered (guard : Bool) (normal : List (Bool × Row)) (entry : List Nat)
    (origins : List Row) (certificate : List Witness)
    (checked : P guard normal entry origins certificate = true)
    (scope : Nat) (a b : Point) (h : owed origins scope a b) : known normal scope a b := by
  obtain ⟨r, member, hr⟩ := h
  simp only [P, Bool.and_eq_true, List.all_eq_true] at checked
  have one := checked.2 r member
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at one
  obtain ⟨w, _, equal, good⟩ := one
  apply valid_origin_has_native normal entry w good scope a b
  simpa [equal] using hr

/-- The erased refinement work contributes no new concrete boundary transfer. -/
theorem dropping_debt_preserves_transfer (guard : Bool) (normal : List (Bool × Row)) (entry : List Nat)
    (origins : List Row) (certificate : List Witness)
    (checked : P guard normal entry origins certificate = true)
    (scope : Nat) (a b : Point) :
    (known normal scope a b ∨ owed origins scope a b) ↔ known normal scope a b := by
  constructor
  · intro h
    exact h.elim id (checked_all_origins_covered guard normal entry origins certificate checked scope a b)
  · exact Or.inl

/-- In an arbitrary caller CFG, replace each covered boundary arc by its
native arc. Caller bind/return arcs and source/sink sites are untouched. -/
inductive Walk (step : Point → Point → Prop) : Point → Point → Prop where
  | done (a : Point) : Walk step a a
  | next {a b c : Point} : step a b → Walk step b c → Walk step a c

theorem walk_map {before after : Point → Point → Prop}
    (replace : ∀ a b, before a b → after a b) {a b : Point} :
    Walk before a b → Walk after a b := by
  intro h
  induction h with
  | done a => exact Walk.done a
  | next one _ ih => exact Walk.next (replace _ _ one) ih

theorem caller_walks_unchanged (guard : Bool) (normal : List (Bool × Row)) (entry : List Nat)
    (origins : List Row) (certificate : List Witness)
    (checked : P guard normal entry origins certificate = true)
    (scope : Nat) (caller : Point → Point → Prop) (a b : Point) :
    Walk (fun u v => caller u v ∨ known normal scope u v ∨ owed origins scope u v) a b ↔
      Walk (fun u v => caller u v ∨ known normal scope u v) a b := by
  constructor
  · apply walk_map
    intro u v h
    exact h.elim Or.inl (fun data => Or.inr ((dropping_debt_preserves_transfer
      guard normal entry origins certificate checked scope u v).mp data))
  · apply walk_map
    intro u v h
    exact h.elim Or.inl (fun data => Or.inr (Or.inl data))

/-- The API deliberately rejects same-direction readers below a STAR entry. -/
theorem same_direction_deeper_reader_rejected (normal : List (Bool × Row)) (entry : List Nat)
    (w : Witness) (same : w.opposite = false)
    (tooDeep : prefixB (view w).inputPrefix entry = false) : valid normal entry w = false := by
  simp [valid, same, tooDeep]

/-- Examples use 1=bytes, 2=array element, 3=another field. -/
def identity : Row := ⟨0, 0, 1, [], []⟩
def readElement : Row := ⟨0, 0, 1, [1, 2], []⟩
def writeBytes : Row := ⟨0, 0, 1, [1], [1]⟩

theorem cut_specialization_example :
    P true [(false, identity)] [1, 2] [specialize identity [1, 2]]
      [⟨specialize identity [1, 2], identity, false, [1, 2]⟩] = true := by decide

theorem read_with_opposite_native_example :
    P true [(true, reverse readElement)] [1] [readElement]
      [⟨readElement, reverse readElement, true, []⟩] = true := by decide

theorem deeper_direct_reader_is_not_enough :
    P true [(false, readElement)] [1] [readElement]
      [⟨readElement, readElement, false, []⟩] = false := by decide

theorem uncovered_second_read_rejects_whole_merged_edge :
    P true [(true, reverse readElement)] [1]
      [readElement, ⟨0, 0, 1, [1, 3], []⟩]
      [⟨readElement, reverse readElement, true, []⟩] = false := by decide

theorem no_normal_provider_no_retirement :
    P true [] [1] [readElement] [⟨readElement, reverse readElement, true, []⟩] = false := by decide

#print axioms checked_all_origins_covered
#print axioms dropping_debt_preserves_transfer
#print axioms caller_walks_unchanged
#print axioms same_direction_deeper_reader_rejected
end NormalBackedDemand
