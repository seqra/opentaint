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

namespace NormalBackedDemand.Observed
def normal0 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins0 : List Row := [⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 1], [1]⟩]
def proof0 : List Witness := [⟨⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 1], [1]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [1]⟩]
theorem edge0_is_retirable : P true normal0 [1, 3] origins0 proof0 = true := by decide
#print axioms edge0_is_retirable
def normal1 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins1 : List Row := [⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 1], [1]⟩]
def proof1 : List Witness := [⟨⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2], [1]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 1], [1]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [1]⟩]
theorem edge1_is_retirable : P true normal1 [2, 3] origins1 proof1 = true := by decide
#print axioms edge1_is_retirable
def normal2 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins2 : List Row := [⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 2], [2]⟩]
def proof2 : List Witness := [⟨⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1], [2]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 2], [2]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [2]⟩]
theorem edge2_is_retirable : P true normal2 [1, 3] origins2 proof2 = true := by decide
#print axioms edge2_is_retirable
def normal3 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins3 : List Row := [⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 2], [2]⟩]
def proof3 : List Witness := [⟨⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 2], [2]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [2]⟩]
theorem edge3_is_retirable : P true normal3 [2, 3] origins3 proof3 = true := by decide
#print axioms edge3_is_retirable
def normal4 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], []⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [1, 3]⟩)]
def origins4 : List Row := [⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [1, 3], []⟩]
def proof4 : List Witness := [⟨⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], []⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [], []⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2]⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1, 3], []⟩, ⟨0, 1, 0, [], [1, 3]⟩, true, []⟩]
theorem edge4_is_retirable : P true normal4 [1] origins4 proof4 = true := by decide
#print axioms edge4_is_retirable
def normal5 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], []⟩), (false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [2, 3]⟩)]
def origins5 : List Row := [⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [2, 3], []⟩]
def proof5 : List Witness := [⟨⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], []⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1]⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2, 3], []⟩, ⟨0, 1, 0, [], [2, 3]⟩, true, []⟩]
theorem edge5_is_retirable : P true normal5 [2] origins5 proof5 = true := by decide
#print axioms edge5_is_retirable
def normal6 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩)]
def origins6 : List Row := [⟨0, 1, 0, [4], [1, 3, 4]⟩]
def proof6 : List Witness := [⟨⟨0, 1, 0, [4], [1, 3, 4]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [4]⟩]
theorem edge6_is_retirable : P true normal6 [4] origins6 proof6 = true := by decide
#print axioms edge6_is_retirable
def normal7 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (false, ⟨0, 1, 0, [1], []⟩)]
def origins7 : List Row := [⟨0, 1, 0, [1], [1, 3, 1]⟩, ⟨0, 1, 0, [1, 3], [1, 3]⟩, ⟨0, 1, 0, [1, 1, 3], [1, 3]⟩]
def proof7 : List Witness := [⟨⟨0, 1, 0, [1], [1, 3, 1]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 3], [1, 3]⟩, ⟨0, 1, 0, [], []⟩, false, [1, 3]⟩, ⟨⟨0, 1, 0, [1, 1, 3], [1, 3]⟩, ⟨0, 1, 0, [1], []⟩, false, [1, 3]⟩]
theorem edge7_is_retirable : P true normal7 [1] origins7 proof7 = true := by decide
#print axioms edge7_is_retirable
def normal8 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [2], [1]⟩), (false, ⟨0, 1, 0, [2], []⟩)]
def origins8 : List Row := [⟨0, 1, 0, [2], [1, 3, 2]⟩, ⟨0, 1, 0, [2, 3], [1, 3]⟩, ⟨0, 1, 0, [2, 1, 3], [1, 3]⟩]
def proof8 : List Witness := [⟨⟨0, 1, 0, [2], [1, 3, 2]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 3], [1, 3]⟩, ⟨0, 1, 0, [2], [1]⟩, false, [3]⟩, ⟨⟨0, 1, 0, [2, 1, 3], [1, 3]⟩, ⟨0, 1, 0, [2], []⟩, false, [1, 3]⟩]
theorem edge8_is_retirable : P true normal8 [2] origins8 proof8 = true := by decide
#print axioms edge8_is_retirable
def normal9 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1]⟩), (false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (true, ⟨0, 0, 1, [], [1]⟩), (true, ⟨0, 0, 1, [1], [2]⟩), (true, ⟨0, 0, 1, [], [2]⟩)]
def origins9 : List Row := [⟨0, 1, 0, [], [1]⟩, ⟨0, 1, 0, [], [1, 3]⟩, ⟨0, 1, 0, [1], [1]⟩, ⟨0, 1, 0, [1, 1], [1]⟩, ⟨0, 1, 0, [2], [1]⟩, ⟨0, 1, 0, [2, 1], [1]⟩]
def proof9 : List Witness := [⟨⟨0, 1, 0, [], [1]⟩, ⟨0, 1, 0, [], [1]⟩, false, []⟩, ⟨⟨0, 1, 0, [], [1, 3]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, []⟩, ⟨⟨0, 1, 0, [1], [1]⟩, ⟨0, 1, 0, [], []⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 1], [1]⟩, ⟨0, 0, 1, [], [1]⟩, true, [1]⟩, ⟨⟨0, 1, 0, [2], [1]⟩, ⟨0, 0, 1, [1], [2]⟩, true, []⟩, ⟨⟨0, 1, 0, [2, 1], [1]⟩, ⟨0, 0, 1, [], [2]⟩, true, [1]⟩]
theorem edge9_is_retirable : P true normal9 [] origins9 proof9 = true := by decide
#print axioms edge9_is_retirable
def normal10 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩)]
def origins10 : List Row := [⟨0, 1, 0, [4], [2, 3, 4]⟩]
def proof10 : List Witness := [⟨⟨0, 1, 0, [4], [2, 3, 4]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [4]⟩]
theorem edge10_is_retirable : P true normal10 [4] origins10 proof10 = true := by decide
#print axioms edge10_is_retirable
def normal11 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩), (false, ⟨0, 1, 0, [1], [2]⟩), (false, ⟨0, 1, 0, [1], []⟩)]
def origins11 : List Row := [⟨0, 1, 0, [1], [2, 3, 1]⟩, ⟨0, 1, 0, [1, 3], [2, 3]⟩, ⟨0, 1, 0, [1, 2, 3], [2, 3]⟩]
def proof11 : List Witness := [⟨⟨0, 1, 0, [1], [2, 3, 1]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 3], [2, 3]⟩, ⟨0, 1, 0, [1], [2]⟩, false, [3]⟩, ⟨⟨0, 1, 0, [1, 2, 3], [2, 3]⟩, ⟨0, 1, 0, [1], []⟩, false, [2, 3]⟩]
theorem edge11_is_retirable : P true normal11 [1] origins11 proof11 = true := by decide
#print axioms edge11_is_retirable
def normal12 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (false, ⟨0, 1, 0, [2], []⟩)]
def origins12 : List Row := [⟨0, 1, 0, [2], [2, 3, 2]⟩, ⟨0, 1, 0, [2, 3], [2, 3]⟩, ⟨0, 1, 0, [2, 2, 3], [2, 3]⟩]
def proof12 : List Witness := [⟨⟨0, 1, 0, [2], [2, 3, 2]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 3], [2, 3]⟩, ⟨0, 1, 0, [], []⟩, false, [2, 3]⟩, ⟨⟨0, 1, 0, [2, 2, 3], [2, 3]⟩, ⟨0, 1, 0, [2], []⟩, false, [2, 3]⟩]
theorem edge12_is_retirable : P true normal12 [2] origins12 proof12 = true := by decide
#print axioms edge12_is_retirable
def normal13 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2]⟩), (false, ⟨0, 1, 0, [], [2, 3]⟩), (true, ⟨0, 0, 1, [2], [1]⟩), (true, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 1, 0, [], []⟩), (true, ⟨0, 0, 1, [], [2]⟩)]
def origins13 : List Row := [⟨0, 1, 0, [], [2]⟩, ⟨0, 1, 0, [], [2, 3]⟩, ⟨0, 1, 0, [1], [2]⟩, ⟨0, 1, 0, [1, 2], [2]⟩, ⟨0, 1, 0, [2], [2]⟩, ⟨0, 1, 0, [2, 2], [2]⟩]
def proof13 : List Witness := [⟨⟨0, 1, 0, [], [2]⟩, ⟨0, 1, 0, [], [2]⟩, false, []⟩, ⟨⟨0, 1, 0, [], [2, 3]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, []⟩, ⟨⟨0, 1, 0, [1], [2]⟩, ⟨0, 0, 1, [2], [1]⟩, true, []⟩, ⟨⟨0, 1, 0, [1, 2], [2]⟩, ⟨0, 0, 1, [], [1]⟩, true, [2]⟩, ⟨⟨0, 1, 0, [2], [2]⟩, ⟨0, 1, 0, [], []⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 2], [2]⟩, ⟨0, 0, 1, [], [2]⟩, true, [2]⟩]
theorem edge13_is_retirable : P true normal13 [] origins13 proof13 = true := by decide
#print axioms edge13_is_retirable
def normal14 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins14 : List Row := [⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 1], [1]⟩]
def proof14 : List Witness := [⟨⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 1], [1]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [1]⟩]
theorem edge14_is_retirable : P true normal14 [1, 3] origins14 proof14 = true := by decide
#print axioms edge14_is_retirable
def normal15 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins15 : List Row := [⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 1], [1]⟩]
def proof15 : List Witness := [⟨⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2], [1]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 1], [1]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [1]⟩]
theorem edge15_is_retirable : P true normal15 [2, 3] origins15 proof15 = true := by decide
#print axioms edge15_is_retirable
def normal16 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins16 : List Row := [⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 2], [2]⟩]
def proof16 : List Witness := [⟨⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1], [2]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 2], [2]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [2]⟩]
theorem edge16_is_retirable : P true normal16 [1, 3] origins16 proof16 = true := by decide
#print axioms edge16_is_retirable
def normal17 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins17 : List Row := [⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 2], [2]⟩]
def proof17 : List Witness := [⟨⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 2], [2]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [2]⟩]
theorem edge17_is_retirable : P true normal17 [2, 3] origins17 proof17 = true := by decide
#print axioms edge17_is_retirable
def normal18 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], []⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [1, 3]⟩)]
def origins18 : List Row := [⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [1, 3], []⟩]
def proof18 : List Witness := [⟨⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], []⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [], []⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2]⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1, 3], []⟩, ⟨0, 1, 0, [], [1, 3]⟩, true, []⟩]
theorem edge18_is_retirable : P true normal18 [1] origins18 proof18 = true := by decide
#print axioms edge18_is_retirable
def normal19 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], []⟩), (false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [2, 3]⟩)]
def origins19 : List Row := [⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [2, 3], []⟩]
def proof19 : List Witness := [⟨⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], []⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1]⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2, 3], []⟩, ⟨0, 1, 0, [], [2, 3]⟩, true, []⟩]
theorem edge19_is_retirable : P true normal19 [2] origins19 proof19 = true := by decide
#print axioms edge19_is_retirable
def normal20 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩)]
def origins20 : List Row := [⟨0, 1, 0, [4], [1, 3, 4]⟩]
def proof20 : List Witness := [⟨⟨0, 1, 0, [4], [1, 3, 4]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [4]⟩]
theorem edge20_is_retirable : P true normal20 [4] origins20 proof20 = true := by decide
#print axioms edge20_is_retirable
def normal21 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (false, ⟨0, 1, 0, [1], []⟩)]
def origins21 : List Row := [⟨0, 1, 0, [1], [1, 3, 1]⟩, ⟨0, 1, 0, [1, 3], [1, 3]⟩, ⟨0, 1, 0, [1, 1, 3], [1, 3]⟩]
def proof21 : List Witness := [⟨⟨0, 1, 0, [1], [1, 3, 1]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 3], [1, 3]⟩, ⟨0, 1, 0, [], []⟩, false, [1, 3]⟩, ⟨⟨0, 1, 0, [1, 1, 3], [1, 3]⟩, ⟨0, 1, 0, [1], []⟩, false, [1, 3]⟩]
theorem edge21_is_retirable : P true normal21 [1] origins21 proof21 = true := by decide
#print axioms edge21_is_retirable
def normal22 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [2], [1]⟩), (false, ⟨0, 1, 0, [2], []⟩)]
def origins22 : List Row := [⟨0, 1, 0, [2], [1, 3, 2]⟩, ⟨0, 1, 0, [2, 3], [1, 3]⟩, ⟨0, 1, 0, [2, 1, 3], [1, 3]⟩]
def proof22 : List Witness := [⟨⟨0, 1, 0, [2], [1, 3, 2]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 3], [1, 3]⟩, ⟨0, 1, 0, [2], [1]⟩, false, [3]⟩, ⟨⟨0, 1, 0, [2, 1, 3], [1, 3]⟩, ⟨0, 1, 0, [2], []⟩, false, [1, 3]⟩]
theorem edge22_is_retirable : P true normal22 [2] origins22 proof22 = true := by decide
#print axioms edge22_is_retirable
def normal23 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [1]⟩), (false, ⟨0, 1, 0, [], [1, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (true, ⟨0, 0, 1, [], [1]⟩), (true, ⟨0, 0, 1, [1], [2]⟩), (true, ⟨0, 0, 1, [], [2]⟩)]
def origins23 : List Row := [⟨0, 1, 0, [], [1]⟩, ⟨0, 1, 0, [], [1, 3]⟩, ⟨0, 1, 0, [1], [1]⟩, ⟨0, 1, 0, [1, 1], [1]⟩, ⟨0, 1, 0, [2], [1]⟩, ⟨0, 1, 0, [2, 1], [1]⟩]
def proof23 : List Witness := [⟨⟨0, 1, 0, [], [1]⟩, ⟨0, 1, 0, [], [1]⟩, false, []⟩, ⟨⟨0, 1, 0, [], [1, 3]⟩, ⟨0, 1, 0, [], [1, 3]⟩, false, []⟩, ⟨⟨0, 1, 0, [1], [1]⟩, ⟨0, 1, 0, [], []⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 1], [1]⟩, ⟨0, 0, 1, [], [1]⟩, true, [1]⟩, ⟨⟨0, 1, 0, [2], [1]⟩, ⟨0, 0, 1, [1], [2]⟩, true, []⟩, ⟨⟨0, 1, 0, [2, 1], [1]⟩, ⟨0, 0, 1, [], [2]⟩, true, [1]⟩]
theorem edge23_is_retirable : P true normal23 [] origins23 proof23 = true := by decide
#print axioms edge23_is_retirable
def normal24 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩)]
def origins24 : List Row := [⟨0, 1, 0, [4], [2, 3, 4]⟩]
def proof24 : List Witness := [⟨⟨0, 1, 0, [4], [2, 3, 4]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [4]⟩]
theorem edge24_is_retirable : P true normal24 [4] origins24 proof24 = true := by decide
#print axioms edge24_is_retirable
def normal25 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩), (false, ⟨0, 1, 0, [1], [2]⟩), (false, ⟨0, 1, 0, [1], []⟩)]
def origins25 : List Row := [⟨0, 1, 0, [1], [2, 3, 1]⟩, ⟨0, 1, 0, [1, 3], [2, 3]⟩, ⟨0, 1, 0, [1, 2, 3], [2, 3]⟩]
def proof25 : List Witness := [⟨⟨0, 1, 0, [1], [2, 3, 1]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [1]⟩, ⟨⟨0, 1, 0, [1, 3], [2, 3]⟩, ⟨0, 1, 0, [1], [2]⟩, false, [3]⟩, ⟨⟨0, 1, 0, [1, 2, 3], [2, 3]⟩, ⟨0, 1, 0, [1], []⟩, false, [2, 3]⟩]
theorem edge25_is_retirable : P true normal25 [1] origins25 proof25 = true := by decide
#print axioms edge25_is_retirable
def normal26 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2, 3]⟩), (false, ⟨0, 1, 0, [], []⟩), (false, ⟨0, 1, 0, [2], []⟩)]
def origins26 : List Row := [⟨0, 1, 0, [2], [2, 3, 2]⟩, ⟨0, 1, 0, [2, 3], [2, 3]⟩, ⟨0, 1, 0, [2, 2, 3], [2, 3]⟩]
def proof26 : List Witness := [⟨⟨0, 1, 0, [2], [2, 3, 2]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 3], [2, 3]⟩, ⟨0, 1, 0, [], []⟩, false, [2, 3]⟩, ⟨⟨0, 1, 0, [2, 2, 3], [2, 3]⟩, ⟨0, 1, 0, [2], []⟩, false, [2, 3]⟩]
theorem edge26_is_retirable : P true normal26 [2] origins26 proof26 = true := by decide
#print axioms edge26_is_retirable
def normal27 : List (Bool × Row) := [(false, ⟨0, 1, 0, [], [2]⟩), (false, ⟨0, 1, 0, [], [2, 3]⟩), (true, ⟨0, 0, 1, [2], [1]⟩), (true, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 1, 0, [], []⟩), (true, ⟨0, 0, 1, [], [2]⟩)]
def origins27 : List Row := [⟨0, 1, 0, [], [2]⟩, ⟨0, 1, 0, [], [2, 3]⟩, ⟨0, 1, 0, [1], [2]⟩, ⟨0, 1, 0, [1, 2], [2]⟩, ⟨0, 1, 0, [2], [2]⟩, ⟨0, 1, 0, [2, 2], [2]⟩]
def proof27 : List Witness := [⟨⟨0, 1, 0, [], [2]⟩, ⟨0, 1, 0, [], [2]⟩, false, []⟩, ⟨⟨0, 1, 0, [], [2, 3]⟩, ⟨0, 1, 0, [], [2, 3]⟩, false, []⟩, ⟨⟨0, 1, 0, [1], [2]⟩, ⟨0, 0, 1, [2], [1]⟩, true, []⟩, ⟨⟨0, 1, 0, [1, 2], [2]⟩, ⟨0, 0, 1, [], [1]⟩, true, [2]⟩, ⟨⟨0, 1, 0, [2], [2]⟩, ⟨0, 1, 0, [], []⟩, false, [2]⟩, ⟨⟨0, 1, 0, [2, 2], [2]⟩, ⟨0, 0, 1, [], [2]⟩, true, [2]⟩]
theorem edge27_is_retirable : P true normal27 [] origins27 proof27 = true := by decide
#print axioms edge27_is_retirable
def normal28 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins28 : List Row := [⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 1], [1]⟩]
def proof28 : List Witness := [⟨⟨0, 0, 1, [1, 3], [1, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3], [1, 1, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 1], [1]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [1]⟩]
theorem edge28_is_retirable : P true normal28 [1, 3] origins28 proof28 = true := by decide
#print axioms edge28_is_retirable
def normal29 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins29 : List Row := [⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 1], [1]⟩]
def proof29 : List Witness := [⟨⟨0, 0, 1, [2, 3], [1, 3]⟩, ⟨0, 0, 1, [2], [1]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [2, 3], [1, 2, 3]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 1], [1]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [1]⟩]
theorem edge29_is_retirable : P true normal29 [2, 3] origins29 proof29 = true := by decide
#print axioms edge29_is_retirable
def normal30 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [1, 3], []⟩)]
def origins30 : List Row := [⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [1, 3, 2], [2]⟩]
def proof30 : List Witness := [⟨⟨0, 0, 1, [1, 3], [2, 3]⟩, ⟨0, 0, 1, [1], [2]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [1, 3], [2, 1, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1, 3]⟩, ⟨⟨0, 0, 1, [1, 3, 2], [2]⟩, ⟨0, 0, 1, [1, 3], []⟩, false, [2]⟩]
theorem edge30_is_retirable : P true normal30 [1, 3] origins30 proof30 = true := by decide
#print axioms edge30_is_retirable
def normal31 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [2, 3], []⟩)]
def origins31 : List Row := [⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [2, 3, 2], [2]⟩]
def proof31 : List Witness := [⟨⟨0, 0, 1, [2, 3], [2, 3]⟩, ⟨0, 0, 1, [], []⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3], [2, 2, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2, 3]⟩, ⟨⟨0, 0, 1, [2, 3, 2], [2]⟩, ⟨0, 0, 1, [2, 3], []⟩, false, [2]⟩]
theorem edge31_is_retirable : P true normal31 [2, 3] origins31 proof31 = true := by decide
#print axioms edge31_is_retirable
def normal32 : List (Bool × Row) := [(false, ⟨0, 0, 1, [1], []⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [1], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [1, 3]⟩)]
def origins32 : List Row := [⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [1, 3], []⟩]
def proof32 : List Witness := [⟨⟨0, 0, 1, [1], []⟩, ⟨0, 0, 1, [1], []⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [1]⟩, ⟨0, 0, 1, [], []⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [1, 1]⟩, ⟨0, 0, 1, [], [1]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1], [2]⟩, ⟨0, 0, 1, [1], [2]⟩, false, []⟩, ⟨⟨0, 0, 1, [1], [2, 1]⟩, ⟨0, 0, 1, [], [2]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [1, 3], []⟩, ⟨0, 1, 0, [], [1, 3]⟩, true, []⟩]
theorem edge32_is_retirable : P true normal32 [1] origins32 proof32 = true := by decide
#print axioms edge32_is_retirable
def normal33 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], []⟩), (false, ⟨0, 0, 1, [2], [1]⟩), (false, ⟨0, 0, 1, [], [1]⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (true, ⟨0, 1, 0, [], [2, 3]⟩)]
def origins33 : List Row := [⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [2, 3], []⟩]
def proof33 : List Witness := [⟨⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], []⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1]⟩, ⟨0, 0, 1, [2], [1]⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [1, 2]⟩, ⟨0, 0, 1, [], [1]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2, 3], []⟩, ⟨0, 1, 0, [], [2, 3]⟩, true, []⟩]
theorem edge33_is_retirable : P true normal33 [2] origins33 proof33 = true := by decide
#print axioms edge33_is_retirable
end NormalBackedDemand.Observed
