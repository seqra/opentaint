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

namespace NormalBackedDemand.AllHelpersV2
-- target cde552d8e8faa68e0ebd0e7c6069650dcb839ca7406c60044f217ae11645c95a
def normal0 : List (Bool × Row) := [(false, ⟨0, 0, 1, [3], []⟩), (false, ⟨0, 0, 1, [3], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [3]⟩), (true, ⟨0, 1, 0, [], [3, 1]⟩)]
def origins0 : List Row := [⟨0, 0, 1, [3], []⟩, ⟨0, 0, 1, [3], [2]⟩, ⟨0, 0, 1, [3], [2, 3]⟩, ⟨0, 0, 1, [3], [3]⟩, ⟨0, 0, 1, [3], [3, 3]⟩, ⟨0, 0, 1, [3, 1], []⟩]
def proof0 : List Witness := [⟨⟨0, 0, 1, [3], []⟩, ⟨0, 0, 1, [3], []⟩, false, []⟩, ⟨⟨0, 0, 1, [3], [2]⟩, ⟨0, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨0, 0, 1, [3], [2, 3]⟩, ⟨0, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [3], [3]⟩, ⟨0, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨0, 0, 1, [3], [3, 3]⟩, ⟨0, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨0, 0, 1, [3, 1], []⟩, ⟨0, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_0 : P true normal0 [3] origins0 proof0 = true := by decide
-- target 8c28cbc8c7fcb2cf9d4d3c27efed8e199fa5e5b36fb8425a4d02d8c7e9f1da2d
def normal1 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], [3]⟩), (false, ⟨0, 0, 1, [], [3]⟩), (false, ⟨0, 0, 1, [2, 1], []⟩)]
def origins1 : List Row := [⟨0, 0, 1, [2, 1], [3, 1]⟩, ⟨0, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨0, 0, 1, [2, 1, 3], [3]⟩]
def proof1 : List Witness := [⟨⟨0, 0, 1, [2, 1], [3, 1]⟩, ⟨0, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨0, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨0, 0, 1, [2, 1, 3], [3]⟩, ⟨0, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_1 : P true normal1 [2, 1] origins1 proof1 = true := by decide
-- target dd126d17395664be292a74a0bd3e32eb2e704f34af682b6958b42f2502e64219
def normal2 : List (Bool × Row) := [(false, ⟨0, 0, 1, [3], [2]⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [3, 1], []⟩)]
def origins2 : List Row := [⟨0, 0, 1, [3, 1], [2, 1]⟩, ⟨0, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨0, 0, 1, [3, 1, 2], [2]⟩]
def proof2 : List Witness := [⟨⟨0, 0, 1, [3, 1], [2, 1]⟩, ⟨0, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨0, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨0, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨0, 0, 1, [3, 1, 2], [2]⟩, ⟨0, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_2 : P true normal2 [3, 1] origins2 proof2 = true := by decide
-- target ad58cab0c4b24b0f6a6d90cd615b107825aa558b97f3121918d19b1100b19949
def normal3 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [3]⟩), (false, ⟨0, 0, 1, [3, 1], []⟩)]
def origins3 : List Row := [⟨0, 0, 1, [3, 1], [3, 1]⟩, ⟨0, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨0, 0, 1, [3, 1, 3], [3]⟩]
def proof3 : List Witness := [⟨⟨0, 0, 1, [3, 1], [3, 1]⟩, ⟨0, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨0, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨0, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨0, 0, 1, [3, 1, 3], [3]⟩, ⟨0, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_3 : P true normal3 [3, 1] origins3 proof3 = true := by decide
-- target 4378d2858903d546e49efff05835fb72b48a5c3cabc81c75173a797e45a3a929
def normal4 : List (Bool × Row) := [(false, ⟨0, 0, 1, [2], []⟩), (false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [2], [3]⟩), (false, ⟨0, 0, 1, [], [3]⟩), (true, ⟨0, 1, 0, [], [2, 1]⟩)]
def origins4 : List Row := [⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [2], [3]⟩, ⟨0, 0, 1, [2], [3, 2]⟩, ⟨0, 0, 1, [2, 1], []⟩]
def proof4 : List Witness := [⟨⟨0, 0, 1, [2], []⟩, ⟨0, 0, 1, [2], []⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [2]⟩, ⟨0, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [2, 2]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2], [3]⟩, ⟨0, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨0, 0, 1, [2], [3, 2]⟩, ⟨0, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨0, 0, 1, [2, 1], []⟩, ⟨0, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_4 : P true normal4 [2] origins4 proof4 = true := by decide
-- target e0f952cda8289cf47b61f3fb68857110dac36f97dd14a68eba711ba3c7d0fcfc
def normal5 : List (Bool × Row) := [(false, ⟨0, 0, 1, [], []⟩), (false, ⟨0, 0, 1, [], [2]⟩), (false, ⟨0, 0, 1, [2, 1], []⟩)]
def origins5 : List Row := [⟨0, 0, 1, [2, 1], [2, 1]⟩, ⟨0, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨0, 0, 1, [2, 1, 2], [2]⟩]
def proof5 : List Witness := [⟨⟨0, 0, 1, [2, 1], [2, 1]⟩, ⟨0, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨0, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨0, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨0, 0, 1, [2, 1, 2], [2]⟩, ⟨0, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_5 : P true normal5 [2, 1] origins5 proof5 = true := by decide
-- target 3dfdf79fa3706fd46f4c82cf4ec0966fa56b95554b4986b3873ec849e37aee4c
def normal6 : List (Bool × Row) := [(false, ⟨1, 0, 1, [2], []⟩), (false, ⟨1, 0, 1, [], []⟩), (false, ⟨1, 0, 1, [], [2]⟩), (false, ⟨1, 0, 1, [2], [3]⟩), (false, ⟨1, 0, 1, [], [3]⟩), (true, ⟨1, 1, 0, [], [2, 1]⟩)]
def origins6 : List Row := [⟨1, 0, 1, [2], []⟩, ⟨1, 0, 1, [2], [2]⟩, ⟨1, 0, 1, [2], [2, 2]⟩, ⟨1, 0, 1, [2], [3]⟩, ⟨1, 0, 1, [2], [3, 2]⟩, ⟨1, 0, 1, [2, 1], []⟩]
def proof6 : List Witness := [⟨⟨1, 0, 1, [2], []⟩, ⟨1, 0, 1, [2], []⟩, false, []⟩, ⟨⟨1, 0, 1, [2], [2]⟩, ⟨1, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨1, 0, 1, [2], [2, 2]⟩, ⟨1, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨1, 0, 1, [2], [3]⟩, ⟨1, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨1, 0, 1, [2], [3, 2]⟩, ⟨1, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨1, 0, 1, [2, 1], []⟩, ⟨1, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_6 : P true normal6 [2] origins6 proof6 = true := by decide
-- target 999826ab024e6409cd6cb51d483d45b0d2595a2023c37004c744895c7ae9255f
def normal7 : List (Bool × Row) := [(false, ⟨1, 0, 1, [3], [2]⟩), (false, ⟨1, 0, 1, [], [2]⟩), (false, ⟨1, 0, 1, [3, 1], []⟩)]
def origins7 : List Row := [⟨1, 0, 1, [3, 1], [2, 1]⟩, ⟨1, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨1, 0, 1, [3, 1, 2], [2]⟩]
def proof7 : List Witness := [⟨⟨1, 0, 1, [3, 1], [2, 1]⟩, ⟨1, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨1, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨1, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨1, 0, 1, [3, 1, 2], [2]⟩, ⟨1, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_7 : P true normal7 [3, 1] origins7 proof7 = true := by decide
-- target e074ff5440ac09f75a4d8320bc7af1dc91284ef9868364dbbe4dec6d64f0a0a3
def normal8 : List (Bool × Row) := [(false, ⟨1, 0, 1, [2], [3]⟩), (false, ⟨1, 0, 1, [], [3]⟩), (false, ⟨1, 0, 1, [2, 1], []⟩)]
def origins8 : List Row := [⟨1, 0, 1, [2, 1], [3, 1]⟩, ⟨1, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨1, 0, 1, [2, 1, 3], [3]⟩]
def proof8 : List Witness := [⟨⟨1, 0, 1, [2, 1], [3, 1]⟩, ⟨1, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨1, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨1, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨1, 0, 1, [2, 1, 3], [3]⟩, ⟨1, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_8 : P true normal8 [2, 1] origins8 proof8 = true := by decide
-- target ae09df3ca6d0cfc88db0273bc97d820c053b105d1d9f03105dc7c9f6a4012808
def normal9 : List (Bool × Row) := [(false, ⟨1, 0, 1, [3], []⟩), (false, ⟨1, 0, 1, [3], [2]⟩), (false, ⟨1, 0, 1, [], [2]⟩), (false, ⟨1, 0, 1, [], []⟩), (false, ⟨1, 0, 1, [], [3]⟩), (true, ⟨1, 1, 0, [], [3, 1]⟩)]
def origins9 : List Row := [⟨1, 0, 1, [3], []⟩, ⟨1, 0, 1, [3], [2]⟩, ⟨1, 0, 1, [3], [2, 3]⟩, ⟨1, 0, 1, [3], [3]⟩, ⟨1, 0, 1, [3], [3, 3]⟩, ⟨1, 0, 1, [3, 1], []⟩]
def proof9 : List Witness := [⟨⟨1, 0, 1, [3], []⟩, ⟨1, 0, 1, [3], []⟩, false, []⟩, ⟨⟨1, 0, 1, [3], [2]⟩, ⟨1, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨1, 0, 1, [3], [2, 3]⟩, ⟨1, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨1, 0, 1, [3], [3]⟩, ⟨1, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨1, 0, 1, [3], [3, 3]⟩, ⟨1, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨1, 0, 1, [3, 1], []⟩, ⟨1, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_9 : P true normal9 [3] origins9 proof9 = true := by decide
-- target 68a4460f98519039f820afe79720066f948953c936c4b73734f37a20f04ab003
def normal10 : List (Bool × Row) := [(false, ⟨1, 0, 1, [], []⟩), (false, ⟨1, 0, 1, [], [3]⟩), (false, ⟨1, 0, 1, [3, 1], []⟩)]
def origins10 : List Row := [⟨1, 0, 1, [3, 1], [3, 1]⟩, ⟨1, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨1, 0, 1, [3, 1, 3], [3]⟩]
def proof10 : List Witness := [⟨⟨1, 0, 1, [3, 1], [3, 1]⟩, ⟨1, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨1, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨1, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨1, 0, 1, [3, 1, 3], [3]⟩, ⟨1, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_10 : P true normal10 [3, 1] origins10 proof10 = true := by decide
-- target c6ca24d9cb01ec778cddae955b99e6b8bfe2ac2d6cb6ba9456b7b708388d9d8f
def normal11 : List (Bool × Row) := [(false, ⟨1, 0, 1, [], []⟩), (false, ⟨1, 0, 1, [], [2]⟩), (false, ⟨1, 0, 1, [2, 1], []⟩)]
def origins11 : List Row := [⟨1, 0, 1, [2, 1], [2, 1]⟩, ⟨1, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨1, 0, 1, [2, 1, 2], [2]⟩]
def proof11 : List Witness := [⟨⟨1, 0, 1, [2, 1], [2, 1]⟩, ⟨1, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨1, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨1, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨1, 0, 1, [2, 1, 2], [2]⟩, ⟨1, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_11 : P true normal11 [2, 1] origins11 proof11 = true := by decide
-- target bc0f23c3ca534a2a5abffd472e8bb73edea824a6f98f0a8c90f0e13e401a513f
def normal12 : List (Bool × Row) := [(false, ⟨2, 0, 1, [2], [3]⟩), (false, ⟨2, 0, 1, [], [3]⟩), (false, ⟨2, 0, 1, [2, 1], []⟩)]
def origins12 : List Row := [⟨2, 0, 1, [2, 1], [3, 1]⟩, ⟨2, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨2, 0, 1, [2, 1, 3], [3]⟩]
def proof12 : List Witness := [⟨⟨2, 0, 1, [2, 1], [3, 1]⟩, ⟨2, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨2, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨2, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨2, 0, 1, [2, 1, 3], [3]⟩, ⟨2, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_12 : P true normal12 [2, 1] origins12 proof12 = true := by decide
-- target cf005d06e9477c5aa4d20f75012823e71092b39a6be89db34259e8d6b11973a2
def normal13 : List (Bool × Row) := [(false, ⟨2, 0, 1, [], []⟩), (false, ⟨2, 0, 1, [], [3]⟩), (false, ⟨2, 0, 1, [3, 1], []⟩)]
def origins13 : List Row := [⟨2, 0, 1, [3, 1], [3, 1]⟩, ⟨2, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨2, 0, 1, [3, 1, 3], [3]⟩]
def proof13 : List Witness := [⟨⟨2, 0, 1, [3, 1], [3, 1]⟩, ⟨2, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨2, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨2, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨2, 0, 1, [3, 1, 3], [3]⟩, ⟨2, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_13 : P true normal13 [3, 1] origins13 proof13 = true := by decide
-- target 3133233bc1b0a28fa3f3a458ab8b519b83dd2ab902b0c6f126826c6d939f1149
def normal14 : List (Bool × Row) := [(false, ⟨2, 0, 1, [2], []⟩), (false, ⟨2, 0, 1, [], []⟩), (false, ⟨2, 0, 1, [], [2]⟩), (false, ⟨2, 0, 1, [2], [3]⟩), (false, ⟨2, 0, 1, [], [3]⟩), (true, ⟨2, 1, 0, [], [2, 1]⟩)]
def origins14 : List Row := [⟨2, 0, 1, [2], []⟩, ⟨2, 0, 1, [2], [2]⟩, ⟨2, 0, 1, [2], [2, 2]⟩, ⟨2, 0, 1, [2], [3]⟩, ⟨2, 0, 1, [2], [3, 2]⟩, ⟨2, 0, 1, [2, 1], []⟩]
def proof14 : List Witness := [⟨⟨2, 0, 1, [2], []⟩, ⟨2, 0, 1, [2], []⟩, false, []⟩, ⟨⟨2, 0, 1, [2], [2]⟩, ⟨2, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨2, 0, 1, [2], [2, 2]⟩, ⟨2, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨2, 0, 1, [2], [3]⟩, ⟨2, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨2, 0, 1, [2], [3, 2]⟩, ⟨2, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨2, 0, 1, [2, 1], []⟩, ⟨2, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_14 : P true normal14 [2] origins14 proof14 = true := by decide
-- target 4b863c204fc70d317ca1b43a47d3361f16be2532c71b479405b0d4a573a94e57
def normal15 : List (Bool × Row) := [(false, ⟨2, 0, 1, [3], []⟩), (false, ⟨2, 0, 1, [3], [2]⟩), (false, ⟨2, 0, 1, [], [2]⟩), (false, ⟨2, 0, 1, [], []⟩), (false, ⟨2, 0, 1, [], [3]⟩), (true, ⟨2, 1, 0, [], [3, 1]⟩)]
def origins15 : List Row := [⟨2, 0, 1, [3], []⟩, ⟨2, 0, 1, [3], [2]⟩, ⟨2, 0, 1, [3], [2, 3]⟩, ⟨2, 0, 1, [3], [3]⟩, ⟨2, 0, 1, [3], [3, 3]⟩, ⟨2, 0, 1, [3, 1], []⟩]
def proof15 : List Witness := [⟨⟨2, 0, 1, [3], []⟩, ⟨2, 0, 1, [3], []⟩, false, []⟩, ⟨⟨2, 0, 1, [3], [2]⟩, ⟨2, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨2, 0, 1, [3], [2, 3]⟩, ⟨2, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨2, 0, 1, [3], [3]⟩, ⟨2, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨2, 0, 1, [3], [3, 3]⟩, ⟨2, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨2, 0, 1, [3, 1], []⟩, ⟨2, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_15 : P true normal15 [3] origins15 proof15 = true := by decide
-- target f8138e3c4c825ac873bf98f5d9428642d1b93afb338303547a7b6ef12da4bea4
def normal16 : List (Bool × Row) := [(false, ⟨2, 0, 1, [], []⟩), (false, ⟨2, 0, 1, [], [2]⟩), (false, ⟨2, 0, 1, [2, 1], []⟩)]
def origins16 : List Row := [⟨2, 0, 1, [2, 1], [2, 1]⟩, ⟨2, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨2, 0, 1, [2, 1, 2], [2]⟩]
def proof16 : List Witness := [⟨⟨2, 0, 1, [2, 1], [2, 1]⟩, ⟨2, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨2, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨2, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨2, 0, 1, [2, 1, 2], [2]⟩, ⟨2, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_16 : P true normal16 [2, 1] origins16 proof16 = true := by decide
-- target 06caf3d19569da85550378fda701b6d31cd26f5f0b19af7275577a8f391a281d
def normal17 : List (Bool × Row) := [(false, ⟨2, 0, 1, [3], [2]⟩), (false, ⟨2, 0, 1, [], [2]⟩), (false, ⟨2, 0, 1, [3, 1], []⟩)]
def origins17 : List Row := [⟨2, 0, 1, [3, 1], [2, 1]⟩, ⟨2, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨2, 0, 1, [3, 1, 2], [2]⟩]
def proof17 : List Witness := [⟨⟨2, 0, 1, [3, 1], [2, 1]⟩, ⟨2, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨2, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨2, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨2, 0, 1, [3, 1, 2], [2]⟩, ⟨2, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_17 : P true normal17 [3, 1] origins17 proof17 = true := by decide
-- target 54bd1c5fdd7138e309e0a248baafbbad6f9309c455598fcc54229f5002dea650
def normal18 : List (Bool × Row) := [(false, ⟨3, 0, 1, [], []⟩), (false, ⟨3, 0, 1, [], [2]⟩), (false, ⟨3, 0, 1, [2, 1], []⟩)]
def origins18 : List Row := [⟨3, 0, 1, [2, 1], [2, 1]⟩, ⟨3, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨3, 0, 1, [2, 1, 2], [2]⟩]
def proof18 : List Witness := [⟨⟨3, 0, 1, [2, 1], [2, 1]⟩, ⟨3, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨3, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨3, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨3, 0, 1, [2, 1, 2], [2]⟩, ⟨3, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_18 : P true normal18 [2, 1] origins18 proof18 = true := by decide
-- target fbb337f6c32302ac3a64bf7cdfd54458cbc1891570951a8f0d279a517ce8e705
def normal19 : List (Bool × Row) := [(false, ⟨3, 0, 1, [2], []⟩), (false, ⟨3, 0, 1, [], []⟩), (false, ⟨3, 0, 1, [], [2]⟩), (false, ⟨3, 0, 1, [2], [3]⟩), (false, ⟨3, 0, 1, [], [3]⟩), (true, ⟨3, 1, 0, [], [2, 1]⟩)]
def origins19 : List Row := [⟨3, 0, 1, [2], []⟩, ⟨3, 0, 1, [2], [2]⟩, ⟨3, 0, 1, [2], [2, 2]⟩, ⟨3, 0, 1, [2], [3]⟩, ⟨3, 0, 1, [2], [3, 2]⟩, ⟨3, 0, 1, [2, 1], []⟩]
def proof19 : List Witness := [⟨⟨3, 0, 1, [2], []⟩, ⟨3, 0, 1, [2], []⟩, false, []⟩, ⟨⟨3, 0, 1, [2], [2]⟩, ⟨3, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨3, 0, 1, [2], [2, 2]⟩, ⟨3, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨3, 0, 1, [2], [3]⟩, ⟨3, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨3, 0, 1, [2], [3, 2]⟩, ⟨3, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨3, 0, 1, [2, 1], []⟩, ⟨3, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_19 : P true normal19 [2] origins19 proof19 = true := by decide
-- target 56e68b4cfe2c082f514f8a9a45c61cfdee8a972b0d9be3044e147e2d2f377ac5
def normal20 : List (Bool × Row) := [(false, ⟨3, 0, 1, [3], [2]⟩), (false, ⟨3, 0, 1, [], [2]⟩), (false, ⟨3, 0, 1, [3, 1], []⟩)]
def origins20 : List Row := [⟨3, 0, 1, [3, 1], [2, 1]⟩, ⟨3, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨3, 0, 1, [3, 1, 2], [2]⟩]
def proof20 : List Witness := [⟨⟨3, 0, 1, [3, 1], [2, 1]⟩, ⟨3, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨3, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨3, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨3, 0, 1, [3, 1, 2], [2]⟩, ⟨3, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_20 : P true normal20 [3, 1] origins20 proof20 = true := by decide
-- target e3147971ab90f9afe355c2f98057bcac72fc9bbf3fb4f551142a854ff6380528
def normal21 : List (Bool × Row) := [(false, ⟨3, 0, 1, [], []⟩), (false, ⟨3, 0, 1, [], [3]⟩), (false, ⟨3, 0, 1, [3, 1], []⟩)]
def origins21 : List Row := [⟨3, 0, 1, [3, 1], [3, 1]⟩, ⟨3, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨3, 0, 1, [3, 1, 3], [3]⟩]
def proof21 : List Witness := [⟨⟨3, 0, 1, [3, 1], [3, 1]⟩, ⟨3, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨3, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨3, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨3, 0, 1, [3, 1, 3], [3]⟩, ⟨3, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_21 : P true normal21 [3, 1] origins21 proof21 = true := by decide
-- target 40b144102e2fdacabd4479bb79368aab38c5c950be5c0c78069bbe1fd336cb48
def normal22 : List (Bool × Row) := [(false, ⟨3, 0, 1, [2], [3]⟩), (false, ⟨3, 0, 1, [], [3]⟩), (false, ⟨3, 0, 1, [2, 1], []⟩)]
def origins22 : List Row := [⟨3, 0, 1, [2, 1], [3, 1]⟩, ⟨3, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨3, 0, 1, [2, 1, 3], [3]⟩]
def proof22 : List Witness := [⟨⟨3, 0, 1, [2, 1], [3, 1]⟩, ⟨3, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨3, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨3, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨3, 0, 1, [2, 1, 3], [3]⟩, ⟨3, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_22 : P true normal22 [2, 1] origins22 proof22 = true := by decide
-- target 50ab1c08ce8794cefd344c1b7d9e020b058f9fd8291e4f2c72e2f8dd7b52a5a7
def normal23 : List (Bool × Row) := [(false, ⟨3, 0, 1, [3], []⟩), (false, ⟨3, 0, 1, [3], [2]⟩), (false, ⟨3, 0, 1, [], [2]⟩), (false, ⟨3, 0, 1, [], []⟩), (false, ⟨3, 0, 1, [], [3]⟩), (true, ⟨3, 1, 0, [], [3, 1]⟩)]
def origins23 : List Row := [⟨3, 0, 1, [3], []⟩, ⟨3, 0, 1, [3], [2]⟩, ⟨3, 0, 1, [3], [2, 3]⟩, ⟨3, 0, 1, [3], [3]⟩, ⟨3, 0, 1, [3], [3, 3]⟩, ⟨3, 0, 1, [3, 1], []⟩]
def proof23 : List Witness := [⟨⟨3, 0, 1, [3], []⟩, ⟨3, 0, 1, [3], []⟩, false, []⟩, ⟨⟨3, 0, 1, [3], [2]⟩, ⟨3, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨3, 0, 1, [3], [2, 3]⟩, ⟨3, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨3, 0, 1, [3], [3]⟩, ⟨3, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨3, 0, 1, [3], [3, 3]⟩, ⟨3, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨3, 0, 1, [3, 1], []⟩, ⟨3, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_23 : P true normal23 [3] origins23 proof23 = true := by decide
-- target 44f9afd8eb340372458f53c42865dfdb2807d49b332cb4048a55986c0d6b850d
def normal24 : List (Bool × Row) := [(false, ⟨4, 0, 1, [2], []⟩), (false, ⟨4, 0, 1, [], []⟩), (false, ⟨4, 0, 1, [], [2]⟩), (false, ⟨4, 0, 1, [2], [3]⟩), (false, ⟨4, 0, 1, [], [3]⟩), (true, ⟨4, 1, 0, [], [2, 1]⟩)]
def origins24 : List Row := [⟨4, 0, 1, [2], []⟩, ⟨4, 0, 1, [2], [2]⟩, ⟨4, 0, 1, [2], [2, 2]⟩, ⟨4, 0, 1, [2], [3]⟩, ⟨4, 0, 1, [2], [3, 2]⟩, ⟨4, 0, 1, [2, 1], []⟩]
def proof24 : List Witness := [⟨⟨4, 0, 1, [2], []⟩, ⟨4, 0, 1, [2], []⟩, false, []⟩, ⟨⟨4, 0, 1, [2], [2]⟩, ⟨4, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨4, 0, 1, [2], [2, 2]⟩, ⟨4, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨4, 0, 1, [2], [3]⟩, ⟨4, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨4, 0, 1, [2], [3, 2]⟩, ⟨4, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨4, 0, 1, [2, 1], []⟩, ⟨4, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_24 : P true normal24 [2] origins24 proof24 = true := by decide
-- target 52e4ac0a34473563cfb313bf7dc93ab76f407c242389869327eedafc417c2dad
def normal25 : List (Bool × Row) := [(false, ⟨4, 0, 1, [3], [2]⟩), (false, ⟨4, 0, 1, [], [2]⟩), (false, ⟨4, 0, 1, [3, 1], []⟩)]
def origins25 : List Row := [⟨4, 0, 1, [3, 1], [2, 1]⟩, ⟨4, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨4, 0, 1, [3, 1, 2], [2]⟩]
def proof25 : List Witness := [⟨⟨4, 0, 1, [3, 1], [2, 1]⟩, ⟨4, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨4, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨4, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨4, 0, 1, [3, 1, 2], [2]⟩, ⟨4, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_25 : P true normal25 [3, 1] origins25 proof25 = true := by decide
-- target 38a1c09f0c2b12792827c8ce694450406e10f67d427e51d78304d9dfe18d28ef
def normal26 : List (Bool × Row) := [(false, ⟨4, 0, 1, [], []⟩), (false, ⟨4, 0, 1, [], [2]⟩), (false, ⟨4, 0, 1, [2, 1], []⟩)]
def origins26 : List Row := [⟨4, 0, 1, [2, 1], [2, 1]⟩, ⟨4, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨4, 0, 1, [2, 1, 2], [2]⟩]
def proof26 : List Witness := [⟨⟨4, 0, 1, [2, 1], [2, 1]⟩, ⟨4, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨4, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨4, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨4, 0, 1, [2, 1, 2], [2]⟩, ⟨4, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_26 : P true normal26 [2, 1] origins26 proof26 = true := by decide
-- target afa577532da4f7ac7b29e6563359d1b12e6fccd3b8937a0547a4f70f5a89fcaf
def normal27 : List (Bool × Row) := [(false, ⟨4, 0, 1, [2], [3]⟩), (false, ⟨4, 0, 1, [], [3]⟩), (false, ⟨4, 0, 1, [2, 1], []⟩)]
def origins27 : List Row := [⟨4, 0, 1, [2, 1], [3, 1]⟩, ⟨4, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨4, 0, 1, [2, 1, 3], [3]⟩]
def proof27 : List Witness := [⟨⟨4, 0, 1, [2, 1], [3, 1]⟩, ⟨4, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨4, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨4, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨4, 0, 1, [2, 1, 3], [3]⟩, ⟨4, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_27 : P true normal27 [2, 1] origins27 proof27 = true := by decide
-- target 851e1ae5d287f7c4dcc72e79bd7ca3da378d71528784afbe7f215f00a913b1b8
def normal28 : List (Bool × Row) := [(false, ⟨4, 0, 1, [3], []⟩), (false, ⟨4, 0, 1, [3], [2]⟩), (false, ⟨4, 0, 1, [], [2]⟩), (false, ⟨4, 0, 1, [], []⟩), (false, ⟨4, 0, 1, [], [3]⟩), (true, ⟨4, 1, 0, [], [3, 1]⟩)]
def origins28 : List Row := [⟨4, 0, 1, [3], []⟩, ⟨4, 0, 1, [3], [2]⟩, ⟨4, 0, 1, [3], [2, 3]⟩, ⟨4, 0, 1, [3], [3]⟩, ⟨4, 0, 1, [3], [3, 3]⟩, ⟨4, 0, 1, [3, 1], []⟩]
def proof28 : List Witness := [⟨⟨4, 0, 1, [3], []⟩, ⟨4, 0, 1, [3], []⟩, false, []⟩, ⟨⟨4, 0, 1, [3], [2]⟩, ⟨4, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨4, 0, 1, [3], [2, 3]⟩, ⟨4, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨4, 0, 1, [3], [3]⟩, ⟨4, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨4, 0, 1, [3], [3, 3]⟩, ⟨4, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨4, 0, 1, [3, 1], []⟩, ⟨4, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_28 : P true normal28 [3] origins28 proof28 = true := by decide
-- target afb592c226876bf31ffc1065f7073a5a58701524a2f21a2b71bdcac76106b42b
def normal29 : List (Bool × Row) := [(false, ⟨4, 0, 1, [], []⟩), (false, ⟨4, 0, 1, [], [3]⟩), (false, ⟨4, 0, 1, [3, 1], []⟩)]
def origins29 : List Row := [⟨4, 0, 1, [3, 1], [3, 1]⟩, ⟨4, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨4, 0, 1, [3, 1, 3], [3]⟩]
def proof29 : List Witness := [⟨⟨4, 0, 1, [3, 1], [3, 1]⟩, ⟨4, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨4, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨4, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨4, 0, 1, [3, 1, 3], [3]⟩, ⟨4, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_29 : P true normal29 [3, 1] origins29 proof29 = true := by decide
-- target f8ec55d151e23d1d3d4ea067fed4a4feaa62bc9ce8ab585b923939fb271c5df4
def normal30 : List (Bool × Row) := [(false, ⟨5, 0, 1, [3], [2]⟩), (false, ⟨5, 0, 1, [], [2]⟩), (false, ⟨5, 0, 1, [3, 1], []⟩)]
def origins30 : List Row := [⟨5, 0, 1, [3, 1], [2, 1]⟩, ⟨5, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨5, 0, 1, [3, 1, 2], [2]⟩]
def proof30 : List Witness := [⟨⟨5, 0, 1, [3, 1], [2, 1]⟩, ⟨5, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨5, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨5, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨5, 0, 1, [3, 1, 2], [2]⟩, ⟨5, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_30 : P true normal30 [3, 1] origins30 proof30 = true := by decide
-- target f44e77797dff7ea59937539f6354843c6a87a6c9117853896836178a631456d5
def normal31 : List (Bool × Row) := [(false, ⟨5, 0, 1, [], []⟩), (false, ⟨5, 0, 1, [], [2]⟩), (false, ⟨5, 0, 1, [2, 1], []⟩)]
def origins31 : List Row := [⟨5, 0, 1, [2, 1], [2, 1]⟩, ⟨5, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨5, 0, 1, [2, 1, 2], [2]⟩]
def proof31 : List Witness := [⟨⟨5, 0, 1, [2, 1], [2, 1]⟩, ⟨5, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨5, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨5, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨5, 0, 1, [2, 1, 2], [2]⟩, ⟨5, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_31 : P true normal31 [2, 1] origins31 proof31 = true := by decide
-- target 7edcf33c76c7b9122e05d5fb39ee8ba478193aacb4e6240e135ff64ab6654f89
def normal32 : List (Bool × Row) := [(false, ⟨5, 0, 1, [2], []⟩), (false, ⟨5, 0, 1, [], []⟩), (false, ⟨5, 0, 1, [], [2]⟩), (false, ⟨5, 0, 1, [2], [3]⟩), (false, ⟨5, 0, 1, [], [3]⟩), (true, ⟨5, 1, 0, [], [2, 1]⟩)]
def origins32 : List Row := [⟨5, 0, 1, [2], []⟩, ⟨5, 0, 1, [2], [2]⟩, ⟨5, 0, 1, [2], [2, 2]⟩, ⟨5, 0, 1, [2], [3]⟩, ⟨5, 0, 1, [2], [3, 2]⟩, ⟨5, 0, 1, [2, 1], []⟩]
def proof32 : List Witness := [⟨⟨5, 0, 1, [2], []⟩, ⟨5, 0, 1, [2], []⟩, false, []⟩, ⟨⟨5, 0, 1, [2], [2]⟩, ⟨5, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨5, 0, 1, [2], [2, 2]⟩, ⟨5, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨5, 0, 1, [2], [3]⟩, ⟨5, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨5, 0, 1, [2], [3, 2]⟩, ⟨5, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨5, 0, 1, [2, 1], []⟩, ⟨5, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_32 : P true normal32 [2] origins32 proof32 = true := by decide
-- target c4e06b2bcaf0fe39071cd24fefc07669a5ea85c3a851bd1276aa46338d5bbf58
def normal33 : List (Bool × Row) := [(false, ⟨5, 0, 1, [3], []⟩), (false, ⟨5, 0, 1, [3], [2]⟩), (false, ⟨5, 0, 1, [], [2]⟩), (false, ⟨5, 0, 1, [], []⟩), (false, ⟨5, 0, 1, [], [3]⟩), (true, ⟨5, 1, 0, [], [3, 1]⟩)]
def origins33 : List Row := [⟨5, 0, 1, [3], []⟩, ⟨5, 0, 1, [3], [2]⟩, ⟨5, 0, 1, [3], [2, 3]⟩, ⟨5, 0, 1, [3], [3]⟩, ⟨5, 0, 1, [3], [3, 3]⟩, ⟨5, 0, 1, [3, 1], []⟩]
def proof33 : List Witness := [⟨⟨5, 0, 1, [3], []⟩, ⟨5, 0, 1, [3], []⟩, false, []⟩, ⟨⟨5, 0, 1, [3], [2]⟩, ⟨5, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨5, 0, 1, [3], [2, 3]⟩, ⟨5, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨5, 0, 1, [3], [3]⟩, ⟨5, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨5, 0, 1, [3], [3, 3]⟩, ⟨5, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨5, 0, 1, [3, 1], []⟩, ⟨5, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_33 : P true normal33 [3] origins33 proof33 = true := by decide
-- target 6ebafd3e49a433b5ea5198af5807a7c1272bf4341c34e8f2ac84fd8378842d1b
def normal34 : List (Bool × Row) := [(false, ⟨5, 0, 1, [2], [3]⟩), (false, ⟨5, 0, 1, [], [3]⟩), (false, ⟨5, 0, 1, [2, 1], []⟩)]
def origins34 : List Row := [⟨5, 0, 1, [2, 1], [3, 1]⟩, ⟨5, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨5, 0, 1, [2, 1, 3], [3]⟩]
def proof34 : List Witness := [⟨⟨5, 0, 1, [2, 1], [3, 1]⟩, ⟨5, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨5, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨5, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨5, 0, 1, [2, 1, 3], [3]⟩, ⟨5, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_34 : P true normal34 [2, 1] origins34 proof34 = true := by decide
-- target f79c525579da7904824ffb5933ca358bd9310adae69cfc292c284b52e181672c
def normal35 : List (Bool × Row) := [(false, ⟨5, 0, 1, [], []⟩), (false, ⟨5, 0, 1, [], [3]⟩), (false, ⟨5, 0, 1, [3, 1], []⟩)]
def origins35 : List Row := [⟨5, 0, 1, [3, 1], [3, 1]⟩, ⟨5, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨5, 0, 1, [3, 1, 3], [3]⟩]
def proof35 : List Witness := [⟨⟨5, 0, 1, [3, 1], [3, 1]⟩, ⟨5, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨5, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨5, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨5, 0, 1, [3, 1, 3], [3]⟩, ⟨5, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_35 : P true normal35 [3, 1] origins35 proof35 = true := by decide
-- target fb2c18679e6fb87bed0cb20408c3b7ed1df93936d0e3e387a4d528eb9f1724f1
def normal36 : List (Bool × Row) := [(false, ⟨6, 0, 1, [], []⟩), (false, ⟨6, 0, 1, [], [2]⟩), (false, ⟨6, 0, 1, [2, 1], []⟩)]
def origins36 : List Row := [⟨6, 0, 1, [2, 1], [2, 1]⟩, ⟨6, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨6, 0, 1, [2, 1, 2], [2]⟩]
def proof36 : List Witness := [⟨⟨6, 0, 1, [2, 1], [2, 1]⟩, ⟨6, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨6, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨6, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨6, 0, 1, [2, 1, 2], [2]⟩, ⟨6, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_36 : P true normal36 [2, 1] origins36 proof36 = true := by decide
-- target 44348ad33e4864a2a1833fd1ad1cb7506922c8d06a612c72aeac4720cffcec4a
def normal37 : List (Bool × Row) := [(false, ⟨6, 0, 1, [2], [3]⟩), (false, ⟨6, 0, 1, [], [3]⟩), (false, ⟨6, 0, 1, [2, 1], []⟩)]
def origins37 : List Row := [⟨6, 0, 1, [2, 1], [3, 1]⟩, ⟨6, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨6, 0, 1, [2, 1, 3], [3]⟩]
def proof37 : List Witness := [⟨⟨6, 0, 1, [2, 1], [3, 1]⟩, ⟨6, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨6, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨6, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨6, 0, 1, [2, 1, 3], [3]⟩, ⟨6, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_37 : P true normal37 [2, 1] origins37 proof37 = true := by decide
-- target 56ff1ce600d47168a19bfeaa026ae6587df452acbc6267a496f2affe2f8a1209
def normal38 : List (Bool × Row) := [(false, ⟨6, 0, 1, [2], []⟩), (false, ⟨6, 0, 1, [], []⟩), (false, ⟨6, 0, 1, [], [2]⟩), (false, ⟨6, 0, 1, [2], [3]⟩), (false, ⟨6, 0, 1, [], [3]⟩), (true, ⟨6, 1, 0, [], [2, 1]⟩)]
def origins38 : List Row := [⟨6, 0, 1, [2], []⟩, ⟨6, 0, 1, [2], [2]⟩, ⟨6, 0, 1, [2], [2, 2]⟩, ⟨6, 0, 1, [2], [3]⟩, ⟨6, 0, 1, [2], [3, 2]⟩, ⟨6, 0, 1, [2, 1], []⟩]
def proof38 : List Witness := [⟨⟨6, 0, 1, [2], []⟩, ⟨6, 0, 1, [2], []⟩, false, []⟩, ⟨⟨6, 0, 1, [2], [2]⟩, ⟨6, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨6, 0, 1, [2], [2, 2]⟩, ⟨6, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨6, 0, 1, [2], [3]⟩, ⟨6, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨6, 0, 1, [2], [3, 2]⟩, ⟨6, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨6, 0, 1, [2, 1], []⟩, ⟨6, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_38 : P true normal38 [2] origins38 proof38 = true := by decide
-- target f4393c40e1434284302b6c1ea8c32c318713c22e0c02a10090303ce4642117e4
def normal39 : List (Bool × Row) := [(false, ⟨6, 0, 1, [3], []⟩), (false, ⟨6, 0, 1, [3], [2]⟩), (false, ⟨6, 0, 1, [], [2]⟩), (false, ⟨6, 0, 1, [], []⟩), (false, ⟨6, 0, 1, [], [3]⟩), (true, ⟨6, 1, 0, [], [3, 1]⟩)]
def origins39 : List Row := [⟨6, 0, 1, [3], []⟩, ⟨6, 0, 1, [3], [2]⟩, ⟨6, 0, 1, [3], [2, 3]⟩, ⟨6, 0, 1, [3], [3]⟩, ⟨6, 0, 1, [3], [3, 3]⟩, ⟨6, 0, 1, [3, 1], []⟩]
def proof39 : List Witness := [⟨⟨6, 0, 1, [3], []⟩, ⟨6, 0, 1, [3], []⟩, false, []⟩, ⟨⟨6, 0, 1, [3], [2]⟩, ⟨6, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨6, 0, 1, [3], [2, 3]⟩, ⟨6, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨6, 0, 1, [3], [3]⟩, ⟨6, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨6, 0, 1, [3], [3, 3]⟩, ⟨6, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨6, 0, 1, [3, 1], []⟩, ⟨6, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_39 : P true normal39 [3] origins39 proof39 = true := by decide
-- target c141fe0508561c4d1bf7f3bd08ce2a67fa4af5d12b41ba455164899104fba152
def normal40 : List (Bool × Row) := [(false, ⟨6, 0, 1, [3], [2]⟩), (false, ⟨6, 0, 1, [], [2]⟩), (false, ⟨6, 0, 1, [3, 1], []⟩)]
def origins40 : List Row := [⟨6, 0, 1, [3, 1], [2, 1]⟩, ⟨6, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨6, 0, 1, [3, 1, 2], [2]⟩]
def proof40 : List Witness := [⟨⟨6, 0, 1, [3, 1], [2, 1]⟩, ⟨6, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨6, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨6, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨6, 0, 1, [3, 1, 2], [2]⟩, ⟨6, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_40 : P true normal40 [3, 1] origins40 proof40 = true := by decide
-- target cc55df3d65cb2f5bdf1fa765e511ed6b2b70a1ba7d75199e2688827628ca7525
def normal41 : List (Bool × Row) := [(false, ⟨6, 0, 1, [], []⟩), (false, ⟨6, 0, 1, [], [3]⟩), (false, ⟨6, 0, 1, [3, 1], []⟩)]
def origins41 : List Row := [⟨6, 0, 1, [3, 1], [3, 1]⟩, ⟨6, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨6, 0, 1, [3, 1, 3], [3]⟩]
def proof41 : List Witness := [⟨⟨6, 0, 1, [3, 1], [3, 1]⟩, ⟨6, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨6, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨6, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨6, 0, 1, [3, 1, 3], [3]⟩, ⟨6, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_41 : P true normal41 [3, 1] origins41 proof41 = true := by decide
-- target 93c4a0a2ea0d649813a4459452f41c6352d36fd4514561c55bb865e8536adc21
def normal42 : List (Bool × Row) := [(false, ⟨7, 0, 1, [2], []⟩), (false, ⟨7, 0, 1, [], []⟩), (false, ⟨7, 0, 1, [], [2]⟩), (false, ⟨7, 0, 1, [2], [3]⟩), (false, ⟨7, 0, 1, [], [3]⟩), (true, ⟨7, 1, 0, [], [2, 1]⟩)]
def origins42 : List Row := [⟨7, 0, 1, [2], []⟩, ⟨7, 0, 1, [2], [2]⟩, ⟨7, 0, 1, [2], [2, 2]⟩, ⟨7, 0, 1, [2], [3]⟩, ⟨7, 0, 1, [2], [3, 2]⟩, ⟨7, 0, 1, [2, 1], []⟩]
def proof42 : List Witness := [⟨⟨7, 0, 1, [2], []⟩, ⟨7, 0, 1, [2], []⟩, false, []⟩, ⟨⟨7, 0, 1, [2], [2]⟩, ⟨7, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨7, 0, 1, [2], [2, 2]⟩, ⟨7, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨7, 0, 1, [2], [3]⟩, ⟨7, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨7, 0, 1, [2], [3, 2]⟩, ⟨7, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨7, 0, 1, [2, 1], []⟩, ⟨7, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_42 : P true normal42 [2] origins42 proof42 = true := by decide
-- target 46bf7e2c836f64c4f2bf81b093c0eff68d3f819fffbc83519a89028434b0f474
def normal43 : List (Bool × Row) := [(false, ⟨7, 0, 1, [], []⟩), (false, ⟨7, 0, 1, [], [2]⟩), (false, ⟨7, 0, 1, [2, 1], []⟩)]
def origins43 : List Row := [⟨7, 0, 1, [2, 1], [2, 1]⟩, ⟨7, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨7, 0, 1, [2, 1, 2], [2]⟩]
def proof43 : List Witness := [⟨⟨7, 0, 1, [2, 1], [2, 1]⟩, ⟨7, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨7, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨7, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨7, 0, 1, [2, 1, 2], [2]⟩, ⟨7, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_43 : P true normal43 [2, 1] origins43 proof43 = true := by decide
-- target b4db8aa08fbbb7bc120623832dccf94248cf1ad2ec4df4f4a01e1b933b447d8d
def normal44 : List (Bool × Row) := [(false, ⟨7, 0, 1, [], []⟩), (false, ⟨7, 0, 1, [], [3]⟩), (false, ⟨7, 0, 1, [3, 1], []⟩)]
def origins44 : List Row := [⟨7, 0, 1, [3, 1], [3, 1]⟩, ⟨7, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨7, 0, 1, [3, 1, 3], [3]⟩]
def proof44 : List Witness := [⟨⟨7, 0, 1, [3, 1], [3, 1]⟩, ⟨7, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨7, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨7, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨7, 0, 1, [3, 1, 3], [3]⟩, ⟨7, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_44 : P true normal44 [3, 1] origins44 proof44 = true := by decide
-- target 38163cc4d56ab6aebe9714b26be191c19795a706437b2448518fa8bb16dcc633
def normal45 : List (Bool × Row) := [(false, ⟨7, 0, 1, [3], []⟩), (false, ⟨7, 0, 1, [3], [2]⟩), (false, ⟨7, 0, 1, [], [2]⟩), (false, ⟨7, 0, 1, [], []⟩), (false, ⟨7, 0, 1, [], [3]⟩), (true, ⟨7, 1, 0, [], [3, 1]⟩)]
def origins45 : List Row := [⟨7, 0, 1, [3], []⟩, ⟨7, 0, 1, [3], [2]⟩, ⟨7, 0, 1, [3], [2, 3]⟩, ⟨7, 0, 1, [3], [3]⟩, ⟨7, 0, 1, [3], [3, 3]⟩, ⟨7, 0, 1, [3, 1], []⟩]
def proof45 : List Witness := [⟨⟨7, 0, 1, [3], []⟩, ⟨7, 0, 1, [3], []⟩, false, []⟩, ⟨⟨7, 0, 1, [3], [2]⟩, ⟨7, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨7, 0, 1, [3], [2, 3]⟩, ⟨7, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨7, 0, 1, [3], [3]⟩, ⟨7, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨7, 0, 1, [3], [3, 3]⟩, ⟨7, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨7, 0, 1, [3, 1], []⟩, ⟨7, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_45 : P true normal45 [3] origins45 proof45 = true := by decide
-- target 640c56e0cf82f9c3f11be9e1aa9baaf90efd63b19ab988dd4a717d179ad0b1f7
def normal46 : List (Bool × Row) := [(false, ⟨7, 0, 1, [2], [3]⟩), (false, ⟨7, 0, 1, [], [3]⟩), (false, ⟨7, 0, 1, [2, 1], []⟩)]
def origins46 : List Row := [⟨7, 0, 1, [2, 1], [3, 1]⟩, ⟨7, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨7, 0, 1, [2, 1, 3], [3]⟩]
def proof46 : List Witness := [⟨⟨7, 0, 1, [2, 1], [3, 1]⟩, ⟨7, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨7, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨7, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨7, 0, 1, [2, 1, 3], [3]⟩, ⟨7, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_46 : P true normal46 [2, 1] origins46 proof46 = true := by decide
-- target ba63b44612862cd1bfdd40aaaf4281e68eee4f37456396e77d1de53d777cccf2
def normal47 : List (Bool × Row) := [(false, ⟨7, 0, 1, [3], [2]⟩), (false, ⟨7, 0, 1, [], [2]⟩), (false, ⟨7, 0, 1, [3, 1], []⟩)]
def origins47 : List Row := [⟨7, 0, 1, [3, 1], [2, 1]⟩, ⟨7, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨7, 0, 1, [3, 1, 2], [2]⟩]
def proof47 : List Witness := [⟨⟨7, 0, 1, [3, 1], [2, 1]⟩, ⟨7, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨7, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨7, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨7, 0, 1, [3, 1, 2], [2]⟩, ⟨7, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_47 : P true normal47 [3, 1] origins47 proof47 = true := by decide
-- target 80869c2b3bc29a2c4636f562c5e1f8f38525d36e90435b3d6283ec295886f024
def normal48 : List (Bool × Row) := [(false, ⟨8, 0, 1, [3], []⟩), (false, ⟨8, 0, 1, [3], [2]⟩), (false, ⟨8, 0, 1, [], [2]⟩), (false, ⟨8, 0, 1, [], []⟩), (false, ⟨8, 0, 1, [], [3]⟩), (true, ⟨8, 1, 0, [], [3, 1]⟩)]
def origins48 : List Row := [⟨8, 0, 1, [3], []⟩, ⟨8, 0, 1, [3], [2]⟩, ⟨8, 0, 1, [3], [2, 3]⟩, ⟨8, 0, 1, [3], [3]⟩, ⟨8, 0, 1, [3], [3, 3]⟩, ⟨8, 0, 1, [3, 1], []⟩]
def proof48 : List Witness := [⟨⟨8, 0, 1, [3], []⟩, ⟨8, 0, 1, [3], []⟩, false, []⟩, ⟨⟨8, 0, 1, [3], [2]⟩, ⟨8, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨8, 0, 1, [3], [2, 3]⟩, ⟨8, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨8, 0, 1, [3], [3]⟩, ⟨8, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨8, 0, 1, [3], [3, 3]⟩, ⟨8, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨8, 0, 1, [3, 1], []⟩, ⟨8, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_48 : P true normal48 [3] origins48 proof48 = true := by decide
-- target ede380f6a3143bfcf8119a776996c82dab9b748e3b93e62aa99a373cd3fa3665
def normal49 : List (Bool × Row) := [(false, ⟨8, 0, 1, [2], []⟩), (false, ⟨8, 0, 1, [], []⟩), (false, ⟨8, 0, 1, [], [2]⟩), (false, ⟨8, 0, 1, [2], [3]⟩), (false, ⟨8, 0, 1, [], [3]⟩), (true, ⟨8, 1, 0, [], [2, 1]⟩)]
def origins49 : List Row := [⟨8, 0, 1, [2], []⟩, ⟨8, 0, 1, [2], [2]⟩, ⟨8, 0, 1, [2], [2, 2]⟩, ⟨8, 0, 1, [2], [3]⟩, ⟨8, 0, 1, [2], [3, 2]⟩, ⟨8, 0, 1, [2, 1], []⟩]
def proof49 : List Witness := [⟨⟨8, 0, 1, [2], []⟩, ⟨8, 0, 1, [2], []⟩, false, []⟩, ⟨⟨8, 0, 1, [2], [2]⟩, ⟨8, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨8, 0, 1, [2], [2, 2]⟩, ⟨8, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨8, 0, 1, [2], [3]⟩, ⟨8, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨8, 0, 1, [2], [3, 2]⟩, ⟨8, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨8, 0, 1, [2, 1], []⟩, ⟨8, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_49 : P true normal49 [2] origins49 proof49 = true := by decide
-- target b4d9f84c2ad4a82a4d7a758b38d3a2cd10828d8055d2c43be7ec956a759774ef
def normal50 : List (Bool × Row) := [(false, ⟨8, 0, 1, [2], [3]⟩), (false, ⟨8, 0, 1, [], [3]⟩), (false, ⟨8, 0, 1, [2, 1], []⟩)]
def origins50 : List Row := [⟨8, 0, 1, [2, 1], [3, 1]⟩, ⟨8, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨8, 0, 1, [2, 1, 3], [3]⟩]
def proof50 : List Witness := [⟨⟨8, 0, 1, [2, 1], [3, 1]⟩, ⟨8, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨8, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨8, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨8, 0, 1, [2, 1, 3], [3]⟩, ⟨8, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_50 : P true normal50 [2, 1] origins50 proof50 = true := by decide
-- target 2f82e7c628b18c0dd359ff4787f5991353dd37ad7ee33759b50e2fd46c207bd6
def normal51 : List (Bool × Row) := [(false, ⟨8, 0, 1, [3], [2]⟩), (false, ⟨8, 0, 1, [], [2]⟩), (false, ⟨8, 0, 1, [3, 1], []⟩)]
def origins51 : List Row := [⟨8, 0, 1, [3, 1], [2, 1]⟩, ⟨8, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨8, 0, 1, [3, 1, 2], [2]⟩]
def proof51 : List Witness := [⟨⟨8, 0, 1, [3, 1], [2, 1]⟩, ⟨8, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨8, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨8, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨8, 0, 1, [3, 1, 2], [2]⟩, ⟨8, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_51 : P true normal51 [3, 1] origins51 proof51 = true := by decide
-- target 87026b8d3c7b6197a307866f42ac8b4058faaec79080eb93da6b9d760977b8f4
def normal52 : List (Bool × Row) := [(false, ⟨8, 0, 1, [], []⟩), (false, ⟨8, 0, 1, [], [2]⟩), (false, ⟨8, 0, 1, [2, 1], []⟩)]
def origins52 : List Row := [⟨8, 0, 1, [2, 1], [2, 1]⟩, ⟨8, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨8, 0, 1, [2, 1, 2], [2]⟩]
def proof52 : List Witness := [⟨⟨8, 0, 1, [2, 1], [2, 1]⟩, ⟨8, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨8, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨8, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨8, 0, 1, [2, 1, 2], [2]⟩, ⟨8, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_52 : P true normal52 [2, 1] origins52 proof52 = true := by decide
-- target a6d3b733a336b494dfbb90d2ef5a369ff4ca2706c9d8b00302135d8eb83a1262
def normal53 : List (Bool × Row) := [(false, ⟨8, 0, 1, [], []⟩), (false, ⟨8, 0, 1, [], [3]⟩), (false, ⟨8, 0, 1, [3, 1], []⟩)]
def origins53 : List Row := [⟨8, 0, 1, [3, 1], [3, 1]⟩, ⟨8, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨8, 0, 1, [3, 1, 3], [3]⟩]
def proof53 : List Witness := [⟨⟨8, 0, 1, [3, 1], [3, 1]⟩, ⟨8, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨8, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨8, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨8, 0, 1, [3, 1, 3], [3]⟩, ⟨8, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_53 : P true normal53 [3, 1] origins53 proof53 = true := by decide
-- target 98df2103875b1e8f4ac9e82395fc4b259bbb2fa8f75cccf9a865515ec2bc8f15
def normal54 : List (Bool × Row) := [(false, ⟨9, 0, 1, [3], []⟩), (false, ⟨9, 0, 1, [3], [2]⟩), (false, ⟨9, 0, 1, [], [2]⟩), (false, ⟨9, 0, 1, [], []⟩), (false, ⟨9, 0, 1, [], [3]⟩), (true, ⟨9, 1, 0, [], [3, 1]⟩)]
def origins54 : List Row := [⟨9, 0, 1, [3], []⟩, ⟨9, 0, 1, [3], [2]⟩, ⟨9, 0, 1, [3], [2, 3]⟩, ⟨9, 0, 1, [3], [3]⟩, ⟨9, 0, 1, [3], [3, 3]⟩, ⟨9, 0, 1, [3, 1], []⟩]
def proof54 : List Witness := [⟨⟨9, 0, 1, [3], []⟩, ⟨9, 0, 1, [3], []⟩, false, []⟩, ⟨⟨9, 0, 1, [3], [2]⟩, ⟨9, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨9, 0, 1, [3], [2, 3]⟩, ⟨9, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨9, 0, 1, [3], [3]⟩, ⟨9, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨9, 0, 1, [3], [3, 3]⟩, ⟨9, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨9, 0, 1, [3, 1], []⟩, ⟨9, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_54 : P true normal54 [3] origins54 proof54 = true := by decide
-- target 2549fd25133a1baab2a3d85d97ada9d6892e13de4a8240f9443ccd7b75bcdab4
def normal55 : List (Bool × Row) := [(false, ⟨9, 0, 1, [3], [2]⟩), (false, ⟨9, 0, 1, [], [2]⟩), (false, ⟨9, 0, 1, [3, 1], []⟩)]
def origins55 : List Row := [⟨9, 0, 1, [3, 1], [2, 1]⟩, ⟨9, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨9, 0, 1, [3, 1, 2], [2]⟩]
def proof55 : List Witness := [⟨⟨9, 0, 1, [3, 1], [2, 1]⟩, ⟨9, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨9, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨9, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨9, 0, 1, [3, 1, 2], [2]⟩, ⟨9, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_55 : P true normal55 [3, 1] origins55 proof55 = true := by decide
-- target 0968bf9e5a984dece4be761d54423a2567b7b785d7507ec2bc776d52512661f8
def normal56 : List (Bool × Row) := [(false, ⟨9, 0, 1, [], []⟩), (false, ⟨9, 0, 1, [], [3]⟩), (false, ⟨9, 0, 1, [3, 1], []⟩)]
def origins56 : List Row := [⟨9, 0, 1, [3, 1], [3, 1]⟩, ⟨9, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨9, 0, 1, [3, 1, 3], [3]⟩]
def proof56 : List Witness := [⟨⟨9, 0, 1, [3, 1], [3, 1]⟩, ⟨9, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨9, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨9, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨9, 0, 1, [3, 1, 3], [3]⟩, ⟨9, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_56 : P true normal56 [3, 1] origins56 proof56 = true := by decide
-- target 27c7f6070dfbffca3e3605d647e31be2b8b004ffe2b945c08659031f3d8e31e4
def normal57 : List (Bool × Row) := [(false, ⟨9, 0, 1, [], []⟩), (false, ⟨9, 0, 1, [], [2]⟩), (false, ⟨9, 0, 1, [2, 1], []⟩)]
def origins57 : List Row := [⟨9, 0, 1, [2, 1], [2, 1]⟩, ⟨9, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨9, 0, 1, [2, 1, 2], [2]⟩]
def proof57 : List Witness := [⟨⟨9, 0, 1, [2, 1], [2, 1]⟩, ⟨9, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨9, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨9, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨9, 0, 1, [2, 1, 2], [2]⟩, ⟨9, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_57 : P true normal57 [2, 1] origins57 proof57 = true := by decide
-- target c4864b03b1a5a5aeb49a66e328ae49bd7c586a53bc6aa0143a3d1ab4e59d4397
def normal58 : List (Bool × Row) := [(false, ⟨9, 0, 1, [2], []⟩), (false, ⟨9, 0, 1, [], []⟩), (false, ⟨9, 0, 1, [], [2]⟩), (false, ⟨9, 0, 1, [2], [3]⟩), (false, ⟨9, 0, 1, [], [3]⟩), (true, ⟨9, 1, 0, [], [2, 1]⟩)]
def origins58 : List Row := [⟨9, 0, 1, [2], []⟩, ⟨9, 0, 1, [2], [2]⟩, ⟨9, 0, 1, [2], [2, 2]⟩, ⟨9, 0, 1, [2], [3]⟩, ⟨9, 0, 1, [2], [3, 2]⟩, ⟨9, 0, 1, [2, 1], []⟩]
def proof58 : List Witness := [⟨⟨9, 0, 1, [2], []⟩, ⟨9, 0, 1, [2], []⟩, false, []⟩, ⟨⟨9, 0, 1, [2], [2]⟩, ⟨9, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨9, 0, 1, [2], [2, 2]⟩, ⟨9, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨9, 0, 1, [2], [3]⟩, ⟨9, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨9, 0, 1, [2], [3, 2]⟩, ⟨9, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨9, 0, 1, [2, 1], []⟩, ⟨9, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_58 : P true normal58 [2] origins58 proof58 = true := by decide
-- target 7399ea451e2b27ba225e9e20b6eb0d45496ec0b67a40551568606c0e8d475c3c
def normal59 : List (Bool × Row) := [(false, ⟨9, 0, 1, [2], [3]⟩), (false, ⟨9, 0, 1, [], [3]⟩), (false, ⟨9, 0, 1, [2, 1], []⟩)]
def origins59 : List Row := [⟨9, 0, 1, [2, 1], [3, 1]⟩, ⟨9, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨9, 0, 1, [2, 1, 3], [3]⟩]
def proof59 : List Witness := [⟨⟨9, 0, 1, [2, 1], [3, 1]⟩, ⟨9, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨9, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨9, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨9, 0, 1, [2, 1, 3], [3]⟩, ⟨9, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_59 : P true normal59 [2, 1] origins59 proof59 = true := by decide
-- target e077dc58b85903fc2a5cc68e2865661bacbc60294182b04274db0669294c28cb
def normal60 : List (Bool × Row) := [(false, ⟨10, 0, 1, [2], []⟩), (false, ⟨10, 0, 1, [], []⟩), (false, ⟨10, 0, 1, [], [2]⟩), (false, ⟨10, 0, 1, [2], [3]⟩), (false, ⟨10, 0, 1, [], [3]⟩), (true, ⟨10, 1, 0, [], [2, 1]⟩)]
def origins60 : List Row := [⟨10, 0, 1, [2], []⟩, ⟨10, 0, 1, [2], [2]⟩, ⟨10, 0, 1, [2], [2, 2]⟩, ⟨10, 0, 1, [2], [3]⟩, ⟨10, 0, 1, [2], [3, 2]⟩, ⟨10, 0, 1, [2, 1], []⟩]
def proof60 : List Witness := [⟨⟨10, 0, 1, [2], []⟩, ⟨10, 0, 1, [2], []⟩, false, []⟩, ⟨⟨10, 0, 1, [2], [2]⟩, ⟨10, 0, 1, [], []⟩, false, [2]⟩, ⟨⟨10, 0, 1, [2], [2, 2]⟩, ⟨10, 0, 1, [], [2]⟩, false, [2]⟩, ⟨⟨10, 0, 1, [2], [3]⟩, ⟨10, 0, 1, [2], [3]⟩, false, []⟩, ⟨⟨10, 0, 1, [2], [3, 2]⟩, ⟨10, 0, 1, [], [3]⟩, false, [2]⟩, ⟨⟨10, 0, 1, [2, 1], []⟩, ⟨10, 1, 0, [], [2, 1]⟩, true, []⟩]
theorem checked_60 : P true normal60 [2] origins60 proof60 = true := by decide
-- target 90c6fa234a6d4d88dcefe32b00087e8517842c9612bb7280f59bee4d368e8716
def normal61 : List (Bool × Row) := [(false, ⟨10, 0, 1, [], []⟩), (false, ⟨10, 0, 1, [], [2]⟩), (false, ⟨10, 0, 1, [2, 1], []⟩)]
def origins61 : List Row := [⟨10, 0, 1, [2, 1], [2, 1]⟩, ⟨10, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨10, 0, 1, [2, 1, 2], [2]⟩]
def proof61 : List Witness := [⟨⟨10, 0, 1, [2, 1], [2, 1]⟩, ⟨10, 0, 1, [], []⟩, false, [2, 1]⟩, ⟨⟨10, 0, 1, [2, 1], [2, 2, 1]⟩, ⟨10, 0, 1, [], [2]⟩, false, [2, 1]⟩, ⟨⟨10, 0, 1, [2, 1, 2], [2]⟩, ⟨10, 0, 1, [2, 1], []⟩, false, [2]⟩]
theorem checked_61 : P true normal61 [2, 1] origins61 proof61 = true := by decide
-- target 1de633d7a4af925a9c1f18a56c7d79dafe1d0628ec371f73b6386c005e776834
def normal62 : List (Bool × Row) := [(false, ⟨10, 0, 1, [3], []⟩), (false, ⟨10, 0, 1, [3], [2]⟩), (false, ⟨10, 0, 1, [], [2]⟩), (false, ⟨10, 0, 1, [], []⟩), (false, ⟨10, 0, 1, [], [3]⟩), (true, ⟨10, 1, 0, [], [3, 1]⟩)]
def origins62 : List Row := [⟨10, 0, 1, [3], []⟩, ⟨10, 0, 1, [3], [2]⟩, ⟨10, 0, 1, [3], [2, 3]⟩, ⟨10, 0, 1, [3], [3]⟩, ⟨10, 0, 1, [3], [3, 3]⟩, ⟨10, 0, 1, [3, 1], []⟩]
def proof62 : List Witness := [⟨⟨10, 0, 1, [3], []⟩, ⟨10, 0, 1, [3], []⟩, false, []⟩, ⟨⟨10, 0, 1, [3], [2]⟩, ⟨10, 0, 1, [3], [2]⟩, false, []⟩, ⟨⟨10, 0, 1, [3], [2, 3]⟩, ⟨10, 0, 1, [], [2]⟩, false, [3]⟩, ⟨⟨10, 0, 1, [3], [3]⟩, ⟨10, 0, 1, [], []⟩, false, [3]⟩, ⟨⟨10, 0, 1, [3], [3, 3]⟩, ⟨10, 0, 1, [], [3]⟩, false, [3]⟩, ⟨⟨10, 0, 1, [3, 1], []⟩, ⟨10, 1, 0, [], [3, 1]⟩, true, []⟩]
theorem checked_62 : P true normal62 [3] origins62 proof62 = true := by decide
-- target ce193aa827ad6b70eabf62f8976c0fa07cd32485e1d0836e6135f7d8cf01d3bc
def normal63 : List (Bool × Row) := [(false, ⟨10, 0, 1, [2], [3]⟩), (false, ⟨10, 0, 1, [], [3]⟩), (false, ⟨10, 0, 1, [2, 1], []⟩)]
def origins63 : List Row := [⟨10, 0, 1, [2, 1], [3, 1]⟩, ⟨10, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨10, 0, 1, [2, 1, 3], [3]⟩]
def proof63 : List Witness := [⟨⟨10, 0, 1, [2, 1], [3, 1]⟩, ⟨10, 0, 1, [2], [3]⟩, false, [1]⟩, ⟨⟨10, 0, 1, [2, 1], [3, 2, 1]⟩, ⟨10, 0, 1, [], [3]⟩, false, [2, 1]⟩, ⟨⟨10, 0, 1, [2, 1, 3], [3]⟩, ⟨10, 0, 1, [2, 1], []⟩, false, [3]⟩]
theorem checked_63 : P true normal63 [2, 1] origins63 proof63 = true := by decide
-- target a8f7c890f040b75f4f9866fd015786260f9243f74257eeb6b4efe4685d9c6ac0
def normal64 : List (Bool × Row) := [(false, ⟨10, 0, 1, [], []⟩), (false, ⟨10, 0, 1, [], [3]⟩), (false, ⟨10, 0, 1, [3, 1], []⟩)]
def origins64 : List Row := [⟨10, 0, 1, [3, 1], [3, 1]⟩, ⟨10, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨10, 0, 1, [3, 1, 3], [3]⟩]
def proof64 : List Witness := [⟨⟨10, 0, 1, [3, 1], [3, 1]⟩, ⟨10, 0, 1, [], []⟩, false, [3, 1]⟩, ⟨⟨10, 0, 1, [3, 1], [3, 3, 1]⟩, ⟨10, 0, 1, [], [3]⟩, false, [3, 1]⟩, ⟨⟨10, 0, 1, [3, 1, 3], [3]⟩, ⟨10, 0, 1, [3, 1], []⟩, false, [3]⟩]
theorem checked_64 : P true normal64 [3, 1] origins64 proof64 = true := by decide
-- target 003af0b2d1ba5308b5b901be54a609cd90c89d82c07115a2dec5ee2db19b321c
def normal65 : List (Bool × Row) := [(false, ⟨10, 0, 1, [3], [2]⟩), (false, ⟨10, 0, 1, [], [2]⟩), (false, ⟨10, 0, 1, [3, 1], []⟩)]
def origins65 : List Row := [⟨10, 0, 1, [3, 1], [2, 1]⟩, ⟨10, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨10, 0, 1, [3, 1, 2], [2]⟩]
def proof65 : List Witness := [⟨⟨10, 0, 1, [3, 1], [2, 1]⟩, ⟨10, 0, 1, [3], [2]⟩, false, [1]⟩, ⟨⟨10, 0, 1, [3, 1], [2, 3, 1]⟩, ⟨10, 0, 1, [], [2]⟩, false, [3, 1]⟩, ⟨⟨10, 0, 1, [3, 1, 2], [2]⟩, ⟨10, 0, 1, [3, 1], []⟩, false, [2]⟩]
theorem checked_65 : P true normal65 [3, 1] origins65 proof65 = true := by decide
end NormalBackedDemand.AllHelpersV2
#print axioms NormalBackedDemand.AllHelpersV2.checked_0
#print axioms NormalBackedDemand.AllHelpersV2.checked_1
#print axioms NormalBackedDemand.AllHelpersV2.checked_2
#print axioms NormalBackedDemand.AllHelpersV2.checked_3
#print axioms NormalBackedDemand.AllHelpersV2.checked_4
#print axioms NormalBackedDemand.AllHelpersV2.checked_5
#print axioms NormalBackedDemand.AllHelpersV2.checked_6
#print axioms NormalBackedDemand.AllHelpersV2.checked_7
#print axioms NormalBackedDemand.AllHelpersV2.checked_8
#print axioms NormalBackedDemand.AllHelpersV2.checked_9
#print axioms NormalBackedDemand.AllHelpersV2.checked_10
#print axioms NormalBackedDemand.AllHelpersV2.checked_11
#print axioms NormalBackedDemand.AllHelpersV2.checked_12
#print axioms NormalBackedDemand.AllHelpersV2.checked_13
#print axioms NormalBackedDemand.AllHelpersV2.checked_14
#print axioms NormalBackedDemand.AllHelpersV2.checked_15
#print axioms NormalBackedDemand.AllHelpersV2.checked_16
#print axioms NormalBackedDemand.AllHelpersV2.checked_17
#print axioms NormalBackedDemand.AllHelpersV2.checked_18
#print axioms NormalBackedDemand.AllHelpersV2.checked_19
#print axioms NormalBackedDemand.AllHelpersV2.checked_20
#print axioms NormalBackedDemand.AllHelpersV2.checked_21
#print axioms NormalBackedDemand.AllHelpersV2.checked_22
#print axioms NormalBackedDemand.AllHelpersV2.checked_23
#print axioms NormalBackedDemand.AllHelpersV2.checked_24
#print axioms NormalBackedDemand.AllHelpersV2.checked_25
#print axioms NormalBackedDemand.AllHelpersV2.checked_26
#print axioms NormalBackedDemand.AllHelpersV2.checked_27
#print axioms NormalBackedDemand.AllHelpersV2.checked_28
#print axioms NormalBackedDemand.AllHelpersV2.checked_29
#print axioms NormalBackedDemand.AllHelpersV2.checked_30
#print axioms NormalBackedDemand.AllHelpersV2.checked_31
#print axioms NormalBackedDemand.AllHelpersV2.checked_32
#print axioms NormalBackedDemand.AllHelpersV2.checked_33
#print axioms NormalBackedDemand.AllHelpersV2.checked_34
#print axioms NormalBackedDemand.AllHelpersV2.checked_35
#print axioms NormalBackedDemand.AllHelpersV2.checked_36
#print axioms NormalBackedDemand.AllHelpersV2.checked_37
#print axioms NormalBackedDemand.AllHelpersV2.checked_38
#print axioms NormalBackedDemand.AllHelpersV2.checked_39
#print axioms NormalBackedDemand.AllHelpersV2.checked_40
#print axioms NormalBackedDemand.AllHelpersV2.checked_41
#print axioms NormalBackedDemand.AllHelpersV2.checked_42
#print axioms NormalBackedDemand.AllHelpersV2.checked_43
#print axioms NormalBackedDemand.AllHelpersV2.checked_44
#print axioms NormalBackedDemand.AllHelpersV2.checked_45
#print axioms NormalBackedDemand.AllHelpersV2.checked_46
#print axioms NormalBackedDemand.AllHelpersV2.checked_47
#print axioms NormalBackedDemand.AllHelpersV2.checked_48
#print axioms NormalBackedDemand.AllHelpersV2.checked_49
#print axioms NormalBackedDemand.AllHelpersV2.checked_50
#print axioms NormalBackedDemand.AllHelpersV2.checked_51
#print axioms NormalBackedDemand.AllHelpersV2.checked_52
#print axioms NormalBackedDemand.AllHelpersV2.checked_53
#print axioms NormalBackedDemand.AllHelpersV2.checked_54
#print axioms NormalBackedDemand.AllHelpersV2.checked_55
#print axioms NormalBackedDemand.AllHelpersV2.checked_56
#print axioms NormalBackedDemand.AllHelpersV2.checked_57
#print axioms NormalBackedDemand.AllHelpersV2.checked_58
#print axioms NormalBackedDemand.AllHelpersV2.checked_59
#print axioms NormalBackedDemand.AllHelpersV2.checked_60
#print axioms NormalBackedDemand.AllHelpersV2.checked_61
#print axioms NormalBackedDemand.AllHelpersV2.checked_62
#print axioms NormalBackedDemand.AllHelpersV2.checked_63
#print axioms NormalBackedDemand.AllHelpersV2.checked_64
#print axioms NormalBackedDemand.AllHelpersV2.checked_65
