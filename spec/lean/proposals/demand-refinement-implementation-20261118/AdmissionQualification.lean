import Std

namespace AdmissionQualification

structure FrozenRow where
  owner : Nat
  entry : Nat
  exit : Nat
  port : Nat
  virtual : Bool
  deriving DecidableEq

structure Publication where
  row : FrozenRow
  raw : Nat

inductive Binding where
  | exact (row : FrozenRow) (raw : Nat)
  | projected (owner entry : Nat) (port : Option Nat) (raw : Nat)

def accepts (p : Publication) : Binding → Prop
  | .exact row raw => p.raw = raw ∧ p.row = row
  | .projected owner entry port raw => p.raw = raw ∧ p.row.virtual = true ∧
      p.row.owner = owner ∧ p.row.entry = entry ∧
      (port = none ∨ port = some p.row.port)

theorem ordinary_binding_cannot_mix_paired_outputs
    (p : Publication) (row : FrozenRow) (h : accepts p (.exact row raw)) :
    p.row.exit = row.exit ∧ p.row.port = row.port :=
  ⟨congrArg FrozenRow.exit h.2, congrArg FrozenRow.port h.2⟩

theorem projected_binding_needs_a_complete_virtual_publication
    (p : Publication) (h : accepts p (.projected owner entry port raw)) :
    ∃ row : FrozenRow, row = p.row ∧ row.virtual = true ∧
      row.owner = owner ∧ row.entry = entry ∧ p.raw = raw :=
  ⟨p.row, rfl, h.2.1, h.2.2.1, h.2.2.2.1, h.1⟩

theorem projected_binding_never_matches_an_explicit_row
    (p : Publication) (ordinary : p.row.virtual = false) :
    ¬ accepts p (.projected owner entry port raw) := by
  intro h
  have projected : p.row.virtual = true := h.2.1
  rw [ordinary] at projected
  exact Bool.false_ne_true projected

inductive PossibleHead : List Nat → List Nat → Prop where
  | named (field : Nat) (rest : List Nat) : PossibleHead (field :: rest) (field :: rest)
  | child (head : List Nat) (field : Nat) : PossibleHead head (head ++ [field])

theorem every_possible_head_passes_the_sparse_index
    (p q : List Nat) (possible : PossibleHead p q) :
    (p = q ∧ p ≠ []) ∨ ∃ f, q = p ++ [f] := by
  cases possible with
  | named field rest => exact Or.inl ⟨rfl, List.cons_ne_nil field rest⟩
  | child head field => exact Or.inr ⟨field, rfl⟩

end AdmissionQualification

#print axioms AdmissionQualification.ordinary_binding_cannot_mix_paired_outputs
#print axioms AdmissionQualification.projected_binding_needs_a_complete_virtual_publication
#print axioms AdmissionQualification.projected_binding_never_matches_an_explicit_row
#print axioms AdmissionQualification.every_possible_head_passes_the_sparse_index
