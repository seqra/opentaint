import Std

namespace UriAliasEquationCandidate
/- A complete equation census must include declared reference operations and
   the pass actions that the same frozen evaluator admits. An inactive clause
   can still occur in the native condition-erased DSU. This model proves only
   the valid configured-equation relation. Its native adapter remains open. -/
structure Equation where
  leftBase : Nat
  rightBase : Nat
  leftPath : List Nat
  rightPath : List Nat
  admitted : Bool
  deriving DecidableEq
structure Point where
  base : Nat
  path : List Nat
  deriving DecidableEq

def free (uri : Nat) (path : List Nat) : Bool := path.all fun f => !(Nat.beq f uri)
def checked (uri : Nat) (catalog : List Equation) : Bool :=
  catalog.all fun row => !row.admitted || (free uri row.leftPath && free uri row.rightPath)

theorem free_sound (uri : Nat) (path : List Nat) (ok : free uri path = true) : uri ∉ path := by
  intro inside
  have h := (List.all_eq_true.mp ok) uri inside
  simp only [Nat.beq_refl, Bool.not_true, Bool.false_eq_true] at h

theorem checked_clause (uri : Nat) (catalog : List Equation) (ok : checked uri catalog = true)
    (row : Equation) (member : row ∈ catalog) (active : row.admitted = true) :
    uri ∉ row.leftPath ∧ uri ∉ row.rightPath := by
  have h := (List.all_eq_true.mp ok) row member
  have both : free uri row.leftPath = true ∧ free uri row.rightPath = true := by
    simpa only [active, Bool.not_true, Bool.false_or, Bool.and_eq_true] using h
  exact ⟨free_sound uri row.leftPath both.1, free_sound uri row.rightPath both.2⟩

def firstUri (uri : Nat) : List Nat → List Nat
  | [] => []
  | f :: rest => if f = uri then f :: rest else firstUri uri rest

theorem first_suffix_of_free_prefix (uri : Nat) (pre suffix : List Nat)
    (noUri : uri ∉ pre) : firstUri uri (pre ++ suffix) = firstUri uri suffix := by
  induction pre with
  | nil => rfl
  | cons f rest ih =>
    have head : f ≠ uri := fun equal => noUri (by simp [equal])
    have tail : uri ∉ rest := fun member => noUri (List.mem_cons_of_mem _ member)
    simpa [firstUri,head] using ih tail

theorem first_suffix_length_le (uri : Nat) (word : List Nat) :
    (firstUri uri word).length ≤ word.length := by
  induction word with
  | nil => exact Nat.le_refl 0
  | cons f rest ih =>
    by_cases same : f = uri
    · simp [firstUri,same]
    · simpa [firstUri,same] using Nat.le_trans ih (Nat.le_succ rest.length)

inductive ValidAlias (catalog : List Equation) : Point → Point → Prop
  | refl (point : Point) : ValidAlias catalog point point
  | copy (row : Equation) (member : row ∈ catalog) (active : row.admitted = true)
      (suffix : List Nat) : ValidAlias catalog
        ⟨row.leftBase,row.leftPath ++ suffix⟩ ⟨row.rightBase,row.rightPath ++ suffix⟩
  | reverse {x y : Point} : ValidAlias catalog x y → ValidAlias catalog y x
  | compose {x y z : Point} : ValidAlias catalog x y → ValidAlias catalog y z → ValidAlias catalog x z

theorem valid_alias_preserves_uri_suffix (uri : Nat) (catalog : List Equation)
    (ok : checked uri catalog = true) (x y : Point) (alias : ValidAlias catalog x y) :
    firstUri uri x.path = firstUri uri y.path := by
  induction alias with
  | refl point => rfl
  | copy row member active suffix =>
    have both := checked_clause uri catalog ok row member active
    exact (first_suffix_of_free_prefix uri row.leftPath suffix both.1).trans
      (first_suffix_of_free_prefix uri row.rightPath suffix both.2).symm
  | reverse _ ih => exact ih.symm
  | compose _ _ first second => exact first.trans second

/- All 135 prospective writers have empty source prefix and a target prefix
   that starts with URI. They cannot be justified by the admitted equations,
   even if the input residual suffix already contains a URI. -/
theorem root_to_literal_uri_is_not_a_valid_alias (uri : Nat) (catalog : List Equation)
    (ok : checked uri catalog = true) (fromBase toBase : Nat) (input addedTail : List Nat) :
    ¬ ValidAlias catalog ⟨fromBase,input⟩ ⟨toBase,uri :: (addedTail ++ input)⟩ := by
  intro alias
  have equal := valid_alias_preserves_uri_suffix uri catalog ok _ _ alias
  have lengths : (firstUri uri input).length = (addedTail.length + input.length).succ := by
    simpa [firstUri] using congrArg List.length equal
  have bounded := first_suffix_length_le uri input
  rw [lengths] at bounded
  exact Nat.not_succ_le_self _ (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left _ _)) bounded)

/- Reject the candidate guard if the literal-writing equation is admitted. -/
example : checked 7 [⟨0,1,[],[7,8],true⟩] = false := by decide
example : checked 7 [⟨0,1,[],[7,8],false⟩,⟨0,2,[],[],true⟩] = true := by decide
end UriAliasEquationCandidate
#print axioms UriAliasEquationCandidate.free_sound
#print axioms UriAliasEquationCandidate.checked_clause
#print axioms UriAliasEquationCandidate.first_suffix_of_free_prefix
#print axioms UriAliasEquationCandidate.first_suffix_length_le
#print axioms UriAliasEquationCandidate.valid_alias_preserves_uri_suffix
#print axioms UriAliasEquationCandidate.root_to_literal_uri_is_not_a_valid_alias
