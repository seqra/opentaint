import Evidence

namespace ExactMayCapture
open TruncationEvidence

-- Rebase a child's suffix language at a covering ancestor coordinate.
-- Unknown below a nonempty shift is not unknown at the ancestor root.
def prependEvidence (shift : Path) : Evidence → Evidence
  | none => some [⟨shift,true⟩]
  | some ps => some (ps.map (fun p => {p with path := shift ++ p.path}))

theorem rebased_empty_bit (shift : Path) (e : Evidence) :
    mayEmpty (prependEvidence shift e) = (shift.isEmpty && mayEmpty e) := by
  cases shift with
  | nil => cases e <;> simp [prependEvidence,mayEmpty]
  | cons f rest => cases e <;> simp [prependEvidence,mayEmpty]

def addBit (previous : Option Bool) (contribution : Bool) : Bool :=
  match previous with | none => contribution | some old => old || contribution

theorem first_real_cut_is_nonempty : addBit none false = false := rfl
theorem unknown_duplicate_widens (old : Bool) : addBit (some old) true = true := by
  cases old <;> rfl
theorem known_duplicate_cannot_clear_empty (bit : Bool) :
    addBit (some true) bit = true := by cases bit <;> rfl
theorem contributor_order_independent (a b : Bool) :
    addBit (some a) b = addBit (some b) a := by cases a <;> cases b <;> rfl

-- The raw result, after paired selection, is the contribution. A missing
-- contribution list is not used as a certificate on a live row.
def gather : List Evidence → Evidence
  | [] => some []
  | e :: rest => merge e (gather rest)

theorem member_language_retained (all : List Evidence) (e : Evidence)
    (member : e ∈ all) (word : Path) (inside : denotes e word) :
    denotes (gather all) word := by
  induction all with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst e
      exact (merge_denotes first (gather rest) word).mpr (Or.inl inside)
    · exact (merge_denotes first (gather rest) word).mpr (Or.inr (ih tail))

theorem excluded_empty_not_in_any_contributor
    (all : List Evidence) (closed : mayEmpty (gather all) = false)
    (e : Evidence) (member : e ∈ all) : ¬ denotes e [] := by
  intro inside
  have final := member_language_retained all e member [] inside
  have positive := (mayEmpty_exact (gather all)).mpr final
  rw [closed] at positive
  cases positive

theorem a_live_known_may_query_has_a_binding (first : Suffix) (rest : List Suffix) :
    ∃ word, denotes (some (first :: rest)) word := by
  exact ⟨first.path,first,by simp,Or.inl rfl⟩

theorem a_live_unknown_may_query_has_a_binding : ∃ word, denotes none word :=
  ⟨[],True.intro⟩

#print axioms rebased_empty_bit
#print axioms first_real_cut_is_nonempty
#print axioms unknown_duplicate_widens
#print axioms known_duplicate_cannot_clear_empty
#print axioms contributor_order_independent
#print axioms member_language_retained
#print axioms excluded_empty_not_in_any_contributor
#print axioms a_live_known_may_query_has_a_binding
#print axioms a_live_unknown_may_query_has_a_binding
end ExactMayCapture
