import Std

namespace DualStarts

abbrev Path := List Nat
inductive Tail where | exact | star | may
  deriving DecidableEq, Repr
structure Pattern where
  base : Nat
  path : Path
  tail : Tail
  deriving DecidableEq, Repr
structure Fact where
  pattern : Pattern
  demand : Bool
  deriving DecidableEq, Repr
structure Summary where
  input : Pattern
  output : Pattern
  demand : Bool
  deriving DecidableEq, Repr

def mkPat (base : Nat) (path : Path) (tail : Tail) : Pattern := ⟨base,path,tail⟩

-- This model is FLOW only. EXACT normalization is not a rule for T.
def normalTail : Tail → Tail | .exact => .star | t => t
def normalize (s : Summary) : Summary :=
  {s with input := {s.input with tail := normalTail s.input.tail},
          output := {s.output with tail := normalTail s.output.tail}}

def starts (base : Nat) (path : Path) : List Summary :=
  [⟨mkPat base path .exact, mkPat base path .exact, false⟩,
   ⟨mkPat base path .may, mkPat base path .may, true⟩]

-- The selected candidate law is defined on SAME-HEAD MAY actuals only.
-- Output MAY absorbs support; the NORMAL provider cannot confirm it.
def applySameMay (s : Summary) (a : Fact) : Option Fact :=
  if a.pattern.base == s.input.base && a.pattern.path == s.input.path &&
     a.pattern.tail == .may &&
     (s.input.tail == .star || s.input.tail == .may) then
    some ⟨{s.output with tail := .may},true⟩
  else none

def starSummary (ib ob : Nat) (ip op : Path) : Summary :=
  ⟨mkPat ib ip .star, mkPat ob op .star, false⟩
def maySummary (ib ob : Nat) (ip op : Path) : Summary :=
  ⟨mkPat ib ip .may, mkPat ob op .may, true⟩

private theorem natSelf (n : Nat) : (n == n) = true := decide_eq_true rfl
private theorem pathSelf (path : Path) : (path == path) = true := by
  induction path with
  | nil => rfl
  | cons n rest ih =>
      change (decide (n = n) && (rest == rest)) = true
      rw [decide_eq_true (Eq.refl n), ih]
      rfl

theorem two_starts_have_distinct_keys (base : Nat) (path : Path) :
    (starts base path).length = 2 ∧
    mkPat base path .exact ≠ mkPat base path .may := by
  constructor
  · rfl
  · intro h; cases h

theorem dual_starts_have_no_live_star (base : Nat) (path : Path)
    (s : Summary) (member : s ∈ starts base path) :
    s.input.tail ≠ .star ∧ s.output.tail ≠ .star := by
  rcases List.mem_cons.mp member with same | more
  · subst s
    change Tail.exact ≠ Tail.star ∧ Tail.exact ≠ Tail.star
    decide
  · rcases List.mem_cons.mp more with same | impossible
    · subst s
      change Tail.may ≠ Tail.star ∧ Tail.may ≠ Tail.star
      decide
    · cases impossible

theorem exact_copy_normalizes_to_correlated_normal
    (ib ob : Nat) (ip op : Path) :
    normalize ⟨mkPat ib ip .exact, mkPat ob op .exact, false⟩ =
      starSummary ib ob ip op := rfl

theorem same_head_may_application_equal
    (ib ob : Nat) (ip op : Path) (support : Bool) :
    applySameMay (starSummary ib ob ip op) ⟨mkPat ib ip .may,support⟩ =
    applySameMay (maySummary ib ob ip op) ⟨mkPat ib ip .may,support⟩ := by
  rfl

theorem normal_provider_preserves_may_uncertainty
    (ib ob : Nat) (ip op : Path) (support : Bool) :
    applySameMay (starSummary ib ob ip op) ⟨mkPat ib ip .may,support⟩ =
      some ⟨mkPat ob op .may,true⟩ := by
  change (if (ib == ib && ip == ip && true && (true || false)) then
    some (Fact.mk (mkPat ob op .may) true) else none) = some (Fact.mk (mkPat ob op .may) true)
  have allowed : (ib == ib && ip == ip && true && (true || false)) = true := by
    rw [natSelf ib, pathSelf ip]
    rfl
  exact ite_eq_left allowed

-- This is not ordinary concrete-pair inclusion. Independent MAY output
-- can choose an empty suffix while the input suffix is nonempty.
def starPair (inputSuffix outputSuffix : Path) : Prop := inputSuffix = outputSuffix
def mayPair (_inputSuffix _outputSuffix : Path) : Prop := True
theorem concrete_relation_inclusion_is_false :
    mayPair [1] [] ∧ ¬ starPair [1] [] := by
  exact ⟨True.intro,by simp [starPair]⟩

-- Ordinary forward field read: an exact root is not a descendant input.
-- Only the relevant two tails and an empty original prefix are modeled.
def forwardRead (a : Fact) : Option Fact :=
  match a.pattern.tail with
  | .exact => none
  | .may => some ⟨mkPat 2 [] .may,true⟩
  | .star => some ⟨mkPat 2 [] .may,true⟩

theorem a_provider_does_not_always_exist :
    forwardRead ⟨mkPat 1 [] .exact,false⟩ = none ∧
    forwardRead ⟨mkPat 1 [] .may,true⟩ = some ⟨mkPat 2 [] .may,true⟩ := by decide

-- A historical operator cell, not an admitted start of the clarified
-- proposal. Its STAR input cannot be used to refute the new policy.
def allowStarAtHead (mayEmptyEvidence : Option Bool) : Bool :=
  mayEmptyEvidence.getD true
def readWithEvidence (evidence : Option Bool) : Option Fact :=
  if allowStarAtHead evidence then forwardRead ⟨mkPat 1 [] .star,false⟩ else none
theorem historical_star_read_with_unknown_evidence :
    allowStarAtHead none = true ∧
    readWithEvidence none = some ⟨mkPat 2 [] .may,true⟩ := by decide

def readFromDualStarts : List (Option Fact) :=
  (starts 1 []).map (fun s => forwardRead ⟨s.output,s.demand⟩)
theorem actual_dual_read_results :
    readFromDualStarts = [none,some ⟨mkPat 2 [] .may,true⟩] := by decide

-- Reversing ret=p.f instead ADDS f. An exact returned point suffices.
def backwardReadExact (field : Nat) : Summary :=
  ⟨mkPat 2 [] .exact,mkPat 1 [field] .exact,false⟩
theorem getter_backward_exact_supplies_normal_provider (field : Nat) :
    normalize (backwardReadExact field) = starSummary 2 1 [] [field] := rfl

-- At a deeper offered MAY head, ordinary correlated application preserves
-- the known suffix. An uncorrelated MAY result need not preserve it.
def descendantStarResult (suffix : Path) : Fact := ⟨mkPat 2 suffix .may,true⟩
def descendantMayResult : Fact := ⟨mkPat 2 [] .may,true⟩
theorem same_head_rule_is_not_a_descendant_equality :
    descendantStarResult [1] ≠ descendantMayResult := by decide

#print axioms two_starts_have_distinct_keys
#print axioms dual_starts_have_no_live_star
#print axioms exact_copy_normalizes_to_correlated_normal
#print axioms same_head_may_application_equal
#print axioms normal_provider_preserves_may_uncertainty
#print axioms concrete_relation_inclusion_is_false
#print axioms a_provider_does_not_always_exist
#print axioms historical_star_read_with_unknown_evidence
#print axioms actual_dual_read_results
#print axioms getter_backward_exact_supplies_normal_provider
#print axioms same_head_rule_is_not_a_descendant_equality
end DualStarts
