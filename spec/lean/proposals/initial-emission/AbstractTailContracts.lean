/-
  Two selected abstract-tail contracts; no production change.

  1. An already present NORMAL STAR/FLOW -> STAR/FLOW relation covers its
     matching EXACT/FLOW -> EXACT/FLOW relation across premise tail geometry.
     This does not prove that the covering relation is always present.
  2. An abstract MUST premise requires definite MUST input. Geometric overlap
     or coverage alone cannot promote STAR, MAY or EXACT input to MUST.

  Scalar scope: Empty exclusions, no static/ND/type/alias behavior, same
  method/record scope and equal endpoint base/path/mark geometry. MUST is
  explicit and independent of the submitted NORMAL/DEMAND layer.
-/
import ApSpec.AbsDefs

namespace AbstractTailContracts
open ApSpec ApSpec.Abs

def starFlow (b : Base) (p : List Acc) : PFact := ⟨b, p, .star Excl.empty, .star⟩
def exactFlow (b : Base) (p : List Acc) : PFact := ⟨b, p, .exact, .star⟩

theorem normal_star_identity_geometry_covers_exact (ib ob : Base)
    (ip op : List Acc) (x y : Loc)
    (h : den (exactFlow ib ip) (exactFlow ob op) x y) :
    den (starFlow ib ip) (starFlow ob op) x y := by
  obtain ⟨hb0, hb1, hm0, hm1, pass, s, t, hp0, hp1, hi, hf⟩ := h
  have hs : s = [] := hi
  have ht : t = [] := hf
  subst s
  subst t
  exact ⟨hb0, hb1, hm0, hm1, pass, [], [], hp0, hp1, rfl, rfl, rfl⟩

/-- If the covering normal relation is stored, discarding the exact relation
    preserves the represented union. It adds no pair to that stored union. -/
theorem dropping_exact_preserves_union_when_cover_is_present (ib ob : Base)
    (ip op : List Acc) (x y : Loc) :
    (den (starFlow ib ip) (starFlow ob op) x y ∨
      den (exactFlow ib ip) (exactFlow ob op) x y) ↔
      den (starFlow ib ip) (starFlow ob op) x y := by
  constructor
  · intro pair
    cases pair with
    | inl existing => exact existing
    | inr exact => exact normal_star_identity_geometry_covers_exact ib ob ip op x y exact
  · exact Or.inl

structure Supplied where
  fact : PFact
  must : Bool
  demandLayer : Bool
deriving DecidableEq, Repr

/-- Only the selected MUST branch is modeled. Ordinary non-MUST matching
    remains a separate existing rule. A claimed MUST with a non-ANY raw tail
    is invalid and does not match either. -/
def matchesAbstractMust (premise : PFact) (actual : Supplied) : Bool :=
  actual.must && actual.fact.kind.isAny && satI premise actual.fact

def mustPremise : PFact := ⟨1, [], .any, .star⟩
def ordinaryStar : PFact := starFlow 1 []
def ordinaryMay : PFact := ⟨1, [], .any, .star⟩
def ordinaryExact : PFact := exactFlow 1 []

theorem geometry_alone_does_not_establish_must :
    satI mustPremise ordinaryStar = true ∧
    satI mustPremise ordinaryMay = true ∧
    matchesAbstractMust mustPremise ⟨ordinaryStar, false, false⟩ = false ∧
    matchesAbstractMust mustPremise ⟨ordinaryMay, false, false⟩ = false ∧
    matchesAbstractMust mustPremise ⟨ordinaryExact, false, false⟩ = false := by decide

theorem only_definite_must_is_admitted (layer : Bool) :
    matchesAbstractMust mustPremise ⟨⟨1, [], .any, .conc 7⟩, true, layer⟩ = true ∧
    matchesAbstractMust mustPremise ⟨ordinaryMay, true, layer⟩ = true ∧
    matchesAbstractMust mustPremise ⟨ordinaryStar, false, layer⟩ = false ∧
    matchesAbstractMust mustPremise ⟨ordinaryMay, false, layer⟩ = false ∧
    matchesAbstractMust mustPremise ⟨ordinaryExact, false, layer⟩ = false := by
  cases layer <;> decide

theorem layer_does_not_create_must (premise fact : PFact) (certainty left right : Bool) :
    matchesAbstractMust premise ⟨fact, certainty, left⟩ =
      matchesAbstractMust premise ⟨fact, certainty, right⟩ := rfl

theorem invalid_must_flags_do_not_bypass_tail_guard :
    matchesAbstractMust mustPremise ⟨ordinaryStar, true, false⟩ = false ∧
    matchesAbstractMust mustPremise ⟨ordinaryExact, true, false⟩ = false := by decide

def check : Bool :=
  !matchesAbstractMust mustPremise ⟨ordinaryStar, false, false⟩ &&
  matchesAbstractMust mustPremise ⟨ordinaryMay, true, true⟩

theorem checked : check = true := by decide

#eval check
#print axioms normal_star_identity_geometry_covers_exact
#print axioms dropping_exact_preserves_union_when_cover_is_present
#print axioms only_definite_must_is_admitted
#print axioms layer_does_not_create_must

end AbstractTailContracts
