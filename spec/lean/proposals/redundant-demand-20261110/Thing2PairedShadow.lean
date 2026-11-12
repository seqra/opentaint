import Std

/-!
Paired C5 and handoff component for the current Thing2 candidate.

This is NOT a retirement certificate. It proves the scalar paired-row part
from an explicit post-reset output grammar. The native SourcePlan must still
derive that grammar, and the complete store/caller proof must still be checked.
No future-equivalence proposition is assumed as a field in a certificate.
-/
namespace Thing2PairedShadow

inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, Repr

structure Geometry where
  base : Nat
  path : List Nat
  tail : Tail
  excluded : List Nat := []
  deriving DecidableEq, Repr

structure Fact where
  geometry : Geometry
  layer : Layer
  isProtected : Bool
  deriving DecidableEq, Repr

/- All DATA in this component has one fixed full mark. It has no FLOW mark
   slot, ZERO, Target, ND original, class-static or primitive-policy producer.
   `Scope` carries the complete native owner/ports; it is never dropped. -/
structure Summary (Scope : Type) where
  scope : Scope
  premise : Geometry
  result : Fact

structure PairedDemand (Scope : Type) where
  scope : Scope
  entry : Geometry
  exit : Geometry
  deriving DecidableEq

def root (base : Nat) (tail : Tail) : Geometry := ⟨base, [], tail, []⟩

/- The concrete-mark part of guidancePattern. A semantic MUST becomes MAY
   and drops E. Other concrete endpoints keep their E. Protection does not
   belong to a demand coordinate; it remains in the original scalar summary. -/
def guidance (g : Geometry) : Geometry :=
  if g.tail == .must then { g with tail := .may, excluded := [] } else g

def handoff (reverseScope : Scope → Scope) (r : Summary Scope) : PairedDemand Scope :=
  ⟨reverseScope r.scope, guidance r.result.geometry, guidance r.premise⟩

theorem guidance_preserves_location (g : Geometry) :
    (guidance g).base = g.base ∧ (guidance g).path = g.path := by
  cases g with | mk b p t e => cases t <;> simp [guidance]

theorem guidance_idempotent (g : Geometry) : guidance (guidance g) = guidance g := by
  cases g with | mk b p t e => cases t <;> simp [guidance]

/- One concrete scalar of restrictConclusionOnly at the same root base.
   STAR is correlated: an EXACT exit does not convert STAR into EXACT.
   The selected reset grammar below has no root STAR survivor. -/
def selectRootExit (exit : Tail) (f : Fact) : Option Fact :=
  if f.geometry.path.isEmpty then
    if exit == .exact && (f.geometry.tail == .may || f.geometry.tail == .must) then
      some { f with geometry := { f.geometry with tail := .exact, excluded := [] } }
    else some f
  else if exit == .star then some f else none

theorem exact_does_not_split_star (f : Fact) (hp : f.geometry.path = [])
    (ht : f.geometry.tail = .star) : selectRootExit .exact f = some f := by
  simp [selectRootExit, hp, ht]

/- Actual selected-T return producers, after the exact-root reset.
   Sources bypass that reset and assign exact root T at the incoming layer.
   A cleaner survivor is protected and DEMAND. Ordinary child copies keep
   a nonempty path and do not relocate a payload to the root. -/
inductive Output where
  | source (layer : Layer)
  | resetMay
  | resetMust (excluded : List Nat)
  | child (first : Nat) (rest : List Nat) (tail : Tail)
      (layer : Layer) (excluded : List Nat)
  deriving DecidableEq, Repr

def Output.fact (base : Nat) : Output → Fact
  | .source l => ⟨root base .exact, l, true⟩
  | .resetMay => ⟨root base .may, .demand, true⟩
  | .resetMust e => ⟨⟨base, [], .must, e⟩, .demand, true⟩
  | .child x xs t l e => ⟨⟨base, x :: xs, t, e⟩, l, true⟩

def exactDebt (base : Nat) : Fact := ⟨root base .exact, .demand, true⟩

theorem exact_only_result_is_debt (base : Nat) (o : Output) (f : Fact)
    (hx : selectRootExit .exact (o.fact base) = some f)
    (hy : selectRootExit .star (o.fact base) ≠ some f) :
    f = exactDebt base := by
  cases o <;> simp_all [Output.fact, selectRootExit, root, exactDebt]

theorem exact_only_result_has_broad_anchor (base : Nat) (o : Output) (f : Fact)
    (hx : selectRootExit .exact (o.fact base) = some f)
    (hy : selectRootExit .star (o.fact base) ≠ some f) :
    selectRootExit .star (o.fact base) = some (o.fact base) ∧
      guidance (o.fact base).geometry = root base .may ∧
      (o.fact base).layer = .demand := by
  cases o <;> simp_all [Output.fact, selectRootExit, guidance, root]

theorem no_new_normal_scalar (base : Nat) (o : Output) (f : Fact)
    (hx : selectRootExit .exact (o.fact base) = some f)
    (hn : f.layer = .normal) :
    selectRootExit .star (o.fact base) = some f := by
  by_cases h : selectRootExit .star (o.fact base) = some f
  · exact h
  · have shape := exact_only_result_is_debt base o f hx h
    rw [shape] at hn
    contradiction

theorem child_cannot_add_root_debt (base x : Nat) (xs : List Nat)
    (t : Tail) (l : Layer) (e : List Nat) :
    selectRootExit .exact ((Output.child x xs t l e).fact base) = none := by
  simp [Output.fact, selectRootExit]

/- Forward shadow output normalizes to an exact-entry row beside a MAY-entry
   row. Their opposite endpoints and full scope remain exactly equal. -/
theorem forward_handoff_shadow (reverseScope : Scope → Scope)
    (scope : Scope) (premise : Geometry) (base : Nat) (o : Output) (f : Fact)
    (hx : selectRootExit .exact (o.fact base) = some f)
    (hy : selectRootExit .star (o.fact base) ≠ some f) :
    handoff reverseScope ⟨scope, premise, f⟩ =
        ⟨reverseScope scope, root base .exact, guidance premise⟩ ∧
    handoff reverseScope ⟨scope, premise, o.fact base⟩ =
        ⟨reverseScope scope, root base .may, guidance premise⟩ := by
  have shape := exact_only_result_is_debt base o f hx hy
  have anchor := exact_only_result_has_broad_anchor base o f hx hy
  subst f
  constructor
  · simp [handoff, exactDebt, guidance, root]
  · simp [handoff, anchor.2.1]

/- Backward same-T source payloads are identical under exact and STAR starts.
   `select` is the SAME row's concrete exit restriction followed by its own
   field budget. It can return zero, one or many scalar paths. It is not a
   boolean assertion that two different native outputs are equivalent.
   The adapter must separately prove that both entry images are admitted. -/
def backRows (scope : Scope) (returnBase : Nat) (initialTail : Tail)
    (payload : Fact) (select : Fact → List Fact) : List (Summary Scope) :=
  (select payload).map fun output => ⟨scope, root returnBase initialTail, output⟩

def projectRows (reverseScope : Scope → Scope) (rs : List (Summary Scope)) :
    List (PairedDemand Scope) := rs.map (handoff reverseScope)

theorem backward_handoff_keeps_full_selected_exit (reverseScope : Scope → Scope)
    (scope : Scope) (returnBase : Nat) (payload : Fact) (select : Fact → List Fact)
    (f : Fact) (hf : f ∈ select payload) :
    ⟨reverseScope scope, guidance f.geometry, root returnBase .exact⟩ ∈
      projectRows reverseScope (backRows scope returnBase .exact payload select) ∧
    ⟨reverseScope scope, guidance f.geometry, root returnBase .star⟩ ∈
      projectRows reverseScope (backRows scope returnBase .star payload select) := by
  constructor
  · simp only [projectRows, backRows, List.mem_map]
    refine ⟨⟨scope, root returnBase .exact, f⟩, ⟨f, hf, rfl⟩, ?_⟩
    simp [handoff, guidance, root]
  · simp only [projectRows, backRows, List.mem_map]
    refine ⟨⟨scope, root returnBase .star, f⟩, ⟨f, hf, rfl⟩, ?_⟩
    simp [handoff, guidance, root]

/- Union/scalar projection is constructive. A packet may contain other marks,
   exact leaves, any leaves and either protection membership. A common packet
   is not erased; its already projected rows remain on BOTH sides. -/
theorem shared_rows_are_retained (shared extras : List (PairedDemand Scope))
    (r : PairedDemand Scope) (hr : r ∈ shared) : r ∈ shared ++ extras :=
  List.mem_append_left extras hr

theorem selected_extra_has_anchor_in_union (reverseScope : Scope → Scope)
    (scope : Scope) (returnBase : Nat) (payload : Fact) (select : Fact → List Fact)
    (common : List (PairedDemand Scope)) (f : Fact) (hf : f ∈ select payload) :
    ⟨reverseScope scope, guidance f.geometry, root returnBase .star⟩ ∈
      common ++ projectRows reverseScope (backRows scope returnBase .star payload select) :=
  List.mem_append_right common
    (backward_handoff_keeps_full_selected_exit reverseScope scope returnBase payload select f hf).2

#print axioms guidance_preserves_location
#print axioms guidance_idempotent
#print axioms exact_does_not_split_star
#print axioms exact_only_result_is_debt
#print axioms exact_only_result_has_broad_anchor
#print axioms no_new_normal_scalar
#print axioms child_cannot_add_root_debt
#print axioms forward_handoff_shadow
#print axioms backward_handoff_keeps_full_selected_exit
#print axioms shared_rows_are_retained
#print axioms selected_extra_has_anchor_in_union

end Thing2PairedShadow
