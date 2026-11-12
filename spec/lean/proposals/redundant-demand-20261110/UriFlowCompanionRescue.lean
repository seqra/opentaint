import Std
namespace UriFlowCompanionRescue
/- Complete family for the selected nonstatic, counted-field FLOW cells only.
   Fields/exclusions/mark compatibility and the next-run cap are preconditions
   of the native adapter; this is not a whole-store retirement theorem. -/
inductive Kind where | exact | star deriving DecidableEq, Repr
structure Initial where
  path : List Nat
  kind : Kind
  deriving DecidableEq, Repr
/- MAY(d) submitted to STAR(d) starts exactly at d, NORMAL/FLOW. -/
def coarseStarStart (d : List Nat) : Initial := ⟨d,.exact⟩
/- A precise strict child submitted to MAY(d) starts after the first field
   and emits the root EXACT/FLOW companion. All starts are NORMAL/FLOW. -/
def refinedMayStarts (d : List Nat) (field : Nat) : List Initial :=
  [⟨d ++ [field],.star⟩, ⟨d,.exact⟩]
theorem same_prefix_may_recreates_exact_start (d : List Nat) (field : Nat) :
    coarseStarStart d ∈ refinedMayStarts d field := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem any_existing_uses_are_preserved (d : List Nat) (field : Nat)
    (uses : Initial → List Nat) (consumer : Nat)
    (h : consumer ∈ uses (coarseStarStart d)) :
    consumer ∈ (refinedMayStarts d field).flatMap uses := by
  exact List.mem_flatMap.mpr ⟨coarseStarStart d,
    same_prefix_may_recreates_exact_start d field,h⟩
/- The shared sibling starts and arbitrary consumer labels are never emptied. -/
theorem common_starts_remain (common : List Initial) (d : List Nat) (field : Nat)
    (i : Initial) (h : i ∈ common) :
    i ∈ common ++ refinedMayStarts d field := List.mem_append_left _ h
/- Root-companion equality is stronger than semantic point overlap. It can
   preserve rules, subscriptions and paired tickets for that exact initial. -/
theorem exact_start_equality (d : List Nat) (field : Nat) :
    (refinedMayStarts d field)[1]? = some (coarseStarStart d) := by rfl
end UriFlowCompanionRescue
#print axioms UriFlowCompanionRescue.same_prefix_may_recreates_exact_start
#print axioms UriFlowCompanionRescue.any_existing_uses_are_preserved
#print axioms UriFlowCompanionRescue.common_starts_remain
#print axioms UriFlowCompanionRescue.exact_start_equality
