import Std
import PlainCoverageFlagViews

/-!
Constructive coverage laws for the existing fixed prefix-MAY U/H reference.
No frozen definition is changed. Equality below is logical region coverage,
not ordering or literal equality of stored list representatives.
-/
namespace CurrentCoverageInvariant
open FlagMatchedSubsumption PlainCoverageFlagViews
set_option autoImplicit false

def region (view : List Geometry) (point : Geometry) : Bool :=
  view.any (fun provider => covers provider point)

def sameFlagCover (incoming candidate : Row) : Bool :=
  decide (incoming.h = candidate.h) && covers (geometry incoming) (geometry candidate)

def matchingOffer (offered : List Row) (candidate : Row) : Bool :=
  offered.any (fun incoming => sameFlagCover incoming candidate)

theorem prefix_reflexive (path : List Nat) : prefixB path path = true := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
    exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl,ih⟩

theorem prefix_transitive (first middle last : List Nat)
    (left : prefixB first middle = true) (right : prefixB middle last = true) :
    prefixB first last = true := by
  induction first generalizing middle last with
  | nil => rfl
  | cons first rest ih =>
    cases middle with
    | nil => simp [prefixB] at left
    | cons mid middle =>
      have leftParts := (Bool.and_eq_true _ _).mp left
      have sameLeft : first = mid := of_decide_eq_true leftParts.1
      cases last with
      | nil => simp [prefixB] at right
      | cons final last =>
        have rightParts := (Bool.and_eq_true _ _).mp right
        have sameRight : mid = final := of_decide_eq_true rightParts.1
        exact (Bool.and_eq_true _ _).mpr
          ⟨decide_eq_true (sameLeft.trans sameRight),ih middle last leftParts.2 rightParts.2⟩

theorem geometry_cover_reflexive (g : Geometry) : covers g g = true :=
  (Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl,prefix_reflexive g.path⟩

theorem geometry_cover_transitive (first middle last : Geometry)
    (left : covers first middle = true) (right : covers middle last = true) :
    covers first last = true := by
  have leftParts := (Bool.and_eq_true _ _).mp left
  have rightParts := (Bool.and_eq_true _ _).mp right
  have sameLeft : first.owner = middle.owner := of_decide_eq_true leftParts.1
  have sameRight : middle.owner = last.owner := of_decide_eq_true rightParts.1
  exact (Bool.and_eq_true _ _).mpr ⟨decide_eq_true (sameLeft.trans sameRight),
    prefix_transitive first.path middle.path last.path leftParts.2 rightParts.2⟩

theorem region_true_iff_computed_member (view : List Geometry) (point : Geometry) :
    region view point = true ↔ ∃ provider ∈ view, covers provider point = true :=
  List.any_eq_true

theorem addCurrent_never_invents_geometry (view : List Geometry) (offered item : Geometry)
    (member : item ∈ addCurrent view offered) : item ∈ view ∨ item = offered := by
  unfold addCurrent at member
  split at member
  · exact Or.inl member
  · rcases List.mem_cons.mp member with fresh | kept
    · exact Or.inr fresh
    · exact Or.inl (List.mem_filter.mp kept).1

theorem addCurrent_represents_each_input (view : List Geometry) (offered item : Geometry)
    (member : item ∈ view ∨ item = offered) :
    ∃ representative ∈ addCurrent view offered, covers representative item = true := by
  unfold addCurrent
  split
  next alreadyCovered =>
    rcases member with old | fresh
    · exact ⟨item,old,geometry_cover_reflexive item⟩
    · subst item
      obtain ⟨provider,present,covered⟩ := List.any_eq_true.mp alreadyCovered
      exact ⟨provider,present,covered⟩
  next notCovered =>
    rcases member with old | fresh
    · by_cases covered : covers offered item = true
      · exact ⟨offered,List.mem_cons_self,covered⟩
      · exact ⟨item,List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
          ⟨old,by simpa using covered⟩)),geometry_cover_reflexive item⟩
    · subst item
      exact ⟨offered,List.mem_cons_self,geometry_cover_reflexive offered⟩

theorem addCurrent_region_iff (view : List Geometry) (offered point : Geometry) :
    region (addCurrent view offered) point = true ↔
      region view point = true ∨ covers offered point = true := by
  constructor
  · intro accepted
    obtain ⟨representative,present,covered⟩ :=
      (region_true_iff_computed_member _ _).mp accepted
    rcases addCurrent_never_invents_geometry view offered representative present with old | fresh
    · exact Or.inl ((region_true_iff_computed_member _ _).mpr ⟨representative,old,covered⟩)
    · subst representative
      exact Or.inr covered
  · intro accepted
    have original : ∃ item, (item ∈ view ∨ item = offered) ∧ covers item point = true := by
      rcases accepted with old | fresh
      · obtain ⟨item,present,covered⟩ := (region_true_iff_computed_member _ _).mp old
        exact ⟨item,Or.inl present,covered⟩
      · exact ⟨offered,Or.inr rfl,fresh⟩
    obtain ⟨item,present,covered⟩ := original
    obtain ⟨representative,kept,backs⟩ := addCurrent_represents_each_input view offered item present
    exact (region_true_iff_computed_member _ _).mpr
      ⟨representative,kept,geometry_cover_transitive representative item point backs covered⟩

theorem bool_equality_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right <;> simp_all

theorem addCurrent_region_union (view : List Geometry) (offered point : Geometry) :
    region (addCurrent view offered) point = (region view point || covers offered point) := by
  apply bool_equality_of_true_iff
  simpa only [Bool.or_eq_true] using addCurrent_region_iff view offered point

theorem matching_offer_requires_same_H (incoming candidate : Row)
    (accepted : sameFlagCover incoming candidate = true) : incoming.h = candidate.h :=
  of_decide_eq_true ((Bool.and_eq_true _ _).mp accepted).1

theorem offer_logical_region_union (state : Views) (incoming candidate : Row) :
    logicalCover (PlainCoverageFlagViews.offer state incoming) candidate =
      (logicalCover state candidate || sameFlagCover incoming candidate) := by
  cases incomingFlag : incoming.h <;> cases candidateFlag : candidate.h
  · simpa [PlainCoverageFlagViews.offer,logicalCover,sameFlagCover,incomingFlag,candidateFlag,region]
      using addCurrent_region_union state.plain (geometry incoming) (geometry candidate)
  · simp [PlainCoverageFlagViews.offer,logicalCover,sameFlagCover,incomingFlag,candidateFlag]
  · simp [PlainCoverageFlagViews.offer,logicalCover,sameFlagCover,incomingFlag,candidateFlag]
  · simpa [PlainCoverageFlagViews.offer,logicalCover,sameFlagCover,incomingFlag,candidateFlag,region]
      using addCurrent_region_union state.flagged (geometry incoming) (geometry candidate)

theorem fold_logical_region_union (initial : Views) (offered : List Row) (candidate : Row) :
    logicalCover (offered.foldl PlainCoverageFlagViews.offer initial) candidate =
      (logicalCover initial candidate || matchingOffer offered candidate) := by
  induction offered generalizing initial with
  | nil => simp [matchingOffer]
  | cons incoming rest ih =>
    change logicalCover (rest.foldl PlainCoverageFlagViews.offer
      (PlainCoverageFlagViews.offer initial incoming)) candidate = _
    rw [ih,offer_logical_region_union]
    change ((logicalCover initial candidate || sameFlagCover incoming candidate) ||
      matchingOffer rest candidate) =
      (logicalCover initial candidate || (sameFlagCover incoming candidate || matchingOffer rest candidate))
    exact Bool.or_assoc _ _ _

theorem empty_current_view_has_no_region (candidate : Row) :
    logicalCover emptyViews candidate = false := by
  cases flag : candidate.h <;> simp [logicalCover,emptyViews,flag]

theorem run_coverage_equals_any_same_H_input (offered : List Row) (candidate : Row) :
    logicalCover (PlainCoverageFlagViews.run offered) candidate = matchingOffer offered candidate := by
  simpa only [PlainCoverageFlagViews.run,empty_current_view_has_no_region,Bool.false_or]
    using fold_logical_region_union emptyViews offered candidate

theorem matchingOffer_true_iff_computed_input (offered : List Row) (candidate : Row) :
    matchingOffer offered candidate = true ↔
      ∃ incoming ∈ offered, sameFlagCover incoming candidate = true :=
  List.any_eq_true

theorem current_coverage_depends_only_on_input_membership (left right : List Row)
    (same : ∀ incoming, incoming ∈ left ↔ incoming ∈ right) (candidate : Row) :
    logicalCover (PlainCoverageFlagViews.run left) candidate =
      logicalCover (PlainCoverageFlagViews.run right) candidate := by
  rw [run_coverage_equals_any_same_H_input,run_coverage_equals_any_same_H_input]
  apply bool_equality_of_true_iff
  rw [matchingOffer_true_iff_computed_input,matchingOffer_true_iff_computed_input]
  constructor
  · rintro ⟨incoming,present,covered⟩
    exact ⟨incoming,(same incoming).mp present,covered⟩
  · rintro ⟨incoming,present,covered⟩
    exact ⟨incoming,(same incoming).mpr present,covered⟩

theorem arbitrary_arrival_permutation_preserves_logical_coverage (left right : List Row)
    (permutation : List.Perm left right) (candidate : Row) :
    logicalCover (PlainCoverageFlagViews.run left) candidate =
      logicalCover (PlainCoverageFlagViews.run right) candidate :=
  current_coverage_depends_only_on_input_membership left right
    (fun _ => permutation.mem_iff) candidate

theorem duplicate_input_does_not_change_logical_coverage (incoming candidate : Row) :
    logicalCover (PlainCoverageFlagViews.run [incoming,incoming]) candidate =
      logicalCover (PlainCoverageFlagViews.run [incoming]) candidate := by
  apply current_coverage_depends_only_on_input_membership
  intro row
  simp

theorem cross_H_offer_does_not_change_this_logical_region (state : Views) (incoming candidate : Row)
    (different : incoming.h ≠ candidate.h) :
    logicalCover (PlainCoverageFlagViews.offer state incoming) candidate = logicalCover state candidate := by
  rw [offer_logical_region_union]
  have rejected : sameFlagCover incoming candidate = false := by simp [sameFlagCover,different]
  rw [rejected]
  exact Bool.or_false _

end CurrentCoverageInvariant
