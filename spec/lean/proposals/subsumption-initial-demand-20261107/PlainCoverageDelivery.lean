/-
Selected two-membership delivery reference, 8 November 2026.

Keep plain and protected rows separately, even at identical geometry. The
flag is part of Row identity. The old OR renderer and its countermodel are
imported as historical dependencies only; they are not used for storage or
publication here. Each logical offer publishes its fresh canonical member
with its own flag. A subscriber applies the same class-specific insertion.

Scope: the existing fixed-owner MAY/T/DEMAND geometry of
PlainCoverageFlagViews. Arbitrary input sequences synchronize producer and
consumer authority. Finite parent/child checks cover both flag orders.
This is not a proof of native packet adapters, distributed scheduling,
all-header subsumption, C2 effects or whole-analyzer progress.
-/
import RenderedDeliveryCounterexample
import PlainCoverageFlagViews

namespace PlainCoverageDelivery
open PlainCoverageFlagViews
open FlagMatchedSubsumption (Row)
set_option autoImplicit false

abbrev Link := RenderedDeliveryCounterexample.Link

def plainRows (state : Views) : List Row :=
  state.plain.map (fun g => lift g false)

def protectedRows (state : Views) : List Row :=
  state.flagged.map (fun g => lift g true)

/- The two classes are retained and exposed separately. No exact-coordinate
OR operation is used by this renderer. -/
def renderSeparate (state : Views) : List Row :=
  plainRows state ++ protectedRows state

/- For one offer, addCurrent either keeps the existing class unchanged or
inserts exactly the incoming geometry and removes its covered descendants.
In the latter case that new ordinary membership is the publication delta.
Consumer insertion removes the corresponding descendants at that owner;
no deletion event or raw-offer history is needed in this scalar model. -/
def delivery (before : Views) (incoming : Row) : List Row :=
  if logicalCover before incoming then [] else [incoming]

def forward (link : Link) (incoming : Row) : Link :=
  let after := offer link.producer incoming
  let consumer := (delivery link.producer incoming).foldl offer link.consumer
  ⟨after,consumer⟩

def execute (arrivals : List Row) : Link :=
  arrivals.foldl forward ⟨emptyViews,emptyViews⟩

/- Trace output for an executable proof witness, not a retained runtime
offer archive or an additional authority used by forward. -/
def publicationTrace : Views → List Row → List Row
  | _,[] => []
  | before,incoming :: rest =>
      delivery before incoming ++ publicationTrace (offer before incoming) rest

theorem prefix_self (path : List Nat) :
    FlagMatchedSubsumption.prefixB path path = true := by
  induction path with
  | nil => rfl
  | cons first rest ih => simp [FlagMatchedSubsumption.prefixB,ih]

theorem geometry_covers_itself (g : Geometry) : covers g g = true := by
  simp [covers,prefix_self]

theorem current_insert_covers_its_offer (view : List Geometry) (g : Geometry) :
    (addCurrent view g).any (fun provider => covers provider g) = true := by
  unfold addCurrent
  split
  next covered => exact covered
  next => simp [geometry_covers_itself]

theorem covered_offer_keeps_its_class_authority (state : Views) (incoming : Row)
    (covered : logicalCover state incoming = true) : offer state incoming = state := by
  cases flag : incoming.h with
  | false =>
      have seen : state.plain.any (fun provider => covers provider (geometry incoming)) = true := by
        simpa [logicalCover,flag] using covered
      simp [offer,flag,addCurrent,seen]
  | true =>
      have seen : state.flagged.any (fun provider => covers provider (geometry incoming)) = true := by
        simpa [logicalCover,flag] using covered
      simp [offer,flag,addCurrent,seen]

theorem every_offer_is_covered_in_its_own_class (state : Views) (incoming : Row) :
    logicalCover (offer state incoming) incoming = true := by
  cases flag : incoming.h with
  | false =>
      simpa [logicalCover,offer,flag] using current_insert_covers_its_offer state.plain (geometry incoming)
  | true =>
      simpa [logicalCover,offer,flag] using current_insert_covers_its_offer state.flagged (geometry incoming)

theorem exact_duplicate_has_no_second_delivery (state : Views) (incoming : Row) :
    delivery (offer state incoming) incoming = [] := by
  simp [delivery,every_offer_is_covered_in_its_own_class]

theorem a_fresh_class_membership_changes_authority (state : Views) (incoming : Row)
    (fresh : logicalCover state incoming = false) : offer state incoming ≠ state := by
  intro unchanged
  have covered := every_offer_is_covered_in_its_own_class state incoming
  rw [unchanged,fresh] at covered
  cases covered

theorem an_unchanged_authority_has_no_delivery (state : Views) (incoming : Row)
    (unchanged : offer state incoming = state) : delivery state incoming = [] := by
  have covered := every_offer_is_covered_in_its_own_class state incoming
  rw [unchanged] at covered
  simp [delivery,covered]

theorem every_delivery_is_the_incoming_membership (state : Views) (incoming emitted : Row)
    (member : emitted ∈ delivery state incoming) : emitted = incoming := by
  cases covered : logicalCover state incoming with
  | false => simpa [delivery,covered] using member
  | true => simp [delivery,covered] at member

theorem delivery_keeps_the_memberships_own_flag (state : Views) (incoming emitted : Row)
    (member : emitted ∈ delivery state incoming) : emitted.h = incoming.h := by
  rw [every_delivery_is_the_incoming_membership state incoming emitted member]

theorem plain_rendered_rows_have_plain_identity (state : Views) (row : Row)
    (member : row ∈ plainRows state) : row.h = false := by
  obtain ⟨g,_,same⟩ := List.mem_map.mp member
  rw [← same]
  rfl

theorem protected_rendered_rows_have_protected_identity (state : Views) (row : Row)
    (member : row ∈ protectedRows state) : row.h = true := by
  obtain ⟨g,_,same⟩ := List.mem_map.mp member
  rw [← same]
  rfl

theorem rendered_classes_are_disjoint (state : Views) (row : Row) :
    ¬ (row ∈ plainRows state ∧ row ∈ protectedRows state) := by
  rintro ⟨plain,flagged⟩
  have left := plain_rendered_rows_have_plain_identity state row plain
  have right := protected_rendered_rows_have_protected_identity state row flagged
  rw [left] at right
  cases right

theorem exact_geometry_with_both_flags_has_two_different_row_identities (g : Geometry) :
    lift g false ≠ lift g true := by
  intro same
  have flag := congrArg Row.h same
  cases flag

theorem rendering_keeps_both_exact_memberships (g : Geometry) :
    renderSeparate ⟨[g],[g]⟩ = [lift g false,lift g true] := rfl

theorem rendering_does_not_collapse_the_two_flags (g : Geometry) :
    (renderSeparate ⟨[g],[g]⟩).length = 2 := rfl

theorem one_delivery_preserves_synchronized_authority (link : Link) (incoming : Row)
    (synchronized : link.consumer = link.producer) :
    (forward link incoming).consumer = (forward link incoming).producer := by
  cases covered : logicalCover link.producer incoming with
  | false => simp [forward,delivery,covered,synchronized]
  | true =>
      have unchanged := covered_offer_keeps_its_class_authority link.producer incoming covered
      simp [forward,delivery,covered,synchronized,unchanged]

theorem every_delivery_sequence_preserves_synchronized_authority
    (arrivals : List Row) (link : Link) (synchronized : link.consumer = link.producer) :
    (arrivals.foldl forward link).consumer = (arrivals.foldl forward link).producer := by
  induction arrivals generalizing link with
  | nil => exact synchronized
  | cons incoming rest ih =>
      exact ih (forward link incoming) (one_delivery_preserves_synchronized_authority link incoming synchronized)

theorem delivery_never_changes_the_producers_canonical_insert
    (arrivals : List Row) (link : Link) :
    (arrivals.foldl forward link).producer = arrivals.foldl offer link.producer := by
  induction arrivals generalizing link with
  | nil => rfl
  | cons incoming rest ih => exact ih (forward link incoming)

theorem every_execution_has_the_complete_authority (arrivals : List Row) :
    (execute arrivals).producer = run arrivals ∧ (execute arrivals).consumer = run arrivals := by
  have producer := delivery_never_changes_the_producers_canonical_insert arrivals ⟨emptyViews,emptyViews⟩
  have synchronized := every_delivery_sequence_preserves_synchronized_authority arrivals
    (⟨emptyViews,emptyViews⟩ : Link) rfl
  exact ⟨producer,synchronized.trans producer⟩

theorem downstream_has_every_class_coverage_predicate (arrivals : List Row) (candidate : Row) :
    logicalCover (execute arrivals).consumer candidate = logicalCover (run arrivals) candidate := by
  rw [(every_execution_has_the_complete_authority arrivals).2]

theorem both_exact_flag_orders_have_the_same_producer_and_consumer (g : Geometry) :
    (execute [lift g true,lift g false]).producer = ⟨[g],[g]⟩ ∧
    (execute [lift g true,lift g false]).consumer = ⟨[g],[g]⟩ ∧
    (execute [lift g false,lift g true]).producer = ⟨[g],[g]⟩ ∧
    (execute [lift g false,lift g true]).consumer = ⟨[g],[g]⟩ := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem both_exact_flag_orders_render_both_memberships (g : Geometry) :
    renderSeparate (execute [lift g true,lift g false]).consumer = [lift g false,lift g true] ∧
    renderSeparate (execute [lift g false,lift g true]).consumer = [lift g false,lift g true] := by
  exact ⟨rfl,rfl⟩

theorem both_arrival_orders_publish_each_class (g : Geometry) :
    publicationTrace emptyViews [lift g true,lift g false] = [lift g true,lift g false] ∧
    publicationTrace emptyViews [lift g false,lift g true] = [lift g false,lift g true] := by
  exact ⟨rfl,rfl⟩

theorem exact_flag_publication_orders_differ_only_by_permutation (g : Geometry) :
    (publicationTrace emptyViews [lift g true,lift g false]).Perm
      (publicationTrace emptyViews [lift g false,lift g true]) := by
  exact List.Perm.swap _ _ []

theorem a_late_plain_row_is_a_real_separate_publication (g : Geometry) :
    delivery (run [lift g true]) (lift g false) = [lift g false] := rfl

theorem repeated_exact_plain_and_protected_offers_emit_nothing_more :
    publicationTrace emptyViews [parent true,parent false,parent true,parent false] =
      [parent true,parent false] ∧
    publicationTrace emptyViews [parent false,parent true,parent false,parent true] =
      [parent false,parent true] := by decide

theorem plain_child_coverage_is_independent_of_parent_flag_arrival_order :
    logicalCover (execute [parent true,parent false]).consumer (child false) = true ∧
    logicalCover (execute [parent false,parent true]).consumer (child false) = true := by decide

theorem child_and_parent_orders_have_the_same_complete_downstream_authority :
    (execute [child false,parent true,parent false,child true]).consumer = ⟨[parentGeometry],[parentGeometry]⟩ ∧
    (execute [parent false,parent true,child true,child false]).consumer = ⟨[parentGeometry],[parentGeometry]⟩ := by decide

theorem a_protected_parent_does_not_cover_a_plain_child :
    logicalCover (execute [parent true]).consumer (child false) = false := by decide

theorem a_plain_parent_does_not_cover_a_protected_child :
    logicalCover (execute [parent false]).consumer (child true) = false := by decide

theorem ordinary_pass_keeps_delivery_class (state : Views) (incoming emitted : Row)
    (member : emitted ∈ delivery state incoming) : (passRow emitted).h = incoming.h := by
  exact delivery_keeps_the_memberships_own_flag state incoming emitted member

theorem ordinary_plain_pass_cannot_create_protection (state : Views) (incoming emitted : Row)
    (plain : incoming.h = false) (member : emitted ∈ delivery state incoming) :
    (passRow emitted).h = false := by
  exact (ordinary_pass_keeps_delivery_class state incoming emitted member).trans plain

end PlainCoverageDelivery

#print axioms PlainCoverageDelivery.prefix_self
#print axioms PlainCoverageDelivery.geometry_covers_itself
#print axioms PlainCoverageDelivery.current_insert_covers_its_offer
#print axioms PlainCoverageDelivery.covered_offer_keeps_its_class_authority
#print axioms PlainCoverageDelivery.every_offer_is_covered_in_its_own_class
#print axioms PlainCoverageDelivery.exact_duplicate_has_no_second_delivery
#print axioms PlainCoverageDelivery.a_fresh_class_membership_changes_authority
#print axioms PlainCoverageDelivery.an_unchanged_authority_has_no_delivery
#print axioms PlainCoverageDelivery.every_delivery_is_the_incoming_membership
#print axioms PlainCoverageDelivery.delivery_keeps_the_memberships_own_flag
#print axioms PlainCoverageDelivery.plain_rendered_rows_have_plain_identity
#print axioms PlainCoverageDelivery.protected_rendered_rows_have_protected_identity
#print axioms PlainCoverageDelivery.rendered_classes_are_disjoint
#print axioms PlainCoverageDelivery.exact_geometry_with_both_flags_has_two_different_row_identities
#print axioms PlainCoverageDelivery.rendering_keeps_both_exact_memberships
#print axioms PlainCoverageDelivery.rendering_does_not_collapse_the_two_flags
#print axioms PlainCoverageDelivery.one_delivery_preserves_synchronized_authority
#print axioms PlainCoverageDelivery.every_delivery_sequence_preserves_synchronized_authority
#print axioms PlainCoverageDelivery.delivery_never_changes_the_producers_canonical_insert
#print axioms PlainCoverageDelivery.every_execution_has_the_complete_authority
#print axioms PlainCoverageDelivery.downstream_has_every_class_coverage_predicate
#print axioms PlainCoverageDelivery.both_exact_flag_orders_have_the_same_producer_and_consumer
#print axioms PlainCoverageDelivery.both_exact_flag_orders_render_both_memberships
#print axioms PlainCoverageDelivery.both_arrival_orders_publish_each_class
#print axioms PlainCoverageDelivery.exact_flag_publication_orders_differ_only_by_permutation
#print axioms PlainCoverageDelivery.a_late_plain_row_is_a_real_separate_publication
#print axioms PlainCoverageDelivery.repeated_exact_plain_and_protected_offers_emit_nothing_more
#print axioms PlainCoverageDelivery.plain_child_coverage_is_independent_of_parent_flag_arrival_order
#print axioms PlainCoverageDelivery.child_and_parent_orders_have_the_same_complete_downstream_authority
#print axioms PlainCoverageDelivery.a_protected_parent_does_not_cover_a_plain_child
#print axioms PlainCoverageDelivery.a_plain_parent_does_not_cover_a_protected_child
#print axioms PlainCoverageDelivery.ordinary_pass_keeps_delivery_class
#print axioms PlainCoverageDelivery.ordinary_plain_pass_cannot_create_protection
