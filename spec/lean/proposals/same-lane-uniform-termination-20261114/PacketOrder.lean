import MarkedClosure

/- Existing owner-queue-empty publication batches, then canonicalize the
   complete native return packet before enqueuing another call. No stale
   descendant is admitted merely because its publication was listed first. -/
namespace SameLanePacketOrder
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedLocalRouting NormalUniformNE SameLaneMarkedClosure

def normalRawReplies : List Value :=
  coldBasis.filterMap fun e => normalApply e ⟨sourceOffer.ap,false,false⟩

def earlyDescendant : Offered := ⟨ProtectedCleanerGrowth.full p 2 .must,false⟩
def earlyPacket := SameLaneUniform.compact true (packet3 [sourceOffer,earlyDescendant])

theorem an_early_descendant_can_start_an_extra_star_query :
    normalRawReplies.any (fun c => c.ap.path.length == 2 && c.ap.mark == some t &&
      c.ap.tail == .must && !c.demand) = true ∧
    (SameLaneMarkedClosure.rows3.flatMap fun row => (plan 3 2 false row earlyDescendant).map Command.seed).any
      (fun q => q.ap.tail == .star && q.ap.mark == some t && q.demand) = true := by decide

theorem egress_coverage_alone_does_not_cancel_that_stale_query :
    earlyPacket.any (fun e => e.2.demand && e.1.tail == .star) = true := by decide

theorem folding_the_whole_existing_normal_packet_prevents_that_query :
    (canonicalActuals normalRawReplies).all (fun c => c.ap.path.isEmpty) = true ∧
    firstReplies = canonicalActuals normalRawReplies ∧
    (canonicalActuals normalRawReplies).length = 2 := by decide

/-- Semantic membership before optional duplicate removal. It makes the
    packet contract independent of enumeration order without a global
    scheduler theorem. All layer, H and mark comparisons are actualCovers. -/
def survives (packet : List Value) (v : Value) : Prop :=
  v ∈ packet ∧ ∀ n ∈ packet, n.ap ≠ v.ap → actualCovers n v = false

theorem enumeration_order_does_not_change_surviving_membership
    (left right : List Value) (sameMembers : ∀ v, v ∈ left ↔ v ∈ right) (v : Value) :
    survives left v ↔ survives right v := by
  constructor
  · intro h
    refine ⟨(sameMembers v).mp h.1,?_⟩
    intro n member different
    exact h.2 n ((sameMembers n).mpr member) different
  · intro h
    refine ⟨(sameMembers v).mpr h.1,?_⟩
    intro n member different
    exact h.2 n ((sameMembers n).mp member) different

theorem both_native_publication_orders_give_the_same_root_classes :
    (canonicalActuals normalRawReplies.reverse).all (fun c => c.ap.path.isEmpty) = true ∧
    (canonicalActuals normalRawReplies.reverse).any (fun c => c.ap.tail == .must) = true ∧
    (canonicalActuals normalRawReplies.reverse).any (fun c => c.ap.tail == .exact) = true := by decide

end SameLanePacketOrder

#print axioms SameLanePacketOrder.an_early_descendant_can_start_an_extra_star_query
#print axioms SameLanePacketOrder.egress_coverage_alone_does_not_cancel_that_stale_query
#print axioms SameLanePacketOrder.folding_the_whole_existing_normal_packet_prevents_that_query
#print axioms SameLanePacketOrder.enumeration_order_does_not_change_surviving_membership
#print axioms SameLanePacketOrder.both_native_publication_orders_give_the_same_root_classes
