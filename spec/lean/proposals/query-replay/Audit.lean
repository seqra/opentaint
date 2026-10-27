import QueryReplay

/- Direct audit of all source theorem declarations and pure definitions.
   No environment-wide enumeration or Classical proof search. -/
#print axioms QueryReplay.subset
#print axioms QueryReplay.permits
#print axioms QueryReplay.permits_iff
#print axioms QueryReplay.unique
#print axioms QueryReplay.unique_mem
#print axioms QueryReplay.unique_nodup
#print axioms QueryReplay.admit
#print axioms QueryReplay.mem_admit
#print axioms QueryReplay.admit_disjoint
#print axioms QueryReplay.admit_nodup
#print axioms QueryReplay.disjoint
#print axioms QueryReplay.admitted_batch_disjoint
#print axioms QueryReplay.transition
#print axioms QueryReplay.findMissing
#print axioms QueryReplay.findMissing_none
#print axioms QueryReplay.findMissing_sound
#print axioms QueryReplay.transition_fresh_witness
#print axioms QueryReplay.newly_authorized_iff
#print axioms QueryReplay.unary_exact_borrow
#print axioms QueryReplay.candidates
#print axioms QueryReplay.candidate_membership
#print axioms QueryReplay.candidate_once
#print axioms QueryReplay.replay
#print axioms QueryReplay.replay_exact
#print axioms QueryReplay.replay_once
#print axioms QueryReplay.complete_nd_required
#print axioms QueryReplay.unrelated_query_no_backfill
#print axioms QueryReplay.already_permitted_no_backfill
#print axioms QueryReplay.zeroPublished
#print axioms QueryReplay.zeroTransition
#print axioms QueryReplay.backward_zero_no_backfill
#print axioms QueryReplay.forward_zero_first_nonempty
#print axioms QueryReplay.regularRawDelta
#print axioms QueryReplay.late_annotation_regular_path
#print axioms QueryReplay.annotation_not_authorization
#print axioms QueryReplay.cumulative_replay_equivalent
#print axioms QueryReplay.controls

#eval QueryReplay.checkControls
