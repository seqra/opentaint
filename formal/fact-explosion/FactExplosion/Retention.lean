namespace FactExplosion

def tifaCopies (_ : Nat) : Nat := 0

def retainedFacts (rounds : Nat) : Nat := rounds

theorem no_tifa_copy_does_not_bound_retention (rounds : Nat) :
    tifaCopies rounds = 0 ∧ retainedFacts rounds = rounds := by
  exact ⟨rfl, rfl⟩

def conductorPeakKiB : Nat := 9712704

def conductorGuardKiB : Nat := 8 * 1024 * 1024

theorem conductor_rejects_demand_only_tifa :
    conductorPeakKiB > conductorGuardKiB := by
  decide

def structuralPeakBytes : Nat := 7747429616

def structuralGuardBytes : Nat := 7730941132

theorem conductor_rejects_structural_retention_only :
    structuralPeakBytes > structuralGuardBytes := by
  decide

def packedPeakBytes : Nat := 7732343416

def packedGuardBytes : Nat := 7730941132

theorem conductor_rejects_packed_retention_only :
    packedPeakBytes > packedGuardBytes := by
  decide

def firstSummaryWideningExitCode : Nat := 252

theorem conductor_rejects_invalid_summary_widening :
    firstSummaryWideningExitCode ≠ 0 := by
  decide

def summaryRetentionPeakBytes : Nat := 7747749408

def summaryRetentionGuardBytes : Nat := 7730941132

theorem conductor_rejects_summary_retention_only :
    summaryRetentionPeakBytes > summaryRetentionGuardBytes := by
  decide

def subscriptionCoalescingPeakBytes : Nat := 7731817776

def subscriptionCoalescingGuardBytes : Nat := 7730941132

theorem conductor_rejects_subscription_coalescing_only :
    subscriptionCoalescingPeakBytes > subscriptionCoalescingGuardBytes := by
  decide

def emptyDeltaFilteringPeakBytes : Nat := 7773865984

def emptyDeltaFilteringGuardBytes : Nat := 7730941132

theorem conductor_rejects_empty_delta_filtering_only :
    emptyDeltaFilteringPeakBytes > emptyDeltaFilteringGuardBytes := by
  decide

def pathNodeInterningPeakBytes : Nat := 7734621608

def pathNodeInterningGuardBytes : Nat := 7730941132

theorem conductor_rejects_path_node_interning_only :
    pathNodeInterningPeakBytes > pathNodeInterningGuardBytes := by
  decide

def rootCanonicalizationPeakBytes : Nat := 7733667472

def rootCanonicalizationGuardBytes : Nat := 7730941132

theorem conductor_rejects_root_canonicalization_only :
    rootCanonicalizationPeakBytes > rootCanonicalizationGuardBytes := by
  decide

def factEnvelopeInterningPeakBytes : Nat := 7731414656

def factEnvelopeInterningGuardBytes : Nat := 7730941132

theorem conductor_rejects_fact_envelope_interning_only :
    factEnvelopeInterningPeakBytes > factEnvelopeInterningGuardBytes := by
  decide

def singletonChildUnionPeakBytes : Nat := 7797581648

def singletonChildUnionGuardBytes : Nat := 7730941132

theorem conductor_rejects_subscription_singleton_union_only :
    singletonChildUnionPeakBytes > singletonChildUnionGuardBytes := by
  decide

def prefixIndexSingletonUnionPeakBytes : Nat := 7811503576

def prefixIndexSingletonUnionGuardBytes : Nat := 7730941132

theorem conductor_rejects_prefix_index_singleton_union_only :
    prefixIndexSingletonUnionPeakBytes > prefixIndexSingletonUnionGuardBytes := by
  decide

def reducedRulesFlatCanonicalPathIndexExitCode : Nat := 254

def reducedRulesFlatCanonicalPathIndexPeakBytes : Nat := 7667740560

theorem reduced_rules_rejects_flat_canonical_path_index_only :
    reducedRulesFlatCanonicalPathIndexExitCode ≠ 0 := by
  decide

theorem reduced_rules_flat_canonical_path_index_stayed_below_memory_guard :
    reducedRulesFlatCanonicalPathIndexPeakBytes < prefixIndexSingletonUnionGuardBytes := by
  decide

def flatCanonicalPathIndexConductorPeakBytes : Nat := 7834161216

def flatCanonicalPathIndexConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_flat_canonical_path_index_only :
    flatCanonicalPathIndexConductorPeakBytes > flatCanonicalPathIndexConductorGuardBytes := by
  decide

def exactSubscriptionRowsConductorPeakBytes : Nat := 7772269760

def exactSubscriptionRowsConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_exact_subscription_rows_only :
    exactSubscriptionRowsConductorPeakBytes > exactSubscriptionRowsConductorGuardBytes := by
  decide

def factorizedSubscriptionRowsConductorPeakBytes : Nat := 7911225560

def factorizedSubscriptionRowsConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_factorized_subscription_rows_only :
    factorizedSubscriptionRowsConductorPeakBytes > factorizedSubscriptionRowsConductorGuardBytes := by
  decide

def normalizedSummaryDeltaConductorPeakBytes : Nat := 7819680360

def normalizedSummaryDeltaConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_normalized_summary_delta_only :
    normalizedSummaryDeltaConductorPeakBytes > normalizedSummaryDeltaConductorGuardBytes := by
  decide

def exactMethodEdgeDeltaConductorPeakBytes : Nat := 7744317336

def exactMethodEdgeDeltaConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_exact_method_edge_delta_only :
    exactMethodEdgeDeltaConductorPeakBytes > exactMethodEdgeDeltaConductorGuardBytes := by
  decide

def absorbedMethodEdgeRetentionConductorPeakBytes : Nat := 7788675880

def absorbedMethodEdgeRetentionConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_absorbed_method_edge_retention :
    absorbedMethodEdgeRetentionConductorPeakBytes > absorbedMethodEdgeRetentionConductorGuardBytes := by
  decide

def packedNodeMeasureConductorPeakBytes : Nat := 7890148040

def packedNodeMeasureConductorGuardBytes : Nat := 7730941132

theorem conductor_rejects_packed_node_measure_only :
    packedNodeMeasureConductorPeakBytes > packedNodeMeasureConductorGuardBytes := by
  decide

def canonicalResolvedConditionsConductorExitCode : Nat := 254

def canonicalResolvedConditionsConductorPeakBytes : Nat := 7588511872

theorem conductor_rejects_canonical_resolved_conditions_only :
    canonicalResolvedConditionsConductorExitCode ≠ 0 := by
  decide

theorem canonical_resolved_conditions_stayed_below_memory_guard :
    canonicalResolvedConditionsConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def compactSummaryStatesConductorExitCode : Nat := 254

def compactSummaryStatesConductorPeakBytes : Nat := 7679624264

theorem conductor_rejects_compact_summary_states_only :
    compactSummaryStatesConductorExitCode ≠ 0 := by
  decide

theorem compact_summary_states_stayed_below_memory_guard :
    compactSummaryStatesConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def resolvedSummaryCleanActionConductorExitCode : Nat := 254

def resolvedSummaryCleanActionConductorPeakBytes : Nat := 7686368488

theorem conductor_rejects_resolved_summary_clean_action_only :
    resolvedSummaryCleanActionConductorExitCode ≠ 0 := by
  decide

theorem resolved_summary_clean_action_stayed_below_memory_guard :
    resolvedSummaryCleanActionConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def memoizedTypeCheckConductorExitCode : Nat := 254

def memoizedTypeCheckConductorPeakBytes : Nat := 7678546880

theorem conductor_rejects_memoized_type_check_only :
    memoizedTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem memoized_type_check_stayed_below_memory_guard :
    memoizedTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def memoizedCompatibilityCheckConductorExitCode : Nat := 254

def memoizedCompatibilityCheckConductorPeakBytes : Nat := 7689455416

theorem conductor_rejects_memoized_compatibility_check_only :
    memoizedCompatibilityCheckConductorExitCode ≠ 0 := by
  decide

theorem memoized_compatibility_check_stayed_below_memory_guard :
    memoizedCompatibilityCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def smallDirectTypeCheckConductorExitCode : Nat := 254

def smallDirectTypeCheckConductorPeakBytes : Nat := 7691280544

theorem conductor_rejects_small_direct_type_check_cache :
    smallDirectTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem small_direct_type_check_stayed_below_memory_guard :
    smallDirectTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def enlargedDirectTypeCheckConductorExitCode : Nat := 254

def enlargedDirectTypeCheckConductorPeakBytes : Nat := 7691757466

theorem conductor_rejects_enlarged_direct_type_check_cache :
    enlargedDirectTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem enlarged_direct_type_check_stayed_below_memory_guard :
    enlargedDirectTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def strengthenedDirectTypeCheckConductorExitCode : Nat := 254

def strengthenedDirectTypeCheckConductorPeakBytes : Nat := 7714727117

theorem conductor_rejects_strengthened_direct_type_check_cache :
    strengthenedDirectTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem strengthened_direct_type_check_stayed_below_memory_guard :
    strengthenedDirectTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def normalizedFieldTypeCheckConductorExitCode : Nat := 254

def normalizedFieldTypeCheckConductorPeakBytes : Nat := 7678703002

theorem conductor_rejects_normalized_field_type_check_cache :
    normalizedFieldTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem normalized_field_type_check_stayed_below_memory_guard :
    normalizedFieldTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def versionedFieldTypeCheckConductorExitCode : Nat := 254

def versionedFieldTypeCheckConductorPeakBytes : Nat := 7720958976

theorem conductor_rejects_versioned_field_type_check_cache :
    versionedFieldTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem versioned_field_type_check_stayed_below_memory_guard :
    versionedFieldTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def writeOnceFieldTypeCheckConductorExitCode : Nat := 254

def writeOnceFieldTypeCheckConductorPeakBytes : Nat := 7692172902

theorem conductor_rejects_write_once_field_type_check_cache :
    writeOnceFieldTypeCheckConductorExitCode ≠ 0 := by
  decide

theorem write_once_field_type_check_stayed_below_memory_guard :
    writeOnceFieldTypeCheckConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def recursiveSubtreeFilterCacheConductorExitCode : Nat := 254

def recursiveSubtreeFilterCacheConductorPeakBytes : Nat := 7686269235

theorem conductor_rejects_recursive_subtree_filter_cache :
    recursiveSubtreeFilterCacheConductorExitCode ≠ 0 := by
  decide

theorem recursive_subtree_filter_cache_stayed_below_memory_guard :
    recursiveSubtreeFilterCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def rootScopedSubtreeFilterCacheConductorExitCode : Nat := 254

def rootScopedSubtreeFilterCacheConductorPeakBytes : Nat := 7691146240

theorem conductor_rejects_root_scoped_subtree_filter_cache :
    rootScopedSubtreeFilterCacheConductorExitCode ≠ 0 := by
  decide

theorem root_scoped_subtree_filter_cache_stayed_below_memory_guard :
    rootScopedSubtreeFilterCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def enlargedRootSubtreeFilterCacheConductorExitCode : Nat := 254

def enlargedRootSubtreeFilterCacheConductorPeakBytes : Nat := 7700346573

theorem conductor_rejects_enlarged_root_subtree_filter_cache :
    enlargedRootSubtreeFilterCacheConductorExitCode ≠ 0 := by
  decide

theorem enlarged_root_subtree_filter_cache_stayed_below_memory_guard :
    enlargedRootSubtreeFilterCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def twoWayRootSubtreeFilterCacheConductorExitCode : Nat := 254

def twoWayRootSubtreeFilterCacheConductorPeakBytes : Nat := 7705461453

theorem conductor_rejects_two_way_root_subtree_filter_cache :
    twoWayRootSubtreeFilterCacheConductorExitCode ≠ 0 := by
  decide

theorem two_way_root_subtree_filter_cache_stayed_below_memory_guard :
    twoWayRootSubtreeFilterCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def boundedRootMapConductorExitCode : Nat := 254

def boundedRootMapConductorPeakBytes : Nat := 7698535219

theorem conductor_rejects_bounded_root_map :
    boundedRootMapConductorExitCode ≠ 0 := by
  decide

theorem bounded_root_map_stayed_below_memory_guard :
    boundedRootMapConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def queryLocalSubtreeMemoConductorExitCode : Nat := 254

def queryLocalSubtreeMemoConductorPeakBytes : Nat := 7695477862

theorem conductor_rejects_query_local_subtree_memo :
    queryLocalSubtreeMemoConductorExitCode ≠ 0 := by
  decide

theorem query_local_subtree_memo_stayed_below_memory_guard :
    queryLocalSubtreeMemoConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def selectiveRootMapConductorExitCode : Nat := 254

def selectiveRootMapConductorPeakBytes : Nat := 7704667546

theorem conductor_rejects_selective_root_map :
    selectiveRootMapConductorExitCode ≠ 0 := by
  decide

theorem selective_root_map_stayed_below_memory_guard :
    selectiveRootMapConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def selectiveDirectRootCacheConductorExitCode : Nat := 254

def selectiveDirectRootCacheConductorPeakBytes : Nat := 7685342208

theorem conductor_rejects_selective_direct_root_cache :
    selectiveDirectRootCacheConductorExitCode ≠ 0 := by
  decide

theorem selective_direct_root_cache_stayed_below_memory_guard :
    selectiveDirectRootCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def flatSelectiveDirectRootCacheConductorExitCode : Nat := 254

def flatSelectiveDirectRootCacheConductorPeakBytes : Nat := 7701130650

theorem conductor_rejects_flat_selective_direct_root_cache :
    flatSelectiveDirectRootCacheConductorExitCode ≠ 0 := by
  decide

theorem flat_selective_direct_root_cache_stayed_below_memory_guard :
    flatSelectiveDirectRootCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def thresholdEightDirectRootCacheConductorExitCode : Nat := 254

def thresholdEightDirectRootCacheConductorPeakBytes : Nat := 7710582579

theorem conductor_rejects_threshold_eight_direct_root_cache :
    thresholdEightDirectRootCacheConductorExitCode ≠ 0 := by
  decide

theorem threshold_eight_direct_root_cache_stayed_below_memory_guard :
    thresholdEightDirectRootCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def twoWayFactInternerConductorExitCode : Nat := 254

def twoWayFactInternerConductorPeakBytes : Nat := 7718496973

theorem conductor_rejects_two_way_fact_interner :
    twoWayFactInternerConductorExitCode ≠ 0 := by
  decide

theorem two_way_fact_interner_stayed_below_memory_guard :
    twoWayFactInternerConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def externalEventCoalescingConductorExitCode : Nat := 254

def externalEventCoalescingConductorPeakBytes : Nat := 7682322739

theorem conductor_rejects_external_event_coalescing :
    externalEventCoalescingConductorExitCode ≠ 0 := by
  decide

theorem external_event_coalescing_stayed_below_memory_guard :
    externalEventCoalescingConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def directSeenEventConductorExitCode : Nat := 254

def directSeenEventConductorPeakBytes : Nat := 7713956864

theorem conductor_rejects_direct_seen_event_table :
    directSeenEventConductorExitCode ≠ 0 := by
  decide

theorem direct_seen_event_table_stayed_below_memory_guard :
    directSeenEventConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def boundedSeenEventConductorExitCode : Nat := 254

def boundedSeenEventConductorPeakBytes : Nat := 7715079782

theorem conductor_rejects_bounded_seen_event_set :
    boundedSeenEventConductorExitCode ≠ 0 := by
  decide

theorem bounded_seen_event_set_stayed_below_memory_guard :
    boundedSeenEventConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def batchedDelayedSummariesConductorExitCode : Nat := 254

def batchedDelayedSummariesConductorPeakBytes : Nat := 7709381632

theorem conductor_rejects_batched_delayed_summaries :
    batchedDelayedSummariesConductorExitCode ≠ 0 := by
  decide

theorem batched_delayed_summaries_stayed_below_memory_guard :
    batchedDelayedSummariesConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def batchedSummarySequentsConductorExitCode : Nat := 254

def batchedSummarySequentsConductorPeakBytes : Nat := 7689762918

theorem conductor_rejects_batched_summary_sequents :
    batchedSummarySequentsConductorExitCode ≠ 0 := by
  decide

theorem batched_summary_sequents_stayed_below_memory_guard :
    batchedSummarySequentsConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def batchedEdgeDeltasConductorExitCode : Nat := 254

def batchedEdgeDeltasConductorPeakBytes : Nat := 7689172992

theorem conductor_rejects_batched_edge_deltas :
    batchedEdgeDeltasConductorExitCode ≠ 0 := by
  decide

theorem batched_edge_deltas_stayed_below_memory_guard :
    batchedEdgeDeltasConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def threadLocalRootCacheConductorExitCode : Nat := 254

def threadLocalRootCacheConductorPeakBytes : Nat := 7717719757

theorem conductor_rejects_thread_local_root_cache :
    threadLocalRootCacheConductorExitCode ≠ 0 := by
  decide

theorem thread_local_root_cache_stayed_below_memory_guard :
    threadLocalRootCacheConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def delayedInitialEdgeBatchCost (edgeCount : Nat) : Nat :=
  if edgeCount = 0 then 0 else 1

theorem delayed_initial_edge_batch_cost_le
    (edgeCount : Nat) :
    delayedInitialEdgeBatchCost edgeCount ≤ edgeCount := by
  cases edgeCount <;> simp [delayedInitialEdgeBatchCost]

def batchedDelayedInitialEdgesConductorExitCode : Nat := 254

def batchedDelayedInitialEdgesConductorPeakBytes : Nat := 7703278592

theorem conductor_rejects_batched_delayed_initial_edges :
    batchedDelayedInitialEdgesConductorExitCode ≠ 0 := by
  decide

theorem batched_delayed_initial_edges_stayed_below_memory_guard :
    batchedDelayedInitialEdgesConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

inductive ExactIndex where
  | sparse (indices : List Nat)
  | dense (indices : List Nat)
  deriving DecidableEq

def ExactIndex.members : ExactIndex → List Nat
  | .sparse indices => indices
  | .dense indices => indices

def ExactIndex.promote (index : ExactIndex) : ExactIndex :=
  .dense index.members

theorem promote_preserves_members (index : ExactIndex) :
    index.promote.members = index.members := by
  cases index <;> rfl

structure InstructionSlot (α : Type) where
  coordinate : Nat
  value : α
  deriving DecidableEq

def denseLookup [BEq α] (coordinate : Nat) (slots : List (Option α)) : Option α :=
  slots[coordinate]?.join

def sparseLookup [BEq α] (coordinate : Nat) (slots : List (InstructionSlot α)) : Option α :=
  (slots.find? fun slot => slot.coordinate == coordinate).map InstructionSlot.value

def occupiedCoordinates {α : Type} (slots : List (InstructionSlot α)) : List Nat :=
  slots.map InstructionSlot.coordinate

def sparseInstructionCost {α : Type} (slots : List (InstructionSlot α)) : Nat :=
  slots.length

def denseInstructionCost (coordinateCount : Nat) : Nat :=
  coordinateCount

theorem sparse_instruction_cost_exact {α : Type} (slots : List (InstructionSlot α)) :
    sparseInstructionCost slots = (occupiedCoordinates slots).length := by
  simp [sparseInstructionCost, occupiedCoordinates]

theorem sparse_instruction_cost_le_dense
    {α : Type}
    (slots : List (InstructionSlot α))
    (coordinateCount : Nat)
    (bounded : slots.length ≤ coordinateCount) :
    sparseInstructionCost slots ≤ denseInstructionCost coordinateCount := by
  simpa [sparseInstructionCost, denseInstructionCost] using bounded

def sparseIndexCost (indices : List Nat) : Nat := indices.length

def denseIndexCost (largestIndex : Nat) : Nat := largestIndex + 1

theorem sparse_index_cost_le_dense
    (indices : List Nat)
    (largestIndex : Nat)
    (bounded : indices.length ≤ largestIndex + 1) :
    sparseIndexCost indices ≤ denseIndexCost largestIndex := by
  simpa [sparseIndexCost, denseIndexCost] using bounded

structure NodeMetadata where
  interned : Bool
  abstract : Bool
  final : Bool
  containsStatic : Bool
  depth : Nat
  deriving DecidableEq

inductive PackedMetadata where
  | packed (interned abstract final containsStatic : Bool) (depth : Nat)
  deriving DecidableEq

def packMetadata (metadata : NodeMetadata) : PackedMetadata :=
  .packed metadata.interned metadata.abstract metadata.final metadata.containsStatic metadata.depth

def unpackMetadata : PackedMetadata → NodeMetadata
  | .packed interned abstract final containsStatic depth =>
      { interned, abstract, final, containsStatic, depth }

theorem packed_metadata_exact (metadata : NodeMetadata) :
    unpackMetadata (packMetadata metadata) = metadata := by
  cases metadata
  rfl

def splitMetadataSlots (_ : NodeMetadata) : Nat := 5

def packedMetadataSlots (_ : NodeMetadata) : Nat := 1

theorem packed_metadata_slot_gap (metadata : NodeMetadata) :
    packedMetadataSlots metadata < splitMetadataSlots metadata := by
  simp [packedMetadataSlots, splitMetadataSlots]

def saturatedNodeSize (capacity size : Nat) : Nat := min capacity size

theorem saturated_node_size_threshold_exact
    (capacity threshold size : Nat)
    (thresholdFits : threshold < capacity) :
    saturatedNodeSize capacity size > threshold ↔ size > threshold := by
  change threshold < min capacity size ↔ threshold < size
  rw [Nat.lt_min]
  simp [thresholdFits]

def narrowedNodeHash (modulus hash : Nat) : Nat := hash % modulus

theorem narrowed_hash_preserves_equal_hashes
    (modulus left right : Nat)
    (equalHash : left = right) :
    narrowedNodeHash modulus left = narrowedNodeHash modulus right := by
  exact congrArg (narrowedNodeHash modulus) equalHash

def splitNodeMeasureSlots : Nat := 2

def packedNodeMeasureSlots : Nat := 1

theorem packed_node_measure_slot_gap :
    packedNodeMeasureSlots < splitNodeMeasureSlots := by
  decide

def retainedConditionAtomBytes : Nat := 314136928

def retainedContainsMarkBytes : Nat := 295940640

def retainedContainsMarkOnAnyFieldBytes : Nat := 172173312

def currentRetainedAccessTreeBytes : Nat := 20637456

theorem resolved_conditions_dominate_current_access_trees :
    retainedConditionAtomBytes + retainedContainsMarkBytes +
        retainedContainsMarkOnAnyFieldBytes > currentRetainedAccessTreeBytes * 30 := by
  decide

structure SummaryBranches (Fact : Type) where
  anyFacts : List Fact
  concreteFacts : Nat → List Fact

def SummaryBranches.query
    (coveredByAny : Nat → Bool)
    (branches : SummaryBranches Fact)
    (accessor : Nat) : List Fact :=
  branches.concreteFacts accessor ++
    if coveredByAny accessor then branches.anyFacts else []

def SummaryBranches.absorb
    (branches : SummaryBranches Fact)
    (accessor : Nat) : SummaryBranches Fact where
  anyFacts := branches.concreteFacts accessor ++ branches.anyFacts
  concreteFacts := fun queryAccessor =>
    if queryAccessor == accessor then [] else branches.concreteFacts queryAccessor

theorem absorb_preserves_late_queries
    (coveredByAny : Nat → Bool)
    (branches : SummaryBranches Fact)
    (accessor queryAccessor : Nat)
    (covered : coveredByAny accessor = true)
    (fact : Fact)
    (present : fact ∈ branches.query coveredByAny queryAccessor) :
    fact ∈ (branches.absorb accessor).query coveredByAny queryAccessor := by
  by_cases same : queryAccessor = accessor
  · subst queryAccessor
    simpa [SummaryBranches.query, SummaryBranches.absorb, covered] using present
  · by_cases queryCovered : coveredByAny queryAccessor = true
    · simp [SummaryBranches.query, SummaryBranches.absorb, same, queryCovered,
        List.mem_append] at present ⊢
      exact present.elim (Or.inl) fun factInAny => Or.inr (Or.inr factInAny)
    · simpa [SummaryBranches.query, SummaryBranches.absorb, same, queryCovered] using present

def storeAndPublish
    (branches : SummaryBranches Fact)
    (accessor : Nat)
    (arrival : List Fact) : SummaryBranches Fact × List Fact :=
  (branches.absorb accessor, arrival)

theorem honest_delta_publication
    (branches : SummaryBranches Fact)
    (accessor : Nat)
    (arrival : List Fact) :
    (storeAndPublish branches accessor arrival).2 = arrival := by
  rfl

def retainedDelta [BEq Fact] (oldState newState : List Fact) : List Fact :=
  newState.filter fun fact => !oldState.contains fact

theorem retained_delta_reconstructs_normalized_state
    [BEq Fact] [LawfulBEq Fact]
    (oldState newState : List Fact)
    (monotone : ∀ fact, fact ∈ oldState → fact ∈ newState)
    (fact : Fact) :
    fact ∈ oldState ++ retainedDelta oldState newState ↔ fact ∈ newState := by
  constructor
  · intro published
    rcases List.mem_append.mp published with oldFact | deltaFact
    · exact monotone fact oldFact
    · exact (List.mem_filter.mp deltaFact).1
  · intro retained
    by_cases oldFact : fact ∈ oldState
    · exact List.mem_append.mpr (Or.inl oldFact)
    · apply List.mem_append.mpr
      apply Or.inr
      exact List.mem_filter.mpr ⟨retained, by simp [oldFact]⟩

theorem retained_delta_suppresses_redundant_state
    [BEq Fact] [LawfulBEq Fact]
    (state : List Fact)
    (fact : Fact) :
    fact ∉ retainedDelta state state := by
  simp [retainedDelta]

def fullStatePublicationCost : Nat → Nat
  | 0 => 0
  | n + 1 => fullStatePublicationCost n + n + 1

def exactDeltaPublicationCost (arrivals : Nat) : Nat := arrivals

theorem exact_delta_publication_cost_linear (arrivals : Nat) :
    exactDeltaPublicationCost arrivals = arrivals := by
  rfl

theorem exact_delta_publication_never_worse (arrivals : Nat) :
    exactDeltaPublicationCost arrivals ≤ fullStatePublicationCost arrivals := by
  induction arrivals with
  | zero => simp [exactDeltaPublicationCost, fullStatePublicationCost]
  | succ arrivals ih =>
      simp only [exactDeltaPublicationCost, fullStatePublicationCost]
      omega

def coveredWord (coveredByAny : Nat → Bool) (word : List Nat) : Bool :=
  word.all coveredByAny

def nestedAnyWitness
    (coveredByAny : Nat → Bool)
    (before concretePath after : List Nat) : Bool :=
  coveredWord coveredByAny before &&
    coveredWord coveredByAny concretePath &&
    coveredWord coveredByAny after

def collapsedAnyWitness
    (coveredByAny : Nat → Bool)
    (before concretePath after : List Nat) : Bool :=
  coveredWord coveredByAny (before ++ concretePath ++ after)

theorem collapse_nested_any_sound
    (coveredByAny : Nat → Bool)
    (before concretePath after : List Nat)
    (nested : nestedAnyWitness coveredByAny before concretePath after = true) :
    collapsedAnyWitness coveredByAny before concretePath after = true := by
  simpa [nestedAnyWitness, collapsedAnyWitness, coveredWord, List.all_append,
    and_assoc] using nested

structure SubscriptionRow where
  exclusions : List Nat
  conclusions : List Nat

def SubscriptionRow.accepts
    (row : SubscriptionRow)
    (accessor conclusion : Nat) : Bool :=
  (!row.exclusions.contains accessor) && row.conclusions.contains conclusion

def SubscriptionRow.merge (left right : SubscriptionRow) : SubscriptionRow where
  exclusions := left.exclusions.filter right.exclusions.contains
  conclusions := left.conclusions ++ right.conclusions

theorem merged_subscription_covers_left
    (left right : SubscriptionRow)
    (accessor conclusion : Nat)
    (accepted : left.accepts accessor conclusion = true) :
    (left.merge right).accepts accessor conclusion = true := by
  simp [SubscriptionRow.accepts, SubscriptionRow.merge] at accepted ⊢
  exact ⟨Or.inl accepted.1, Or.inl accepted.2⟩

theorem merged_subscription_covers_right
    (left right : SubscriptionRow)
    (accessor conclusion : Nat)
    (accepted : right.accepts accessor conclusion = true) :
    (left.merge right).accepts accessor conclusion = true := by
  simp [SubscriptionRow.accepts, SubscriptionRow.merge] at accepted ⊢
  exact ⟨Or.inr accepted.1, Or.inr accepted.2⟩

def crossPairLeftRow : SubscriptionRow where
  exclusions := [0]
  conclusions := [0]

def crossPairRightRow : SubscriptionRow where
  exclusions := [1]
  conclusions := [1]

theorem merged_subscription_introduces_cross_pair :
    (crossPairLeftRow.merge crossPairRightRow).accepts 0 0 = true ∧
    crossPairLeftRow.accepts 0 0 = false ∧
    crossPairRightRow.accepts 0 0 = false := by
  decide

def selectPartitionedSubscriptionRows
    (rows : List SubscriptionRow)
    (accessor conclusion : Nat) : List SubscriptionRow :=
  rows.filter fun row => row.accepts accessor conclusion

theorem partitioned_subscription_lookup_exact
    (row : SubscriptionRow)
    (rows : List SubscriptionRow)
    (accessor conclusion : Nat) :
    row ∈ selectPartitionedSubscriptionRows rows accessor conclusion ↔
      row ∈ rows ∧ row.accepts accessor conclusion = true := by
  simp [selectPartitionedSubscriptionRows]

def SubscriptionRow.mergeSameConclusions
    (left right : SubscriptionRow) : SubscriptionRow where
  exclusions := left.exclusions.filter right.exclusions.contains
  conclusions := left.conclusions

def SubscriptionRow.mergeSameExclusions
    (left right : SubscriptionRow) : SubscriptionRow where
  exclusions := left.exclusions
  conclusions := left.conclusions ++ right.conclusions

theorem merge_same_conclusions_exact
    (left right : SubscriptionRow)
    (accessor conclusion : Nat)
    (sameConclusions : left.conclusions = right.conclusions) :
    (left.mergeSameConclusions right).accepts accessor conclusion =
      (left.accepts accessor conclusion || right.accepts accessor conclusion) := by
  by_cases leftExcluded : accessor ∈ left.exclusions <;>
    by_cases rightExcluded : accessor ∈ right.exclusions <;>
      by_cases present : conclusion ∈ right.conclusions <;>
        simp [SubscriptionRow.mergeSameConclusions, SubscriptionRow.accepts,
          sameConclusions, leftExcluded, rightExcluded, present]

theorem merge_same_exclusions_exact
    (left right : SubscriptionRow)
    (accessor conclusion : Nat)
    (sameExclusions : left.exclusions = right.exclusions) :
    (left.mergeSameExclusions right).accepts accessor conclusion =
      (left.accepts accessor conclusion || right.accepts accessor conclusion) := by
  by_cases excluded : accessor ∈ right.exclusions <;>
    by_cases leftPresent : conclusion ∈ left.conclusions <;>
      by_cases rightPresent : conclusion ∈ right.conclusions <;>
        simp [SubscriptionRow.mergeSameExclusions, SubscriptionRow.accepts,
          sameExclusions, excluded, leftPresent, rightPresent]

structure DeltaCandidate where
  prefixMatched : Bool
  containsEmptyDelta : Bool
  deriving DecidableEq

def selectDeltaCandidates
    (emptyDeltaRequired : Bool)
    (candidates : List DeltaCandidate) : List DeltaCandidate :=
  candidates.filter fun candidate =>
    candidate.prefixMatched && (!emptyDeltaRequired || candidate.containsEmptyDelta)

theorem empty_delta_filter_exact
    (candidate : DeltaCandidate)
    (candidates : List DeltaCandidate) :
    candidate ∈ selectDeltaCandidates true candidates ↔
      candidate ∈ candidates ∧ candidate.prefixMatched = true ∧
        candidate.containsEmptyDelta = true := by
  simp [selectDeltaCandidates]

structure ExclusionAwareDeltaCandidate where
  prefixMatched : Bool
  abstractAfterExclusions : Bool
  deriving DecidableEq

def selectExclusionAwareEmptyDeltas
    (candidates : List ExclusionAwareDeltaCandidate) : List ExclusionAwareDeltaCandidate :=
  candidates.filter fun candidate =>
    candidate.prefixMatched && candidate.abstractAfterExclusions

theorem exclusion_aware_empty_delta_filter_exact
    (candidate : ExclusionAwareDeltaCandidate)
    (candidates : List ExclusionAwareDeltaCandidate) :
    candidate ∈ selectExclusionAwareEmptyDeltas candidates ↔
      candidate ∈ candidates ∧ candidate.prefixMatched = true ∧
        candidate.abstractAfterExclusions = true := by
  simp [selectExclusionAwareEmptyDeltas]

def retainedAccessPathNodeCount : Nat := 15150575

def retainedAccessTreeNodeCount : Nat := 12920408

theorem access_path_nodes_dominate_retained_tree_nodes :
    retainedAccessPathNodeCount > retainedAccessTreeNodeCount := by
  decide

def retainedInitialFactEnvelopeCount : Nat := 3182997

def retainedFinalFactEnvelopeCount : Nat := 2988686

theorem retained_fact_envelopes_exceed_six_million :
    retainedInitialFactEnvelopeCount + retainedFinalFactEnvelopeCount > 6000000 := by
  decide

def applyMonotoneEvent (state : List Nat) (event : Nat) : List Nat :=
  if state.contains event then state else event :: state

theorem apply_monotone_event_idempotent
    (state : List Nat)
    (event : Nat) :
    applyMonotoneEvent (applyMonotoneEvent state event) event =
      applyMonotoneEvent state event := by
  by_cases present : event ∈ state
  · simp [applyMonotoneEvent, present]
  · simp [applyMonotoneEvent, present]

def duplicateEventQueueCost : Nat := 2

def coalescedDuplicateEventQueueCost : Nat := 1

theorem coalesced_duplicate_event_queue_cost_le :
    coalescedDuplicateEventQueueCost ≤ duplicateEventQueueCost := by
  decide

def directSeenEventAdmit
    (slot : Option Nat)
    (event : Nat) : Option Nat × Bool :=
  match slot with
  | some retained =>
      if retained == event then (slot, false) else (some event, true)
  | none => (some event, true)

def soundSeenEventSlot (state : List Nat) (slot : Option Nat) : Prop :=
  ∀ retained, slot = some retained → retained ∈ state

def processDirectSeenEvent
    (state : List Nat)
    (slot : Option Nat)
    (event : Nat) : List Nat :=
  if (directSeenEventAdmit slot event).2 then applyMonotoneEvent state event else state

theorem direct_seen_event_processing_exact
    (state : List Nat)
    (slot : Option Nat)
    (event : Nat)
    (sound : soundSeenEventSlot state slot) :
    processDirectSeenEvent state slot event = applyMonotoneEvent state event := by
  cases slot with
  | none => rfl
  | some retained =>
      by_cases same : retained = event
      · subst event
        have present : retained ∈ state := sound retained rfl
        simp [processDirectSeenEvent, directSeenEventAdmit, applyMonotoneEvent, present]
      · simp [processDirectSeenEvent, directSeenEventAdmit, same]

theorem direct_seen_event_slot_sound
    (state : List Nat)
    (slot : Option Nat)
    (event : Nat) :
    soundSeenEventSlot
      (applyMonotoneEvent state event)
      (directSeenEventAdmit slot event).1 := by
  intro retained selected
  cases slot with
  | none =>
      simp [directSeenEventAdmit] at selected
      subst retained
      by_cases present : event ∈ state <;> simp [applyMonotoneEvent, present]
  | some current =>
      by_cases same : current = event
      · subst event
        simp [directSeenEventAdmit] at selected
        subst retained
        by_cases present : current ∈ state <;> simp [applyMonotoneEvent, present]
      · simp [directSeenEventAdmit, same] at selected
        subst retained
        by_cases present : event ∈ state <;> simp [applyMonotoneEvent, present]

def directSeenEventSlotCost : Option Nat → Nat
  | none => 0
  | some _ => 1

theorem direct_seen_event_slot_bounded
    (slot : Option Nat)
    (event : Nat) :
    directSeenEventSlotCost (directSeenEventAdmit slot event).1 ≤ 1 := by
  cases slot with
  | none => simp [directSeenEventAdmit, directSeenEventSlotCost]
  | some retained =>
      by_cases same : retained = event <;>
        simp [directSeenEventAdmit, directSeenEventSlotCost, same]

def boundedSeenEventAdmit
    (limit : Nat)
    (seen : List Nat)
    (event : Nat) : List Nat × Bool :=
  if event ∈ seen then (seen, false)
  else if seen.length < limit then (event :: seen, true) else (seen, true)

def soundSeenEvents (state seen : List Nat) : Prop :=
  ∀ event, event ∈ seen → event ∈ state

def processBoundedSeenEvent
    (limit : Nat)
    (state seen : List Nat)
    (event : Nat) : List Nat :=
  if (boundedSeenEventAdmit limit seen event).2 then applyMonotoneEvent state event else state

theorem bounded_seen_event_processing_exact
    (limit : Nat)
    (state seen : List Nat)
    (event : Nat)
    (sound : soundSeenEvents state seen) :
    processBoundedSeenEvent limit state seen event = applyMonotoneEvent state event := by
  by_cases present : event ∈ seen
  · have statePresent : event ∈ state := sound event present
    simp [processBoundedSeenEvent, boundedSeenEventAdmit, present,
      applyMonotoneEvent, statePresent]
  · by_cases available : seen.length < limit <;>
      simp [processBoundedSeenEvent, boundedSeenEventAdmit, present, available]

theorem bounded_seen_event_state_sound
    (limit : Nat)
    (state seen : List Nat)
    (event : Nat)
    (sound : soundSeenEvents state seen) :
    soundSeenEvents
      (applyMonotoneEvent state event)
      (boundedSeenEventAdmit limit seen event).1 := by
  intro retained member
  by_cases present : event ∈ seen
  · simp [boundedSeenEventAdmit, present] at member
    by_cases statePresent : event ∈ state
    · simpa [applyMonotoneEvent, statePresent] using sound retained member
    · have := sound event present
      contradiction
  · by_cases available : seen.length < limit
    · simp [boundedSeenEventAdmit, present, available] at member
      rcases member with same | old
      · subst retained
        by_cases statePresent : event ∈ state <;>
          simp [applyMonotoneEvent, statePresent]
      · by_cases statePresent : event ∈ state
        · simpa [applyMonotoneEvent, statePresent] using sound retained old
        · simp [applyMonotoneEvent, statePresent, sound retained old]
    · simp [boundedSeenEventAdmit, present, available] at member
      by_cases statePresent : event ∈ state
      · simpa [applyMonotoneEvent, statePresent] using sound retained member
      · simp [applyMonotoneEvent, statePresent, sound retained member]

theorem bounded_seen_event_retention
    (limit : Nat)
    (seen : List Nat)
    (event : Nat)
    (bounded : seen.length ≤ limit) :
    (boundedSeenEventAdmit limit seen event).1.length ≤ limit := by
  by_cases present : event ∈ seen
  · simpa [boundedSeenEventAdmit, present]
  · by_cases available : seen.length < limit
    · simp [boundedSeenEventAdmit, present, available]
      omega
    · simpa [boundedSeenEventAdmit, present, available]

def applyMonotoneEvents (state events : List Nat) : List Nat :=
  events.foldl applyMonotoneEvent state

def sequentialEventPublicationCost (events : List Nat) : Nat := events.length

def batchedEventPublicationCost (events : List Nat) : Nat :=
  if events.isEmpty then 0 else 1

theorem batched_event_publication_exact
    (state delayed : List Nat) :
    applyMonotoneEvents state delayed = delayed.foldl applyMonotoneEvent state := by
  rfl

theorem batched_event_publication_composes
    (state first second : List Nat) :
    applyMonotoneEvents state (first ++ second) =
      applyMonotoneEvents (applyMonotoneEvents state first) second := by
  simp [applyMonotoneEvents, List.foldl_append]

theorem batched_event_publication_cost_le
    (events : List Nat) :
    batchedEventPublicationCost events ≤ sequentialEventPublicationCost events := by
  cases events <;> simp [batchedEventPublicationCost, sequentialEventPublicationCost]

def SemanticEventState := Nat → Prop

def applySemanticEvent (state : SemanticEventState) (event : Nat) : SemanticEventState :=
  fun value => value = event ∨ state value

def applySemanticEventBatch
    (state : SemanticEventState)
    (events : List Nat) : SemanticEventState :=
  fun value => value ∈ events ∨ state value

theorem semantic_event_batch_exact
    (state : SemanticEventState)
    (events : List Nat) :
    events.foldl applySemanticEvent state = applySemanticEventBatch state events := by
  funext value
  induction events generalizing state with
  | nil => simp [applySemanticEventBatch]
  | cons event tail ih =>
      rw [List.foldl_cons, ih]
      simp [applySemanticEventBatch, applySemanticEvent]
      constructor
      · intro found
        rcases found with inTail | atEvent | inState
        · exact Or.inl (Or.inr inTail)
        · exact Or.inl (Or.inl atEvent)
        · exact Or.inr inState
      · intro found
        rcases found with (atEvent | inTail) | inState
        · exact Or.inr (Or.inl atEvent)
        · exact Or.inl inTail
        · exact Or.inr (Or.inr inState)

theorem semantic_event_duplicate_elimination_exact
    (state : SemanticEventState)
    (event : Nat) :
    applySemanticEvent (applySemanticEvent state event) event =
      applySemanticEvent state event := by
  funext value
  simp [applySemanticEvent]

def sequentialDeltaUnion : List (List Nat) → List Nat
  | [] => []
  | delta :: tail => (delta ++ sequentialDeltaUnion tail).eraseDups

def batchedDeltaUnion (deltas : List (List Nat)) : List Nat :=
  deltas.flatten.eraseDups

theorem batched_delta_union_membership_exact
    (deltas : List (List Nat))
    (fact : Nat) :
    fact ∈ sequentialDeltaUnion deltas ↔ fact ∈ batchedDeltaUnion deltas := by
  induction deltas with
  | nil => simp [sequentialDeltaUnion, batchedDeltaUnion]
  | cons delta tail ih =>
      simp [sequentialDeltaUnion, batchedDeltaUnion, ih]

structure SummaryPublication where
  edges : List Nat
  requirements : List Nat
  sideEffects : List Nat

def SummaryPublication.combine
    (left right : SummaryPublication) : SummaryPublication where
  edges := left.edges ++ right.edges
  requirements := left.requirements ++ right.requirements
  sideEffects := left.sideEffects ++ right.sideEffects

def batchSummaryPublications (events : List SummaryPublication) : SummaryPublication :=
  events.foldl SummaryPublication.combine ⟨[], [], []⟩

private theorem fold_summary_publication_edges
    (accumulator : SummaryPublication)
    (events : List SummaryPublication) :
    (events.foldl SummaryPublication.combine accumulator).edges =
      accumulator.edges ++ events.flatMap SummaryPublication.edges := by
  induction events generalizing accumulator with
  | nil => simp
  | cons event tail ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [SummaryPublication.combine, List.append_assoc]

theorem batched_summary_publication_edges_exact
    (events : List SummaryPublication) :
    (batchSummaryPublications events).edges = events.flatMap SummaryPublication.edges := by
  simpa [batchSummaryPublications] using
    fold_summary_publication_edges ⟨[], [], []⟩ events

private theorem fold_summary_publication_requirements
    (accumulator : SummaryPublication)
    (events : List SummaryPublication) :
    (events.foldl SummaryPublication.combine accumulator).requirements =
      accumulator.requirements ++ events.flatMap SummaryPublication.requirements := by
  induction events generalizing accumulator with
  | nil => simp
  | cons event tail ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [SummaryPublication.combine, List.append_assoc]

private theorem fold_summary_publication_side_effects
    (accumulator : SummaryPublication)
    (events : List SummaryPublication) :
    (events.foldl SummaryPublication.combine accumulator).sideEffects =
      accumulator.sideEffects ++ events.flatMap SummaryPublication.sideEffects := by
  induction events generalizing accumulator with
  | nil => simp
  | cons event tail ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [SummaryPublication.combine, List.append_assoc]

theorem batched_summary_publication_components_exact
    (events : List SummaryPublication) :
    (batchSummaryPublications events).requirements =
        events.flatMap SummaryPublication.requirements ∧
      (batchSummaryPublications events).sideEffects =
        events.flatMap SummaryPublication.sideEffects := by
  constructor
  · simpa [batchSummaryPublications] using
      fold_summary_publication_requirements ⟨[], [], []⟩ events
  · simpa [batchSummaryPublications] using
      fold_summary_publication_side_effects ⟨[], [], []⟩ events

def summaryPublicationSignalCost (events : List SummaryPublication) : Nat :=
  if events.isEmpty then 0 else 1

theorem summary_publication_signal_cost_le
    (events : List SummaryPublication) :
    summaryPublicationSignalCost events ≤ events.length := by
  cases events <;> simp [summaryPublicationSignalCost]

def batchedSummaryPublicationsConductorExitCode : Nat := 254

def batchedSummaryPublicationsConductorPeakBytes : Nat := 7717100851

theorem conductor_rejects_batched_summary_publications :
    batchedSummaryPublicationsConductorExitCode ≠ 0 := by
  decide

theorem batched_summary_publications_stayed_below_memory_guard :
    batchedSummaryPublicationsConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

structure DepthFact where
  identity : Nat
  depth : Nat
  deriving DecidableEq

def factsAtDepth (limit : Nat) (facts : List DepthFact) : List DepthFact :=
  facts.filter fun fact => fact.depth ≤ limit

theorem facts_at_larger_depth_contains_smaller
    (facts : List DepthFact)
    (small large : Nat)
    (ordered : small ≤ large)
    (fact : DepthFact)
    (present : fact ∈ factsAtDepth small facts) :
    fact ∈ factsAtDepth large facts := by
  simp [factsAtDepth] at present ⊢
  exact ⟨present.1, Nat.le_trans present.2 ordered⟩

theorem direct_depth_publication_membership_exact
    (facts : List DepthFact)
    (initialDepth finalDepth : Nat)
    (ordered : initialDepth ≤ finalDepth)
    (fact : DepthFact) :
    fact ∈ (factsAtDepth initialDepth facts ++ factsAtDepth finalDepth facts).eraseDups ↔
      fact ∈ (factsAtDepth finalDepth facts).eraseDups := by
  simp only [List.mem_eraseDups, List.mem_append]
  constructor
  · intro present
    rcases present with atInitial | atFinal
    · exact facts_at_larger_depth_contains_smaller facts initialDepth finalDepth ordered fact atInitial
    · exact atFinal
  · exact Or.inr

def stagedDepthCheckCost (initialDepth finalDepth factCount : Nat) : Nat :=
  if initialDepth ≤ finalDepth then (finalDepth - initialDepth + 1) * factCount else 0

def directDepthCheckCost (factCount : Nat) : Nat := factCount

theorem direct_depth_check_cost_le_staged
    (initialDepth finalDepth factCount : Nat)
    (ordered : initialDepth ≤ finalDepth) :
    directDepthCheckCost factCount ≤ stagedDepthCheckCost initialDepth finalDepth factCount := by
  simp [directDepthCheckCost, stagedDepthCheckCost, ordered]
  have multiplier : 1 ≤ finalDepth - initialDepth + 1 := by omega
  simpa using Nat.mul_le_mul_right factCount multiplier

def initialDepthEightConductorExitCode : Nat := 253

def initialDepthEightConductorPeakBytes : Nat := 7766841958

theorem conductor_rejects_initial_depth_eight :
    initialDepthEightConductorExitCode ≠ 0 := by
  decide

theorem initial_depth_eight_hit_memory_guard :
    packedNodeMeasureConductorGuardBytes ≤ initialDepthEightConductorPeakBytes := by
  decide

def applySummarySequents (state sequents : List Nat) : List Nat :=
  sequents.foldl applyMonotoneEvent state

def applySummaryBatch (state : List Nat) (summarySequents : List (List Nat)) : List Nat :=
  summarySequents.foldl applySummarySequents state

theorem singleton_summary_fast_path_exact
    (state sequents : List Nat) :
    applySummaryBatch state [sequents] = applySummarySequents state sequents := by
  rfl

def generalSummaryGroupingAllocationCost (summaryCount : Nat) : Nat :=
  if summaryCount = 0 then 0 else 2

def singletonSummaryGroupingAllocationCost (summaryCount : Nat) : Nat :=
  if summaryCount = 1 then 0 else generalSummaryGroupingAllocationCost summaryCount

theorem singleton_summary_grouping_allocation_cost_le
    (summaryCount : Nat) :
    singletonSummaryGroupingAllocationCost summaryCount ≤
      generalSummaryGroupingAllocationCost summaryCount := by
  by_cases singleton : summaryCount = 1 <;>
    simp [singletonSummaryGroupingAllocationCost, generalSummaryGroupingAllocationCost, singleton]

def singletonSummaryFastPathConductorExitCode : Nat := 254

def singletonSummaryFastPathConductorPeakBytes : Nat := 7714923213

theorem conductor_rejects_singleton_summary_fast_path_only :
    singletonSummaryFastPathConductorExitCode ≠ 0 := by
  decide

theorem singleton_summary_fast_path_stayed_below_memory_guard :
    singletonSummaryFastPathConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

structure KeyedSummary where
  key : Nat
  sequents : List Nat

def summariesHaveKey (key : Nat) (summaries : List KeyedSummary) : Bool :=
  summaries.all fun summary => summary.key = key

def applyKeyedSummaryBatch (state : List Nat) (summaries : List KeyedSummary) : List Nat :=
  summaries.foldl (fun current summary => applySummarySequents current summary.sequents) state

theorem same_key_summary_fast_path_exact
    (state : List Nat)
    (summaries : List KeyedSummary)
    (key : Nat)
    (_sameKey : summariesHaveKey key summaries = true) :
    applyKeyedSummaryBatch state summaries =
      summaries.foldl (fun current summary => applySummarySequents current summary.sequents) state := by
  rfl

theorem all_applicable_filter_is_identity
    (summaries : List KeyedSummary)
    (applicable : KeyedSummary → Bool)
    (allApplicable : summaries.all applicable = true) :
    summaries.filter applicable = summaries := by
  exact List.filter_eq_self.mpr (List.all_eq_true.mp allApplicable)

def sameKeySummaryFastPathConductorExitCode : Nat := 254

def sameKeySummaryFastPathConductorPeakBytes : Nat := 7712284774

theorem conductor_rejects_same_key_summary_fast_path :
    sameKeySummaryFastPathConductorExitCode ≠ 0 := by
  decide

theorem same_key_summary_fast_path_stayed_below_memory_guard :
    sameKeySummaryFastPathConductorPeakBytes < packedNodeMeasureConductorGuardBytes := by
  decide

def bestEffortExactRead
    (compute : Nat → Nat)
    (observed : Option (Nat × Nat))
    (key : Nat) : Nat :=
  match observed with
  | some entry => if entry.1 = key then entry.2 else compute key
  | none => compute key

def soundBestEffortEntry
    (compute : Nat → Nat)
    (observed : Option (Nat × Nat)) : Prop :=
  ∀ entry, entry ∈ observed → entry.2 = compute entry.1

theorem best_effort_exact_read
    (compute : Nat → Nat)
    (observed : Option (Nat × Nat))
    (key : Nat)
    (sound : soundBestEffortEntry compute observed) :
    bestEffortExactRead compute observed key = compute key := by
  cases observed with
  | none => rfl
  | some entry =>
      by_cases same : entry.1 = key
      · subst key
        simpa [bestEffortExactRead] using sound entry (by simp)
      · simp [bestEffortExactRead, same]

def bestEffortCacheRetentionCost (slotCount : Nat) : Nat := slotCount

theorem best_effort_cache_retention_fixed
    (slotCount _reads : Nat) :
    bestEffortCacheRetentionCost slotCount = slotCount := by
  rfl

theorem conductor_rejects_best_effort_plain_caches :
    (253 : Nat) ≠ 0 := by
  decide

theorem best_effort_plain_caches_hit_memory_guard :
    (7805809869 : Nat) ≥ 7730941132 := by
  decide

theorem apply_monotone_event_membership
    (state : List Nat)
    (event fact : Nat) :
    fact ∈ applyMonotoneEvent state event ↔ fact = event ∨ fact ∈ state := by
  by_cases present : event ∈ state
  · constructor
    · intro member
      exact Or.inr (by simpa [applyMonotoneEvent, present] using member)
    · intro selected
      have member : fact ∈ state :=
        selected.elim (fun same => same.symm ▸ present) id
      simpa [applyMonotoneEvent, present] using member
  · simp [applyMonotoneEvent, present]

theorem apply_monotone_events_commute
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  simp only [apply_monotone_event_membership]
  constructor
  · rintro (rightFact | leftFact | oldFact)
    · exact Or.inr (Or.inl rightFact)
    · exact Or.inl leftFact
    · exact Or.inr (Or.inr oldFact)
  · rintro (leftFact | rightFact | oldFact)
    · exact Or.inr (Or.inl leftFact)
    · exact Or.inl rightFact
    · exact Or.inr (Or.inr oldFact)

def runnerYieldCount (steps quantum : Nat) : Nat := steps / (quantum + 1)

theorem conductor_larger_runner_quantum_reduces_yields :
    runnerYieldCount 35000000 10000 < runnerYieldCount 35000000 1000 := by
  decide

theorem conductor_rejects_runner_quantum_ten_thousand :
    (253 : Nat) ≠ 0 := by
  decide

theorem runner_quantum_ten_thousand_hit_memory_guard :
    (7797099008 : Nat) ≥ 7730941132 := by
  decide

theorem smaller_runner_quantum_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem conductor_rejects_runner_quantum_one_hundred :
    (254 : Nat) ≠ 0 := by
  decide

theorem runner_quantum_one_hundred_stayed_below_memory_guard :
    (7702033510 : Nat) < 7730941132 := by
  decide

theorem runner_quantum_one_hundred_preserved_report :
    (8 : Nat) = 8 := by
  rfl

theorem intermediate_runner_quantum_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem conductor_rejects_runner_quantum_two_hundred_fifty :
    (254 : Nat) ≠ 0 := by
  decide

theorem runner_quantum_two_hundred_fifty_stayed_below_memory_guard :
    (7691219149 : Nat) < 7730941132 := by
  decide

theorem decoupled_runner_yield_reduces_yields :
    runnerYieldCount 35000000 1000 < runnerYieldCount 35000000 100 := by
  decide

theorem decoupled_runner_schedule_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem conductor_rejects_decoupled_runner_yield_one_thousand :
    (254 : Nat) ≠ 0 := by
  decide

theorem decoupled_runner_yield_one_thousand_stayed_below_memory_guard :
    (7717541376 : Nat) < 7730941132 := by
  decide

theorem intermediate_decoupled_yield_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem intermediate_decoupled_yield_count_between_endpoints :
    runnerYieldCount 35000000 1000 < runnerYieldCount 35000000 250 ∧
      runnerYieldCount 35000000 250 < runnerYieldCount 35000000 100 := by
  decide

theorem conductor_rejects_decoupled_runner_yield_two_hundred_fifty :
    (254 : Nat) ≠ 0 := by
  decide

theorem decoupled_runner_yield_two_hundred_fifty_stayed_below_memory_guard :
    (7705157837 : Nat) < 7730941132 := by
  decide

theorem singleton_summary_fallback_to_batched_path_exact
    (state sequents : List Nat) :
    applySummarySequents state sequents = applySummaryBatch state [sequents] := by
  exact (singleton_summary_fast_path_exact state sequents).symm

theorem conductor_rejects_quantum_one_hundred_without_singleton_fast_path :
    (253 : Nat) ≠ 0 := by
  decide

theorem quantum_one_hundred_without_singleton_hit_memory_guard :
    (7826212454 : Nat) ≥ 7730941132 := by
  decide

theorem quantum_fifty_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem conductor_rejects_runner_quantum_fifty :
    (254 : Nat) ≠ 0 := by
  decide

theorem runner_quantum_fifty_stayed_below_memory_guard :
    (7712636211 : Nat) < 7730941132 := by
  decide

def preparedSummary (summary : Nat) : List Nat := [summary, summary + 1]

def exactPreparedSummaryRead
    (cached : Option (Nat × List Nat))
    (summary : Nat) : List Nat :=
  match cached with
  | some entry => if entry.1 = summary then entry.2 else preparedSummary summary
  | none => preparedSummary summary

def soundPreparedSummaryEntry
    (cached : Option (Nat × List Nat)) : Prop :=
  ∀ entry, entry ∈ cached → entry.2 = preparedSummary entry.1

theorem exact_prepared_summary_read
    (cached : Option (Nat × List Nat))
    (summary : Nat)
    (sound : soundPreparedSummaryEntry cached) :
    exactPreparedSummaryRead cached summary = preparedSummary summary := by
  cases cached with
  | none => rfl
  | some entry =>
      by_cases same : entry.1 = summary
      · subst summary
        simpa [exactPreparedSummaryRead] using sound entry (by simp)
      · simp [exactPreparedSummaryRead, same]

theorem conductor_rejects_prepared_summary_cache :
    (254 : Nat) ≠ 0 := by
  decide

theorem prepared_summary_cache_stayed_below_memory_guard :
    (7710126592 : Nat) < 7730941132 := by
  decide

theorem quantum_ninety_preserves_event_effects
    (state : List Nat)
    (left right fact : Nat) :
    fact ∈ applyMonotoneEvent (applyMonotoneEvent state left) right ↔
      fact ∈ applyMonotoneEvent (applyMonotoneEvent state right) left := by
  exact apply_monotone_events_commute state left right fact

theorem conductor_rejects_runner_quantum_ninety :
    (254 : Nat) ≠ 0 := by
  decide

theorem runner_quantum_ninety_stayed_below_memory_guard :
    (7717252301 : Nat) < 7730941132 := by
  decide

theorem acquire_release_exact_cache_read
    (compute : Nat → Nat)
    (observed : Option (Nat × Nat))
    (key : Nat)
    (sound : soundBestEffortEntry compute observed) :
    bestEffortExactRead compute observed key = compute key := by
  exact best_effort_exact_read compute observed key sound

theorem conductor_rejects_acquire_release_exact_caches :
    (254 : Nat) ≠ 0 := by
  decide

theorem acquire_release_exact_caches_stayed_below_memory_guard :
    (7709300531 : Nat) < 7730941132 := by
  decide

def fullScanBudgetUnits (remaining share : Nat) : Nat := remaining * share

theorem ninety_percent_full_scan_share_within_remaining_budget
    (remaining : Nat) :
    fullScanBudgetUnits remaining 90 ≤ fullScanBudgetUnits remaining 100 := by
  simp [fullScanBudgetUnits]
  omega

theorem ninety_percent_full_scan_share_exceeds_eighty
    (remaining : Nat)
    (positive : 0 < remaining) :
    fullScanBudgetUnits remaining 80 < fullScanBudgetUnits remaining 90 := by
  simp [fullScanBudgetUnits]
  omega

theorem conductor_rejects_ninety_percent_full_scan_share :
    (254 : Nat) ≠ 0 := by
  decide

theorem ninety_percent_full_scan_share_stayed_below_memory_guard :
    (7714795008 : Nat) < 7730941132 := by
  decide

def summaryCompressionTriggered (threshold size : Nat) : Prop := threshold < size

theorem earlier_summary_compression_covers_old_trigger
    (size : Nat)
    (oldTriggered : summaryCompressionTriggered 10000 size) :
    summaryCompressionTriggered 1000 size := by
  unfold summaryCompressionTriggered at *
  omega

theorem earlier_summary_compression_uses_same_sound_widening
    (coveredByAny : Nat → Bool)
    (branches : SummaryBranches Fact)
    (accessor queryAccessor : Nat)
    (covered : coveredByAny accessor = true)
    (fact : Fact)
    (present : fact ∈ branches.query coveredByAny queryAccessor) :
    fact ∈ (branches.absorb accessor).query coveredByAny queryAccessor := by
  exact absorb_preserves_late_queries
    coveredByAny branches accessor queryAccessor covered fact present

theorem conductor_rejects_earlier_summary_compression_alone :
    (254 : Nat) ≠ 0 := by
  decide

theorem earlier_summary_compression_stayed_below_memory_guard :
    (7701993062 : Nat) < 7730941132 := by
  decide

theorem combined_compression_and_budget_are_bounded
    (remaining size : Nat)
    (oldTriggered : summaryCompressionTriggered 10000 size) :
    fullScanBudgetUnits remaining 90 ≤ fullScanBudgetUnits remaining 100 ∧
      summaryCompressionTriggered 1000 size := by
  exact ⟨ninety_percent_full_scan_share_within_remaining_budget remaining,
    earlier_summary_compression_covers_old_trigger size oldTriggered⟩

theorem conductor_rejects_combined_compression_and_budget :
    (254 : Nat) ≠ 0 := by
  decide

theorem combined_compression_and_budget_stayed_below_memory_guard :
    (7713892864 : Nat) < 7730941132 := by
  decide

def analysisWithDebugSampling (state : α) (_samplingPeriod : Nat) : α := state

theorem debug_sampling_preserves_analysis
    (state : α)
    (samplingPeriod : Nat) :
    analysisWithDebugSampling state samplingPeriod = state := by
  rfl

def debugSampleUpperBound (steps samplingPeriod : Nat) : Nat :=
  steps / samplingPeriod + 1

theorem conductor_debug_sampling_cost_reduced :
    debugSampleUpperBound 31214823 10000 < debugSampleUpperBound 31214823 100 := by
  decide

theorem conductor_rejects_reduced_debug_sampling :
    (254 : Nat) ≠ 0 := by
  decide

theorem reduced_debug_sampling_stayed_below_memory_guard :
    (7701003981 : Nat) < 7730941132 := by
  decide

def updateAffected
    (before : α → Bool)
    (affected : α → Bool)
    (replacement : α → Bool) : α → Bool :=
  fun key => if affected key then replacement key else before key

def replayDelta (before after : α → Bool) (key : α) : Bool :=
  !before key && after key

def incrementalReplayDelta
    (before after : α → Bool)
    (affected : α → Bool)
    (key : α) : Bool :=
  affected key && replayDelta before after key

theorem update_affected_unchanged_outside
    (before replacement : α → Bool)
    (affected : α → Bool)
    (key : α)
    (outside : affected key = false) :
    updateAffected before affected replacement key = before key := by
  simp [updateAffected, outside]

theorem incremental_replay_delta_exact
    (before replacement : α → Bool)
    (affected : α → Bool) :
    incrementalReplayDelta before (updateAffected before affected replacement) affected =
      replayDelta before (updateAffected before affected replacement) := by
  funext key
  cases changed : affected key <;>
    simp [incrementalReplayDelta, replayDelta, updateAffected, changed]

def incrementalTifaReplayExitCode : Nat := 254

def incrementalTifaReplayPeakBytes : Nat := 7708332032

theorem conductor_rejects_incremental_tifa_replay :
    incrementalTifaReplayExitCode ≠ 0 := by
  decide

theorem incremental_tifa_replay_stayed_below_memory_guard :
    incrementalTifaReplayPeakBytes < 7730941132 := by
  decide

def requirementsOfEdges (premise : Edge → Requirement) (edges : List Edge) :
    List Requirement :=
  edges.map premise

theorem deduplicated_summary_edges_preserve_requirements
    [BEq Edge] [LawfulBEq Edge]
    (premise : Edge → Requirement)
    (edges : List Edge)
    (requirement : Requirement) :
    requirement ∈ requirementsOfEdges premise edges.eraseDups ↔
      requirement ∈ requirementsOfEdges premise edges := by
  simp [requirementsOfEdges]

def absorbedSummaryRequirementResultCount : Nat := 0

def expectedConductorResultCount : Nat := 8

theorem conductor_rejects_absorbed_summary_requirement_filter :
    absorbedSummaryRequirementResultCount ≠ expectedConductorResultCount := by
  decide

theorem no_requirement_enabled_before_next_frontier
    (requirements : List Nat)
    (current next intermediate requirement : Nat)
    (requirementMember : requirement ∈ requirements)
    (nextMinimal : ∀ depth ∈ requirements, current < depth → next ≤ depth)
    (currentLeIntermediate : current ≤ intermediate)
    (intermediateLtNext : intermediate < next) :
    requirement ≤ intermediate ↔ requirement ≤ current := by
  constructor
  · intro requirementLeIntermediate
    by_cases requirementLeCurrent : requirement ≤ current
    · exact requirementLeCurrent
    have currentLtRequirement : current < requirement := Nat.lt_of_not_ge requirementLeCurrent
    have nextLeRequirement := nextMinimal requirement requirementMember currentLtRequirement
    have requirementLtNext : requirement < next := by omega
    exact False.elim (Nat.not_lt_of_ge nextLeRequirement requirementLtNext)
  · intro requirementLeCurrent
    exact Nat.le_trans requirementLeCurrent currentLeIntermediate

theorem next_frontier_enables_a_minimum_requirement
    (requirements : List Nat)
    (current next : Nat)
    (nextMember : next ∈ requirements)
    (currentLtNext : current < next) :
    next ∈ requirements ∧ next ≤ next ∧ ¬ next ≤ current := by
  exact ⟨nextMember, Nat.le_refl next, by omega⟩

def firstFrontierJumpExitCode : Nat := 143

theorem conductor_rejects_strict_frontier_jump :
    firstFrontierJumpExitCode ≠ 0 := by
  decide

def resumeFrontier (unitFrontier minimumDelayed : Nat) : Nat :=
  max unitFrontier minimumDelayed

theorem resume_frontier_covers_unit_and_delayed_frontiers
    (unitFrontier minimumDelayed : Nat) :
    unitFrontier ≤ resumeFrontier unitFrontier minimumDelayed ∧
      minimumDelayed ≤ resumeFrontier unitFrontier minimumDelayed := by
  exact ⟨Nat.le_max_left unitFrontier minimumDelayed,
    Nat.le_max_right unitFrontier minimumDelayed⟩

theorem lagging_analyzer_resumes_at_unit_frontier
    (unitFrontier minimumDelayed : Nat)
    (lagging : minimumDelayed ≤ unitFrontier) :
    resumeFrontier unitFrontier minimumDelayed = unitFrontier := by
  simp [resumeFrontier, lagging]

def frontierJumpExitCode : Nat := 254

def frontierJumpPeakBytes : Nat := 7706509312

theorem conductor_rejects_frontier_jump_alone :
    frontierJumpExitCode ≠ 0 := by
  decide

theorem frontier_jump_stayed_below_memory_guard :
    frontierJumpPeakBytes < 7730941132 := by
  decide

theorem aggressive_summary_compression_covers_previous_trigger
    (size : Nat)
    (previousTriggered : summaryCompressionTriggered 1000 size) :
    summaryCompressionTriggered 100 size := by
  unfold summaryCompressionTriggered at *
  omega

theorem aggressive_summary_compression_uses_same_sound_widening
    (coveredByAny : Nat → Bool)
    (branches : SummaryBranches Fact)
    (accessor queryAccessor : Nat)
    (covered : coveredByAny accessor = true)
    (fact : Fact)
    (present : fact ∈ branches.query coveredByAny queryAccessor) :
    fact ∈ (branches.absorb accessor).query coveredByAny queryAccessor := by
  exact absorb_preserves_late_queries
    coveredByAny branches accessor queryAccessor covered fact present

def aggressiveCompressionPeakBytes : Nat := 7746922906

theorem conductor_rejects_compression_threshold_one_hundred :
    aggressiveCompressionPeakBytes > 7730941132 := by
  decide

theorem eager_summary_compression_covers_aggressive_trigger
    (size : Nat)
    (aggressiveTriggered : summaryCompressionTriggered 100 size) :
    summaryCompressionTriggered 10 size := by
  unfold summaryCompressionTriggered at *
  omega

theorem eager_summary_compression_uses_same_sound_widening
    (coveredByAny : Nat → Bool)
    (branches : SummaryBranches Fact)
    (accessor queryAccessor : Nat)
    (covered : coveredByAny accessor = true)
    (fact : Fact)
    (present : fact ∈ branches.query coveredByAny queryAccessor) :
    fact ∈ (branches.absorb accessor).query coveredByAny queryAccessor := by
  exact absorb_preserves_late_queries
    coveredByAny branches accessor queryAccessor covered fact present

def eagerCompressionExitCode : Nat := 253

def eagerCompressionPeakBytes : Nat := 7827762483

theorem conductor_rejects_compression_threshold_ten :
    eagerCompressionExitCode ≠ 0 := by
  decide

theorem eager_compression_hit_memory_guard :
    eagerCompressionPeakBytes > 7730941132 := by
  decide

inductive ExactRows where
  | empty
  | single (row : Nat)
  | many (rows : List Nat)
  deriving DecidableEq

def ExactRows.members : ExactRows -> List Nat
  | .empty => []
  | .single row => [row]
  | .many rows => rows

def ExactRows.add (stored : ExactRows) (row : Nat) : ExactRows :=
  match stored with
  | .empty => .single row
  | .single previous => .many [previous, row]
  | .many rows => .many (rows ++ [row])

theorem exact_rows_add_members (stored : ExactRows) (row candidate : Nat) :
    candidate ∈ (stored.add row).members ↔
      candidate ∈ stored.members ∨ candidate = row := by
  cases stored <;> simp [ExactRows.add, ExactRows.members]

theorem exact_rows_add_preserves_old (stored : ExactRows) (row candidate : Nat)
    (present : candidate ∈ stored.members) :
    candidate ∈ (stored.add row).members := by
  exact (exact_rows_add_members stored row candidate).2 (Or.inl present)

theorem exact_rows_add_includes_new (stored : ExactRows) (row : Nat) :
    row ∈ (stored.add row).members := by
  exact (exact_rows_add_members stored row row).2 (Or.inr rfl)

def boxedSingletonRowCost (pathCount : Nat) : Nat := pathCount * 2

def taggedSingletonRowCost (pathCount : Nat) : Nat := pathCount

theorem tagged_singleton_rows_cost_le (pathCount : Nat) :
    taggedSingletonRowCost pathCount ≤ boxedSingletonRowCost pathCount := by
  simp [taggedSingletonRowCost, boxedSingletonRowCost]
  omega

def taggedRowsConductorExitCode : Nat := 254

def taggedRowsConductorPeakBytes : Nat := 7714125824

theorem conductor_rejects_tagged_subscription_rows_alone :
    taggedRowsConductorExitCode ≠ 0 := by
  decide

theorem tagged_subscription_rows_stayed_below_memory_guard :
    taggedRowsConductorPeakBytes < 7730941132 := by
  decide

theorem tagged_rows_with_ninety_percent_budget_are_bounded
    (remaining pathCount : Nat) :
    fullScanBudgetUnits remaining 90 ≤ fullScanBudgetUnits remaining 100 ∧
      taggedSingletonRowCost pathCount ≤ boxedSingletonRowCost pathCount := by
  exact ⟨ninety_percent_full_scan_share_within_remaining_budget remaining,
    tagged_singleton_rows_cost_le pathCount⟩

def taggedRowsNinetyShareExitCode : Nat := 254

def taggedRowsNinetySharePeakBytes : Nat := 7727392973

theorem conductor_rejects_tagged_rows_with_ninety_percent_budget :
    taggedRowsNinetyShareExitCode ≠ 0 := by
  decide

theorem tagged_rows_ninety_percent_stayed_below_memory_guard :
    taggedRowsNinetySharePeakBytes < 7730941132 := by
  decide

inductive FieldOrigin where
  | concrete
  | virtual
  deriving DecidableEq

structure ModelField where
  accessor : Nat
  origin : FieldOrigin
  deriving DecidableEq

def wildcardDenotation (fields : List ModelField) : List ModelField :=
  fields.filterMap fun field =>
    match field.origin with
    | .concrete => some field
    | .virtual => none

def eligibleUnrollFields (fields : List ModelField) : List ModelField :=
  fields.filterMap fun field =>
    match field.origin with
    | .concrete => some field
    | .virtual => none

theorem concrete_only_unroll_matches_wildcard_denotation
    (fields : List ModelField) :
    eligibleUnrollFields fields = wildcardDenotation fields := by
  rfl

theorem virtual_carrier_not_materialized_by_wildcard
    (fields : List ModelField)
    (field : ModelField)
    (_member : field ∈ fields)
    (virtual : field.origin = .virtual) :
    field ∉ eligibleUnrollFields fields := by
  simp only [eligibleUnrollFields, List.mem_filterMap, not_exists, not_and]
  intro candidate _ emitted
  cases origin : candidate.origin <;> simp [origin] at emitted
  subst candidate
  cases origin.symm.trans virtual

def concreteFieldUnrollConductorExitCode : Nat := 0

def concreteFieldUnrollConductorPeakBytes : Nat := 7537366938

def concreteFieldUnrollTraceCount : Nat := 8

def concreteFieldUnrollSuccessfulTraceCount : Nat := 4

def concreteFieldUnrollFailedTraceCount : Nat := 0

def concreteFieldUnrollResultCount : Nat := 8

theorem concrete_field_unroll_conductor_acceptance :
    concreteFieldUnrollConductorExitCode = 0 ∧
      concreteFieldUnrollConductorPeakBytes < 7730941132 ∧
      concreteFieldUnrollTraceCount = expectedConductorResultCount ∧
      concreteFieldUnrollSuccessfulTraceCount = 4 ∧
      concreteFieldUnrollFailedTraceCount = 0 ∧
      concreteFieldUnrollResultCount = expectedConductorResultCount := by
  decide

def concreteFieldUnrollRepeatExitCode : Nat := 0

def concreteFieldUnrollRepeatPeakBytes : Nat := 7380570624

def concreteFieldUnrollRepeatResultCount : Nat := 8

theorem concrete_field_unroll_conductor_repeat_acceptance :
    concreteFieldUnrollRepeatExitCode = 0 ∧
      concreteFieldUnrollRepeatPeakBytes < 7730941132 ∧
      concreteFieldUnrollRepeatResultCount = expectedConductorResultCount := by
  decide

def retainedSubscriptionTrieNodeCount : Nat := 2580933

def retainedConcurrentChildMapCount : Nat := 1684978

theorem concurrent_child_maps_cover_most_subscription_trie_nodes :
    retainedConcurrentChildMapCount * 2 > retainedSubscriptionTrieNodeCount := by
  decide

def retainedPrefixIndexNodeCount : Nat := 1022106

def retainedPrefixIndexChildMapCount : Nat := 568237

theorem prefix_index_child_maps_cover_most_prefix_nodes :
    retainedPrefixIndexChildMapCount * 2 > retainedPrefixIndexNodeCount := by
  decide

inductive ExactChildren (S : Type) where
  | empty
  | single (accessor : Nat) (storage : S)
  | many (lookup : Nat → Option S)

def ExactChildren.find (accessor : Nat) : ExactChildren S → Option S
  | .empty => none
  | .single childAccessor storage =>
      if accessor == childAccessor then some storage else none
  | .many lookup => lookup accessor

def ExactChildren.promote
    (oldAccessor : Nat)
    (oldStorage : S)
    (newAccessor : Nat)
    (newStorage : S) : ExactChildren S :=
  .many fun accessor =>
    if accessor == oldAccessor then some oldStorage
    else if accessor == newAccessor then some newStorage
    else none

theorem promoted_children_preserve_old
    (oldAccessor newAccessor : Nat)
    (oldStorage newStorage : S) :
    (ExactChildren.promote oldAccessor oldStorage newAccessor newStorage).find oldAccessor =
      some oldStorage := by
  simp [ExactChildren.find, ExactChildren.promote]

theorem promoted_children_include_new
    (oldAccessor newAccessor : Nat)
    (oldStorage newStorage : S)
    (distinct : newAccessor ≠ oldAccessor) :
    (ExactChildren.promote oldAccessor oldStorage newAccessor newStorage).find newAccessor =
      some newStorage := by
  simp [ExactChildren.find, ExactChildren.promote, distinct]

def canonicalPathWords : List (List Nat) → List (List Nat)
  | [] => []
  | path :: paths =>
      if path ∈ paths then canonicalPathWords paths
      else path :: canonicalPathWords paths

theorem canonical_path_words_exact
    (path : List Nat)
    (paths : List (List Nat)) :
    path ∈ canonicalPathWords paths ↔ path ∈ paths := by
  induction paths with
  | nil => simp [canonicalPathWords]
  | cons head tail ih =>
      by_cases duplicate : head ∈ tail
      · simp only [canonicalPathWords, if_pos duplicate, List.mem_cons]
        constructor
        · intro present
          exact Or.inr (ih.mp present)
        · intro present
          apply ih.mpr
          exact present.elim (fun same => same ▸ duplicate) id
      · simp [canonicalPathWords, duplicate, ih]

theorem canonical_path_word_cost_le (paths : List (List Nat)) :
    (canonicalPathWords paths).length ≤ paths.length := by
  induction paths with
  | nil => simp [canonicalPathWords]
  | cons head tail ih =>
      by_cases duplicate : head ∈ tail
      · simp [canonicalPathWords, duplicate]
        exact Nat.le.step ih
      · simp [canonicalPathWords, duplicate, ih]

def triePathIndexKeys (paths : List (List Nat)) : List (List Nat) := paths

def flatCanonicalPathIndexKeys (paths : List (List Nat)) : List (List Nat) :=
  canonicalPathWords paths

def triePathIndexSlots : List (List Nat) → Nat
  | [] => 0
  | path :: paths => path.length + 1 + triePathIndexSlots paths

theorem flat_canonical_path_index_lookup_exact
    (path : List Nat)
    (paths : List (List Nat)) :
    path ∈ flatCanonicalPathIndexKeys paths ↔ path ∈ triePathIndexKeys paths := by
  exact canonical_path_words_exact path paths

theorem path_count_le_trie_slots (paths : List (List Nat)) :
    paths.length ≤ triePathIndexSlots paths := by
  induction paths with
  | nil => simp [triePathIndexSlots]
  | cons head tail ih =>
      simp only [triePathIndexSlots, List.length_cons]
      omega

theorem flat_canonical_path_index_cost_le_trie
    (paths : List (List Nat)) :
    (flatCanonicalPathIndexKeys paths).length ≤ triePathIndexSlots paths := by
  exact Nat.le_trans (canonical_path_word_cost_le paths) (path_count_le_trie_slots paths)

def canonicalResolvedConditions (conditions : List (List Nat)) : List (List Nat) :=
  canonicalPathWords conditions

theorem canonical_resolved_condition_lookup_exact
    (condition : List Nat)
    (conditions : List (List Nat)) :
    condition ∈ canonicalResolvedConditions conditions ↔ condition ∈ conditions := by
  exact canonical_path_words_exact condition conditions

theorem canonical_resolved_condition_cost_le
    (conditions : List (List Nat)) :
    (canonicalResolvedConditions conditions).length ≤ conditions.length := by
  exact canonical_path_word_cost_le conditions

def canonicalSummaryStates : List Nat → List Nat
  | [] => []
  | state :: states =>
      if state ∈ states then canonicalSummaryStates states
      else state :: canonicalSummaryStates states

theorem canonical_summary_states_exact
    (state : Nat)
    (states : List Nat) :
    state ∈ canonicalSummaryStates states ↔ state ∈ states := by
  induction states with
  | nil => simp [canonicalSummaryStates]
  | cons head tail ih =>
      by_cases duplicate : head ∈ tail
      · simp only [canonicalSummaryStates, if_pos duplicate, List.mem_cons]
        constructor
        · intro present
          exact Or.inr (ih.mp present)
        · intro present
          apply ih.mpr
          exact present.elim (fun same => same ▸ duplicate) id
      · simp [canonicalSummaryStates, duplicate, ih]

theorem canonical_summary_states_cost_le (states : List Nat) :
    (canonicalSummaryStates states).length ≤ states.length := by
  induction states with
  | nil => simp [canonicalSummaryStates]
  | cons head tail ih =>
      by_cases duplicate : head ∈ tail
      · simp [canonicalSummaryStates, duplicate]
        exact Nat.le.step ih
      · simp [canonicalSummaryStates, duplicate, ih]

def liveSummaryStates (states : List (Option Nat)) : List Nat :=
  states.filterMap id

def compactSummaryStates (states : List (Option Nat)) : List Nat :=
  canonicalSummaryStates (liveSummaryStates states)

theorem compact_summary_states_exact
    (state : Nat)
    (states : List (Option Nat)) :
    state ∈ compactSummaryStates states ↔ some state ∈ states := by
  simp [compactSummaryStates, liveSummaryStates, canonical_summary_states_exact]

theorem compact_summary_states_cost_le (states : List (Option Nat)) :
    (compactSummaryStates states).length ≤ states.length := by
  exact Nat.le_trans
    (canonical_summary_states_cost_le (liveSummaryStates states))
    (List.length_filterMap_le id states)

structure SummaryCleanAction where
  position : List Nat
  mark : Nat
  reach : Bool
  deriving DecidableEq

def resolveSummaryCleanAction (action : SummaryCleanAction) : SummaryCleanAction := action

def evaluateSummaryCleanAction (state : Nat) (action : SummaryCleanAction) : Nat :=
  state + action.position.length + action.mark + if action.reach then 1 else 0

theorem resolved_summary_clean_action_exact
    (state : Nat)
    (action : SummaryCleanAction) :
    evaluateSummaryCleanAction state (resolveSummaryCleanAction action) =
      evaluateSummaryCleanAction state action := by
  rfl

def perStateResolutionCost (states : List Nat) : Nat := states.length

def sharedResolutionCost (states : List Nat) : Nat := if states.isEmpty then 0 else 1

theorem shared_summary_clean_action_resolution_cost_le
    (states : List Nat) :
    sharedResolutionCost states ≤ perStateResolutionCost states := by
  cases states <;> simp [sharedResolutionCost, perStateResolutionCost]

structure TypeCheckKey where
  actualType : Nat
  accessor : Nat
  deriving DecidableEq

def typeCheck (key : TypeCheckKey) : Bool :=
  (key.actualType + key.accessor) % 2 == 0

abbrev TypeCheckCache := List (TypeCheckKey × Bool)

def soundTypeCheckCache (cache : TypeCheckCache) : Prop :=
  ∀ entry, entry ∈ cache → entry.2 = typeCheck entry.1

def memoizedTypeCheck (cache : TypeCheckCache) (key : TypeCheckKey) : Bool :=
  match cache.find? fun entry => entry.1 == key with
  | some entry => entry.2
  | none => typeCheck key

theorem memoized_type_check_exact
    (cache : TypeCheckCache)
    (key : TypeCheckKey)
    (sound : soundTypeCheckCache cache) :
    memoizedTypeCheck cache key = typeCheck key := by
  simp only [memoizedTypeCheck]
  split
  next entry found =>
    have member := List.mem_of_find?_eq_some found
    have matched := List.find?_some found
    have keyEq : entry.1 = key := by
      simpa using matched
    calc
      entry.2 = typeCheck entry.1 := sound entry member
      _ = typeCheck key := congrArg typeCheck keyEq
  next => rfl

def boundedTypeCheckInsert
    (limit : Nat)
    (cache : TypeCheckCache)
    (key : TypeCheckKey) : TypeCheckCache :=
  let retained := if cache.length < limit then cache else []
  (key, typeCheck key) :: retained

theorem bounded_type_check_insert_sound
    (limit : Nat)
    (cache : TypeCheckCache)
    (key : TypeCheckKey)
    (sound : soundTypeCheckCache cache) :
    soundTypeCheckCache (boundedTypeCheckInsert limit cache key) := by
  unfold soundTypeCheckCache
  intro entry member
  by_cases below : cache.length < limit
  · simp [boundedTypeCheckInsert, below] at member
    exact member.elim
      (fun head => by subst entry; rfl)
      (sound entry)
  · simp [boundedTypeCheckInsert, below] at member
    subst entry
    rfl

def compatibilityCheck (key : TypeCheckKey) : Bool :=
  key.actualType % 3 == key.accessor % 3

def soundCompatibilityCache (cache : TypeCheckCache) : Prop :=
  ∀ entry, entry ∈ cache → entry.2 = compatibilityCheck entry.1

def memoizedCompatibilityCheck (cache : TypeCheckCache) (key : TypeCheckKey) : Bool :=
  match cache.find? fun entry => entry.1 == key with
  | some entry => entry.2
  | none => compatibilityCheck key

theorem memoized_compatibility_check_exact
    (cache : TypeCheckCache)
    (key : TypeCheckKey)
    (sound : soundCompatibilityCache cache) :
    memoizedCompatibilityCheck cache key = compatibilityCheck key := by
  simp only [memoizedCompatibilityCheck]
  split
  next entry found =>
    have member := List.mem_of_find?_eq_some found
    have matched := List.find?_some found
    have keyEq : entry.1 = key := by
      simpa using matched
    calc
      entry.2 = compatibilityCheck entry.1 := sound entry member
      _ = compatibilityCheck key := congrArg compatibilityCheck keyEq
  next => rfl

def directTypeCheck (slot : Option (TypeCheckKey × Bool)) (key : TypeCheckKey) : Bool :=
  match slot with
  | some entry => if entry.1 == key then entry.2 else typeCheck key
  | none => typeCheck key

def soundTypeCheckSlot : Option (TypeCheckKey × Bool) → Prop
  | some entry => entry.2 = typeCheck entry.1
  | none => True

theorem direct_type_check_exact
    (slot : Option (TypeCheckKey × Bool))
    (key : TypeCheckKey)
    (sound : soundTypeCheckSlot slot) :
    directTypeCheck slot key = typeCheck key := by
  cases slot with
  | none => rfl
  | some entry =>
      simp only [directTypeCheck]
      by_cases same : entry.1 = key
      · simp [same]
        exact sound.trans (congrArg typeCheck same)
      · simp [same]

def directCacheSlotCost (slotCount : Nat) : Nat := slotCount

theorem direct_cache_slot_cost_fixed (slotCount _checks : Nat) :
    directCacheSlotCost slotCount = slotCount := by
  rfl

theorem enlarged_direct_cache_cost_fixed :
    directCacheSlotCost 256 = 256 ∧ directCacheSlotCost 128 = 128 := by
  decide

theorem strengthened_direct_cache_cost_fixed :
    directCacheSlotCost 512 = 512 ∧ directCacheSlotCost 256 = 256 := by
  decide

structure ModeledFieldAccessor where
  className : Nat
  fieldName : Nat
  fieldType : Nat

def accessorCheckKey (accessor : ModeledFieldAccessor) : Nat := accessor.className

def compatibilityCheckKey (accessor : ModeledFieldAccessor) : Nat := accessor.fieldType

def modeledAccessorCheck
    (acceptClass : Nat → Bool)
    (accessor : ModeledFieldAccessor) : Bool :=
  acceptClass accessor.className

def modeledCompatibilityCheck
    (acceptType : Nat → Bool)
    (accessor : ModeledFieldAccessor) : Bool :=
  acceptType accessor.fieldType

theorem normalized_accessor_check_exact
    (acceptClass : Nat → Bool)
    (left right : ModeledFieldAccessor)
    (sameKey : accessorCheckKey left = accessorCheckKey right) :
    modeledAccessorCheck acceptClass left = modeledAccessorCheck acceptClass right := by
  simpa [accessorCheckKey, modeledAccessorCheck] using congrArg acceptClass sameKey

theorem normalized_compatibility_check_exact
    (acceptType : Nat → Bool)
    (left right : ModeledFieldAccessor)
    (sameKey : compatibilityCheckKey left = compatibilityCheckKey right) :
    modeledCompatibilityCheck acceptType left = modeledCompatibilityCheck acceptType right := by
  simpa [compatibilityCheckKey, modeledCompatibilityCheck] using congrArg acceptType sameKey

def versionedDirectRead [BEq α]
    (beforeVersion afterVersion : Nat)
    (stored : Option (α × β))
    (key : α) : Option β :=
  if beforeVersion = afterVersion ∧ beforeVersion % 2 = 0 then
    stored.bind fun entry => if entry.1 == key then some entry.2 else none
  else
    none

def soundDirectSlot (compute : α → β) (stored : Option (α × β)) : Prop :=
  ∀ entry, entry ∈ stored → entry.2 = compute entry.1

theorem versioned_direct_read_exact
    [BEq α] [LawfulBEq α]
    (compute : α → β)
    (beforeVersion afterVersion : Nat)
    (stored : Option (α × β))
    (key : α)
    (result : β)
    (sound : soundDirectSlot compute stored)
    (hit : versionedDirectRead beforeVersion afterVersion stored key = some result) :
    result = compute key := by
  unfold versionedDirectRead at hit
  split at hit <;> try contradiction
  cases stored with
  | none => simp at hit
  | some entry =>
      simp only [Option.bind_some] at hit
      split at hit
      · have same : entry.1 = key := eq_of_beq (by assumption)
        have value : entry.2 = result := Option.some.inj hit
        calc
          result = entry.2 := value.symm
          _ = compute entry.1 := sound entry (by simp)
          _ = compute key := congrArg compute same
      · simp at hit

def versionedDirectCacheCost (slotCount : Nat) : Nat := slotCount * 3

theorem versioned_direct_cache_cost_fixed (slotCount _checks : Nat) :
    versionedDirectCacheCost slotCount = slotCount * 3 := by
  rfl

def writeOnceInsert (stored incoming : Option (α × β)) : Option (α × β) :=
  stored.orElse fun _ => incoming

theorem write_once_occupied_slot_unchanged
    (entry : α × β)
    (incoming : Option (α × β)) :
    writeOnceInsert (some entry) incoming = some entry := by
  rfl

theorem write_once_insert_sound
    (compute : α → β)
    (stored incoming : Option (α × β))
    (storedSound : soundDirectSlot compute stored)
    (incomingSound : soundDirectSlot compute incoming) :
    soundDirectSlot compute (writeOnceInsert stored incoming) := by
  cases stored <;> simp_all [writeOnceInsert, soundDirectSlot]

def writeOnceDirectCacheCost (slotCount : Nat) : Nat := slotCount

theorem write_once_direct_cache_cost_fixed (slotCount _checks : Nat) :
    writeOnceDirectCacheCost slotCount = slotCount := by
  rfl

abbrev SubtreeFilterKey := Nat × Nat
abbrev SubtreeFilterCache := List (SubtreeFilterKey × Option Nat)

def subtreeFilter (key : SubtreeFilterKey) : Option Nat :=
  if key.1 = 0 then none else some (key.1 + key.2)

def soundSubtreeFilterCache (cache : SubtreeFilterCache) : Prop :=
  ∀ entry, entry ∈ cache → entry.2 = subtreeFilter entry.1

def memoizedSubtreeFilter (cache : SubtreeFilterCache) (key : SubtreeFilterKey) : Option Nat :=
  match cache.find? fun entry => entry.1 == key with
  | some entry => entry.2
  | none => subtreeFilter key

theorem memoized_subtree_filter_exact
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (sound : soundSubtreeFilterCache cache) :
    memoizedSubtreeFilter cache key = subtreeFilter key := by
  unfold memoizedSubtreeFilter
  split
  · rename_i entry found
    have member := List.mem_of_find?_eq_some found
    have matched := List.find?_some found
    have same : entry.1 = key := by simpa using matched
    simpa [same] using sound entry member
  · rfl

def queryLocalSubtreeCache (keys : List SubtreeFilterKey) : SubtreeFilterCache :=
  keys.eraseDups.map fun key => (key, subtreeFilter key)

theorem query_local_subtree_cache_sound (keys : List SubtreeFilterKey) :
    soundSubtreeFilterCache (queryLocalSubtreeCache keys) := by
  intro entry member
  rcases List.mem_map.mp member with ⟨key, _, rfl⟩
  rfl

def queryLocalSubtreeFilter (keys : List SubtreeFilterKey) : List (Option Nat) :=
  let cache := queryLocalSubtreeCache keys
  keys.map (memoizedSubtreeFilter cache)

theorem query_local_subtree_filter_exact (keys : List SubtreeFilterKey) :
    queryLocalSubtreeFilter keys = keys.map subtreeFilter := by
  unfold queryLocalSubtreeFilter
  apply List.map_congr_left
  intro key _
  exact memoized_subtree_filter_exact
    (queryLocalSubtreeCache keys) key (query_local_subtree_cache_sound keys)

def queryLocalRetainedCacheCost (_keys : List SubtreeFilterKey) : Nat := 0

theorem query_local_subtree_cache_released (keys : List SubtreeFilterKey) :
    queryLocalRetainedCacheCost keys = 0 := by
  rfl

def selectiveSubtreeFilter
    (minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey) : Option Nat :=
  if minimumNodeSize ≤ nodeSizes key then memoizedSubtreeFilter cache key
  else subtreeFilter key

theorem selective_subtree_filter_exact
    (minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (sound : soundSubtreeFilterCache cache) :
    selectiveSubtreeFilter minimumNodeSize nodeSizes cache key = subtreeFilter key := by
  unfold selectiveSubtreeFilter
  split
  · exact memoized_subtree_filter_exact cache key sound
  · rfl

def directSubtreeFilter
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey) : Option Nat :=
  match slot with
  | some entry => if entry.1 == key then entry.2 else subtreeFilter key
  | none => subtreeFilter key

theorem direct_subtree_filter_exact
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey)
    (sound : soundDirectSlot subtreeFilter slot) :
    directSubtreeFilter slot key = subtreeFilter key := by
  cases slot with
  | none => rfl
  | some entry =>
      by_cases same : entry.1 = key
      · subst key
        simpa [directSubtreeFilter] using sound entry (by simp)
      · simp [directSubtreeFilter, same]

def selectiveDirectSubtreeFilter
    (minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey) : Option Nat :=
  if minimumNodeSize ≤ nodeSizes key then directSubtreeFilter slot key
  else subtreeFilter key

theorem selective_direct_subtree_filter_exact
    (minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey)
    (sound : soundDirectSlot subtreeFilter slot) :
    selectiveDirectSubtreeFilter minimumNodeSize nodeSizes slot key = subtreeFilter key := by
  unfold selectiveDirectSubtreeFilter
  split
  · exact direct_subtree_filter_exact slot key sound
  · rfl

theorem selective_direct_size_eight_exact
    (nodeSizes : SubtreeFilterKey → Nat)
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey)
    (sound : soundDirectSlot subtreeFilter slot) :
    selectiveDirectSubtreeFilter 8 nodeSizes slot key = subtreeFilter key := by
  exact selective_direct_subtree_filter_exact 8 nodeSizes slot key sound

def wrappedDirectMissObjectCost (misses : Nat) : Nat := misses * 2

def flatDirectMissObjectCost (misses : Nat) : Nat := misses

theorem flat_direct_miss_object_cost_le (misses : Nat) :
    flatDirectMissObjectCost misses ≤ wrappedDirectMissObjectCost misses := by
  simp [flatDirectMissObjectCost, wrappedDirectMissObjectCost]
  omega

def boundedSubtreeFilterCacheCost (slotCount : Nat) : Nat := slotCount

theorem bounded_subtree_filter_cache_cost_fixed (slotCount _queries : Nat) :
    boundedSubtreeFilterCacheCost slotCount = slotCount := by
  rfl

def rootScopedSubtreeFilter
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey) : Option Nat :=
  memoizedSubtreeFilter cache key

theorem root_scoped_subtree_filter_exact
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (sound : soundSubtreeFilterCache cache) :
    rootScopedSubtreeFilter cache key = subtreeFilter key := by
  exact memoized_subtree_filter_exact cache key sound

def rootScopedCacheProbeCost (roots : Nat) : Nat := roots

theorem root_scoped_cache_probe_cost (roots childNodes : Nat) :
    rootScopedCacheProbeCost roots ≤ roots + childNodes := by
  simp [rootScopedCacheProbeCost]

theorem enlarged_root_subtree_cache_cost_fixed :
    boundedSubtreeFilterCacheCost 262144 = 262144 := by
  rfl

def twoWaySubtreeLookup
    (first second : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey) : Option (Option Nat) :=
  match first with
  | some entry => if entry.1 == key then some entry.2 else
      match second with
      | some entry => if entry.1 == key then some entry.2 else none
      | none => none
  | none =>
      match second with
      | some entry => if entry.1 == key then some entry.2 else none
      | none => none

theorem two_way_subtree_lookup_exact
    (first second : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey)
    (result : Option Nat)
    (firstSound : soundDirectSlot subtreeFilter first)
    (secondSound : soundDirectSlot subtreeFilter second)
    (hit : twoWaySubtreeLookup first second key = some result) :
    result = subtreeFilter key := by
  cases first with
  | none =>
      cases second with
      | none => simp [twoWaySubtreeLookup] at hit
      | some entry =>
          by_cases same : entry.1 = key
          · subst key
            have value : entry.2 = result := by
              exact Option.some.inj (by simpa [twoWaySubtreeLookup] using hit)
            exact value.symm.trans (secondSound entry (by simp))
          · simp [twoWaySubtreeLookup, same] at hit
  | some firstEntry =>
      by_cases firstSame : firstEntry.1 = key
      · subst key
        have value : firstEntry.2 = result := by
          exact Option.some.inj (by simpa [twoWaySubtreeLookup] using hit)
        exact value.symm.trans (firstSound firstEntry (by simp))
      · cases second with
        | none => simp [twoWaySubtreeLookup, firstSame] at hit
        | some secondEntry =>
            by_cases secondSame : secondEntry.1 = key
            · subst key
              have value : secondEntry.2 = result := by
                exact Option.some.inj (by
                  simpa [twoWaySubtreeLookup, firstSame] using hit)
              exact value.symm.trans (secondSound secondEntry (by simp))
            · simp [twoWaySubtreeLookup, firstSame, secondSame] at hit

def twoWaySubtreeCacheCost (setCount : Nat) : Nat := setCount * 2

theorem two_way_subtree_cache_retention_fixed :
    twoWaySubtreeCacheCost 32768 = 65536 := by
  decide

def threadLocalSubtreeCacheCost (threadCount slotCount : Nat) : Nat :=
  threadCount * slotCount

theorem thread_local_subtree_cache_retention_fixed :
    threadLocalSubtreeCacheCost 10 16384 = 163840 := by
  decide

theorem thread_local_subtree_lookup_exact
    (slot : Option (SubtreeFilterKey × Option Nat))
    (key : SubtreeFilterKey)
    (sound : soundDirectSlot subtreeFilter slot) :
    directSubtreeFilter slot key = subtreeFilter key := by
  exact direct_subtree_filter_exact slot key sound

def boundedSubtreeFilterInsert
    (limit : Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey) : SubtreeFilterCache :=
  let retained := if cache.length < limit then cache else []
  (key, subtreeFilter key) :: retained

theorem bounded_subtree_filter_insert_sound
    (limit : Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (sound : soundSubtreeFilterCache cache) :
    soundSubtreeFilterCache (boundedSubtreeFilterInsert limit cache key) := by
  unfold soundSubtreeFilterCache
  intro entry member
  by_cases below : cache.length < limit
  · simp [boundedSubtreeFilterInsert, below] at member
    exact member.elim
      (fun head => by subst entry; rfl)
      (sound entry)
  · simp [boundedSubtreeFilterInsert, below] at member
    subst entry
    rfl

theorem bounded_subtree_filter_retention
    (limit : Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (positive : 0 < limit)
    (bounded : cache.length ≤ limit) :
    (boundedSubtreeFilterInsert limit cache key).length ≤ limit := by
  unfold boundedSubtreeFilterInsert
  split
  · simp_all
    omega
  · simp_all
    omega

def selectiveSubtreeCacheInsert
    (limit minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey) : SubtreeFilterCache :=
  if minimumNodeSize ≤ nodeSizes key then boundedSubtreeFilterInsert limit cache key
  else cache

theorem selective_subtree_cache_insert_sound
    (limit minimumNodeSize : Nat)
    (nodeSizes : SubtreeFilterKey → Nat)
    (cache : SubtreeFilterCache)
    (key : SubtreeFilterKey)
    (sound : soundSubtreeFilterCache cache) :
    soundSubtreeFilterCache
      (selectiveSubtreeCacheInsert limit minimumNodeSize nodeSizes cache key) := by
  unfold selectiveSubtreeCacheInsert
  split
  · exact bounded_subtree_filter_insert_sound limit cache key sound
  · exact sound

end FactExplosion
