package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.InitialToFinalSummaryStorageStats
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.util.ConcurrentReadSafeLong2ObjectMap
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.long2ObjectMap
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodInitialToFinalBaseOnlyApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonF2FSummary<BaseOnlyAccess, BaseOnlyAccess>(methodInitialStatement),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess, BaseOnlyAccess> = F2FStorage(apManager)

    private class F2FStorage(
        private val manager: BaseOnlyApManager,
    ) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
        private val mergedExclusions = linkedMapOf<BaseOnlySummaryEdgeAccessKey, ExclusionSet>()
        private val rawKeysByFieldGroup = linkedMapOf<
            BaseOnlyFieldErasureGroup,
            MutableList<BaseOnlySummaryEdgeAccessKey>,
        >()
        private val fieldGeneralizer = BaseOnlyF2FFieldGeneralizer(
            mergeExclusions = ::intersectSummaryFieldGeneralizationExclusions,
        )

        private val summaries = CanonicalSummaryIndex()

        private class CanonicalSummaryIndex {
            @Volatile
            private var liveEdgeCount = 0L

            @Volatile
            private var liveFinalFactSizeSum = 0L

            private class EdgeNode {
                @Volatile
                var exclusion: ExclusionSet? = null
            }

            private class FinalIndex {
                val finals: ConcurrentReadSafeLong2ObjectMap<EdgeNode> = long2ObjectMap()
                val candidates = BaseOnlyInitialAccessIndex<EdgeNode>()
            }

            private val initials = BaseOnlyInitialAccessIndex<FinalIndex>()

            fun put(edge: BaseOnlySummaryEdge): ExclusionSet? {
                val finalIndex = initials.getOrCreate(edge.initial, ::FinalIndex)
                val node = finalIndex.finals[edge.final] ?: EdgeNode().also {
                    finalIndex.finals.put(edge.final, it)
                    finalIndex.candidates.getOrCreate(edge.final) { it }
                }
                val previous = node.exclusion
                node.exclusion = edge.exclusion
                if (previous == null) {
                    liveEdgeCount++
                    liveFinalFactSizeSum += edge.final.size
                }
                return previous
            }

            fun remove(edge: BaseOnlySummaryEdge): Boolean {
                val node = initials.get(edge.initial)?.finals?.get(edge.final) ?: return false
                if (node.exclusion != edge.exclusion) return false
                node.exclusion = null
                liveEdgeCount--
                liveFinalFactSizeSum -= edge.final.size
                return true
            }

            fun get(key: BaseOnlySummaryEdgeAccessKey): ExclusionSet? =
                initials.get(key.initial)?.finals?.get(key.final)?.exclusion

            fun stats(): InitialToFinalSummaryStorageStats =
                InitialToFinalSummaryStorageStats(liveEdgeCount, liveFinalFactSizeSum)

            fun collectAll(consume: (BaseOnlySummaryEdge) -> Unit) {
                initials.collectAll { initial, finals -> finals.collect(initial, consume) }
            }

            fun collectCandidates(initial: BaseOnlyAccess, consume: (BaseOnlySummaryEdge) -> Unit) {
                initials.collectCandidates(initial) { candidateInitial, finals ->
                    finals.collect(candidateInitial, consume)
                }
            }

            fun collectCandidates(
                initial: BaseOnlyAccess,
                final: BaseOnlyAccess,
                consume: (BaseOnlySummaryEdge) -> Unit,
            ) {
                initials.collectCandidates(initial) { candidateInitial, finals ->
                    finals.collectCandidates(candidateInitial, final, consume)
                }
            }

            fun collectFinalCandidates(
                final: BaseOnlyAccess,
                consume: (BaseOnlySummaryEdge) -> Unit,
            ) {
                initials.collectAll { candidateInitial, finals ->
                    finals.collectCandidates(candidateInitial, final, consume)
                }
            }

            private fun FinalIndex.collect(
                initial: BaseOnlyAccess,
                consume: (BaseOnlySummaryEdge) -> Unit,
            ) {
                finals.forEachEntry { final, node ->
                    node.exclusion?.let { exclusion ->
                        consume(BaseOnlySummaryEdge(initial, final, exclusion))
                    }
                }
            }

            private fun FinalIndex.collectCandidates(
                initial: BaseOnlyAccess,
                final: BaseOnlyAccess,
                consume: (BaseOnlySummaryEdge) -> Unit,
            ) {
                candidates.collectCandidates(final) { candidateFinal, node ->
                    node.exclusion?.let { exclusion ->
                        consume(BaseOnlySummaryEdge(initial, candidateFinal, exclusion))
                    }
                }
            }
        }

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val newEdges = edges.filterNot {
                it.initial.isCollapsed ||
                    it.final.isCollapsed
            }
            if (newEdges.isEmpty()) return

            val pendingDelta = linkedMapOf<BaseOnlySummaryEdgeAccessKey, BaseOnlySummaryEdge>()
            val candidates = mergeExactEdges(newEdges)
            candidates.sortedWith(BASE_ONLY_SUMMARY_EDGE_ORDER).forEach { candidate ->
                if (manager.summaryStorageFieldGeneralizationEnabled &&
                    fieldGeneralizer.isGeneralized(candidate.initial, candidate.final)
                ) {
                    removeRawEdge(candidate.accessKey)
                    fieldGeneralizer.observeCanonicalEdge(candidate)?.let { update ->
                        insertCanonical(update.representative, pendingDelta, observeForGeneralization = false)
                    }
                    return@forEach
                }

                insertCanonical(candidate, pendingDelta, observeForGeneralization = true)
            }

            pendingDelta.values.forEach { edge ->
                if (summaries.get(edge.accessKey) == edge.exclusion) added += edge.toBuilder()
            }
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPattern: BaseOnlyAccess?,
        ) {
            collectViews(initialFactPattern).forEach { (key, exclusion) ->
                dst += BaseOnlySummaryEdge(key.initial, key.final, exclusion).toBuilder()
            }
        }

        override fun collectSummariesByFinalTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            finalFactPattern: BaseOnlyAccess,
        ) {
            collectViews(initialFactPattern = null, finalFactPattern = finalFactPattern).forEach { (key, exclusion) ->
                dst += BaseOnlySummaryEdge(key.initial, key.final, exclusion).toBuilder()
            }
        }

        override fun storageStats(): InitialToFinalSummaryStorageStats = summaries.stats()

        private fun mergeExactEdges(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
        ): List<BaseOnlySummaryEdge> {
            val affectedKeys = linkedSetOf<BaseOnlySummaryEdgeAccessKey>()
            edges.forEach { edge ->
                val key = BaseOnlySummaryEdgeAccessKey(edge.initial, edge.final)
                affectedKeys += key
                val previous = mergedExclusions[key]
                mergedExclusions[key] = previous?.intersect(edge.exclusion) ?: edge.exclusion
                if (manager.summaryStorageFieldGeneralizationEnabled && previous == null) {
                    fieldGeneralizer.groupOf(edge.initial, edge.final)?.let { group ->
                        rawKeysByFieldGroup.getOrPut(group, ::arrayListOf).add(key)
                    }
                }
            }

            return affectedKeys.map { key ->
                BaseOnlySummaryEdge(
                    initial = key.initial,
                    final = key.final,
                    exclusion = mergedExclusions.getValue(key),
                )
            }
        }

        private fun insertCanonical(
            candidate: BaseOnlySummaryEdge,
            pendingDelta: MutableMap<BaseOnlySummaryEdgeAccessKey, BaseOnlySummaryEdge>,
            observeForGeneralization: Boolean,
        ) {
            val candidateKey = candidate.accessKey
            val related = canonicalCandidates(candidate.initial, candidate.final)
            for (existing in related) {
                if (existing.accessKey == candidateKey) continue
                if (BaseOnlySummaryEdgeOps.canonicallyCovers(manager, existing, candidate)) return
            }

            putCanonical(candidate, pendingDelta)
            related.forEach { existing ->
                if (existing.accessKey != candidateKey &&
                    BaseOnlySummaryEdgeOps.canonicallyCovers(manager, candidate, existing)
                ) {
                    removeCanonical(existing, pendingDelta)
                }
            }

            if (!observeForGeneralization || !manager.summaryStorageFieldGeneralizationEnabled) return
            val update = fieldGeneralizer.observeCanonicalEdge(candidate) ?: return
            if (update.newlyGeneralized) purgeRawGroup(update.representative)
            insertCanonical(update.representative, pendingDelta, observeForGeneralization = false)
            update.absorbedMembers.forEach { member ->
                currentEdge(member)?.let { removeCanonical(it, pendingDelta) }
            }
            if (update.newlyGeneralized) pendingDelta[update.representative.accessKey] = update.representative
        }

        private fun putCanonical(
            edge: BaseOnlySummaryEdge,
            pendingDelta: MutableMap<BaseOnlySummaryEdgeAccessKey, BaseOnlySummaryEdge>,
        ) {
            val key = edge.accessKey
            val previous = summaries.put(edge)
            if (previous != edge.exclusion) pendingDelta[key] = edge
        }

        private fun removeCanonical(
            edge: BaseOnlySummaryEdge,
            pendingDelta: MutableMap<BaseOnlySummaryEdgeAccessKey, BaseOnlySummaryEdge>,
        ) {
            val key = edge.accessKey
            if (!summaries.remove(edge)) return
            pendingDelta.remove(key)
            fieldGeneralizer.removeCanonicalEdge(edge)
        }

        private fun canonicalCandidates(
            initial: BaseOnlyAccess,
            final: BaseOnlyAccess,
        ): List<BaseOnlySummaryEdge> = buildList {
            summaries.collectCandidates(initial, final) { add(it) }
        }

        private fun currentEdge(key: BaseOnlySummaryEdgeAccessKey): BaseOnlySummaryEdge? =
            summaries.get(key)?.let { exclusion -> BaseOnlySummaryEdge(key.initial, key.final, exclusion) }

        private fun removeRawEdge(key: BaseOnlySummaryEdgeAccessKey) {
            mergedExclusions.remove(key)
        }

        private fun purgeRawGroup(representative: BaseOnlySummaryEdge) {
            val group = fieldGeneralizer.groupOf(representative.initial, representative.final) ?: return
            rawKeysByFieldGroup.remove(group)?.forEach(mergedExclusions::remove)
        }

        private fun collectViews(
            initialFactPattern: BaseOnlyAccess?,
            finalFactPattern: BaseOnlyAccess? = null,
        ): Map<BaseOnlySummaryEdgeAccessKey, ExclusionSet> {
            val views = linkedMapOf<BaseOnlySummaryEdgeAccessKey, ExclusionSet>()
            fun collect(edge: BaseOnlySummaryEdge) {
                views.addIfMatches(
                    initialFactPattern,
                    finalFactPattern,
                    edge.initial,
                    edge.final,
                    edge.exclusion,
                )

                if (manager.traceResolutionModeEnabled()) {
                    val normalizedInitial = normalizeSummaryInitialAccess(edge.initial, edge.final)
                    if (normalizedInitial != edge.initial) {
                        views.addIfMatches(
                            initialFactPattern,
                            finalFactPattern,
                            normalizedInitial,
                            edge.final,
                            edge.exclusion,
                        )
                    }
                }
            }

            if (finalFactPattern != null) {
                summaries.collectFinalCandidates(finalFactPattern, ::collect)
                return views
            }

            if (initialFactPattern == null || manager.traceResolutionModeEnabled()) {
                summaries.collectAll(::collect)
                return views
            }

            summaries.collectCandidates(initialFactPattern, ::collect)
            return views
        }

        private fun MutableMap<BaseOnlySummaryEdgeAccessKey, ExclusionSet>.addIfMatches(
            initialPattern: BaseOnlyAccess?,
            finalPattern: BaseOnlyAccess?,
            initial: BaseOnlyAccess,
            final: BaseOnlyAccess,
            exclusion: ExclusionSet,
        ) {
            if (initialPattern != null && !baseOnlySummaryInitialMatches(initialPattern, initial)) return
            if (finalPattern != null && !baseOnlySummaryInitialMatches(finalPattern, final)) return
            val key = BaseOnlySummaryEdgeAccessKey(initial, final)
            this[key] = this[key]?.intersect(exclusion) ?: exclusion
        }

        private fun BaseOnlySummaryEdge.toBuilder(): F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess> =
            Builder(manager)
                .setInitialAp(initial)
                .setExitAp(final)
                .setExclusion(exclusion)

    }

    private class Builder(override val apManager: BaseOnlyApManager) :
        F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>(), BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
        override fun nonNullIAP(iap: BaseOnlyAccess?): BaseOnlyAccess = iap ?: ABSTRACT_EMPTY_ACCESS
    }
}

internal fun normalizeSummaryInitialAccess(initial: BaseOnlyAccess, final: BaseOnlyAccess): BaseOnlyAccess {
    if (initial.apSlot != 1 || final.apSlot != 2) return initial
    return packBaseOnlyAccess(initial.staticIdx, NO_ACCESSOR, ABSTRACT_MARK)
}
