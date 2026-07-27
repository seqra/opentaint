package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
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
        private data class EdgeKey(
            val initial: BaseOnlyAccess,
            val final: BaseOnlyAccess,
        )

        private val mergedExclusions = linkedMapOf<BaseOnlyAccess, ExclusionSet>()

        @Volatile
        private var summaries: List<BaseOnlySummaryEdge> = emptyList()

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val newEdges = edges.filterNot { it.initial.isCollapsed || it.final.isCollapsed }
            if (newEdges.isEmpty()) return

            val affectedInitials = updateMergedExclusions(newEdges)
            val candidates = rebuildAffectedSummaries(newEdges, affectedInitials)
            val previous = summaries
            summaries = retainCanonicalSummaries(previous, affectedInitials, candidates)
            appendAddedSummaries(previous, summaries, added)
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPattern: BaseOnlyAccess?,
        ) {
            collectViews(initialFactPattern).forEach { (key, exclusion) ->
                dst += BaseOnlySummaryEdge(key.initial, key.final, exclusion).toBuilder()
            }
        }

        private fun updateMergedExclusions(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
        ): Set<BaseOnlyAccess> {
            val affectedInitials = linkedSetOf<BaseOnlyAccess>()
            edges.forEach { edge ->
                affectedInitials += edge.initial
                val previous = mergedExclusions[edge.initial]
                mergedExclusions[edge.initial] = previous?.intersect(edge.exclusion) ?: edge.exclusion
            }
            return affectedInitials
        }

        private fun rebuildAffectedSummaries(
            newEdges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            affectedInitials: Set<BaseOnlyAccess>,
        ): List<BaseOnlySummaryEdge> {
            val candidates = linkedMapOf<EdgeKey, BaseOnlySummaryEdge>()

            summaries.filter { it.initial in affectedInitials }.forEach { edge ->
                candidates[edge.key] = edge.withMergedExclusion()
            }
            newEdges.forEach { edge ->
                val key = EdgeKey(edge.initial, edge.final)
                candidates[key] = BaseOnlySummaryEdge(
                    initial = edge.initial,
                    final = edge.final,
                    exclusion = mergedExclusions.getValue(edge.initial),
                )
            }

            return candidates.values.toList()
        }

        private val BaseOnlySummaryEdge.key: EdgeKey
            get() = EdgeKey(initial, final)

        private fun BaseOnlySummaryEdge.withMergedExclusion(): BaseOnlySummaryEdge =
            copy(exclusion = mergedExclusions.getValue(initial))

        private fun retainCanonicalSummaries(
            previous: List<BaseOnlySummaryEdge>,
            affectedInitials: Set<BaseOnlyAccess>,
            candidates: List<BaseOnlySummaryEdge>,
        ): List<BaseOnlySummaryEdge> {
            val retained = previous.filterTo(arrayListOf()) { it.initial !in affectedInitials }
            candidates.sortedWith(edgeOrder).forEach { candidate ->
                if (retained.any { isCanonicalCover(it, candidate) }) return@forEach
                retained.removeAll { isCanonicalCover(candidate, it) }
                retained += candidate
            }
            return retained.sortedWith(edgeOrder)
        }

        private fun isCanonicalCover(
            cover: BaseOnlySummaryEdge,
            covered: BaseOnlySummaryEdge,
        ): Boolean {
            if (!BaseOnlySummaryEdgeOps.subsumes(manager, cover, covered)) return false
            if (!BaseOnlySummaryEdgeOps.subsumes(manager, covered, cover)) return true
            return edgeOrder.compare(cover, covered) < 0
        }

        private fun appendAddedSummaries(
            previous: List<BaseOnlySummaryEdge>,
            current: List<BaseOnlySummaryEdge>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val previousSet = previous.toHashSet()
            current.filterNot { it in previousSet }.forEach { edge ->
                added += edge.toBuilder()
            }
        }

        private fun collectViews(initialFactPattern: BaseOnlyAccess?): Map<EdgeKey, ExclusionSet> {
            val views = linkedMapOf<EdgeKey, ExclusionSet>()
            summaries.forEach { edge ->
                views.addIfMatches(initialFactPattern, edge.initial, edge.final, edge.exclusion)

                if (manager.normalizedEdgesEnabled()) {
                    val normalizedInitial = normalizeSummaryInitialAccess(edge.initial, edge.final)
                    if (normalizedInitial != edge.initial) {
                        views.addIfMatches(initialFactPattern, normalizedInitial, edge.final, edge.exclusion)
                    }
                }
            }
            return views
        }

        private fun MutableMap<EdgeKey, ExclusionSet>.addIfMatches(
            pattern: BaseOnlyAccess?,
            initial: BaseOnlyAccess,
            final: BaseOnlyAccess,
            exclusion: ExclusionSet,
        ) {
            if (pattern != null && !baseOnlySummaryInitialMatches(pattern, initial)) return
            val key = EdgeKey(initial, final)
            this[key] = this[key]?.intersect(exclusion) ?: exclusion
        }

        private fun BaseOnlySummaryEdge.toBuilder(): F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess> =
            Builder(manager)
                .setInitialAp(initial)
                .setExitAp(final)
                .setExclusion(exclusion)

        private val edgeOrder = compareBy<BaseOnlySummaryEdge>(
            { it.initial },
            { it.final },
        )
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
