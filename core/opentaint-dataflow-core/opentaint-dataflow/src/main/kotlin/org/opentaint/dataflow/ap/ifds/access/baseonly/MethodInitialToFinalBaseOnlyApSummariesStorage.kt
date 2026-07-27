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

        private val mergedExclusions = linkedMapOf<EdgeKey, ExclusionSet>()
        private val fieldGeneralizer = BaseOnlyF2FFieldGeneralizer()

        @Volatile
        private var summaries: List<BaseOnlySummaryEdge> = emptyList()

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val newEdges = edges.filterNot {
                it.initial.isCollapsed ||
                    it.final.isCollapsed
            }
            if (newEdges.isEmpty()) return

            val candidates = mergeExactEdges(newEdges)
            val previous = summaries
            val canonical = retainCanonicalSummaries(previous, candidates)
            if (!manager.fieldGeneralizationEnabled) {
                summaries = canonical
                appendAddedSummaries(previous, summaries, emptySet(), added)
                return
            }

            val generalization = fieldGeneralizer.rewrite(canonical)
            purgeGeneralizedExactEdges()
            summaries = generalization.summaries
            appendAddedSummaries(previous, summaries, generalization.newlyGeneralized, added)
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPattern: BaseOnlyAccess?,
        ) {
            collectViews(initialFactPattern).forEach { (key, exclusion) ->
                dst += BaseOnlySummaryEdge(key.initial, key.final, exclusion).toBuilder()
            }
        }

        private fun mergeExactEdges(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
        ): List<BaseOnlySummaryEdge> {
            val affectedKeys = linkedSetOf<EdgeKey>()
            edges.forEach { edge ->
                val key = EdgeKey(edge.initial, edge.final)
                affectedKeys += key
                val previous = mergedExclusions[key]
                mergedExclusions[key] = previous?.intersect(edge.exclusion) ?: edge.exclusion
            }

            return affectedKeys.map { key ->
                BaseOnlySummaryEdge(
                    initial = key.initial,
                    final = key.final,
                    exclusion = mergedExclusions.getValue(key),
                )
            }
        }

        private val BaseOnlySummaryEdge.key: EdgeKey
            get() = EdgeKey(initial, final)

        private fun retainCanonicalSummaries(
            previous: List<BaseOnlySummaryEdge>,
            candidates: List<BaseOnlySummaryEdge>,
        ): List<BaseOnlySummaryEdge> {
            val affectedKeys = candidates.mapTo(hashSetOf()) { it.key }
            val retained = previous.filterTo(arrayListOf()) { it.key !in affectedKeys }
            candidates.sortedWith(BASE_ONLY_SUMMARY_EDGE_ORDER).forEach { candidate ->
                if (retained.any { BaseOnlySummaryEdgeOps.canonicallyCovers(manager, it, candidate) }) {
                    return@forEach
                }
                retained.removeAll { BaseOnlySummaryEdgeOps.canonicallyCovers(manager, candidate, it) }
                retained += candidate
            }
            return retained.sortedWith(BASE_ONLY_SUMMARY_EDGE_ORDER)
        }

        private fun purgeGeneralizedExactEdges() {
            mergedExclusions.entries.removeAll { (key, _) ->
                fieldGeneralizer.isGeneralized(key.initial, key.final)
            }
        }

        private fun appendAddedSummaries(
            previous: List<BaseOnlySummaryEdge>,
            current: List<BaseOnlySummaryEdge>,
            newlyGeneralized: Set<BaseOnlyFieldErasureGroup>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val previousSet = previous.toHashSet()
            val forcedRepresentatives = newlyGeneralized.mapTo(linkedSetOf(), fieldGeneralizer::representative)
            current.filter { it in forcedRepresentatives || it !in previousSet }.forEach { edge ->
                added += edge.toBuilder()
            }
        }

        private fun collectViews(initialFactPattern: BaseOnlyAccess?): Map<EdgeKey, ExclusionSet> {
            val views = linkedMapOf<EdgeKey, ExclusionSet>()
            summaries.forEach { edge ->
                views.addIfMatches(initialFactPattern, edge.initial, edge.final, edge.exclusion)

                if (manager.traceResolutionModeEnabled()) {
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
