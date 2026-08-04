package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet

internal const val MAX_FIELD_ENUMERATION_EDGES = 16

internal data class BaseOnlyFieldErasureGroup(
    val initial: BaseOnlyAccess,
    val final: BaseOnlyAccess,
)

internal data class BaseOnlyFieldGeneralizationResult(
    val summaries: List<BaseOnlySummaryEdge>,
    val newlyGeneralized: Set<BaseOnlyFieldErasureGroup>,
)

/**
 * Writer-owned widening state for one initial-base/final-base storage scope.
 */
internal class BaseOnlyF2FFieldGeneralizer(
    private val maxEnumeratedEdges: Int = MAX_FIELD_ENUMERATION_EDGES,
) {
    private val generalizedGroups = linkedSetOf<BaseOnlyFieldErasureGroup>()
    private val exclusionsByGroup = linkedMapOf<BaseOnlyFieldErasureGroup, ExclusionSet>()

    fun groupOf(initial: BaseOnlyAccess, final: BaseOnlyAccess): BaseOnlyFieldErasureGroup? {
        val erasedInitial = initial.eraseFieldForSummaryGeneralization() ?: return null
        val erasedFinal = final.eraseFieldForSummaryGeneralization() ?: return null
        return BaseOnlyFieldErasureGroup(erasedInitial, erasedFinal)
    }

    fun isGeneralized(initial: BaseOnlyAccess, final: BaseOnlyAccess): Boolean =
        groupOf(initial, final) in generalizedGroups

    fun rewrite(summaries: List<BaseOnlySummaryEdge>): BaseOnlyFieldGeneralizationResult {
        val members = summaries.groupByTo(linkedMapOf()) { edge ->
            groupOf(edge.initial, edge.final)
        }

        val newlyGeneralized = linkedSetOf<BaseOnlyFieldErasureGroup>()
        members.forEach { (group, edges) ->
            if (group == null) return@forEach

            val observedExclusion = edges
                .map(BaseOnlySummaryEdge::exclusion)
                .reduce(ExclusionSet::union)
            exclusionsByGroup[group] = if (group in generalizedGroups) {
                exclusionsByGroup.getValue(group).union(observedExclusion)
            } else {
                observedExclusion
            }

            if (group !in generalizedGroups && edges.size > maxEnumeratedEdges) {
                generalizedGroups += group
                newlyGeneralized += group
            }
        }

        if (generalizedGroups.isEmpty()) {
            return BaseOnlyFieldGeneralizationResult(summaries, emptySet())
        }

        val rewritten = summaries.filterTo(arrayListOf()) { edge ->
            groupOf(edge.initial, edge.final) !in generalizedGroups
        }
        generalizedGroups.forEach { group ->
            rewritten += createRepresentative(group)
        }
        rewritten.sortWith(BASE_ONLY_SUMMARY_EDGE_ORDER)

        return BaseOnlyFieldGeneralizationResult(rewritten, newlyGeneralized)
    }

    fun representative(group: BaseOnlyFieldErasureGroup): BaseOnlySummaryEdge =
        createRepresentative(group)

    private fun createRepresentative(group: BaseOnlyFieldErasureGroup): BaseOnlySummaryEdge =
        BaseOnlySummaryEdge(group.initial, group.final, exclusionsByGroup.getValue(group))
}

internal fun BaseOnlyAccess.eraseFieldForSummaryGeneralization(): BaseOnlyAccess? {
    if (staticIdx != NO_ACCESSOR || valueAccessorState != BaseOnlyValueAccessorState.Normal) return null

    val eligible = when {
        fieldIdx == ABSTRACT_MARK && suffixIdx == NO_ACCESSOR -> true
        fieldIdx.isStructuralIdx() && suffixIdx == ABSTRACT_MARK -> true
        fieldIdx == NO_ACCESSOR && suffixIdx == ABSTRACT_MARK -> true
        else -> false
    }
    return ABSTRACT_EMPTY_ACCESS.takeIf { eligible }
}

internal val BASE_ONLY_SUMMARY_EDGE_ORDER = compareBy<BaseOnlySummaryEdge>(
    { it.initial },
    { it.final },
)
