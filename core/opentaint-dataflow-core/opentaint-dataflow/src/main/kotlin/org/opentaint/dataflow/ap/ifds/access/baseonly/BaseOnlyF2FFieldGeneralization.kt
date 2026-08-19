package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor

internal const val MAX_FIELD_ENUMERATION_EDGES = 8

internal data class BaseOnlySummaryEdgeAccessKey(
    val initial: BaseOnlyAccess,
    val final: BaseOnlyAccess,
)

internal data class BaseOnlyFieldErasureGroup(
    val initial: BaseOnlyAccess,
    val final: BaseOnlyAccess,
)

internal data class BaseOnlyFieldGeneralizationResult(
    val summaries: List<BaseOnlySummaryEdge>,
    val newlyGeneralized: Set<BaseOnlyFieldErasureGroup>,
)

internal data class BaseOnlyFieldGeneralizationUpdate(
    val representative: BaseOnlySummaryEdge,
    val absorbedMembers: Set<BaseOnlySummaryEdgeAccessKey>,
    val newlyGeneralized: Boolean,
)

/**
 * Writer-owned widening state for one initial-base/final-base storage scope.
 */
internal class BaseOnlyF2FFieldGeneralizer(
    private val maxEnumeratedEdges: Int = MAX_FIELD_ENUMERATION_EDGES,
    private val mergeExclusions: (List<ExclusionSet>) -> ExclusionSet = { exclusions ->
        exclusions.reduce(ExclusionSet::union)
    },
) {
    private val generalizedGroups = linkedSetOf<BaseOnlyFieldErasureGroup>()
    private val exclusionsByGroup = linkedMapOf<BaseOnlyFieldErasureGroup, ExclusionSet>()
    private val membersByGroup = linkedMapOf<
        BaseOnlyFieldErasureGroup,
        LinkedHashMap<BaseOnlySummaryEdgeAccessKey, ExclusionSet>,
    >()

    fun groupOf(initial: BaseOnlyAccess, final: BaseOnlyAccess): BaseOnlyFieldErasureGroup? {
        val erasedInitial = initial.eraseFieldForSummaryGeneralization() ?: return null
        val erasedFinal = final.eraseFieldForSummaryGeneralization() ?: return null
        return BaseOnlyFieldErasureGroup(erasedInitial, erasedFinal)
    }

    fun isGeneralized(initial: BaseOnlyAccess, final: BaseOnlyAccess): Boolean =
        groupOf(initial, final) in generalizedGroups

    /**
     * Incrementally observes one canonical edge. Until the group crosses its budget the edge
     * remains exact. Afterwards each new member only updates the already materialized
     * representative.
     */
    fun observeCanonicalEdge(edge: BaseOnlySummaryEdge): BaseOnlyFieldGeneralizationUpdate? {
        val group = groupOf(edge.initial, edge.final) ?: return null
        val currentRepresentativeExclusion = exclusionsByGroup[group]
        if (group in generalizedGroups) {
            val mergedExclusion = mergeExclusions(listOf(currentRepresentativeExclusion!!, edge.exclusion))
            if (mergedExclusion == currentRepresentativeExclusion) return null
            exclusionsByGroup[group] = mergedExclusion
            return BaseOnlyFieldGeneralizationUpdate(
                representative = createRepresentative(group),
                absorbedMembers = emptySet(),
                newlyGeneralized = false,
            )
        }

        val members = membersByGroup.getOrPut(group) { linkedMapOf() }
        members[edge.accessKey] = edge.exclusion
        if (members.size <= maxEnumeratedEdges) return null

        exclusionsByGroup[group] = mergeExclusions(members.values.toList())
        generalizedGroups += group
        membersByGroup.remove(group)
        return BaseOnlyFieldGeneralizationUpdate(
            representative = createRepresentative(group),
            absorbedMembers = members.keys.toSet(),
            newlyGeneralized = true,
        )
    }

    fun removeCanonicalEdge(edge: BaseOnlySummaryEdge) {
        val group = groupOf(edge.initial, edge.final) ?: return
        if (group in generalizedGroups) return
        val members = membersByGroup[group] ?: return
        members.remove(edge.accessKey)
        if (members.isEmpty()) membersByGroup.remove(group)
    }

    fun rewrite(summaries: List<BaseOnlySummaryEdge>): BaseOnlyFieldGeneralizationResult {
        val members = summaries.groupByTo(linkedMapOf()) { edge ->
            groupOf(edge.initial, edge.final)
        }

        val newlyGeneralized = linkedSetOf<BaseOnlyFieldErasureGroup>()
        members.forEach { (group, edges) ->
            if (group == null) return@forEach

            val observedExclusion = mergeExclusions(edges.map(BaseOnlySummaryEdge::exclusion))
            exclusionsByGroup[group] = if (group in generalizedGroups) {
                mergeExclusions(listOf(exclusionsByGroup.getValue(group), observedExclusion))
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

internal val BaseOnlySummaryEdge.accessKey: BaseOnlySummaryEdgeAccessKey
    get() = BaseOnlySummaryEdgeAccessKey(initial, final)

internal fun intersectSummaryFieldGeneralizationExclusions(
    exclusions: List<ExclusionSet>,
): ExclusionSet = exclusions
    .map(ExclusionSet::suffixExclusions)
    .reduce(ExclusionSet::intersect)

private fun ExclusionSet.suffixExclusions(): ExclusionSet = when (this) {
    ExclusionSet.Empty,
    ExclusionSet.Universe,
    -> this

    is ExclusionSet.Concrete -> set.fold(ExclusionSet.Empty as ExclusionSet) { suffix, accessor ->
        when (accessor) {
            AnyAccessor,
            ElementAccessor,
            is ClassStaticAccessor,
            is FieldAccessor,
            -> suffix

            else -> suffix.add(accessor)
        }
    }
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
