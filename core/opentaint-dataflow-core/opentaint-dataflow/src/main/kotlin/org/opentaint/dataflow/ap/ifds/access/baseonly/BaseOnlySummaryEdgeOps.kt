package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet

internal data class BaseOnlySummaryEdge(
    val initial: BaseOnlyAccess,
    val final: BaseOnlyAccess,
    val exclusion: ExclusionSet,
)

internal object BaseOnlySummaryEdgeOps {
    fun canonicallyCovers(
        manager: BaseOnlyApManager,
        cover: BaseOnlySummaryEdge,
        covered: BaseOnlySummaryEdge,
    ): Boolean {
        if (!subsumes(manager, cover, covered)) return false
        if (!subsumes(manager, covered, cover)) return true
        return BASE_ONLY_SUMMARY_EDGE_ORDER.compare(cover, covered) < 0
    }

    fun subsumes(
        manager: BaseOnlyApManager,
        general: BaseOnlySummaryEdge,
        specific: BaseOnlySummaryEdge,
    ): Boolean {
        if (general.initial == specific.initial) {
            val effectiveExclusion = specific.exclusion.union(general.exclusion)
            return effectiveExclusion == specific.exclusion &&
                BaseOnlyAccessOps.covers(general.final, specific.final)
        }

        val specificInitial = SummaryFact(specific.initial, specific.exclusion)
        val specificFinal = SummaryFact(specific.final, specific.exclusion)
        val application = applyEdge(manager, general, specificInitial) ?: return false
        if (application.result != specificFinal) return false

        return reconstructInitials(
            manager = manager,
            edge = general,
            final = specificFinal,
            residual = application.residual,
        ).any { it == specificInitial.access }
    }

    private fun applyEdge(
        manager: BaseOnlyApManager,
        edge: BaseOnlySummaryEdge,
        initial: SummaryFact,
    ): SummaryApplication? {
        val match = BaseOnlyAccessOps.matchPrefix(initial.access, edge.initial)
        if (match.emptyDelta) {
            return SummaryApplication(
                residual = SummaryResidual.Empty,
                result = SummaryFact(edge.final, initial.exclusion.union(edge.exclusion)),
            )
        }
        if (!match.hasSuffix) return null

        val residualAccess = retainResidual(manager, match.suffix, edge.exclusion) ?: return null
        val resultAccess = BaseOnlyAccessOps.appendFinal(edge.final, residualAccess) ?: return null
        return SummaryApplication(
            residual = SummaryResidual.Access(residualAccess),
            result = SummaryFact(resultAccess, initial.exclusion),
        )
    }

    private fun reconstructInitials(
        manager: BaseOnlyApManager,
        edge: BaseOnlySummaryEdge,
        final: SummaryFact,
        residual: SummaryResidual,
    ): Sequence<BaseOnlyAccess> {
        return BaseOnlyAccessOps.splitDelta(
            fact = final.access,
            pattern = edge.final,
            manager = manager,
            exclusions = edge.exclusion,
        ).asSequence().mapNotNull { (_, delta) ->
            val reconstructedResidual = delta.toSummaryResidual(manager, edge.exclusion) ?: return@mapNotNull null
            if (reconstructedResidual != residual) return@mapNotNull null

            when (reconstructedResidual) {
                SummaryResidual.Empty -> edge.initial
                is SummaryResidual.Access -> BaseOnlyAccessOps.append(edge.initial, reconstructedResidual.access)
            }
        }
    }

    private fun BaseOnlyInitialDelta.toSummaryResidual(
        manager: BaseOnlyApManager,
        exclusions: ExclusionSet,
    ): SummaryResidual? = when (this) {
        BaseOnlyEmptyInitialDelta -> SummaryResidual.Empty
        is BaseOnlyNodeInitialDelta ->
            retainResidual(manager, access, exclusions)?.let(SummaryResidual::Access)
    }


    private fun retainResidual(
        manager: BaseOnlyApManager,
        residual: BaseOnlyAccess,
        exclusions: ExclusionSet,
    ): BaseOnlyAccess? = when (exclusions) {
        ExclusionSet.Empty -> residual
        ExclusionSet.Universe -> null
        is ExclusionSet.Concrete -> {
            val accessor = residual.headOrNull?.let(manager.interner::accessor)
            residual.takeUnless { accessor != null && exclusions.contains(accessor) }
        }
    }

    private data class SummaryApplication(
        val residual: SummaryResidual,
        val result: SummaryFact,
    )

    private data class SummaryFact(
        val access: BaseOnlyAccess,
        val exclusion: ExclusionSet,
    )

    private sealed interface SummaryResidual {
        data object Empty : SummaryResidual
        data class Access(val access: BaseOnlyAccess) : SummaryResidual
    }
}
