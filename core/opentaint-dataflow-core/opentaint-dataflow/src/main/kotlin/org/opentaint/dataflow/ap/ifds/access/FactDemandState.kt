package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet

/**
 * Demand-analysis state carried by an IFDS fact edge.
 *
 * Cleaner semantics do not belong here. They are part of the access-path representation selected
 * for the analysis, alongside the concrete or abstract fact that they constrain.
 */
data class FactDemandState(
    val exclusions: ExclusionSet,
) {
    infix fun then(other: FactDemandState): FactDemandState {
        val composedExclusions = exclusions.union(other.exclusions)
        return when {
            composedExclusions === exclusions -> this
            composedExclusions === other.exclusions -> other
            else -> FactDemandState(composedExclusions)
        }
    }

    infix fun join(other: FactDemandState): FactDemandState = then(other)

    fun exclude(accessor: Accessor): FactDemandState =
        withExclusions(exclusions.add(accessor))

    fun withExclusions(exclusions: ExclusionSet): FactDemandState = when {
        exclusions is ExclusionSet.Universe -> Universe
        exclusions === this.exclusions -> this
        else -> FactDemandState(exclusions)
    }

    companion object {
        val Empty = FactDemandState(ExclusionSet.Empty)
        val Universe = FactDemandState(ExclusionSet.Universe)
    }
}
