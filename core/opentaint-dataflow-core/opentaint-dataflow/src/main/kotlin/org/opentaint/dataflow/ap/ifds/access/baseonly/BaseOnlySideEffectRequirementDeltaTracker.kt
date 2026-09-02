package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp

internal class BaseOnlySideEffectRequirementDeltaTracker {
    private data class Key(
        val currentBase: AccessPathBase,
        val currentAccess: BaseOnlyAccess,
        val requirementBase: AccessPathBase,
        val requirementAccess: BaseOnlyAccess,
    )

    private val appliedExclusions = hashMapOf<Key, ExclusionSet>()

    fun add(
        currentInitial: InitialFactAp,
        requirement: InitialFactAp,
    ): InitialFactAp? {
        currentInitial as BaseOnlyInitialFactAp
        requirement as BaseOnlyInitialFactAp

        val key = Key(currentInitial.base, currentInitial.access, requirement.base, requirement.access)
        val previous = appliedExclusions[key]
        if (previous == null) {
            appliedExclusions[key] = requirement.exclusions
            return requirement
        }

        val incoming = requirement.exclusions
        val update = when {
            incoming is ExclusionSet.Empty || previous is ExclusionSet.Universe -> null
            incoming is ExclusionSet.Universe -> ExclusionUpdate(incoming, incoming)
            previous is ExclusionSet.Empty -> ExclusionUpdate(incoming, incoming)
            else -> {
                check(previous is ExclusionSet.Concrete && incoming is ExclusionSet.Concrete)
                val previousSet = previous.set as BaseOnlyExclusionAccessorSet
                val incomingSet = incoming.set as BaseOnlyExclusionAccessorSet
                previousSet.unionWithAdded(incomingSet)?.let {
                    ExclusionUpdate(
                        merged = ExclusionSet.Concrete(it.union),
                        added = ExclusionSet.Concrete(it.added),
                    )
                }
            }
        } ?: return null

        appliedExclusions[key] = update.merged
        return requirement.replaceExclusions(update.added)
    }

    private data class ExclusionUpdate(
        val merged: ExclusionSet,
        val added: ExclusionSet,
    )
}
