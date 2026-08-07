package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.long2ObjectMap
import java.util.concurrent.ConcurrentHashMap

class BaseOnlySideEffectRequirementApStorage : SideEffectRequirementApStorage {
    private val based = ConcurrentHashMap<AccessPathBase, RequirementStorage>()

    override fun add(requirements: List<InitialFactAp>): List<InitialFactAp> {
        val modified = mutableListOf<RequirementStorage>()

        for (requirement in requirements) {
            requirement as BaseOnlyInitialFactAp
            if (requirement.access.isCollapsed) continue
            val storage = based.computeIfAbsent(requirement.base) { RequirementStorage() }
            if (storage.mergeAdd(requirement) != null) modified += storage
        }

        val result = mutableListOf<InitialFactAp>()
        modified.forEach { it.getAndResetDelta(result) }
        return result
    }

    override fun filterTo(dst: MutableList<InitialFactAp>, fact: FinalFactAp) {
        fact as BaseOnlyFinalFactAp
        val storage = based[fact.base] ?: return
        storage.filterTo(dst, fact.access)
    }

    override fun collectAllRequirementsTo(dst: MutableList<InitialFactAp>) {
        based.values.forEach { storage ->
            storage.collectAllTo(dst)
        }
    }

    private class RequirementStorage {
        private val requirements = long2ObjectMap<BaseOnlyInitialFactAp>()
        private val delta = Long2ObjectOpenHashMap<BaseOnlyInitialFactAp>()

        fun mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
            val previous = requirements.get(requirement.access)
            if (previous == null) {
                requirements.put(requirement.access, requirement)
                delta.put(requirement.access, requirement)
                return requirement
            }

            val merged = previous.mergeAdd(requirement) ?: return null
            requirements.put(requirement.access, merged)

            val addedExclusions = requirement.exclusions.addedComparedTo(previous.exclusions)
            check(addedExclusions !is ExclusionSet.Empty)
            val addedRequirement = requirement.replaceExclusions(addedExclusions) as BaseOnlyInitialFactAp
            val previousDelta = delta[requirement.access]
            val mergedDelta = checkNotNull(previousDelta.mergeAdd(addedRequirement))
            delta.put(requirement.access, mergedDelta)
            return addedRequirement
        }

        fun getAndResetDelta(dst: MutableList<InitialFactAp>) {
            dst.addAll(delta.values)
            delta.clear()
        }

        fun filterTo(dst: MutableList<InitialFactAp>, fact: BaseOnlyAccess) {
            requirements.forEachEntry { _, requirement ->
                if (baseOnlySummaryInitialMatches(fact, requirement.access)) {
                    dst.add(requirement)
                }
            }
        }

        fun collectAllTo(dst: MutableList<InitialFactAp>) {
            requirements.forEachEntry { _, requirement -> dst.add(requirement) }
        }
    }
}

private fun ExclusionSet.addedComparedTo(previous: ExclusionSet): ExclusionSet = when (this) {
    ExclusionSet.Empty -> ExclusionSet.Empty
    ExclusionSet.Universe -> error("Unexpected universe exclusion")
    is ExclusionSet.Concrete -> when (previous) {
        ExclusionSet.Empty -> this
        ExclusionSet.Universe -> ExclusionSet.Empty
        is ExclusionSet.Concrete -> {
            val added = set.removeAll(previous.set)
            when {
                added === set -> this
                added.isEmpty() -> ExclusionSet.Empty
                else -> ExclusionSet.Concrete(added, added.hashCode())
            }
        }
    }
}

private fun BaseOnlyInitialFactAp?.mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
    if (this == null) return requirement
    val mergedExclusion = exclusions.union(requirement.exclusions)
    if (mergedExclusion === exclusions) return null
    return BaseOnlyInitialFactAp(requirement.manager, requirement.base, requirement.access, mergedExclusion)
}
