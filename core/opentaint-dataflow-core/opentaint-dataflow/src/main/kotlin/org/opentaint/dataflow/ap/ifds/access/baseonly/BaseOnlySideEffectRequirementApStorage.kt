package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
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
        private class RequirementNode(initial: BaseOnlyInitialFactAp) {
            @Volatile
            var requirement: BaseOnlyInitialFactAp = initial
        }

        private val requirements = BaseOnlyInitialAccessIndex<RequirementNode>()
        private val delta = Long2ObjectOpenHashMap<BaseOnlyInitialFactAp>()

        fun mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
            var added = false
            val node = requirements.getOrCreate(requirement.access) {
                added = true
                RequirementNode(requirement)
            }
            if (added) {
                delta.put(requirement.access, requirement)
                return requirement
            }

            val previous = node.requirement
            val update = previous.mergeWithAdded(requirement) ?: return null
            val merged = update.merged
            node.requirement = merged

            val addedRequirement = requirement.replaceExclusions(update.added) as BaseOnlyInitialFactAp
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
            requirements.collectCandidates(fact) { _, node ->
                val requirement = node.requirement
                if (baseOnlySummaryInitialMatches(fact, requirement.access)) {
                    dst.add(requirement)
                }
            }
        }

        fun collectAllTo(dst: MutableList<InitialFactAp>) {
            requirements.collectAll { _, node -> dst.add(node.requirement) }
        }
    }
}

private data class ExclusionMerge(
    val merged: BaseOnlyInitialFactAp,
    val added: ExclusionSet,
)

private fun BaseOnlyInitialFactAp.mergeWithAdded(requirement: BaseOnlyInitialFactAp): ExclusionMerge? {
    val previousExclusions = exclusions
    val incomingExclusions = requirement.exclusions
    if (incomingExclusions is ExclusionSet.Empty) return null
    if (previousExclusions is ExclusionSet.Empty) {
        return ExclusionMerge(requirement, incomingExclusions)
    }
    check(previousExclusions is ExclusionSet.Concrete && incomingExclusions is ExclusionSet.Concrete)

    val previousSet = previousExclusions.set as BaseOnlyExclusionAccessorSet
    val incomingSet = incomingExclusions.set as BaseOnlyExclusionAccessorSet
    val update = previousSet.unionWithAdded(incomingSet) ?: return null
    val mergedExclusions = ExclusionSet.Concrete(update.union)
    val addedExclusions = ExclusionSet.Concrete(update.added)
    return ExclusionMerge(
        BaseOnlyInitialFactAp(requirement.manager, requirement.base, requirement.access, mergedExclusions),
        addedExclusions,
    )
}

private fun BaseOnlyInitialFactAp?.mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
    if (this == null) return requirement
    val mergedExclusion = exclusions.union(requirement.exclusions)
    if (mergedExclusion === exclusions) return null
    return BaseOnlyInitialFactAp(requirement.manager, requirement.base, requirement.access, mergedExclusion)
}
