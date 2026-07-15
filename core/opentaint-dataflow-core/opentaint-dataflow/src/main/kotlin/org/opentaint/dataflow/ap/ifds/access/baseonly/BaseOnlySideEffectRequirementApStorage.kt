package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
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
            val storage = based.computeIfAbsent(requirement.base) { RequirementStorage() }
            if (storage.mergeAdd(requirement) != null) modified += storage
        }

        val result = mutableListOf<InitialFactAp>()
        modified.forEach { it.getAndResetDelta(result) }
        return result
    }

    override fun filterTo(dst: MutableList<InitialFactAp>, fact: FinalFactAp) {
        val storage = based[fact.base] ?: return
        dst.addAll(storage.requirements.values)
    }

    override fun collectAllRequirementsTo(dst: MutableList<InitialFactAp>) {
        based.values.forEach { dst.addAll(it.requirements.values) }
    }

    private class RequirementStorage {
        val requirements = Long2ObjectOpenHashMap<BaseOnlyInitialFactAp>()
        private val delta = Long2ObjectOpenHashMap<BaseOnlyInitialFactAp>()

        fun mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
            val merged = requirements.get(requirement.access).mergeAdd(requirement) ?: return null
            requirements.put(requirement.access, merged)
            delta.put(requirement.access, merged)
            return merged
        }

        fun getAndResetDelta(dst: MutableList<InitialFactAp>) {
            dst.addAll(delta.values)
            delta.clear()
        }
    }
}

private fun BaseOnlyInitialFactAp?.mergeAdd(requirement: BaseOnlyInitialFactAp): BaseOnlyInitialFactAp? {
    if (this == null) return requirement
    val mergedExclusion = exclusions.union(requirement.exclusions)
    if (mergedExclusion === exclusions) return null
    return BaseOnlyInitialFactAp(requirement.manager, requirement.base, requirement.access, mergedExclusion)
}
