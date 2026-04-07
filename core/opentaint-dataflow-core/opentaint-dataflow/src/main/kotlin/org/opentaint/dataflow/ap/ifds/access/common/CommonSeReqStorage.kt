package org.opentaint.dataflow.ap.ifds.access.common

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.util.collectToListWithPostProcess
import java.util.concurrent.ConcurrentHashMap

abstract class CommonSeReqStorage<IAP, FAP : Any> :
    SideEffectRequirementApStorage,
    InitialApAccess<IAP>, FinalApAccess<FAP> {
    private val based = ConcurrentHashMap<AccessPathBase, Storage<IAP, FAP>>()

    interface Storage<IAP, FAP : Any> {
        fun add(requirement: IAP, exclusionSet: ExclusionSet): Boolean
        fun getAndResetDelta(delta: MutableList<Pair<IAP, ExclusionSet>>)
        fun find(dst: MutableList<Pair<IAP, ExclusionSet>>, pattern: FAP?)
    }

    abstract fun createStorage(): Storage<IAP, FAP>

    override fun add(requirements: List<InitialFactAp>): List<InitialFactAp> {
        val modifiedBases = hashSetOf<AccessPathBase>()
        val modifiedStorages = mutableListOf<Pair<AccessPathBase, Storage<IAP, FAP>>>()

        for (requirement in requirements) {
            val base = requirement.base
            val storage = based.computeIfAbsent(base) { createStorage() }

            if (!storage.add(getInitialAccess(requirement), requirement.exclusions)) {
                continue
            }

            if (!modifiedBases.add(base)) {
                continue
            }

            modifiedStorages.add(base to storage)
        }

        val result = mutableListOf<InitialFactAp>()
        for ((base, storage) in modifiedStorages) {
            collectToListWithPostProcess(
                result,
                { storage.getAndResetDelta(it) },
                { (iap, ex) -> createInitial(base, iap, ex) }
            )
        }
        return result
    }

    override fun filterTo(dst: MutableList<InitialFactAp>, fact: FinalFactAp) {
        val storage = based[fact.base] ?: return
        val finalAccess = getFinalAccess(fact)

        collectToListWithPostProcess(
            dst,
            { storage.find(it, finalAccess) },
            { (iap, ex) -> createInitial(fact.base, iap, ex) }
        )
    }

    override fun collectAllRequirementsTo(dst: MutableList<InitialFactAp>) {
        based.entries.forEach { (base, storage) ->
            collectToListWithPostProcess(
                dst,
                { storage.find(it, pattern = null) },
                { (iap, ex) -> createInitial(base, iap, ex) }
            )
        }
    }
}
