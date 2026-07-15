package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class FactSESummariesBaseOnlyStorage(
    methodInitialInst: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonFactSideEffectSummary<BaseOnlyAccess, BaseOnlyAccess>(methodInitialInst),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess, BaseOnlyAccess> = SEStorage(apManager)

    private class SEStorage(private val manager: BaseOnlyApManager) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
        private val perInitial = Long2ObjectOpenHashMap<MergeStorage>()

        override fun add(
            iap: BaseOnlyAccess,
            se: Map<SideEffectKind, ExclusionSet>,
            added: MutableList<FactSEBuilder<BaseOnlyAccess>>,
        ) {
            val storageNode = perInitial.get(iap) ?: MergeStorage(manager, iap).also { perInitial.put(iap, it) }
            for ((kind, exclusion) in se) {
                storageNode.add(kind, exclusion)?.let { added += it }
            }
        }

        override fun collectSummariesTo(
            dst: MutableList<FactSEBuilder<BaseOnlyAccess>>,
            initialFactPattern: BaseOnlyAccess?,
        ) {
            perInitial.values.forEach { dst += it.summaries() }
        }
    }

    private class MergeStorage(private val manager: BaseOnlyApManager, private val initialAccess: BaseOnlyAccess) :
        SideEffectExclusionMergingStorage<BaseOnlyAccess>() {
        override fun createBuilder(): FactSEBuilder<BaseOnlyAccess> = Builder(manager).setInitialAp(initialAccess)
    }

    private class Builder(override val apManager: BaseOnlyApManager) :
        FactSEBuilder<BaseOnlyAccess>(), BaseOnlyInitialApAccess {
        override fun nonNullIAP(iap: BaseOnlyAccess?): BaseOnlyAccess = iap ?: ABSTRACT_EMPTY_ACCESS
    }
}
