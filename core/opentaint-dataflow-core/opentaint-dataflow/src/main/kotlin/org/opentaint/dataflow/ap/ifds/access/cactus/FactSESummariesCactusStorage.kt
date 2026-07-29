package org.opentaint.dataflow.ap.ifds.access.cactus

import kotlinx.collections.immutable.persistentHashMapOf
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.Storage
import org.opentaint.ir.api.common.cfg.CommonInst

class FactSESummariesCactusStorage(
    methodInitialInst: CommonInst,
) : CommonFactSideEffectSummary<CactusInitialAccess, CactusFinalAccess>(methodInitialInst),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createStorage(): Storage<CactusInitialAccess, CactusFinalAccess> =
        CactusSEStorage()
}

private class CactusSEStorage : Storage<CactusInitialAccess, CactusFinalAccess> {
    private var initialAccessToStorage =
        persistentHashMapOf<CactusInitialAccess, CactusSEMergeStorage>()

    private fun getOrCreate(initialAccess: CactusInitialAccess): CactusSEMergeStorage =
        initialAccessToStorage.getOrElse(initialAccess) {
            CactusSEMergeStorage(initialAccess).also {
                initialAccessToStorage = initialAccessToStorage.put(initialAccess, it)
            }
        }

    override fun add(
        iap: CactusInitialAccess,
        se: Map<SideEffectKind, ExclusionSet>,
        added: MutableList<FactSEBuilder<CactusInitialAccess>>,
    ) {
        val storageNode = getOrCreate(iap)
        for ((kind, exclusion) in se) {
            storageNode.add(kind, exclusion)?.let { added += it }
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<FactSEBuilder<CactusInitialAccess>>,
        initialFactPattern: CactusFinalAccess?,
    ) {
        initialAccessToStorage.values.forEach { storage ->
            dst += storage.summaries()
        }
    }
}

private class CactusSEMergeStorage(
    private val initialAccess: CactusInitialAccess,
) : CommonFactSideEffectSummary.SideEffectExclusionMergingStorage<CactusInitialAccess>() {
    override fun createBuilder(): FactSEBuilder<CactusInitialAccess> =
        FactSECactusApBuilder().setInitialAp(initialAccess)
}

private class FactSECactusApBuilder : FactSEBuilder<CactusInitialAccess>(),
    CactusInitialApAccess {
    override fun nonNullIAP(iap: CactusInitialAccess): CactusInitialAccess = iap
}
