package org.opentaint.dataflow.ap.ifds.access.cactus

import kotlinx.collections.immutable.persistentHashMapOf
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.Storage
import org.opentaint.ir.api.common.cfg.CommonInst

class FactSESummariesCactusStorage(
    methodInitialInst: CommonInst
) : CommonFactSideEffectSummary<CactusInitialAccess, CactusFinalAccess>(methodInitialInst),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createStorage(): Storage<CactusInitialAccess, CactusFinalAccess> =
        CactusSEStorage()
}

private class CactusSEStorage : Storage<CactusInitialAccess, CactusFinalAccess> {
    private var initialAccessToStorage =
        persistentHashMapOf<AccessPathWithCycles.AccessNode?, CactusSEMergeStorage>()

    private fun getOrCreate(initialAccess: AccessPathWithCycles.AccessNode?): CactusSEMergeStorage =
        initialAccessToStorage.getOrElse(initialAccess) {
            CactusSEMergeStorage(initialAccess).also {
                initialAccessToStorage = initialAccessToStorage.put(initialAccess, it)
            }
        }

    override fun add(
        iap: CactusInitialAccess,
        se: Map<SideEffectKind, FactDemandState>,
        added: MutableList<FactSEBuilder<CactusInitialAccess>>
    ) {
        val storageNode = getOrCreate(iap.access)
        for ((kind, demandState) in se) {
            storageNode.add(kind, demandState, iap.cleanerEffects)?.let { added += it }
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<FactSEBuilder<CactusInitialAccess>>,
        initialFactPattern: CactusFinalAccess?
    ) {
        initialAccessToStorage.values.forEach { storage ->
            dst += storage.summaries()
        }
    }
}

private class CactusSEMergeStorage(
    private val initialAccess: AccessPathWithCycles.AccessNode?,
) {
    private data class State(
        val demandState: FactDemandState,
        val cleanerEffects: AnyFieldCleanerEffects,
    )

    private var sideEffects = persistentHashMapOf<SideEffectKind, State>()

    fun add(
        kind: SideEffectKind,
        demandState: FactDemandState,
        cleanerEffects: AnyFieldCleanerEffects,
    ): FactSEBuilder<CactusInitialAccess>? {
        val current = sideEffects[kind]
        val merged = current?.let {
            State(it.demandState join demandState, it.cleanerEffects join cleanerEffects)
        } ?: State(demandState, cleanerEffects)
        if (merged == current) return null

        sideEffects = sideEffects.put(kind, merged)
        return builder(kind, merged)
    }

    fun summaries(): List<FactSEBuilder<CactusInitialAccess>> =
        sideEffects.map { (kind, state) -> builder(kind, state) }

    private fun builder(
        kind: SideEffectKind,
        state: State,
    ): FactSEBuilder<CactusInitialAccess> =
        FactSECactusApBuilder()
            .setInitialAp(CactusInitialAccess(initialAccess, state.cleanerEffects))
            .setDemandState(state.demandState)
            .setKind(kind)
}

private class FactSECactusApBuilder: FactSEBuilder<CactusInitialAccess>(),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun nonNullIAP(iap: CactusInitialAccess?): CactusInitialAccess =
        iap ?: error("iap not initialized")
}
