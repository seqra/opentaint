package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.SideEffectExclusionMergingStorage
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.Storage
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

class FactSESummariesAutomataStorage(methodEntryPoint: CommonInst) :
    CommonFactSideEffectSummary<AutomataInitialAccess, AutomataFinalAccess>(methodEntryPoint),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createStorage(): Storage<AutomataInitialAccess, AutomataFinalAccess> = SEStorage()
}

private class SEStorage : Storage<AutomataInitialAccess, AutomataFinalAccess> {
    private val storage = ConcurrentHashMap<AutomataInitialAccess, SEExclusionStorage>()

    override fun add(
        iap: AutomataInitialAccess,
        se: Map<SideEffectKind, ExclusionSet>,
        added: MutableList<FactSEBuilder<AutomataInitialAccess>>,
    ) {
        val storageNode = storage.computeIfAbsent(iap) { SEExclusionStorage(iap) }
        for ((kind, exclusion) in se) {
            storageNode.add(kind, exclusion)?.let { added += it }
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<FactSEBuilder<AutomataInitialAccess>>,
        initialFactPattern: AutomataFinalAccess?,
    ) {
        storage.values.forEach { dst += it.summaries() }
    }
}

private class SEExclusionStorage(
    private val iap: AutomataInitialAccess,
) : SideEffectExclusionMergingStorage<AutomataInitialAccess>() {
    override fun createBuilder(): FactSEBuilder<AutomataInitialAccess> =
        Builder().setInitialAp(iap)
}

private class Builder : FactSEBuilder<AutomataInitialAccess>(), AutomataInitialApAccess {
    override fun nonNullIAP(iap: AutomataInitialAccess?): AutomataInitialAccess =
        iap ?: error("iap not initialized")
}
