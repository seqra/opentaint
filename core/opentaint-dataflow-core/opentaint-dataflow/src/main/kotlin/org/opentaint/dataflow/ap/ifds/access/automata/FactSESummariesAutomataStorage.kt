package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.FactSEBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactSideEffectSummary.Storage
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

class FactSESummariesAutomataStorage(methodEntryPoint: CommonInst) :
    CommonFactSideEffectSummary<AutomataAccess, AutomataAccess>(methodEntryPoint),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createStorage(): Storage<AutomataAccess, AutomataAccess> = SEStorage()
}

private class SEStorage : Storage<AutomataAccess, AutomataAccess> {
    private val storage = ConcurrentHashMap<AccessGraph, SEExclusionStorage>()

    override fun add(
        iap: AutomataAccess,
        se: Map<SideEffectKind, FactDemandState>,
        added: MutableList<FactSEBuilder<AutomataAccess>>
    ) {
        val storageNode = storage.computeIfAbsent(iap.access) { SEExclusionStorage(iap.access) }
        for ((kind, demandState) in se) {
            storageNode.add(kind, demandState, iap.cleanerEffects)?.let { added += it }
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<FactSEBuilder<AutomataAccess>>,
        initialFactPattern: AutomataAccess?
    ) {
        storage.values.forEach {
            dst += it.summaries()
        }
    }
}

private class SEExclusionStorage(
    private val iap: AccessGraph,
) {
    private data class State(
        val demandState: FactDemandState,
        val cleanerEffects: AnyFieldCleanerEffects,
    )

    private val sideEffects = ConcurrentHashMap<SideEffectKind, State>()

    fun add(
        kind: SideEffectKind,
        demandState: FactDemandState,
        cleanerEffects: AnyFieldCleanerEffects,
    ): FactSEBuilder<AutomataAccess>? {
        val current = sideEffects[kind]
        val merged = current?.let {
            State(it.demandState join demandState, it.cleanerEffects join cleanerEffects)
        } ?: State(demandState, cleanerEffects)
        if (merged == current) return null

        sideEffects[kind] = merged
        return builder(kind, merged)
    }

    fun summaries(): List<FactSEBuilder<AutomataAccess>> =
        sideEffects.map { (kind, state) -> builder(kind, state) }

    private fun builder(kind: SideEffectKind, state: State): FactSEBuilder<AutomataAccess> =
        Builder()
            .setInitialAp(AutomataAccess(iap, state.cleanerEffects))
            .setDemandState(state.demandState)
            .setKind(kind)
}

private class Builder : FactSEBuilder<AutomataAccess>(), AutomataInitialApAccess {
    override fun nonNullIAP(iap: AutomataAccess?): AutomataAccess = iap
        ?: error("iap not initialized")
}
