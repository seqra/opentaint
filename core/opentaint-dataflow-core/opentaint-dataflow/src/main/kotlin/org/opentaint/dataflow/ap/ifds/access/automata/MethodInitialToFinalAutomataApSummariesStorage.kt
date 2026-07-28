package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary.F2FBBuilder
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.dataflow.util.concurrentReadSafeForEach
import org.opentaint.dataflow.util.forEach
import org.opentaint.dataflow.util.getOrCreateIndex
import org.opentaint.dataflow.util.object2IntMap
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodInitialToFinalAutomataApSummariesStorage(
    methodInitialStatement: CommonInst,
) : CommonF2FSummary<AutomataAccess, AutomataAccess>(methodInitialStatement),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createStorage(): Storage<AutomataAccess, AutomataAccess> = InitialToFinalApStorage()
}

private class InitialToFinalApStorage : CommonF2FSummary.Storage<AutomataAccess, AutomataAccess> {
    private val initialFactGraphIndex = object2IntMap<AccessGraph>()
    private val initialFactGraphs = arrayListOf<AccessGraph>()
    private val finalFactGraphStorages = arrayListOf<FinalApStorage>()

    private val initialGraphIndex = GraphIndex()

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<AutomataAccess, AutomataAccess>>,
        added: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>,
    ) {
        val modifiedStorages = BitSet()

        for (edge in edges) {
            check(edge.initial.cleanerEffects == edge.final.cleanerEffects)
            val storageIdx = getOrCreateStorageIdx(edge.initial)
            val storage = finalFactGraphStorages[storageIdx]

            if (storage.add(edge.demandState, edge.final)) {
                modifiedStorages.set(storageIdx)
            }
        }

        modifiedStorages.forEach { storageIdx ->
            val storage = finalFactGraphStorages[storageIdx]
            val storageEdges = mutableListOf<F2FBBuilder<AutomataAccess, AutomataAccess>>()
            storage.addAndResetDelta(storageEdges)

            val initialAg = initialFactGraphs[storageIdx]
            val initial = AutomataAccess(initialAg, storage.cleanerEffects())
            storageEdges.mapTo(added) { it.setInitialAp(initial) }
        }
    }

    private fun getOrCreateStorageIdx(initial: AutomataAccess): Int {
        return initialFactGraphIndex.getOrCreateIndex(initial.access) { newIdx ->
            initialFactGraphs.add(initial.access)
            finalFactGraphStorages.add(FinalApStorage())
            initialGraphIndex.add(initial.access, newIdx)
            return newIdx
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>,
        initialFactPatter: AutomataAccess?,
    ) {
        if (initialFactPatter != null) {
            filterEdgesTo(dst, initialFactPatter)
        } else {
            allEdgesTo(dst)
        }
    }

    private fun allEdgesTo(dst: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>) {
        finalFactGraphStorages.concurrentReadSafeForEach { idx, finalStorage ->
            val initialAg = initialFactGraphs[idx]
            val initial = AutomataAccess(initialAg, finalStorage.cleanerEffects())
            collectToListWithPostProcess(dst, {
                finalStorage.allEdgesTo(it)
            }, {
                it.setInitialAp(initial)
            })
        }
    }

    private fun filterEdgesTo(
        dst: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>,
        accessPattern: AutomataAccess,
    ) {
        initialGraphIndex.localizeGraphHasDeltaWithIndexedGraph(accessPattern.access).forEach { storageIdx ->
            val initialAg = initialFactGraphs[storageIdx]

            if (accessPattern.access.delta(initialAg).isEmpty()) {
                return@forEach
            }

            val finalStorage = finalFactGraphStorages[storageIdx]
            collectToListWithPostProcess(dst, {
                finalStorage.allEdgesTo(it)
            }, {
                it.setInitialAp(AutomataAccess(initialAg, finalStorage.cleanerEffects()))
            })
        }
    }

    override fun toString(): String {
        val builder = StringBuilder()
        finalFactGraphStorages.concurrentReadSafeForEach { idx, finalStorage ->
            val initialAg = initialFactGraphs[idx]
            builder.appendLine("($initialAg -> $finalStorage)")
        }
        return builder.toString()
    }
}

private class FinalApStorage {
    private var demandStateStorage: FactDemandState? = null
    private var cleanerEffects: AnyFieldCleanerEffects? = null
    private val agStorage = AccessGraphStorageWithCompression()
    private var stateModified: Boolean = false

    fun cleanerEffects(): AnyFieldCleanerEffects = cleanerEffects
        ?: error("Cleaner effects are not initialized")

    fun addAndResetDelta(modified: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>) {
        val demandState = demandStateStorage ?: return
        val effects = cleanerEffects ?: return
        if (stateModified) {
            agStorage.allGraphs().forEach { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setDemandState(demandState)
                    .setExitAp(AutomataAccess(ag, effects))
            }
        } else {
            agStorage.mapAndResetDelta { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setDemandState(demandState)
                    .setExitAp(AutomataAccess(ag, effects))
            }
        }

        stateModified = false
    }

    fun add(demandState: FactDemandState, finalAp: AutomataAccess): Boolean {
        val mergedState = demandStateStorage?.join(demandState) ?: demandState
        val mergedEffects = cleanerEffects?.join(finalAp.cleanerEffects) ?: finalAp.cleanerEffects
        if (mergedState === demandStateStorage && mergedEffects === cleanerEffects) {
            return agStorage.add(finalAp.access)
        }

        demandStateStorage = mergedState
        cleanerEffects = mergedEffects
        agStorage.add(finalAp.access)
        stateModified = true

        return true
    }

    fun allEdgesTo(dst: MutableList<F2FBBuilder<AutomataAccess, AutomataAccess>>) {
        val demandState = demandStateStorage ?: return
        val effects = cleanerEffects ?: return
        collectToListWithPostProcess(dst, {
            agStorage.allGraphsTo(it)
        }, { ag ->
            FactToFactEdgeBuilderBuilder()
                .setDemandState(demandState)
                .setExitAp(AutomataAccess(ag, effects))
        })
    }

    override fun toString(): String = "($demandStateStorage -> $agStorage)"
}

class FactToFactEdgeBuilderBuilder : F2FBBuilder<AutomataAccess, AutomataAccess>(),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun nonNullIAP(iap: AutomataAccess?): AutomataAccess = iap!!
}
